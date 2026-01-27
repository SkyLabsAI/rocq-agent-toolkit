from collections.abc import Callable
from typing import Annotated, override

from observability import get_logger
from observability.tracing.decorators import trace
from provenance_toolkit import Provenance
from rocq_doc_manager import RocqCursor

from ..action import Action

logger = get_logger("rocq_agent")

# Rocq tactics and commands have a lot of variations that make dealing
# with them complex. In an ideal world, we would get this information
# from Rocq and operate at the abstract syntax level, but that requires
# exposing APIs from Rocq that are not currently exposed. Several
# notes.
#
# Commands are interactions with Rocq that end with a `.`, e.g.
#
# - `Lemma foo : True.`
# - `Hint Resolve foo : typeclass_instances.`
#
# Commands expose a very "raw", text-based level of interaction with Rocq
# and can be used as an escape hatch when finer-grained APIs are not suitable.
#
# One way to build commands is via tactics, and we sometimes wish to
# manipulate tactics, e.g. by adding `progress`, or running tactics on
# resulting goals. Some example tactics are the following:
#
# - `intros`
# - `1: reflexivity`
# - `1,3: lia`
#
# Note that tactics **do not** end in a `.`[^..tactics].
#
# Another class of interactions are "tactics" for focusing and bracketing.
# These include interactions such as `{`, `-`, `+`, `*`. These interactions
# are currently not well supported in this framework and are currently
# best to work with these as commands.
#
# [^..tactics]: The ".." abbreviation, e.g. in `intros..`, does mean that
# tactics can syntactically end in a `.`. However, note that to execute this,
# you need `intros.. .` (often without the space between the two).
#


def is_command(cmd: str) -> bool:
    """Detect whether the string looks like a Rocq command."""
    if cmd in "{}+-*":
        # commonly supported bracketing commands that do not
        # use `.`s.
        return True
    return cmd.endswith("...") if cmd.endswith("..") else cmd.endswith(".")


def tactic_of(tactic: str) -> str:
    """Get a tactic from a tactic string.

    NOTE: This is currently simple, but should support features such as
    goal selectors. This might require type changes.
    """
    tactic = tactic.strip()
    assert not is_command(tactic)
    return tactic


class RocqCommandAction(Action[RocqCursor]):
    """Execute a single Rocq command.

    This command **must** end in a '.'.
    """

    _command: Annotated[str, Provenance.Reflect.Field]

    def __init__(self, cmd: str) -> None:
        """Build an action to run the command."""
        assert is_command(cmd)
        self._command = cmd

    @override
    @trace("RocqCommandAction")
    def interact(self, state: RocqCursor) -> RocqCursor:
        # TODO: the fact that cursors are not functional is quite annoying here.
        # It should be the caller that creates a new cursor, but in this case
        # we will basically always be returning our own cursor.
        # If cursors were functional, we would just be returning the latest
        # cursor here.
        response = state.insert_command(self._command)
        if isinstance(response, RocqCursor.Err):
            # Preserve the actual Rocq error message
            raise Action.Failed(
                message=response.message,
                details=response,
            )
        return state

    @override
    def key(self) -> str:
        return self._command


class RocqTacticAction(Action[RocqCursor]):
    """Execute a single Rocq tactic, potentially with modifiers.

    Note that the tactic is not a command, so it should **not** end in a `.`
    (unless it is a tactic such as `intros..`).
    """

    _tactic: Annotated[str, Provenance.Reflect.Field]

    def __init__(
        self,
        tactic: str,
        *,
        progress: bool = False,
        no_evar: bool = False,
    ) -> None:
        """The tactic must be a Rocq tactic, **not** a Rocq command, so it should **not** end in a '.'."""
        tactic = tactic_of(tactic)
        # NOTE: we place the `progress` first, then the match
        tactic = f"progress ({tactic})" if progress else tactic
        tactic = (
            f"{tactic}; lazymatch goal with |- ?g => assert_fails (has_evar g) end"
            if no_evar
            else tactic
        )
        self._tactic = tactic

    @override
    @trace("RocqTacticAction")
    def interact(self, state: RocqCursor) -> RocqCursor:
        # TODO: the fact that cursors are not functional is quite annoying here.
        # It should be the caller that creates a new cursor, but in this case
        # we will basically always be returning our own cursor.
        # If cursors were functional, we would just be returning the latest
        # cursor here.
        response = state.insert_command(f"{self._tactic}.")
        if isinstance(response, RocqCursor.Err):
            # Preserve the actual Rocq error message
            raise Action.Failed(
                message=response.message,
                details=response,
            )
        return state

    @override
    def key(self) -> str:
        return self._tactic


class RocqRetryCommandAction(Action[RocqCursor]):
    """
    A Rocq action that retries using a given (often LLM-based) rectifier.

    Inherits tactic execution from RocqTacticAction and adds:
    - Cursor passed to rectifier for goal/context access
    - Real Rocq error message preservation
    - Retry loop with rectifier callback

    After interact() completes successfully, use `final_tactic` to get the
    tactic that actually succeeded (which may differ from the original if
    rectification occurred).
    """

    _rectifier: Annotated[
        Callable[[RocqCursor, str, str], str | None] | None,
        Provenance.Reflect.CallableField,
    ]
    _max_retries: Annotated[int, Provenance.Reflect.Field]
    _final_command: str | None  # imperative state, does not contribute to provenance

    def __init__(
        self,
        command: str,
        rectifier: Callable[[RocqCursor, str, str], str | None] | None,
        max_retries: int = 3,
        **kwargs,
    ) -> None:
        """
        Args:
            tactic: Initial tactic string to try (tactics do not include the '.').
            rectifier: Function (cursor, tactic, error) -> rectified_tactic | None
            max_retries: Maximum number of rectification attempts
        """
        command = command.strip()
        self._initial_command = command
        self._rectifier = rectifier
        self._max_retries = max_retries
        self._final_command: str | None = None

    @property
    def final_command(self) -> str | None:
        """
        The tactic that actually succeeded (after any rectification).

        Returns None if interact() hasn't been called or failed.
        Use this for logging/tracing what actually ran.
        """
        return self._final_command

    @override
    def interact(self, state: RocqCursor) -> RocqCursor:
        self._final_command = None
        command = self._initial_command

        # Total attempts = 1 (original) + N (retries)
        max_attempts = (self._max_retries + 1) if self._rectifier else 1

        for attempt in range(max_attempts):
            response = state.insert_command(command)
            if not isinstance(response, RocqCursor.Err):
                self._final_command = command
                return state

            if attempt == max_attempts - 1:
                # out of attempts, we fail
                raise Action.Failed(
                    message=(
                        f"Max retries ({self._max_retries}) exceeded for '{self._initial_command}'. "
                        f"Last error: {response.message}"
                    ),
                    details=response,
                )

            # We know self._rectifier is not None because max_attempts > 1
            assert self._rectifier is not None
            rectified = self._rectifier(state, command, response.message)

            if rectified is None:
                raise Action.Failed(
                    message=f"Could not rectify after {attempt + 1} attempts: {response.message}",
                    details=response,
                )

            command = rectified

        # Unreachable
        raise Action.Failed("Unexpected loop termination")

    @override
    def key(self) -> str:
        """
        Returns the original tactic for deduplication and loop detection.

        We use the original (not rectified) tactic because:
        1. Deduplication: If the generator suggests "autoo." multiple times,
           we shouldn't retry it—it'll just rectify to the same thing.
        2. Loop detection: The repetition policy checks recent action keys
           to prevent cycles. Using original keys ensures we detect when
           the generator keeps suggesting the same broken tactic.

        For the tactic that actually succeeded, use `final_tactic` instead.
        """
        return self._initial_command
