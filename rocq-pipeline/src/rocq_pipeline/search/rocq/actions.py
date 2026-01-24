from collections.abc import Callable
from typing import Annotated, override

from observability import get_logger
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


class RocqTacticAction(Action[RocqCursor]):
    """Execute a single Rocq tactic."""

    _tactic: Annotated[str, Provenance.Reflect.Field]

    def __init__(self, tactic: str) -> None:
        self._tactic = tactic

    @override
    def interact(self, state: RocqCursor) -> RocqCursor:
        # TODO: the fact that cursors are not functional is quite annoying here.
        # It should be the caller that creates a new cursor, but in this case
        # we will basically always be returning our own cursor.
        # If cursors were functional, we would just be returning the latest
        # cursor here.
        response = self.run_tactic(state, self._tactic)
        if isinstance(response, RocqCursor.Err):
            # Preserve the actual Rocq error message
            logger.info(f"  RocqTacticAction: '{self._tactic}' failed.")
            raise Action.Failed(
                message=response.message,
                details=response,
            )
        logger.info(f"  RocqTacticAction: '{self._tactic}' succeeded.")
        return state

    def run_tactic(
        self, rc: RocqCursor, tactic: str
    ) -> RocqCursor.CommandData | RocqCursor.Err[RocqCursor.CommandError]:
        return rc.insert_command(tactic)

    @override
    def key(self) -> str:
        return self._tactic.strip()


class RocqRetryAction(RocqTacticAction):
    """
    Rocq tactic with LLM-based rectification on failure.

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
    _final_tactic: str | None  # this field is mutable

    def __init__(
        self,
        tactic: str,
        rectifier: Callable[[RocqCursor, str, str], str | None] | None,
        max_retries: int = 3,
    ) -> None:
        """
        Args:
            tactic: Initial tactic string to try
            rectifier: Function (cursor, tactic, error) -> rectified_tactic | None
            max_retries: Maximum number of rectification attempts
        """
        super().__init__(tactic)
        self._rectifier = rectifier
        self._max_retries = max_retries
        self._final_tactic: str | None = None

    @property
    def final_tactic(self) -> str | None:
        """
        The tactic that actually succeeded (after any rectification).

        Returns None if interact() hasn't been called or failed.
        Use this for logging/tracing what actually ran.
        """
        return self._final_tactic

    @override
    def interact(self, state: RocqCursor) -> RocqCursor:
        self._final_tactic = None
        tactic = self._tactic

        # Total attempts = 1 (original) + N (retries)
        max_attempts = (self._max_retries + 1) if self._rectifier else 1

        for attempt in range(max_attempts):
            # 1. Try the tactic
            response = self.run_tactic(state, tactic)

            # 2. Success path
            if not isinstance(response, RocqCursor.Err):
                self._final_tactic = tactic
                return state

            # 3. Failure path - can we try again?
            is_last_attempt = attempt == max_attempts - 1
            if is_last_attempt:
                raise Action.Failed(
                    message=(
                        f"Max retries ({self._max_retries}) exceeded for '{self._tactic}'. "
                        f"Last error: {response.message}"
                    ),
                    details=response,
                )

            # 4. Recovery logic (Rectification)
            # We know self._rectifier is not None because max_attempts > 1
            assert self._rectifier is not None
            rectified = self._rectifier(state, tactic, response.message)

            if rectified is None:
                raise Action.Failed(
                    message=f"Could not rectify after {attempt + 1} attempts: {response.message}",
                    details=response,
                )

            tactic = rectified

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
        return self._tactic.strip()
