import logging
import re
from collections.abc import Callable, Iterator, Sequence
from contextlib import contextmanager
from typing import Any, Literal, Self, override
from warnings import deprecated

from jsonrpc_tp import JsonRPCTP

from .dune_util import dune_env_hack
from .rocq_doc_manager_api import RocqDocManagerAPI as API

logger = logging.getLogger(__name__)


class RocqDocManager(API):
    NO_GOAL_STRINGS: set[str] = {
        "No such goal.",
        "No more goals."
    }

    def __init__(
            self,
            rocq_args: list[str],
            file_path: str,
            chdir: str | None = None,
            dune: bool = False,
            dune_disable_global_lock: bool = True,
    ) -> None:
        env: dict[str, str] | None = None
        args: list[str] = []
        if dune:
            assert chdir is None

            # NOTE: workaround issue with [dune exec] not properly handling
            # the "--no-build" flag.
            if dune_disable_global_lock:
                env = dune_env_hack()
            args = [
                "dune", "exec", "--no-build",
                "--no-print-directory", "--display=quiet",
                "rocq-doc-manager", "--", file_path,
                "--"
            ] + rocq_args
        else:
            args = ["rocq-doc-manager", file_path, "--"] + rocq_args
        super().__init__(JsonRPCTP(args=args, cwd=chdir, env=env))
        self._file_path: str = file_path
        self._file_loaded: bool = False

    # ===== BEGIN: deprecations ===============================================
    @deprecated("use `query_text`")
    def text_query(self, text: str, index: int) -> str | API.Err[None]:
        return self.query_text(text, index)

    @deprecated("use `query_text_all`")
    def text_query_all(self, text: str, indices: list[int] | None) -> list[str] | API.Err[None]:
        return self.query_text_all(text, indices)

    @deprecated("use `query_json`")
    def json_query(self, text: str, index: int) -> Any | API.Err[None]:
        return self.query_json(text, index)

    @deprecated("use `query_json_all`")
    def json_query_all(self, text: str, indices: list[int] | None) -> list[Any] | API.Err[None]:
        return self.query_json_all(text, indices)
    # ===== END: deprecations =================================================

    # ===== BEGIN: API patches ================================================
    # Note: patch load_file to raise/warn if the file is reloaded, since
    # this duplicates the document contents.
    @override
    def load_file(
            self,
            strict: bool = False,
    ) -> None | API.Err[API.RocqLoc | None]:
        if self._file_loaded:
            msg = f"reloading {self._file_path} duplicates document content"
            if strict:
                raise API.Error(msg)
            else:
                logger.warning(msg)
        return super().load_file()

    def quit(self) -> None:
        self._rpc.quit()

    # Note: patch insert_command since it is unsafe to
    # insert multiple commands without intervening blanks.
    @override
    def insert_command(
            self,
            text: str,
            blanks: str | None = "\n",
    ) -> API.CommandData | API.Err[API.CommandError]:
        insert_reply = super().insert_command(text)
        if isinstance(insert_reply, API.Err):
            return insert_reply
        if blanks is not None:
            if not re.match(r"\s+|\(\*.*\*\)", blanks):
                logger.warning(" ".join([
                    "blanks should be whitespace or Rocq comments:",
                    f"\"{blanks}\"",
                ]))
            self.insert_blanks(blanks)
        return insert_reply
    # ===== END: API patches ==================================================

    # ===== BEGIN: contextmanagers ============================================
    @contextmanager
    def sess(self, load_file: bool = True) -> Iterator[Self]:
        with self._rpc.sess():
            if load_file:
                load_reply = self.load_file()
                if isinstance(load_reply, API.Err):
                    raise API.Error(
                        f"RocqDocManager.load_file failed: {load_reply}"
                    )

            yield self

    @contextmanager
    def ctx(self, rollback: bool = True) -> Iterator[Self]:
        """Base RDM context manager supporting optional doc rollback."""
        current_idx: int = 0 # satisfies pyright.
        if rollback:
            current_idx = self.cursor_index()
            # NOTE: blanks are fused, so inserting blanks at the beginning
            # of a rollback context can leave the document in a modified state.
            # By inserting a real (but trivial) command that we rollback, we
            # ensure that the document is left unchanged.
            marker_cmd = "Check tt."
            insert_command_reply = self.insert_command(marker_cmd)
            if isinstance(insert_command_reply, API.Err):
                raise API.Error(" ".join([
                    f"RocqDocManager failed to insert {marker_cmd}:",
                    str(insert_command_reply),
                ]))

        yield self

        if rollback:
            revert_reply = self.revert_before(True, current_idx)
            if isinstance(revert_reply, API.Err):
                raise API.Error(" ".join([
                    "RocqDocManager failed to rollback to",
                    f"{current_idx}: {revert_reply}",
                ]))

    @contextmanager
    def aborted_goal_ctx(
            self,
            goal: str = "True",
            rollback: bool = True
    ) -> Iterator[Self]:
        """RDM context manager that sets up an aborted goal."""
        with self.ctx(rollback=rollback):
            goal_reply = self.insert_command(f"Goal {goal}.")
            if isinstance(goal_reply, API.Err):
                raise API.Error(goal_reply)

            yield self

            abort_reply = self.insert_command("Abort.")
            if isinstance(abort_reply, API.Err):
                raise API.Error(abort_reply)

    # NOTE: we could expose a more structured way to build the context list.
    @contextmanager
    def Section(
            self,
            name: str,
            context: list[str] | None = None,
            rollback: bool = False,
    ) -> Iterator[Self]:
        with self.ctx(rollback=rollback):
            begin_section_reply = self.insert_command(f"Section {name}.")
            if isinstance(begin_section_reply, API.Err):
                raise API.Error(begin_section_reply)

            if context is not None:
                context_reply = self.insert_command(
                    f"Context {' '.join(context)}."
                )
                if isinstance(context_reply, API.Err):
                    raise API.Error(context_reply)

            yield self

            end_section_reply = self.insert_command(f"End {name}.")
            if isinstance(end_section_reply, API.Err):
                raise API.Error(end_section_reply)
    # ===== END: contextmanagers ==============================================

    # ===== BEGIN: visitors ===================================================
    # TODOS:
    # - expose smarter and more efficient visitors (e.g. skipping
    #   non side-effecting proof sentences, batching visits, etc...)
    # - update rocq-doc-manager API to reflect that kind must be
    #   "command" or "blanks".
    def advance_to_first_match(
            self,
            fn: Callable[[str, str], bool],
            step_over_match: bool = False,
    ) -> bool:
        """Move to the first matching point. NOTE: proofs are not skipped."""
        prefix = self.doc_prefix()
        suffix = self.doc_suffix()

        candidate_prefix_matches = [
            (idx, item)
            for idx, item in enumerate(prefix)
            if fn(item.text, item.kind)
        ]
        candidate_suffix_matches = [
            (idx+len(prefix), item)
            for idx, item in enumerate(suffix)
            if fn(item.text, item.kind)
        ]

        def pretty_match_candidates(
                candidates: Sequence[
                    tuple[int, API.PrefixItem | API.SuffixItem]
                ],
        ) -> str:
            return "\n".join([
                f"\t- {item.text} of {item.kind} @ idx {idx}"
                for idx, item in candidates
            ])

        # 1a. fast pass: warn if the prefix contains candidate matches;
        # currently, we only advance through the suffix and ignore the prefix
        if candidate_prefix_matches:
            logger.warning("\n".join([
                "Candidate match(es) in the doc prefix are skipped:",
                pretty_match_candidates(candidate_prefix_matches),
                "",
            ]))

        # 1b. fast pass: return False if the suffix doesn't contain any matches
        if not candidate_suffix_matches:
            return False

        # 1c. fast pass: warn if the suffix contains multiple candidate
        # matches; currently we only use the first match
        match_idx, match_item = candidate_suffix_matches[0]
        pretty_match = (
            f"{match_item.text} of {match_item.kind} @ idx {match_idx}"
        )
        if len(candidate_suffix_matches) != 1:
            logger.warning("\n".join([
                f"Using first candidate match ({pretty_match}); skipping:",
                pretty_match_candidates(candidate_suffix_matches[1:]),
                "",
            ]))

        # 2. advance_to the match
        #
        # NOTE: proofs are not skipped
        advance_to_reply = self.advance_to(match_idx)
        if isinstance(advance_to_reply, API.Err):
            logger.warning(" ".join([
                f"Failed to advance to the match ({pretty_match}):",
                str(advance_to_reply),
            ]))
            return False

        if step_over_match:
            run_step_reply = self.run_step()
            if isinstance(run_step_reply, API.Err):
                logger.warning(
                    "Failed to step over the match: {run_step_repl}",
                )
                return False

        return True
    # ===== END: visitors =====================================================

    # ===== BEGIN: macros =====================================================
    def Compute(
            self,
            term: str,
            rollback: bool = True,
    ) -> tuple[str, str] | API.Err[API.CommandError] | API.Err[list[str]] | API.Err[None]:
        """Run [Compute {term}.] and return the resulting value and type.

        Arguments:
            - term (str): the term to compute
            - rollback (bool=True): whether to rollback the command

        Raises:
            - RocqDocManager.Error: if inserting the requested command fails

        Returns:
            - a tuple containing:
                - the computed value
                - the type of the computed value
        """
        with self.aborted_goal_ctx(
                goal=f"exists v, v = ({term})",
                rollback=rollback
        ):
            command_reply = self.insert_command("vm_compute.")
            if isinstance(command_reply, API.Err):
                return command_reply

            query_reply = self.query_text_all(
                """match goal with
| |- context[@ex ?TY (fun x => x = ?RESULT)] => idtac RESULT; idtac TY
end.""",
                indices=None,
            )
            if isinstance(query_reply, API.Err):
                return query_reply

            if len(query_reply) != 2:
                return API.Err(
                    message="RocqDocManager.Compute: expected a term and type",
                    data=query_reply
                )

            return (query_reply[0], query_reply[1])

    def current_goal(self) -> API.ProofState | None | API.Err[None]:
        result = self.query('About nat.')
        if isinstance(result, self.Err):
            return result
        return result.proof_state

    def _import_export_cmd(
            self,
            kind: Literal["Import"] | Literal["Export"],
            logpath: str,
            require: bool = True,
    ) -> API.CommandData | API.Err[API.CommandError]:
        cmd: str = f"{'Require ' if require else ''}{kind} {logpath}."
        return self.insert_command(cmd)

    def Import(
            self,
            logpath: str,
    ) -> API.CommandData | API.Err[API.CommandError]:
        return self._import_export_cmd("Import", logpath, require=False)

    def Export(
            self,
            logpath: str,
            require: bool = True,
    ) -> API.CommandData | API.Err[API.CommandError]:
        return self._import_export_cmd("Export", logpath, require=False)

    def RequireImport(
            self,
            logpath: str,
    ) -> API.CommandData | API.Err[API.CommandError]:
        return self._import_export_cmd("Import", logpath, require=True)

    def RequireExport(
            self,
            logpath: str,
            require: bool = True,
    ) -> API.CommandData | API.Err[API.CommandError]:
        return self._import_export_cmd("Export", logpath, require=True)

    def fresh_ident(self, ident: str) -> str | API.Err[None]:
        """Return a fresh name based on [ident].

        Arguments:
            - mgr (RocqDocManager): the document manager to send the request to
            - ident (str): the base for the fresh name

        Raises:
            - RocqDocManager.Error: if inserting the requested command fails.

        Returns:
            - a Rocq name which is guaranteed to be fresh at the
                  current loc. within [mgr]
        """
        return self.query_text(
            f"Eval lazy in ltac:(let nm := fresh \"{ident}\" in idtac nm).",
            0
        )
    # ===== END: macros =======================================================
