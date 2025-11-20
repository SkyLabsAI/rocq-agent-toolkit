from collections.abc import Iterator
from contextlib import contextmanager
from typing import Literal, Self, override

from .dune_util import dune_env_hack
from .rocq_doc_manager_api import RocqDocManagerAPI as API


class RocqDocManager(API):
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
        super().__init__(args=args, cwd=chdir, env=env)

    # Note: patch insert_command since it is unsafe to
    # insert multiple commands without intervening blanks.
    @override
    def insert_command(
            self,
            text: str,
            blanks: str | None = "\n",
    ) -> API.CommandData | API.Err[API.RocqLoc | None]:
        insert_reply = super().insert_command(text)
        if isinstance(insert_reply, API.Err):
            return insert_reply
        if blanks is not None:
            self.insert_blanks(blanks)
        return insert_reply

    @contextmanager
    @override
    def sess(self, load_file: bool = True) -> Iterator[Self]:
        with super().sess():
            if load_file:
                load_reply = self.load_file()
                if isinstance(load_reply, RocqDocManager.Err):
                    raise self.Error(
                        f"RocqDocManager.load_file failed: {load_reply}"
                    )

            yield self

    @contextmanager
    def ctx(self, rollback: bool = True) -> Iterator[Self]:
        """Base RDM context manager supporting optional doc rollback."""
        if rollback:
            current_idx: int = self.cursor_index()
            # NOTE: blanks are fused, so inserting blanks at the beginning
            # of a rollback context can leave the document in a modified state.
            # By inserting a real (but trivial) command that we rollback, we
            # ensure that the document is left unchanged.
            marker_cmd = "Check tt."
            insert_command_reply = self.insert_command(marker_cmd)
            if isinstance(insert_command_reply, RocqDocManager.Err):
                raise self.Error(" ".join([
                    f"RocqDocManager failed to insert {marker_cmd}:",
                    str(insert_command_reply),
                ]))

        yield self

        if rollback:
            revert_reply = self.revert_before(True, current_idx)
            if isinstance(revert_reply, RocqDocManager.Err):
                raise self.Error(" ".join([
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
            if isinstance(goal_reply, self.Err):
                raise self.Error(goal_reply)

            yield self

            abort_reply = self.insert_command("Abort.")
            if isinstance(abort_reply, self.Err):
                raise self.Error(abort_reply)

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
            if isinstance(begin_section_reply, self.Err):
                raise self.Error(begin_section_reply)

            if context is not None:
                context_reply = self.insert_command(
                    f"Context {' '.join(context)}."
                )
                if isinstance(context_reply, self.Err):
                    raise self.Error(context_reply)

            yield self

            end_section_reply = self.insert_command(f"End {name}.")
            if isinstance(end_section_reply, self.Err):
                raise self.Error(end_section_reply)

    def Compute(
            self,
            term: str,
            rollback: bool = True,
    ) -> tuple[str, str] | API.Err[API.RocqLoc | None] | API.Err[list[str]] | API.Err[None]:
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
            if isinstance(command_reply, self.Err):
                return command_reply

            query_reply = self.text_query_all(
                """match goal with
| |- context[@ex ?TY (fun x => x = ?RESULT)] => idtac RESULT; idtac TY
end.""",
                indices=None,
            )
            if isinstance(query_reply, self.Err):
                return query_reply

            if len(query_reply) != 2:
                return self.Err(
                    message="RocqDocManager.Compute: expected a term and type",
                    data=query_reply
                )

            return (query_reply[0], query_reply[1])

    def current_goal(self) -> str | API.Err[None]:
        result = self.run_command('idtac.')
        if isinstance(result, self.Err):
            return result
        index = self.cursor_index()
        self.revert_before(True, index)
        if isinstance(result.open_subgoals, str):
            return result.open_subgoals
        return self.Err("No goals available.", None)

    def _import_export_cmd(
            self,
            kind: Literal["Import"] | Literal["Export"],
            logpath: str,
            require: bool = True,
    ) -> API.CommandData | API.Err[API.RocqLoc | None]:
        cmd: str = f"{'Require ' if require else ''}{kind} {logpath}."
        return self.insert_command(cmd)

    def Import(
            self,
            logpath: str,
    ) -> API.CommandData | API.Err[API.RocqLoc | None]:
        return self._import_export_cmd("Import", logpath, require=False)

    def Export(
            self,
            logpath: str,
            require: bool = True,
    ) -> API.CommandData | API.Err[API.RocqLoc | None]:
        return self._import_export_cmd("Export", logpath, require=False)

    def RequireImport(
            self,
            logpath: str,
    ) -> API.CommandData | API.Err[API.RocqLoc | None]:
        return self._import_export_cmd("Import", logpath, require=True)

    def RequireExport(
            self,
            logpath: str,
            require: bool = True,
    ) -> API.CommandData | API.Err[API.RocqLoc | None]:
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
        return self.text_query(
            f"Eval lazy in ltac:(let nm := fresh \"{ident}\" in idtac nm).",
            0
        )
