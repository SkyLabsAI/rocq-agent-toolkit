from jsonrpc_tp import Err

from .dune_util import dune_env_hack
from .rocq_doc_manager_api import RocqDocManagerAPI


class RocqDocManager(RocqDocManagerAPI):
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
                "dune", "exec", "--no-build", "--display=quiet",
                "rocq-doc-manager", "--", file_path,
                "--"
            ] + rocq_args
        else:
            args = ["rocq-doc-manager", file_path, "--"] + rocq_args
        super().__init__(args=args, cwd=chdir, env=env)

    def current_goal(self) -> str | Err[None]:
        result = self.run_command('idtac.')
        if isinstance(result, Err):
            return result
        index = self.cursor_index()
        self.revert_before(True, index)
        if isinstance(result.open_subgoals, str):
            return result.open_subgoals
        return Err("No goals available.", None)




