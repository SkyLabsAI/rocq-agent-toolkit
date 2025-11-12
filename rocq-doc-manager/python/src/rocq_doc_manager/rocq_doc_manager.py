from .rocq_doc_manager_api import RocqDocManagerAPI
from .rocq_doc_manager_raw import Err


class RocqDocManager(RocqDocManagerAPI):
    def current_goal(self) -> str | Err[None]:
        result = self.run_command('idtac.')
        if isinstance(result, Err):
            return result
        index = self.cursor_index()
        self.revert_before(True, index)
        if isinstance(result.open_subgoals, str):
            return result.open_subgoals
        return Err("No goals available.", None)
