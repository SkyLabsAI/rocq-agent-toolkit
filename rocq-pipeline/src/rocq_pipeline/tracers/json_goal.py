import json
from pathlib import Path
from typing import Any, override

from rocq_doc_manager.rocq_doc_manager import RocqDocManager

from .extractor import StateExtractor


class JsonGoal(StateExtractor[list[Any]]):
    _RAW_PATH = "skylabs_ai.extractors.goal_to_json.basic.goal_util"
    _IRIS_PATH = "skylabs_ai.extractors.goal_to_json.iris.goal_util"

    @staticmethod
    def find_user_contrib(installed: bool=True) -> Path:
        cur = Path(__file__)
        while not (cur / "_build").exists():
            cur = cur.parent
        return cur /"_build"/"install"/"default"/"lib"/"coq"/"user-contrib"

    def _mod(self) -> str:
        return JsonGoal._IRIS_PATH if self._iris else JsonGoal._RAW_PATH

    def _tactic(self) -> str:
        return f"all: {self._mod()}.goal_to_json."

    def _check_iris(self, rdm: RocqDocManager) -> bool:
        result = rdm.text_query("Locate iris.proofmode.environments.envs_entails.", 0)
        assert not isinstance(result, RocqDocManager.Err)
        return not result.startswith("No object")

    @override
    def extra_paths(self) -> dict[str, Path]:
        return {"": self.find_user_contrib()}

    def start_proof(self, rdm: RocqDocManager) -> None:
        # Detect iris
        self._iris = self._check_iris(rdm)

        result = rdm.run_command(f"Require {self._mod()}.")
        if isinstance(result, RocqDocManager.Err):
            raise RuntimeError(f"Failed to initialize JsonGoal extractor: {result}")

    def __call__(self, rdm: RocqDocManager) -> list[Any] | None:
        result = rdm.text_query_all(self._tactic(), indices=None)
        if isinstance(result, rdm.Err):
            if "Init.Not_focussed" in result.message:
                return []
            print(f"got error, {result}")
            return None
        elif result == ['This subproof is complete, but there are some unfocused goals.\nTry unfocusing with "}".\n']:
            return []
        else:
            return [json.loads(goal) for goal in result]
