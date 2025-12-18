import json
from pathlib import Path
from typing import Any, override

from rocq_doc_manager import RocqCursor

from .extractor import StateExtractor


class JsonGoal(StateExtractor[list[Any]]):
    _RAW_PATH = "skylabs_ai.extractors.goal_to_json.basic.goal_util"
    _IRIS_PATH = "skylabs_ai.extractors.goal_to_json.iris.goal_util"

    def __init__(self, iris: bool | None = None):
        self._iris: bool | None = iris

    @staticmethod
    def find_user_contrib(installed: bool = True) -> Path:
        cur = Path(__file__)
        while not (cur / "_build").exists():
            cur = cur.parent
        return cur / "_build" / "install" / "default" / "lib" / "coq" / "user-contrib"

    def _mod(self) -> str:
        return JsonGoal._IRIS_PATH if self._iris else JsonGoal._RAW_PATH

    def _tactic(self) -> str:
        return f"all: {self._mod()}.goal_to_json."

    def _check_iris(self, rdm: RocqCursor) -> bool:
        result = rdm.query_text("Locate iris.proofmode.environments.envs_entails.", 0)
        assert not isinstance(result, RocqCursor.Err)
        return not result.startswith("No object")

    @override
    def extra_paths(self) -> dict[str, Path]:
        user = self.find_user_contrib()

        def ext(path: Path, ls: list[str]) -> Path:
            for x in ls:
                path = path / x
            return path

        PATHS = [
            "skylabs_ai.extractors.goal_to_json",
            "skylabs_ai.ltac2_json",
            "skylabs_ai.ltac2_derive",
            "skylabs.ltac2.extra",
        ]
        return {k: ext(user, k.split(".")) for k in PATHS}

    def start_proof(self, rdm: RocqCursor) -> None:
        # Detect iris
        if self._iris is None:
            self._iris = self._check_iris(rdm)

        result = rdm.run_command(f"Require {self._mod()}.")
        if isinstance(result, RocqCursor.Err):
            raise RuntimeError(f"Failed to initialize JsonGoal extractor: {result}")

    _NO_GOAL_PREFIXES: list[str] = [
        "This subproof is complete, but there are some unfocused goals.",
        "No more goals",
        "All the remaining goals are on the shelf",
    ]

    def __call__(self, rdm: RocqCursor) -> list[Any] | None:
        result = rdm.query_text_all(self._tactic(), indices=None)
        if isinstance(result, rdm.Err):
            if "Init.Not_focussed" in result.message:
                return []
            return None
        elif len(result) == 1 or any(
            result[0].startswith(x) for x in self._NO_GOAL_PREFIXES
        ):
            # TODO: 'All the remaining goals are on the shelf'
            return []
        else:
            try:
                return [json.loads(goal) for goal in result]
            except ValueError as err:
                raise ValueError(f"bad value in {result}") from err
