import json
from pathlib import Path
from typing import Any

from rocq_doc_manager import RocqCursor

from ..proof_state import ProofState
from ..proof_state.goal import RocqGoal
from .extractor import DocumentWatcher, TacticExtractor


class JsonGoal(
    DocumentWatcher, TacticExtractor[None, tuple[list[Any] | None, list[Any] | None]]
):
    _RAW_PATH = "skylabs_ai.extractors.goal_to_json.basic.goal_util"
    _IRIS_PATH = "skylabs_ai.extractors.goal_to_json.iris.goal_util"

    def __init__(self, iris: bool | None = None, minimize_diff: bool = False):
        self._iris: bool | None = iris
        self._minimize_diff = minimize_diff
        self._preGoals: tuple[dict[int, RocqGoal], list[str] | None] | None = None

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
        result = rdm.query_text(
            "Locate iris.proofmode.environments.envs_entails.", index=0
        )
        assert not isinstance(result, RocqCursor.Err)
        return not result.startswith("No object")

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

    def setup(self, rdm: RocqCursor) -> None:
        pass

    def start_proof(self, rdm: RocqCursor) -> None:
        # Detect iris
        if self._iris is None:
            self._iris = self._check_iris(rdm)

        result = rdm.run_command(f"Require {self._mod()}.")
        if isinstance(result, RocqCursor.Err):
            raise Exception(f"Failed to initialize JsonGoal extractor: {result}")

    def end_proof(self, rdm: RocqCursor) -> None:
        pass

    _NO_GOAL_PREFIXES: list[str] = [
        "This subproof is complete, but there are some unfocused goals.",
        "No more goals",
        "All the remaining goals are on the shelf",
    ]

    def get_goals(self, rdm: RocqCursor) -> list[str] | None:
        result = rdm.query_text_all(self._tactic(), indices=None)
        if isinstance(result, rdm.Err):
            if "Init.Not_focussed" in result.message:
                return []
            return None
        elif len(result) == 1 and any(
            result[0].startswith(x) for x in self._NO_GOAL_PREFIXES
        ):
            # TODO: 'All the remaining goals are on the shelf'
            return []
        else:
            return result

    def before(self, rdm: RocqCursor, tactic: str) -> None:
        result = self.get_goals(rdm)
        self._preGoals = (ProofState(rdm.current_goal()).goals, result)

    def after(
        self, rdm: RocqCursor, tactic: str
    ) -> tuple[list[Any] | None, list[Any] | None]:
        result = self.get_goals(rdm)
        goals = ProofState(rdm.current_goal()).goals

        assert self._preGoals is not None
        preGoals, preResult = self._preGoals

        if self._minimize_diff:
            changed = set()
            new = set(goals.keys())
            for preIdx, preGoal in preGoals.items():
                preParts = preGoal.parts
                found = False
                for idx, goal in goals.items():
                    if preParts.equal_up_to_numbering(goal.parts):
                        found = True
                        new.remove(idx)
                        break
                if not found:
                    changed.add(preIdx)

            if len(changed) == 1 and preResult is not None and result is not None:
                preResult = [preResult[preIdx - 1] for preIdx in changed]
                result = [result[idx - 1] for idx in new]

        preResult = (
            [json.loads(goal) for goal in preResult] if preResult is not None else None
        )
        result = [json.loads(goal) for goal in result] if result is not None else None

        return (preResult, result)
