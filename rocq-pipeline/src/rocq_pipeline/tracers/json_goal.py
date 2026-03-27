import json
from pathlib import Path
from typing import Any

from pydantic import JsonValue
from rocq_doc_manager import RocqCursor
from rocq_doc_manager import rocq_doc_manager_api as rdm_api
from rocq_dune_util import DuneRocqPlugin

# from rocq_pipeline.proof_state import ProofState
# from rocq_pipeline.proof_state.goal import RocqGoal
from rocq_pipeline.with_deps import UsingRocqDeps

from .extractor import (
    BracketedExtractor,
    DefaultDocumentWatcher,
    Extracted,
    ExtractorResult,
    OutputDict,
    Skip,
)

type output = list[Any] | None
# type goals = dict[int, RocqGoal]  # 1-indexed
type results = list[str] | None
type state = tuple[rdm_api.ProofState, results]


def goal_diff(
    preGoals: rdm_api.ProofState, postGoals: rdm_api.ProofState | None
) -> tuple[set[int], set[int]]:  # result sets are 1-indexed
    """
    Given an initial set of goals, return the sets of changed goals
    and new goals.
    """
    if postGoals is None:
        return (set(range(0, len(preGoals.focused_goals))), set())

    changed = set()
    new = set(range(0, len(postGoals.focused_goals)))
    for preIdx, preGoal in enumerate(preGoals.focused_goals):
        for idx, goal in enumerate(postGoals.focused_goals):
            if preGoal == goal:
                new.remove(idx)
                break
        else:
            # Runs if the loop does not break
            changed.add(preIdx)
    return (changed, new)


class JsonGoal(
    DefaultDocumentWatcher,
    BracketedExtractor[state, OutputDict[JsonValue]],
    UsingRocqDeps,
):
    _RAW_PATH = "skylabs_ai.extractors.goal_to_json.basic.goal_util"
    _IRIS_PATH = "skylabs_ai.extractors.goal_to_json.iris.goal_util"

    def __init__(self, iris: bool | None = None, by_goal: bool = False):
        self._iris: bool | None = iris
        self._by_goal = by_goal

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

    async def _check_iris(self, rc: RocqCursor) -> bool:
        result = await rc.query_text(
            "Locate iris.proofmode.environments.envs_entails.", index=0
        )
        assert not isinstance(result, rdm_api.Err)
        return not result.startswith("No object")

    def rocq_deps(self) -> list[DuneRocqPlugin]:
        return [
            DuneRocqPlugin(
                opam_pkg="rocq-goal-to-json",
                entry_points=["basic/theories/goal_util.v"],
            ),
            DuneRocqPlugin(
                opam_pkg="rocq-goal-to-json_iris",
                entry_points=["iris/theories/goal_util.v"],
            ),
        ]

    async def start_proof(self, rc: RocqCursor) -> None:
        # Detect iris
        if self._iris is None:
            self._iris = await self._check_iris(rc)

        result = await rc.run_command(f"Require {self._mod()}.")
        if isinstance(result, rdm_api.Err):
            raise Exception(f"Failed to initialize JsonGoal extractor: {result}")

    _NO_GOAL_PREFIXES: list[str] = [
        "This subproof is complete, but there are some unfocused goals.",
        "No more goals",
        "All the remaining goals are on the shelf",
    ]

    async def get_goals(self, rc: RocqCursor) -> list[str] | None:
        result = await rc.query_text_all(self._tactic(), indices=None)
        if isinstance(result, rdm_api.Err):
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

    @staticmethod
    def supported_tactic(tactic: str) -> bool:
        tactic = tactic.strip()
        # TODO: ask the tagger if the tactic starts with a goal selector
        return tactic.endswith(".") or tactic in ["{", "}"]

    async def before(self, rc: RocqCursor, tactic: str) -> ExtractorResult:
        if not self.supported_tactic(tactic):
            return Skip()
        result = await self.get_goals(rc)
        return Extracted((await rc.current_goal(), result))

    async def after(
        self,
        rc: RocqCursor,
        tactic: str,
        result_before: state,
    ) -> OutputDict[JsonValue]:
        result = await self.get_goals(rc)
        goals = await rc.current_goal()

        preGoals, preResult = result_before

        if self._by_goal:
            (changed, new) = goal_diff(preGoals, goals)
            if len(changed) == 1 and preResult is not None and result is not None:
                preResult = [preResult[preIdx - 1] for preIdx in changed]
                result = [result[idx - 1] for idx in new]

        preGoalsX: list[JsonValue] = (
            [json.loads(goal) for goal in preResult] if preResult is not None else []
        )
        postGoals: list[JsonValue] = (
            [json.loads(goal) for goal in result] if result is not None else []
        )

        return {"before": preGoalsX, "after": postGoals}


def build_by_goal() -> JsonGoal:
    return JsonGoal(by_goal=True)


def build_full_state() -> JsonGoal:
    return JsonGoal(by_goal=False)


def build() -> JsonGoal:
    return build_by_goal()
