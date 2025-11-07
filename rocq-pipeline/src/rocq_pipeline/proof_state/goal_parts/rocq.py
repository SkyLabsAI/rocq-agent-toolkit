from dataclasses import dataclass, field
from typing import Protocol


@dataclass(frozen=True)
class RocqGoalParts:
    # --- Fields ---
    # Relative goal number
    rocq_rel_goal_num: int = field(kw_only=True)
    # Number of Rocq evars
    rocq_shelved_cnt: int | None = field(default=0, kw_only=True)
    # Rocq goal ID
    rocq_goal_id: int | None = field(kw_only=True)
    # Rocq hypotheses, of the form [<NAMES> : <TYPE>] -- where <NAMES>
    # is a comma-separated list of Rocq identifiers.
    rocq_hyps: dict[str, str] = field(default_factory=dict, kw_only=True)
    # Rocq definitions, of the form [<NAME> := <TERM>].
    rocq_defns: dict[str, str] = field(default_factory=dict, kw_only=True)
    # Rocq conclusion.
    rocq_concl: str = field(kw_only=True)

    def wellformed(self) -> bool:
        # NOTE: Rocq goals must have a conclusion; a goal of "True" or
        # "emp" is well-formed
        return self.rocq_rel_goal_num is not None and self.rocq_concl != ""


class into_GoalParts[GOAL_PARTS: RocqGoalParts](Protocol):
    def __call__(
        self,
        goal: str,
        rocq_goal_id: int | None = None,
        rocq_rel_goal_num: int | None = None,
        rocq_shelved_cnt: int | None = None,
        is_concl_only: bool = False,
        silent: bool = False,
    ) -> GOAL_PARTS:
        ...
