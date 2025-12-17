from dataclasses import asdict, dataclass, field
from functools import cached_property
from typing import Any, Protocol


@dataclass(frozen=True)
class RocqGoalParts:
    """Structured parts of a single Rocq goal.

    This is a frozen dataclass; member functions should only be
    const helpers for working with the structured data.
    """

    # --- Fields ---
    rocq_goal_raw: str = field(kw_only=True)
    # Relative goal number
    rocq_rel_goal_num: int = field(default=1, kw_only=True)
    # Number of Rocq evars
    rocq_shelved_cnt: int = field(default=0, kw_only=True)
    # Number of Rocq evars that have been given up on (i.e. `admit`ted)
    rocq_admit_cnt: int = field(default=0, kw_only=True)
    # Rocq goal ID
    rocq_goal_id: int | None = field(kw_only=True)
    # Rocq hypotheses: idents map to a type and an optional definition
    rocq_hyps: dict[str, tuple[str, str | None]] = field(
        default_factory=dict, kw_only=True
    )
    # Rocq conclusion.
    rocq_concl: str = field(kw_only=True)

    def wellformed(self) -> bool:
        # NOTE: Rocq goals must have a conclusion; a goal of "True" or
        # "emp" is well-formed
        return self.rocq_rel_goal_num is not None and self.rocq_concl != ""

    def to_json(self) -> dict[str, Any]:
        return asdict(self)


class into_GoalParts[GOAL_PARTS: RocqGoalParts](Protocol):
    def __call__(
        self,
        goal: str,
        *,
        rocq_rel_goal_num: int,
        rocq_shelved_cnt: int,
        rocq_admit_cnt: int,
        rocq_goal_id: int | None = None,
        is_concl_only: bool = False,
        silent: bool = False,
    ) -> GOAL_PARTS: ...
