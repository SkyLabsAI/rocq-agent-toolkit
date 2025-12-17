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

    @cached_property
    def rocq_goal_raw(self) -> str:
        header = f"Goal {self.rocq_rel_goal_num}"
        if self.rocq_shelved_cnt is not None:
            header += f" ({self.rocq_shelved_cnt} Shelved)"
        if self.rocq_goal_id is not None:
            header += " (ID: self.rocq_goal_id)"

        hypotheses = "\n".join(
            f"{nm} : {ty}" + ("" if defn is None else f" := {defn}")
            for nm, (ty, defn) in self.rocq_hyps.items()
        )

        separator = "=" * 28

        return f"{header}\n\n{hypotheses}\n{separator}\n{self.rocq_concl}"

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
