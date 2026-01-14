# ---------------------------------------------------------------------
# PROOF STATE
#
# A proof state consists of one or more (structured; heterogenous) goals.
# ---------------------------------------------------------------------
import copy
import logging
from typing import Any, overload

from rocq_doc_manager import RocqDocManager as RDM

from rocq_pipeline.proof_state import parse
from rocq_pipeline.proof_state.goal import IrisGoal, RocqGoal

__all__ = [
    "goal_parts",
    "RocqGoal",
    "IrisGoal",
    "ProofState",
]

logger = logging.getLogger(__name__)


class ProofState:
    """Structured proof states.

    A proof state is a heterogenous collection of structured goals (Rocq,
    Iris or client extensions). This is a derivation atop
    RocqDocManager.ProofState exposing a structured / hierarchical view of
    the focused goals.
    """

    def __init__(
        self,
        pf_state: RDM.ProofState | None,
        goal_ty_upperbound: type[RocqGoal] = RocqGoal,
    ) -> None:
        if pf_state is not None and not isinstance(pf_state, RDM.ProofState):
            raise ValueError(
                " ".join(
                    [
                        "Expected goal (ProofState | None), but got",
                        f"({type(pf_state)}) {pf_state}",
                    ]
                )
            )

        # Use the new base class
        if not issubclass(goal_ty_upperbound, RocqGoal):
            raise RuntimeError(f"{goal_ty_upperbound} not a subclass of RocqGoal")

        self._goal_ty_upperbound = goal_ty_upperbound

        # Note: we additionally track shelved_cnt and admit_cnt in each goal
        # for the purposes of printing and local queries.
        self._shelved_cnt: int = 0
        self._admit_cnt: int = 0
        self._unfocused_goals: list[int] = []
        self._focused_goals: dict[int, RocqGoal] = {}

        # TODO: simplify this once we fully move away from whole proof state strings
        if pf_state is not None:
            self._shelved_cnt = pf_state.shelved_goals
            self._admit_cnt = pf_state.given_up_goals

            # NOTE: we avoid making a shallow copy because `RDM.ProofState` is a frozen
            # dataclass; in the `unfocused_goals` property below we return a shallow
            # copy.
            self._unfocused_goals = pf_state.unfocused_goals

            # NOTE: start at rel_goal_num=1, since Rocq goals are 1-indexed
            for rel_goal_num, focused_goal_str in enumerate(
                pf_state.focused_goals,
                start=1,
            ):
                self._focused_goals[rel_goal_num] = parse.str_into_Goal(
                    focused_goal_str,
                    goal_ty_upperbound=self._goal_ty_upperbound,
                    rocq_rel_goal_num=rel_goal_num,
                    rocq_shelved_cnt=self._shelved_cnt,
                    rocq_admit_cnt=self._admit_cnt,
                    # NOTE: we don't get this from RocqDocManager.ProofState
                    rocq_goal_id=None,
                )

    def __str__(self) -> str:
        total_goals = len(self.goals) + len(self.unfocused_goals)
        goals_plural: bool = 1 < total_goals
        header_total_goals = f"{total_goals} Goal{'s' if goals_plural else ''} Total"
        header_goals_info = "; ".join(
            [
                f"{len(self.goals)} focused",
                f"{len(self.unfocused_goals)} unfocused ({self.unfocused_goals})",
                f"{self.shelved_cnt} shelved",
                f"{self.admit_cnt} admitted",
            ]
        )
        header = f"{header_total_goals}\n\t{header_goals_info}\n\n"
        return header + "\n\n".join(g.parts.rocq_goal_raw for g in self.goals.values())

    # NOTE: no [from_json], since ProofState stores class information in a
    # member variable.
    def to_json(self) -> dict[str, Any]:
        return {
            "focused_goals": {idx: goal.to_json() for idx, goal in self.goals.items()},
            "unfocused_goals": self.unfocused_goals,
            "shelved_cnt": self.shelved_cnt,
            "admit_cnt": self.admit_cnt,
        }

    def closed(self, proof: bool = False) -> bool:
        """Predicate indicating whether the focused goals are fully closed.

        Note: if proof=True, return False if any shelved/admitted remain."""
        if len(self._focused_goals) != 0:
            return False

        if proof:
            return (
                len(self._unfocused_goals) == 0
                and self._shelved_cnt == 0
                and self._admit_cnt == 0
            )
        else:
            return True

    @property
    def goal_ty_upperbound(self) -> type[RocqGoal]:
        """The upperbound for the type of constituent goals."""
        return self._goal_ty_upperbound

    @property
    def shelved_cnt(self) -> int:
        """The number of shelved goals in the current proof state."""
        return self._shelved_cnt

    @property
    def admit_cnt(self) -> int:
        """The number of admitted goals in the current proof state."""
        return self._admit_cnt

    @property
    def unfocused_goals(self) -> list[int]:
        """The stack of indices corresponding to unfocused goals."""
        return self._unfocused_goals[:]

    @property
    def goals(self) -> dict[int, RocqGoal]:
        """Mapping from (focused) goal index to structured goal contents.

        Note: individual goals are upper-bounded by [goal_ty_upperbound]."""
        return copy.deepcopy(self._focused_goals)

    @overload
    def goal[Goal_T: RocqGoal](
        self, idx: int = 1, *, strict: bool = True, cast_to: type[Goal_T]
    ) -> Goal_T | None:
        """
        Gets a specific goal and casts it to the requested type.
        - If strict=True: Raises KeyError if not found, TypeError if wrong type.
        - If strict=False: Returns None if not found or wrong type.
        """
        ...

    @overload
    def goal[Goal_T: RocqGoal](
        self, idx: int = 1, *, strict: bool = True, cast_to: None = None
    ) -> RocqGoal | None:
        """
        Gets a specific goal, returning it as the base RocqGoal.
        - If strict=True: Raises KeyError if not found.
        - If strict=False: Returns None if not found.
        """
        ...

    def goal[Goal_T: RocqGoal](
        self,
        idx: int = 1,
        *,
        strict: bool = True,
        cast_to: type[Goal_T] | None = None,
    ) -> Goal_T | RocqGoal | None:
        g = self._focused_goals.get(idx)

        # 1. Handle goal not found
        if g is None:
            if strict:
                raise KeyError(
                    " ".join(
                        [
                            f"No goal found with index {idx}.",
                            f"Found: {self._focused_goals.keys()}",
                        ]
                    )
                )
            return None

        # 2. Handle type checking/casting
        if cast_to:
            if isinstance(g, cast_to):
                return g  # Success: it's the type (or subtype) requested

            # Type mismatch:
            if strict:
                raise TypeError(
                    f"Goal {idx} is of type {type(g).__name__}, "
                    f"not the requested type {cast_to.__name__}"
                )
            else:
                return None  # Non-strict: return None on type mismatch

        # 3. No cast_to: return the goal as is
        return g
