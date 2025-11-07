# ---------------------------------------------------------------------
# PROOF STATE
#
# A proof state consists of one or more (structured; heterogenous) goals.
# ---------------------------------------------------------------------
import copy
from typing import overload

from rocq_pipeline.proof_state.goal import RocqGoal, IrisGoal, BrickGoal
from rocq_pipeline.proof_state import parse

__all__ = [
    "goal_parts",
    "RocqGoal",
    "IrisGoal",
    "BrickGoal",
    "ProofState",
]


class ProofState:
    def __init__(
        self,
        pf_state_str: str,
        # Use the new base class
        goal_ty_bound: type[RocqGoal] = RocqGoal,
    ) -> None:
        if not isinstance(pf_state_str, str):
            raise ValueError(" ".join([
                "Expected goal (str), but got",
                f"({type(pf_state_str)}) {pf_state_str}"
            ]))

        # Use the new base class
        if not issubclass(goal_ty_bound, RocqGoal):
            raise RuntimeError(f"{goal_ty_bound} not a subclass of RocqGoal")

        self._goal_ty_bound = goal_ty_bound
        self._goals: dict[int, RocqGoal] = parse.into_Goals(
            pf_state_str,
            goal_ty_bound
        )

    @property
    def goals(self) -> dict[int, RocqGoal]:
        return copy.deepcopy(self._goals)

    @overload
    def goal[Goal_T: RocqGoal](
            self,
            idx: int = 1,
            *,
            strict: bool = True,
            cast_to: type[Goal_T]
    ) -> Goal_T | None:
        """
        Gets a specific goal and casts it to the requested type.
        - If strict=True: Raises KeyError if not found, TypeError if wrong type.
        - If strict=False: Returns None if not found or wrong type.
        """
        ...

    @overload
    def goal[Goal_T: RocqGoal](
            self,
            idx: int = 1,
            *,
            strict: bool = True,
            cast_to: None = None
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
        g = self._goals.get(idx)

        # 1. Handle goal not found
        if g is None:
            if strict:
                raise KeyError(" ".join([
                    f"No goal found with index {idx}.",
                    f"Found: {self._goals.keys()}",
                ]))
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
