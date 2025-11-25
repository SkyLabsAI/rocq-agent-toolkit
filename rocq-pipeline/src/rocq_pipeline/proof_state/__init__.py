# ---------------------------------------------------------------------
# PROOF STATE
#
# A proof state consists of one or more (structured; heterogenous) goals.
# ---------------------------------------------------------------------
import copy
from typing import Any, overload

from rocq_pipeline.proof_state import parse
from rocq_pipeline.proof_state.goal import BrickGoal, IrisGoal, RocqGoal

__all__ = [
    "goal_parts",
    "RocqGoal",
    "IrisGoal",
    "BrickGoal",
    "ProofState",
]


class ProofState:
    """Structured proof states.

    A proof state is a heterogenous collection of structured goals (Rocq,
    Iris or Brick).

    NOTE: some proof state (evars, goal IDs) is not currently reflected in
    in the structured proof state.
    """

    def __init__(
        self,
        pf_state: str | None,
        # Use the new base class
        goal_ty_bound: type[RocqGoal] = RocqGoal,
    ) -> None:
        if pf_state is not None and not isinstance(pf_state, str):
            raise ValueError(" ".join([
                "Expected goal (str), but got",
                f"({type(pf_state)}) {pf_state}"
            ]))

        # Use the new base class
        if not issubclass(goal_ty_bound, RocqGoal):
            raise RuntimeError(f"{goal_ty_bound} not a subclass of RocqGoal")

        self._goal_ty_bound = goal_ty_bound
        self._goals: dict[int, RocqGoal] = (
            {}
            if pf_state is None else
            parse.into_Goals(pf_state, goal_ty_bound)
        )

    # NOTE: no [from_json], since ProofState stores class information in a
    # member variable.
    def to_json(self) -> dict[int, Any]:
        return {
            idx: goal.to_json()
            for idx, goal in self.goals.items()
        }

    def closed(self) -> bool:
        """Predicate indicating whether the proof state is fully closed."""
        return len(self._goals) == 0

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
