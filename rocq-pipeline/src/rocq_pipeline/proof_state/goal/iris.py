from typing import cast, override
from rocq_pipeline.proof_state.goal import RocqGoal
from rocq_pipeline.proof_state.goal_parts import IrisGoalParts


class IrisGoal(RocqGoal):
    """Single Iris goal, consisting of structured goal parts.

    This class may contain mutable state and should collect
    all utilities that can be expressed at the level of structured
    Iris goals.
    """

    # Override the PartsDataclass to point to the Iris version
    PartsDataclass: type[IrisGoalParts] = IrisGoalParts

    @property
    @override
    def parts(self) -> IrisGoalParts:
        # Override property for correct type hinting
        return cast(IrisGoalParts, self._parts)
