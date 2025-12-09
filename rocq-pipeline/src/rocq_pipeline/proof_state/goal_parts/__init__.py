"""Hierarchy of immutable structured goal parts.

Goal parts form a hierarchy (Rocq -> Iris -> Brick), and derived
classes expose additional structural decompositions.
"""

# ---------------------------------------------------------------------
# DATACLASS (PARTS) DEFINITIONS
#
# These are the "data" part of the goals. They are frozen dataclasses
# that hold the parsed string components. The hierarchy (from base to
# derived) is:
#   RocqGoalParts -> IrisGoalParts -> BrickGoalParts
# and clients can extend this hierarchy.
# ---------------------------------------------------------------------

# NOTE: because [RocqGoal -> IrisGoal -> BrickGoal], it is
# important that we import them in this order and /not/
# alphabetical order.
from rocq_pipeline.proof_state.goal_parts.rocq import (  # isort:skip
    RocqGoalParts,
    into_GoalParts,
)
from rocq_pipeline.proof_state.goal_parts.iris import (  # isort:skip
    IrisGoalParts,
)
from rocq_pipeline.proof_state.goal_parts.brick import (  # isort:skip
    BrickGoalParts,
)


__all__ = ["into_GoalParts", "RocqGoalParts", "IrisGoalParts", "BrickGoalParts"]
