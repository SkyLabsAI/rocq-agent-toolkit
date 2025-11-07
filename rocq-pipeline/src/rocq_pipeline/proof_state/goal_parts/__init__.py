# ---------------------------------------------------------------------
# DATACLASS (PARTS) DEFINITIONS
#
# These are the "data" part of the goals. They are frozen dataclasses
# that hold the parsed string components. The hierarchy is:
#   RocqGoalParts -> IrisGoalParts -> BrickGoalParts
# and clients can extend this hierarchy.
# ---------------------------------------------------------------------


from .rocq import into_GoalParts, RocqGoalParts
from .iris import IrisGoalParts
from .brick import BrickGoalParts

__all__ = [
    "into_GoalParts",
    "RocqGoalParts",
    "IrisGoalParts",
    "BrickGoalParts"
]
