"""Hierarchy of immutable structured goal parts.

Goal parts form a hierarchy (Rocq -> Iris -> Brick), and derived
classes expose additional structural decompositions.
"""

# ---------------------------------------------------------------------
# DATACLASS (PARTS) DEFINITIONS
#
# These are the "data" part of the goals. They are frozen dataclasses
# that hold the parsed string components. The hierarchy is:
#   RocqGoalParts -> IrisGoalParts -> BrickGoalParts
# and clients can extend this hierarchy.
# ---------------------------------------------------------------------


from .brick import BrickGoalParts
from .iris import IrisGoalParts
from .rocq import RocqGoalParts, into_GoalParts

__all__ = [
    "into_GoalParts",
    "RocqGoalParts",
    "IrisGoalParts",
    "BrickGoalParts"
]
