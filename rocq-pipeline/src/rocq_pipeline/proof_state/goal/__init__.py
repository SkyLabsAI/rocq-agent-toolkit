# ---------------------------------------------------------------------
# GOAL WRAPPER DEFINITIONS
#
# These are the "behavior" part of the goals. They wrap the 'Parts'
# dataclasses and provide a common interface and potential methods.
# The hierarchy is:
#   RocqGoal -> IrisGoal -> BrickGoal
# and clients can extend this hierarchy.
# ---------------------------------------------------------------------

from .rocq import RocqGoal
from .iris import IrisGoal
from .brick import BrickGoal

__all__ = [
    "RocqGoal",
    "IrisGoal",
    "BrickGoal",
]
