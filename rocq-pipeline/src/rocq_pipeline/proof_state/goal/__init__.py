"""Hierarchy of structured goals.

Structured goals form a hierarchy (Rocq -> Iris -> Brick) and consist
of immutable [goal_parts]. They may contain mutable state and expose
utilities for interacting with structured goals of a given kind.
"""

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
