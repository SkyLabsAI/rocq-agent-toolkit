"""String based parsing for constructing [goal_parts].

[into_goals] takes the string for a proof state and returns
a dictionary containing mapping relative goal indexes to the
most specific [goal_parts] possible.

TODO: Replace this string-based parsing with Ltac2 utilities.
"""

from .rocq import into_RocqGoalParts
from .iris import into_IrisGoalParts, Rocq2IrisGoalParts
from .brick import (
    into_BrickGoalParts,
    Rocq2BrickGoalParts,
    Iris2BrickGoalParts
)
from .proof_state import into_Goals


__all__ = [
    "into_Goals",

    "into_RocqGoalParts",

    "into_IrisGoalParts",
    "Rocq2IrisGoalParts",

    "into_BrickGoalParts",
    "Rocq2BrickGoalParts",
    "Iris2BrickGoalParts",
]
