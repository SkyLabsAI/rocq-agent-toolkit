"""String based parsing for constructing [goal_parts].

[into_goals] takes the string for a proof state and returns
a dictionary containing mapping relative goal indexes to the
most specific [goal_parts] possible.

TODO: Replace this string-based parsing with Ltac2 utilities.
"""

# NOTE: because [RocqGoal -> IrisGoal -> BrickGoal], it is
# important that we import them in this order and /not/
# alphabetical order.
from .rocq import into_RocqGoalParts  # isort:skip
from .iris import Rocq2IrisGoalParts, into_IrisGoalParts  # isort:skip
from .brick import (  # isort:skip
    Iris2BrickGoalParts,
    Rocq2BrickGoalParts,
    into_BrickGoalParts,
)

# TODO: remove str_into_Goals
from .proof_state import str_into_Goal  # isort:skip

__all__ = [
    "str_into_Goal",
    "str_into_Goals",
    "into_RocqGoalParts",
    "into_IrisGoalParts",
    "Rocq2IrisGoalParts",
    "into_BrickGoalParts",
    "Rocq2BrickGoalParts",
    "Iris2BrickGoalParts",
]
