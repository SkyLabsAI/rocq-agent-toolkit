# TODO: Replace this string-based parsing with OCaml tooling.
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
