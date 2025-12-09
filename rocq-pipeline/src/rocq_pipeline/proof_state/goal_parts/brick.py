from dataclasses import dataclass

from .iris import IrisGoalParts


@dataclass(frozen=True)
class BrickGoalParts(IrisGoalParts):
    """Structured parts of a single Brick goal.

    This is a frozen dataclass; member functions should only be
    const helpers for working with the structured data.
    """

    pass
