from dataclasses import dataclass

from .iris import IrisGoalParts


@dataclass(frozen=True)
class BrickGoalParts(IrisGoalParts):
    pass
