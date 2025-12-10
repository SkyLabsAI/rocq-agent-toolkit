import re
from typing import cast, override

from rocq_pipeline.proof_state.goal import IrisGoal
from rocq_pipeline.proof_state.goal_parts import BrickGoalParts


def head_ast(s: str, constructs: list[str]) -> bool:
    for ast in constructs:
        if re.search(
            rf"::wpS\s+\[.*?\]\s+\({ast}",
            s,
            re.DOTALL,  # "." should match everything, including newlines
        ):
            return True
    return False


class BrickGoal(IrisGoal):
    """Single Brick goal, consisting of structured goal parts.

    This class may contain mutable state and should collect
    all utilities that can be expressed at the level of structured
    Iris goals.
    """

    # Override the PartsDataclass to point to the Brick version
    PartsDataclass: type[BrickGoalParts] = BrickGoalParts

    @property
    @override
    def parts(self) -> BrickGoalParts:
        # Override property for correct type hinting
        return cast(BrickGoalParts, self._parts)

    def is_loop_goal(self) -> bool:
        """
        Checks if the spatial conclusion contains a loop AST node.
        """
        return head_ast(self.parts.iris_spat_concl, ["Sdo_while", "Sfor", "Swhile"])

    def is_conditional_goal(self) -> bool:
        """
        Checks if the spatial conclusion contains a 'if' AST node.
        """
        return head_ast(self.parts.iris_spat_concl, ["Sif"])
