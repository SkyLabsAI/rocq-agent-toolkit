import re

from typing import cast, override
from rocq_pipeline.proof_state.goal import IrisGoal
from rocq_pipeline.proof_state.goal_parts import BrickGoalParts


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
        if not self.parts.iris_spat_concl:
            return False

        for loop_ast_text in ["Sdo_while", "Sfor", "Swhile"]:
            if re.search(
                fr"::wpS\s+\[.*?\]\s+\({loop_ast_text}",
                self.parts.iris_spat_concl,
                re.DOTALL,  # "." should match everything, including newlines
            ):
                return True
        return False
