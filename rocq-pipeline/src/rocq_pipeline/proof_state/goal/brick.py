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

    @staticmethod
    def wpS_head_stmt_matches(s: str, constructs: list[str]) -> bool:
        for ast in constructs:
            if re.search(
                rf"::wpS\s+\[.*?\]\s+\({ast}",
                s,
                re.DOTALL,  # "." should match everything, including newlines
            ):
                return True
        return False

    @staticmethod
    def if_decide_then_else_extract(text: str) -> tuple[str, str, str] | None:
        pattern = r"if\s+decide\s*\(([^)]+)\)\s+then\s+(.+?)\s+else\s+(.+)"

        match = re.search(pattern, text, re.DOTALL)

        if match:
            return match.group(1), match.group(2), match.group(3)
        return None

    @property
    @override
    def parts(self) -> BrickGoalParts:
        # Override property for correct type hinting
        return cast(BrickGoalParts, self._parts)

    def is_loop_goal(self) -> bool:
        """
        Checks if the spatial conclusion contains a loop AST node.
        """
        return BrickGoal.wpS_head_stmt_matches(
            self.parts.iris_spat_concl, ["Sdo_while", "Sfor", "Swhile"]
        )

    def is_conditional_goal(self) -> bool:
        """
        Checks if the spatial conclusion contains a 'if' AST node.
        """
        # return BrickGoal.wpS_head_stmt_matches(self.parts.iris_spat_concl, ["Sif"])
        pattern = r"^branch\.(stmt|expr)"

        if re.search(pattern, self.parts.iris_spat_concl):
            return True
        return False

    def is_if_decide_then_else_goal(self) -> tuple[str, str, str] | None:
        """
        Checks if the spatial conclusion contains a 'if decide (xxx) then yyy else zzz' term.
        """
        return BrickGoal.if_decide_then_else_extract(self.parts.iris_spat_concl)
