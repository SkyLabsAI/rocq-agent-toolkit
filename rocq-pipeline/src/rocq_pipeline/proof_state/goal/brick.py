import re
from typing import Literal, cast, override

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

    def regex_brick_spat_concl_wp(
        self,
        *asts: str,
        kind: Literal[
            "S", "E"
        ] = "S",  # Note: various wp forms (ellipses not permitted)
        search: bool = False,
        ignore_leading_whitespace: bool = True,
        re_flags: re.RegexFlag = re.DOTALL,
    ) -> dict[str, re.Match[str] | None]:
        res = {
            ast: self.regex_iris_spat_concl(
                rf"::wp{kind}\s+\[.*?\]\s+\({ast}",
                search=search,
                ignore_leading_whitespace=ignore_leading_whitespace,
                re_flags=re_flags,
            )
            for ast in asts
        }
        return res

    def regex_brick_spat_concl_nonwp(
        self,
        s: str,
        search: bool = False,
        ignore_leading_whitespace: bool = True,
        re_flags: re.RegexFlag = re.DOTALL,
    ) -> re.Match[str] | None:
        return self.regex_iris_spat_concl(
            re.escape(s),
            search=search,
            ignore_leading_whitespace=ignore_leading_whitespace,
            re_flags=re_flags,
        )

    def is_loop_goal(self) -> bool:
        """
        Checks if the spatial conclusion contains a loop AST node.
        """
        d: dict[str, re.Match[str] | None] = self.regex_brick_spat_concl_wp(
            "Sdo_while", "Sfor", "Swhile", kind="S"
        )
        res: bool = any(value is not None for value in d.values())
        return res

    def is_branch_stmt_goal(self) -> bool:
        """
        Checks if the spatial conclusion starts with a 'branch.stmt' node.
        """
        return bool(self.regex_brick_spat_concl_nonwp(r"branch.stmt"))

    def is_branch_expr_goal(self) -> bool:
        """
        Checks if the spatial conclusion contains a 'branch.expr' node.
        """
        return bool(self.regex_brick_spat_concl_nonwp(r"branch.expr"))

    def is_conditional_goal(self) -> bool:
        """
        Checks if the spatial conclusion starts with a 'branch.stmt' or 'branch.expr' node.
        """
        return self.is_branch_stmt_goal() or self.is_branch_expr_goal()

    def is_if_decide_then_else_goal(self) -> tuple[str, str, str] | None:
        """
        Checks if the spatial conclusion contains a 'if decide (xxx) then yyy else zzz' term.
        """
        return BrickGoal.if_decide_then_else_extract(self.parts.iris_spat_concl)
