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
    def parse_decide_condition(text: str, bool_decide: bool = False) -> str | None:
        """
        Parses 'if <keyword> (A) then (B) else (C)' logic.

        Args:
            text: The string to parse.
            bool_decide: Whether to use 'bool_decide' or 'decide'.

        Returns:
            re.Match object with groups (Condition, Then-Block, Else-Block) if successful.
            None if parsing fails or if the split creates unbalanced parentheses.

        Note: We could also return all three parts as a tuple, but for now we
        only return the Condition part since regex matching may not be sufficient
        for all cases we encounter (cf. test case 9 in test_parse_decide condition.py).
        """

        # Escape the keyword just in case it contains special regex chars
        keyword = "bool_decide" if bool_decide else "decide"

        # Dynamically build the pattern
        # 1. if <keyword> ...   -> Anchor
        # 2. (.+?) ... then     -> Lazy match for Condition (Group 1)
        # 3. (.+?) ... else     -> Lazy match for Then-Block (Group 2)
        # 4. (.+)               -> Greedy match for Else-Block (Group 3)
        pattern = rf"if\s+{keyword}\s*(.+?)\s+\bthen\b\s+(.+?)\s+\belse\b\s+(.+)"

        match = re.search(pattern, text, re.DOTALL)

        if not match:
            return None

        cond_part = match.group(1).strip()
        then_part = match.group(2).strip()

        # --- AMBIGUITY GUARDS ---
        # Heuristic: If we split on a 'fake' delimiter inside a string or nested structure,
        # the parenthesis count in the preceding block will likely be unequal.

        # Guard 1: Condition (Group 1)
        if cond_part.count("(") != cond_part.count(")"):
            return None

        # Guard 2: Then-Block (Group 2)
        if then_part.count("(") != then_part.count(")"):
            return None
        return match.group(1)

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

    def is_if_decide_then_else_goal(self) -> str | None:
        """
        Checks if the spatial conclusion contains a 'if decide xxx then yyy else zzz' term.
        """
        return BrickGoal.parse_decide_condition(
            self.parts.iris_spat_concl, bool_decide=False
        )

    def is_if_bool_decide_then_else_goal(self) -> str | None:
        """
        Checks if the spatial conclusion contains a 'if bool_decide xxx then yyy else zzz' term.
        """
        return BrickGoal.parse_decide_condition(
            self.parts.iris_spat_concl, bool_decide=True
        )
