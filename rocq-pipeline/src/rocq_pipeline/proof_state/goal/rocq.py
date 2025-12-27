import re
from typing import Any

from rocq_pipeline.proof_state.goal_parts import RocqGoalParts


class RocqGoal:
    """Single Rocq goal, consisting of structured goal parts.

    This class may contain mutable state and should collect
    all utilities that can be expressed at the level of structured
    Rocq goals.
    """

    # This tells the classmethod 'from_str' which Parts dataclass to use.
    # Subclasses will override this.
    PartsDataclass: type[RocqGoalParts] = RocqGoalParts

    def __init__(self, parts: RocqGoalParts) -> None:
        if not isinstance(parts, RocqGoalParts):
            raise ValueError(f"Expected parts (RocqGoalParts), but got ({type(parts)})")
        self._parts = parts

    def to_json(self) -> dict[str, Any]:
        return self.parts.to_json()

    @property
    def raw_str(self) -> str:
        return self._parts.rocq_goal_raw

    def __str__(self) -> str:
        return self.raw_str

    @property
    def parts(self) -> RocqGoalParts:
        return self._parts

    def wellformed(self) -> bool:
        return self.parts.wellformed()

    # naming the function re confuses mypy
    def regex(
        self,
        re_pat: str,
        text: str,
        search: bool = False,
        ignore_leading_whitespace: bool = True,
        re_flags: re.RegexFlag = re.DOTALL,  # Note: default may benefit from including more, e.g. `re.MULTILINE`
    ) -> re.Match[str] | None:
        if search:
            return re.search(re_pat, text, re_flags)
        else:
            if ignore_leading_whitespace:
                re_pat = rf"\s*?{re_pat}"
            return re.match(re_pat, text, re_flags)

    def regex_rocq_concl(
        self,
        re_pat: str,
        search: bool = False,
        ignore_leading_whitespace: bool = True,
        re_flags: re.RegexFlag = re.DOTALL,
    ) -> re.Match[str] | None:
        return self.regex(
            re_pat,
            self.parts.rocq_concl,
            search=search,
            ignore_leading_whitespace=ignore_leading_whitespace,
            re_flags=re_flags,
        )
