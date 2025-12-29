import re
from typing import cast, override

from rocq_pipeline.proof_state.goal import RocqGoal
from rocq_pipeline.proof_state.goal_parts import IrisGoalParts


class IrisGoal(RocqGoal):
    """Single Iris goal, consisting of structured goal parts.

    This class may contain mutable state and should collect
    all utilities that can be expressed at the level of structured
    Iris goals.
    """

    # Override the PartsDataclass to point to the Iris version
    PartsDataclass: type[IrisGoalParts] = IrisGoalParts

    @property
    @override
    def parts(self) -> IrisGoalParts:
        # Override property for correct type hinting
        return cast(IrisGoalParts, self._parts)

    def regex_iris_spat_concl(
        self,
        re_pat: str,
        search: bool = False,
        ignore_leading_whitespace: bool = True,
        re_flags: re.RegexFlag = re.DOTALL,
    ) -> re.Match[str] | None:
        return self.regex(
            re_pat,
            self.parts.iris_spat_concl,
            search=search,
            ignore_leading_whitespace=ignore_leading_whitespace,
            re_flags=re_flags,
        )

    def regex_iris_pers_hyps(
        self,
        re_pat: str,
        search: bool = False,
        ignore_leading_whitespace: bool = True,
        re_flags: re.RegexFlag = re.DOTALL,
    ) -> dict[str, re.Match[str] | None]:
        pers_hyps: dict[str, str] = self.parts.iris_pers_hyps
        return {
            n: self.regex(
                re_pat,
                resource,
                search=search,
                ignore_leading_whitespace=ignore_leading_whitespace,
                re_flags=re_flags,
            )
            for n, resource in pers_hyps.items()
        }

    def regex_iris_pers_hyps_anon(
        self,
        re_pat: str,
        search: bool = False,
        ignore_leading_whitespace: bool = True,
        re_flags: re.RegexFlag = re.DOTALL,
    ) -> set[re.Match[str] | None]:
        pers_hyps_anon: set[str] = self.parts.iris_pers_hyps_anon
        return {
            self.regex(
                re_pat,
                hyp,
                search=search,
                ignore_leading_whitespace=ignore_leading_whitespace,
                re_flags=re_flags,
            )
            for hyp in pers_hyps_anon
        }

    def regex_iris_spat_hyps(
        self,
        re_pat: str,
        search: bool = False,
        ignore_leading_whitespace: bool = True,
        re_flags: re.RegexFlag = re.DOTALL,
    ) -> dict[str, re.Match[str] | None]:
        spat_hyps: dict[str, str] = self.parts.iris_pers_hyps
        return {
            n: self.regex(
                re_pat,
                resource,
                search=search,
                ignore_leading_whitespace=ignore_leading_whitespace,
                re_flags=re_flags,
            )
            for n, resource in spat_hyps.items()
        }

    def regex_iris_spat_hyps_anon(
        self,
        re_pat: str,
        search: bool = False,
        ignore_leading_whitespace: bool = True,
        re_flags: re.RegexFlag = re.DOTALL,
    ) -> set[re.Match[str] | None]:
        spat_hyps_anon: set[str] = self.parts.iris_pers_hyps_anon
        return {
            self.regex(
                re_pat,
                hyp,
                search=search,
                ignore_leading_whitespace=ignore_leading_whitespace,
                re_flags=re_flags,
            )
            for hyp in spat_hyps_anon
        }
