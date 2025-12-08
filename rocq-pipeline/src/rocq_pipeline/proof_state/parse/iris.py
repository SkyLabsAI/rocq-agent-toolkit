import re
from dataclasses import asdict

from rocq_pipeline.proof_state.goal_parts.iris import IrisGoalParts
from rocq_pipeline.proof_state.goal_parts.rocq import RocqGoalParts
from rocq_pipeline.proof_state.parse.rocq import into_RocqGoalParts


class IrisGoalPatterns:
    # --- Pre-compiled Regexes ---
    _RE_NAMED = re.compile(r"(?P<name>\"\S+\")\s*:\s*(?P<resource>.*)$")
    _RE_ANON = re.compile(r"_\s*:\s*(?P<resource>.*)$")
    _RE_PERS = re.compile(r"-+□$")
    _RE_SPAT = re.compile(r"-+∗$")

    @staticmethod
    def iris_named_resource_parts(line: str) -> re.Match | None:
        return IrisGoalPatterns._RE_NAMED.match(line)

    @staticmethod
    def iris_anon_resource_parts(line: str) -> re.Match | None:
        return IrisGoalPatterns._RE_ANON.match(line)

    @staticmethod
    def iris_pers_separator(line: str) -> re.Match | None:
        return IrisGoalPatterns._RE_PERS.match(line)

    @staticmethod
    def iris_spat_separator(line: str) -> re.Match | None:
        return IrisGoalPatterns._RE_SPAT.match(line)


def into_IrisGoalParts(
        goal: str,
        *,
        rocq_rel_goal_num: int,
        rocq_shelved_cnt: int,
        rocq_admit_cnt: int,
        rocq_goal_id: int | None = None,
        is_concl_only: bool = False,
        silent: bool = False,
) -> IrisGoalParts:
    # First, parse as a Rocq goal
    rocq_parts = into_RocqGoalParts(
        goal,
        rocq_goal_id=rocq_goal_id,
        rocq_rel_goal_num=rocq_rel_goal_num,
        rocq_shelved_cnt=rocq_shelved_cnt,
        rocq_admit_cnt=rocq_admit_cnt,
        is_concl_only=is_concl_only,
        silent=silent,
    )
    # Then, parse the Rocq conclusion into Iris parts
    return Rocq2IrisGoalParts(
        rocq_parts,
        silent=silent,
    )


def Rocq2IrisGoalParts(
        rocq_parts: RocqGoalParts,
        silent: bool = False,
) -> IrisGoalParts:
    iris_pers_hyps = dict[str, str]()
    iris_pers_hyps_anon = set[str]()
    iris_spat_hyps = dict[str, str]()
    iris_spat_hyps_anon = set[str]()
    iris_spat_concl: str = ""  # Default to empty
    unknown: list[str] = []

    lines = rocq_parts.rocq_concl.split("\n")
    iris_hyps: dict[str, str] = {}
    iris_hyps_anon: set[str] = set()

    for i in range(len(lines)):
        line = lines[i].strip()
        if line == "":
            continue

        if IrisGoalPatterns.iris_pers_separator(line):
            iris_pers_hyps = iris_hyps
            iris_pers_hyps_anon = iris_hyps_anon
            if any(IrisGoalPatterns.iris_spat_separator(later_lines.strip()) for later_lines in lines[i+1:]):
                iris_hyps = {}
                iris_hyps_anon = set()
            else:
                iris_spat_concl = "\n".join(lines[i + 1:]).strip()
        elif IrisGoalPatterns.iris_spat_separator(line):
            iris_spat_hyps = iris_hyps
            iris_spat_hyps_anon = iris_hyps_anon
            iris_spat_concl = "\n".join(lines[i + 1:]).strip()
            break  # Found spatial conclusion, we are done
        elif (m := IrisGoalPatterns.iris_named_resource_parts(line)):
            name = m.groupdict()["name"]
            resource = m.groupdict()["resource"]
            iris_hyps[name] = resource
        elif (m := IrisGoalPatterns.iris_anon_resource_parts(line)):
            resource = m.groupdict()["resource"]
            iris_hyps_anon.add(resource)
        else:
            unknown.append(line)

    if unknown and not silent:
        print(f"Warning (unknown Iris goal content): {unknown}")

    return IrisGoalParts(
        **asdict(rocq_parts),  # Copy all fields from base
        iris_pers_hyps=iris_pers_hyps,
        iris_pers_hyps_anon=iris_pers_hyps_anon,
        iris_spat_hyps=iris_spat_hyps,
        iris_spat_hyps_anon=iris_spat_hyps_anon,
        iris_spat_concl=iris_spat_concl,
    )
