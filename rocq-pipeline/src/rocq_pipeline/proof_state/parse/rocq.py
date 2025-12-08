import re

from rocq_pipeline.proof_state.goal_parts.rocq import RocqGoalParts


class RocqPatterns:
    # --- Pre-compiled Regexes ---
    _RE_DEFN = re.compile(r"(?P<name>.+?)\s*:=\s*(?P<term>.*)\s*:\s*(?P<type>.*)$")
    _RE_HYP = re.compile(r"(?P<name>.+?)\s*:\s*(?P<type>.*)$")
    _RE_SEP = re.compile(r"=+$")

    @staticmethod
    def rocq_defn_parts(line: str) -> re.Match | None:
        return RocqPatterns._RE_DEFN.match(line)

    @staticmethod
    def rocq_hyp_parts(line: str) -> re.Match | None:
        return RocqPatterns._RE_HYP.match(line)

    @staticmethod
    def rocq_proof_separator(line: str) -> re.Match | None:
        return RocqPatterns._RE_SEP.match(line)


def into_RocqGoalParts(
        goal: str,
        *,
        rocq_rel_goal_num: int,
        rocq_shelved_cnt: int,
        rocq_admit_cnt: int,
        rocq_goal_id: int | None = None,
        is_concl_only: bool = False,
        silent: bool = False,
) -> RocqGoalParts:
    rocq_hyps = dict[str, tuple[str, str | None]]()
    rocq_concl = ""
    unknown: list[str] = []

    if is_concl_only:
        # Case: "goal <N> is:"
        rocq_concl = goal.strip()
    else:
        lines = goal.split("\n")
        separator_found = False
        for i in range(len(lines)):
            line = lines[i].strip()
            if line == "":
                continue

            if RocqPatterns.rocq_proof_separator(line):
                rocq_concl = "\n".join(lines[i + 1:]).strip()
                separator_found = True
                break
            if (match := RocqPatterns.rocq_defn_parts(line)):
                name = match.groupdict()["name"].strip()
                ty = match.groupdict()["type"].strip()
                term = match.groupdict()["term"].strip()
                rocq_hyps[name.strip()] = (ty, term)
            elif (match := RocqPatterns.rocq_hyp_parts(line)):
                ty = match.groupdict()["type"].strip()
                for name in match.groupdict()["name"].split(","):
                    rocq_hyps[name.strip()] = (ty, None)
            else:
                unknown.append(line)

        if not separator_found:
            rocq_concl = goal.strip()
            unknown.clear()

    if unknown and not silent:
        print(f"Warning (unknown Rocq goal content): {unknown}")

    return RocqGoalParts(
        rocq_goal_id=rocq_goal_id,
        rocq_rel_goal_num=rocq_rel_goal_num,
        rocq_shelved_cnt=rocq_shelved_cnt,
        rocq_admit_cnt=rocq_admit_cnt,
        rocq_hyps=rocq_hyps,
        rocq_concl=rocq_concl,
    )
