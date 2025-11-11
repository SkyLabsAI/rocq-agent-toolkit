import re
from collections.abc import Iterator

from rocq_pipeline.proof_state.goal import BrickGoal, IrisGoal, RocqGoal
from rocq_pipeline.proof_state.parse.brick import into_BrickGoalParts
from rocq_pipeline.proof_state.parse.iris import into_IrisGoalParts
from rocq_pipeline.proof_state.parse.rocq import into_RocqGoalParts

_parse_into_GoalParts = {
    RocqGoal: into_RocqGoalParts,
    IrisGoal: into_IrisGoalParts,
    BrickGoal: into_BrickGoalParts,
}


def into_Goals(
        pf_state_str: str,
        goal_ty_bound: type[RocqGoal] = RocqGoal,
) -> dict[int, RocqGoal]:
    if not issubclass(goal_ty_bound, RocqGoal):
        raise RuntimeError(f"{goal_ty_bound} not a subclass of RocqGoal")

    goal_parts: dict[int, RocqGoal] = {}
    for goal in _into_Goals.parse_proof_state(pf_state_str, goal_ty_bound):
        if goal.wellformed():
            goal_parts[goal.parts.rocq_rel_goal_num] = goal

    return goal_parts


class _into_Goals:
    # --- Pre-compiled Regexes ---
    _RE_GOAL_COUNT = re.compile(
        r"^\s*(\d+)\s+(?:focused\s+)?goal[s]?\s*(?:\(shelved:\s*(\d+)\))?.*$"
    )
    _RE_GOAL_IS = re.compile(r"^\s*goal\s+(\d+)\s+\(?(?:ID\s+\d+\))?\s*is:.*$")

    @staticmethod
    def _parse_goal_string(
        goal_str: str,
        goal_ty_bound: type[RocqGoal],
        rocq_rel_goal_num: int,
        rocq_shelved_cnt: int | None,
        is_concl_only: bool,
    ) -> RocqGoal | None:
        """
        Tries to parse a single goal string using the MRO of the goal_ty_bound.
        Starts with the most specific type and falls back to the most general.
        """
        for cls in goal_ty_bound.__mro__:
            if not issubclass(cls, RocqGoal):
                continue

            structured_goal = cls(_parse_into_GoalParts[cls](
                goal_str,
                rocq_goal_id=None,
                rocq_rel_goal_num=rocq_rel_goal_num,
                rocq_shelved_cnt=rocq_shelved_cnt,
                is_concl_only=is_concl_only,
                silent=True,  # Silence warnings during fallback
            ))

            if structured_goal.wellformed():
                return structured_goal

        # Warning if no parser worked
        print(
            "Warning: Could not parse goal "
            f"{rocq_rel_goal_num}:\n{goal_str[:200]}..."
        )
        return None

    @classmethod
    def parse_proof_state(
        cls,
        pf_state_str: str,
        goal_ty_bound: type[RocqGoal],
    ) -> Iterator[RocqGoal]:
        """
        Parses a proof state string and yields structured goals.
        This is a static generator that manages its own parsing state.
        """
        # --- Local state variables ---
        current_goal_lines: list[str] = []
        goal_counter: int = 1
        current_shelved_cnt: int | None = None
        current_is_concl_only: bool = False

        # Simple state machine:
        # 0 = PRE (searching for the first goal's metadata)
        # 1 = CONTENT (collecting lines for the current goal)
        state = 0

        for line in pf_state_str.split("\n"):
            stripped_line = line.strip()

            # Check for metadata lines
            m1 = cls._RE_GOAL_COUNT.match(stripped_line)
            m2 = not m1 and cls._RE_GOAL_IS.match(stripped_line)

            if m1 or m2:
                # --- Found a metadata line ---
                if state == 1:
                    # We were in CONTENT, so this is the *next* goal.
                    # Process the goal we just finished collecting.
                    goal_str = "\n".join(current_goal_lines).strip()
                    if goal_str:
                        structured_goal = cls._parse_goal_string(
                            goal_str,
                            goal_ty_bound,
                            goal_counter,  # Use incrementing counter
                            current_shelved_cnt,
                            current_is_concl_only,
                        )
                        if structured_goal:
                            yield structured_goal
                            goal_counter += 1  # Increment *after* yielding

                # --- Reset state for the *new* goal ---
                state = 1  # We are now officially in a goal
                current_goal_lines = []
                if m1:
                    # "N goals" line
                    current_shelved_cnt = int(m1.group(2)) if m1.group(2) else None
                    current_is_concl_only = False
                elif m2:
                    # "goal N is:" line
                    current_shelved_cnt = None
                    current_is_concl_only = True
                continue

            # --- Not a metadata line ---
            if state == 1:
                # We are in CONTENT, so collect this line
                # (Skip leading blank lines *within* a goal's content)
                if not current_goal_lines and stripped_line == "":
                    continue
                current_goal_lines.append(line)

            # if state == 0, we're in PRE and this isn't metadata,
            # so we just discard the line (it's junk before the first goal)

        # --- Process the very last goal (after the loop ends) ---
        if state == 1 and current_goal_lines:
            goal_str = "\n".join(current_goal_lines).strip()
            if goal_str:
                structured_goal = cls._parse_goal_string(
                    goal_str,
                    goal_ty_bound,
                    goal_counter,  # Use the final counter value
                    current_shelved_cnt,
                    current_is_concl_only,
                )
                if structured_goal:
                    yield structured_goal
