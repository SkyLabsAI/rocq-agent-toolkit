
from rocq_pipeline.proof_state.goal import BrickGoal, IrisGoal, RocqGoal
from rocq_pipeline.proof_state.parse.brick import into_BrickGoalParts
from rocq_pipeline.proof_state.parse.iris import into_IrisGoalParts
from rocq_pipeline.proof_state.parse.rocq import into_RocqGoalParts

_parse_into_GoalParts = {
    RocqGoal: into_RocqGoalParts,
    IrisGoal: into_IrisGoalParts,
    BrickGoal: into_BrickGoalParts,
}


def str_into_Goal(
        goal_str: str,
        *,
        goal_ty_upperbound: type[RocqGoal] = RocqGoal,
        rocq_rel_goal_num: int,
        rocq_shelved_cnt: int,
        rocq_admit_cnt: int,
        rocq_goal_id: int | None = None,
) -> RocqGoal:
    if not issubclass(goal_ty_upperbound, RocqGoal):
        raise RuntimeError(f"{goal_ty_upperbound} not a subclass of RocqGoal")

    goal = _into_Goals.parse_goal_string(
        goal_str,
        goal_ty_upperbound=goal_ty_upperbound,
        rocq_rel_goal_num=rocq_rel_goal_num,
        rocq_shelved_cnt=rocq_shelved_cnt,
        rocq_admit_cnt=rocq_admit_cnt,
        rocq_goal_id=rocq_goal_id,
    )
    if goal is not None and goal.wellformed():
        return goal
    else:
        raise RuntimeError(
            f"Goal parsing failure (upperbound {goal_ty_upperbound.__name__}):\n{goal_str}"
        )


class _into_Goals:
    @staticmethod
    def parse_goal_string(
            goal_str: str,
            *,
            goal_ty_upperbound: type[RocqGoal],
            rocq_rel_goal_num: int,
            rocq_shelved_cnt: int,
            rocq_admit_cnt: int,
            rocq_goal_id: int | None = None,
            is_concl_only: bool = False,
    ) -> RocqGoal | None:
        """
        Try to parse a single goal string using the MRO of goal_ty_upperbound.
        Start with the most specific type and falls back to the most general.
        """
        for cls in goal_ty_upperbound.__mro__:
            if not issubclass(cls, RocqGoal):
                continue

            structured_goal = cls(
                _parse_into_GoalParts[cls](
                    goal_str,
                    rocq_rel_goal_num=rocq_rel_goal_num,
                    rocq_shelved_cnt=rocq_shelved_cnt,
                    rocq_admit_cnt=rocq_admit_cnt,
                    rocq_goal_id=rocq_goal_id,
                    is_concl_only=is_concl_only,
                    silent=True,  # Silence warnings during fallback
                )
            )

            if structured_goal.wellformed():
                return structured_goal

        # Warning if no parser worked
        print(
            f"Warning: Could not parse goal {rocq_rel_goal_num}:\n{goal_str[:200]}..."
        )
        return None
