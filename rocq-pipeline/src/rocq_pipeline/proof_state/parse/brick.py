from dataclasses import asdict

from rocq_pipeline.proof_state.goal_parts.brick import BrickGoalParts
from rocq_pipeline.proof_state.goal_parts.iris import IrisGoalParts
from rocq_pipeline.proof_state.goal_parts.rocq import RocqGoalParts
from rocq_pipeline.proof_state.parse.iris import (
    Rocq2IrisGoalParts,
    into_IrisGoalParts,
)


def into_BrickGoalParts(
    goal: str,
    *,
    rocq_rel_goal_num: int,
    rocq_shelved_cnt: int,
    rocq_admit_cnt: int,
    rocq_goal_id: int | None = None,
    is_concl_only: bool = False,
    silent: bool = False,
) -> BrickGoalParts:
    # Parse as an Iris goal
    iris_parts = into_IrisGoalParts(
        goal,
        rocq_goal_id=rocq_goal_id,
        rocq_rel_goal_num=rocq_rel_goal_num,
        rocq_shelved_cnt=rocq_shelved_cnt,
        rocq_admit_cnt=rocq_admit_cnt,
        is_concl_only=is_concl_only,
        silent=silent,
    )
    # Then, upgrade to a Brick goal
    return Iris2BrickGoalParts(
        iris_parts,
        silent=silent,
    )


def Rocq2BrickGoalParts(
    rocq_parts: RocqGoalParts,
    silent: bool = False,
) -> BrickGoalParts:
    return Iris2BrickGoalParts(
        Rocq2IrisGoalParts(
            rocq_parts,
            silent=silent,
        ),
        silent=silent,
    )


def Iris2BrickGoalParts(
    iris_parts: IrisGoalParts,
    silent: bool = False,
) -> BrickGoalParts:
    # NOTE: carry out additional structural decomposition here.
    # e.g., brick_some_context = parse_context(iris_parts.iris_spat_concl)

    return BrickGoalParts(
        **asdict(iris_parts),
        # NOTE: include additional fields here.
        # brick_some_context=brick_some_context,
    )
