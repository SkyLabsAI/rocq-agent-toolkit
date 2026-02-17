#
# This file provides utilities for testing rollouts
#


from rocq_pipeline.search.rollout import Rollout


async def is_empty[T](r: Rollout[T]) -> None:
    """Assert that the Rollout is empty"""
    try:
        result = await r.next()
        raise AssertionError(f"Should be empty, but got {result}")
    except StopAsyncIteration:
        pass


def approx[T](logprob: float, result: T | None) -> Rollout.Approx[T]:
    """Construct a `Rollout.Approx` without needing to
    name the arguments"""
    return Rollout.Approx(logprob=logprob, result=result)
