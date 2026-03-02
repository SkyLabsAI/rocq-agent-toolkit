#
# This file provides utilities for testing rollouts
#


from pyroof_search.rollout import Proposals


async def is_empty[T](r: Proposals[T]) -> None:
    """Assert that the Rollout is empty"""
    try:
        result = await r.next()
        raise AssertionError(f"Should be empty, but got {result}")
    except StopAsyncIteration:
        pass


def approx[T](logprob: float, result: T | None) -> Proposals.Approx[T]:
    """Construct a `Rollout.Approx` without needing to
    name the arguments"""
    return Proposals.Approx(logprob=logprob, result=result)
