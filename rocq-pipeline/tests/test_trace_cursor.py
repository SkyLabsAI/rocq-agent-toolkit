from collections.abc import AsyncGenerator, Awaitable, Callable
from contextlib import asynccontextmanager
from pathlib import Path

import pytest
from rocq_doc_manager import rc_sess
from rocq_doc_manager import rocq_doc_manager_api as rdm_api
from rocq_doc_manager.rocq_cursor_protocol import RocqCursor
from rocq_pipeline.agent.proof import trace_cursor


@asynccontextmanager
async def build_both(
    verbose: bool,
) -> AsyncGenerator[tuple[RocqCursor, RocqCursor]]:
    async with rc_sess(
        Path(__file__).parent / "test.v", rocq_args=[], load_file=True
    ) as rc:
        traced = trace_cursor.TracingCursor.of_cursor(await rc.clone(), verbose=verbose)
        try:
            print(await rc.doc_prefix())
            print(await rc.doc_suffix())
            yield (rc, traced)
        finally:
            await traced.dispose()
            await rc.dispose()


async def same[T](fn: Callable[[RocqCursor], Awaitable[T]], verbose: bool) -> None:
    async with build_both(verbose) as (rc, traced):
        result: T | Exception | None = None
        traced_result: T | Exception | None = None
        try:
            result = await fn(rc)
        except Exception as e:
            result = e
        try:
            traced_result = await fn(traced)
        except Exception as e:
            traced_result = e
        assert type(result) is type(traced_result)
        if isinstance(result, Exception):
            assert isinstance(traced_result, Exception)
            assert str(result) == str(traced_result)
        elif isinstance(result, rdm_api.CommandData):
            assert isinstance(traced_result, rdm_api.CommandData)
            assert result.proof_state == traced_result.proof_state
        elif isinstance(result, rdm_api.Err):
            assert isinstance(traced_result, rdm_api.Err)
            assert result.data == traced_result.data
        else:
            assert result == traced_result


_methods_and_kwargs = {
    "insert_command": {"ghost": False},
    "query": {},
    "query_text_all": {},
    "query_json_all": {},
}


@pytest.mark.parametrize("verbose", [True, False], ids=[True, False])
@pytest.mark.parametrize(
    "method",
    _methods_and_kwargs.keys(),
    ids=_methods_and_kwargs.keys(),
)
@pytest.mark.asyncio
async def test_insert_command(verbose: bool, method: str) -> None:
    async def call(rc: RocqCursor):
        return await getattr(rc, method)("About nat.", **_methods_and_kwargs[method])

    await same(call, verbose)


@pytest.mark.parametrize("verbose", [True, False], ids=[True, False])
@pytest.mark.parametrize(
    "method",
    ["query_json", "query_text"],
    ids=["query_json", "query_text"],
)
@pytest.mark.asyncio
async def test_with_index(verbose: bool, method: str) -> None:
    async def call(rc: RocqCursor):
        return await getattr(rc, method)("About nat.", index=0)

    await same(call, verbose)


# @pytest.mark.parametrize("verbose", [True, False], ids=[True, False])
# def test_query(verbose: bool) -> None:
#     same(lambda rc: rc.query("About nat."), verbose)


# @pytest.mark.parametrize("verbose", [True, False], ids=[True, False])
# def test_query_text_all(verbose: bool) -> None:
#     same(lambda rc: rc.query_text_all("About nat."), verbose)


@pytest.mark.parametrize("verbose", [True, False], ids=[True, False])
@pytest.mark.asyncio
async def test_run_step(verbose: bool) -> None:
    async def call(rc: RocqCursor):
        return await rc.run_step()

    await same(call, verbose)
