from collections.abc import Awaitable, Callable, Mapping
from typing import Any, Literal, Protocol, Self, TypedDict, cast

from pydantic import BaseModel, Field, JsonValue
from rocq_doc_manager import RocqCursor
from rocq_dune_util import DuneRocqPlugin
from rocq_pipeline.with_deps import UsingRocqDeps, rocq_deps_for


class OutputDict[A](TypedDict):
    """Class that captures the intuition that an interaction has a "before"
    state and an "after" state."""

    # TODO: expand this with an "info" field
    before: A
    after: A


def pivot_output_dict[K, A](input: dict[K, OutputDict[A]]) -> OutputDict[dict[K, A]]:
    """The type says it all."""
    result: OutputDict[dict[K, A]] = {"before": {}, "after": {}}
    for k, v in input.items():
        result["before"][k] = v["before"]
        result["after"][k] = v["after"]
    return result


class InteractionTrace(BaseModel):
    """The trace of a single interaction, e.g. a tactic execution in a particular proof script."""

    action: str = Field(description="The action that is run, usually a tactic")
    before: JsonValue = Field(
        description="Information about the state before the action"
    )
    after: JsonValue = Field(description="Information about the state after the action")
    info: JsonValue | None = Field(
        description="Extra information about the action, e.g. the result of `Check x` if the tactic is `rewrite x` or the lemmas applied by a larger bit of automation"
    )

    @classmethod
    def of_output_dict(
        cls,
        tactic: str,
        result: OutputDict[JsonValue],
        *,
        info: dict[str, JsonValue] | None = None,
    ) -> Self:
        return cls(
            action=tactic,
            before=result["before"],
            after=result["after"],
            info=info,
        )


class DocumentWatcher(Protocol):
    """
    Provides callback infrastructure to watch certain parts of the document.

    When used in a tracing context, it is important that any manipulations of
    the document do not affect the behavior of other parts of the file.
    """

    async def setup(self, rc: RocqCursor) -> None:
        """
        Sets up the infrastructure necessary to run the extractor.

        This is called once **per-file** and should NOT have any user-visible
        side effects in the Rocq document, e.g. it should not alter parsing
        scopes or bring new symbols into scope.
        """
        ...

    async def start_proof(self, rc: RocqCursor) -> None:
        """
        Function called at the start of a proof.

        This is called once at the start of any proof that is being traced.
        """
        ...

    async def end_proof(self, rc: RocqCursor) -> None:
        """
        Function called at the end of the proof.

        Note: This occurs after the last tactic invocation. There may
        still be open subgoals if the proof is being closed by `Admitted`.
        """
        ...


class DefaultDocumentWatcher(DocumentWatcher):
    async def setup(self, rc: RocqCursor) -> None:
        pass

    async def start_proof(self, rc: RocqCursor) -> None:
        pass

    async def end_proof(self, rc: RocqCursor) -> None:
        pass


class StateExtractor[T](Protocol):
    """
    A StateExtractor extracts state from a Rocq proof.
    """

    async def extract(self, rc: RocqCursor) -> T | None:
        """
        Extract a feature from the current state.
        """
        ...


class AllDocumentWatcher(DocumentWatcher):
    """
    Produce an object that contains the results of all of the state extractors
    """

    def __init__(self, watchers: Mapping[str, DocumentWatcher]):
        self._watchers: Mapping[str, DocumentWatcher] = watchers

    async def setup(self, rc: RocqCursor) -> None:
        for _, w in self._watchers.items():
            await w.setup(rc)

    async def start_proof(self, rc: RocqCursor) -> None:
        for _, w in self._watchers.items():
            await w.start_proof(rc)

    async def end_proof(self, rc: RocqCursor) -> None:
        for _, w in self._watchers.items():
            await w.end_proof(rc)


class AllStateExtractor(StateExtractor[dict[str, Any]]):
    """
    Produce an object that contains the results of all of the state extractors
    """

    def __init__(self, extractors: dict[str, StateExtractor[Any]]):
        self._extractors: dict[str, StateExtractor[Any]] = extractors

    async def extract(self, rc: RocqCursor) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for k, extractor in self._extractors.items():
            # TODO: for now, we assume that extractors are hygeinic in the sense that they do revert any effects they might have on the document.
            # In the future, we could use the revert environment to enforce this.
            k_result = await extractor.extract(rc)
            if k_result is not None:
                result[k] = k_result
        return result


class BracketInterface[A](Protocol):
    """
    Is used internally to enforce the [before]-before-[after] invariant of
    [BracketedExtractor].

    Inheriting from [BracketedExtractor] automatically implements this interface.
    """

    type After[B] = Callable[[RocqCursor, str], Awaitable[B | None]]

    async def before_internal(self, rc: RocqCursor, tactic: str) -> After[A] | None: ...


class ExtractorResult[T](Protocol):
    """
    Wraps the result of calling an extractor in an object that allows
    distinguishing the absence of a result value from the intent to skip the
    current command (or tactic). Python cannot distinguish Optional[T] from
    Optional[Optional[T]] which means we cannot use a [None] value to represent
    a result of type Optional[T]. Instead, we use an extra boolean.

    We do not use Optional[T] directly. Instead, we annotate [result] to
    establish a weak but nonetheless helpful connection between the boolean and
    the returned value.
    """

    def val(self) -> tuple[Literal[False], None] | tuple[Literal[True], T]: ...


class Extracted[T](ExtractorResult[T]):
    __slots__ = ["_result"]

    def __init__(self, t: T):
        self._result = t

    def val(self) -> tuple[Literal[True], T]:
        return (True, self._result)


class Skip[T](ExtractorResult[T]):
    def val(self) -> tuple[Literal[False], None]:
        return (False, None)


class BracketedExtractor[B, A](BracketInterface[A], Protocol):
    """
    Extract information about the execution of a command (or a tactic). Classes
    implementing this protocol can extract additional information based on the
    command, e.g. adding the types of lemmas that are used in a tactic.

    Note that [before] will always be called before [after] and the return value
    of [before] is passed to [after] as the [result_before] value.

    Both [before] and [after] can return [None] to indicate that this command or
    tactic is not supported by the extractor.
    """

    async def before(self, rc: RocqCursor, tactic: str) -> ExtractorResult[B]: ...

    async def after(
        self, rc: RocqCursor, tactic: str, result_before: B
    ) -> A | None: ...

    async def before_internal(
        self, rc: RocqCursor, tactic: str
    ) -> BracketInterface.After[A] | None:
        result_before = await self.before(rc, tactic)
        match result_before.val():
            case (True, v):
                v = cast(B, v)  # mypy is not smart enough to figure this out

                async def fn(rc: RocqCursor, tactic: str) -> A | None:
                    return await self.after(rc, tactic, v)

                return fn
            case _:
                return None


class TrivialBracketedExtractor[A](
    BracketedExtractor[A, OutputDict[A]], StateExtractor[A]
):
    """A BracketExtractor from a StateExtractor.

    NOTE: We use inheritence here instead of composition so that
    we can passthru any dependencies; however, it might be nicer
    to work with lower-level components."""

    async def before(self, rc: RocqCursor, tactic: str) -> ExtractorResult[A]:
        match await self.extract(rc):
            case None:
                return Skip()
            case val:
                return Extracted(val)

    async def after(
        self, rc: RocqCursor, tactic: str, result_before: A
    ) -> OutputDict[A] | None:
        result_after = await self.extract(rc)
        if result_after is None:
            return None
        return {"before": result_before, "after": result_after}


class AllBracketInterface[K, V](BracketInterface[dict[K, V]]):
    def __init__(self, extractors: Mapping[K, BracketInterface[V]]) -> None:
        self._extractors = extractors

    async def before_internal(
        self, rc: RocqCursor, tactic: str
    ) -> BracketInterface.After[dict[K, V]] | None:
        result = {
            k: v
            for k, extractor in self._extractors.items()
            if (v := await extractor.before_internal(rc, tactic))
        }

        async def final_result(rc: RocqCursor, tactic: str) -> dict[K, V]:
            return {
                k: v for k, after in result.items() if (v := await after(rc, tactic))
            }

        return final_result


class Tracer[A](DocumentWatcher, BracketInterface[A], Protocol):
    """
    The protocol that the tracer relies on.
    """

    pass


class MapTracer[A, B](Tracer[B]):
    def __init__(self, tracer: Tracer[A], fn: Callable[[A], B]) -> None:
        self._tracer = tracer
        self._fn = fn

    def rocq_deps(self) -> list[DuneRocqPlugin]:
        return rocq_deps_for(self._tracer)

    async def setup(self, rc: RocqCursor) -> None:
        return await self._tracer.setup(rc)

    async def start_proof(self, rc: RocqCursor) -> None:
        return await self._tracer.start_proof(rc)

    async def end_proof(self, rc: RocqCursor) -> None:
        return await self._tracer.end_proof(rc)

    async def before_internal(
        self, rc: RocqCursor, tactic: str
    ) -> BracketInterface.After[B] | None:
        after_a = await self._tracer.before_internal(rc, tactic)
        if after_a is None:
            return None
        fn = self._fn

        async def after_b(rc: RocqCursor, tactic: str) -> B | None:
            nonlocal after_a, fn
            assert after_a is not None
            a = await after_a(rc, tactic)
            return None if a is None else fn(a)

        return after_b


class AllTracer[A](AllDocumentWatcher, AllBracketInterface[str, A], UsingRocqDeps):
    """Build a `Tracer` that combines many individual `Tracer`s."""

    def __init__(self, tracers: Mapping[str, Tracer[A]]) -> None:
        # It is a bit wasteful to have two fields instead of just one.
        AllDocumentWatcher.__init__(self, tracers)
        AllBracketInterface.__init__(self, tracers)

    def rocq_deps(self) -> list[DuneRocqPlugin]:
        return [
            x for tracer in self._extractors.values() for x in rocq_deps_for(tracer)
        ]
