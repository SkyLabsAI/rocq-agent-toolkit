from collections.abc import Callable, Generator
from pathlib import Path
from typing import Any, override

from rocq_doc_manager import RocqDocManager


class DocumentWatcher:
    """
    Provides callback infrastructure to watch certain parts of the document.

    When used in a tracing context, it is important that any manipulations of
    the document do not affect the behavior of other parts of the file.
    """

    def extra_paths(self) -> dict[str, Path]:
        return {}

    def setup(self, rdm: RocqDocManager) -> None:
        """
        Sets up the infrastructure necessary to run the extractor.

        This is called once **per-file** and should NOT have any user-visible
        side effects in the Rocq document, e.g. it should not alter parsing
        scopes or bring new symbols into scope.
        """
        _ = rdm

    def start_proof(self, rdm: RocqDocManager) -> None:
        """
        Function called at the start of a proof.

        This is called once at the start of any proof that is being traced.
        """
        _ = rdm

    def end_proof(self, rdm: RocqDocManager) -> None:
        """
        Function called at the end of the proof.

        Note: This occurs after the last tactic invocation. There may
        still be open subgoals if the proof is being closed by `Admitted`.
        """
        _ = rdm


class StateExtractor[T](DocumentWatcher):
    """
    A StateExtractor extracts state from a Rocq proof.
    """

    def __call__(self, rdm: RocqDocManager) -> T | None:
        """
        Extract a feature from the current state.
        """
        return None

def merge_into[A,B](a: dict[A,B], b:dict[A,B]) -> None:
    for k, v in b.items():
        if k in a and a[k] != v:
            raise RuntimeError("Overlapping entries")
        a[k] = v

def merge_all[A,B](ds: Generator[dict[A,B]], into: dict[A,B]|None=None) -> dict[A,B]:
    result: dict[A,B] = {} if into is None else into
    for x in ds:
        merge_into(result, x)
    return result

class AllStateExtractor(StateExtractor[dict[str,Any]]):
    """
    Produce an object that contains the results of all of the state extractors
    """
    def __init__(self, extractors: dict[str, StateExtractor[Any]]):
        self._extractors:dict[str, StateExtractor[Any]] = extractors

    @override
    def extra_paths(self) -> dict[str, Path]:
        return merge_all((x.extra_paths() for x in self._extractors.values()), super().extra_paths())

    def setup(self, rdm: RocqDocManager) -> None:
        for _, e in self._extractors.items():
            e.setup(rdm)

    def start_proof(self, rdm: RocqDocManager) -> None:
        for _, e in self._extractors.items():
            e.start_proof(rdm)

    def end_proof(self, rdm: RocqDocManager) -> None:
        for _, e in self._extractors.items():
            e.end_proof(rdm)

    @override
    def __call__(self, rdm: RocqDocManager) -> dict[str,Any]:
        result: dict[str, Any] = {}
        for (k,extract) in self._extractors.items():
            # TODO: for now, we assume that extractors are hygeinic in the sense that they do revert any effects they might have on the document.
            # In the future, we could use the revert environment to enforce this.
            try:
                k_result = extract(rdm)
                if k_result is not None:
                    result[k] = k_result
            except Exception:
                pass
        return result

class GoalAsString(StateExtractor[str]):
    """A simple extractor that just gets the current goal the way it is printed in Rocq."""
    def __call__(self, rdm: RocqDocManager) -> str:
        result = rdm.current_goal()
        if isinstance(result, rdm.Resp):
            return result.result # type: ignore
        return ""

class TacticExtractor[T](DocumentWatcher):
    """
    Extract information about the execution of a tactic. This class can extract
    additional information based on the tactic, e.g. adding the types of lemmas that
    are used.

    Note that [before] will always be called before [after], so you can pass state
    from the before to the after using the class state.
    """
    def before(self, rdm: RocqDocManager, tactic:str) -> T | None:
        return None

    def after(self, rdm: RocqDocManager, tactic:str) -> T | None:
        return None

class AllTacticExtractor(TacticExtractor[dict[str,Any]]):
    def __init__(self, extractors: dict[str, TacticExtractor[Any]]) -> None:
        self._extractors = extractors

    @override
    def extra_paths(self) -> dict[str, Path]:
        return merge_all((x.extra_paths() for x in self._extractors.values()), super().extra_paths())

    def setup(self, rdm: RocqDocManager) -> None:
        for _, e in self._extractors.items():
            e.setup(rdm)

    def start_proof(self, rdm: RocqDocManager) -> None:
        for _, e in self._extractors.items():
            e.start_proof(rdm)

    def end_proof(self, rdm: RocqDocManager) -> None:
        for _, e in self._extractors.items():
            e.end_proof(rdm)

    def before(self, rdm: RocqDocManager, tactic:str) -> dict[str,Any] | None:
        def go[T](e: TacticExtractor[T]) -> T|None:
            try:
                return e.before(rdm, tactic)
            except Exception:
                return None
        return {key: go(e) for key, e in self._extractors.items()}

    def after(self, rdm: RocqDocManager, tactic:str) -> dict[str,Any] | None:
        def go[T](e: TacticExtractor[T]) -> T|None:
            try:
                return e.after(rdm, tactic)
            except Exception:
                return None
        return {key: go(e) for key, e in self._extractors.items()}

class Before[T](TacticExtractor[T]):
    """Run the StateExtractor before the tactic runs"""
    def __init__(self, state: StateExtractor[T]):
        self._extractor = state

    @override
    def extra_paths(self) -> dict[str, Path]:
        return self._extractor.extra_paths()

    def setup(self, rdm: RocqDocManager) -> None:
        self._extractor.setup(rdm)

    def start_proof(self, rdm: RocqDocManager) -> None:
        self._extractor.start_proof(rdm)

    def end_proof(self, rdm: RocqDocManager) -> None:
        self._extractor.end_proof(rdm)

    @override
    def before(self, rdm: RocqDocManager, tactic:str) -> T|None:
        return self._extractor(rdm)

class After[T](TacticExtractor[T]):
    """Run the StateExtractor after the tactic runs"""
    def __init__(self, state: StateExtractor[T]):
        self._extractor = state

    @override
    def extra_paths(self) -> dict[str, Path]:
        return self._extractor.extra_paths()

    def setup(self, rdm: RocqDocManager) -> None:
        self._extractor.setup(rdm)

    def start_proof(self, rdm: RocqDocManager) -> None:
        self._extractor.start_proof(rdm)

    def end_proof(self, rdm: RocqDocManager) -> None:
        self._extractor.end_proof(rdm)

    @override
    def after(self, rdm: RocqDocManager, tactic:str) -> T|None:
        return self._extractor(rdm)

class BeforeAndAfter[T](TacticExtractor[T]):
    """Run the StateExtractor before and after the tactic runs"""
    def __init__(self, state: StateExtractor[T]):
        self._extractor = state

    @override
    def extra_paths(self) -> dict[str, Path]:
        return self._extractor.extra_paths()

    def setup(self, rdm: RocqDocManager) -> None:
        self._extractor.setup(rdm)

    def start_proof(self, rdm: RocqDocManager) -> None:
        self._extractor.start_proof(rdm)

    def end_proof(self, rdm: RocqDocManager) -> None:
        self._extractor.end_proof(rdm)

    @override
    def before(self, rdm: RocqDocManager, tactic:str) -> T|None:
        return self._extractor(rdm)

    @override
    def after(self, rdm: RocqDocManager, tactic:str) -> T|None:
        return self._extractor(rdm)

class TacticExtractorBuilder:
    @staticmethod
    def of_tactic_extractor[T](build: Callable[[], TacticExtractor[T]] | type[TacticExtractor[T]]) -> "TacticExtractorBuilder":
        return TacticExtractorBuilder(build)

    def __init__(self, build: Callable[[], TacticExtractor[Any]]) -> None:
        self._builder = build

    def build(self) -> TacticExtractor[Any]:
        return self._builder()
