from typing import Any, override

from rocq_doc_manager import RocqDocManager


class StateExtractor[T]:
    """
    A StateExtractor extracts state from a Rocq proof.
    """
    def __call__(self, rdm: RocqDocManager) -> T | None:
        """
        Extract a feature from the current state.
        """
        return None

class AllStateExtractor(StateExtractor[dict[str,Any]]):
    """
    Produce an object that contains the results of all of the state extractors
    """
    def __init__(self, extractors: dict[str, StateExtractor[Any]]):
        self._extractors:dict[str, StateExtractor] = extractors

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

class TacticExtractor[T]:
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
    def before(self, rdm: RocqDocManager, tactic:str) -> T|None:
        return self._extractor(rdm)

class After[T](TacticExtractor[T]):
    """Run the StateExtractor after the tactic runs"""
    def __init__(self, state: StateExtractor[T]):
        self._extractor = state
    @override
    def after(self, rdm: RocqDocManager, tactic:str) -> T|None:
        return self._extractor(rdm)

class BeforeAndAfter[T](TacticExtractor[T]):
    """Run the StateExtractor before and after the tactic runs"""
    def __init__(self, state: StateExtractor[T]):
        self._extractor = state

    @override
    def before(self, rdm: RocqDocManager, tactic:str) -> T|None:
        return self._extractor(rdm)

    @override
    def after(self, rdm: RocqDocManager, tactic:str) -> T|None:
        return self._extractor(rdm)
