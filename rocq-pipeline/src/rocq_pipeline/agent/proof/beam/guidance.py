from abc import ABC, abstractmethod
from typing import Callable, Tuple, Dict, Any, TypeVar, List, override

from rocq_doc_manager import RocqCursor

# Import the Generic Protocols
from ...search_foundation.protocols import Guidance as GuidanceProtocol
from ...search_foundation.types import BeamNode

# Import your Local Adapter
from .beam import RocqStateAdapter

# U is the return type of the internal scoring logic (usually float)
U = TypeVar("U")

class Guidance(GuidanceProtocol[RocqStateAdapter], ABC):
    """
    Abstract base class for Rocq Guidance.
    Implements the generic protocol but delegates to a cleaner interface.
    """
    
    @abstractmethod
    def score(self, state: RocqStateAdapter, node: BeamNode) -> Tuple[float, Dict[str, Any]]:
        """
        Required by ActionBeamSearch.
        We return (score, metadata_dict).
        """
        ...

class LLMGuidance(Guidance):
    @override
    def score(self, state: RocqStateAdapter, node: BeamNode) -> Tuple[float, Dict[str, Any]]:
        # 1. Unwrap the cursor
        cursor = state.cursor
        
        # 2. Your original logic
        # (Returning -inf as placeholder, plus empty metadata)
        return -float("inf"), {}

class GoalBasedGuidance(Guidance):
    """
    Computes scores based on subgoals using an inner guidance strategy.
    """
    def __init__(
        self, 
        guidance: Guidance, 
        combine: Callable[[List[float]], float] = min
    ) -> None:
        self._guidance = guidance
        self._combine = combine

    @override
    def score(self, state: RocqStateAdapter, node: BeamNode) -> Tuple[float, Dict[str, Any]]:
        cursor = state.cursor
        
        raise NotImplementedError()