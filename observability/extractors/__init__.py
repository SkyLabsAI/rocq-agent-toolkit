"""
Attribute extractors for different operation types.

Extractors are responsible for understanding the context of different types of operations
and extracting relevant attributes for tracing and metrics. They provide a clean way
to add framework-specific intelligence without coupling the core functionality.

Built-in extractors:
- HttpExtractor: For HTTP requests (Flask, FastAPI, Django, etc.)
- RpcExtractor: For RPC calls (gRPC, internal service calls, etc.)
- DatabaseExtractor: For database operations
- WorkflowExtractor: For workflow/pipeline steps
- LangChainExtractor: For LangChain/LangGraph operations and AI workflows
- CustomExtractor: For custom operation types

You can also create your own extractors by inheriting from AttributeExtractor.
"""

from .base import AttributeExtractor
from .http import HttpExtractor
from .rpc import RpcExtractor
from .database import DatabaseExtractor
from .workflow import WorkflowExtractor
from .langchain import LangChainExtractor
from .custom import CustomExtractor

# Registry for string-based extractor lookup
EXTRACTOR_REGISTRY = {
    "http": HttpExtractor,
    "rpc": RpcExtractor,
    "database": DatabaseExtractor,
    "workflow": WorkflowExtractor,
    "langchain": LangChainExtractor,
    "custom": CustomExtractor,
}

def get_extractor(name_or_extractor, **kwargs):
    """
    Get an extractor instance from name or return the extractor if already instantiated.
    
    Args:
        name_or_extractor: String name, extractor class, or extractor instance
        **kwargs: Arguments to pass to extractor constructor
        
    Returns:
        AttributeExtractor instance
    """
    if isinstance(name_or_extractor, str):
        if name_or_extractor not in EXTRACTOR_REGISTRY:
            raise ValueError(f"Unknown extractor: {name_or_extractor}. Available: {list(EXTRACTOR_REGISTRY.keys())}")
        return EXTRACTOR_REGISTRY[name_or_extractor](**kwargs)
    elif isinstance(name_or_extractor, type) and issubclass(name_or_extractor, AttributeExtractor):
        return name_or_extractor(**kwargs)
    elif isinstance(name_or_extractor, AttributeExtractor):
        return name_or_extractor
    else:
        raise ValueError(f"Invalid extractor type: {type(name_or_extractor)}")

__all__ = [
    "AttributeExtractor",
    "HttpExtractor",
    "RpcExtractor", 
    "DatabaseExtractor",
    "WorkflowExtractor",
    "LangChainExtractor",
    "CustomExtractor",
    "get_extractor",
] 