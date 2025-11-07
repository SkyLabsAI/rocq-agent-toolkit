"""Python API for the Rocq document manager.

This package provides a Python interface to interact with the Rocq document
manager.
"""

from .dune_util import dune_env_hack, DuneUtil
from .rocq_doc_manager import RocqDocManager

__all__ = [
    "dune_env_hack",
    "DuneUtil",
    "RocqDocManager",
]
