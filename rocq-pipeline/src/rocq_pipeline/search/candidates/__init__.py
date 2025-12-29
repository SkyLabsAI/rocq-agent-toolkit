"""
Layer 3: Candidate generation for proof search.

This module provides protocols and adapters for generating and correcting
candidate actions (tactics, moves, etc.) from state descriptions.
Implementations (e.g., LLM-based generators) live in application code.
"""

from .core import (
    Candidate,
    CandidateGenerator,
    CandidateRectifier,
    GeneratorStrategy,
)

__all__ = [
    "Candidate",
    "CandidateGenerator",
    "CandidateRectifier",
    "GeneratorStrategy",
]
