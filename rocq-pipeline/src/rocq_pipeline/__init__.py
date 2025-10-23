"""Rocq Pipeline: A framework for automated theorem proving with Coq.

This package provides agents, locators, and task runners for automated
theorem proving workflows with Coq documents.
"""

# Import modules for organized access
from . import agent
from . import auto_agent
from . import locator
from . import task_runner
from . import tasks

# Expose core result types and common agents at top level
from .agent import Agent, GiveUp, Finished, Tactic
from .auto_agent import AutoAgent
from .locator import parse_locator

__version__ = "0.1.0"
__all__ = [
    # Modules for organized access
    "agent",
    "auto_agent",
    "locator",
    "task_runner",
    "tasks",
    # Core types at top level
    "Agent",
    "GiveUp",
    "Finished",
    "Tactic",
    "AutoAgent",
    "parse_locator",
]
