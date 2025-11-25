from .classes import Agent, AgentBuilder, ProofAgent
from .dataclasses import (
    AgentConfig,
    Finished,
    GiveUp,
    TacticApplication,
    TaskResult,
)

__all__: list[str] = [
    # dataclasses.py
    "AgentConfig",
    "Finished",
    "GiveUp",
    "TacticApplication",
    "TaskResult",
    # classes.py,
    "Agent",
    "AgentBuilder",
    "ProofAgent",
]
