"""Auto agent implementation for automated theorem proving.

This module provides a simple agent that uses Coq's 'auto' tactic
for automated proof completion.
"""

from rocq_pipeline.agent import OneShotAgent


class AutoAgent(OneShotAgent):
    """An agent that uses Coq's 'auto' tactic for proof completion.

    This is a simple one-shot agent that attempts to complete proofs
    using Coq's built-in 'auto' tactic, which tries to solve goals
    automatically using a database of hints.
    """

    def __init__(self):
        """Initialize the auto agent with the 'auto' tactic."""
        super().__init__("auto")
