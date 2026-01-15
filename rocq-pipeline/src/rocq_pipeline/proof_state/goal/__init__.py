"""Hierarchy of structured goals.

Structured goals form a hierarchy (Rocq -> Iris) and consist
of immutable [goal_parts]. They may contain mutable state and expose
utilities for interacting with structured goals of a given kind.
"""

# ---------------------------------------------------------------------
# GOAL WRAPPER DEFINITIONS
#
# These are the "behavior" part of the goals. They wrap the 'Parts'
# dataclasses and provide a common interface and potential methods.
# The hierarchy (from base to derived) is:
#   RocqGoal -> IrisGoal
# and clients can extend this hierarchy.
# ---------------------------------------------------------------------

# NOTE: because [RocqGoal -> IrisGoal], it is
# important that we import them in this order and /not/
# alphabetical order.
from rocq_pipeline.proof_state.goal.rocq import RocqGoal  # isort:skip
from rocq_pipeline.proof_state.goal.iris import IrisGoal  # isort:skip


__all__ = [
    "RocqGoal",
    "IrisGoal",
]
