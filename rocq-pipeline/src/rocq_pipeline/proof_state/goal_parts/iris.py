from dataclasses import dataclass, field
from typing import override

from .rocq import RocqGoalParts


@dataclass(frozen=True)
class IrisGoalParts(RocqGoalParts):
    """Structured parts of a single Iris goal.

    This is a frozen dataclass; member functions should only be
    const helpers for working with the structured data.
    """

    # --- Fields ---
    # Iris persistent hypotheses, of the form ["<NAME>" : <RESOURCE>].
    iris_pers_hyps: dict[str, str] = field(default_factory=dict, kw_only=True)
    # Iris persistent hypotheses, of the form [_ : <RESOURCE>].
    iris_pers_hyps_anon: set[str] = field(default_factory=set, kw_only=True)
    # Iris spatial hypotheses, of the form ["<NAME>" : <RESOURCE>].
    iris_spat_hyps: dict[str, str] = field(default_factory=dict, kw_only=True)
    # Iris spatial hypotheses, of the form ["<NAME>" : <RESOURCE>].
    iris_spat_hyps_anon: set[str] = field(default_factory=set, kw_only=True)
    # Iris spatial conclusion
    #
    # NOTE: we could impose additional structure, e.g. by breaking apart
    # top-level separating conjuncts when possible.
    iris_spat_concl: str = field(kw_only=True)

    @override
    def wellformed(self) -> bool:
        # An Iris goal MUST have a non-empty spatial conclusion
        return super().wellformed() and self.iris_spat_concl != ""
