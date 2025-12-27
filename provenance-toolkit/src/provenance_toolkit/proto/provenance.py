from abc import abstractmethod
from typing import override

from ..meta.mro_tracker import MROTracker
from .signature import WithSignature


class WithProvenance[PROVENANCE: WithSignature](WithSignature):
    @MROTracker.Meta.compute
    @classmethod
    @abstractmethod
    def cls_provenance(cls) -> PROVENANCE:
        """Compute rich provenance of [cls]."""
        raise NotImplementedError

    @MROTracker.Meta.compute
    def provenance(self) -> PROVENANCE:
        """Compute rich provenance of [cls]; default to cls_provenance()."""
        return self.cls_provenance()

    @override
    @classmethod
    def cls_signature(cls) -> str:
        return cls.cls_provenance().cls_signature()
