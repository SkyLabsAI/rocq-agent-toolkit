from abc import abstractmethod
from typing import Protocol, override, runtime_checkable

from .signature import WithSignature


@runtime_checkable
class WithProvenance[PROVENANCE: WithSignature](WithSignature, Protocol):
    @classmethod
    @abstractmethod
    def cls_provenance(cls) -> PROVENANCE:
        """Compute rich provenance of [cls]."""
        raise NotImplementedError

    def provenance(self) -> PROVENANCE:
        """Compute rich provenance of [cls]; default to cls_provenance()."""
        return self.cls_provenance()

    @override
    @classmethod
    def cls_signature(cls) -> str:
        return cls.cls_provenance().cls_signature()
