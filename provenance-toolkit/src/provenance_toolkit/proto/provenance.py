from __future__ import annotations

import logging
from abc import abstractmethod
from typing import override

from .signature import WithSignature

logger = logging.getLogger(__name__)


class WithProvenance[PROVENANCE: WithSignature](WithSignature):
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
