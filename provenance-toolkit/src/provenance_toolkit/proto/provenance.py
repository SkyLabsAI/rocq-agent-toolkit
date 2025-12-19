"""Protocols for classes and instances that have rich provenance data."""

from __future__ import annotations

import logging
from abc import abstractmethod
from typing import final, override

from .signature import ComputeSignature, SignatureT, WithSignature

logger = logging.getLogger(__name__)


class ProvenanceData(WithSignature):
    """Protocol for types that can be used as rich provenance data."""

    @abstractmethod
    def is_cls_provenance(self) -> bool:
        """Predicate: whether self is class provenance data."""

    def is_instance_provenance(self) -> bool:
        """Predicate: whether self is instance provenance data."""
        return not self.is_cls_provenance()

    @abstractmethod
    def to_signature(self) -> SignatureT:
        """Compute a stable/unique signatuer from the rich provenance data."""

    # Note: leaving compute_cls_signature NotImplemented
    @override
    def compute_my_cls_signature(self) -> SignatureT:
        """Compute stable/unique class signature."""
        if not self.is_cls_provenance():
            raise ValueError(f"not class provenance: {self}")
        return self.to_signature()

    @override
    def compute_signature(self) -> SignatureT:
        """Compute the stable/unique instance signature; default to cls_signature()."""
        if not self.is_instance_provenance():
            raise ValueError(f"not instance provenance: {self}")
        return self.to_signature()


class ComputeProvenance(ComputeSignature):
    """Core protocol for rich class & instance provenance data.

    Note: derivers are obliged to uniformly supply class /and/ instance provenance
    data.
    """

    @classmethod
    @abstractmethod
    def compute_cls_provenance(cls) -> ProvenanceData:
        """Compute rich provenance of self.__class__."""
        raise NotImplementedError

    def compute_provenance(self) -> ProvenanceData:
        """Compute rich provenance of [cls]; default to cls_provenance()."""
        return self.compute_cls_provenance()


class WithProvenance(ComputeProvenance, WithSignature):
    """Protocol for computing rich class & instance provenance data."""

    @final
    @classmethod
    def cls_provenances(
        cls,
    ) -> dict[type[ComputeProvenance], ProvenanceData]:
        """Compute the rich class provenance for each participating base of cls.

        Returns: dict, mapping each participating class type to its computed provenance.
        """
        provenances = {}
        for klass in cls.mro():
            if klass is ComputeProvenance:
                continue
            elif not issubclass(klass, ComputeProvenance):
                continue
            provenances[klass] = klass.compute_cls_provenance()
        return provenances

    @final
    def provenances(
        self,
    ) -> dict[type[ComputeProvenance], ProvenanceData]:
        """Compute the rich instance provenance for each participating base of cls.

        Returns: dict, mapping each participating class type to its computed signature.
        """
        provenances = {}
        for klass in type(self).mro():
            if klass is ComputeProvenance:
                continue
            elif not issubclass(klass, ComputeProvenance):
                continue
            provenances[klass] = klass.compute_provenance(self)
        return provenances

    @override
    @classmethod
    def compute_cls_signature(cls) -> SignatureT:
        cls_provenance = cls.compute_cls_provenance()
        return SignatureT.join(
            {
                cls: super().compute_cls_signature(),
                type(cls_provenance): cls_provenance.to_signature(),
            },
        )

    @override
    def compute_signature(self) -> SignatureT:
        provenance = self.compute_provenance()
        return SignatureT.join(
            {
                type(self): super().compute_my_cls_signature(),
                type(provenance): provenance.to_signature(),
            },
        )
