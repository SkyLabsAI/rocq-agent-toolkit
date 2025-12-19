"""Protocols for classes that have stable/unique (joint) signatures."""

from __future__ import annotations

import logging
from typing import Protocol, final, runtime_checkable

from .base import JoinSignatures, SignatureT

logger = logging.getLogger(__name__)


@runtime_checkable
class ComputeClassSignature(Protocol):
    """Core protocol for computing stable/unique class signatures."""

    @classmethod
    def compute_cls_signature(cls) -> SignatureT:
        """Compute stable/unique class signature."""
        raise NotImplementedError

    def compute_my_cls_signature(self) -> SignatureT:
        """Compute stable/unique class signature from an instance."""
        return self.compute_cls_signature()


class WithClassSignature(ComputeClassSignature):
    """Protocol for computing stable/unique (joint) class signatures."""

    @final
    @classmethod
    def cls_signature(
        cls,
        join: JoinSignatures[ComputeClassSignature] | None = None,
    ) -> SignatureT:
        """Compute joint class signature using each participating base of cls.

        Arguments:
          - join: optional override of the JoinSignatures protocol to use

        Returns:
          - str: a joint, stable/unique class signature
        """
        return SignatureT.join(cls.cls_signatures(), by=join)

    @final
    def my_cls_signature(
        self,
        join: JoinSignatures[ComputeClassSignature] | None = None,
    ) -> SignatureT:
        """Compute joint class signature using each participating base of cls.

        Arguments:
          - join: optional override of the JoinSignatures protocol to use

        Returns:
          - str: a joint, stable/unique class signature
        """
        return SignatureT.join(self.my_cls_signatures(), by=join)

    @final
    @classmethod
    def cls_signatures(
        cls,
    ) -> dict[type[ComputeClassSignature], SignatureT]:
        """Compute the stable/unique class signature for each participating base.

        Returns: dict, mapping each participating class type to its computed signature.
        """
        signatures = {}
        for klass in cls.mro():
            if klass is ComputeClassSignature:
                continue
            elif not issubclass(klass, ComputeClassSignature):
                continue
            signatures[klass] = klass.compute_cls_signature()
        return signatures

    @final
    def my_cls_signatures(
        self,
    ) -> dict[type[ComputeClassSignature], SignatureT]:
        """Compute the stable/unique class signature for each participating base.

        Returns: dict, mapping each participating class type to its computed signature.
        """
        signatures = {}
        for klass in type(self).mro():
            if klass is ComputeClassSignature:
                continue
            elif not issubclass(klass, ComputeClassSignature):
                continue
            signatures[klass] = klass.compute_my_cls_signature(self)
        return signatures
