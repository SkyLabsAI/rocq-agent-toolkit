"""Protocols for instances that have stable/unique (joint) signatures."""

from __future__ import annotations

import logging
from typing import final

from .base import JoinSignatures, SignatureT
from .for_class import ComputeClassSignature, WithClassSignature

logger = logging.getLogger(__name__)


class ComputeSignature(ComputeClassSignature):
    """Core protocol for computing stable/unique class & instance signatures."""

    def compute_signature(self) -> SignatureT:
        """Compute the stable/unique instance signature; default to cls_signature()."""
        return self.compute_my_cls_signature()


class WithSignature(ComputeSignature, WithClassSignature):
    """Protocol for computing stable/unique (joint) class signatures."""

    @final
    def signature(
        self,
        join: JoinSignatures | None = None,
    ) -> SignatureT:
        """Compute the joint instance signature using each participating base of cls.

        Arguments:
          - join: optional override of the JoinSignatures protocol to use

        Returns:
          - str: a joint, stable/unique instance signature
        """
        return SignatureT.join(self.signatures(), instance=True, by=join)

    @final
    def signatures(
        self,
    ) -> dict[type[ComputeSignature], SignatureT]:
        """Compute the stable/unique instance signature for each participating base.

        Returns: dict, mapping each participating class type to its computed signature.
        """
        signatures = {}
        for klass in type(self).mro():
            if klass is ComputeSignature:
                continue
            elif not issubclass(klass, ComputeSignature):
                continue
            signatures[klass] = klass.compute_signature(self)
        return signatures
