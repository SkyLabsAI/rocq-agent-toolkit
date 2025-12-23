"""Protocols for instances that have provenance data.

cf. __init__.py for more details."""

from __future__ import annotations

import logging
from typing import Protocol, final, runtime_checkable

from .base import ComputeChecksumProvenanceT, ProvenanceT

logger = logging.getLogger(__name__)


@runtime_checkable
class _ComputeInstanceProvenance(Protocol):
    """Protocol for computing instance provenance data."""

    def compute_provenance(self) -> dict[type[WithInstanceProvenance], ProvenanceT]:
        """Compute rich provenance of self.

        Returns a dictionary mapping each provenance provider type to its provenance data.
        Classes should use super() to get parent provenance and add their own entry.
        """
        return {}


class WithInstanceProvenance(_ComputeInstanceProvenance):
    """Extension Point: protocol for computing instance provenance data.

    The core API is:
    - `checksum()` -> str:
       Compute a semi-stable checksum for the provenance data for self.
    - `checksums()` -> dict[type[WithInstanceProvenance], str]:
       Compute the checksums of provenance data for self, keyed by the type of the class
       that computed it.
    - `provenance()` -> dict[type[WithInstanceProvenance], ProvenanceT]:
       Compute provenance data for self, keyed by the type of the class that
       computed it.

    Classes should override `compute_provenance()` to return a dictionary mapping
    their provenance provider type to their provenance data. They should use super()
    to get parent provenance dictionaries and merge them with their own entry.

    Note: cf. provenance-toolkit/src/examples/ for more details.
    """

    @final
    def checksum(
        self,
        *,
        by: ComputeChecksumProvenanceT | None = None,
    ) -> str:
        """Compute checksum from joint instance provenance."""
        return ProvenanceT.joint_checksum(self.provenance(), by=by)

    @final
    def checksums(
        self,
        *,
        by: ComputeChecksumProvenanceT | None = None,
    ) -> dict[type[WithInstanceProvenance], str]:
        """Compute checksums for each participating base class.

        Returns: dict, mapping each participating class type to its computed checksum.
        """
        return {
            klass: provenance.checksum(by=by)
            for klass, provenance in self.provenance().items()
        }

    @final
    def provenance(
        self,
    ) -> dict[type[WithInstanceProvenance], ProvenanceT]:
        """Compute provenance data for self.

        Returns: dict, mapping each provenance provider type to its computed provenance data.

        Note: cf. class docstring for more details.
        """
        return self.compute_provenance()
