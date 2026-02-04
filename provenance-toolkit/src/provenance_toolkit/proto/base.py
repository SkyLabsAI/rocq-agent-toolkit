"""Base types for provenance data.

cf. __init__.py for more details."""

from __future__ import annotations

import hashlib
import json
from abc import ABC, abstractmethod
from collections.abc import Mapping
from typing import Any, Protocol, final, runtime_checkable


@runtime_checkable
class ComputeChecksumProvenanceT(Protocol):
    """Protocol for computing pseudo-unique checksum for provenance data."""

    def __call__(self, provenance: bytes | str | ProvenanceT) -> str: ...


class DefaultComputeChecksumProvenanceT(ComputeChecksumProvenanceT):
    """Default: use hashlib.md5 to compute the checksum for provenance data.

    Note: set usedforsecurity=False, since it's only used for agent identity.
    """

    def __call__(self, provenance: bytes | str | ProvenanceT) -> str:
        prov_bytes: bytes
        if isinstance(provenance, bytes):
            prov_bytes = provenance
        elif isinstance(provenance, str):
            prov_bytes = provenance.encode("utf-8")
        elif isinstance(provenance, ProvenanceT):
            prov_bytes = provenance.stable_serialize().encode("utf-8")
        else:
            raise ValueError(f"Invalid provenance type: {type(provenance)}")

        return hashlib.md5(prov_bytes, usedforsecurity=False).hexdigest()


class ProvenanceT(ABC):
    """Protocol for types that track class/instance provenance information."""

    def __eq__(self, other: Any) -> Any:
        if type(self) is not type(other):
            return NotImplemented
        return True

    def __str__(self) -> str:
        return self.stable_serialize()

    @abstractmethod
    def stable_serialize(self) -> str:
        """Convert provenance to a stable string for checksum computation."""
        raise NotImplementedError

    @abstractmethod
    def is_cls_provenance(self) -> bool:
        """Predicate: whether self is class provenance data."""
        raise NotImplementedError

    def is_instance_provenance(self) -> bool:
        """Predicate: whether self is instance provenance data."""
        return not self.is_cls_provenance()

    @final
    def checksum(
        self,
        *,
        by: ComputeChecksumProvenanceT | None = None,
    ) -> str:
        """Compute a semi-stable checksum for this provenance data."""
        if by is None:
            by = DefaultComputeChecksumProvenanceT()

        return by(self)

    @final
    @staticmethod
    def joint_checksum[K: type](
        provenances: Mapping[K, ProvenanceT],
        *,
        by: ComputeChecksumProvenanceT | None = None,
    ) -> str:
        """Compute a semi-stable checksum for a collection of provenance data."""
        if by is None:
            by = DefaultComputeChecksumProvenanceT()

        prov_checksums = {
            provenance_provider_klass.__qualname__: prov.checksum(by=by)
            for provenance_provider_klass, prov in provenances.items()
        }
        stable_prov_checksum_bytes = json.dumps(
            prov_checksums,
            sort_keys=True,
            ensure_ascii=False,
        ).encode("utf-8")

        return by(stable_prov_checksum_bytes)
