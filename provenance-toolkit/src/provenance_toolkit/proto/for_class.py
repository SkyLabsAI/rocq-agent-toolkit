"""Protocols for classes that have provenance data.

cf. __init__.py for more details."""

from __future__ import annotations

import logging
from collections.abc import Mapping, MutableMapping
from typing import Protocol, final, runtime_checkable

from .base import ComputeChecksumProvenanceT, ProvenanceT

logger = logging.getLogger(__name__)


@runtime_checkable
class _ComputeClassProvenance(Protocol):
    """Protocol for computing class provenance data."""

    @classmethod
    def compute_cls_provenance(
        cls,
    ) -> MutableMapping[type[WithClassProvenance], ProvenanceT]:
        """Compute rich provenance of klass (mutable variant for cooperative inheritance).

        Returns a mutable dictionary mapping each provenance provider type to its provenance data.
        Classes should use super() to get parent provenance and add their own entry.
        """
        return {}


class WithClassProvenance(_ComputeClassProvenance):
    """Extension Point: protocol for computing class provenance data.

    The core API is:
    - `cls_checksum()` -> str:
       Compute a semi-stable checksum for the provenance data for cls.
    - `cls_checksums()` -> Mapping[type[WithClassProvenance], str]:
       Compute the checksums of provenance data for cls, keyed by the type of the class
       that computed it.
    - `cls_provenance_json()` -> dict[str, str]:
       Compute provenance JSON data for cls, keyed by the type of the class that
       computed it.
    - `cls_provenance()` -> Mapping[type[WithClassProvenance], ProvenanceT]:
       Compute provenance data for cls, keyed by the type of the class that
       computed it.

    Classes should override `compute_cls_provenance()` to return a mutable dictionary mapping
    their provenance provider type to their provenance data. They should use super()
    to get parent provenance dictionaries and merge them with their own entry.

    Note: cf. provenance-toolkit/src/examples/ for more details.
    """

    @final
    @classmethod
    def cls_checksum(
        cls,
        *,
        by: ComputeChecksumProvenanceT | None = None,
    ) -> str:
        """Compute checksum from joint class provenance."""
        return ProvenanceT.joint_checksum(cls.cls_provenance(), by=by)

    @final
    @classmethod
    def cls_checksums(
        cls,
        *,
        by: ComputeChecksumProvenanceT | None = None,
    ) -> Mapping[type[WithClassProvenance], str]:
        """Compute checksums for each participating base class.

        Returns: Mapping, mapping each participating class type to its computed checksum.
        """
        return {
            klass: provenance.checksum(by=by)
            for klass, provenance in cls.cls_provenance().items()
        }

    @final
    @classmethod
    def cls_provenance_json(
        cls,
    ) -> dict[str, str]:
        """Compute JSON serialized provenance data for cls.

        Returns: dict, mapping each provenance provider type qualname to its serialized provenance data.

        Note: cf. class docstring for more details.
        """
        return {
            klass.__qualname__: prov.stable_serialize()
            for klass, prov in cls.cls_provenance().items()
        }

    @final
    @classmethod
    def cls_provenance(
        cls,
    ) -> Mapping[type[WithClassProvenance], ProvenanceT]:
        """Compute provenance data for cls.

        Returns: Mapping, mapping each provenance provider type to its computed provenance data.

        Note: cf. class docstring for more details.
        """
        return cls.compute_cls_provenance()
