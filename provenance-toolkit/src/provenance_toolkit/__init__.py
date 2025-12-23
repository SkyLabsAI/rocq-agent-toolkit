"""Core interface for the Signature protocol, plus concrete Provenance implementations."""

from typing import TypeAlias

from .meta import FinalNamespaceMeta
from .proto import (
    ComputeChecksumProvenanceT,
    ProvenanceT,
    WithClassProvenance,
    WithInstanceProvenance,
    WithProvenance,
)
from .provenance import ProvenanceVersionData, WithVersionProvenance


class Provenance(
    metaclass=FinalNamespaceMeta,
    derive_from={
        # Abstract protocols:
        "Proto": WithProvenance,
        "ProtoClass": WithClassProvenance,
        "ProtoInstance": WithInstanceProvenance,
        # Concrete implementations:
        "Version": WithVersionProvenance,
    },
):
    T: TypeAlias = ProvenanceT  # noqa: UP040
    ComputeChecksumT: TypeAlias = ComputeChecksumProvenanceT  # noqa: UP040
    Proto: TypeAlias = WithProvenance  # noqa: UP040
    ProtoClass: TypeAlias = WithClassProvenance  # noqa: UP040
    ProtoInstance: TypeAlias = WithInstanceProvenance  # noqa: UP040
    Version: TypeAlias = WithVersionProvenance  # noqa: UP040
    VersionT: TypeAlias = ProvenanceVersionData  # noqa: UP040


__all__: list[str] = [
    # core namespace classes
    "Provenance",
    # meta/
    "FinalNamespaceMeta",
]
