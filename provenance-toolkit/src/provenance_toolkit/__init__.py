"""Core interface for the Signature protocol, plus concrete Provenance implementations."""

from typing import TypeAlias

from semver import Version

from .meta import FinalNamespaceMeta
from .proto import (
    ComputeProvenance,
    ComputeSignature,
    JoinSignatures,
    WithProvenance,
    WithSignature,
)
from .provenance import WithVersionProvenance


class Signature(
    metaclass=FinalNamespaceMeta,
    derive_from={
        "Proto": WithSignature,
    },
):
    CoreProto: TypeAlias = ComputeSignature  # noqa: UP040
    Join: TypeAlias = JoinSignatures  # noqa: UP040
    Proto: TypeAlias = WithSignature  # noqa: UP040


class Provenance(
    metaclass=FinalNamespaceMeta,
    derive_from={
        "Proto": WithProvenance,
        "Version": WithVersionProvenance,
    },
):
    CoreProto: TypeAlias = ComputeProvenance  # noqa: UP040
    Proto: TypeAlias = WithProvenance  # noqa: UP040
    Version: TypeAlias = WithVersionProvenance  # noqa: UP040


__all__: list[str] = [
    # re-export semver.Version
    "Version",
    # core namespace classes
    "Signature",
    "Provenance",
    # meta/
    "FinalNamespaceMeta",
]
