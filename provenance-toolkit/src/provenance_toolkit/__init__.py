"""Core interface for the Signature protocol, plus concrete Provenance implementations."""

from typing import TypeAlias

from semver import Version

from .meta import FinalNamespaceMeta
from .proto import WithProvenance, WithSignature
from .provenance import WithVersionProvenance


class Signature(
    metaclass=FinalNamespaceMeta,
    derive_from={
        "Proto": WithSignature,
    },
):
    Proto: TypeAlias = WithSignature  # noqa: UP040


class Provenance(
    metaclass=FinalNamespaceMeta,
    derive_from={
        "Proto": WithProvenance,
        "Version": WithVersionProvenance,
    },
):
    Proto: TypeAlias = WithProvenance  # noqa: UP040
    Version: TypeAlias = WithVersionProvenance  # noqa: UP040


__all__: list[str] = [
    "Version",
    "Signature",
    "Provenance",
    # meta/
    "FinalNamespaceMeta",
]
