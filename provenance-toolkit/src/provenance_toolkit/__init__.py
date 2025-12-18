"""Base classes for participating in the Signature / Provenance protocols.

You can derive directly from the top-level classes if you want to provide custom

"""

from typing import TypeAlias

from .meta import (
    FinalNamespaceMeta,
    MROTracker,
)
from .method_types import MethodTypes, MethodWrapper, wrap_method
from .proto import Version, WithProvenance, WithSignature, WithVersionSignature


class Signature(
    metaclass=FinalNamespaceMeta,
    derive_from={
        "Proto": WithSignature,
        "VersionProto": WithVersionSignature,
        # "VersionMeta": VersionSignatureMeta,
    },
):
    Proto: TypeAlias = WithSignature  # noqa: UP040
    VersionProto: TypeAlias = WithVersionSignature  # noqa: UP040
    # VersionMeta: TypeAlias = VersionSignatureMeta  # noqa: UP040


class Provenance(
    metaclass=FinalNamespaceMeta,
    derive_from={
        "Proto": WithProvenance,
        # "Derive": DeriveProvenanceMeta,
    },
):
    Proto: TypeAlias = WithProvenance  # noqa: UP040
    # DeriveMeta: TypeAlias = DeriveProvenanceMeta  # noqa: UP040


__all__: list[str] = [
    "Version",
    "Signature",
    "Provenance",
    # meta/
    "FinalNamespaceMeta",
    "MROTracker",
    # method_types.py
    "MethodTypes",
    "MethodWrapper",
    "wrap_method",
]
