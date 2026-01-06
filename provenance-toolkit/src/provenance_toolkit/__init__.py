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
from .provenance import (
    ClassIdentityProvenanceData,
    ProvenanceVersionData,
    ReflectProvenanceData,
    WithClassIdentityProvenance,
    WithReflectProvenance,
    WithVersionProvenance,
)


class WithFullProvenance(
    WithClassIdentityProvenance,
    WithVersionProvenance,
    WithReflectProvenance,
):
    """All provenance mixins, for both classes and instances."""

    pass


class Provenance(
    metaclass=FinalNamespaceMeta,
    derive_from={
        # Abstract protocols:
        "Proto": WithProvenance,
        "ProtoClass": WithClassProvenance,
        "ProtoInstance": WithInstanceProvenance,
        # Concrete implementations:
        "ClassIdentity": WithClassIdentityProvenance,
        "Version": WithVersionProvenance,
        "Reflect": WithReflectProvenance,
    },
):
    T: TypeAlias = ProvenanceT  # noqa: UP040
    ComputeChecksumT: TypeAlias = ComputeChecksumProvenanceT  # noqa: UP040
    Proto: TypeAlias = WithProvenance  # noqa: UP040
    ProtoClass: TypeAlias = WithClassProvenance  # noqa: UP040
    ProtoInstance: TypeAlias = WithInstanceProvenance  # noqa: UP040
    ClassIdentity: TypeAlias = WithClassIdentityProvenance  # noqa: UP040
    ClassIdentityT: TypeAlias = ClassIdentityProvenanceData  # noqa: UP040
    Version: TypeAlias = WithVersionProvenance  # noqa: UP040
    VersionT: TypeAlias = ProvenanceVersionData  # noqa: UP040
    Reflect: TypeAlias = WithReflectProvenance  # noqa: UP040
    ReflectT: TypeAlias = ReflectProvenanceData  # noqa: UP040
    Full: TypeAlias = WithFullProvenance  # noqa: UP040


__all__: list[str] = [
    # core namespace classes
    "Provenance",
    # meta/
    "FinalNamespaceMeta",
]
