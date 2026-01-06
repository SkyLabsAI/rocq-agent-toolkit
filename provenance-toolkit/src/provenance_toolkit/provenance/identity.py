"""Class identity provenance - includes class qualname in provenance data.

This module provides a mixin that adds the class qualified name to provenance data,
ensuring that different classes have unique checksums even if they share the same
version string.

cf. __init__.py for more details."""

from __future__ import annotations

import logging
from typing import Any, override

from ..proto import (
    ProvenanceT,
    WithClassProvenance,
    WithInstanceProvenance,
    WithProvenance,
)

logger = logging.getLogger(__name__)


class ClassIdentityProvenanceData(ProvenanceT):
    """Provenance data that captures the fully qualified class name (module + qualname) and direct base classes."""

    def __init__(self, cls: type) -> None:
        self._cls = cls

    def __eq__(self, other: Any) -> Any:
        super_eq = super().__eq__(other)
        if super_eq is NotImplemented:
            return NotImplemented
        return self._cls is other._cls

    @property
    def cls(self) -> type:
        """Return the class reference."""
        return self._cls

    @property
    def module(self) -> str:
        return self._cls.__module__

    @property
    def qualname(self) -> str:
        return self._cls.__qualname__

    @property
    def bases(self) -> tuple[type, ...]:
        """Return tuple of direct base class types."""
        return self._cls.__bases__

    @staticmethod
    def full_qualname(class_type: type) -> str:
        """Return the fully qualified name: module.qualname"""
        return f"{class_type.__module__}.{class_type.__qualname__}"

    @override
    def is_cls_provenance(self) -> bool:
        return True

    @override
    def is_instance_provenance(self) -> bool:
        return True

    @override
    def stable_serialize(self) -> str:
        """Serialize to a stable string format including module, qualname, and bases."""
        bases = self.bases
        if not bases:
            return ClassIdentityProvenanceData.full_qualname(self._cls)
        # Format: module.qualname[bases]
        # Each base is formatted as module.qualname
        bases_str = ",".join(
            ClassIdentityProvenanceData.full_qualname(base) for base in bases
        )
        return f"{ClassIdentityProvenanceData.full_qualname(self._cls)}({bases_str})"


class WithClassIdentityProvenance(WithProvenance):
    """Protocol for types that include class identity in their provenance.

    This mixin adds the class's fully qualified name (module + qualname) to the
    provenance data, ensuring that different classes have unique checksums even
    if they share the same version string or other provenance attributes.
    """

    @override
    @classmethod
    def compute_cls_provenance(cls) -> dict[type[WithClassProvenance], ProvenanceT]:
        result = super().compute_cls_provenance()
        result[WithClassIdentityProvenance] = ClassIdentityProvenanceData(cls)
        return result

    @override
    def compute_provenance(self) -> dict[type[WithInstanceProvenance], ProvenanceT]:
        result = super().compute_provenance()
        result[WithClassIdentityProvenance] = ClassIdentityProvenanceData(type(self))
        return result

    def __init__(self, *args: Any, **kwargs: Any) -> None:
        super().__init__(*args, **kwargs)
