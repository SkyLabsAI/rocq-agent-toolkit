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


class ProvenanceClassIdentityData(ProvenanceT):
    """Provenance data that captures the fully qualified class name (module + qualname)."""

    def __init__(self, module: str, qualname: str) -> None:
        self._module = module
        self._qualname = qualname

    def __eq__(self, other: Any) -> Any:
        super_eq = super().__eq__(other)
        if super_eq is NotImplemented:
            return NotImplemented
        return self.module == other.module and self.qualname == other.qualname

    @property
    def module(self) -> str:
        return self._module

    @property
    def qualname(self) -> str:
        return self._qualname

    @property
    def full_qualname(self) -> str:
        """Return the fully qualified name: module.qualname"""
        return f"{self._module}.{self._qualname}"

    @override
    def is_cls_provenance(self) -> bool:
        return True

    @override
    def is_instance_provenance(self) -> bool:
        return True

    @override
    def stable_serialize(self) -> str:
        return self.full_qualname


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
        result[WithClassIdentityProvenance] = ProvenanceClassIdentityData(
            cls.__module__,
            cls.__qualname__,
        )
        return result

    @override
    def compute_provenance(self) -> dict[type[WithInstanceProvenance], ProvenanceT]:
        result = super().compute_provenance()
        result[WithClassIdentityProvenance] = ProvenanceClassIdentityData(
            self.__class__.__module__,
            self.__class__.__qualname__,
        )
        return result

    def __init__(self, *args: Any, **kwargs: Any) -> None:
        super().__init__(*args, **kwargs)

