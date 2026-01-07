from __future__ import annotations

import logging
from typing import Any, ClassVar, override

from semver import Version

from ..proto import (
    ProvenanceT,
    WithClassProvenance,
    WithInstanceProvenance,
    WithProvenance,
)

logger = logging.getLogger(__name__)


class ProvenanceVersionData(ProvenanceT):
    def __init__(self, version: str | Version | None) -> None:
        self._version: Version | None = None
        if version is not None:
            if isinstance(version, Version):
                self._version = version
            else:
                assert isinstance(version, str)
                self._version = Version.parse(version)

    def __eq__(self, other: Any) -> Any:
        super_eq = super().__eq__(other)
        if super_eq is NotImplemented:
            return NotImplemented
        elif not super_eq:
            return False
        return self.version == other.version

    @property
    def version(self) -> Version | None:
        return self._version

    @override
    def is_cls_provenance(self) -> bool:
        return True

    @override
    def is_instance_provenance(self) -> bool:
        return True

    @override
    def stable_serialize(self) -> str:
        return str(self._version)


class WithVersionProvenance(WithProvenance):
    """Protocol for types that use version information for produce signatures."""

    @override
    @classmethod
    def compute_cls_provenance(cls) -> dict[type[WithClassProvenance], ProvenanceT]:
        result = super().compute_cls_provenance()
        result[WithVersionProvenance] = WithVersionProvenance._VERSION(cls)
        return result

    @override
    def compute_provenance(self) -> dict[type[WithInstanceProvenance], ProvenanceT]:
        result = super().compute_provenance()
        result[WithVersionProvenance] = WithVersionProvenance._VERSION(self.__class__)
        return result

    @classmethod
    def cls_version(cls) -> Version | None:
        """Compute stable/unique signature of [cls]."""
        return WithVersionProvenance._VERSION(cls).version

    def version(self) -> Version | None:
        """Compute the stable/unique signature of [self]; default to cls_signature()."""
        return WithVersionProvenance._VERSION(self.__class__).version

    def __init__(self, *args: Any, **kwargs: Any) -> None:
        super().__init__(*args, **kwargs)

    @classmethod
    def __init_subclass__(
        cls, *, VERSION: str | Version | None = None, **kwargs
    ) -> None:
        prov_version = ProvenanceVersionData(VERSION)
        WithVersionProvenance.__WithVersionProvenance_VERSIONS[cls] = prov_version
        return super().__init_subclass__(**kwargs)

    @staticmethod
    def _VERSION(klass: type[WithVersionProvenance]) -> ProvenanceVersionData:
        return WithVersionProvenance.__WithVersionProvenance_VERSIONS[klass]

    __WithVersionProvenance_VERSIONS: ClassVar[
        dict[type[WithVersionProvenance], ProvenanceVersionData]
    ] = {}
