from __future__ import annotations

import logging
from typing import Any, ClassVar, override

from semver import Version

from ..proto.provenance import WithProvenance

logger = logging.getLogger(__name__)


class WithVersionProvenance(WithProvenance):
    """Protocol for types that use version information for produce signatures."""

    @classmethod
    def cls_version(cls) -> Version:
        """Compute stable/unique signature of [cls]."""
        return WithVersionProvenance._VERSION(cls)

    def version(self) -> Version:
        """Compute the stable/unique signature of [self]; default to cls_signature()."""
        return self.cls_version()

    @override
    @classmethod
    def cls_signature(cls) -> str:
        return str(cls.cls_version())

    @override
    def signature(self) -> str:
        return str(self.version())

    def __init__(self, *args: Any, **kwargs: Any) -> None:
        return super().__init__(*args, **kwargs)

    @classmethod
    def __init_subclass__(cls, *, VERSION: Version, **kwargs) -> None:
        WithVersionProvenance.__WithVersionProvenance_VERSIONS[cls] = VERSION
        return super().__init_subclass__(**kwargs)

    @staticmethod
    def _VERSION(cls: type[WithVersionProvenance]) -> Version:
        return WithVersionProvenance.__WithVersionProvenance_VERSIONS[cls]

    __WithVersionProvenance_VERSIONS: ClassVar[
        dict[type[WithVersionProvenance], Version]
    ] = {}
