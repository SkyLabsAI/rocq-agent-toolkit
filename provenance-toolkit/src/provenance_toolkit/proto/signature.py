from __future__ import annotations

import logging
from abc import abstractmethod
from typing import Any, ClassVar, override

from semver import Version

from ..meta.mro_tracker import MROTracker

logger = logging.getLogger(__name__)


class WithSignature(metaclass=MROTracker.Meta):
    """Protocol for types that can produce stable/unique class & instance signatures."""

    @MROTracker.Meta.compute_classmethod
    @classmethod
    @abstractmethod
    def cls_signature(cls) -> str:
        """Compute stable/unique signature of [cls]."""
        raise NotImplementedError

    @MROTracker.Meta.compute
    def signature(self) -> str:
        """Compute the stable/unique signature of [self]; default to cls_signature()."""
        return self.cls_signature()

    def __init__(self, *args: Any, **kwargs: Any) -> None:
        return super().__init__(*args, **kwargs)


class WithVersionSignature(WithSignature):
    """Protocol for types that use version information for produce signatures."""

    @MROTracker.Meta.compute
    @classmethod
    def cls_version(cls) -> Version:
        """Compute stable/unique signature of [cls]."""
        return WithVersionSignature._VERSION(cls)

    @MROTracker.Meta.compute
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
        WithVersionSignature.__WithVersionSignature_VERSIONS[cls] = VERSION
        return super().__init_subclass__(**kwargs)

    @staticmethod
    def _VERSION(cls: type[WithVersionSignature]) -> Version:
        return WithVersionSignature.__WithVersionSignature_VERSIONS[cls]

    __WithVersionSignature_VERSIONS: ClassVar[
        dict[type[WithVersionSignature], Version]
    ] = {}
