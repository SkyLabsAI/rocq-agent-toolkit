from __future__ import annotations

import logging
from abc import abstractmethod
from typing import Any, ClassVar, Protocol, override, runtime_checkable

from semver import Version

logger = logging.getLogger(__name__)


@runtime_checkable
class WithSignature(Protocol):
    """Protocol for types that can produce stable/unique class & instance signatures."""

    @classmethod
    @abstractmethod
    def cls_signature(cls) -> str:
        """Compute stable/unique signature of [cls]."""
        raise NotImplementedError

    def signature(self) -> str:
        """Compute the stable/unique signature of [self]; default to cls_signature()."""
        return self.cls_signature()

    def __init__(self, *args: Any, **kwargs: Any) -> None:
        return super().__init__(*args, **kwargs)


@runtime_checkable
class WithVersionSignature(WithSignature, Protocol):
    """Protocol for types that use version information for produce signatures."""

    @classmethod
    def cls_version(cls) -> Version:
        """Compute stable/unique signature of [cls]."""
        print(f"!!! {cls}")
        return WithVersionSignature._VERSION(cls)

    def version(self) -> Version:
        """Compute the stable/unique signature of [self]; default to cls_signature()."""
        print(f"!!! {self}")
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

    __WithVersionSignature_VERSIONS: ClassVar[dict[type[WithVersionSignature], Version]] = {}
