from __future__ import annotations

import logging
from abc import abstractmethod
from typing import Any

logger = logging.getLogger(__name__)


class WithSignature:
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
