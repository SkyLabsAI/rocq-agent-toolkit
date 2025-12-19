"""Base types & protocols for working with stable/unique signatures."""

from __future__ import annotations

import logging
from typing import Any, Protocol, final, runtime_checkable

logger = logging.getLogger(__name__)

type RawSignatureT = str


@runtime_checkable
class JoinSignatures[OBJ](Protocol):
    """Protocol for joining signatures from multiple objects."""

    def __call__(
        self,
        signatures: dict[type[OBJ], RawSignatureT],
        *,
        instance: bool = False,
    ) -> RawSignatureT: ...


class DefaultJoinSignatures[OBJ](JoinSignatures[OBJ]):
    def __call__(
        self,
        signatures: dict[type[OBJ], RawSignatureT],
        *,
        instance: bool = False,
    ) -> RawSignatureT:
        """Default implementation of JoinSignatures.

        Uniformly handles joining of class and instance signatures as
        ```
        "+".join(f"{klass.__qualname__}@{sig}" for klass, sig in signatures)
        ```
        """
        return "+".join(
            f"{klass.__qualname__}@{sig}" for klass, sig in signatures.items()
        )


class SignatureT:
    def __init__(self, raw: RawSignatureT) -> None:
        self._raw = raw

    @property
    def raw(self) -> RawSignatureT:
        return self._raw

    def __eq__(self, other: Any) -> Any:
        if type(self.raw) is not type(other.raw):
            return NotImplemented
        return self.raw == other.raw

    def __str__(self) -> str:
        return str(self.raw)

    def __repr__(self) -> str:
        return repr(self.raw)

    @final
    @staticmethod
    def join[OBJ](
        signatures: dict[type[OBJ], SignatureT],
        *,
        instance: bool = False,
        by: JoinSignatures[OBJ] | None = None,
    ) -> SignatureT:
        if by is None:
            by = DefaultJoinSignatures()
        return SignatureT(
            by(
                {k: s.raw for k, s in signatures.items()},
                instance=instance,
            )
        )
