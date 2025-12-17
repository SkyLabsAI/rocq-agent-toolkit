from typing import Any, ClassVar, override

from provenance_toolkit import Signature, Version


class A(Signature.VersionProto, VERSION=Version.parse("0.0.1")):
    def __init__(self, *args: Any, **kwargs: Any) -> None:
        super().__init__(*args, **kwargs)


class B(A, VERSION=Version.parse("0.1.0")):
    STATIC_DATA: ClassVar[int] = 42

    def __init__(self, *args: Any, **kwargs: Any) -> None:
        super().__init__(*args, **kwargs)

    @override
    @classmethod
    def cls_signature(cls) -> str:
        return f"{cls.cls_version()}-{cls.STATIC_DATA}"


class C(A, VERSION=Version.parse("1.0.0")):
    def __init__(self, data: int, *args: Any, **kwargs: Any):
        self._data = data
        super().__init__(*args, **kwargs)

    @property
    def data(self) -> int:
        return self._data

    @override
    def signature(self) -> str:
        return f"{self.version()}-{self.data}"


class D(B, C, VERSION=Version.parse("2.0.0")):
    def __init__(self, *args: Any, data: int = 21718, **kwargs: Any):
        super().__init__(data, *args, **kwargs)


def test_A() -> None:
    assert A.cls_version() == Version.parse("0.0.1")
    assert A.cls_signature() == A.cls_version()
    assert A().signature() == A().version()

def test_B() -> None:
    assert B.cls_version() == Version.parse("0.1.0")
    assert B.cls_signature() == f"{B.cls_version()}-{B.STATIC_DATA}"
    assert B().signature() == B.cls_version()
    assert B().signature() == B().version()


def test_C() -> None:
    assert C.cls_version() == Version.parse("1.0.0")
    assert C.cls_signature() == C.cls_version()
    assert C(42).signature() == f"{C.cls_version()}-42"
    assert C(42).signature() != C(314).version()


def test_D() -> None:
    assert D.cls_version() == Version.parse("2.0.0")
    assert D.cls_signature() == f"{D.cls_version()}-{B.STATIC_DATA}"
    assert D().signature() == f"{D().version()}-{D().data}"
    assert D(data=65536).signature() != D().signature()
