from abc import abstractmethod
from typing import Any, override

from provenance_toolkit import Provenance


class A(Provenance.Base):
    @Provenance.register
    @classmethod
    def foo(cls) -> int:
        return 42

    @Provenance.register
    @abstractmethod
    def bar(self) -> int:
        raise NotImplementedError


class B(A):
    @override
    def bar(self) -> int:
        return self.my_cls_logic() + self.my_logic()

    @Provenance.compute
    @classmethod
    def my_cls_logic(cls) -> int:
        return 300

    @Provenance.compute
    def my_logic(self) -> int:
        return 14


def test_B() -> None:
    assert B.foo() == 42
    assert B().bar() == 314


class C(A):
    @override
    def bar(self) -> int:
        return 21718


def test_C() -> None:
    assert C.foo() == 42
    assert C().bar() == 21718


class D(B, C):
    @override
    @classmethod
    def foo(cls) -> int:
        return 24

    @override
    def bar(self) -> int:
        return B.bar(self) + C.bar(self)


def test_D() -> None:
    assert D.foo() == 24
    assert D().bar() == 22032


def mk_expected_provenance_metadata_for(
    cls: type[Provenance.Base],
    cls_code: dict[str, Any] | None = None,
    cls_extra: dict[str, Any] | None = None,
    extra: dict[str, Any] | None = None,
    instance: bool = False,
) -> dict[str, Any]:
    return {
        "cls": cls.__qualname__,
        "bases": [
            base.__qualname__
            for base in cls.__bases__
            if issubclass(base, Provenance.Base)
        ],
        "cls_code": cls_code or {},
        "cls_extra": cls_extra or {},
        "extra": (extra or {}) if instance else {},
    }


def expected_provenance_metadatas(
    instance: bool = False,
) -> dict[type[Provenance.Base], list[dict[str, Any]]]:
    return {
        Provenance.Base: [
            mk_expected_provenance_metadata_for(
                Provenance.Base,
                cls_extra={
                    "VERSION": Provenance.Base.VERSION,
                },
                instance=instance,
            ),
        ],
        A: [
            mk_expected_provenance_metadata_for(
                A,
                cls_code={
                    "bar": (
                        "\n".join(
                            [
                                "    @Provenance.register",
                                "    @abstractmethod",
                                "    def bar(self) -> int:",
                                "        raise NotImplementedError",
                                "",  # trailing newline
                            ]
                        )
                    ),
                    "foo": (
                        "\n".join(
                            [
                                "    @Provenance.register",
                                "    @classmethod",
                                "    def foo(cls) -> int:",
                                "        return 42",
                                "",  # trailing newline
                            ]
                        )
                    ),
                },
                instance=instance,
            ),
        ],
        B: [
            mk_expected_provenance_metadata_for(
                B,
                cls_code={
                    "bar": (
                        "\n".join(
                            [
                                "    @override",
                                "    def bar(self) -> int:",
                                "        return self.my_cls_logic() + self.my_logic()",
                                "",  # trailing newline
                            ]
                        )
                    ),
                    "my_cls_logic": (
                        "\n".join(
                            [
                                "    @Provenance.compute",
                                "    @classmethod",
                                "    def my_cls_logic(cls) -> int:",
                                "        return 300",
                                "",  # trailing newline
                            ]
                        )
                    ),
                    "my_logic": (
                        "\n".join(
                            [
                                "    @Provenance.compute",
                                "    def my_logic(self) -> int:",
                                "        return 14",
                                "",  # trailing newline
                            ]
                        )
                    ),
                },
                cls_extra={
                    "my_cls_logic": 300,
                },
                extra={
                    "my_logic": 14,
                },
                instance=instance,
            ),
        ],
        C: [
            mk_expected_provenance_metadata_for(
                C,
                cls_code={
                    "bar": (
                        "\n".join(
                            [
                                "    @override",
                                "    def bar(self) -> int:",
                                "        return 21718",
                                "",  # trailing newline
                            ]
                        )
                    ),
                },
                instance=instance,
            ),
        ],
        D: [
            mk_expected_provenance_metadata_for(
                D,
                cls_code={
                    "foo": (
                        "\n".join(
                            [
                                "    @override",
                                "    @classmethod",
                                "    def foo(cls) -> int:",
                                "        return 24",
                                "",  # trailing newline
                            ]
                        )
                    ),
                    "bar": (
                        "\n".join(
                            [
                                "    @override",
                                "    def bar(self) -> int:",
                                "        return B.bar(self) + C.bar(self)",
                                "",  # trailing newline
                            ]
                        )
                    ),
                },
                instance=instance,
            ),
        ],
    }


def mk_expected_provenance_metadatas_for(
    o: type[Provenance.Base] | Provenance.Base,
) -> dict[str, list[dict[str, Any]]]:
    if isinstance(o, Provenance.Base):
        instance = True
        o_cls = o.__class__
    elif issubclass(o, Provenance.Base):
        instance = False
        o_cls = o
    else:
        raise AssertionError(
            f"{o} ({type(o)}) must be an instance or class of Provenance.Base"
        )

    return {
        cls.__qualname__: metadata
        for cls, metadata in expected_provenance_metadatas(instance=instance).items()
        if cls in Provenance.filtered_mro(o_cls)
    }


def test_A_provenance() -> None:
    assert Provenance.of_cls(A) == mk_expected_provenance_metadatas_for(A)
    assert Provenance.checksum_of_cls(A) == "d6d49d0593fe8ae23c8fc8db6cfab8a6"


def test_B_provenance() -> None:
    assert Provenance.of_cls(B) == mk_expected_provenance_metadatas_for(B)
    assert Provenance.checksum_of_cls(B) == "4e32d88b43a6c7a8f9ef0cfe67005c40"

    assert Provenance.of(B()) == mk_expected_provenance_metadatas_for(B())
    assert Provenance.checksum_of(B()) == "302c03b6a69ef31a62743dd215c11a25"


def test_C_provenance() -> None:
    assert Provenance.of_cls(C) == mk_expected_provenance_metadatas_for(C)
    assert Provenance.checksum_of_cls(C) == "def45b25c5117f51475b0bfe1cee6e6d"

    assert Provenance.of(C()) == mk_expected_provenance_metadatas_for(C())
    assert Provenance.checksum_of(C()) == Provenance.checksum_of_cls(C)


def test_D_provenance() -> None:
    assert Provenance.of_cls(D) == mk_expected_provenance_metadatas_for(D)
    assert Provenance.checksum_of_cls(D) == "8ffb28788762c7a1a91148d94e129299"

    assert Provenance.of(D()) == mk_expected_provenance_metadatas_for(D())
    assert Provenance.checksum_of(D()) == "c76906d4eac5704ec804192f22af00ee"
