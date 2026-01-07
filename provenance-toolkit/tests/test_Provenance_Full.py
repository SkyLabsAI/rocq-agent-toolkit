"""Simple integration test of [Provenance.Full]."""

from typing import Annotated, Any

import semver
from provenance_toolkit import Provenance


class A(Provenance.Full, VERSION="0.0.1"):
    _data: Annotated[int, Provenance.Reflect.Field]

    def __init__(self, data: int, *args: Any, **kwargs: Any) -> None:
        super().__init__(*args, **kwargs)
        self._data = data


class Config(Provenance.Reflect):
    _name: Annotated[str, Provenance.Reflect.Field]

    def __init__(self, name: str) -> None:
        self._name = name


class B(A):  # VERSION=None
    _cfg: Annotated[Config, Provenance.Reflect.Field]

    def __init__(self, cfg: Config, *args: Any, **kwargs: Any) -> None:
        super().__init__(314, *args, **kwargs)
        self._cfg = cfg


class C(A, VERSION=(A.cls_version() or semver.Version.parse("0.0.0")).bump_minor()):
    _cfg: Annotated[Config, Provenance.Reflect.Field] = Config("bar")

    def __init__(self, *args: Any, **kwargs: Any):
        super().__init__(21718, *args, **kwargs)


def test_A() -> None:
    cls_version = semver.Version.parse("0.0.1")
    assert A.cls_version() == cls_version

    a = A(42)

    cls_prov = A.cls_provenance()
    assert len(cls_prov) == 3
    assert cls_prov[Provenance.ClassIdentity] == Provenance.ClassIdentityT(A)
    assert cls_prov[Provenance.Version] == Provenance.VersionT(cls_version)
    assert cls_prov[Provenance.Reflect] == Provenance.ReflectT(
        {},
        is_cls_provenance=True,
    )

    prov = a.provenance()
    assert len(prov) == 3
    assert prov[Provenance.ClassIdentity] == cls_prov[Provenance.ClassIdentity]
    assert prov[Provenance.Version] == cls_prov[Provenance.Version]
    assert prov[Provenance.Reflect] != cls_prov[Provenance.Reflect]
    assert prov[Provenance.Reflect] == Provenance.ReflectT({"_data": 42})

    cls_checksum = A.cls_checksum()
    cls_checksum_from_instance = a.cls_checksum()
    checksum = a.checksum()
    assert cls_checksum == cls_checksum_from_instance
    assert cls_checksum != checksum

    cls_checksums = A.cls_checksums()
    cls_checksums_from_instance = a.cls_checksums()
    checksums = a.checksums()
    assert cls_checksums == cls_checksums_from_instance
    assert cls_checksums != checksums
    assert (
        cls_checksums[Provenance.ClassIdentity] == checksums[Provenance.ClassIdentity]
    )
    assert cls_checksums[Provenance.Version] == checksums[Provenance.Version]
    assert cls_checksums[Provenance.Reflect] != checksums[Provenance.Reflect]


def test_B() -> None:
    cls_version = None
    assert B.cls_version() == cls_version

    b = B(Config("foo"))

    cls_prov = B.cls_provenance()
    assert len(cls_prov) == 3
    assert cls_prov[Provenance.ClassIdentity] == Provenance.ClassIdentityT(B)
    assert cls_prov[Provenance.Version] == Provenance.VersionT(cls_version)
    assert cls_prov[Provenance.Reflect] == Provenance.ReflectT(
        {},
        is_cls_provenance=True,
    )

    prov = b.provenance()
    assert len(prov) == 3
    assert prov[Provenance.ClassIdentity] == cls_prov[Provenance.ClassIdentity]
    assert prov[Provenance.Version] == cls_prov[Provenance.Version]
    assert prov[Provenance.Reflect] != cls_prov[Provenance.Reflect]
    prov_reflect_expected = Provenance.ReflectT(
        {
            "_data": 314,
            "_cfg": {
                Provenance.Reflect: Provenance.ReflectT(
                    {
                        "_name": "foo",
                    },
                )
            },
        },
    )
    print(str(prov[Provenance.Reflect]))
    print(str(prov_reflect_expected))
    assert prov[Provenance.Reflect] == prov_reflect_expected

    cls_checksum = B.cls_checksum()
    cls_checksum_from_instance = b.cls_checksum()
    checksum = b.checksum()
    assert cls_checksum == cls_checksum_from_instance
    assert cls_checksum != checksum

    cls_checksums = B.cls_checksums()
    cls_checksums_from_instance = b.cls_checksums()
    checksums = b.checksums()
    assert cls_checksums == cls_checksums_from_instance
    assert cls_checksums != checksums
    assert (
        cls_checksums[Provenance.ClassIdentity] == checksums[Provenance.ClassIdentity]
    )
    assert cls_checksums[Provenance.Version] == checksums[Provenance.Version]
    assert cls_checksums[Provenance.Reflect] != checksums[Provenance.Reflect]


def test_C() -> None:
    cls_version = semver.Version.parse("0.1.0")
    assert C.cls_version() == cls_version

    c = C()

    cls_prov = C.cls_provenance()
    assert len(cls_prov) == 3
    assert cls_prov[Provenance.ClassIdentity] == Provenance.ClassIdentityT(C)
    assert cls_prov[Provenance.Version] == Provenance.VersionT(cls_version)
    print(str(cls_prov[Provenance.Reflect]))
    assert cls_prov[Provenance.Reflect] == Provenance.ReflectT(
        {
            "_cfg": {
                Provenance.Reflect: Provenance.ReflectT(
                    {
                        "_name": "bar",
                    },
                )
            }
        },
        is_cls_provenance=True,
    )

    prov = c.provenance()
    assert len(prov) == 3
    assert prov[Provenance.ClassIdentity] == cls_prov[Provenance.ClassIdentity]
    assert prov[Provenance.Version] == cls_prov[Provenance.Version]
    assert prov[Provenance.Reflect] != cls_prov[Provenance.Reflect]
    assert prov[Provenance.Reflect] == Provenance.ReflectT(
        {
            "_data": 21718,
            "_cfg": {
                Provenance.Reflect: Provenance.ReflectT(
                    {
                        "_name": "bar",
                    },
                )
            },
        },
    )

    cls_checksum = C.cls_checksum()
    cls_checksum_from_instance = c.cls_checksum()
    checksum = c.checksum()
    assert cls_checksum == cls_checksum_from_instance
    assert cls_checksum != checksum

    cls_checksums = C.cls_checksums()
    cls_checksums_from_instance = c.cls_checksums()
    checksums = c.checksums()
    assert cls_checksums == cls_checksums_from_instance
    assert cls_checksums != checksums
    assert (
        cls_checksums[Provenance.ClassIdentity] == checksums[Provenance.ClassIdentity]
    )
    assert cls_checksums[Provenance.Version] == checksums[Provenance.Version]
    assert cls_checksums[Provenance.Reflect] != checksums[Provenance.Reflect]
