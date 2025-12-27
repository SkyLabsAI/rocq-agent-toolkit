from typing import Any

import semver
from provenance_toolkit import Provenance


class A(Provenance.Version, VERSION="0.0.1"):
    def __init__(self, *args: Any, **kwargs: Any) -> None:
        super().__init__(*args, **kwargs)


class B(A):  # VERSION=None
    def __init__(self, *args: Any, **kwargs: Any) -> None:
        super().__init__(*args, **kwargs)


class C(A, VERSION=(A.cls_version() or semver.Version.parse("0.0.0")).bump_minor()):
    def __init__(self, *args: Any, **kwargs: Any):
        super().__init__(*args, **kwargs)


def test_A() -> None:
    cls_version = semver.Version.parse("0.0.1")
    assert A.cls_version() == cls_version

    cls_prov = A.cls_provenance()
    assert len(cls_prov) == 1
    assert cls_prov[Provenance.Version] == Provenance.VersionT(cls_version)
    assert cls_prov == A().provenance()

    assert A.cls_checksum() == "d5814a8e681d4cb64afea9241e77b233"
    assert A.cls_checksum() == A().checksum()

    assert A.cls_checksums() == {
        Provenance.Version: "25e64aa754c310d45c1e084d574c1bb0",
    }
    assert A.cls_checksums() == A().checksums()


def test_B() -> None:
    cls_version = None
    assert B.cls_version() == cls_version

    cls_prov = B.cls_provenance()
    assert len(cls_prov) == 1
    assert cls_prov[Provenance.Version] == Provenance.VersionT(cls_version)
    assert cls_prov == B().provenance()

    assert B.cls_checksum() == "67e35a7b4141bfe576eaa58dc81c014f"
    assert B.cls_checksum() == B().checksum()

    assert B.cls_checksums() == {
        Provenance.Version: "6adf97f83acf6453d4a6a4b1070f3754",
    }
    assert B.cls_checksums() == B().checksums()


def test_C() -> None:
    cls_version = semver.Version.parse("0.1.0")
    assert C.cls_version() == cls_version

    cls_prov = C.cls_provenance()
    assert len(cls_prov) == 1
    assert cls_prov[Provenance.Version] == Provenance.VersionT(cls_version)
    assert cls_prov == C().provenance()

    assert C.cls_checksum() == "6fdeab3aaa4eb326d3b66818cb75078f"
    assert C.cls_checksum() == C().checksum()

    assert C.cls_checksums() == {
        Provenance.Version: "e5d18b4e2c1dc1975775ee385ab41c85",
    }
    assert C.cls_checksums() == C().checksums()
