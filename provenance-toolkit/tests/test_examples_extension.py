import semver
from examples.extensions import (
    A,
    B,
    C,
    CustomProvenance,
    D,
    WithCustomProvenance,
    WithCustomProvenanceDerived,
)
from provenance_toolkit import Provenance


def test_build_objects() -> None:
    A()
    B()
    C(42)
    D()


def test_A() -> None:
    cls_version = semver.Version.parse("0.1.2")
    assert A.cls_version() == cls_version

    cls_prov = A.cls_provenance()
    assert len(cls_prov) == 1
    assert cls_prov[Provenance.Version] == Provenance.VersionT(cls_version)
    assert cls_prov == A().provenance()

    assert A.cls_checksum() == "7eb944665a66601a0e09f1322b3d45f6"
    assert A.cls_checksum() == A().checksum()

    assert A.cls_checksums() == {
        Provenance.Version: "02f4b6c2b9b79a9b6868ced06242d888",
    }
    assert A.cls_checksums() == A().checksums()


def test_B() -> None:
    cls_version = semver.Version.parse("2.1.0")
    assert B.cls_version() == cls_version

    cls_prov = B.cls_provenance()
    assert len(cls_prov) == 1
    assert cls_prov[Provenance.Version] == Provenance.VersionT(cls_version)
    assert cls_prov == B().provenance()

    assert B.cls_checksum() == "50d52e8eb1f00d8d8d6f097aac7e1313"
    assert B.cls_checksum() == B().checksum()

    assert B.cls_checksums() == {
        Provenance.Version: "5337810b0c500ace9c4cd745f4b8bcf5",
    }
    assert B.cls_checksums() == B().checksums()


def test_C() -> None:
    cls_version = semver.Version.parse("3.4.5")
    assert C.cls_version() == cls_version

    cls_prov = C.cls_provenance()
    assert len(cls_prov) == 2
    assert cls_prov[Provenance.Version] == Provenance.VersionT(cls_version)
    assert cls_prov[WithCustomProvenance] == CustomProvenance()

    c = C(42)
    prov = c.provenance()
    assert cls_prov != prov
    assert len(prov) == 2
    assert prov[Provenance.Version] == Provenance.VersionT(cls_version)
    assert prov[WithCustomProvenance] == CustomProvenance({"num": 42}, instance=True)

    assert C.cls_checksum() == "315ff6463d0192d142cce62a827b09e1"
    assert C.cls_checksum() != c.checksum()
    assert c.checksum() == "6e224a7325af45cefbf326a70bf9fc99"

    assert C.cls_checksums() == {
        Provenance.Version: "78d96a7d448fe79810332b54067e951f",
        WithCustomProvenance: "99914b932bd37a50b983c5e7c90ae93b",
    }
    assert C.cls_checksums() != c.checksums()
    assert C.cls_checksums()[Provenance.Version] == c.checksums()[Provenance.Version]
    assert c.checksums()[WithCustomProvenance] == "ef3c4576589b2b0ae618a72f47f1550b"


def test_D() -> None:
    cls_version = semver.Version.parse("9.8.7")
    assert D.cls_version() == cls_version

    cls_prov = D.cls_provenance()
    assert len(cls_prov) == 3
    assert cls_prov[Provenance.Version] == Provenance.VersionT(cls_version)
    assert cls_prov[WithCustomProvenance] == CustomProvenance()
    assert cls_prov[WithCustomProvenanceDerived] == CustomProvenance({"num": 21718})

    d = D()
    prov = d.provenance()
    assert cls_prov != prov
    assert len(prov) == 2
    assert prov[Provenance.Version] == Provenance.VersionT(cls_version)
    assert prov[WithCustomProvenance] == CustomProvenance({"num": 314}, instance=True)

    assert D.cls_checksum() == "41f3fd8fb03f32cdd258415670ab35c1"
    assert D.cls_checksum() != d.checksum()
    assert d.checksum() == "848ea9125da3feb4ded75cdb86641671"

    assert D.cls_checksums() == {
        Provenance.Version: "e506088200b444246baf54828f9746f1",
        WithCustomProvenance: "99914b932bd37a50b983c5e7c90ae93b",
        WithCustomProvenanceDerived: "89d9243aaec1bdc0bab3197383f363f7",
    }
    assert D.cls_checksums() != d.checksums()
    assert D.cls_checksums()[Provenance.Version] == d.checksums()[Provenance.Version]
    assert d.checksums()[WithCustomProvenance] == "430955f64ba0f04993c4f7b8d44d62ac"
