import json
from typing import Any, override

from provenance_toolkit import Provenance


class A(Provenance.Version, VERSION="0.1.2"):
    pass


class B(A, VERSION="2.1.0"):
    pass


class CustomProvenance(Provenance.T):
    def __init__(
        self,
        data: dict[str, Any] | None = None,
        instance: bool = False,
    ) -> None:
        self._data = data or {}
        self._is_cls_provenance = not instance

    def __eq__(self, other: Any) -> Any:
        super_eq = super().__eq__(other)
        if super_eq is NotImplemented:
            return NotImplemented
        return (
            self._data == other._data
            and self._is_cls_provenance == other._is_cls_provenance
        )

    @override
    def is_cls_provenance(self) -> bool:
        return self._is_cls_provenance

    @override
    def stable_serialize(self) -> str:
        return json.dumps(self._data, sort_keys=True, ensure_ascii=False)


class WithCustomProvenance(Provenance.Proto):
    def __init__(self, num: int, *args: Any, **kwargs: Any) -> None:
        super().__init__(*args, **kwargs)
        self._num = num

    @override
    @classmethod
    def compute_cls_provenance(cls) -> dict[type[Provenance.ProtoClass], Provenance.T]:
        result = super().compute_cls_provenance()
        result[WithCustomProvenance] = CustomProvenance()
        return result

    @override
    def compute_provenance(self) -> dict[type[Provenance.ProtoInstance], Provenance.T]:
        result = super().compute_provenance()
        result[WithCustomProvenance] = CustomProvenance(
            data={"num": self._num}, instance=True
        )
        return result


class C(A, WithCustomProvenance, VERSION="3.4.5"):
    def __init__(self, num: int, *args: Any, **kwargs: Any) -> None:
        super().__init__(num, *args, **kwargs)


class WithCustomProvenanceDerived(WithCustomProvenance):
    @override
    @classmethod
    def compute_cls_provenance(cls) -> dict[type[Provenance.ProtoClass], Provenance.T]:
        result = super().compute_cls_provenance()
        result[WithCustomProvenanceDerived] = CustomProvenance({"num": 21718})
        return result


class D(B, C, WithCustomProvenanceDerived, VERSION="9.8.7"):
    def __init__(self, *args: Any, **kwargs: Any) -> None:
        super().__init__(314, *args, **kwargs)


if __name__ == "__main__":
    from pprint import pprint

    print(f"A.cls_checksum() = {A.cls_checksum()}")
    print(f"A().cls_checksum() = {A().checksum()}")
    print("A.cls_checksums()")
    pprint(A.cls_checksums())
    print("A().checksums()")
    pprint(A().checksums())
    print("A.cls_provenance()")
    pprint(A.cls_provenance())
    print("A().provenance()")
    pprint(A().provenance())
    print("~" * 50)

    print(f"B.cls_checksum() = {B.cls_checksum()}")
    print(f"B().cls_checksum() = {B().checksum()}")
    print("B.cls_checksums()")
    pprint(B.cls_checksums())
    print("B().checksums()")
    pprint(B().checksums())
    print("B.cls_provenance()")
    pprint(B.cls_provenance())
    print("B().provenance()")
    pprint(B().provenance())
    print("~" * 50)

    print(f"C.cls_checksum() = {C.cls_checksum()}")
    print(f"C(42).cls_checksum() = {C(42).checksum()}")
    print("C.cls_checksums()")
    pprint(C.cls_checksums())
    print("C(42).checksums()")
    pprint(C(42).checksums())
    print("C.cls_provenance()")
    pprint(C.cls_provenance())
    print("C(42).provenance()")
    pprint(C(42).provenance())
    print("~" * 50)

    print(f"D.cls_checksum() = {D.cls_checksum()}")
    print(f"D().cls_checksum() = {D().checksum()}")
    print("D.cls_checksums()")
    pprint(D.cls_checksums())
    print("D().checksums()")
    pprint(D().checksums())
    print("D.cls_provenance()")
    pprint(D.cls_provenance())
    print("D().provenance()")
    pprint(D().provenance())
    print("~" * 50)
