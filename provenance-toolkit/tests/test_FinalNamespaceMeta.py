import pytest
from provenance_toolkit import FinalNamespaceMeta


class Foo:
    pass


def test_bad_FinalNamespaceMeta() -> None:
    with pytest.raises(ValueError) as exc_info1:

        class Bad1(metaclass=FinalNamespaceMeta, derive_from={}):
            pass

    assert (
        str(exc_info1.value) == "Bad1 should provide a non-empty list for derive_from"
    )

    with pytest.raises(AttributeError) as exc_info2:

        class Bad2(metaclass=FinalNamespaceMeta, derive_from={"Missing": type}):
            pass

    assert "Missing not in namespace of Bad2" in str(exc_info2.value)

    with pytest.raises(ValueError) as exc_info3:

        class Bad3(metaclass=FinalNamespaceMeta, derive_from={"Foo": type}):
            Foo: type = Foo

    assert "expected Bad3.Foo to have value type, but it is Foo" in str(exc_info3.value)
