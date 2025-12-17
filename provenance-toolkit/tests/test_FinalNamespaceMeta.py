import pytest
from provenance_toolkit.util import FinalNamespaceMeta


class Foo:
    pass


def test_bad_FinalNamespaceMeta() -> None:
    with pytest.raises(ValueError) as exc_info:

        class Bad1(metaclass=FinalNamespaceMeta, derive_from={}):
            pass

    assert str(exc_info.value) == "Bad1 should provide a non-empty list for derive_from"

    with pytest.raises(AttributeError) as exc_info:

        class Bad2(metaclass=FinalNamespaceMeta, derive_from={"Missing": type}):
            pass

    assert "Missing not in namespace of Bad2" in str(exc_info.value)

    with pytest.raises(ValueError) as exc_info:

        class Bad3(metaclass=FinalNamespaceMeta, derive_from={"Foo": type}):
            Foo: type = Foo

    assert "expected Bad3.Foo to have value type, but it is Foo" in str(exc_info.value)
