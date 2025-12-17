import pytest
from provenance_toolkit import Signature


def test_Signature() -> None:
    Signature()


def test_prevent_derive_Signature() -> None:
    with pytest.raises(TypeError) as exc_info:

        class BadSignatureDeriver(Signature):
            pass

    assert str(exc_info.value) == "type 'Signature' is not an acceptable base type"
