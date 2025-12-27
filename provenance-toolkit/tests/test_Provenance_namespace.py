import pytest
from provenance_toolkit import Provenance


def test_Provenance() -> None:
    Provenance()


def test_prevent_derive_Provenance() -> None:
    with pytest.raises(TypeError) as exc_info:

        class BadProvenanceDeriver(Provenance):
            pass

    assert str(exc_info.value) == "type 'Provenance' is not an acceptable base type"
