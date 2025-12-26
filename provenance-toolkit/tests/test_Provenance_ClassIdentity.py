"""Tests for WithClassIdentityProvenance mixin."""

from provenance_toolkit import Provenance


class SampleAgent(Provenance.ClassIdentity, Provenance.Version, VERSION="1.0.0"):
    """A sample agent class."""

    pass


class SampleAgentDerived(SampleAgent, VERSION="1.1.0"):
    """A derived sample agent class."""

    pass


class AnotherAgent(Provenance.ClassIdentity, Provenance.Version, VERSION="1.0.0"):
    """Another agent class with the same version."""

    pass


def test_class_identity_in_provenance():
    """Test that class identity is included in provenance data."""
    prov = SampleAgent.cls_provenance_json()
    assert "WithClassIdentityProvenance" in prov
    assert "SampleAgent" in prov["WithClassIdentityProvenance"]


def test_different_classes_have_different_checksums():
    """Test that different classes with the same VERSION have different checksums."""
    checksum1 = SampleAgent.cls_checksum()
    checksum2 = AnotherAgent.cls_checksum()
    assert checksum1 != checksum2


def test_derived_class_has_different_checksum():
    """Test that derived classes have different checksums."""
    checksum1 = SampleAgent.cls_checksum()
    checksum2 = SampleAgentDerived.cls_checksum()
    assert checksum1 != checksum2


def test_instance_provenance_matches_class():
    """Test that instance provenance includes class identity."""
    agent = SampleAgent()
    prov = agent.provenance_json()
    assert "WithClassIdentityProvenance" in prov
    assert "SampleAgent" in prov["WithClassIdentityProvenance"]


def test_full_qualname_includes_module():
    """Test that the provenance includes the full module path."""
    prov = SampleAgent.cls_provenance_json()
    identity = prov["WithClassIdentityProvenance"]
    # Should include the module path
    assert "test_Provenance_ClassIdentity" in identity
    assert "SampleAgent" in identity


def test_class_and_instance_checksums_match():
    """Test that class and instance checksums match for agents without instance-specific provenance."""
    agent = SampleAgent()
    assert SampleAgent.cls_checksum() == agent.checksum()

