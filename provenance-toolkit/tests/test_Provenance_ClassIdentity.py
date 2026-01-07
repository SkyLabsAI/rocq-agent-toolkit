"""Tests for WithClassIdentityProvenance mixin."""

from provenance_toolkit import Provenance
from provenance_toolkit.provenance.identity import (
    ClassIdentityProvenanceData,
    WithClassIdentityProvenance,
)


class SampleAgent(Provenance.ClassIdentity, Provenance.Version, VERSION="1.0.0"):
    """A sample agent class."""

    pass


class SampleAgentDerived(SampleAgent, VERSION="1.1.0"):
    """A derived sample agent class."""

    pass


class AnotherAgent(Provenance.ClassIdentity, Provenance.Version, VERSION="1.0.0"):
    """Another agent class with the same version."""

    pass


class BaseClass(Provenance.ClassIdentity, Provenance.Version, VERSION="1.0.0"):
    """A base class for testing inheritance."""

    pass


class DerivedFromBase(BaseClass, VERSION="1.0.0"):
    """A class derived from BaseClass."""

    pass


class DerivedFromSampleAgent(SampleAgent, VERSION="1.0.0"):
    """Another class derived from SampleAgent."""

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


def test_bases_captured_in_provenance():
    """Test that direct base classes are captured in provenance data."""
    prov = SampleAgentDerived.cls_provenance()
    identity_data = prov[WithClassIdentityProvenance]
    assert isinstance(identity_data, ClassIdentityProvenanceData)
    assert identity_data.bases is not None
    assert len(identity_data.bases) > 0
    # Should include SampleAgent as a base
    assert SampleAgent in identity_data.bases


def test_bases_in_serialization():
    """Test that bases are included in the stable serialization."""
    prov = SampleAgentDerived.cls_provenance()
    identity_data = prov[WithClassIdentityProvenance]
    serialized = identity_data.stable_serialize()
    # Should include the base class information
    assert SampleAgent.__qualname__ in serialized
    assert "(" in serialized  # Should have parentheses for bases


def test_different_bases_produce_different_checksums():
    """Test that classes with different base classes have different checksums."""
    # Both have same version, but different bases
    checksum1 = DerivedFromBase.cls_checksum()
    checksum2 = DerivedFromSampleAgent.cls_checksum()
    assert checksum1 != checksum2


def test_same_bases_same_qualname_different_checksums():
    """Test that classes with same bases but different qualnames have different checksums."""
    checksum1 = SampleAgentDerived.cls_checksum()
    checksum2 = DerivedFromSampleAgent.cls_checksum()
    # Both derive from SampleAgent, but have different qualnames
    assert checksum1 != checksum2


def test_bases_property_access():
    """Test that the bases property returns the correct tuple format."""
    prov = SampleAgentDerived.cls_provenance()
    identity_data = prov[WithClassIdentityProvenance]
    assert isinstance(identity_data, ClassIdentityProvenanceData)
    assert identity_data.bases is not None
    assert len(identity_data.bases) > 0
    # Each base should be a type
    for base in identity_data.bases:
        assert isinstance(base, type)
