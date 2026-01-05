"""Tests for WithReflectProvenance mixin and Data annotation."""

from typing import Annotated, Final, get_args, get_origin

import pytest
from provenance_toolkit import Provenance
from provenance_toolkit.provenance.reflect import (
    ReflectProvenanceData,
    TransformData,
    WithReflectProvenance,
)


class Config(Provenance.ClassIdentity, Provenance.Version, VERSION="1.0.0"):
    """Test configuration class with provenance."""

    pass


class TestDataAnnotation:
    """Tests for Data.__class_getitem__ behavior."""

    def test_data_single_arg(self):
        """Test Data[T] returns Annotated[T, ()]."""
        hint = Provenance.Reflect.Data[int]
        assert get_origin(hint) is Annotated
        args = get_args(hint)
        assert args[0] is int
        assert args[1] == ()  # Empty tuple marker

    def test_data_with_callable(self):
        """Test Data[T, callable] returns Annotated[T, TransformData]."""
        transform_func = lambda x: x * 2
        hint = Provenance.Reflect.Data[int, transform_func]
        assert get_origin(hint) is Annotated
        args = get_args(hint)
        assert args[0] is int
        assert isinstance(args[1], TransformData)
        assert args[1].func is transform_func

    def test_data_with_static_method(self):
        """Test Data[T, staticmethod] works."""

        class TestClass:
            @staticmethod
            def transform(val: int) -> int:
                return val * 2

        hint = Provenance.Reflect.Data[int, TestClass.transform]
        args = get_args(hint)
        assert args[0] is int
        assert isinstance(args[1], TransformData)
        assert args[1].func is TestClass.transform

    def test_data_invalid_args(self):
        """Test Data with invalid number of arguments raises TypeError."""
        with pytest.raises(TypeError, match="expects 1 or 2 arguments"):
            Provenance.Reflect.Data[int, str, float]  # type: ignore

    def test_data_invalid_callable(self):
        """Test Data with non-callable second argument raises TypeError."""
        with pytest.raises(TypeError, match="must be callable"):
            Provenance.Reflect.Data[int, "not_callable"]  # type: ignore


class TestReflectProvenanceData:
    """Tests for ReflectProvenanceData serialization."""

    def test_serialization(self):
        """Test that ReflectProvenanceData serializes correctly."""
        data = {"x": 42, "y": "test", "z": None}
        prov = ReflectProvenanceData(data)
        serialized = prov.stable_serialize()
        # Should be valid JSON with sorted keys
        assert '"x"' in serialized
        assert '"y"' in serialized
        assert '"z"' in serialized
        assert "42" in serialized
        assert "test" in serialized
        assert "null" in serialized

    def test_equality(self):
        """Test that ReflectProvenanceData equality works."""
        data1 = {"x": 42}
        data2 = {"x": 42}
        data3 = {"x": 43}
        prov1 = ReflectProvenanceData(data1)
        prov2 = ReflectProvenanceData(data2)
        prov3 = ReflectProvenanceData(data3)
        assert prov1 == prov2
        assert prov1 != prov3

    def test_is_provenance(self):
        """Test is_cls_provenance and is_instance_provenance."""
        prov = ReflectProvenanceData({"x": 42})
        assert prov.is_cls_provenance()
        assert prov.is_instance_provenance()


class TestWithReflectProvenance:
    """Tests for WithReflectProvenance mixin."""

    def test_class_provenance_with_values(self):
        """Test class provenance with fields that have values."""

        class TestClass(
            Provenance.ClassIdentity,
            Provenance.Version,
            Provenance.Reflect,
            VERSION="1.0.0",
        ):
            x: Final[Provenance.Reflect.Data[int]] = 42
            y: Final[Provenance.Reflect.Data[float, lambda v: round(v, 2)]] = 3.14159

        cls_prov = TestClass.cls_provenance()
        assert WithReflectProvenance in cls_prov
        reflect_prov = cls_prov[WithReflectProvenance]
        assert isinstance(reflect_prov, ReflectProvenanceData)
        assert reflect_prov.data["x"] == 42
        assert reflect_prov.data["y"] == 3.14

    def test_class_provenance_with_unset_fields(self):
        """Test class provenance with annotated but unset fields."""

        class TestClass(
            Provenance.ClassIdentity,
            Provenance.Version,
            Provenance.Reflect,
            VERSION="1.0.0",
        ):
            x: Final[Provenance.Reflect.Data[int]] = 42
            # Annotated but not assigned - should use None
            model: Provenance.Reflect.Data[str, lambda x: f"model_{x}" if x else "none"]

        cls_prov = TestClass.cls_provenance()
        reflect_prov = cls_prov[WithReflectProvenance]
        assert reflect_prov.data["x"] == 42
        assert reflect_prov.data["model"] == "none"  # transform(None)

    def test_instance_provenance_with_values(self):
        """Test instance provenance with fields that have values."""

        class TestClass(
            Provenance.ClassIdentity,
            Provenance.Version,
            Provenance.Reflect,
            VERSION="1.0.0",
        ):
            x: Final[Provenance.Reflect.Data[int]] = 42
            model: Provenance.Reflect.Data[str, lambda x: f"model_{x}"]

        instance = TestClass()
        instance.model = "gpt-4"

        inst_prov = instance.provenance()
        reflect_prov = inst_prov[WithReflectProvenance]
        assert reflect_prov.data["x"] == 42
        assert reflect_prov.data["model"] == "model_gpt-4"

    def test_instance_provenance_with_unset_fields(self):
        """Test instance provenance with annotated but unset fields."""

        class TestClass(
            Provenance.ClassIdentity,
            Provenance.Version,
            Provenance.Reflect,
            VERSION="1.0.0",
        ):
            x: Final[Provenance.Reflect.Data[int]] = 42
            model: Provenance.Reflect.Data[str, lambda x: f"model_{x}" if x else "none"]

        instance = TestClass()
        # Don't set model

        inst_prov = instance.provenance()
        reflect_prov = inst_prov[WithReflectProvenance]
        assert reflect_prov.data["x"] == 42
        assert reflect_prov.data["model"] == "none"  # transform(None)

    def test_provenance_aware_auto_detection(self):
        """Test best-effort auto-detection of provenance-aware objects."""

        class TestClass(
            Provenance.ClassIdentity,
            Provenance.Version,
            Provenance.Reflect,
            VERSION="1.0.0",
        ):
            cfg: Final[Provenance.Reflect.Data[Config]] = Config()

        cls_prov = TestClass.cls_provenance()
        reflect_prov = cls_prov[WithReflectProvenance]
        # Should extract checksum from Config's provenance
        assert "cfg" in reflect_prov.data
        assert isinstance(reflect_prov.data["cfg"], str)  # checksum

    def test_explicit_transform_overrides_auto_detection(self):
        """Test that explicit transform takes priority over auto-detection."""

        class TestClass(
            Provenance.ClassIdentity,
            Provenance.Version,
            Provenance.Reflect,
            VERSION="1.0.0",
        ):
            cfg: Final[
                Provenance.Reflect.Data[Config, lambda c: "custom_transform"]
            ] = Config()

        cls_prov = TestClass.cls_provenance()
        reflect_prov = cls_prov[WithReflectProvenance]
        assert reflect_prov.data["cfg"] == "custom_transform"

    def test_identity_for_raw_data(self):
        """Test that raw data uses identity function."""

        class TestClass(
            Provenance.ClassIdentity,
            Provenance.Version,
            Provenance.Reflect,
            VERSION="1.0.0",
        ):
            x: Final[Provenance.Reflect.Data[int]] = 42
            y: Final[Provenance.Reflect.Data[str]] = "test"

        cls_prov = TestClass.cls_provenance()
        reflect_prov = cls_prov[WithReflectProvenance]
        assert reflect_prov.data["x"] == 42
        assert reflect_prov.data["y"] == "test"

    def test_none_values_included(self):
        """Test that None values are included in provenance."""

        class TestClass(
            Provenance.ClassIdentity,
            Provenance.Version,
            Provenance.Reflect,
            VERSION="1.0.0",
        ):
            x: Final[Provenance.Reflect.Data[int | None]] = None

        cls_prov = TestClass.cls_provenance()
        reflect_prov = cls_prov[WithReflectProvenance]
        assert reflect_prov.data["x"] is None

    def test_class_data_is_instance_data(self):
        """Test that class data is also included in instance provenance."""

        class TestClass(
            Provenance.ClassIdentity,
            Provenance.Version,
            Provenance.Reflect,
            VERSION="1.0.0",
        ):
            x: Final[Provenance.Reflect.Data[int]] = 42

        instance = TestClass()
        cls_prov = TestClass.cls_provenance()
        inst_prov = instance.provenance()

        cls_reflect = cls_prov[WithReflectProvenance]
        inst_reflect = inst_prov[WithReflectProvenance]

        # Class data should be in instance data
        assert cls_reflect.data["x"] == inst_reflect.data["x"]

    def test_wrapped_in_final(self):
        """Test that Data works when wrapped in Final."""

        class TestClass(
            Provenance.ClassIdentity,
            Provenance.Version,
            Provenance.Reflect,
            VERSION="1.0.0",
        ):
            x: Final[Provenance.Reflect.Data[int]] = 42

        cls_prov = TestClass.cls_provenance()
        reflect_prov = cls_prov[WithReflectProvenance]
        assert reflect_prov.data["x"] == 42

    def test_multiple_fields(self):
        """Test multiple annotated fields are all collected."""

        class TestClass(
            Provenance.ClassIdentity,
            Provenance.Version,
            Provenance.Reflect,
            VERSION="1.0.0",
        ):
            a: Final[Provenance.Reflect.Data[int]] = 1
            b: Final[Provenance.Reflect.Data[str]] = "two"
            c: Final[Provenance.Reflect.Data[float, lambda x: round(x, 1)]] = 3.456

        cls_prov = TestClass.cls_provenance()
        reflect_prov = cls_prov[WithReflectProvenance]
        assert len(reflect_prov.data) == 3
        assert reflect_prov.data["a"] == 1
        assert reflect_prov.data["b"] == "two"
        assert reflect_prov.data["c"] == 3.5

    def test_non_annotated_fields_ignored(self):
        """Test that non-annotated fields are ignored."""

        class TestClass(
            Provenance.ClassIdentity,
            Provenance.Version,
            Provenance.Reflect,
            VERSION="1.0.0",
        ):
            x: Final[Provenance.Reflect.Data[int]] = 42
            y: int = 100  # Not annotated with Data

        cls_prov = TestClass.cls_provenance()
        reflect_prov = cls_prov[WithReflectProvenance]
        assert "x" in reflect_prov.data
        assert "y" not in reflect_prov.data

    def test_checksum_stability(self):
        """Test that checksums are stable for same data."""

        class TestClass(
            Provenance.ClassIdentity,
            Provenance.Version,
            Provenance.Reflect,
            VERSION="1.0.0",
        ):
            x: Final[Provenance.Reflect.Data[int]] = 42

        checksum1 = TestClass.cls_checksum()
        checksum2 = TestClass.cls_checksum()
        assert checksum1 == checksum2

    def test_checksum_changes_with_data(self):
        """Test that checksums change when data changes."""

        class TestClass1(
            Provenance.ClassIdentity,
            Provenance.Version,
            Provenance.Reflect,
            VERSION="1.0.0",
        ):
            x: Final[Provenance.Reflect.Data[int]] = 42

        class TestClass2(
            Provenance.ClassIdentity,
            Provenance.Version,
            Provenance.Reflect,
            VERSION="1.0.0",
        ):
            x: Final[Provenance.Reflect.Data[int]] = 43

        checksum1 = TestClass1.cls_checksum()
        checksum2 = TestClass2.cls_checksum()
        assert checksum1 != checksum2
