"""Tests for WithReflectProvenance mixin and Field annotation."""

from __future__ import annotations

from typing import Annotated, Final, get_args, get_origin

from provenance_toolkit import Provenance
from provenance_toolkit.provenance.reflect import (
    ReflectProvenanceData,
    WithReflectProvenance,
)


class Config(Provenance.ClassIdentity, Provenance.Version, VERSION="1.0.0"):
    """Test configuration class with provenance."""


class TestFieldAnnotation:
    """Tests for Field annotation behavior."""

    def test_field_single_arg(self):
        """Test Annotated[T, Field] works."""
        hint = Annotated[int, Provenance.Reflect.Field]
        assert get_origin(hint) is Annotated
        args = get_args(hint)
        assert args[0] is int
        assert args[1] is Provenance.Reflect.Field
        assert args[1].transform is None

    def test_field_with_callable(self):
        """Test Annotated[T, Field(transform=callable)] works."""

        def transform(val: int) -> int:
            return val * 2

        hint = Annotated[int, Provenance.Reflect.Field(transform=transform)]
        assert get_origin(hint) is Annotated
        args = get_args(hint)
        assert args[0] is int
        assert isinstance(args[1], Provenance.Reflect.Field)
        assert args[1].transform is transform

    def test_field_with_static_method(self):
        """Test Annotated[T, Field(transform=staticmethod)] works."""

        class TestClass:
            @staticmethod
            def transform(val: int) -> int:
                return val * 2

        hint = Annotated[int, Provenance.Reflect.Field(transform=TestClass.transform)]
        args = get_args(hint)
        assert args[0] is int
        assert isinstance(args[1], Provenance.Reflect.Field)
        assert args[1].transform is TestClass.transform


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


# Test classes defined at module level
class MyClassWithValues(
    Provenance.ClassIdentity,
    Provenance.Version,
    Provenance.Reflect,
    VERSION="1.0.0",
):
    """Test class with values for class provenance."""

    @staticmethod
    def normalize(val: float) -> float:
        """Normalize a float value."""
        return round(val, 2)

    x: Final[Annotated[int, Provenance.Reflect.Field]] = 42
    y: Final[
        Annotated[
            float,
            Provenance.Reflect.Field(transform=normalize),
        ]
    ] = 3.14159


class MyClassUnset(
    Provenance.ClassIdentity,
    Provenance.Version,
    Provenance.Reflect,
    VERSION="1.0.0",
):
    """Test class with unset fields."""

    x: Final[Annotated[int, Provenance.Reflect.Field]] = 42
    # Annotated but not assigned - should use None
    model: Annotated[
        str,
        Provenance.Reflect.Field(transform=lambda x: f"model_{x}" if x else "none"),
    ]


class MyClassInstance(
    Provenance.ClassIdentity,
    Provenance.Version,
    Provenance.Reflect,
    VERSION="1.0.0",
):
    """Test class for instance provenance with values."""

    x: Final[Annotated[int, Provenance.Reflect.Field]] = 42
    model: Annotated[str, Provenance.Reflect.Field(transform=lambda x: f"model_{x}")]


class MyClassInstanceUnset(
    Provenance.ClassIdentity,
    Provenance.Version,
    Provenance.Reflect,
    VERSION="1.0.0",
):
    """Test class for instance provenance with unset fields."""

    x: Final[Annotated[int, Provenance.Reflect.Field]] = 42
    model: Annotated[
        str,
        Provenance.Reflect.Field(transform=lambda x: f"model_{x}" if x else "none"),
    ]


class MyClassAutoDetect(
    Provenance.ClassIdentity,
    Provenance.Version,
    Provenance.Reflect,
    VERSION="1.0.0",
):
    """Test class for provenance-aware auto-detection."""

    cfg: Final[Annotated[Config, Provenance.Reflect.Field]] = Config()


class MyClassExplicitTransform(
    Provenance.ClassIdentity,
    Provenance.Version,
    Provenance.Reflect,
    VERSION="1.0.0",
):
    """Test class for explicit transform override."""

    cfg: Final[
        Annotated[
            Config,
            Provenance.Reflect.Field(transform=lambda c: "custom_transform"),
        ]
    ] = Config()


class MyClassIdentity(
    Provenance.ClassIdentity,
    Provenance.Version,
    Provenance.Reflect,
    VERSION="1.0.0",
):
    """Test class for identity function."""

    x: Final[Annotated[int, Provenance.Reflect.Field]] = 42
    y: Final[Annotated[str, Provenance.Reflect.Field]] = "test"


class MyClassNone(
    Provenance.ClassIdentity,
    Provenance.Version,
    Provenance.Reflect,
    VERSION="1.0.0",
):
    """Test class for None values."""

    x: Final[Annotated[int | None, Provenance.Reflect.Field]] = None


class MyClassData(
    Provenance.ClassIdentity,
    Provenance.Version,
    Provenance.Reflect,
    VERSION="1.0.0",
):
    """Test class for class data in instance provenance."""

    x: Final[Annotated[int, Provenance.Reflect.Field]] = 42


class MyClassFinal(
    Provenance.ClassIdentity,
    Provenance.Version,
    Provenance.Reflect,
    VERSION="1.0.0",
):
    """Test class for Final wrapper."""

    x: Final[Annotated[int, Provenance.Reflect.Field]] = 42


class MyClassMultiple(
    Provenance.ClassIdentity,
    Provenance.Version,
    Provenance.Reflect,
    VERSION="1.0.0",
):
    """Test class for multiple fields."""

    @staticmethod
    def my_round(x: float) -> float:
        return round(x, 1)

    a: Final[Annotated[int, Provenance.Reflect.Field]] = 1
    b: Final[Annotated[str, Provenance.Reflect.Field]] = "two"
    c: Final[
        Annotated[
            float,
            Provenance.Reflect.Field(transform=my_round),
        ]
    ] = 3.456


class MyClassNonAnnotated(
    Provenance.ClassIdentity,
    Provenance.Version,
    Provenance.Reflect,
    VERSION="1.0.0",
):
    """Test class for non-annotated fields."""

    x: Final[Annotated[int, Provenance.Reflect.Field]] = 42
    y: int = 100  # Not annotated with Field


class MyClassStability(
    Provenance.ClassIdentity,
    Provenance.Version,
    Provenance.Reflect,
    VERSION="1.0.0",
):
    """Test class for checksum stability."""

    x: Final[Annotated[int, Provenance.Reflect.Field]] = 42


class MyClass1(
    Provenance.ClassIdentity,
    Provenance.Version,
    Provenance.Reflect,
    VERSION="1.0.0",
):
    """Test class 1 for checksum changes."""

    x: Final[Annotated[int, Provenance.Reflect.Field]] = 42


class MyClass2(
    Provenance.ClassIdentity,
    Provenance.Version,
    Provenance.Reflect,
    VERSION="1.0.0",
):
    """Test class 2 for checksum changes."""

    x: Final[Annotated[int, Provenance.Reflect.Field]] = 43


class MyClassWithInstanceFields(
    Provenance.ClassIdentity,
    Provenance.Version,
    Provenance.Reflect,
    VERSION="1.0.0",
):
    """Test class with both class and instance fields."""

    # Class field - should appear in both class and instance provenance
    class_field: Final[Annotated[int, Provenance.Reflect.Field]] = 100

    # Instance field - annotated but not assigned at class level
    # Should only appear in instance provenance, not class provenance
    instance_field: Annotated[str, Provenance.Reflect.Field]

    def __init__(self, instance_value: str) -> None:
        """Initialize with instance field value."""
        super().__init__()
        self.instance_field = instance_value


class MyClassMultipleInstanceFields(
    Provenance.ClassIdentity,
    Provenance.Version,
    Provenance.Reflect,
    VERSION="1.0.0",
):
    """Test class with multiple instance fields."""

    @staticmethod
    def round_float(x: float) -> float:
        return round(x, 2)

    # Class field
    class_val: Final[Annotated[int, Provenance.Reflect.Field]] = 42

    # Multiple instance fields
    instance_str: Annotated[str, Provenance.Reflect.Field]
    instance_int: Annotated[int, Provenance.Reflect.Field]
    instance_float: Annotated[
        float,
        Provenance.Reflect.Field(transform=round_float),
    ]

    def __init__(self, s: str, i: int, f: float) -> None:
        """Initialize with instance field values."""
        super().__init__()
        self.instance_str = s
        self.instance_int = i
        self.instance_float = f


class MyClassOnlyInstanceFields(
    Provenance.ClassIdentity,
    Provenance.Version,
    Provenance.Reflect,
    VERSION="1.0.0",
):
    """Test class with only instance fields (no class fields)."""

    # Only instance fields - no class fields
    instance_only: Annotated[str, Provenance.Reflect.Field]

    def __init__(self, value: str) -> None:
        """Initialize with instance field value."""
        super().__init__()
        self.instance_only = value


class TestWithReflectProvenance:
    """Tests for WithReflectProvenance mixin."""

    def test_class_provenance_with_values(self):
        """Test class provenance with fields that have values."""
        cls_prov = MyClassWithValues.cls_provenance()
        assert WithReflectProvenance in cls_prov
        reflect_prov = cls_prov[WithReflectProvenance]
        assert isinstance(reflect_prov, ReflectProvenanceData)
        assert reflect_prov.data["x"] == 42
        assert reflect_prov.data["y"] == 3.14

    def test_class_provenance_with_unset_fields(self):
        """Test class provenance with annotated but unset fields."""
        cls_prov = MyClassUnset.cls_provenance()
        reflect_prov = cls_prov[WithReflectProvenance]
        assert isinstance(reflect_prov, ReflectProvenanceData)
        assert reflect_prov.data["x"] == 42
        # Instance fields (annotated but not assigned at class level) should not appear in class provenance
        assert "model" not in reflect_prov.data

    def test_instance_provenance_with_values(self):
        """Test instance provenance with fields that have values."""
        instance = MyClassInstance()
        instance.model = "gpt-4"

        inst_prov = instance.provenance()
        reflect_prov = inst_prov[WithReflectProvenance]
        assert isinstance(reflect_prov, ReflectProvenanceData)
        assert reflect_prov.data["x"] == 42
        assert reflect_prov.data["model"] == "model_gpt-4"

    def test_instance_provenance_with_unset_fields(self):
        """Test instance provenance with annotated but unset fields."""
        instance = MyClassInstanceUnset()
        # Don't set model

        inst_prov = instance.provenance()
        reflect_prov = inst_prov[WithReflectProvenance]
        assert isinstance(reflect_prov, ReflectProvenanceData)
        assert reflect_prov.data["x"] == 42
        assert reflect_prov.data["model"] == "none"  # transform(None)

    def test_provenance_aware_auto_detection(self):
        """Test best-effort auto-detection of provenance-aware objects."""
        cls_prov = MyClassAutoDetect.cls_provenance()
        reflect_prov = cls_prov[WithReflectProvenance]
        assert isinstance(reflect_prov, ReflectProvenanceData)
        # Should extract checksum from Config's provenance
        assert "cfg" in reflect_prov.data
        assert reflect_prov.data["cfg"] == Config().cls_provenance()

    def test_explicit_transform_overrides_auto_detection(self):
        """Test that explicit transform takes priority over auto-detection."""
        cls_prov = MyClassExplicitTransform.cls_provenance()
        reflect_prov = cls_prov[WithReflectProvenance]
        assert isinstance(reflect_prov, ReflectProvenanceData)
        assert reflect_prov.data["cfg"] == "custom_transform"

    def test_identity_for_raw_data(self):
        """Test that raw data uses identity function."""
        cls_prov = MyClassIdentity.cls_provenance()
        reflect_prov = cls_prov[WithReflectProvenance]
        assert isinstance(reflect_prov, ReflectProvenanceData)
        assert reflect_prov.data["x"] == 42
        assert reflect_prov.data["y"] == "test"

    def test_none_values_included(self):
        """Test that None values are included in provenance."""
        cls_prov = MyClassNone.cls_provenance()
        reflect_prov = cls_prov[WithReflectProvenance]
        assert isinstance(reflect_prov, ReflectProvenanceData)
        assert reflect_prov.data["x"] is None

    def test_class_data_is_instance_data(self):
        """Test that class data is also included in instance provenance."""
        instance = MyClassData()
        cls_prov = MyClassData.cls_provenance()
        inst_prov = instance.provenance()

        cls_reflect = cls_prov[WithReflectProvenance]
        inst_reflect = inst_prov[WithReflectProvenance]
        assert isinstance(cls_reflect, ReflectProvenanceData)
        assert isinstance(inst_reflect, ReflectProvenanceData)

        # Class data should be in instance data
        assert cls_reflect.data["x"] == inst_reflect.data["x"]

    def test_wrapped_in_final(self):
        """Test that Data works when wrapped in Final."""
        cls_prov = MyClassFinal.cls_provenance()
        reflect_prov = cls_prov[WithReflectProvenance]
        assert isinstance(reflect_prov, ReflectProvenanceData)
        assert reflect_prov.data["x"] == 42

    def test_multiple_fields(self):
        """Test multiple annotated fields are all collected."""
        cls_prov = MyClassMultiple.cls_provenance()
        reflect_prov = cls_prov[WithReflectProvenance]
        assert isinstance(reflect_prov, ReflectProvenanceData)
        assert len(reflect_prov.data) == 3
        assert reflect_prov.data["a"] == 1
        assert reflect_prov.data["b"] == "two"
        assert reflect_prov.data["c"] == 3.5

    def test_non_annotated_fields_ignored(self):
        """Test that non-annotated fields are ignored."""
        cls_prov = MyClassNonAnnotated.cls_provenance()
        reflect_prov = cls_prov[WithReflectProvenance]
        assert isinstance(reflect_prov, ReflectProvenanceData)
        assert "x" in reflect_prov.data
        assert "y" not in reflect_prov.data

    def test_checksum_stability(self):
        """Test that checksums are stable for same data."""
        checksum1 = MyClassStability.cls_checksum()
        checksum2 = MyClassStability.cls_checksum()
        assert checksum1 == checksum2

    def test_checksum_changes_with_data(self):
        """Test that checksums change when data changes."""
        checksum1 = MyClass1.cls_checksum()
        checksum2 = MyClass2.cls_checksum()
        assert checksum1 != checksum2

    def test_instance_fields_not_in_class_provenance(self):
        """Test that instance fields annotated in __init__ are NOT in class provenance."""
        cls_prov = MyClassWithInstanceFields.cls_provenance()
        reflect_prov = cls_prov[WithReflectProvenance]
        assert isinstance(reflect_prov, ReflectProvenanceData)
        # Class field should be present
        assert "class_field" in reflect_prov.data
        assert reflect_prov.data["class_field"] == 100
        # Instance field should NOT be present in class provenance
        assert "instance_field" not in reflect_prov.data

    def test_class_fields_in_instance_provenance(self):
        """Test that class fields ARE included in instance provenance."""
        instance = MyClassWithInstanceFields("test_value")
        inst_prov = instance.provenance()
        reflect_prov = inst_prov[WithReflectProvenance]
        assert isinstance(reflect_prov, ReflectProvenanceData)
        # Class field should be present in instance provenance
        assert "class_field" in reflect_prov.data
        assert reflect_prov.data["class_field"] == 100
        # Instance field should also be present
        assert "instance_field" in reflect_prov.data
        assert reflect_prov.data["instance_field"] == "test_value"

    def test_instance_fields_in_instance_provenance(self):
        """Test that instance fields annotated in __init__ ARE in instance provenance."""
        instance = MyClassWithInstanceFields("instance_data")
        inst_prov = instance.provenance()
        reflect_prov = inst_prov[WithReflectProvenance]
        assert isinstance(reflect_prov, ReflectProvenanceData)
        # Instance field should be present
        assert "instance_field" in reflect_prov.data
        assert reflect_prov.data["instance_field"] == "instance_data"

    def test_multiple_instance_fields(self):
        """Test multiple instance fields are handled correctly."""
        instance = MyClassMultipleInstanceFields("str_val", 123, 3.14159)
        cls_prov = MyClassMultipleInstanceFields.cls_provenance()
        inst_prov = instance.provenance()

        cls_reflect = cls_prov[WithReflectProvenance]
        inst_reflect = inst_prov[WithReflectProvenance]
        assert isinstance(cls_reflect, ReflectProvenanceData)
        assert isinstance(inst_reflect, ReflectProvenanceData)

        # Class provenance should only have class field
        assert "class_val" in cls_reflect.data
        assert cls_reflect.data["class_val"] == 42
        assert "instance_str" not in cls_reflect.data
        assert "instance_int" not in cls_reflect.data
        assert "instance_float" not in cls_reflect.data

        # Instance provenance should have both class and instance fields
        assert "class_val" in inst_reflect.data
        assert inst_reflect.data["class_val"] == 42
        assert "instance_str" in inst_reflect.data
        assert inst_reflect.data["instance_str"] == "str_val"
        assert "instance_int" in inst_reflect.data
        assert inst_reflect.data["instance_int"] == 123
        assert "instance_float" in inst_reflect.data
        assert inst_reflect.data["instance_float"] == 3.14  # transformed

    def test_only_instance_fields_class_provenance_empty(self):
        """Test that class provenance is empty when only instance fields exist."""
        cls_prov = MyClassOnlyInstanceFields.cls_provenance()
        reflect_prov = cls_prov[WithReflectProvenance]
        assert isinstance(reflect_prov, ReflectProvenanceData)
        # Should be empty or only contain fields that exist at class level
        assert "instance_only" not in reflect_prov.data
        # If there are no class fields, the data dict should be empty
        assert len(reflect_prov.data) == 0

    def test_only_instance_fields_instance_provenance_has_them(self):
        """Test that instance provenance includes instance fields when no class fields exist."""
        instance = MyClassOnlyInstanceFields("only_instance")
        inst_prov = instance.provenance()
        reflect_prov = inst_prov[WithReflectProvenance]
        assert isinstance(reflect_prov, ReflectProvenanceData)
        # Instance field should be present
        assert "instance_only" in reflect_prov.data
        assert reflect_prov.data["instance_only"] == "only_instance"
