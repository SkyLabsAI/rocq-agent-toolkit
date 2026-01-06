"""Tests for WithReflectProvenance mixin and Field annotation."""

from __future__ import annotations

from typing import Annotated, Final, get_args, get_origin

from provenance_toolkit import Provenance
from provenance_toolkit.provenance.reflect import (
    ReflectProvenanceData,
    WithReflectProvenance,
)


def _assert_stable_serialize_no_error(prov: ReflectProvenanceData) -> None:
    try:
        assert prov.stable_serialize() == prov.stable_serialize()
    except Exception as exc:
        raise AssertionError(
            f"'ReflectProvenance.stable_serialize' exception for {prov}"
        ) from exc


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

    def test_is_cls_provenance(self):
        """Test is_cls_provenance and is_instance_provenance."""
        prov = ReflectProvenanceData({"x": 42}, is_cls_provenance=True)
        assert prov.is_cls_provenance()
        assert not prov.is_instance_provenance()

    def test_is_instance_provenance(self):
        """Test is_cls_provenance and is_instance_provenance."""
        prov = ReflectProvenanceData({"x": 42})
        assert not prov.is_cls_provenance()
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


class MyClassAutoDetectChecksum1(
    Provenance.ClassIdentity,
    Provenance.Version,
    Provenance.Reflect,
    VERSION="1.0.0",
):
    """Test class for checksum with auto-detected class provenance (version 1)."""

    cfg: Final[Annotated[Config, Provenance.Reflect.Field]] = Config()


class MyClassAutoDetectChecksum2(
    Provenance.ClassIdentity,
    Provenance.Version,
    Provenance.Reflect,
    VERSION="1.0.0",
):
    """Test class for checksum with auto-detected class provenance (version 2)."""

    # Different Config instance - should have same checksum since Config has no instance state
    cfg: Final[Annotated[Config, Provenance.Reflect.Field]] = Config()


class ConfigWithValue(
    Provenance.ClassIdentity,
    Provenance.Version,
    Provenance.Reflect,
    VERSION="1.0.0",
):
    """Config class with a value field for testing instance provenance auto-detection."""

    value: Annotated[int, Provenance.Reflect.Field]

    def __init__(self, value: int) -> None:
        """Initialize with a value."""
        super().__init__()
        self.value = value


class MyClassInstanceAutoDetect(
    Provenance.ClassIdentity,
    Provenance.Version,
    Provenance.Reflect,
    VERSION="1.0.0",
):
    """Test class for instance provenance auto-detection."""

    cfg: Annotated[ConfigWithValue, Provenance.Reflect.Field]

    def __init__(self, cfg: ConfigWithValue) -> None:
        """Initialize with a config."""
        super().__init__()
        self.cfg = cfg


class TestWithReflectProvenance:
    """Tests for WithReflectProvenance mixin."""

    def test_class_provenance_with_values(self):
        """Test class provenance with fields that have values."""
        cls_prov = MyClassWithValues.cls_provenance()
        assert WithReflectProvenance in cls_prov
        reflect_prov = cls_prov[WithReflectProvenance]
        assert isinstance(reflect_prov, ReflectProvenanceData)
        _assert_stable_serialize_no_error(reflect_prov)
        assert reflect_prov.data["x"] == 42
        assert reflect_prov.data["y"] == 3.14

    def test_class_provenance_with_unset_fields(self):
        """Test class provenance with annotated but unset fields."""
        cls_prov = MyClassUnset.cls_provenance()
        reflect_prov = cls_prov[WithReflectProvenance]
        assert isinstance(reflect_prov, ReflectProvenanceData)
        _assert_stable_serialize_no_error(reflect_prov)
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
        _assert_stable_serialize_no_error(reflect_prov)
        assert reflect_prov.data["x"] == 42
        assert reflect_prov.data["model"] == "model_gpt-4"

    def test_instance_provenance_with_unset_fields(self):
        """Test instance provenance with annotated but unset fields."""
        instance = MyClassInstanceUnset()
        # Don't set model

        inst_prov = instance.provenance()
        reflect_prov = inst_prov[WithReflectProvenance]
        assert isinstance(reflect_prov, ReflectProvenanceData)
        _assert_stable_serialize_no_error(reflect_prov)
        assert reflect_prov.data["x"] == 42
        assert reflect_prov.data["model"] == "none"  # transform(None)

    def test_provenance_aware_auto_detection(self):
        """Test best-effort auto-detection of provenance-aware objects."""
        cls_prov = MyClassAutoDetect.cls_provenance()
        reflect_prov = cls_prov[WithReflectProvenance]
        assert isinstance(reflect_prov, ReflectProvenanceData)
        _assert_stable_serialize_no_error(reflect_prov)
        # Should extract checksum from Config's provenance
        assert "cfg" in reflect_prov.data
        assert reflect_prov.data["cfg"] == Config().cls_provenance()

    def test_explicit_transform_overrides_auto_detection(self):
        """Test that explicit transform takes priority over auto-detection."""
        cls_prov = MyClassExplicitTransform.cls_provenance()
        reflect_prov = cls_prov[WithReflectProvenance]
        assert isinstance(reflect_prov, ReflectProvenanceData)
        _assert_stable_serialize_no_error(reflect_prov)
        assert reflect_prov.data["cfg"] == "custom_transform"

    def test_identity_for_raw_data(self):
        """Test that raw data uses identity function."""
        cls_prov = MyClassIdentity.cls_provenance()
        reflect_prov = cls_prov[WithReflectProvenance]
        assert isinstance(reflect_prov, ReflectProvenanceData)
        _assert_stable_serialize_no_error(reflect_prov)
        assert reflect_prov.data["x"] == 42
        assert reflect_prov.data["y"] == "test"

    def test_none_values_included(self):
        """Test that None values are included in provenance."""
        cls_prov = MyClassNone.cls_provenance()
        reflect_prov = cls_prov[WithReflectProvenance]
        assert isinstance(reflect_prov, ReflectProvenanceData)
        _assert_stable_serialize_no_error(reflect_prov)
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
        _assert_stable_serialize_no_error(cls_reflect)
        _assert_stable_serialize_no_error(inst_reflect)

        # Class data should be in instance data
        assert cls_reflect.data["x"] == inst_reflect.data["x"]

    def test_wrapped_in_final(self):
        """Test that Data works when wrapped in Final."""
        cls_prov = MyClassFinal.cls_provenance()
        reflect_prov = cls_prov[WithReflectProvenance]
        assert isinstance(reflect_prov, ReflectProvenanceData)
        _assert_stable_serialize_no_error(reflect_prov)
        assert reflect_prov.data["x"] == 42

    def test_multiple_fields(self):
        """Test multiple annotated fields are all collected."""
        cls_prov = MyClassMultiple.cls_provenance()
        reflect_prov = cls_prov[WithReflectProvenance]
        assert isinstance(reflect_prov, ReflectProvenanceData)
        _assert_stable_serialize_no_error(reflect_prov)
        assert len(reflect_prov.data) == 3
        assert reflect_prov.data["a"] == 1
        assert reflect_prov.data["b"] == "two"
        assert reflect_prov.data["c"] == 3.5

    def test_non_annotated_fields_ignored(self):
        """Test that non-annotated fields are ignored."""
        cls_prov = MyClassNonAnnotated.cls_provenance()
        reflect_prov = cls_prov[WithReflectProvenance]
        assert isinstance(reflect_prov, ReflectProvenanceData)
        _assert_stable_serialize_no_error(reflect_prov)
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
        _assert_stable_serialize_no_error(reflect_prov)
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
        _assert_stable_serialize_no_error(reflect_prov)
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
        _assert_stable_serialize_no_error(reflect_prov)
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
        _assert_stable_serialize_no_error(cls_reflect)
        _assert_stable_serialize_no_error(inst_reflect)

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
        _assert_stable_serialize_no_error(reflect_prov)
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
        _assert_stable_serialize_no_error(reflect_prov)
        # Instance field should be present
        assert "instance_only" in reflect_prov.data
        assert reflect_prov.data["instance_only"] == "only_instance"

    def test_class_checksum_with_auto_detected_provenance(self):
        """Test that class checksum is computed when fields are auto-detected to use cls_provenance()."""
        checksum = MyClassAutoDetect.cls_checksum()
        # Should be a valid checksum (non-empty string)
        assert isinstance(checksum, str)
        assert len(checksum) > 0
        # Should be stable
        checksum2 = MyClassAutoDetect.cls_checksum()
        assert checksum == checksum2

    def test_class_checksum_with_auto_detected_provenance_stability(self):
        """Test that class checksums are stable for the same class with auto-detected provenance."""
        checksum1 = MyClassAutoDetectChecksum1.cls_checksum()
        checksum2 = MyClassAutoDetectChecksum1.cls_checksum()
        # Same class should produce same checksum
        assert checksum1 == checksum2
        # Verify that the checksum includes the auto-detected provenance
        # by checking that it's different from a class without the auto-detected field
        checksum_without = MyClassStability.cls_checksum()
        assert checksum1 != checksum_without

    def test_instance_checksum_with_auto_detected_provenance(self):
        """Test that instance checksum is computed when fields are auto-detected to use provenance()."""
        cfg1 = ConfigWithValue(42)
        instance1 = MyClassInstanceAutoDetect(cfg1)
        checksum1 = instance1.checksum()
        # Should be a valid checksum (non-empty string)
        assert isinstance(checksum1, str)
        assert len(checksum1) > 0
        # Should be stable
        checksum1_again = instance1.checksum()
        assert checksum1 == checksum1_again

    def test_instance_checksum_changes_with_auto_detected_provenance(self):
        """Test that instance checksums change when auto-detected provenance changes."""
        cfg1 = ConfigWithValue(42)
        cfg2 = ConfigWithValue(43)
        instance1 = MyClassInstanceAutoDetect(cfg1)
        instance2 = MyClassInstanceAutoDetect(cfg2)
        checksum1 = instance1.checksum()
        checksum2 = instance2.checksum()
        # Different config values should produce different checksums
        assert checksum1 != checksum2

    def test_instance_checksum_same_auto_detected_provenance(self):
        """Test that instance checksums are the same for same auto-detected provenance."""
        cfg1 = ConfigWithValue(42)
        cfg2 = ConfigWithValue(42)
        instance1 = MyClassInstanceAutoDetect(cfg1)
        instance2 = MyClassInstanceAutoDetect(cfg2)
        checksum1 = instance1.checksum()
        checksum2 = instance2.checksum()
        # Same config values should produce same checksums
        assert checksum1 == checksum2


# Test classes for container-like annotated data with provenance-aware objects
class ActionWithProvenance(
    Provenance.ClassIdentity,
    Provenance.Version,
    Provenance.Reflect,
    VERSION="1.0.0",
):
    """Test action class with provenance for container tests."""

    name: Annotated[str, Provenance.Reflect.Field]

    def __init__(self, name: str) -> None:
        """Initialize with a name."""
        super().__init__()
        self.name = name


class StrategyWithContainerList(
    Provenance.ClassIdentity,
    Provenance.Version,
    Provenance.Reflect,
    VERSION="1.0.0",
):
    """Test strategy class with a list of actions (container-like annotated data)."""

    actions: Annotated[list[ActionWithProvenance], Provenance.Reflect.Field]

    def __init__(self, actions: list[ActionWithProvenance]) -> None:
        """Initialize with a list of actions."""
        super().__init__()
        self.actions = actions


class StrategyWithContainerTuple(
    Provenance.ClassIdentity,
    Provenance.Version,
    Provenance.Reflect,
    VERSION="1.0.0",
):
    """Test strategy class with a tuple of (probability, action) pairs."""

    tactics: Annotated[
        list[tuple[float, ActionWithProvenance]], Provenance.Reflect.Field
    ]

    def __init__(self, tactics: list[tuple[float, ActionWithProvenance]]) -> None:
        """Initialize with a list of (probability, action) tuples."""
        super().__init__()
        self.tactics = tactics


class StrategyWithContainerDict(
    Provenance.ClassIdentity,
    Provenance.Version,
    Provenance.Reflect,
    VERSION="1.0.0",
):
    """Test strategy class with a dict mapping names to actions."""

    action_map: Annotated[dict[str, ActionWithProvenance], Provenance.Reflect.Field]

    def __init__(self, action_map: dict[str, ActionWithProvenance]) -> None:
        """Initialize with a dict of actions."""
        super().__init__()
        self.action_map = action_map


class StrategyWithNestedContainers(
    Provenance.ClassIdentity,
    Provenance.Version,
    Provenance.Reflect,
    VERSION="1.0.0",
):
    """Test strategy class with nested containers."""

    strategy_groups: Annotated[
        list[list[ActionWithProvenance]], Provenance.Reflect.Field
    ]

    def __init__(self, strategy_groups: list[list[ActionWithProvenance]]) -> None:
        """Initialize with nested lists of actions."""
        super().__init__()
        self.strategy_groups = strategy_groups


class TestContainerLikeAnnotatedData:
    """Tests for container-like annotated data containing provenance-aware objects.

    These tests verify that the recursive processing of container-like annotated
    data works correctly. Without the fix, these tests would fail because the
    provenance-aware objects inside containers would not be properly processed.
    """

    def test_list_of_actions_serialization(self):
        """Test that a list of actions can be serialized correctly."""
        action1 = ActionWithProvenance("action1")
        action2 = ActionWithProvenance("action2")
        strategy = StrategyWithContainerList([action1, action2])

        # This should not raise an exception
        inst_prov = strategy.provenance()
        reflect_prov = inst_prov[WithReflectProvenance]
        assert isinstance(reflect_prov, ReflectProvenanceData)
        _assert_stable_serialize_no_error(reflect_prov)

        # The actions should be recursively processed to their provenance
        actions_data = reflect_prov.data["actions"]
        assert isinstance(actions_data, list)
        assert len(actions_data) == 2

        # Each action should be converted to its provenance data
        for action_prov in actions_data:
            assert isinstance(action_prov, dict)
            # Should contain provenance data from ActionWithProvenance
            assert WithReflectProvenance in action_prov

        # Serialization should work without errors
        serialized = reflect_prov.stable_serialize()
        assert isinstance(serialized, str)
        assert len(serialized) > 0

    def test_tuple_of_probability_action_pairs_serialization(self):
        """Test that tuples of (probability, action) pairs can be serialized."""
        action1 = ActionWithProvenance("auto")
        action2 = ActionWithProvenance("tauto")
        strategy = StrategyWithContainerTuple([(1.0, action1), (0.5, action2)])

        # This should not raise an exception
        inst_prov = strategy.provenance()
        reflect_prov = inst_prov[WithReflectProvenance]
        assert isinstance(reflect_prov, ReflectProvenanceData)
        _assert_stable_serialize_no_error(reflect_prov)

        # The tactics should be recursively processed
        tactics_data = reflect_prov.data["tactics"]
        assert isinstance(tactics_data, list)
        assert len(tactics_data) == 2

        # Each tuple should be processed
        for tactic_tuple in tactics_data:
            assert isinstance(tactic_tuple, list)  # Tuples become lists in JSON
            assert len(tactic_tuple) == 2
            assert isinstance(tactic_tuple[0], float)
            # The action should be converted to its provenance
            assert isinstance(tactic_tuple[1], dict)
            assert WithReflectProvenance in tactic_tuple[1]

        # Serialization should work without errors
        serialized = reflect_prov.stable_serialize()
        assert isinstance(serialized, str)
        assert len(serialized) > 0

    def test_dict_of_actions_serialization(self):
        """Test that a dict mapping names to actions can be serialized."""
        action1 = ActionWithProvenance("action1")
        action2 = ActionWithProvenance("action2")
        strategy = StrategyWithContainerDict({"first": action1, "second": action2})

        # This should not raise an exception
        inst_prov = strategy.provenance()
        reflect_prov = inst_prov[WithReflectProvenance]
        assert isinstance(reflect_prov, ReflectProvenanceData)
        _assert_stable_serialize_no_error(reflect_prov)

        # The action_map should be recursively processed
        action_map_data = reflect_prov.data["action_map"]
        assert isinstance(action_map_data, dict)
        assert len(action_map_data) == 2

        # Each action should be converted to its provenance
        for action_prov in action_map_data.values():
            assert isinstance(action_prov, dict)
            assert WithReflectProvenance in action_prov

        # Serialization should work without errors
        serialized = reflect_prov.stable_serialize()
        assert isinstance(serialized, str)
        assert len(serialized) > 0

    def test_nested_containers_serialization(self):
        """Test that nested containers (list of lists) can be serialized."""
        action1 = ActionWithProvenance("action1")
        action2 = ActionWithProvenance("action2")
        action3 = ActionWithProvenance("action3")
        strategy = StrategyWithNestedContainers([[action1, action2], [action3]])

        # This should not raise an exception
        inst_prov = strategy.provenance()
        reflect_prov = inst_prov[WithReflectProvenance]
        assert isinstance(reflect_prov, ReflectProvenanceData)
        _assert_stable_serialize_no_error(reflect_prov)

        # The nested lists should be recursively processed
        groups_data = reflect_prov.data["strategy_groups"]
        assert isinstance(groups_data, list)
        assert len(groups_data) == 2

        # Each inner list should be processed
        assert isinstance(groups_data[0], list)
        assert len(groups_data[0]) == 2
        assert isinstance(groups_data[1], list)
        assert len(groups_data[1]) == 1

        # Each action should be converted to its provenance
        for group in groups_data:
            for action_prov in group:
                assert isinstance(action_prov, dict)
                assert WithReflectProvenance in action_prov

        # Serialization should work without errors
        serialized = reflect_prov.stable_serialize()
        assert isinstance(serialized, str)
        assert len(serialized) > 0

    def test_list_of_actions_class_provenance(self):
        """Test that class provenance works with container-like data."""

        # For class provenance, we need class-level fields
        # This test verifies that the is_cls_provenance flag is correctly used
        class StrategyWithClassLevelList(
            Provenance.ClassIdentity,
            Provenance.Version,
            Provenance.Reflect,
            VERSION="1.0.0",
        ):
            """Strategy with class-level list of action types."""

            action_types: Final[
                Annotated[list[type[ActionWithProvenance]], Provenance.Reflect.Field]
            ] = [ActionWithProvenance]

        cls_prov = StrategyWithClassLevelList.cls_provenance()
        reflect_prov = cls_prov[WithReflectProvenance]
        assert isinstance(reflect_prov, ReflectProvenanceData)
        _assert_stable_serialize_no_error(reflect_prov)

        # The action_types should be processed
        action_types_data = reflect_prov.data["action_types"]
        assert isinstance(action_types_data, list)
        assert len(action_types_data) == 1

        # The class should be converted to its class provenance
        assert isinstance(action_types_data[0], dict)
        assert WithReflectProvenance in action_types_data[0]

        # Serialization should work without errors
        serialized = reflect_prov.stable_serialize()
        assert isinstance(serialized, str)
        assert len(serialized) > 0

    def test_mixed_container_content(self):
        """Test container with mixed content (some with provenance, some without)."""
        action1 = ActionWithProvenance("action1")
        action2 = ActionWithProvenance("action2")

        class StrategyWithMixedContent(
            Provenance.ClassIdentity,
            Provenance.Version,
            Provenance.Reflect,
            VERSION="1.0.0",
        ):
            """Strategy with mixed container content."""

            mixed_list: Annotated[
                list[ActionWithProvenance | str], Provenance.Reflect.Field
            ]

            def __init__(self, mixed_list: list[ActionWithProvenance | str]) -> None:
                super().__init__()
                self.mixed_list = mixed_list

        strategy = StrategyWithMixedContent([action1, "plain_string", action2])

        # This should not raise an exception
        inst_prov = strategy.provenance()
        reflect_prov = inst_prov[WithReflectProvenance]
        assert isinstance(reflect_prov, ReflectProvenanceData)
        _assert_stable_serialize_no_error(reflect_prov)

        # The mixed list should be processed
        mixed_data = reflect_prov.data["mixed_list"]
        assert isinstance(mixed_data, list)
        assert len(mixed_data) == 3

        # Actions should be converted to provenance, strings should remain strings
        assert isinstance(mixed_data[0], dict)  # action1 provenance
        assert isinstance(mixed_data[1], str)  # plain_string
        assert isinstance(mixed_data[2], dict)  # action2 provenance

        # Serialization should work without errors
        serialized = reflect_prov.stable_serialize()
        assert isinstance(serialized, str)
        assert len(serialized) > 0
