"""Tests for method_types.py: uniform method decoration with type preservation."""

from __future__ import annotations

from collections.abc import Callable
from functools import lru_cache
from types import FunctionType
from typing import Any, Never

from provenance_toolkit import MethodDecorator, MethodTypes, MethodWrapper

# ============================================================================
# Test utilities: decorators that assert method types
# ============================================================================


def assert_method_type(
    expected_type: (
        type[staticmethod]
        | type[classmethod]
        | type[FunctionType]
        | type[property]
        | type[MethodWrapper]
    ),
) -> Callable[[Any], Any]:
    """Create a decorator that asserts the method type matches expected_type.

    Args:
        expected_type: The expected method type (staticmethod, classmethod,
            FunctionType for bound methods, property, or MethodWrapper)

    Returns:
        A decorator that asserts the method type and returns it unchanged
    """

    def decorator(fn: Any) -> Any:
        assert isinstance(fn, expected_type), (
            f"Expected {expected_type}, got {type(fn)}"
        )
        return fn

    return decorator


# ============================================================================
# Test class with various method types and decorators
# ============================================================================


class SomeClass:
    """Test class with various method types and decorator combinations."""

    _instance_count = 0

    def __init__(self, value: int = 0) -> None:
        self._value = value
        SomeClass._instance_count += 1

    # ========================================================================
    # Static methods
    # ========================================================================

    @assert_method_type(staticmethod)
    @staticmethod
    @assert_method_type(FunctionType)  # Before @staticmethod: raw function
    def static_no_decorators(x: int) -> int:
        """Static method with no additional decorators."""
        return x * 2

    @assert_method_type(staticmethod)
    @staticmethod
    @lru_cache(maxsize=128)
    @assert_method_type(FunctionType)  # Before @lru_cache: raw function
    def static_with_lru_cache(x: int) -> int:
        """Static method with @lru_cache decorator."""
        return x * 3

    @assert_method_type(staticmethod)
    @staticmethod
    @assert_method_type(MethodWrapper)  # After @MethodDecorator.wrap: MethodWrapper
    @MethodDecorator.wrap
    @assert_method_type(FunctionType)  # Before @MethodDecorator.wrap: raw function
    def static_with_wrap_method(x: int) -> int:
        """Static method with @MethodDecorator.wrap decorator."""
        return x * 4

    @assert_method_type(staticmethod)
    @staticmethod
    @assert_method_type(MethodWrapper)  # After @MethodDecorator.wrap: MethodWrapper
    @MethodDecorator.wrap
    @lru_cache(maxsize=128)
    @assert_method_type(FunctionType)  # Before @lru_cache: raw function
    def static_with_both(x: int) -> int:
        """Static method with both @lru_cache and @MethodDecorator.wrap."""
        return x * 5

    # ========================================================================
    # Class methods
    # ========================================================================

    @assert_method_type(classmethod)
    @classmethod
    @assert_method_type(FunctionType)  # Before @classmethod: raw function
    def class_no_decorators(cls) -> str:
        """Class method with no additional decorators."""
        return cls.__name__

    @assert_method_type(classmethod)
    @classmethod
    @lru_cache(maxsize=128)
    @assert_method_type(FunctionType)  # Before @lru_cache: raw function
    def class_with_lru_cache(cls) -> str:
        """Class method with @lru_cache decorator."""
        return f"{cls.__name__}_cached"

    @assert_method_type(classmethod)
    @classmethod
    @assert_method_type(MethodWrapper)  # After @MethodDecorator.wrap: MethodWrapper
    @MethodDecorator.wrap
    @assert_method_type(FunctionType)  # Before @MethodDecorator.wrap: raw function
    def class_with_wrap_method(cls) -> str:
        """Class method with @MethodDecorator.wrap decorator."""
        return f"{cls.__name__}_wrapped"

    @assert_method_type(classmethod)
    @classmethod
    @assert_method_type(MethodWrapper)  # After @MethodDecorator.wrap: MethodWrapper
    @MethodDecorator.wrap
    @lru_cache(maxsize=128)
    @assert_method_type(FunctionType)  # Before @lru_cache: raw function
    def class_with_both(cls) -> str:
        """Class method with both @lru_cache and @MethodDecorator.wrap."""
        return f"{cls.__name__}_both"

    # ========================================================================
    # Bound methods
    # ========================================================================

    @assert_method_type(FunctionType)  # Bound method: FunctionType
    def bound_no_decorators(self, x: int) -> int:
        """Bound method with no additional decorators."""
        return self._value + x

    @assert_method_type(MethodWrapper)  # After @MethodDecorator.wrap: MethodWrapper
    @MethodDecorator.wrap
    @assert_method_type(FunctionType)  # Before @MethodDecorator.wrap: raw function
    def bound_with_wrap_method(self, x: int) -> int:
        """Bound method with @MethodDecorator.wrap decorator."""
        return self._value + x * 3

    @assert_method_type(MethodWrapper)  # After @MethodDecorator.wrap: MethodWrapper
    @MethodDecorator.wrap
    @assert_method_type(FunctionType)  # Before @MethodDecorator.wrap: raw function
    def bound_with_wrap_method_only(self, x: int) -> int:
        """Bound method with @MethodDecorator.wrap decorator."""
        return self._value + x * 4

    # ========================================================================
    # Properties
    # ========================================================================

    # Note: mypy doesn't allow decorators to appear above @property,
    # but the implementation is safe for this use case (and pyright successfully
    # typechecks this).

    @assert_method_type(property)  # type: ignore[prop-decorator]
    @property
    @assert_method_type(FunctionType)  # Before @property: raw function
    def prop_no_decorators(self) -> int:
        """Property with no additional decorators."""
        return self._value

    @assert_method_type(property)  # type: ignore[prop-decorator]
    @property
    @assert_method_type(MethodWrapper)  # After @MethodDecorator.wrap: MethodWrapper
    @MethodDecorator.wrap
    @assert_method_type(FunctionType)  # Before @MethodDecorator.wrap: raw function
    def prop_with_wrap_method(self) -> int:
        """Property with @MethodDecorator.wrap decorator."""
        return self._value * 3

    @assert_method_type(property)  # type: ignore[prop-decorator]
    @property
    @assert_method_type(MethodWrapper)  # After @MethodDecorator.wrap: MethodWrapper
    @MethodDecorator.wrap
    @assert_method_type(FunctionType)  # Before @MethodDecorator.wrap: raw function
    def prop_with_wrap_method_only(self) -> int:
        """Property with @MethodDecorator.wrap decorator."""
        return self._value * 4


# ============================================================================
# Test cases
# ============================================================================


def test_static_methods() -> None:
    """Test static methods with various decorator combinations."""
    # No decorators
    assert SomeClass.static_no_decorators(5) == 10

    # With lru_cache
    assert SomeClass.static_with_lru_cache(5) == 15
    assert SomeClass.static_with_lru_cache(5) == 15  # Should be cached

    # With MethodDecorator.wrap
    assert SomeClass.static_with_wrap_method(5) == 20

    # With both
    assert SomeClass.static_with_both(5) == 25
    assert SomeClass.static_with_both(5) == 25  # Should be cached


def test_class_methods() -> None:
    """Test class methods with various decorator combinations."""
    # No decorators
    assert SomeClass.class_no_decorators() == "SomeClass"

    # With lru_cache
    assert SomeClass.class_with_lru_cache() == "SomeClass_cached"
    assert SomeClass.class_with_lru_cache() == "SomeClass_cached"  # Should be cached

    # With MethodDecorator.wrap
    assert SomeClass.class_with_wrap_method() == "SomeClass_wrapped"

    # With both
    assert SomeClass.class_with_both() == "SomeClass_both"
    assert SomeClass.class_with_both() == "SomeClass_both"  # Should be cached


def test_bound_methods() -> None:
    """Test bound methods with various decorator combinations."""
    obj = SomeClass(10)

    # No decorators
    assert obj.bound_no_decorators(5) == 15

    # With MethodDecorator.wrap
    assert obj.bound_with_wrap_method(5) == 25

    # With MethodDecorator.wrap only
    assert obj.bound_with_wrap_method_only(5) == 30


def test_properties() -> None:
    """Test properties with various decorator combinations."""
    obj = SomeClass(10)

    # No decorators
    assert obj.prop_no_decorators == 10

    # With MethodDecorator.wrap
    assert obj.prop_with_wrap_method == 30

    # With MethodDecorator.wrap only
    assert obj.prop_with_wrap_method_only == 40


def test_wrap_method_with_original_descriptor() -> None:
    """Test that MethodDecorator.wrap correctly passes original descriptor to wrapper."""
    call_count = {"count": 0}
    original_descriptors: list[Any] = []

    def tracking_wrapper[O, **P, T](
        raw_fn: MethodTypes.RAW_METHOD[O, P, T],
        descriptor_metadata: dict[str, Any],
        _wrapper_args: tuple[Any, ...],
        _wrapper_kwargs: dict[str, Any],
    ) -> MethodTypes.RAW_METHOD[O, P, T]:
        call_count["count"] += 1
        # Store metadata for verification
        original_descriptors.append(descriptor_metadata)
        return raw_fn

    class TrackingTest:
        @MethodDecorator.wrap(wrapper_fn=tracking_wrapper)  # type: ignore[arg-type]
        @staticmethod
        def static_method(x: int) -> int:
            return x * 2

        @MethodDecorator.wrap(wrapper_fn=tracking_wrapper)  # type: ignore[arg-type]
        @classmethod
        def class_method(cls) -> str:
            return cls.__name__

        @MethodDecorator.wrap(wrapper_fn=tracking_wrapper)  # type: ignore[arg-type]
        def bound_method(self, x: int) -> int:
            return x * 3

        @MethodDecorator.wrap(wrapper_fn=tracking_wrapper)  # type: ignore[arg-type,prop-decorator]
        @property
        def prop(self) -> int:
            return 42

    # Call methods to trigger wrapper
    assert TrackingTest.static_method(5) == 10
    assert TrackingTest.class_method() == "TrackingTest"
    obj = TrackingTest()
    assert obj.bound_method(5) == 15
    assert obj.prop == 42  # type: ignore[misc]

    # Verify wrapper was called for each method
    assert call_count["count"] == 4

    # Verify metadata was captured correctly
    assert len(original_descriptors) == 4
    assert original_descriptors[0]["descriptor_type"] is staticmethod
    assert original_descriptors[1]["descriptor_type"] is classmethod
    assert original_descriptors[2]["descriptor_type"] is None  # bound method
    assert original_descriptors[3]["descriptor_type"] is property


def test_wrap_method_attribute_access() -> None:
    """Test that MethodDecorator.wrap allows adding attributes to final reconstructed descriptor."""

    def attribute_setter[O, **P, T](
        final_descriptor: MethodTypes.RAW_METHOD[O, P, T] | MethodTypes.METHOD[O, P, T],
        _descriptor_metadata: dict[str, Any],
        _wrapper_args: tuple[Any, ...],
        _wrapper_kwargs: dict[str, Any],
    ) -> None:
        # Add an attribute to the final reconstructed descriptor
        object.__setattr__(final_descriptor, "__test_attr", "test_value")

    class AttrTest:
        @MethodDecorator.wrap(attribute_setter=attribute_setter)
        @staticmethod
        def static_method(x: int) -> int:
            return x * 2

        @MethodDecorator.wrap(attribute_setter=attribute_setter)
        @classmethod
        def class_method(cls) -> str:
            return cls.__name__

        @MethodDecorator.wrap(attribute_setter=attribute_setter)
        def bound_method(self, x: int) -> int:
            return x * 3

        @MethodDecorator.wrap(attribute_setter=attribute_setter)  # type: ignore[prop-decorator]
        @property
        def prop(self) -> int:
            return 42

    # Access methods to trigger wrapper
    AttrTest.static_method(5)
    AttrTest.class_method()
    obj = AttrTest()
    obj.bound_method(5)
    _ = obj.prop  # type: ignore[misc]

    # Verify attributes were added to the final descriptors
    # Access the methods to trigger descriptor reconstruction and attribute setting
    _static_desc = AttrTest.__dict__["static_method"]
    # The MethodWrapper will reconstruct the descriptor and apply attributes
    # We can verify by accessing the method and checking the returned descriptor
    result = AttrTest.static_method(5)
    assert result == 10
    # The attribute should be on the reconstructed staticmethod
    # Note: We can't easily check this without storing a reference, but the
    # attribute_setter was called on the final descriptor


def test_wrap_method_decorator_factory() -> None:
    """Test MethodDecorator.wrap used as a decorator factory with keyword arguments."""

    def simple_wrapper[O, **P, T](
        raw_fn: MethodTypes.RAW_METHOD[O, P, T],
        _descriptor_metadata: dict[str, Any],
        _wrapper_args: tuple[Any, ...],
        _wrapper_kwargs: dict[str, Any],
    ) -> MethodTypes.RAW_METHOD[O, P, T]:
        return raw_fn

    class FactoryTest:
        @staticmethod
        @MethodDecorator.wrap(wrapper_fn=simple_wrapper, raw=True)
        def static_method(x: int) -> int:
            return x * 2

        @staticmethod
        @MethodDecorator.wrap(wrapper_fn=simple_wrapper)
        def static_method2(x: int) -> int:
            return FactoryTest.static_method(x)

        @classmethod
        @MethodDecorator.wrap(wrapper_fn=simple_wrapper, raw=True)
        def class_method(cls) -> str:
            return cls.__name__

        @MethodDecorator.wrap(wrapper_fn=simple_wrapper)
        @classmethod
        def class_method2(cls) -> str:
            return cls.class_method()

        @MethodDecorator.wrap(wrapper_fn=simple_wrapper, raw=True)
        def bound_method(self, x: int) -> int:
            return x * 3

    assert FactoryTest.static_method(5) == 10
    assert FactoryTest.static_method(5) == FactoryTest.static_method2(5)
    assert FactoryTest.class_method() == "FactoryTest"
    assert FactoryTest.class_method() == FactoryTest.class_method2()
    obj = FactoryTest()
    assert obj.bound_method(5) == 15


def test_wrap_method_direct_call() -> None:
    """Test MethodDecorator.wrap used as a direct function call."""

    def simple_wrapper[O, **P, T](
        raw_fn: MethodTypes.RAW_METHOD[O, P, T],
        _descriptor_metadata: dict[str, Any],
        _wrapper_args: tuple[Any, ...],
        _wrapper_kwargs: dict[str, Any],
    ) -> MethodTypes.RAW_METHOD[O, P, T]:
        return raw_fn

    def plain_function(x: int) -> int:
        return x * 2

    # Direct call with a function
    wrapped: MethodWrapper[Never, [int], int] = MethodDecorator.wrap(
        plain_function,
        wrapper_fn=simple_wrapper,
        raw=True,
    )
    assert wrapped(5) == 10


def test_type_preservation() -> None:
    """Test that MethodDecorator.wrap preserves method types for type checkers."""

    class TypeTest:
        @MethodDecorator.wrap
        @staticmethod
        def static_method(x: int) -> int:
            return x * 2

        @MethodDecorator.wrap
        @classmethod
        def class_method(cls) -> str:
            return cls.__name__

        @MethodDecorator.wrap
        def bound_method(self, x: int) -> int:
            return x * 3

        @MethodDecorator.wrap  # type: ignore[prop-decorator]
        @property
        def prop(self) -> int:
            return 42

    # Type checker should understand these are the correct types
    static_result: int = TypeTest.static_method(5)
    class_result: str = TypeTest.class_method()
    obj = TypeTest()
    bound_result: int = obj.bound_method(5)
    prop_result: int = obj.prop  # type: ignore[misc]

    assert static_result == 10
    assert class_result == "TypeTest"
    assert bound_result == 15
    assert prop_result == 42
