"""Utilities and types for uniform metaprogramming on methods of classes."""

# Note: this is generic and could potentially be distributed as a separate module.

from __future__ import annotations

import logging
from collections.abc import Callable
from functools import wraps
from types import FunctionType
from typing import (
    Annotated,  # for intersection of types, cf. MethodTypes.RAW_BOUNDMETHOD
    Any,
    Concatenate,
    Literal,
    TypeIs,
    cast,
    final,
    overload,
)

from .method_types import *

logger = logging.getLogger(__name__)


# Type alias for wrapper function: wraps the raw function (behavior modification)
# The inputs are:
#   - raw_fn: RAW_METHOD (the underlying function)
#   - descriptor_metadata: dict with information about the descriptor type
#   - wrapper_args: positional arguments for the wrapper
#   - wrapper_kwargs: keyword arguments for the wrapper
# Output is a wrapped callable
type WrapperFunc[O, **P, T] = Callable[
    [
        MethodTypes.RAW_METHOD[O, P, T],
        dict[str, Any],  # descriptor metadata
        tuple[Any, ...],
        dict[str, Any],
    ],
    MethodTypes.RAW_METHOD[O, P, T],
]

# Type alias for attribute setter: adds attributes to the final reconstructed descriptor
# The inputs are:
#   - final_descriptor: METHOD (the reconstructed descriptor after wrapping)
#   - descriptor_metadata: dict with information about the descriptor type
#   - wrapper_args: positional arguments
#   - wrapper_kwargs: keyword arguments
# Output is None (modifies descriptor in place)
type AttributeSetter[O, **P, T] = Callable[
    [
        MethodTypes.RAW_METHOD[O, P, T] | MethodTypes.METHOD[O, P, T],
        dict[str, Any],  # descriptor metadata
        tuple[Any, ...],
        dict[str, Any],
    ],
    None,
]


class MethodWrapper[O, **P, T, METH_TV]:
    """A descriptor that wraps a function/method and allows uniform decoration.

    This class implements the descriptor protocol to handle all types of methods
    correctly, including regular methods, static methods, class methods, and
    properties. It preserves the original method type and works correctly with
    static type checkers. It also works correctly regarding of the order that
    classmethod/staticmethod/property decorators are applied.

    Based on: https://asyncmove.com/blog/2025/01/all-decorators-systematically-decorating-python-class-methods/
    """

    # Constants for special attribute names
    DUNDER_GET = "__get__"
    DUNDER_DOC = "__doc__"
    DUNDER_ABSTRACT = "__isabstractmethod__"
    DUNDER_MODULE = "__module__"
    DUNDER_NAME = "__name__"
    DUNDER_QUALNAME = "__qualname__"

    def __init__(
        self,
        fn: MethodTypes.METHOD[O, P, T] | MethodTypes.RAW_METHOD[O, P, T],
        wrapper_fn: WrapperFunc[O, P, T] | None = None,
        attribute_setter: AttributeSetter[O, P, T] | None = None,
        wrapper_fn_args: tuple[Any, ...] | None = None,
        wrapper_fn_kwargs: dict[str, Any] | None = None,
    ) -> None:
        """Initialize the MethodWrapper.

        Args:
            fn: The function or method to wrap (can be a descriptor or callable)
            wrapper_fn: Function that wraps the raw function. Signature:
                (raw_fn, descriptor_metadata, wrapper_args, wrapper_kwargs) -> wrapped_fn
            attribute_setter: Optional function that adds attributes to the final descriptor.
                Signature: (final_descriptor, descriptor_metadata, wrapper_args, wrapper_kwargs) -> None
            wrapper_fn_args: Positional arguments to pass to wrapper_fn and attribute_setter
            wrapper_fn_kwargs: Keyword arguments to pass to wrapper_fn and attribute_setter
        """
        # Copy special attributes from the original function
        for attr_name in (
            self.DUNDER_ABSTRACT,
            self.DUNDER_DOC,
            self.DUNDER_MODULE,
            self.DUNDER_NAME,
            self.DUNDER_QUALNAME,
        ):
            attr_value = getattr(fn, attr_name, None)
            if attr_value is not None:
                setattr(self, attr_name, attr_value)

        # Initialize instance attributes with proper types
        self._inst: O | None = None
        self._owner: type[O] | None = (
            None  # Cached owner class (set on first __get__ call with owner)
        )
        self._descriptor_type: (
            type[staticmethod] | type[classmethod] | type[property] | None
        ) = None
        self._property_getter_type: type[staticmethod] | type[classmethod] | None = None
        self._property_fget: Any | None = None
        self._property_fset: Any | None = None
        self._property_fdel: Any | None = None
        self._fn: MethodTypes.RAW_METHOD[O, P, T] | None = None
        self._is_free_fn: bool = False

        # Store wrapper function and attribute setter
        if wrapper_fn is None:

            def default_wrapper_fn(
                raw_fn: MethodTypes.RAW_METHOD[O, P, T],
                _descriptor_metadata: dict[str, Any],
                wrapper_args: tuple[Any, ...],
                wrapper_kwargs: dict[str, Any],
            ) -> MethodTypes.RAW_METHOD[O, P, T]:
                if wrapper_args:
                    logger.warning(
                        "wrap_method: %s received positional arguments: %s",
                        raw_fn.__name__ if hasattr(raw_fn, "__name__") else raw_fn,
                        wrapper_args,
                    )
                if wrapper_kwargs:
                    logger.warning(
                        "wrap_method: %s received keyword arguments: %s",
                        raw_fn.__name__ if hasattr(raw_fn, "__name__") else raw_fn,
                        wrapper_kwargs,
                    )
                return raw_fn

            self._wrapper_fn: WrapperFunc[O, P, T] = default_wrapper_fn
        else:
            self._wrapper_fn = wrapper_fn

        self._attribute_setter = attribute_setter
        self._wrapper_fn_args = wrapper_fn_args if wrapper_fn_args is not None else ()
        self._wrapper_fn_kwargs = (
            wrapper_fn_kwargs if wrapper_fn_kwargs is not None else {}
        )

        # Determine if this is a descriptor (staticmethod, classmethod, property) or a function
        # Store the original descriptor type for reconstruction
        if isinstance(fn, staticmethod):
            self._extract_staticmethod_info(fn)
        elif isinstance(fn, classmethod):
            self._extract_classmethod_info(fn)
        elif isinstance(fn, property):
            self._extract_property_info(fn)
        elif isinstance(fn, FunctionType):
            # It's a bound method (FunctionType) or free function
            self._set_descriptor_type(None)
            self._fn = fn
            self._is_free_fn = True
        else:
            if not callable(fn):
                raise ValueError(f"fn is not callable: {fn}")
            self._set_descriptor_type(None)
            self._fn = fn
            self._is_free_fn = not hasattr(fn, self.DUNDER_GET)

    def _set_descriptor_type(
        self,
        descriptor_type: type[staticmethod] | type[classmethod] | type[property] | None,
    ) -> None:
        """Set the descriptor type with a guard to prevent overwriting.

        Args:
            descriptor_type: The descriptor type to set
        """
        if (
            self._descriptor_type is not None
            and self._descriptor_type != descriptor_type
        ):
            raise ValueError(
                f"Cannot overwrite descriptor_type {self._descriptor_type} with {descriptor_type}"
            )
        self._descriptor_type = descriptor_type

    def _extract_staticmethod_info(self, static_method: staticmethod[Any, Any]) -> None:
        """Extract information from a staticmethod descriptor.

        Args:
            static_method: The staticmethod descriptor to extract info from
        """
        self._set_descriptor_type(staticmethod)
        self._fn = static_method.__func__
        self._is_free_fn = False

    def _extract_classmethod_info(
        self, class_method: classmethod[Any, Any, Any]
    ) -> None:
        """Extract information from a classmethod descriptor.

        Args:
            class_method: The classmethod descriptor to extract info from
        """
        self._set_descriptor_type(classmethod)
        self._fn = class_method.__func__
        self._is_free_fn = False

    def _extract_property_info(self, prop: property) -> None:
        """Extract information from a property descriptor.

        Args:
            prop: The property descriptor to extract info from
        """
        self._set_descriptor_type(property)
        # Store property attributes
        self._property_fget = prop.fget
        self._property_fset = getattr(prop, "fset", None)
        self._property_fdel = getattr(prop, "fdel", None)
        # Check if the getter is itself a staticmethod or classmethod
        fget = prop.fget
        if isinstance(fget, staticmethod):
            self._property_getter_type = staticmethod
            self._fn = fget.__func__
        elif isinstance(fget, classmethod):
            self._property_getter_type = classmethod
            self._fn = fget.__func__
        else:
            self._property_getter_type = None
            self._fn = fget  # Use fget as the function to wrap
        self._is_free_fn = False

    def _detect_wrapped_descriptor(self, owner: type[Any]) -> None:
        """Detect if this MethodWrapper is wrapped by a descriptor in the owner class.

        This handles the case where wrap_method is applied before @staticmethod/@classmethod/@property.

        Args:
            owner: The class that owns this method
        """
        if self._descriptor_type is not None:
            # Already detected, no need to check again
            return

        attr_name = getattr(self, "__name__", None)
        if attr_name is None or attr_name not in owner.__dict__:
            return

        attr_value = owner.__dict__[attr_name]
        # Check if attr_value is a staticmethod/classmethod that wraps self
        if isinstance(attr_value, staticmethod):
            wrapped_func = getattr(attr_value, "__func__", None)
            if wrapped_func is self:
                self._set_descriptor_type(staticmethod)
                # The function is already stored in self._fn from __init__
        elif isinstance(attr_value, classmethod):
            wrapped_func = getattr(attr_value, "__func__", None)
            if wrapped_func is self:
                self._set_descriptor_type(classmethod)
                # The function is already stored in self._fn from __init__
        elif isinstance(attr_value, property):
            self._detect_wrapped_property(attr_value)

        # Also check if we're being accessed as the __func__ of a classmethod/staticmethod
        # This happens when @classmethod/@staticmethod is applied after @wrap_method
        # In this case, the classmethod/staticmethod object is returned by __get__,
        # and we need to handle being called from that context
        # We detect this by checking if we're being called from a classmethod/staticmethod context
        # via the call stack or by checking if owner has a classmethod/staticmethod with us as __func__
        if self._descriptor_type is None:
            # Check if any attribute in the class is a classmethod/staticmethod with us as __func__
            for value in owner.__dict__.values():
                if isinstance(value, (classmethod, staticmethod)):
                    wrapped_func = getattr(value, "__func__", None)
                    if wrapped_func is self:
                        if isinstance(value, classmethod):
                            self._set_descriptor_type(classmethod)
                        elif isinstance(value, staticmethod):
                            self._set_descriptor_type(staticmethod)
                        break

    def _detect_wrapped_property(self, prop: property) -> None:
        """Detect if this MethodWrapper is wrapped by a property descriptor.

        Args:
            prop: The property descriptor that might wrap self
        """
        # For property, check if fget is self or wraps self
        fget = getattr(prop, "fget", None)
        property_getter_type: type[staticmethod] | type[classmethod] | None = None

        if fget is self:
            property_getter_type = None
        # Also check if fget is a staticmethod/classmethod wrapping self
        elif isinstance(fget, staticmethod):
            if getattr(fget, "__func__", None) is self:
                property_getter_type = staticmethod
        elif isinstance(fget, classmethod):
            if getattr(fget, "__func__", None) is self:
                property_getter_type = classmethod
        else:
            # fget doesn't wrap self, so we're not wrapped by this property
            return

        # If we get here, we've detected that we're wrapped by this property
        self._set_descriptor_type(property)
        # Only set property_getter_type if it hasn't been set yet (guard against overwriting)
        if self._property_getter_type is None:
            self._property_getter_type = property_getter_type
        # Only set fset/fdel if they haven't been set yet (guard against overwriting)
        if self._property_fset is None:
            self._property_fset = getattr(prop, "fset", None)
        if self._property_fdel is None:
            self._property_fdel = getattr(prop, "fdel", None)
        # The function is already stored in self._fn from __init__

    def _build_descriptor_metadata(self) -> dict[str, Any]:
        """Build metadata dictionary about the descriptor type.

        Returns:
            A dictionary containing information about the descriptor type,
            property attributes, etc.
        """
        return {
            "descriptor_type": self._descriptor_type,
            "property_getter_type": self._property_getter_type,
            "property_fset": self._property_fset,
            "property_fdel": self._property_fdel,
        }

    @overload
    def __get__(
        self,
        inst: O | None,
        owner: type[O] | None = None,
        descriptor_type: type[property] = property,
    ) -> T: ...
    @overload
    def __get__(
        self,
        inst: O | None,
        owner: type[O] | None = None,
        descriptor_type: type[classmethod] = classmethod,
    ) -> MethodTypes.RAW_CLASSMETHOD[O, P, T]: ...
    @overload
    def __get__(
        self,
        inst: O | None,
        owner: type[O] | None = None,
        descriptor_type: type[staticmethod] = staticmethod,
    ) -> MethodTypes.RAW_STATICMETHOD[P, T]: ...
    @overload
    def __get__(
        self,
        inst: O,
        owner: type[O] | None = None,
        descriptor_type: None = None,
    ) -> MethodTypes.RAW_BOUNDMETHOD[O, P, T]: ...

    def __get__(
        self,
        inst: O | None,
        owner: type[O] | None = None,
        descriptor_type: (
            type[staticmethod] | type[classmethod] | type[property] | None
        ) = None,
    ) -> METH_TV | MethodTypes.RAW_METHOD[O, P, T] | T:
        """Implements the descriptor protocol.

        Args:
            inst: The instance that the method is being accessed from (None for class access)
            owner: The class that owns the method

        Returns:
            The wrapped method, preserving the original descriptor type
        """
        self._inst = inst
        # Cache the owner if we don't have one yet (for later use when owner=None)
        if self._owner is None and owner is not None:
            self._owner = owner
        self._is_free_fn = False

        # If we don't have a descriptor type yet, check if we're wrapped by one
        # This handles the case where wrap_method is applied before @staticmethod/@classmethod/@property
        assert self._fn is not None, "fn is not set"
        fn_to_wrap: MethodTypes.RAW_METHOD[O, P, T]
        # Use the current owner if provided, otherwise fall back to cached owner
        owner_to_use = owner if owner is not None else self._owner
        if owner_to_use is not None:
            self._detect_wrapped_descriptor(owner_to_use)

        # Get the underlying function to wrap
        if self._descriptor_type is staticmethod:
            # For staticmethod, use the stored function directly
            fn_to_wrap = self._fn
        elif self._descriptor_type is classmethod:
            # For classmethod, use the stored function directly
            fn_to_wrap = self._fn
        elif self._descriptor_type is property:
            # For property, we need to wrap the getter
            # Use the stored function (already unwrapped if it was staticmethod/classmethod)
            fn_to_wrap = self._fn
            if fn_to_wrap is None:
                raise AttributeError("property has no getter")
        else:
            # Free function or bound method - use directly
            fn_to_wrap = self._fn

        # Build descriptor metadata
        descriptor_metadata = self._build_descriptor_metadata()

        # Phase 1: Apply the wrapper function to wrap behavior
        wrapped_fn: MethodTypes.RAW_METHOD[O, P, T] = self._wrapper_fn(
            fn_to_wrap,
            descriptor_metadata,
            self._wrapper_fn_args,
            self._wrapper_fn_kwargs,
        )

        # Preserve metadata
        if hasattr(fn_to_wrap, "__name__"):
            wrapped_fn = wraps(cast(Callable[..., Any], fn_to_wrap))(
                cast(Callable[..., Any], wrapped_fn)
            )

        # Phase 2: Reconstruct the descriptor from the wrapped function
        final_descriptor: MethodTypes.RAW_METHOD[O, P, T] | MethodTypes.METHOD[O, P, T]
        if self._descriptor_type is staticmethod:
            # For staticmethod, always return the wrapped function directly.
            # staticmethod.__get__ always returns the underlying function, not the staticmethod object.
            final_descriptor = wrapped_fn
        elif self._descriptor_type is classmethod:
            cm = classmethod(cast(MethodTypes.RAW_CLASSMETHOD[O, P, T], wrapped_fn))
            # For classmethod, we need to return the bound method, not the classmethod object
            # This is because classmethod objects are not directly callable
            if owner is not None:
                # Return the bound method by calling classmethod.__get__
                final_descriptor = cm.__get__(inst, owner)
            else:
                final_descriptor = cm
        elif self._descriptor_type is property:
            # Reconstruct property with wrapped getter
            # If the original getter was a staticmethod or classmethod, preserve that
            fget: Any
            if self._property_getter_type is staticmethod:
                fget = staticmethod(
                    cast(MethodTypes.RAW_STATICMETHOD[P, T], wrapped_fn)
                )
            elif self._property_getter_type is classmethod:
                fget = classmethod(
                    cast(MethodTypes.RAW_CLASSMETHOD[O, P, T], wrapped_fn)
                )
            else:
                fget = wrapped_fn
            prop = property(
                fget=fget,
                fset=self._property_fset,
                fdel=self._property_fdel,
            )
            # For property, we need to return the result of property.__get__, not the property object
            # This is because property objects are not directly accessible - they need to be accessed
            # through the descriptor protocol
            if inst is not None and owner is not None:
                # Return the value by calling property.__get__
                final_descriptor = prop.__get__(inst, owner)
            else:
                final_descriptor = prop
        else:
            # Bound method or free function - return the wrapped function directly
            # If accessed from an instance, bind it
            if inst is not None and owner is not None:
                if not hasattr(wrapped_fn, "__get__"):
                    raise TypeError(
                        "wrapped_fn does not have __get__ method and cannot be bound"
                    )
                # Create a bound method
                final_descriptor = object.__getattribute__(wrapped_fn, "__get__")(
                    inst, owner
                )
            else:
                final_descriptor = wrapped_fn

        # Phase 3: Apply attribute setter to the final reconstructed descriptor
        if self._attribute_setter is not None:
            # Only apply attribute setter if the descriptor supports it
            # Bound methods don't support setting attributes
            try:
                self._attribute_setter(
                    final_descriptor,
                    descriptor_metadata,
                    self._wrapper_fn_args,
                    self._wrapper_fn_kwargs,
                )
            except (AttributeError, TypeError):
                # Bound methods and some other descriptors don't support setting attributes
                # This is expected and we just skip the attribute setter
                pass

        # Note: unsafe cast; we rely on MethodDecorator to instantiate METH_TV in the right way.
        return cast(METH_TV, final_descriptor)

    @overload
    def __call__(self, cls: type[O], *args: P.args, **kwargs: P.kwargs) -> T:
        """Overload for classmethod: first arg is the class."""

    @overload
    def __call__(self, self_arg: O, *args: P.args, **kwargs: P.kwargs) -> T:
        """Overload for bound method: first arg is the instance."""

    @overload
    def __call__(self, *args: P.args, **kwargs: P.kwargs) -> T:
        """Overload for staticmethod: no instance/class arg."""

    def __call__(self, *args: Any, **kwargs: Any) -> T:
        """Calls the wrapped function with the provided arguments.

        This is used when the MethodWrapper instance is called directly
        (e.g., `wrapper = MethodWrapper(fn); wrapper(args)`).

        For methods on classes, `__get__` is called when accessing the attribute,
        which returns the final descriptor that handles its own invocation.

        This also handles the case where MethodWrapper is the __func__ of a classmethod/staticmethod.
        When @classmethod/@staticmethod wraps a MethodWrapper, classmethod.__get__/staticmethod.__get__
        returns the MethodWrapper instance. When that instance is called, we need to handle it correctly.
        """
        # If descriptor type is not set, try to detect it
        if self._descriptor_type is None:
            if self._owner is not None:
                self._detect_wrapped_descriptor(self._owner)
            elif self._fn is not None:
                # If we don't have a cached owner, check if the function's __qualname__
                # suggests it's a method (has a dot). If so, assume it's a staticmethod
                # and treat it as such. This handles the case where @staticmethod is
                # applied after @MethodDecorator.wrap and we're called before __get__
                # is ever called with an owner.
                qualname = getattr(self._fn, "__qualname__", None)
                if qualname and "." in qualname and not qualname.endswith(".<locals>"):
                    logger.debug(
                        f"Qualname suggests it's a method: {qualname}, setting descriptor type to staticmethod"
                    )
                    # Looks like a method, assume it's a staticmethod
                    self._set_descriptor_type(staticmethod)

        # Handle each descriptor type uniformly
        if self._descriptor_type is classmethod:
            # For classmethod, the first argument should be the class
            if args:
                first_arg = args[0]
                if isinstance(first_arg, type):
                    # First argument is a class, use it as owner
                    owner = cast(type[O], first_arg)
                    return self.__get__(None, owner, descriptor_type=classmethod)(
                        owner, *args[1:], **kwargs
                    )
            # Fallback: try to use cached owner
            if self._owner is not None:
                cm_descriptor_fallback = self.__get__(
                    None, self._owner, descriptor_type=classmethod
                )
                # Need to pass the class as first argument, then remaining args
                return cm_descriptor_fallback(self._owner, *args, **kwargs)
            # If no owner available, we can't properly call a classmethod
            raise TypeError("Cannot call classmethod without a class context")
        elif self._descriptor_type is staticmethod:
            # For staticmethod, call with no instance/owner
            sm_descriptor_raw = self.__get__(None, None, descriptor_type=staticmethod)
            # RAW_STATICMETHOD is Callable[P, T], so *args, **kwargs should work
            sm_descriptor: MethodTypes.RAW_STATICMETHOD[P, T] = cast(
                MethodTypes.RAW_STATICMETHOD[P, T], sm_descriptor_raw
            )
            return sm_descriptor(*args, **kwargs)
        elif self._descriptor_type is property:
            # For property, we need an instance to access it
            if not args:
                raise TypeError("Cannot access property without an instance")
            prop_inst: O = cast(O, args[0])
            prop_owner: type[O] = (
                self._owner
                if self._owner is not None
                else cast(type[O], type(prop_inst))
            )
            # When accessing property on instance, property.__get__ returns T
            # Access property on instance - this returns T
            prop_value = self.__get__(prop_inst, prop_owner, descriptor_type=property)
            return cast(T, prop_value)
        else:
            # Bound method or free function
            if args:
                # Bound method: try to infer instance from args
                bound_inst: O = cast(O, args[0])
                bound_owner: type[O] = (
                    self._owner
                    if self._owner is not None
                    else cast(type[O], type(bound_inst))
                )
                # RAW_BOUNDMETHOD expects O as first arg, then P.args
                bound_descriptor_raw = self.__get__(
                    bound_inst, bound_owner, descriptor_type=None
                )
                bound_descriptor: MethodTypes.RAW_BOUNDMETHOD[O, P, T] = cast(
                    MethodTypes.RAW_BOUNDMETHOD[O, P, T], bound_descriptor_raw
                )
                return bound_descriptor(bound_inst, *args[1:], **kwargs)
            else:
                # Free function: just call with args (no instance)
                # For free functions, we need to use the function directly
                # since __get__ with None requires an instance for bound methods
                if self._fn is not None:
                    # Directly call the function if available
                    fn_callable: Callable[P, T] = cast(Callable[P, T], self._fn)
                    return fn_callable(*args, **kwargs)
                # Fallback: this shouldn't happen, but handle it
                raise TypeError("Cannot call method without function or instance")


type METH[O, **P, T] = MethodTypes.RAW_METHOD[O, P, T] | MethodTypes.METHOD[O, P, T] | T


class MethodDecorator:
    """Base class for method decorators that use wrap_method functionality."""

    @overload
    @staticmethod
    def wrap[O, **P, T](
        fn: None = None,
        *,
        wrapper_fn: WrapperFunc[O, P, T] | None = None,
        attribute_setter: AttributeSetter[O, P, T] | None = None,
        wrapper_fn_args: tuple[Any, ...] | None = None,
        wrapper_fn_kwargs: dict[str, Any] | None = None,
        raw: Literal[True],
    ) -> Callable[
        [MethodTypes.RAW_METHOD[O, P, T]],
        MethodWrapper[O, P, T, MethodTypes.RAW_METHOD[O, P, T] | T],
    ]:
        """Overload: Decorator factory with wrapper_fn (and optional attribute_setter)."""

    @overload
    @staticmethod
    def wrap[O, **P, T](
        fn: None = None,
        *,
        wrapper_fn: WrapperFunc[O, P, T] | None = None,
        attribute_setter: AttributeSetter[O, P, T] | None = None,
        wrapper_fn_args: tuple[Any, ...] | None = None,
        wrapper_fn_kwargs: dict[str, Any] | None = None,
        raw: Literal[False] = False,
    ) -> Callable[
        [MethodTypes.METHOD[O, P, T]],
        MethodWrapper[O, P, T, MethodTypes.METHOD[O, P, T] | T],
    ]:
        """Overload: Decorator factory with wrapper_fn (and optional attribute_setter)."""

    @overload
    @staticmethod
    def wrap[O, **P, T](
        fn: None = None,
        *,
        wrapper_fn: WrapperFunc[O, P, T] | None = None,
        attribute_setter: AttributeSetter[O, P, T] | None = None,
        wrapper_fn_args: tuple[Any, ...] | None = None,
        wrapper_fn_kwargs: dict[str, Any] | None = None,
        raw: bool = False,
    ) -> (
        Callable[
            [MethodTypes.RAW_METHOD[O, P, T]],
            MethodWrapper[O, P, T, MethodTypes.RAW_METHOD[O, P, T] | T],
        ]
        | Callable[
            [MethodTypes.METHOD[O, P, T]],
            MethodWrapper[
                O,
                P,
                T,
                MethodTypes.RAW_METHOD[O, P, T] | MethodTypes.METHOD[O, P, T] | T,
            ],
        ]
    ):
        """Overload: Decorator factory with wrapper_fn when raw is a general bool."""

    # Note: mypy is unable to distinguish between MethodTypes.RAW_METHOD and
    # MethodTypes.METHOD in the overloads, so we need to use type; pyright
    # successfully typechecks these overloads.

    # Overloads for specific method types to infer the descriptor return type
    @overload
    @staticmethod
    def wrap[O, **P, T](
        fn: MethodTypes.CLASSMETHOD[O, P, T],
        *,
        wrapper_fn: WrapperFunc[O, P, T] | None = None,
        attribute_setter: AttributeSetter[O, P, T] | None = None,
        wrapper_fn_args: tuple[Any, ...] | None = None,
        wrapper_fn_kwargs: dict[str, Any] | None = None,
        raw: Literal[False] = False,
    ) -> MethodWrapper[O, P, T, MethodTypes.RAW_CLASSMETHOD[O, P, T]]:
        """Overload: classmethod -> returns RAW_CLASSMETHOD from __get__."""

    @overload
    @staticmethod
    def wrap[**P, T](
        fn: MethodTypes.STATICMETHOD[P, T],
        *,
        wrapper_fn: WrapperFunc[Any, P, T] | None = None,
        attribute_setter: AttributeSetter[Any, P, T] | None = None,
        wrapper_fn_args: tuple[Any, ...] | None = None,
        wrapper_fn_kwargs: dict[str, Any] | None = None,
        raw: Literal[False] = False,
    ) -> MethodWrapper[Any, P, T, MethodTypes.RAW_STATICMETHOD[P, T]]:
        """Overload: staticmethod -> returns RAW_STATICMETHOD from __get__."""

    @overload
    @staticmethod
    def wrap[O, **P, T](
        fn: MethodTypes.BOUNDMETHOD[O, P, T],
        *,
        wrapper_fn: WrapperFunc[O, P, T] | None = None,
        attribute_setter: AttributeSetter[O, P, T] | None = None,
        wrapper_fn_args: tuple[Any, ...] | None = None,
        wrapper_fn_kwargs: dict[str, Any] | None = None,
        raw: Literal[False] = False,
    ) -> MethodWrapper[O, P, T, MethodTypes.RAW_BOUNDMETHOD[O, P, T]]:
        """Overload: bound method -> returns RAW_BOUNDMETHOD from __get__."""

    @overload
    @staticmethod
    def wrap[O, **P, T](
        fn: MethodTypes.PROPERTY,
        *,
        wrapper_fn: WrapperFunc[O, P, T] | None = None,
        attribute_setter: AttributeSetter[O, P, T] | None = None,
        wrapper_fn_args: tuple[Any, ...] | None = None,
        wrapper_fn_kwargs: dict[str, Any] | None = None,
        raw: Literal[False] = False,
    ) -> MethodWrapper[O, P, T, T]:
        """Overload: property -> returns T (property value) from __get__."""

    @overload
    @staticmethod
    def wrap[O, **P, T](
        fn: MethodTypes.RAW_METHOD[O, P, T],
        *,
        wrapper_fn: WrapperFunc[O, P, T] | None = None,
        attribute_setter: AttributeSetter[O, P, T] | None = None,
        wrapper_fn_args: tuple[Any, ...] | None = None,
        wrapper_fn_kwargs: dict[str, Any] | None = None,
        raw: Literal[True],
    ) -> MethodWrapper[O, P, T, MethodTypes.RAW_METHOD[O, P, T]]:
        """Overload: RAW_METHOD -> returns RAW_METHOD from __get__."""

    @overload
    @staticmethod
    def wrap[O, **P, T](
        fn: MethodTypes.METHOD[O, P, T],
        *,
        wrapper_fn: WrapperFunc[O, P, T] | None = None,
        attribute_setter: AttributeSetter[O, P, T] | None = None,
        wrapper_fn_args: tuple[Any, ...] | None = None,
        wrapper_fn_kwargs: dict[str, Any] | None = None,
        raw: Literal[False] = False,
    ) -> MethodWrapper[
        O,
        P,
        T,
        MethodTypes.RAW_METHOD[O, P, T] | MethodTypes.METHOD[O, P, T] | T,
    ]:
        """Overload: METHOD -> returns union of possible descriptor types from __get__."""

    @overload
    @staticmethod
    def wrap[O, **P, T](
        fn: MethodTypes.RAW_METHOD[O, P, T] | MethodTypes.METHOD[O, P, T] | None = None,
        *,
        wrapper_fn: WrapperFunc[O, P, T] | None = None,
        attribute_setter: AttributeSetter[O, P, T] | None = None,
        wrapper_fn_args: tuple[Any, ...] | None = None,
        wrapper_fn_kwargs: dict[str, Any] | None = None,
        raw: bool = False,
    ) -> (
        MethodWrapper[O, P, T, METH[O, P, T]]
        | Callable[
            [MethodTypes.RAW_METHOD[O, P, T]],
            MethodWrapper[O, P, T, MethodTypes.RAW_METHOD[O, P, T] | T],
        ]
        | Callable[
            [MethodTypes.METHOD[O, P, T]],
            MethodWrapper[
                O,
                P,
                T,
                MethodTypes.RAW_METHOD[O, P, T] | MethodTypes.METHOD[O, P, T] | T,
            ],
        ]
    ):
        """Overload: Direct call when fn and raw are unions/general types."""

    # Note: mypy is unable to distinguish between MethodTypes.RAW_METHOD and
    # MethodTypes.METHOD in the overloads, and this causes issues when typechecking
    # implementation; pyright successfully typechecks this.
    @staticmethod
    def wrap[O, **P, T](  # type: ignore[misc]
        fn: MethodTypes.RAW_METHOD[O, P, T] | MethodTypes.METHOD[O, P, T] | None = None,
        *,
        wrapper_fn: WrapperFunc[O, P, T] | None = None,
        attribute_setter: AttributeSetter[O, P, T] | None = None,
        wrapper_fn_args: tuple[Any, ...] | None = None,
        wrapper_fn_kwargs: dict[str, Any] | None = None,
        raw: bool | Literal[True] | Literal[False] = False,
    ) -> (
        MethodWrapper[O, P, T, METH[O, P, T]]
        | Callable[
            [MethodTypes.RAW_METHOD[O, P, T]],
            MethodWrapper[
                O,
                P,
                T,
                MethodTypes.RAW_METHOD[O, P, T] | T,
            ],
        ]
        | Callable[
            [MethodTypes.METHOD[O, P, T]],
            MethodWrapper[O, P, T, METH[O, P, T]],
        ]
    ):
        """Wrap a method with a wrapper function, preserving its type; optionally add attributes to the final descriptor.

        This method creates a MethodWrapper that can handle any method type
        (staticmethod, classmethod, bound method, property) uniformly while
        preserving type information for static type checkers.

        Can be used in three ways:
        1. Direct decoration: ``@MethodDecorator.wrap_method``
        2. Decorator factory: ``@MethodDecorator.wrap_method(wrapper_fn=...)`` or ``@MethodDecorator.wrap_method(attribute_setter=...)``
        3. Direct call: ``MethodDecorator.wrap_method(fn, wrapper_fn=...)`` or ``MethodDecorator.wrap_method(fn, attribute_setter=...)``

        Args:
            fn: The method to wrap (can be any METHOD type). If None, returns a decorator.
                When used as a decorator factory (fn=None), at least one of wrapper_fn or
                attribute_setter must be provided.
            wrapper_fn: Optional function that wraps the raw function (behavior modification).
                Signature: (raw_fn, descriptor_metadata, wrapper_args, wrapper_kwargs) -> wrapped_fn
                If not provided, the raw function is returned unchanged.
            attribute_setter: Optional function that adds attributes to the final descriptor.
                Signature: (final_descriptor, descriptor_metadata, wrapper_args, wrapper_kwargs) -> None
                This is called after the descriptor is reconstructed, so attributes are added to the
                final descriptor that will be returned.
            wrapper_fn_args: Positional arguments to pass to wrapper_fn and attribute_setter
            wrapper_fn_kwargs: Keyword arguments to pass to wrapper_fn and attribute_setter

        Returns:
            A wrapped method of the same type as the input, or a decorator function
            if `fn` is None.

        Example:
            >>> def logging_wrapper(fn, args, kwargs):
            ...     @wraps(fn)
            ...     def wrapped(*args, **kwargs):
            ...         print(f"Calling {fn.__name__}")
            ...         return fn(*args, **kwargs)
            ...     return wrapped
            ...
            >>> def add_attr(final_desc, metadata, args, kwargs):
            ...     object.__setattr__(final_desc, "__custom_attr", "value")
            ...
            >>> class MyClass:
            ...     @staticmethod
            ...     @MethodDecorator.wrap_method(wrapper_fn=logging_wrapper)
            ...     def static_method(x: int) -> int:
            ...         return x * 2
            ...
            ...     @classmethod
            ...     @MethodDecorator.wrap_method(attribute_setter=add_attr)
            ...     def class_method(cls) -> str:
            ...         return cls.__name__
            ...
            ...     @MethodDecorator.wrap_method(wrapper_fn=logging_wrapper)
            ...     def instance_method(self, x: int) -> int:
            ...         return x * 3
        """
        # If fn is None, we're being called as a decorator factory
        if fn is None:
            # For the decorator factory overload, at least one of wrapper_fn or attribute_setter
            # must be provided
            assert (
                wrapper_fn is not None or attribute_setter is not None
            ), "At least one of wrapper_fn or attribute_setter must be provided when fn is None"

            def decorator(
                method: MethodTypes.METHOD[O, P, T] | MethodTypes.RAW_METHOD[O, P, T],
            ) -> MethodWrapper[O, P, T, METH[O, P, T]]:
                # The descriptor type will be inferred by overloads based on the input type
                return MethodWrapper(
                    method,
                    wrapper_fn,
                    attribute_setter,
                    wrapper_fn_args,
                    wrapper_fn_kwargs,
                )

            return decorator

        # Otherwise, wrap the function directly
        # The descriptor type will be inferred by overloads based on the input type
        return MethodWrapper(
            fn, wrapper_fn, attribute_setter, wrapper_fn_args, wrapper_fn_kwargs
        )
