"""Utilities and types for uniform metaprogramming on methods of classes."""

# Note: this is generic and could potentially be distributed as a separate module.

from __future__ import annotations

import inspect
import logging
from collections.abc import Callable
from types import FunctionType, MethodType
from typing import Annotated, Concatenate, TypeIs

logger = logging.getLogger(__name__)

# TODO: investigate other libraries that we may be able to use, including:
# - wrapt: https://github.com/GrahamDumpleton/wrapt
# - https://github.com/micheles/decorator
#   + Note: based on reading the docs, this may not support our specific use case

# Python `def`s in classes are either bound methods or descriptors. The most
# common descriptors are:
# - property
# - staticmethod
# - classmethod
# and they are:
# 1. usually applied as decorators (i.e. `@property`, `@staticmethod`, `@classmethod`)
# 2. special-cased by static typecheckers like `mypy` and `pyright`

# The following list captures typing information; the part after ~= is the type of the
# underlying `Callable` that is invoked when calling (cf. Notes at the end of this
# comment block):
# - property: property
#   + get (default from `@property`):
#     * staticmethod[[], T]                 ~=   Callable[                           T]
#     * FunctionType (on CLS)               ~=   Callable[                [CLS],     T]
#   + set (from @my_prop.setter):
#     * staticmethod[[T], None]             ~=   Callable[                       T , None]
#     * FunctionType (on CLS)               ~=   Callable[                [CLS], T , None]
#   + del (from @my_prop.deleter):
#     * staticmethod[[], None]              ~=   Callable[                           None]
#     * FunctionType (on CLS)               ~=   Callable[                [CLS],     None]
# - staticmethod: staticmethod[P, T]        ~=   Callable[                       P , T]
# - classmethod:  classmethod[CLS, P, T]    ~=   Callable[Concatenate[type[CLS], P], T]
# - bound method:  FunctionType  (on CLS)   ~=   Callable[Concatenate[     CLS,  P], T]
#
# Notes:
# - since python 3.13, @classmethod and @property cannot be combined
# - Functions and methods https://docs.python.org/3/howto/descriptor.html#functions-and-methods
#   + __get__ & __call__ are the key methods for uniform dispatching of calls on both
#     methods and descriptors
# - Experiences writing the `wrapt` decorator library:
#   + https://github.com/GrahamDumpleton/wrapt?tab=readme-ov-file#related-blog-posts

# BEGIN helpers
#
# Note: we repeat `Callable[...]` in Annotated because we want to use it for
# the annotation, and as the raw underlying type; cf.
# https://docs.python.org/3/library/typing.html#typing.Annotated
type _AnnotatedCallableT[KIND, **P, T] = Annotated[
    Callable[P, T],
    KIND,
    Callable[P, T],
]
type _FuncT[**P, T] = _AnnotatedCallableT[FunctionType, P, T]
type _BoundFuncT[**P, T] = _AnnotatedCallableT[MethodType, P, T]
# END helpers

# BEGIN functions
type FuncInstancePropertyGetT[O, T] = _FuncT[[O], T]
type FuncStaticPropertyGetT[T] = _FuncT[[], T]
type FuncPropertyGetT[O, T] = (
    FuncInstancePropertyGetT[O, T] | FuncStaticPropertyGetT[T]
)
type FuncInstancePropertySetT[O, T] = _FuncT[[O, T], None]
type FuncStaticPropertySetT[T] = _FuncT[[T], None]
type FuncPropertySetT[O, T] = (
    FuncInstancePropertySetT[O, T] | FuncStaticPropertySetT[T]
)
type FuncInstancePropertyDelT[O] = _FuncT[[O], None]
type FuncStaticPropertyDelT = _FuncT[[], None]
type FuncPropertyDelT[O] = (FuncInstancePropertyDelT[O] | FuncStaticPropertyDelT)
type FuncStaticmethodT[**P, T] = _FuncT[P, T]
type FuncClassmethodT[O, **P, T] = _FuncT[Concatenate[type[O], P], T]
type FuncInstancemethodT[O, **P, T] = _FuncT[Concatenate[O, P], T]
type FuncT[O, **P, T] = (
    FuncPropertyGetT[O, T]
    | FuncPropertySetT[O, T]
    | FuncPropertyDelT[O]
    | FuncStaticmethodT[P, T]
    | FuncClassmethodT[O, P, T]
    | FuncInstancemethodT[O, P, T]
)
# BEGIN functions

# BEGIN bound methods
type BoundFuncInstancePropertyGetT[T] = _BoundFuncT[[], T]
type BoundFuncStaticPropertyGetT[T] = _BoundFuncT[[], T]
type BoundFuncPropertyGetT[O, T] = (
    BoundFuncInstancePropertyGetT[O, T] | BoundFuncStaticPropertyGetT[T]
)
type BoundFuncInstancePropertySetT[O, T] = _FuncT[[T], None]
type BoundFuncStaticPropertySetT[T] = _FuncT[[T], None]
type BoundFuncPropertySetT[O, T] = (
    BoundFuncInstancePropertySetT[O, T] | BoundFuncStaticPropertySetT[T]
)
type BoundFuncInstancePropertyDelT = _BoundFuncT[[], None]
type BoundFuncStaticPropertyDelT = _BoundFuncT[[], None]
type BoundFuncPropertyDelT = (
    BoundFuncInstancePropertyDelT | BoundFuncStaticPropertyDelT
)
type BoundFuncStaticmethodT[**P, T] = _BoundFuncT[P, T]
type BoundFuncClassmethodT[**P, T] = _BoundFuncT[P, T]
type BoundFuncInstancemethodT[**P, T] = _BoundFuncT[P, T]
type BoundFuncT[**P, T] = (
    FuncPropertyGetT[T]
    | FuncPropertySetT[T]
    | FuncPropertyDelT
    | FuncStaticmethodT[P, T]
    | FuncClassmethodT[P, T]
    | FuncInstancemethodT[P, T]
)
# BEGIN bound methods

# BEGIN methods & descriptors
#
# Note: `property` descriptors track the RAW_PROPERTY_XXXs in corresponding fget/fset/fdel
type PropertyT = property
type StaticmethodT[**P, T] = staticmethod[P, T]
type ClassmethodT[O, **P, T] = classmethod[O, P, T]
type InstancemethodT[O, **P, T] = FuncInstancemethodT[O, P, T]
type MethodT[O, **P, T] = (
    PropertyT | StaticmethodT[P, T] | ClassmethodT[O, P, T] | InstancemethodT[O, P, T]
)
# END methods & descriptors


# BEGIN type narrowing functions

# High-level narrowing functions


def is_method[O, **P, T](
    maybe_fn: MethodT[O, P, T] | FuncT[O, P, T],
    cls: type[O] | None = None,
) -> TypeIs[MethodT[O, P, T] | FuncT[O, P, T]]:
    """Check if maybe_fn is a method (wrapped or raw).

    This function checks if the input is any kind of method (staticmethod, classmethod,
    bound method, property) or raw function that could be a method.
    """
    if isinstance(maybe_fn, (staticmethod, classmethod, property)):
        # Descriptors are always methods
        return True
    elif isinstance(maybe_fn, FunctionType):
        # For FunctionType, check if it's in the class dict to confirm it's a method
        if cls is not None:
            for value in cls.__dict__.values():
                if value is maybe_fn:
                    return True
        # If no cls provided, assume FunctionType could be a method
        # (this is a best-effort approximation)
        return True
    else:
        return False


def is_staticmethod[O, **P, T](
    maybe_fn: MethodT[O, P, T] | FuncT[O, P, T],
    cls: type[O] | None = None,
) -> TypeIs[StaticmethodT[P, T]]:
    """Check if maybe_fn is a static method; narrow the type if it is.

    Works for both wrapped staticmethod descriptors and raw staticmethod functions.
    """
    # Check if it's a wrapped staticmethod descriptor
    if isinstance(maybe_fn, staticmethod):
        return True
    # For raw functions, check signature to see if it matches staticmethod pattern
    if isinstance(maybe_fn, FunctionType):
        try:
            sig = inspect.signature(maybe_fn)
            # Staticmethods don't have self/cls as first parameter
            # Check if first param is not self/cls-like
            params = list(sig.parameters.values())
            if params and params[0].name in ("self", "cls"):
                return False
            # Could be a staticmethod if it's in the class dict
            if cls is not None:
                for value in cls.__dict__.values():
                    if value is maybe_fn:
                        return True
        except (ValueError, TypeError):
            pass
    return False


def is_classmethod[O, **P, T](
    maybe_fn: MethodT[O, P, T] | FuncT[O, P, T],
    cls: type[O] | None = None,
) -> TypeIs[ClassmethodT[O, P, T]]:
    """Check if maybe_fn is a class method; narrow the type if it is.

    Works for both wrapped classmethod descriptors and raw classmethod functions.
    """
    # Check if it's a wrapped classmethod descriptor
    if isinstance(maybe_fn, classmethod):
        return True
    # For raw functions, check signature to see if it matches classmethod pattern
    if isinstance(maybe_fn, FunctionType):
        try:
            sig = inspect.signature(maybe_fn)
            params = list(sig.parameters.values())
            # Classmethods have cls as first parameter
            if params and params[0].name == "cls":
                if cls is not None:
                    for value in cls.__dict__.values():
                        if value is maybe_fn:
                            return True
        except (ValueError, TypeError):
            pass
    return False


def is_instancemethod[O, **P, T](
    maybe_fn: MethodT[O, P, T] | FuncT[O, P, T],
    cls: type[O] | None = None,
) -> TypeIs[InstancemethodT[O, P, T]]:
    """Check if maybe_fn is an instance method; narrow the type if it is."""
    if isinstance(maybe_fn, FunctionType):
        # Check if it's in the class dict and has self as first parameter
        if cls is not None:
            for value in cls.__dict__.values():
                if value is maybe_fn:
                    try:
                        sig = inspect.signature(maybe_fn)
                        params = list(sig.parameters.values())
                        # Instance methods have self as first parameter
                        if params and params[0].name == "self":
                            return True
                    except (ValueError, TypeError):
                        # If we can't inspect, assume it could be an instance method
                        return True
        # If no cls provided, check signature for self parameter
        try:
            sig = inspect.signature(maybe_fn)
            params = list(sig.parameters.values())
            if params and params[0].name == "self":
                return True
        except (ValueError, TypeError):
            pass
    return False


# Alias for backward compatibility
is_boundmethod = is_instancemethod


def is_property[O, **P, T](
    maybe_prop: MethodT[O, P, T] | FuncT[O, P, T],
    cls: type[O] | None = None,
) -> TypeIs[PropertyT]:
    """Check if maybe_prop is a property descriptor; narrow the type if it is.

    Works for wrapped property descriptors. Properties are always wrapped descriptors,
    not raw functions.
    """
    return isinstance(maybe_prop, property)


# Property narrowing functions


def is_property_get[O, T](
    maybe_prop: MethodT[O, ..., T] | FuncT[O, ..., T],
    cls: type[O] | None = None,
) -> TypeIs[PropertyT]:
    """Check if maybe_prop is a property with a getter; narrow the type if it is."""
    if not isinstance(maybe_prop, property):
        return False
    return maybe_prop.fget is not None


def is_property_set[O, T](
    maybe_prop: MethodT[O, ..., T] | FuncT[O, ..., T],
    cls: type[O] | None = None,
) -> TypeIs[PropertyT]:
    """Check if maybe_prop is a property with a setter; narrow the type if it is."""
    if not isinstance(maybe_prop, property):
        return False
    return maybe_prop.fset is not None


def is_property_del[O](
    maybe_prop: MethodT[O, ..., ...] | FuncT[O, ..., ...],
    cls: type[O] | None = None,
) -> TypeIs[PropertyT]:
    """Check if maybe_prop is a property with a deleter; narrow the type if it is."""
    if not isinstance(maybe_prop, property):
        return False
    return maybe_prop.fdel is not None


def is_instance_property_get[O, T](
    maybe_prop: MethodT[O, ..., T] | FuncT[O, ..., T],
    cls: type[O] | None = None,
) -> TypeIs[PropertyT]:
    """Check if maybe_prop is a property with an instance getter (not static); narrow the type if it is."""
    if not isinstance(maybe_prop, property):
        return False
    if maybe_prop.fget is None:
        return False
    # Instance property getters are FunctionType, not staticmethod
    return isinstance(maybe_prop.fget, FunctionType) and not isinstance(
        maybe_prop.fget, staticmethod
    )


def is_static_property_get[T](
    maybe_prop: MethodT[..., ..., T] | FuncT[..., ..., T],
    cls: type[...] | None = None,
) -> TypeIs[PropertyT]:
    """Check if maybe_prop is a property with a static getter; narrow the type if it is."""
    if not isinstance(maybe_prop, property):
        return False
    if maybe_prop.fget is None:
        return False
    return isinstance(maybe_prop.fget, staticmethod)


# Raw function narrowing functions


def is_func_staticmethod[**P, T](
    maybe_fn: MethodT[..., P, T] | FuncT[..., P, T],
    cls: type[...] | None = None,
) -> TypeIs[FuncStaticmethodT[P, T]]:
    """Check if maybe_fn is a raw staticmethod function; narrow the type if it is."""
    if not isinstance(maybe_fn, FunctionType):
        return False
    try:
        sig = inspect.signature(maybe_fn)
        params = list(sig.parameters.values())
        # Staticmethods don't have self/cls as first parameter
        if params and params[0].name in ("self", "cls"):
            return False
        # Check if it's in the class dict as a staticmethod
        if cls is not None:
            for name, value in cls.__dict__.items():
                if value is maybe_fn:
                    # Check if it's wrapped in a staticmethod descriptor
                    attr = getattr(cls, name, None)
                    if isinstance(attr, staticmethod):
                        return True
                    # Or check if there's a staticmethod wrapping it
                    if isinstance(value, staticmethod):
                        return True
                    # name is used for getattr above
                    _ = name
        return True
    except (ValueError, TypeError):
        return False


def is_func_classmethod[O, **P, T](
    maybe_fn: MethodT[O, P, T] | FuncT[O, P, T],
    cls: type[O] | None = None,
) -> TypeIs[FuncClassmethodT[O, P, T]]:
    """Check if maybe_fn is a raw classmethod function; narrow the type if it is."""
    if not isinstance(maybe_fn, FunctionType):
        return False
    try:
        sig = inspect.signature(maybe_fn)
        params = list(sig.parameters.values())
        # Classmethods have cls as first parameter
        if params and params[0].name == "cls":
            if cls is not None:
                for name, value in cls.__dict__.items():
                    if value is maybe_fn:
                        # Check if it's wrapped in a classmethod descriptor
                        attr = getattr(cls, name, None)
                        if isinstance(attr, classmethod):
                            return True
            return True
    except (ValueError, TypeError):
        pass
    return False


def is_func_instancemethod[O, **P, T](
    maybe_fn: MethodT[O, P, T] | FuncT[O, P, T],
    cls: type[O] | None = None,
) -> TypeIs[FuncInstancemethodT[O, P, T]]:
    """Check if maybe_fn is a raw instance method function; narrow the type if it is."""
    if not isinstance(maybe_fn, FunctionType):
        return False
    try:
        sig = inspect.signature(maybe_fn)
        params = list(sig.parameters.values())
        # Instance methods have self as first parameter
        if params and params[0].name == "self":
            if cls is not None:
                for value in cls.__dict__.values():
                    if value is maybe_fn:
                        return True
            return True
    except (ValueError, TypeError):
        pass
    return False


def is_func_property_get[O, T](
    maybe_fn: MethodT[O, ..., T] | FuncT[O, ..., T],
    cls: type[O] | None = None,
) -> TypeIs[FuncPropertyGetT[O, T]]:
    """Check if maybe_fn is a raw property getter function; narrow the type if it is."""
    if not isinstance(maybe_fn, FunctionType):
        return False
    try:
        sig = inspect.signature(maybe_fn)
        params = list(sig.parameters.values())
        # Property getters have 0 or 1 parameter (self for instance, none for static)
        if len(params) == 0:
            # Static property getter
            if cls is not None:
                for _name, value in cls.__dict__.items():
                    if value is maybe_fn or (
                        isinstance(value, property) and value.fget is maybe_fn
                    ):
                        return True
            return True
        elif len(params) == 1:
            # Instance property getter (has self)
            if params[0].name == "self":
                if cls is not None:
                    for _name, value in cls.__dict__.items():
                        if value is maybe_fn or (
                            isinstance(value, property) and value.fget is maybe_fn
                        ):
                            return True
                return True
    except (ValueError, TypeError):
        pass
    return False


def is_func_property_set[O, T](
    maybe_fn: MethodT[O, ..., T] | FuncT[O, ..., T],
    cls: type[O] | None = None,
) -> TypeIs[FuncPropertySetT[O, T]]:
    """Check if maybe_fn is a raw property setter function; narrow the type if it is."""
    if not isinstance(maybe_fn, FunctionType):
        return False
    try:
        sig = inspect.signature(maybe_fn)
        params = list(sig.parameters.values())
        # Property setters have 1 or 2 parameters (value for static, self+value for instance)
        if len(params) == 1:
            # Static property setter
            if cls is not None:
                for _name, value in cls.__dict__.items():
                    if isinstance(value, property) and value.fset is maybe_fn:
                        return True
            return True
        elif len(params) == 2:
            # Instance property setter (has self and value)
            if params[0].name == "self":
                if cls is not None:
                    for _name, value in cls.__dict__.items():
                        if isinstance(value, property) and value.fset is maybe_fn:
                            return True
                return True
    except (ValueError, TypeError):
        pass
    return False


def is_func_property_del[O](
    maybe_fn: MethodT[O, ..., ...] | FuncT[O, ..., ...],
    cls: type[O] | None = None,
) -> TypeIs[FuncPropertyDelT[O]]:
    """Check if maybe_fn is a raw property deleter function; narrow the type if it is."""
    if not isinstance(maybe_fn, FunctionType):
        return False
    try:
        sig = inspect.signature(maybe_fn)
        params = list(sig.parameters.values())
        # Property deleters have 0 or 1 parameter (none for static, self for instance)
        if len(params) == 0:
            # Static property deleter
            if cls is not None:
                for _name, value in cls.__dict__.items():
                    if isinstance(value, property) and value.fdel is maybe_fn:
                        return True
            return True
        elif len(params) == 1:
            # Instance property deleter (has self)
            if params[0].name == "self":
                if cls is not None:
                    for _name, value in cls.__dict__.items():
                        if isinstance(value, property) and value.fdel is maybe_fn:
                            return True
                return True
    except (ValueError, TypeError):
        pass
    return False


# END type narrowing functions
