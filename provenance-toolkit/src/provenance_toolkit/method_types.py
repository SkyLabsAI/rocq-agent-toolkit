"""Utilities and types for uniform metaprogramming on methods of classes."""

# NOTE: this is generic and could potentially be distributed as a separate
# module.

from __future__ import annotations

import logging
from collections.abc import Callable
from types import FunctionType
from typing import (
    Annotated,  # for intersection of types, cf. MethodTypes.RAW_BOUNDMETHOD
    Any,
    Concatenate,
    TypeIs,
    final,
)

logger = logging.getLogger(__name__)


class MethodTypes:
    """Utilities and types for metaprogramming with methods of classes.

    Functionality is implemented in a best-effort way; underapproximations
    are either logged or raised as exception, depending on [strict: bool] args.
    """

    # Python `def`s in classes are one of:
    # 1. static: staticmethod[P, T]       ~=   Callable[                       P , T]
    # 2. class:  classmethod[CLS, P, T]   ~=   Callable[Concatenate[type[CLS], P], T]
    # 3. bound:  FunctionType  (on CLS)   ~=   Callable[Concatenate[     CLS,  P], T]
    #
    # The following `type`s are used to capture/propagate precise typing information
    # when building decorators (e.g. `Provenance.register`+`Provenance.extend{_as}`,
    # cf. __init__.py)
    type RAW_STATICMETHOD[**P, T] = Callable[P, T]
    type RAW_CLASSMETHOD[O, **P, T] = Callable[Concatenate[type[O], P], T]
    type RAW_BOUNDMETHOD[O, **P, T] = Annotated[
        Callable[Concatenate[O, P], T],
        FunctionType,
        # Note: we repeat `Callable[...]` because we want to use it for
        # the annotation, and as the raw underlying type.
        #
        # cf. https://docs.python.org/3/library/typing.html#typing.Annotated
        Callable[Concatenate[O, P], T],
    ]
    # Note: since python 3.13, @classmethod and @property cannot be combined
    #
    # cf. https://docs.python.org/3/library/functions.html#classmethod
    type RAW_PROPERTY[O, T] = (
        Annotated[
            Callable[[type[O]], T],
            FunctionType,
            # Note: we repeat `Callable[...]` because we want to use it for
            # the annotation, and as the raw underlying type.
            #
            # cf. https://docs.python.org/3/library/typing.html#typing.Annotated
            Callable[[type[O]], T],
        ] |
        Annotated[
            Callable[[O], T],
            FunctionType,
            # Note: we repeat `Callable[...]` because we want to use it for
            # the annotation, and as the raw underlying type.
            #
            # cf. https://docs.python.org/3/library/typing.html#typing.Annotated
            Callable[[O], T],
        ]
    )
    type RAW_METHOD[O, **P, T] = (
        MethodTypes.RAW_STATICMETHOD[P, T]
        | MethodTypes.RAW_CLASSMETHOD[O, P, T]
        | MethodTypes.RAW_BOUNDMETHOD[O, P, T]
        | MethodTypes.RAW_PROPERTY[O, T]
    )
    type STATICMETHOD[**P, T] = staticmethod[P, T]
    type CLASSMETHOD[O, **P, T] = classmethod[O, P, T]
    type BOUNDMETHOD[O, **P, T] = MethodTypes.RAW_BOUNDMETHOD[O, P, T]
    type PROPERTY = property
    # Note: FunctionType doesn't support generic type annotations, but typecheckers
    # like mypy are smart enough to coerce a `FunctionType` to `RAW_BOUNDMETHOD` if
    # the types actually line up.
    type METHOD[O, **P, T] = (
        MethodTypes.STATICMETHOD[P, T]
        | MethodTypes.CLASSMETHOD[O, P, T]
        | MethodTypes.RAW_BOUNDMETHOD[O, P, T]
        | MethodTypes.PROPERTY
    )

    @final
    @staticmethod
    def is_staticmethod[O, **P, T](
        maybe_fn: METHOD[O, P, T],
        cls: type[O] | None = None,
    ) -> TypeIs[STATICMETHOD[P, T]]:
        """Check if maybe_fn is a static method; narrow the type if it is."""
        if MethodTypes.is_method(maybe_fn, cls=cls):
            return False
        elif not isinstance(maybe_fn, staticmethod):
            return False
        else:
            return True

    @final
    @staticmethod
    def is_classmethod[O, **P, T](
        maybe_fn: METHOD[O, P, T],
        cls: type[O] | None = None,
    ) -> TypeIs[CLASSMETHOD[O, P, T]]:
        """Check if maybe_fn is a class method; narrow the type if it is."""
        if not MethodTypes.is_method(maybe_fn, cls=cls):
            return False
        elif not isinstance(maybe_fn, classmethod):
            return False
        else:
            return True

    @final
    @staticmethod
    def is_boundmethod[O, **P, T](
        maybe_fn: METHOD[O, P, T],
        cls: type[O] | None = None,
    ) -> TypeIs[BOUNDMETHOD[O, P, T]]:
        """Check if maybe_fn is a bound method; narrow the type if it is."""
        if not MethodTypes.is_method(maybe_fn, cls=cls):
            return False
        elif not isinstance(maybe_fn, FunctionType):
            return False
        else:
            return True

    @final
    @staticmethod
    def is_property[O, T](
        maybe_prop: Any,
        cls: type[O] | None = None,
    ) -> TypeIs[property]:
        """Check if maybe_prop is a property descriptor; narrow the type if it is."""
        if not MethodTypes.is_method(maybe_prop, cls=cls):
            return False
        elif not isinstance(maybe_prop, property):
            return False
        else:
            return True

    @final
    @staticmethod
    def is_method[O, **P, T](
        maybe_fn: METHOD[O, P, T],
        cls: type[O] | None = None,
    ) -> TypeIs[METHOD[O, P, T]]:
        """Check if maybe_fn is a method."""
        if not isinstance(maybe_fn, (staticmethod, classmethod, FunctionType, property)):
            return False

        def __log_skip_check_return_true(msg: str) -> bool:
            """Log a message and return True."""
            logger.info(
                "MethodTypes.is_method returned True w/out check (%s): %s",
                maybe_fn,
                msg,
            )
            return True

        if cls is None:
            return __log_skip_check_return_true("no supplied cls type")
        else:
            for value in cls.__dict__.values():
                if value is maybe_fn:
                    return True

            return False
