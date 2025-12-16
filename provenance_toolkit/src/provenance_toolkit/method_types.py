"""Utilities and types for uniform metaprogramming on methods of classes."""

# NOTE: this is generic and could potentially be distributed as a separate
# module.

import logging
from collections.abc import Callable
from types import FunctionType
from typing import (
    Annotated,  # for intersection of types, cf. MethodTypes.RAW_BOUNDMETHOD
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
    type RAW_METHOD[O, **P, T] = (
        MethodTypes.RAW_STATICMETHOD[P, T]
        | MethodTypes.RAW_CLASSMETHOD[O, P, T]
        | MethodTypes.RAW_BOUNDMETHOD[O, P, T]
    )
    type STATICMETHOD[**P, T] = staticmethod[P, T]
    type CLASSMETHOD[O, **P, T] = classmethod[O, P, T]
    type BOUNDMETHOD[O, **P, T] = MethodTypes.RAW_BOUNDMETHOD[O, P, T]
    # Note: FunctionType doesn't support generic type annotations, but typecheckers
    # like mypy are smart enough to coerce a `FunctionType` to `RAW_BOUNDMETHOD` if
    # the types actually line up.
    type METHOD[O, **P, T] = (
        MethodTypes.STATICMETHOD[P, T]
        | MethodTypes.CLASSMETHOD[O, P, T]
        | MethodTypes.RAW_BOUNDMETHOD[O, P, T]
    )

    @final
    @staticmethod
    def is_staticmethod[O, **P, T](
        maybe_fn: METHOD[O, P, T],
        cls: type[O] | None = None,
    ) -> TypeIs[STATICMETHOD[P, T]]:
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
        if not MethodTypes.is_method(maybe_fn, cls=cls):
            return False
        elif not isinstance(maybe_fn, FunctionType):
            return False
        else:
            return True

    @final
    @staticmethod
    def is_method[O, **P, T](
        maybe_fn: METHOD[O, P, T],
        cls: type[O] | None = None,
    ) -> TypeIs[METHOD[O, P, T]]:
        if not isinstance(maybe_fn, (staticmethod, classmethod, FunctionType)):
            return False

        def __log_skip_check_return_True(msg: str) -> None:
            logger.info(
                f"MethodTypes.is_method returned True w/out check ({maybe_fn}): {msg}"
            )

        if cls is None:
            __log_skip_check_return_True("no supplied cls type")
            return True
        else:
            for value in cls.__dict__.values():
                if value is maybe_fn:
                    return True

            return False
