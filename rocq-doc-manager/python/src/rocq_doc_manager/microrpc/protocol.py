"""
This file defines the wire-level protocols that are used in
in microrpc services.
"""

import inspect
from collections.abc import Callable, Sequence
from typing import Any, Protocol, get_type_hints, runtime_checkable

from pydantic import BaseModel, RootModel, create_model


class ObjectId(BaseModel):
    id: int


@runtime_checkable
class AsArguments(Protocol):
    def as_args(self) -> tuple[Sequence[Any], dict[str, Any]]:
        """Returns the positional and keyword arguments for this member"""
        ...


def get_protocol(func: Callable) -> tuple[type[BaseModel], type[RootModel]]:
    """
    Returns a pair of (ArgumentModel, ReturnModel) for the given function.
    """
    # 1. Resolve all type hints
    type_hints = get_type_hints(
        func, globalns=getattr(func, "__globals__", {}), include_extras=True
    )

    # 2. Construct Argument Model
    sig = inspect.signature(func)
    arg_fields: dict[str, Any] = {}

    position = 0
    args = []
    kwargs = {}
    for name, param in sig.parameters.items():
        if name == "self":
            arg_fields["self"] = (ObjectId, ...)
            args = ["self"]
            continue

        annotation = type_hints.get(name)
        if annotation is None:
            raise ValueError(f"Missing type annotation on {func.__name__}/{name}")
        if annotation is Any:
            raise ValueError(
                f"Protocols do not support `Any` on {func.__name__}/{name}"
            )
        if param.kind == inspect._ParameterKind.POSITIONAL_ONLY:
            name = f"_arg_{position}"
            args.append(name)
            position += 1
        else:
            kwargs[name] = name
        if param.default is inspect.Parameter.empty:
            arg_fields[name] = (annotation, ...)
        else:
            arg_fields[name] = (annotation, param.default)

    ArgModel = create_model(f"{func.__name__}_Args", **arg_fields)

    def as_args(self) -> tuple[Sequence[Any], dict[str, Any]]:
        nonlocal args
        nonlocal kwargs
        my_args = [getattr(self, x) for x in self._args]
        my_kwargs = {key: getattr(self, val) for key, val in self._kwargs.items()}
        return (my_args, my_kwargs)

    ArgModel.as_args = as_args

    # 3. Construct Return Model
    # We use RootModel so we can validate return types like list[int] or dict[str, str]
    return_hint = type_hints.get("return")
    if return_hint is None:
        raise ValueError(f"Missing return type annotation on {func.__name__}")
    if return_hint is Any:
        raise ValueError(f"Protocols do not support `Any` on {func.__name__}")

    # We create a specific subclass of RootModel for this function's return type
    RetModel = create_model(
        f"{func.__name__}_Result",
        __base__=RootModel[return_hint],  # type: ignore
    )

    # 4. Return
    return (ArgModel, RetModel)
