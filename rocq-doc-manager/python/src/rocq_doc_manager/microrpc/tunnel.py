from __future__ import annotations

from collections.abc import Callable
from functools import wraps
from types import FunctionType
from typing import (
    Protocol,
    get_protocol_members,
    get_type_hints,
    is_protocol,
)

from pydantic import JsonValue


class _RPC(Protocol):
    """Internal protocol to document requirements on wrapped classes"""

    async def _rpc(self, method: str, params: JsonValue | None): ...


def _wrap_func(name, func):
    ty = get_type_hints(func)["return"]

    @wraps(func)
    async def wrapped(self, *args, **kwargs):
        return await self._rpc(ty, name, list(args), kwargs)

    return wrapped


# TODO: this should get moved closer to `ClassDispatcher`
def proxy_protocol(
    protocol, passthru: list[str] | None = None
) -> Callable[[type[_RPC]], type]:
    """A class decorator that implements the methods of a Protocol using the
    underlying RPC mechanism."""

    assert is_protocol(protocol)

    def wrap(cls):
        for fn in get_protocol_members(protocol):
            if hasattr(cls, fn):
                continue
            func = getattr(protocol, fn)
            if not isinstance(func, FunctionType):
                raise AssertionError
            if passthru is not None and fn in passthru:
                # passthru functions are not made remote.
                # These are necessary because we can not proxy higher-order functions
                setattr(cls, fn, getattr(protocol, fn))
            else:
                setattr(cls, fn, _wrap_func(fn, func))
        return type(cls.__name__, cls.__bases__, dict(cls.__dict__))

    return wrap
