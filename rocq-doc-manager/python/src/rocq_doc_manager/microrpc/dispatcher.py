import functools
import inspect
from collections.abc import Callable
from types import FunctionType, NoneType
from typing import (
    Any,
    Protocol,
    get_protocol_members,
    get_type_hints,
    is_protocol,
    override,
)

from pydantic import BaseModel, JsonValue, RootModel, TypeAdapter

from rocq_doc_manager.cursor.websocket import Encoder
from rocq_doc_manager.microrpc.deserialize import Decoder
from rocq_doc_manager.microrpc.protocol import get_protocol


class Dispatcher(Protocol):
    """Dispatchers capture a JSON-RPC-style protocol.
    They interpret methods given arguments and keyword arguments.
    """

    async def dispatch(
        self, method: str, params: JsonValue | None
    ) -> tuple[bool, JsonValue]: ...


class ClassDispatcher(Dispatcher):
    def __init__(
        self, target: object, *, whitelist: list[str], enc: Encoder, dec: Decoder
    ) -> None:
        super().__init__()
        self._encoder = enc
        self._decoder = dec
        self._target = target
        self._whitelist = whitelist

    @override
    async def dispatch(
        self, method: str, params: JsonValue | None
    ) -> tuple[bool, JsonValue]:
        if method not in self._whitelist:
            return (False, "Bad request")

        meth = getattr(self._target, method)
        # TODO: parse the arguments using the decoder
        args: list[Any] = []
        kwargs: dict[str, Any] = {}
        try:
            return (True, self._encoder.encode(meth(*args, **kwargs)))
        except Exception as err:
            return (False, self._encoder.encode(err))

    @staticmethod
    def by_rpc[**P, R](
        input: type[BaseModel] | None = None, output: type[RootModel] | None = None
    ) -> Callable[[Callable[P, R]], Callable[P, R]]:
        def go(func: Callable[P, R]) -> Callable[P, R]:
            arg_model: type[BaseModel]
            ret_model: type[RootModel]
            if input is None or output is None:
                arg_proto, ret_proto = get_protocol(func)
                arg_model = arg_proto if input is None else input
                ret_model = ret_proto if output is None else output
            else:
                arg_model = input
                ret_model = output

            assert hasattr(arg_model, "_args_kwargs")

            signature = inspect.signature(func)
            type_hints = get_type_hints(func)
            return_type: type[R] | None = type_hints.get("return")
            assert return_type is not None
            assert return_type is not Any
            adapter = TypeAdapter(return_type)

            def _prepare_payload(
                instance: Dispatcher, *args: P.args, **kwargs: P.kwargs
            ) -> tuple[str, str]:
                """Helper to bundle arguments into JSON."""
                bound_args = signature.bind(instance, *args, **kwargs)
                bound_args.apply_defaults()

                # Exclude 'self' from the RPC payload
                arguments = {
                    k: v for k, v in bound_args.arguments.items() if k != "self"
                }
                return func.__name__, RootModel(arguments).model_dump_json()

            # --- ASYNC WRAPPER ---
            if inspect.iscoroutinefunction(func):

                @functools.wraps(func)
                async def async_wrapper(
                    self: Dispatcher, *args: P.args, **kwargs: P.kwargs
                ) -> R:
                    method_name, json_payload = _prepare_payload(self, *args, **kwargs)

                    raw_response = await self.dispatch(method_name, json_payload)

                    if return_type is NoneType:
                        return  # type: ignore
                    else:
                        return adapter.validate_python(raw_response)

                return async_wrapper  # type: ignore
            else:
                # --- SYNC WRAPPER ---
                @functools.wraps(func)
                def sync_wrapper(
                    self: Dispatcher, *args: P.args, **kwargs: P.kwargs
                ) -> R:
                    method_name, json_payload = _prepare_payload(self, *args, **kwargs)

                    raw_response = self.dispatch(method_name, json_payload)

                    if return_type is NoneType:
                        return  # type: ignore
                    else:
                        return adapter.validate_python(raw_response)

                return sync_wrapper

        return go


class _RPC(Protocol):
    async def _rpc(
        self, method: str, params: dict[str, JsonValue] | None
    ) -> tuple[bool, JsonValue]: ...


def proxy_protocol(
    protocol, passthru: list[str] | None = None
) -> Callable[[type[_RPC]], type]:
    """A class decorator that implements the methods of a Protocol using the
    underlying RPC mechanism."""

    def _wrap_func(name, func):
        ty = get_type_hints(func)["return"]

        @functools.wraps(func)
        async def wrapped(self, *args, **kwargs):
            return await self._rpc(ty, name, list(args), kwargs)

        return wrapped

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


class NamespaceDispatcher(Dispatcher):
    """A NamespaceDispatcher serves many protocols over a single connection
    and uses methods of the form `namespace/method`.
    """

    _dispatchers: dict[str, Dispatcher]

    def __init__(
        self, dispatchers: dict[str, Dispatcher], *, default: Dispatcher | None = None
    ):
        """dispatchers is a mapping from namespace to the underlying Dispatcher."""
        self._dispatchers = dispatchers
        self._default = default

    @override
    async def dispatch(
        self, method: str, params: JsonValue | None
    ) -> tuple[bool, JsonValue]:
        ns_method = None
        try:
            [ns, ns_method] = method.split("/", 1)
            dispatcher: Dispatcher | None = self._dispatchers[ns]
        except ValueError:
            # Since this is communicated back to the caller, it may
            # not make sense to propagate e
            dispatcher = None
        except IndexError:
            dispatcher = None
        if dispatcher and ns_method:
            return await dispatcher.dispatch(ns_method, params)
        elif self._default:
            return await self._default.dispatch(method, params)
        return (False, f"Unsupported method: '{method}'")
