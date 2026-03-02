from typing import Any, Protocol, override

from rocq_doc_manager.microrpc.deserialize import Decoder
from rocq_doc_manager.microrpc.duplex import JsonValue
from rocq_doc_manager.rocq_cursor_websocket import Encoder


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
