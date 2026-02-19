from typing import Any, Protocol, override


class Dispatcher(Protocol):
    """Dispatchers capture a JSON-RPC-style protocol.
    They interpret methods given arguments and keyword arguments.
    """

    async def dispatch(
        self, method: str, args: list[Any], kwargs: dict[str, Any]
    ) -> Any:
        pass


class NamespaceDispatcher(Dispatcher):
    """A NamespaceDispatcher serves many protocols over a single connection
    and uses methods of the form `namespace/method`.
    """

    _dispatchers: dict[str, Dispatcher]

    def __init__(self, dispatchers: dict[str, Dispatcher]):
        """dispatchers is a mapping from namespace to the underlying Dispatcher."""
        self._dispatchers = dispatchers

    @override
    async def dispatch(
        self, method: str, args: list[Any], kwargs: dict[str, Any]
    ) -> Any:
        try:
            [ns, ns_method] = method.split("/", 1)
        except ValueError as e:
            # Since this is communicated back to the caller, it may
            # not make sense to propagate e
            raise ValueError(f"Unsupported method: '{method}'") from e
        if ns in self._dispatchers:
            return await self._dispatchers[ns].dispatch(ns_method, args, kwargs)
