import asyncio

from jsonrpc_tp import AsyncJsonRPCTP as API
from jsonrpc_tp import Process
from jsonrpc_tp.websocket_proxy import ProxyBackend, WebsocketToBackend
from websockets import connect, serve

from .test_async import echo_test_helper


def test_echo():
    async def main():
        n = 0

        api_ref = None

        async def handle_notification(method: str, params: dict) -> None:
            nonlocal n
            n += 1
            await api_ref.raw_notification("ok", [])

        backend = await Process.start(
            ["dune", "exec", "jsonrpc-tp.delayed-echo-api", "--", "4"]
        )
        async with serve(
            WebsocketToBackend.make_handler(backend), host="127.0.0.1", port=None
        ) as server:
            (host, port) = server.sockets[0].getsockname()
            async with connect(f"ws://{host}:{port}") as client:
                proxy = ProxyBackend(client)
                api = API(
                    proxy,
                    handle_notification=handle_notification,
                )
                api_ref = api

                await echo_test_helper(api)

                await api.quit()
                assert n == 4

    asyncio.run(main())


def test_echo_dual():
    async def main():
        n = 0

        async def handle(conn):
            api_ref = None

            async def handle_notification(method: str, params: dict) -> None:
                nonlocal n
                n += 1
                await api_ref.raw_notification("ok", [])

            proxy = ProxyBackend(conn)
            api = API(
                proxy,
                handle_notification=handle_notification,
            )
            api_ref = api

            await echo_test_helper(api)

            await api.quit()

        backend = await Process.start(
            ["dune", "exec", "jsonrpc-tp.delayed-echo-api", "--", "4"]
        )

        async with serve(handle, host="127.0.0.1", port=None) as server:
            (host, port) = server.sockets[0].getsockname()
            async with connect(f"ws://{host}:{port}") as client:
                server = WebsocketToBackend(backend, client)
                await server.loop()

    asyncio.run(main())
