import asyncio

from jsonrpc_tp import AsyncJsonRPCTP as API
from jsonrpc_tp import Process
from jsonrpc_tp.websocket_proxy import Handlers, ProxyBackend
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

        process = await Process.start(
            ["dune", "exec", "jsonrpc-tp.delayed-echo-api", "--", "4"]
        )
        handler = Handlers(process)
        async with await serve(handler.handle, host="127.0.0.1", port=None) as server:
            host = server.sockets[0].getsockname()[0]
            port = server.sockets[0].getsockname()[1]
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
