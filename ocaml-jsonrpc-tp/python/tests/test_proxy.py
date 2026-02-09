import asyncio

from jsonrpc_tp import AsyncJsonRPCTP as API
from jsonrpc_tp import Process, Resp
from jsonrpc_tp.websocket_proxy import Handlers, ProxyBackend
from websockets import connect, serve


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
        async with serve(handler.handle, host="127.0.0.1", port=None) as server:
            port = server.sockets[0].getsockname()[1]
            async with connect(f"ws://172.0.0.1:{port}") as client:
                proxy = ProxyBackend(client)
                api = API(
                    proxy,
                    handle_notification=handle_notification,
                )
                api_ref = api

                messages = ["Bye!", "Coucou!", "Hello!", "Bye!"]

                responses = await asyncio.gather(
                    api.raw_request("echo", [2, messages[0]]),
                    api.raw_request("echo", [3, messages[1]]),
                    api.raw_request("echo", [1, messages[2]]),
                    api.raw_request("echo", [0, messages[3]]),
                )

                for i in range(4):
                    r = responses[i]
                    assert isinstance(r, Resp)
                    assert r.result == messages[i]

        await api.quit()
        assert n == 4

    asyncio.run(main())
