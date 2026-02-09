import asyncio

from jsonrpc_tp import AsyncJsonRPCTP as API
from jsonrpc_tp import Process, Resp


def test_trivial_shutdown():
    async def main():
        backend = await Process.start(
            ["dune", "exec", "jsonrpc-tp.delayed-echo-api", "--", "4"]
        )
        api = API(backend)
        await api.quit()

    asyncio.run(main())


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

        api = API(
            backend,
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
