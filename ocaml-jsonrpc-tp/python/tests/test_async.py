import asyncio

from jsonrpc_tp import AsyncJsonRPCTP as API
from jsonrpc_tp import Resp


def test_trivial_shutdown():
    async def main():
        api = API(["dune", "exec", "jsonrpc-tp.test-api", "--", "4"])
        await api.start()
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

        api = API(
            ["dune", "exec", "jsonrpc-tp.test-api", "--", "4"],
            handle_notification=handle_notification,
        )
        api_ref = api
        await api.start()

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


def test_large_packets():
    async def main():
        n = 0

        api_ref = None

        async def handle_notification(method: str, params: dict) -> None:
            nonlocal n
            n += 1
            await api_ref.raw_notification("ok", [])

        api = API(
            ["dune", "exec", "jsonrpc-tp.test-api", "--", "4"],
            handle_notification=handle_notification,
        )
        api_ref = api
        await api.start()

        sizes = [1000000, 2000000, 4000000, 8000000]

        responses = await asyncio.gather(
            api.raw_request("yes", [sizes[0]]),
            api.raw_request("yes", [sizes[1]]),
            api.raw_request("yes", [sizes[2]]),
            api.raw_request("yes", [sizes[3]]),
        )

        for i in range(4):
            r = responses[i]
            assert isinstance(r, Resp)
            assert len(r.result) == sizes[i]

        await api.quit()
        assert n == 4

    asyncio.run(main())
