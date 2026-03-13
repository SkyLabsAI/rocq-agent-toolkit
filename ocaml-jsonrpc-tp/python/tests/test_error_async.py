import asyncio

from jsonrpc_tp import AsyncJsonRPCTP as API
from jsonrpc_tp import Error


def test_bad_command_true():
    async def main():
        try:
            api = API(["true"])
            await api.start()
            raise AssertionError()
        except Error as e:
            assert e.stderr is None

    asyncio.run(main())


def test_bad_command_false():
    async def main():
        try:
            api = API(["false"])
            await api.start()
            raise AssertionError()
        except Error as e:
            assert e.stderr is None

    asyncio.run(main())


def test_bad_command_grep():
    async def main():
        try:
            api = API(["grep"])
            await api.start()
            raise AssertionError()
        except Error as e:
            assert e.stderr is not None
            assert e.stderr != ""

    asyncio.run(main())


def test_bad_command_echo():
    async def main():
        try:
            api = API(["echo", "Hello!"])
            await api.start()
            raise AssertionError()
        except Error as e:
            assert e.stderr is None

    asyncio.run(main())
