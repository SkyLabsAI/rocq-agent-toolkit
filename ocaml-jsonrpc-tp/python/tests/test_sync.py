from jsonrpc_tp import JsonRPCTP as API
from jsonrpc_tp import Resp


def test_trivial_shutdown():
    api = API(["dune", "exec", "jsonrpc-tp.test-api"])
    api.quit()


def test_echo():
    n = 0

    api_ref = None

    def handle_notification(method: str, params: dict) -> None:
        nonlocal n
        n += 1
        api_ref.raw_notification("ok", [])

    api = API(["dune", "exec", "jsonrpc-tp.test-api"])
    api_ref = api

    messages = ["Bye!", "Coucou!", "Hello!", "Bye!"]

    responses = [
        api.raw_request(
            "echo", [0, messages[0]], handle_notification=handle_notification
        ),
        api.raw_request(
            "echo", [1, messages[1]], handle_notification=handle_notification
        ),
        api.raw_request(
            "echo", [1, messages[2]], handle_notification=handle_notification
        ),
        api.raw_request(
            "echo", [0, messages[3]], handle_notification=handle_notification
        ),
    ]

    for i in range(4):
        r = responses[i]
        assert isinstance(r, Resp)
        assert r.result == messages[i]

    api.quit()
    assert n == 4


def test_large_packets():
    n = 0

    api_ref = None

    def handle_notification(method: str, params: dict) -> None:
        nonlocal n
        n += 1
        api_ref.raw_notification("ok", [])

    api = API(["dune", "exec", "jsonrpc-tp.test-api"])
    api_ref = api

    sizes = [1000000, 2000000, 4000000, 8000000]

    responses = [
        api.raw_request("yes", [sizes[0]], handle_notification=handle_notification),
        api.raw_request("yes", [sizes[1]], handle_notification=handle_notification),
        api.raw_request("yes", [sizes[2]], handle_notification=handle_notification),
        api.raw_request("yes", [sizes[3]], handle_notification=handle_notification),
    ]

    for i in range(4):
        r = responses[i]
        assert isinstance(r, Resp)
        assert len(r.result) == sizes[i]

    api.quit()
    assert n == 4
