from jsonrpc_tp import JsonRPCTP as API
from jsonrpc_tp import Resp


def test_unicode():
    n = 0

    api_ref = None

    def handle_notification(method: str, params: dict) -> None:
        nonlocal n
        n += 1
        api_ref.raw_notification("ok", ["😊😊😊"])

    api = API(["dune", "exec", "jsonrpc-tp.test-api"])
    api_ref = api

    huge_length = 1000000
    huge = "😊" * huge_length
    assert len(huge.encode()) == 4 * huge_length
    messages = ["😊", "€€", huge] * 50

    responses = [
        api.raw_request("echo", [0, m], handle_notification=handle_notification)
        for m in messages
    ]

    for i in range(len(messages)):
        r = responses[i]
        assert isinstance(r, Resp)
        assert r.result == messages[i]

    api.quit()
    assert n == len(messages)
