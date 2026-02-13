from jsonrpc_tp import Error
from jsonrpc_tp import JsonRPCTP as API


def test_bad_command_true():
    try:
        _ = API(["true"])
        raise AssertionError()
    except Error as e:
        assert e.stderr is None


def test_bad_command_false():
    try:
        _ = API(["false"])
        raise AssertionError()
    except Error as e:
        assert e.stderr is None


def test_bad_command_grep():
    try:
        _ = API(["grep"])
        raise AssertionError()
    except Error as e:
        assert e.stderr is not None
        assert e.stderr != ""


def test_bad_command_echo():
    try:
        _ = API(["echo", "Hello!"])
        raise AssertionError()
    except Error as e:
        assert e.stderr is None
