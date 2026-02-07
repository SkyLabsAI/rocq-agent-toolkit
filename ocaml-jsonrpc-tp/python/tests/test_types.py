import re
from collections.abc import Callable, Sequence

import pytest
from jsonrpc_tp.types import Err, Reply, Resp

# Note: tests are tightly coupled to the underlying implementation
# since we are patching dataclass to play nicely with covariant data,
# cf. https://github.com/microsoft/pyright/discussions/11012


class ReplyFixtures:
    type _mk_Reply[T] = Callable[[T], Reply[T]]
    type _mk_Err[T] = Callable[[str, T], Err[T]]
    type _mk_Resp[T] = Callable[[T], Resp[T]]

    @pytest.fixture(scope="session")
    @staticmethod
    def mk_Reply[T]() -> _mk_Reply[T]:
        return lambda data: Reply(data=data)

    @pytest.fixture(scope="session")
    @staticmethod
    def mk_Err[T]() -> _mk_Err[T]:
        return lambda message, data: Err(message=message, data=data)

    @pytest.fixture(scope="session")
    @staticmethod
    def mk_Resp[T]() -> _mk_Resp[T]:
        return lambda result: Resp(result=result)

    # Note: the rest of the fixtures use the default scope of function to
    # ensure that get fresh instances

    @pytest.fixture
    @staticmethod
    def Reply_None(mk_Reply: _mk_Reply[None]) -> Reply[None]:
        return mk_Reply(None)

    @pytest.fixture
    @staticmethod
    def Err_None(mk_Err: _mk_Err[None]) -> Err[None]:
        return mk_Err("", None)

    @pytest.fixture
    @staticmethod
    def Resp_None(mk_Resp: _mk_Resp[None]) -> Resp[None]:
        return mk_Resp(None)


class TestReplyErrResp(ReplyFixtures):
    @pytest.mark.parametrize(
        "reply_cls, expected_positional_args",
        [
            (Reply, ["data"]),
            (Err, ["message", "data"]),
            (Resp, ["result"]),
        ],
    )
    @staticmethod
    def test_required_positional_args(
        reply_cls: type[Reply],
        expected_positional_args: Sequence[str],
    ) -> None:
        with pytest.raises(TypeError) as exc_info:
            # Note: explicitly testing ctor call that misses arguments
            _reply = reply_cls()  # type: ignore
        pluralization = "s" if 1 < len(expected_positional_args) else ""
        assert exc_info.match(
            re.escape(
                " ".join(
                    [
                        f"{reply_cls.__qualname__}.__init__() missing",
                        f"{len(expected_positional_args)} required positional",
                        f"argument{pluralization}:",
                        " and ".join(
                            f"'{arg_nm}'" for arg_nm in expected_positional_args
                        ),
                    ]
                )
            )
        )

    def test_bool_Reply_not_implemented(self, Reply_None: Reply[None]) -> None:
        with pytest.raises(NotImplementedError):
            bool(Reply_None)

    def test_bool_Err(self, Err_None: Err[None]) -> None:
        assert not bool(Err_None)

    def test_bool_Resp(self, Resp_None: Resp[None]) -> None:
        assert bool(Resp_None)

    def test_eq_other_types(
        self,
        Reply_None: Reply[None],
        Err_None: Err[None],
        Resp_None: Resp[None],
    ) -> None:
        replies_None = [Reply_None, Err_None, Resp_None]

        class SomeCls:
            pass

        class MyReply(Reply[None]):
            pass

        for i in range(len(replies_None)):
            mk: object
            for mk in [None, "", 0, [], {}, set(), float(0), SomeCls()]:
                assert replies_None[i].__eq__(mk) is NotImplemented

            eq = replies_None[i].__eq__(MyReply(None))
            assert eq is not NotImplemented
            assert not eq

    def test_eq_None(
        self,
        Reply_None: Reply[None],
        Err_None: Err[None],
        Resp_None: Resp[None],
    ) -> None:
        replies_None = [Reply_None, Err_None, Resp_None]

        for i in range(len(replies_None)):
            for j in range(len(replies_None)):
                a = replies_None[i]
                b = replies_None[j]
                a_eq_b = a.__eq__(b)
                b_eq_a = b.__eq__(a)

                assert a_eq_b is not NotImplemented
                assert b_eq_a is not NotImplemented
                assert isinstance(a_eq_b, bool)
                assert isinstance(b_eq_a, bool)

                if i == j:
                    assert a_eq_b and b_eq_a
                else:
                    assert not (a_eq_b or b_eq_a)

    def test_eq_Err_messages(self, mk_Err: ReplyFixtures._mk_Err[None]) -> None:
        strs = ["", "Foo", "Bar", "Baz", "Qux"]
        for i in range(len(strs)):
            for j in range(len(strs)):
                if i == j:
                    assert mk_Err(strs[i], None) == mk_Err(strs[j], None)
                else:
                    assert mk_Err(strs[i], None) != mk_Err(strs[j], None)

    def test_repr_roundtrip_None(self) -> None:
        # Note: we could use `eval`, but we avoid it since it introduces a
        # potential security hole.
        _test_reply = Reply(data=None)
        reply_repr = "Reply(data=None)"
        assert repr(_test_reply) == reply_repr

        _test_err = Err(message="", data=None)
        err_repr = "Err(message='', data=None)"
        assert repr(_test_err) == err_repr

        _test_resp = Resp(result=None)
        resp_repr = "Resp(result=None)"
        assert repr(_test_resp) == resp_repr

    def test_covariant_Reply(
        self,
        mk_Reply: ReplyFixtures._mk_Reply,
    ) -> None:
        r1: Reply[None] = mk_Reply(None)
        r2: Reply[str] = mk_Reply("FooBar")
        r3: Reply[Exception] = mk_Reply(Exception())

        assert r1 != r2
        assert r1 != r3
        assert r2 != r3

        def rs() -> Sequence[Reply[None | str | Exception]]:
            return [r1, r2, r3]

        _r: Reply[None | str | Exception]
        for r in rs():
            _r = r
            assert _r == r
