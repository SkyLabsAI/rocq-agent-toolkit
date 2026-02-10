import re
from collections.abc import Callable, Sequence

import pytest
from jsonrpc_tp import Err, Resp

# Note: tests are tightly coupled to the underlying implementation
# since we are patching dataclass to play nicely with covariant data,
# cf. https://github.com/microsoft/pyright/discussions/11012


class ReplyFixtures:
    type _mk_Err[T] = Callable[[str, T], Err[T]]
    type _mk_Resp[T] = Callable[[T], Resp[T]]

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
    def Err_None(mk_Err: _mk_Err[None]) -> Err[None]:
        return mk_Err("", None)

    @pytest.fixture
    @staticmethod
    def Resp_None(mk_Resp: _mk_Resp[None]) -> Resp[None]:
        return mk_Resp(None)


class TestErrResp(ReplyFixtures):
    @pytest.mark.parametrize(
        "reply_cls, expected_positional_args",
        [
            (Err, ["message", "data"]),
            (Resp, ["result"]),
        ],
    )
    @staticmethod
    def test_required_positional_args(
        reply_cls: type[Err[object]] | type[Resp[object]],
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

    def test_bool_Err(self, Err_None: Err[None]) -> None:
        assert not bool(Err_None)

    def test_bool_Resp(self, Resp_None: Resp[None]) -> None:
        assert bool(Resp_None)

    def test_eq_other_types(
        self,
        Err_None: Err[None],
        Resp_None: Resp[None],
    ) -> None:
        replies_None = [Err_None, Resp_None]

        class SomeCls:
            pass

        class MyErr(Err[None]):
            pass

        class MyResp(Resp[None]):
            pass

        for i in range(len(replies_None)):
            mk: object
            for mk in [None, "", 0, [], {}, set(), float(0), SomeCls()]:
                assert replies_None[i].__eq__(mk) is NotImplemented

            # Test with subclass of the same type
            if isinstance(replies_None[i], Err):
                eq = replies_None[i].__eq__(MyErr("", None))
            else:
                eq = replies_None[i].__eq__(MyResp(None))
            assert eq is not NotImplemented
            assert not eq

    def test_eq_None(
        self,
        Err_None: Err[None],
        Resp_None: Resp[None],
    ) -> None:
        replies_None = [Err_None, Resp_None]

        for i in range(len(replies_None)):
            for j in range(len(replies_None)):
                a = replies_None[i]
                b = replies_None[j]
                a_eq_b = a.__eq__(b)
                b_eq_a = b.__eq__(a)

                if i == j:
                    assert a_eq_b is not NotImplemented
                    assert b_eq_a is not NotImplemented
                    assert isinstance(a_eq_b, bool)
                    assert isinstance(b_eq_a, bool)
                    assert a_eq_b and b_eq_a
                else:
                    assert a_eq_b is NotImplemented
                    assert b_eq_a is NotImplemented
                    assert not (a == b or b == a)

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
        _test_err = Err(message="", data=None)
        err_repr = "Err(message='', data=None)"
        assert repr(_test_err) == err_repr

        _test_resp = Resp(result=None)
        resp_repr = "Resp(result=None)"
        assert repr(_test_resp) == resp_repr

    def test_covariant_Err(
        self,
        mk_Err: ReplyFixtures._mk_Err,
    ) -> None:
        e1: Err[None] = mk_Err("", None)
        e2: Err[str] = mk_Err("", "FooBar")
        e3: Err[Exception] = mk_Err("", Exception())

        assert e1 != e2
        assert e1 != e3
        assert e2 != e3

        def es() -> Sequence[Err[None | str | Exception]]:
            return [e1, e2, e3]

        _e: Err[None | str | Exception]
        for e in es():
            _e = e
            assert _e == e

    def test_covariant_Resp(
        self,
        mk_Resp: ReplyFixtures._mk_Resp,
    ) -> None:
        r1: Resp[None] = mk_Resp(None)
        r2: Resp[str] = mk_Resp("FooBar")
        r3: Resp[Exception] = mk_Resp(Exception())

        assert r1 != r2
        assert r1 != r3
        assert r2 != r3

        def rs() -> Sequence[Resp[None | str | Exception]]:
            return [r1, r2, r3]

        _r: Resp[None | str | Exception]
        for r in rs():
            _r = r
            assert _r == r
