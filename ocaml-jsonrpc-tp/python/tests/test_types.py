import pytest
from jsonrpc_tp.types import Err, Resp


def mk_Err_covariant(b: bool) -> Err[int | float]:
    if b:
        return Err(message="", data=42)
    else:
        return Err(message="", data=3.1415)


def mk_Err_covariant_composition(b1: bool, b2: bool) -> Err[int | float | str]:
    if b1:
        return Err(message="", data="euler's constant")
    else:
        return mk_Err_covariant(b2)


def mk_Resp_covariant(b: bool) -> Resp[int | float]:
    if b:
        return Resp(result=42)
    else:
        return Resp(result=3.1415)


def mk_Resp_covariant_composition(b1: bool, b2: bool) -> Resp[int | float | str]:
    if b1:
        return Resp(result="euler's constant")
    else:
        return mk_Resp_covariant(b2)


@pytest.mark.parametrize("b1", [True, False])
@pytest.mark.parametrize("b2", [True, False])
def test_covariance_ok(b1: bool, b2: bool) -> None:
    assert isinstance(mk_Err_covariant_composition(b1, b2), Err)
    assert isinstance(mk_Resp_covariant_composition(b1, b2), Resp)
