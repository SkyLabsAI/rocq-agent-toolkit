from collections.abc import Callable
from contextlib import nullcontext as does_not_raise

import pytest
import rocq_agent_toolkit_utils.json as json
from pydantic import BaseModel


class Foo(BaseModel):
    num: int
    flag: bool


class Nested(BaseModel):
    foo: Foo


def _test_roundtrip[T](
    data: T,
    *,
    deserialize: Callable[[str], T],
    **kwargs,
) -> None:
    json_str = json.dumps(data, **kwargs)
    assert json_str != json.dumps(json_str, **kwargs)
    assert data == deserialize(json_str)


def test_BaseModel_roundtrip() -> None:
    _test_roundtrip(
        Foo(num=42, flag=True),
        deserialize=Foo.model_validate_json,
    )


def test_Nested_roundtrip() -> None:
    _test_roundtrip(
        Nested(foo=Foo(num=42, flag=True)),
        deserialize=Nested.model_validate_json,
    )


def test_dict_roundtrip() -> None:
    _test_roundtrip(
        {
            "foo": "bar",
            "baz": 42,
            "qux": {
                "zobs": [
                    42,
                    314,
                    271828,
                ],
            },
            "range": list(range(10)),
        },
        deserialize=json.loads,
        sort_keys=True,
    )


@pytest.mark.parametrize(
    "test_ctx, o",
    [
        (does_not_raise(), 42),
        (does_not_raise(), Foo(num=42, flag=True)),
        (does_not_raise(), Nested(foo=Foo(num=314, flag=False))),
        (pytest.raises(TypeError), lambda _: False),
        (pytest.raises(TypeError), int),
        (pytest.raises(TypeError), Exception),
        (pytest.raises(TypeError), Exception()),
        (pytest.raises(TypeError), Foo),
        (pytest.raises(TypeError), Nested),
    ],
)
def test_dumps_raises(test_ctx, o):
    with test_ctx:
        json.dumps(o)
