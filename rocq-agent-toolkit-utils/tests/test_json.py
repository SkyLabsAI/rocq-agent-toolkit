import re
from collections.abc import Callable
from typing import Any

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
    deserialize_str: Callable[[str], T],
    deserialize_structured: Callable[[Any], T],
    **kwargs,
) -> None:
    assert data == deserialize_str(json.dumps(data, **kwargs))
    assert data == deserialize_structured(json.dumps(data, structured=True, **kwargs))


def test_BaseModel_roundtrip() -> None:
    _test_roundtrip(
        Foo(num=42, flag=True),
        deserialize_str=Foo.model_validate_json,
        deserialize_structured=Foo.model_validate,
    )


def test_Nested_roundtrip() -> None:
    _test_roundtrip(
        Nested(foo=Foo(num=42, flag=True)),
        deserialize_str=Nested.model_validate_json,
        deserialize_structured=Nested.model_validate,
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
        deserialize_str=json.loads,
        deserialize_structured=json.loads,
        sort_keys=True,
    )


def test_dumps_serialization_error():
    with pytest.raises(TypeError) as excinfo:
        json.dumps(test_dumps_serialization_error)
    assert re.search(
        "Serialization failure",
        str(excinfo.value),
    )
