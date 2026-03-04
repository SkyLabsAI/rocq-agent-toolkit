"""Re-expose the builtin `json` module with a more robust/opinionated default for dumps.

This module is meant to be used instead of the builtin json module:
```python
import rocq_agent_toolkit_utils.json as json
```
"""

import json as libjson
from json import (
    JSONDecodeError,
    JSONDecoder,
    JSONEncoder,
    dump,
    # Note: we provide a more robust implementation of dumps
    # dumps
    load,
    loads,
)
from typing import Any, Literal, overload

from pydantic import BaseModel

import rocq_agent_toolkit_utils as rat_utils


@overload
def dumps(x: Any, *, structured: Literal[True], **kwargs) -> Any:
    """Wrapper for json.dumps: handle (nested) objects in a best-effort way.

    Arguments:
        x: object to try serializing as JSON string
        args: passthrough positional arguments for json.dumps
        structured=True: return structured data instead of a string
        kwargs: passthrough keyword arguments for json.dumps
    Returns:
        best effort serialization result
    Raises:
        TypeError if best effort serialization fails
    """
    ...


@overload
def dumps(x: Any, *, structured: bool | Literal[False] = False, **kwargs) -> str:
    """Wrapper for json.dumps: handle (nested) objects in a best-effort way.

    Arguments:
        x: object to try serializing as JSON string
        args: passthrough positional arguments for json.dumps
        structured=True: return structured data instead of a string
        kwargs: passthrough keyword arguments for json.dumps
    Returns:
        best effort serialization result
    Raises:
        TypeError if best effort serialization fails
    """
    ...


def dumps(
    x: Any,
    *,
    structured: bool = False,
    **kwargs,
) -> str | Any:
    """Wrapper for json.dumps: handle (nested) objects in a best-effort way.

    Arguments:
        x: object to try serializing as JSON string (or data iff structured=True)
        structured (optional): return structured data instead of a string
        kwargs: passthrough keyword arguments for json.dumps
    Returns:
        best effort serialization result
    Raises:
        TypeError if best effort serialization fails
    """
    try:
        data: Any

        if isinstance(x, BaseModel):
            data = x.model_dump() if structured else x.model_dump_json()
        elif hasattr(x, "to_json") and callable(x.to_json):
            data = x.to_json()
        else:  # isinstance(x, (int, float, bool, str, type(None))), custom types, etc...
            data = libjson.dumps(
                x, default=lambda y: dumps(y, structured=False, **kwargs), **kwargs
            )

        return data if structured else str(data)
    except Exception as e:
        raise TypeError(
            f"Serialization failure:{rat_utils.objects.info(x, verbose=True)}"
        ) from e


__all__ = [
    "JSONDecodeError",
    "JSONDecoder",
    "JSONEncoder",
    "dump",
    "dumps",
    "load",
    "loads",
]
assert set(__all__) == set(libjson.__all__), (
    f"{__name__} should provide the same symbols as the builtin json module"
)
