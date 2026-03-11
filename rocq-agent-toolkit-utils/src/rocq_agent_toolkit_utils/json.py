"""Re-expose the builtin `json` module with a robust & overridable default for dumps.

This module is meant to be used instead of the builtin json module:
```python
import rocq_agent_toolkit_utils.json as json
```
"""

import json as libjson
import logging
from collections.abc import Callable
from dataclasses import asdict, is_dataclass
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
from typing import Any, TypeGuard, override

from pydantic import BaseModel, JsonValue

import rocq_agent_toolkit_utils as rat_utils

logger = logging.getLogger(__name__)


def obj_jsonable(o: Any) -> TypeGuard[JsonValue]:
    """Predicate: test whether [o] is an object that can be serialized to a JSON string.

    cf. pydantic.JsonValue
    """
    if o is None or isinstance(o, (bool, int, float, str)):
        return True
    elif isinstance(o, list) and all(obj_jsonable(elem) for elem in o):
        return True
    elif isinstance(o, dict) and all(
        isinstance(k, str) and obj_jsonable(v) for k, v in o.items()
    ):
        return True
    else:
        return False


class OverridableBestEffortEncoder(JSONEncoder):
    def __init__(self, **kwargs) -> None:
        """Build a best effort JSONEncoder.

        Note: "default" kwarg is intercepted and tried preferrentially.

        Arguments:
            kwargs: JSONEncoder kwargs
        """
        self._default_override: Callable[..., object] | None = None
        super().__init__(**self._intercept_overrides(**kwargs))

    @override
    def default(self, o: Any) -> JsonValue:
        # 1. If present, prefer self._default_override
        e_default: Exception | None = None
        if self._default_override:
            try:
                result = self._default_override(o)
                assert obj_jsonable(result), " ".join(
                    [
                        "'default(o)' should produce a JsonValue:",
                        rat_utils.objects.info(
                            self._default_override, o, result, verbose=True
                        ),
                    ]
                )
                return result
            except Exception as _e_default:
                e_default = _e_default
                logger.debug(
                    " ".join(
                        [
                            "'default' override failed to process o:",
                            rat_utils.objects.info(
                                self._default_override, o, verbose=True
                            ),
                        ]
                    ),
                    exc_info=True,
                )

        # 2. Otherwise, use self._best_effort & properly chain exceptions
        try:
            return self._best_effort(o)
        except Exception as e:
            if e_default:
                raise e from e_default
            else:
                raise e

    def _best_effort(self, o: Any) -> JsonValue:
        """Core logic for the custom, best effort implementation of JSONDecoder.default."""
        # Fastpath for types
        if isinstance(o, type):
            return super().default(o)

        # BEGIN TODO: "safe" serialization that hides private data
        elif is_dataclass(o):
            # Note: needed by typecheckers; assert holds after the isinstance(o, type) check above
            assert not isinstance(o, type)
            return asdict(o)
        elif isinstance(o, BaseModel):
            return o.model_dump(mode="json")
        # END TODO: "safe" serialization that hides private data

        else:  # isinstance(x, (int, float, bool, str, type(None))), custom types, etc...
            return super().default(o)

    def _intercept_overrides(self, **kwargs: Any) -> dict[str, Any]:
        """Intercept 'cls'+'default' kwargs for JSONEncoder"""
        default_override = kwargs.pop("default", None)

        if default_override is not None:
            assert callable(default_override), " ".join(
                [
                    "'default' isn't callable:",
                    rat_utils.objects.info(default_override, verbose=True),
                ]
            )
            # Note: we could use [inspect] to type-check [default_override]

            self._default_override = default_override

        return kwargs


def dumps(o: Any, **kwargs) -> str:
    """Smart wrapper for json.dumps: handle (nested) objects in a best-effort way.

    Note: unless "cls" is supplied in kwargs, OverridableBestEffortEncoder will be used.

    Arguments:
        o: object to try serializing as JSON string
        kwargs: passthrough keyword arguments for json.dumps
    Returns:
        best effort serialization result as a JSON string
    Raises:
        TypeError if best effort serialization fails
    """
    cls = kwargs.pop("cls", OverridableBestEffortEncoder)

    try:
        return libjson.dumps(o, cls=cls, **kwargs)
    except Exception as e:
        e.add_note(rat_utils.objects.info(o, verbose=True))
        raise e


__all__ = [
    "JSONDecodeError",
    "JSONDecoder",
    "JSONEncoder",
    "dump",
    "dumps",
    "load",
    "loads",
]
assert set(libjson.__all__) <= set(__all__), (
    f"{__name__} should provide the same symbols as the builtin json module"
)
