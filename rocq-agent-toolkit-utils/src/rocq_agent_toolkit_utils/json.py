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
from typing import Any, override

from pydantic import BaseModel, JsonValue

import rocq_agent_toolkit_utils as rat_utils

logger = logging.getLogger(__name__)


class OverridableBestEffortEncoder(JSONEncoder):
    def __init__(
        self,
        cls_encoder_override: type[JSONEncoder] | None = None,
        default_override: Callable[[Any], JsonValue] | None = None,
        **kwargs,
    ) -> None:
        """Build a best effort JSONEncoder.

        Arguments:
            cls_encoder_override (optional override): type of a JSONEncoder that should be preferrentially tried
                Note: custom implementation of dumps passes its cls kwarg here
            default_override (optional override): default callable that should be preferrentially tried
                Note: custom implementation of dumps passes its default kwarg here
        """
        super().__init__(**kwargs)

        self._ordered_overrides: list[tuple[str, Callable[[Any], JsonValue]]] = []
        self._mk_ordered_overrides(
            encoder_override=None
            if cls_encoder_override is None
            else cls_encoder_override(**kwargs),
            default_override=default_override,
        )

    @override
    def default(self, o: Any) -> JsonValue:
        # 1. Try overrides in order & commit to the first one that succeeds
        #
        # Note: record exceptions and re-raise as an ExceptionGroup if _best_effort later fails
        ordered_override_exceptions: list[Exception] = []
        for qualnm, default_override in self._ordered_overrides:
            try:
                return default_override(o)
            except Exception as e_default_override:
                e_default_override.add_note(f"{qualnm}.default")
                ordered_override_exceptions.append(e_default_override)

        # 2. As a last resort use self._best_effort & properly chain exceptions
        if not ordered_override_exceptions:
            return self._best_effort(o)
        else:
            e_overrides = ExceptionGroup(
                "User overrides of JSONDecoder.default",
                ordered_override_exceptions,
            )
            try:
                return self._best_effort(o)
            except Exception as e:
                raise e from e_overrides

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

    def _mk_ordered_overrides(
        self,
        *,
        encoder_override: JSONEncoder | None,
        default_override: Callable[[Any], JsonValue] | None,
    ) -> None:
        """Initialize self._ordered_overrides."""
        assert hasattr(self, "_ordered_overrides")
        assert isinstance(self._ordered_overrides, list)

        if encoder_override is not None:
            encoder_override_qualnm = type(encoder_override).__qualname__
            self._ordered_overrides.append(
                (encoder_override_qualnm, encoder_override.default)
            )

        if default_override is not None:
            default_override_qualnm = getattr(
                default_override, "__qualname__", repr(default_override)
            )
            self._ordered_overrides.append((default_override_qualnm, default_override))


def dumps(o: Any, **kwargs) -> str:
    """Smart wrapper for json.dumps: handle (nested) objects in a best-effort way.

    Note: cls/default kwargs will be intercepted and handled explicitly by OverridableBestEffortEncoder.

    Arguments:
        o: object to try serializing as JSON string
        kwargs: passthrough keyword arguments for json.dumps
    Returns:
        best effort serialization result as a JSON string
    Raises:
        TypeError if best effort serialization fails
    """
    try:
        return libjson.dumps(o, cls=OverridableBestEffortEncoder, **kwargs)
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
