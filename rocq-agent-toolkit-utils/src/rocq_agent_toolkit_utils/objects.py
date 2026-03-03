"""Collection of utilities for working with Python [object]s.

This module is meant to be used in a qualified way:
```python
import rocq_agent_toolkit_utils as rat_utils

...

raise ValueError(
    f"Expected ...:\n{rat_utils.object.info(x)}"
)
```
"""

import difflib
import logging
import pprint

from collections.abc import Sequence
from typing import Any, TypedDict

logger = logging.getLogger(__name__)


# Note: using functional definition since some keys match python builtins (e.g. "type")
ObjMetadata = TypedDict(
    "ObjMetadata",
    {
        "value": Any,
        "type": type,
        "str": str,
        "repr": str,
        "dec_id": int,
        "hex_id": int,
    }
)
__expected_ObjMetadata_key_order = [
    "value",
    "type",
    "str",
    "repr",
    "dec_id",
    "hex_id",
]
__actual_ObjMetadata_key_order = list(ObjMetadata.__annotations__.keys())
assert __actual_ObjMetadata_key_order == __expected_ObjMetadata_key_order, (
    "\n".join(
        [
            "ObjMetadata keys don't match expected order:",
            "\n".join(
                difflib.ndiff(
                    __expected_ObjMetadata_key_order,
                    __actual_ObjMetadata_key_order,
                )
            ),
        ]
    )
)


def metadata(o: object) -> ObjMetadata:
    return {
        "value": o,
        "type": type(o),
        "str": str(o),
        "repr": repr(o),
        "dec_id": id(o),
        "hex_id": hex(id(o)),
    }


def info(
    o: object,
    *os: object,
    include_value: bool = True,
    leading_separator: str | None = "\n",
    verbose: bool = False,
    vverbose: bool = False,
    **kwargs,
) -> str:
    """Use newlines to join the requested object metadata produced by [info_lines]

    Arguments:
        o: object to produce formatted information for
        include_value: whether or not to include the value of o
        leading_separator: optional separator to include at the beginning
        verbose: whether or not to include verbose data (repr)
            Note: forced to True when vverbose=True
        vverbose: whether or not to include very verbose data (dec/hex id)
        kwargs: passthrough keyword arguments for pprint.pformat
    Returns:
        string of requested (prettified) object metadata for each o in os
    """
    if "indent" in kwargs and len(os) != 0:
        logger.debug("Increasing indent to account for multiple objects")
        kwargs["indent"] = int(kwargs["indent"]) + 2

    all_os = (o,) + os
    llines = [
        info_lines(
            o,
            include_value=include_value,
            verbose=verbose,
            vverbose=vverbose,
            **kwargs,
        ) for o in all_os
    ]

    return (leading_separator if leading_separator else "") + "\n\n".join(
        "\n".join(map(lambda line: f"{'- ' if len(all_os) != 1 else ''}{line}", lines)) for lines in llines
    )


def info_lines(
    o: object,
    *,
    include_value: bool = True,
    verbose: bool = False,
    vverbose: bool = False,
    **kwargs,
) -> Sequence[str]:
    """Use pprint.pformat to produce an Sequence of requested object metadata for o.

    Arguments:
        o: object to produce formatted information for
        include_value: whether or not to include the value of o
        verbose: whether or not to include verbose data (repr)
            Note: forced to True when vverbose=True
        vverbose: whether or not to include very verbose data (dec/hex id)
        kwargs: passthrough keyword arguments for pprint.pformat
    Returns:
        Sequence of requested (prettified) object metadata
    """
    if vverbose:
        if not verbose:
            logger.debug("vverbose forces verbose=True")
            verbose = True

    lines: list[str] = []
    # Note: TypedDict guarantees (cf. above [assert]) that keys/values/items are iterated in order
    for k, v in metadata(o).items():
        if (k_renamed := _include_info_as(
                k,
                v,
                include_value=include_value,
                verbose=verbose,
                vverbose=vverbose,
        )) is not None:
            v_pretty = v if isinstance(v, str) else pprint.pformat(v, **kwargs)
            lines.append(f"{k_renamed}{'=' if k_renamed else ''}{v_pretty}")
    assert len(lines) != 0, (
        "No included info:\n" + pprint.pformat(o, indent=1, **kwargs)
    )

    return lines


def _include_info_as(
    k: str,
    v: object,
    *,
    include_value: bool = True,
    verbose: bool = False,
    vverbose: bool = False,
) -> str | None:
    """Helper predicate for [info]: the name to use when including [k], or None if it should be excluded.

    cf. [info] docstring for details regarding flags.
    """
    if vverbose:
        assert verbose, "verbose should be True when vverbose is"

    if k == "value":
        if include_value:
            if not pprint.isreadable(v):
                logger.warning(f"Missing __str__ for {type(v).__qualname__}")
            return ""
        else:
            return None
    elif k == "type":
        if verbose:
            return k
        else:
            return None
    elif k == "str":  # Note: "value" will be pretty-printed using __str__
        return None
    elif k == "repr":
        if verbose:
            return k
        else:
            return None
    elif k in {"dec_id", "hex_id"}:
        if vverbose:
            return k
        else:
            return None
    else:
        raise ValueError(f"{k} is not an ObjMetadata key: {ObjMetadata.keys()}")
