import itertools
import logging
import pprint
import pytest
import re

from dataclasses import dataclass

import rocq_agent_toolkit_utils as rat_utils


def test_info_simple_types() -> None:
    for v in [42, 3.14, True, "foobar", None]:
        assert rat_utils.objects.info(v, leading_separator=None) == (v if isinstance(v, str) else pprint.pformat(v))


def test_info_list_of_simple_types() -> None:
    assert rat_utils.objects.info(
        [42, 3.14, True, "foobar", None],
        leading_separator=None,
    ) == "[42, 3.14, True, 'foobar', None]"


def test_info_lines_vverbose_override_verbose(caplog: pytest.LogCaptureFixture) -> None:
    with caplog.at_level(logging.DEBUG):
        rat_utils.objects.info_lines(42, vverbose=True)
    assert len(caplog.records) == 1
    assert re.search(
        "vverbose forces verbose=True",
        caplog.text,
    )


def test_info_class_missing_str(caplog: pytest.LogCaptureFixture) -> None:
    class Foo:
        def __init__(self, data: int) -> None:
            self._data = data

    with caplog.at_level(logging.WARNING):
        info = rat_utils.objects.info(
            Foo(42),
            leading_separator=None,
        )
        assert re.search(
            fr"<{__name__}.{Foo.__qualname__} object at",
            info,
        )
    assert len(caplog.records) == 1
    assert re.search(
        fr"Missing __str__ for {Foo.__qualname__}",
        caplog.text,
    )


@pytest.mark.parametrize(
    "num, flag",
    itertools.product(
        [42, 2.71828, 3.14],
        [True, False],
    ))
def test_info_lines_dataclass(caplog: pytest.LogCaptureFixture, num: int, flag: bool) -> None:
    @dataclass
    class Foo:
        num: int
        flag: bool

    foo = Foo(num, flag)

    with caplog.at_level(logging.DEBUG):
        lines = rat_utils.objects.info_lines(
            foo,
        )
        assert len(lines) == 1
        assert re.search(
            fr"Foo\(num={num}, flag={flag}\)",
            lines[0],
        )
    assert not caplog.records

    with caplog.at_level(logging.DEBUG):
        lines = rat_utils.objects.info_lines(
            foo,
            verbose=True,
        )
        assert len(lines) == 3
        assert re.search(
            fr"Foo\(num={num}, flag={flag}\)",
            lines[0],
        )
        assert re.search(
            fr"type=<class '{__name__}.{Foo.__qualname__}'",
            lines[1],
        )
        assert re.search(
            fr"repr={Foo.__qualname__}\(num={num}, flag={flag}\)",
            lines[2],
        )
    assert not caplog.records

    with caplog.at_level(logging.INFO):
        lines = rat_utils.objects.info_lines(
            foo,
            vverbose=True,
        )
        assert len(lines) == 5
        assert re.search(
            fr"Foo\(num={num}, flag={flag}\)",
            lines[0],
        )
        assert re.search(
            fr"type=<class '{__name__}.{Foo.__qualname__}'",
            lines[1],
        )
        assert re.search(
            fr"repr={Foo.__qualname__}\(num={num}, flag={flag}\)",
            lines[2],
        )

        dec_id_parts = lines[3].split("=")
        assert len(dec_id_parts) == 2
        assert dec_id_parts[0] == "dec_id"
        dec_id: int = int(dec_id_parts[1])

        assert lines[4] == f"hex_id={hex(dec_id)}"
    assert not caplog.records


def test_info_dict_of_dataclasses() -> None:
    @dataclass
    class Foo:
        num: int
        flag: bool

    d = {}

    keys = ["a", "b", "c", "x", "y", "z"]
    for i, k in enumerate(keys, start=42):
        d[k] = Foo(num=i, flag=(i % 2 == 0))

    assert rat_utils.objects.info_lines(d, verbose=True) == [
        pprint.pformat(d),
        "type=<class 'dict'>",
        "repr=" + repr(d),
    ]


def test_info_multiple_dataclasses() -> None:
    @dataclass
    class Foo:
        num: int
        flag: bool

    d = Foo(num=42, flag=False)
    d_info_singleton = rat_utils.objects.info(
        d,
        leading_separator=None,
        vverbose=True,
    )
    d_info_item = "\n".join(
        f"- {line}" for line in d_info_singleton.split("\n")
    )

    for i in range(2, 100):
        assert rat_utils.objects.info(
            *([d] * i),
            leading_separator=None,
            vverbose=True,
        ) == "\n\n".join([d_info_item]*i)
