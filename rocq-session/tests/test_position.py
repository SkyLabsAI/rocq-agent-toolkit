"""Tests for LSP position → UTF-8 byte offset."""

import pytest
from rocq_session.position import lsp_position_to_byte_offset, utf16_code_unit_count


def test_utf16_count_ascii() -> None:
    assert utf16_code_unit_count("") == 0
    assert utf16_code_unit_count("abc") == 3


def test_utf16_count_supplementary() -> None:
    s = "\U0001f600"  # 😀 — 2 UTF-16 code units
    assert utf16_code_unit_count(s) == 2


def test_single_line_start() -> None:
    src = "Check nat."
    assert lsp_position_to_byte_offset(src, 0, 0) == 0


def test_single_line_end_of_line() -> None:
    src = "Check nat."
    assert lsp_position_to_byte_offset(src, 0, len("Check nat.")) == len(b"Check nat.")


def test_multiline_second_line() -> None:
    src = "a\nbc"
    # Line 1 starts after "a\n" = 2 bytes
    assert lsp_position_to_byte_offset(src, 1, 0) == 2
    assert lsp_position_to_byte_offset(src, 1, 1) == 3


def test_utf16_after_bmp_char() -> None:
    src = "é\nx"  # é is 2 UTF-8 bytes, 1 UTF-16 unit
    line0_utf16 = utf16_code_unit_count("é")
    assert line0_utf16 == 1
    assert lsp_position_to_byte_offset(src, 0, 1) == len("é".encode())


def test_utf16_supplementary_on_line() -> None:
    line = "a\U0001f600b"
    src = line
    # a = 1 utf16, emoji = 2, after emoji character index 3
    assert lsp_position_to_byte_offset(src, 0, 3) == len("a\U0001f600".encode())


def test_line_out_of_range() -> None:
    with pytest.raises(ValueError, match="out of range"):
        lsp_position_to_byte_offset("x", 1, 0)


def test_character_past_eol() -> None:
    with pytest.raises(ValueError, match="past end of line"):
        lsp_position_to_byte_offset("ab", 0, 10)
