"""Map LSP-style positions (0-based line, UTF-16 character) to UTF-8 byte offsets."""


def utf16_code_unit_count(line: str) -> int:
    """Number of UTF-16 code units in `line` (BMP = 1 per char, astral = 2)."""
    n = 0
    for ch in line:
        n += 2 if ord(ch) > 0xFFFF else 1
    return n


def lsp_position_to_byte_offset(source: str, line: int, character: int) -> int:
    """Return 0-based byte offset in UTF-8 encoding of `source`.

    - `line` is 0-based.
    - `character` is 0-based UTF-16 offset from the start of that line (no ``\\n``).
    - Allowed ``character`` values are ``0 .. utf16_code_unit_count(line_text)``
      inclusive (end-of-line is ``utf16_code_unit_count``).
    """
    lines = source.split("\n")
    if line < 0 or line >= len(lines):
        msg = f"line {line} is out of range (document has {len(lines)} lines)"
        raise ValueError(msg)
    line_text = lines[line]
    if character < 0:
        raise ValueError("character must be non-negative")

    line_utf16 = utf16_code_unit_count(line_text)
    if character > line_utf16:
        msg = (
            f"character {character} is past end of line "
            f"(line has {line_utf16} UTF-16 code units)"
        )
        raise ValueError(msg)

    prefix_before_line = 0
    for j in range(line):
        prefix_before_line += len(lines[j].encode("utf-8")) + 1

    if character == 0:
        return prefix_before_line

    if character == line_utf16:
        return prefix_before_line + len(line_text.encode("utf-8"))

    utf16_used = 0
    byte_off = 0
    for ch in line_text:
        units = 2 if ord(ch) > 0xFFFF else 1
        encoded = ch.encode("utf-8")
        if utf16_used + units > character:
            raise ValueError("character offset splits a UTF-16 code unit")
        utf16_used += units
        byte_off += len(encoded)
        if utf16_used == character:
            return prefix_before_line + byte_off

    raise AssertionError("unreachable: character should be <= line_utf16")
