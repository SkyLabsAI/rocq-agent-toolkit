from __future__ import annotations

from pydantic import BaseModel, Field


class FileOffset(BaseModel):
    line: int = Field(description="line number (0 base)", ge=0)
    col: int = Field(description="column number (0 base)", ge=0)
    offset: int = Field(description="full file offset (0 base)", ge=0)

    @staticmethod
    def of_string(contents: str) -> FileOffset:
        if contents == "":
            return FileOffset(line=0, col=0, offset=0)
        offset = len(contents)
        lines = contents.splitlines()
        line = max(0, len(lines))
        if contents[-1] == "\n":
            col = 0
        else:
            col = len(lines[-1])
        return FileOffset(line=line, col=col, offset=offset)
