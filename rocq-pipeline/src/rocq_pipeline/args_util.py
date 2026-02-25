import os
import sys
from argparse import ArgumentParser
from collections.abc import Callable
from io import StringIO
from pathlib import Path
from urllib.parse import urlparse


def valid_file(
    exists: bool | None = None,
    check_creatable: bool = False,
    allowed_suffixes: list[str] | None = None,
) -> Callable[[str], Path]:
    """
    Returns a validator function that (optionally) checks if the given file
    exists, can be created, or has one of the allowed suffix (extension).
    """

    def validator(file: str) -> Path:
        path = Path(file)

        if exists is not None:
            if exists and not path.exists():
                sys.exit(f"Error: file {path} does not exist.")
            if not exists and path.exists():
                sys.exit(f"Error: file {path} already exists.")

        if check_creatable:
            if not path.parent.exists():
                sys.exit(
                    f"Error: file {path} cannot be created (parent directory does not exist)."
                )
            if path.exists() and not os.access(path, os.W_OK):
                sys.exit(f"Error: file {path} exists, but cannot be written.")
            if not path.exists() and not os.access(path.parent, os.W_OK):
                sys.exit(f"Error: file {path} cannot be created.")

        if allowed_suffixes is not None:
            if path.suffix not in allowed_suffixes:
                sys.exit(
                    f"Error: invalid extension on {path} (must be: {', '.join(allowed_suffixes)})."
                )
        return path

    return validator


def validate_url(url: str) -> str:
    """Custom validator to check if the input is a valid URL."""
    result = urlparse(url)
    if all([result.scheme, result.netloc]):
        return url
    raise ValueError(f"Invalid URL: '{url}'")


def split_args(argv: list[str] | None = None) -> tuple[list[str], list[str]]:
    """Split arguments at the -- if it exists.

    @param argv if null, this uses `sys.argv[1:]`
    @returns (args, extra_args)
    """
    args = sys.argv[1:] if argv is None else argv
    extra_args: list[str] = []
    try:
        idx = args.index("--")
        extra_args = args[idx + 1 :]
        args = args[:idx]
    except ValueError:
        pass
    return (args, extra_args)


def adapt_usage(parser: ArgumentParser, whom: str) -> None:
    usage_stream = StringIO()
    parser.print_usage(usage_stream)
    # The format of the value is 'usage: ...\n'
    # We capture the ... and append the suffix.
    usage = usage_stream.getvalue().split(" ", maxsplit=1)[1].strip()

    parser.usage = f"{usage} -- ...{whom} arguments..."
