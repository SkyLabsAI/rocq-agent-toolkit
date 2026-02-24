import sys
from pathlib import Path


def pytest_configure() -> None:
    """
    Ensure `src/` is importable when running tests without installing the
    package.
    """
    repo_root = Path(__file__).resolve().parents[1]
    src = repo_root / "src"
    if src.is_dir():
        sys.path.insert(0, str(src))
