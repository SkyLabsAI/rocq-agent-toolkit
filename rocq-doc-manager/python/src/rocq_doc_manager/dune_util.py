import os
import subprocess
from pathlib import Path


def dune_env_hack() -> dict[str, str]:
    """Builds an environment that forces the disabling of the build lock"""
    env_copy: dict[str, str] = os.environ.copy()
    env_copy["DUNE_CONFIG__GLOBAL_LOCK"] = "disabled"
    return env_copy


# TODO: hoist into a separate `rocq-dune-util` package.
class DuneUtil:
    @staticmethod
    def rocq_args_for(file_path: str | Path) -> list[str]:
        """Compute Rocq args needed to build/process a target Rocq file."""
        file_path = Path(file_path)
        if file_path.suffix != ".v":
            raise ValueError(f"Expected [.v] file: {str(file_path)}")

        # The dune environment hack is not needed for [dune coq top].
        dune_args_result = subprocess.run([
            "dune", "coq", "top", "--no-build", "--display=quiet",
            "--toplevel=rocq-fake-repl", file_path
        ], capture_output=True)
        dune_args = dune_args_result.stdout.decode(encoding='utf-8')
        return [x.strip() for x in dune_args.splitlines()]
