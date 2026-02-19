"""
Collection of utilities around dune and Rocq

This package provides a Python interface to the dune build system. It allows
running builds, as well as querying dune for information. The main feature is
the ability to query dune for Rocq CLI arguments for a Rocq source file.
"""

from .rocq_dune_util import (
    DuneError,
    DuneRocqPlugin,
    DuneRocqPluginNotFound,
    dune_build,
    dune_env_hack,
    dune_sourceroot,
    rocq_args_for,
)

__all__ = [
    "DuneError",
    "DuneRocqPlugin",
    "DuneRocqPluginNotFound",
    "dune_build",
    "dune_env_hack",
    "dune_sourceroot",
    "rocq_args_for",
]
