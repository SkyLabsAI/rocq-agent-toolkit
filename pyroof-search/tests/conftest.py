"""Shared fixtures for frontier tests."""

from __future__ import annotations

import os

import pytest


def _env_int(name: str, default: int) -> int:
    """Read an integer from the environment to keep parameters user-controlled."""
    value = os.getenv(name)
    if value is None or not value.strip():
        return default
    return int(value)


def _env_int_list(name: str, default: list[int]) -> list[int]:
    """Read a comma-separated integer list from the environment."""
    value = os.getenv(name)
    if value is None or not value.strip():
        return default
    return [int(item.strip()) for item in value.split(",") if item.strip()]


@pytest.fixture
def take_count() -> int:
    return _env_int("ROCQ_FRONTIER_TAKE_COUNT", 2)


@pytest.fixture
def push_values() -> list[int]:
    return _env_int_list("ROCQ_FRONTIER_PUSH_VALUES", [1, 2, 3])
