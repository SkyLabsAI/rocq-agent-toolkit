"""Public client package for the Remote Agent protocol + proxy CLI.

This package intentionally contains only client-side code (protocol models and
the proxy that runs near rocq-doc-manager). Server code lives in a separate,
private package (`remote_agent_server`).
"""

from __future__ import annotations

__all__ = ["__version__"]

__version__ = "0.1.0"

