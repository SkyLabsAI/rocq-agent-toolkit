import argparse
import os
import sys
import webbrowser
from argparse import ArgumentParser, Namespace
from typing import Any, Protocol

# Importing internal envs registers Local/Staging/CI environments via EnvironmentRegistry.
import rocq_pipeline.internal.envs as envs
from rocq_pipeline.env_manager import EnvironmentRegistry


class _ArgparseSubparsers(Protocol):
    def add_parser(self, name: str, **kwargs: Any) -> argparse.ArgumentParser: ...


def _get_env_name(arguments: Namespace) -> str:
    # CLI flag wins, then env var fallback.
    env_name = getattr(arguments, "env", None) or os.getenv("RAT_ENV")
    return (env_name or "local").strip()


def _resolve_urls(env_name: str) -> dict[str, str]:
    # Explicit overrides (useful for staging/prod routing)
    dashboard_url = os.getenv("RAT_DASHBOARD_URL")
    backend_url = os.getenv("RAT_BACKEND_URL")
    grafana_url = os.getenv("RAT_GRAFANA_URL")
    docs_url = os.getenv("RAT_DOCS_URL")

    if dashboard_url and backend_url and grafana_url and docs_url:
        return {
            "dashboard": dashboard_url,
            "backend": backend_url,
            "grafana": grafana_url,
            "docs": docs_url,
        }

    env_name_lower = env_name.lower()
    if env_name_lower == "local":
        host = "localhost"
        dashboard = f"http://{host}:{envs.DEFAULT_FRONTEND_PORT}"
        backend = f"http://{host}:{envs.DEFAULT_BACKEND_PORT}"
        grafana = f"http://{host}:{envs.DEFAULT_GRAFANA_PORT}"
        docs = f"{backend}/docs"
    elif env_name_lower == "staging":
        host = str(envs.DEFAULT_SERVER_IP)
        dashboard = f"http://{host}:{envs.DEFAULT_FRONTEND_PORT}"
        backend = f"http://{host}:{envs.DEFAULT_BACKEND_PORT}"
        grafana = f"http://{host}:{envs.DEFAULT_GRAFANA_PORT}"
        docs = f"{backend}/docs"
    elif env_name_lower == "ci":
        raise ValueError(
            "env 'ci' is not supported by this CLI (reserved for GitHub workflows)"
        )
    else:
        # Unknown env: behave like local but allow overrides to drive actual routing.
        host = "localhost"
        dashboard = f"http://{host}:{envs.DEFAULT_FRONTEND_PORT}"
        backend = f"http://{host}:{envs.DEFAULT_BACKEND_PORT}"
        grafana = f"http://{host}:{envs.DEFAULT_GRAFANA_PORT}"
        docs = f"{backend}/docs"

    # Apply partial overrides if provided
    return {
        "dashboard": (dashboard_url or dashboard).rstrip("/"),
        "backend": (backend_url or backend).rstrip("/"),
        "grafana": (grafana_url or grafana).rstrip("/"),
        "docs": (docs_url or docs).rstrip("/"),
    }


def _maybe_open(url: str, enabled: bool) -> None:
    if not enabled:
        return
    try:
        webbrowser.open(url, new=2)
    except Exception as e:
        print(f"Warning: failed to open browser: {e}", file=sys.stderr)


def mk_service_parser(
    parent: _ArgparseSubparsers | None = None,
) -> argparse.ArgumentParser:
    if parent:
        parser = parent.add_parser(
            "service", help="Manage local RAT dashboard services"
        )
    else:
        parser = ArgumentParser(description="Manage local RAT dashboard services")

    # argparse note: options for a parser must appear before its positional subcommands.
    # To allow both:
    #   - rat service --env local status
    #   - rat service status --env local
    # we share an env parent parser with each subcommand below.
    env_parent = argparse.ArgumentParser(add_help=False)
    env_parent.add_argument(
        "--env",
        type=str,
        default=os.getenv("RAT_ENV") or "local",
        help="Environment routing ('local', 'staging'). Default: RAT_ENV or 'local'.",
    )

    parser.add_argument(
        "--env",
        type=str,
        default=os.getenv("RAT_ENV") or "local",
        help="Environment routing ('local', 'staging'). Default: RAT_ENV or 'local'.",
    )

    subparsers = parser.add_subparsers(dest="service_command", help="Service commands")

    p_start = subparsers.add_parser(
        "start",
        parents=[env_parent],
        help="Start services (docker compose for local; connectivity check for staging).",
    )
    p_start.add_argument(
        "--no-open",
        action="store_true",
        help="Do not open the dashboard in a browser after starting.",
    )

    p_stop = subparsers.add_parser(
        "stop",
        parents=[env_parent],
        help="Stop local docker compose services.",
    )
    p_stop.add_argument(
        "--volumes",
        action="store_true",
        help="Also remove docker volumes (destructive).",
    )

    subparsers.add_parser(
        "status",
        parents=[env_parent],
        help="Show service status and URLs.",
    )

    p_doc = subparsers.add_parser(
        "doc",
        parents=[env_parent],
        help="Open the FastAPI docs URL for the backend.",
    )
    p_doc.add_argument(
        "--no-open",
        action="store_true",
        help="Do not open a browser (print the URL only).",
    )

    return parser


def _print_urls(env_name: str) -> dict[str, str]:
    try:
        urls = _resolve_urls(env_name)
    except ValueError as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(2)
    print(f"Environment: {env_name}")
    print(f"Dashboard:   {urls['dashboard']}")
    print(f"Backend:     {urls['backend']}")
    print(f"Docs:        {urls['docs']}")
    print(f"Grafana:     {urls['grafana']}")
    return urls


def service_run_ns(arguments: Namespace, extra_args: list[str] | None = None) -> None:
    assert extra_args is None or len(extra_args) == 0
    env_name = _get_env_name(arguments)
    cmd = getattr(arguments, "service_command", None)

    if cmd is None:
        # Argparse will not enforce a subcommand by default.
        mk_service_parser().print_help()
        return

    if cmd == "start":
        env_cls = EnvironmentRegistry.get(env_name)
        env = env_cls()
        ok = env.setup()
        if not ok:
            sys.exit(2)
        urls = _print_urls(env_name)
        _maybe_open(urls["dashboard"], enabled=not bool(arguments.no_open))
        return

    if cmd == "stop":
        if env_name.lower() != "local":
            print(
                "Stop is only supported for --env local (docker-managed services).",
                file=sys.stderr,
            )
            sys.exit(2)
        env = envs.LocalEnvironment()
        ok = env.docker_manager.stop_all_services(
            remove_volumes=bool(arguments.volumes)
        )
        if not ok:
            sys.exit(2)
        return

    if cmd == "status":
        urls = _print_urls(env_name)
        if env_name.lower() == "local":
            env = envs.LocalEnvironment()
            if not env.docker_manager.check_docker_running():
                print("Docker:      NOT running", file=sys.stderr)
                sys.exit(2)
            services = env.docker_manager.check_services()
            print("Containers:")
            for name, running in services.items():
                status = "running" if running else "not running"
                print(f"  - {name}: {status}")
        else:
            # For non-local envs we don't manage containers; status is URL visibility.
            # (Users can override with RAT_*_URL env vars.)
            print("Note: non-local env; container status is not managed by this CLI.")
            print("Tip: set RAT_DASHBOARD_URL / RAT_BACKEND_URL if routing differs.")
        return

    if cmd == "doc":
        urls = _print_urls(env_name)
        _maybe_open(urls["docs"], enabled=not bool(arguments.no_open))
        return

    mk_service_parser().print_help()


def mk_dashboard_parser(
    parent: _ArgparseSubparsers | None = None,
) -> argparse.ArgumentParser:
    if parent:
        parser = parent.add_parser("dashboard", help="Open the dashboard in a browser")
    else:
        parser = ArgumentParser(description="Open the dashboard in a browser")

    parser.add_argument(
        "--env",
        type=str,
        default=os.getenv("RAT_ENV") or "local",
        help="Environment routing ('local', 'staging'). Default: RAT_ENV or 'local'.",
    )
    parser.add_argument(
        "--no-open",
        action="store_true",
        help="Do not open a browser (print the URL only).",
    )
    return parser


def dashboard_run_ns(arguments: Namespace, extra_args: list[str] | None = None) -> None:
    assert extra_args is None or len(extra_args) == 0
    env_name = _get_env_name(arguments)
    urls = _print_urls(env_name)
    _maybe_open(urls["dashboard"], enabled=not bool(arguments.no_open))
