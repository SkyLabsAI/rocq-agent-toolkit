"""
Environment Implementations for Rocq Pipeline.
This registers the environments with the EnvironmentRegistry.
Contains logic for Local (Docker) and Staging environments.
We use this to setup observability services and toolkit services.
"""

import os
import subprocess
import sys
import time
from pathlib import Path
from typing import Any

import httpx

from rocq_pipeline.env_manager import Environment, EnvironmentRegistry

DEFAULT_SERVER_IP = os.environ.get("DEFAULT_SERVER_IP", "172.31.0.1")
DEFAULT_PUBLIC_IP = os.environ.get("DEFAULT_PUBLIC_IP", "213.248.100.43:9010")


DEFAULT_FRONTEND_PORT = os.environ.get("DEFAULT_FRONTEND_PORT", 3005)
DEFAULT_BACKEND_PORT = os.environ.get("DEFAULT_BACKEND_PORT", 8010)
DEFAULT_GRAFANA_PORT = os.environ.get("DEFAULT_GRAFANA_PORT", 3010)
DEFAULT_ALLOY_PORT = os.environ.get("DEFAULT_ALLOY_PORT", 4327)

OBSERVABILITY_DOCKER_COMPOSE_DIR = (
    "fmdeps/rocq-agent-toolkit/observability/docker_compose"
)
DASHBOARD_DOCKER_COMPOSE_DIR = "fmdeps/rocq-agent-toolkit/dashboard"


def ingest_results_file(
    result_file: Path,
    base_url: str,
    source_file_name: str | None = None,
    timeout: float = 60.0,
) -> dict[str, Any] | None:
    """Upload a JSONL results file to a Rocq Agent Toolkit backend.

    This mirrors the standalone client in ``client.ingester`` but is kept
    local to the pipeline so we do not need to import across projects.
    """
    if not result_file.exists():
        print(f"Error: Result file not found: {result_file}", file=sys.stderr)
        return None

    if source_file_name is None:
        source_file_name = result_file.name

    base = base_url.rstrip("/")
    url = f"{base}/api/ingest/file"

    params: dict[str, str] = {}
    if source_file_name is not None:
        params["source_file_name"] = source_file_name

    try:
        # First, check that the endpoint is reachable.
        try:
            with httpx.Client(timeout=timeout) as client:
                # We only care that the server is reachable; any status code
                # indicates that the endpoint exists.
                resp = client.get(base)
                print(f"Backend endpoint {base} reachable (status {resp.status_code})")
        except httpx.RequestError as exc:
            print(
                f"Error: Backend endpoint {base} is not reachable: {exc}",
                file=sys.stderr,
            )
            return None

        with result_file.open("rb") as f:
            files = {"file": (result_file.name, f, "application/jsonl")}
            with httpx.Client(timeout=timeout) as client:
                response = client.post(url, files=files, params=params)

        response.raise_for_status()
    except httpx.HTTPStatusError as exc:
        print(
            "Error: backend returned error during ingestion: "
            f"{exc.response.status_code} {exc.response.text}",
            file=sys.stderr,
        )
        return None
    except httpx.RequestError as exc:
        print(
            f"Error: failed to upload results to backend at {base}: {exc}",
            file=sys.stderr,
        )
        return None

    data: dict[str, Any] = response.json()

    # Print a concise human-readable summary, mirroring client.ingester.
    success = data.get("success")
    message = data.get("message", "")
    runs = data.get("runs_ingested")
    tasks = data.get("tasks_ingested")

    print(f"Success: {success}")
    if message:
        print(message)
    if runs is not None and tasks is not None:
        print(f"Runs ingested: {runs}, Tasks ingested: {tasks}")

    return data


class DockerServiceManager:
    """Manages Docker services for local development"""

    def __init__(self, workspace_root: Path):
        self.workspace_root = workspace_root
        self.observability_compose_dir = (
            workspace_root / OBSERVABILITY_DOCKER_COMPOSE_DIR
        )
        self.toolkit_dir = workspace_root / DASHBOARD_DOCKER_COMPOSE_DIR

    def _run_command(
        self, cmd: list[str], cwd: Path | None = None, check: bool = True
    ) -> subprocess.CompletedProcess[Any]:
        """Run a shell command and return the result"""
        try:
            result = subprocess.run(
                cmd, cwd=cwd, capture_output=True, text=True, check=check
            )
            return result
        except subprocess.CalledProcessError as e:
            print(f"Error: Command failed: {' '.join(cmd)}", file=sys.stderr)
            print(f"Error: {e.stderr}", file=sys.stderr)
            raise

    def check_docker_running(self) -> bool:
        """Check if Docker daemon is running"""
        try:
            result = self._run_command(["docker", "info"], check=False)
            return result.returncode == 0
        except FileNotFoundError:
            print("Error: Docker is not installed or not in PATH", file=sys.stderr)
            return False

    def check_service_running(self, container_name: str) -> bool:
        """Check if a specific Docker container is running"""
        try:
            result = self._run_command(
                ["docker", "inspect", "-f", "{{.State.Running}}", container_name],
                check=False,
            )
            return result.returncode == 0 and result.stdout.strip() == "true"
        except Exception:
            return False

    def check_services(self) -> dict[str, bool]:
        """Check the status of all required services"""
        services = {
            "alloy": self.check_service_running("rocq-alloy-local"),
            "loki": self.check_service_running("rocq-loki-local"),
            "tempo": self.check_service_running("rocq-tempo-local"),
            "grafana": self.check_service_running("rocq-grafana-local"),
            "backend": self.check_service_running("rocq-agent-toolkit-backend"),
            "frontend": self.check_service_running("rocq-agent-toolkit-frontend"),
            "database": self.check_service_running("rocq-agent-toolkit-db"),
        }
        return services

    def start_observability_services(self) -> bool:
        """Start Alloy and Loki services for observability"""

        if not self.observability_compose_dir.exists():
            print(
                f"Error: Observability compose directory not found: {self.observability_compose_dir}",
                file=sys.stderr,
            )
            return False

        try:
            # Start alloy and loki services
            self._run_command(
                [
                    "docker",
                    "compose",
                    "-f",
                    "docker-compose.rocq.yml",
                    "up",
                    "--build",
                    "-d",
                ],
                cwd=self.observability_compose_dir,
            )

            print("Observability services started successfully")
            return True
        except Exception as e:
            print(
                f"Error: Failed to start observability services: {e}", file=sys.stderr
            )
            return False

    def start_toolkit_services(self) -> bool:
        """Start frontend and backend services"""

        if not self.toolkit_dir.exists():
            print(
                f"Error: Toolkit directory not found: {self.toolkit_dir}",
                file=sys.stderr,
            )
            return False

        try:
            self._run_command(
                ["docker", "compose", "up", "--build", "-d"], cwd=self.toolkit_dir
            )

            print("Toolkit services started successfully")
            return True
        except Exception as e:
            print(f"Error: Failed to start toolkit services: {e}", file=sys.stderr)
            return False

    def ensure_services_running(self) -> bool:
        """Ensure all required services are running, starting them if necessary"""
        if not self.check_docker_running():
            print(
                "Error: Docker is not running. Please start Docker and try again.",
                file=sys.stderr,
            )
            return False
        services = self.check_services()
        if all(services.values()):
            print("All services are already running")
            return True

        print("Some services are not running. Checking status:")
        for service, running in services.items():
            status = "Running" if running else "Not running"
            print(f"  {service}: {status}")

        # Start observability services if needed
        if not services["alloy"] or not services["loki"]:
            if not self.start_observability_services():
                return False

        # Start toolkit services if needed
        if not services["backend"] or not services["frontend"]:
            if not self.start_toolkit_services():
                return False

        # Wait for all services to report as running, with a bounded timeout.
        if self._wait_for_services():
            print("All services started successfully")
            return True

        print("Error: Some services failed to start before timeout", file=sys.stderr)
        return False

    def _wait_for_services(
        self, timeout_seconds: int = 120, poll_interval_seconds: int = 5
    ) -> bool:
        """Wait until all required services are running or a timeout is reached."""
        start_time = time.time()

        while True:
            services = self.check_services()
            if all(services.values()):
                return True

            elapsed = time.time() - start_time
            if elapsed >= timeout_seconds:
                print(
                    f"Error: Timeout ({elapsed:.1f}s) while waiting for services to start",
                    file=sys.stderr,
                )
                for service, running in services.items():
                    status = "Running" if running else "Not running"
                    print(f"  {service}: {status}", file=sys.stderr)
                return False

            pending = [name for name, running in services.items() if not running]
            print(
                f"Waiting for services to start ({', '.join(pending)}). Elapsed: {elapsed:.1f}s, "
                f"next check in {poll_interval_seconds}s"
            )
            time.sleep(poll_interval_seconds)


class LocalEnvironment(Environment):
    """
    Standard Local implementation using Docker.
    """

    def __init__(self) -> None:
        self.workspace_root = self._find_workspace_root()
        self.docker_manager = DockerServiceManager(self.workspace_root)

    def _find_workspace_root(self) -> Path:
        """Find the workspace root directory"""
        # Allow override via ENV VAR
        if os.environ.get("ROCQ_WORKSPACE_ROOT"):
            return Path(os.environ["ROCQ_WORKSPACE_ROOT"])

        # Start from current file location and go up to find workspace root
        current = Path(__file__).resolve()

        # Go up until we find the workspace root indicators
        for parent in current.parents:
            if (parent / "psi").exists() and (parent / "fmdeps").exists():
                return parent

        print(
            "Warning: Workspace root not found via standard structure. Using current dir.",
            file=sys.stderr,
        )
        return Path.cwd()

    def setup(self) -> bool:
        print("Setting up Local Docker Environment...")
        return self.docker_manager.ensure_services_running()

    def post_run(self, result_file: Path) -> None:
        print("Uploading results to local backend via HTTP ingest...")
        ingest_results_file(
            result_file=result_file,
            base_url=f"http://localhost:{DEFAULT_BACKEND_PORT}",
            source_file_name=result_file.name,
        )
        print(
            f"Results saved locally. View results at: http://localhost:{DEFAULT_FRONTEND_PORT}/"
        )
        print(
            f"Raw Logs can be viewed at Grafana Dashboard at: http://localhost:{DEFAULT_GRAFANA_PORT}/explore"
        )

    def get_otlp_endpoint(self) -> str:
        return f"http://localhost:{DEFAULT_ALLOY_PORT}"


class StagingEnvironment(Environment):
    """
    Internal Staging Environment.
    """

    def __init__(self) -> None:
        self.server = DEFAULT_SERVER_IP
        self.frontend_port = DEFAULT_FRONTEND_PORT
        self.grafana_port = DEFAULT_GRAFANA_PORT

    def get_otlp_endpoint(self) -> str:
        return f"http://{self.server}:{DEFAULT_ALLOY_PORT}"

    def setup(self) -> bool:
        """Check if staging server is reachable"""
        print(f"Checking connectivity to staging server {self.server}...")

        try:
            result = subprocess.run(
                ["ping", "-c", "1", "-W", "2", self.server],
                capture_output=True,
                timeout=5,
                check=False,
            )

            if result.returncode != 0:
                print(
                    f"Error: Cannot reach staging server {self.server}", file=sys.stderr
                )
                print(
                    "Error: Please ensure you are connected to the VPN", file=sys.stderr
                )
                return False

            print(f"Server {self.server} is reachable")
            # Configure environment variables for logging if needed (handled by get_otlp_endpoint)
            print(f"Configured LOG_OTLP_ENDPOINT={self.get_otlp_endpoint()}")
            return True

        except Exception as e:
            print(f"Error: Failed to check server connectivity: {e}", file=sys.stderr)
            return False

    def post_run(self, result_file: Path) -> None:
        """Upload results file to staging backend via HTTP ingest."""
        print("Uploading results to staging backend via HTTP ingest...")
        base_url = f"http://{self.server}:{DEFAULT_BACKEND_PORT}"
        ingest_results_file(
            result_file=result_file,
            base_url=base_url,
            source_file_name=result_file.name,
        )
        print(f"View results at: http://{self.server}:{self.frontend_port}/")
        print(
            f"Raw Logs can be viewed at Grafana Dashboard at: http://{self.server}:{self.grafana_port}/explore"
        )


class GithubActionsEnvironment(Environment):
    """
    Github Actions Environment.
    """

    def __init__(self) -> None:
        self.server = DEFAULT_PUBLIC_IP
        self.frontend_port = DEFAULT_FRONTEND_PORT
        self.grafana_port = DEFAULT_GRAFANA_PORT

    def get_otlp_endpoint(self) -> str:
        return f"http://{self.server}/"

    def setup(self) -> bool:
        """Check if github actions environment is reachable"""
        return True

    def post_run(self, result_file: Path) -> None:
        """Upload results file to github actions backend via HTTP ingest."""
        print("Uploading results to backend via HTTP ingest...")
        base_url = f"http://{self.server}/rat"
        ingest_results_file(
            result_file=result_file,
            base_url=base_url,
            source_file_name=result_file.name,
        )
        print(f"View results at: http://{self.server}:{self.frontend_port}/")
        print(
            f"Raw Logs can be viewed at Grafana Dashboard at: http://{self.server}:{self.grafana_port}/explore"
        )


# Register environments
EnvironmentRegistry.register("local", LocalEnvironment)
EnvironmentRegistry.register("staging", StagingEnvironment)
EnvironmentRegistry.register("ci", GithubActionsEnvironment)
