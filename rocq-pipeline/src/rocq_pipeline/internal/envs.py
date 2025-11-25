"""
Internal Environment Implementations for Rocq Pipeline.
Contains proprietary logic for Local (Docker) and Staging environments.
"""

import os
import subprocess
import sys
import time
from pathlib import Path

from rocq_pipeline.env_manager import Environment, EnvironmentRegistry

DEFAULT_SERVER = "172.31.0.1"
DEFAULT_DATA_PATH = "/data/skylabs/rocq-agent-runner/data/"
DEFAULT_FRONTEND_PORT = 3005
DEFAULT_GRAFANA_PORT = 3000


class DockerServiceManager:
    """Manages Docker services for local development"""

    def __init__(self, workspace_root: Path):
        self.workspace_root = workspace_root
        self.observability_compose_dir = (
            workspace_root
            / "psi/backend/psi_verifier/observability/observability_docker_compose"
        )
        self.toolkit_dir = workspace_root / "psi/backend/rocq_agent_toolkit"

    def _run_command(
        self, cmd: list[str], cwd: Path | None = None, check: bool = True
    ) -> subprocess.CompletedProcess:
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
            "alloy": self.check_service_running("alloy"),
            "loki": self.check_service_running("loki"),
            "grafana": self.check_service_running("grafana"),
            "backend": self.check_service_running("rocq-agent-toolkit-backend"),
            "frontend": self.check_service_running("rocq-agent-toolkit-frontend"),
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
                    "docker-compose.yml",
                    "-f",
                    "docker-compose.rocq.yml",
                    "up",
                    "--build",
                    "-d",
                    "alloy",
                    "loki",
                    "grafana",
                ],
                cwd=self.observability_compose_dir,
            )

            print("Observability services started successfully")
            return True
        except Exception as e:
            print(f"Error: Failed to start observability services: {e}", file=sys.stderr)
            return False

    def start_toolkit_services(self) -> bool:
        """Start frontend and backend services"""

        if not self.toolkit_dir.exists():
            print(f"Error: Toolkit directory not found: {self.toolkit_dir}", file=sys.stderr)
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
        print(
            f"Results saved locally. View results at: http://localhost:{DEFAULT_FRONTEND_PORT}/"
        )
        print(
            f"Raw Logs can be viewed at Grafana Dashboard at: http://localhost:{DEFAULT_GRAFANA_PORT}/explore"
        )

    def get_otlp_endpoint(self) -> str:
        return "http://0.0.0.0:4317"


class StagingEnvironment(Environment):
    """
    Internal Staging Environment.
    """

    def __init__(self) -> None:
        self.server = DEFAULT_SERVER
        self.data_path = DEFAULT_DATA_PATH
        self.frontend_port = DEFAULT_FRONTEND_PORT
        self.grafana_port = DEFAULT_GRAFANA_PORT

    def get_otlp_endpoint(self) -> str:
        return f"http://{self.server}:4317"

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
                print(f"Error: Cannot reach staging server {self.server}", file=sys.stderr)
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
        """Upload results file to staging server via SCP"""
        if not result_file.exists():
            print(f"Error: Result file not found: {result_file}", file=sys.stderr)
            return

        print("Uploading results to staging server...")

        scp_target = f"{self.server}:{self.data_path}"
        cmd = ["scp", str(result_file), scp_target]

        try:
            result = subprocess.run(
                cmd, capture_output=True, text=True, timeout=60, check=False
            )

            if result.returncode == 0:
                print(f"Results uploaded successfully to {scp_target}")
                print(
                    f"View results at: http://{self.server}:{self.frontend_port}/"
                )
                print(
                    f"Raw Logs can be viewed at Grafana Dashboard at: http://{self.server}:{self.grafana_port}/explore"
                )
            else:
                print("Error: Failed to upload results", file=sys.stderr)
                print(f"Error: {result.stderr}", file=sys.stderr)
                print(
                    f"Please upload manually using: scp {result_file} {scp_target}"
                )

        except subprocess.TimeoutExpired:
            print("Error: Upload timed out", file=sys.stderr)
            print(
                f"Please upload manually using: scp {result_file} {scp_target}"
            )
        except Exception as e:
            print(f"Error: Failed to upload results: {e}", file=sys.stderr)
            print(
                f"Please upload manually using: scp {result_file} {scp_target}"
            )


# Register environments
EnvironmentRegistry.register("local", LocalEnvironment)
EnvironmentRegistry.register("staging", StagingEnvironment)
