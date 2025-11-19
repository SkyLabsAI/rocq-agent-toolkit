"""
Internal Environment Implementations for Rocq Pipeline.
Contains proprietary logic for Local (Docker) and Staging environments.
"""

import os
import subprocess
import time
from pathlib import Path

from observability import get_logger

from rocq_pipeline.env_manager import Environment, EnvironmentRegistry

logger = get_logger("env_internal")

DEFAULT_SERVER = "172.31.0.1"
DEFAULT_DATA_PATH = "/data/skylabs/rocq-agent-runner/data/"
DEFAULT_FRONTEND_PORT = 3005


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
            logger.error(f"Command failed: {' '.join(cmd)}")
            logger.error(f"Error: {e.stderr}")
            raise

    def check_docker_running(self) -> bool:
        """Check if Docker daemon is running"""
        try:
            result = self._run_command(["docker", "info"], check=False)
            return result.returncode == 0
        except FileNotFoundError:
            logger.error("Docker is not installed or not in PATH")
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
            "backend": self.check_service_running("rocq-agent-toolkit-backend"),
            "frontend": self.check_service_running("rocq-agent-toolkit-frontend"),
        }
        return services

    def start_observability_services(self) -> bool:
        """Start Alloy and Loki services for observability"""

        if not self.observability_compose_dir.exists():
            logger.error(
                f"Observability compose directory not found: {self.observability_compose_dir}"
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
                ],
                cwd=self.observability_compose_dir,
            )

            logger.info("Observability services started successfully")
            return True
        except Exception as e:
            logger.error(f"Failed to start observability services: {e}")
            return False

    def start_toolkit_services(self) -> bool:
        """Start frontend and backend services"""

        if not self.toolkit_dir.exists():
            logger.error(f"Toolkit directory not found: {self.toolkit_dir}")
            return False

        try:
            self._run_command(
                ["docker", "compose", "up", "--build", "-d"], cwd=self.toolkit_dir
            )

            logger.info("Toolkit services started successfully")
            return True
        except Exception as e:
            logger.error(f"Failed to start toolkit services: {e}")
            return False

    def ensure_services_running(self) -> bool:
        """Ensure all required services are running, starting them if necessary"""
        if not self.check_docker_running():
            logger.error("Docker is not running. Please start Docker and try again.")
            return False
        services = self.check_services()
        if all(services.values()):
            logger.info("All services are already running")
            return True

        logger.info("Some services are not running. Checking status:")
        for service, running in services.items():
            status = "Running" if running else "Not running"
            logger.info(f"  {service}: {status}")

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
            logger.info("All services started successfully")
            return True

        logger.error("Some services failed to start before timeout")
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
                logger.error(
                    "Timeout (%.1fs) while waiting for services to start",
                    elapsed,
                )
                for service, running in services.items():
                    status = "Running" if running else "Not running"
                    logger.error(f"  {service}: {status}")
                return False

            pending = [name for name, running in services.items() if not running]
            logger.info(
                "Waiting for services to start (%s). Elapsed: %.1fs, "
                "next check in %ds",
                ", ".join(pending),
                elapsed,
                poll_interval_seconds,
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

        logger.warning("Workspace root not found via standard structure. Using current dir.")
        return Path.cwd()

    def setup(self) -> bool:
        logger.info("Setting up Local Docker Environment...")
        return self.docker_manager.ensure_services_running()

    def post_run(self, result_file: Path) -> None:
        logger.info(
            f"Results saved locally. View results at: http://localhost:{DEFAULT_FRONTEND_PORT}/"
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

    def get_otlp_endpoint(self) -> str:
        return f"http://{self.server}:4317"

    def setup(self) -> bool:
        """Check if staging server is reachable"""
        logger.info(f"Checking connectivity to staging server {self.server}...")

        try:
            result = subprocess.run(
                ["ping", "-c", "1", "-W", "2", self.server],
                capture_output=True,
                timeout=5,
                check=False,
            )

            if result.returncode != 0:
                logger.error(f"Cannot reach staging server {self.server}")
                logger.error("Please ensure you are connected to the VPN")
                return False

            logger.info(f"Server {self.server} is reachable")
            # Configure environment variables for logging if needed (handled by get_otlp_endpoint)
            logger.info(f"Configured LOG_OTLP_ENDPOINT={self.get_otlp_endpoint()}")
            return True

        except Exception as e:
            logger.error(f"Failed to check server connectivity: {e}")
            return False

    def post_run(self, result_file: Path) -> None:
        """Upload results file to staging server via SCP"""
        if not result_file.exists():
            logger.error(f"Result file not found: {result_file}")
            return

        logger.info("Uploading results to staging server...")

        scp_target = f"{self.server}:{self.data_path}"
        cmd = ["scp", str(result_file), scp_target]

        try:
            result = subprocess.run(
                cmd, capture_output=True, text=True, timeout=60, check=False
            )

            if result.returncode == 0:
                logger.info(f"Results uploaded successfully to {scp_target}")
                logger.info(
                    f"View results at: http://{self.server}:{self.frontend_port}/"
                )
            else:
                logger.error("Failed to upload results")
                logger.error(f"Error: {result.stderr}")
                logger.info(
                    f"Please upload manually using: scp {result_file} {scp_target}"
                )

        except subprocess.TimeoutExpired:
            logger.error("Upload timed out")
            logger.info(
                f"Please upload manually using: scp {result_file} {scp_target}"
            )
        except Exception as e:
            logger.error(f"Failed to upload results: {e}")
            logger.info(
                f"Please upload manually using: scp {result_file} {scp_target}"
            )


# Register environments
EnvironmentRegistry.register("local", LocalEnvironment)
EnvironmentRegistry.register("staging", StagingEnvironment)
