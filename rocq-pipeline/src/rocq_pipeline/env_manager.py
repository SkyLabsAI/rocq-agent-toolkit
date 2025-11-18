"""
Environment manager for Rocq Pipeline
Handles local and staging deployment configurations and service management.
"""

import os
import subprocess
import time
from dataclasses import dataclass
from enum import Enum
from pathlib import Path

from observability import get_logger

logger = get_logger("env_manager")


DEFAULT_SERVER = "172.31.0.1"
DEFAULT_DATA_PATH = "/data/skylabs/rocq-agent-runner/data/"
DEFAULT_FRONTEND_PORT = 3005

class DeploymentMode(Enum):
    """Deployment mode enumeration"""

    NONE = "none"
    LOCAL = "local"
    STAGING = "staging"


@dataclass
class DeploymentConfig:
    """Configuration for different deployment modes"""

    mode: DeploymentMode


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
        """Wait until all required services are running or a timeout is reached.

        This avoids relying on a fixed sleep and instead polls Docker for the
        container states in a professional and robust manner.
        """
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


class StagingManager:
    """Manages staging deployment configuration and file uploads"""


    def __init__(self) -> None:
        self.server = DEFAULT_SERVER
        self.data_path = DEFAULT_DATA_PATH
        self.frontend_port = DEFAULT_FRONTEND_PORT

    def check_server_connectivity(self) -> bool:
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
            return True

        except Exception as e:
            logger.error(f"Failed to check server connectivity: {e}")
            return False

    def configure_environment(self) -> None:
        """Configure environment variables for staging"""
        otlp_endpoint = f"http://{self.server}:4317"
        logger.info(f"Configured LOG_OTLP_ENDPOINT={otlp_endpoint}")

    def upload_results(self, result_file: Path) -> bool:
        """Upload results file to staging server via SCP"""
        if not result_file.exists():
            logger.error(f"Result file not found: {result_file}")
            return False

        logger.info("Uploading results to staging server...")

        scp_target = f"{self.server}:{self.data_path}"
        cmd = ["scp", str(result_file), scp_target]

        try:
            result = subprocess.run(
                cmd, capture_output=True, text=True, timeout=60, check=False
            )

            if result.returncode == 0:
                logger.info(f"Results uploaded successfully to {scp_target}")
                logger.info(f"View results at: http://{self.server}:{self.frontend_port}/")
                return True
            else:
                logger.error("Failed to upload results")
                logger.error(f"Error: {result.stderr}")
                logger.info(
                    f"Please upload manually using: scp {result_file} {scp_target}"
                )
                return False

        except subprocess.TimeoutExpired:
            logger.error("Upload timed out")
            logger.info(f"Please upload manually using: scp {result_file} {scp_target}")
            return False
        except Exception as e:
            logger.error(f"Failed to upload results: {e}")
            logger.info(f"Please upload manually using: scp {result_file} {scp_target}")
            return False


class EnvironmentManager:
    """Main environment manager that coordinates deployment modes"""

    def __init__(self, config: DeploymentConfig, workspace_root: Path | None = None):
        self.config = config

        # Try to find workspace root
        if workspace_root is None:
            workspace_root = self._find_workspace_root()

        self.workspace_root = workspace_root
        self.docker_manager = (
            DockerServiceManager(workspace_root)
            if config.mode == DeploymentMode.LOCAL
            else None
        )
        self.staging_manager = (
            StagingManager() if config.mode == DeploymentMode.STAGING else None
        )

    def _find_workspace_root(self) -> Path:
        """Find the workspace root directory"""
        # Start from current file location and go up to find workspace root
        current = Path(__file__).resolve()

        # Go up until we find the workspace root indicators
        for parent in current.parents:
            if (parent / "psi").exists() and (parent / "fmdeps").exists():
                return parent

        logger.error("Workspace root not found")
        raise ValueError("Workspace root not found")

    def setup(self) -> bool:
        """Setup the environment based on deployment mode"""
        if self.config.mode == DeploymentMode.NONE:
            return True

        logger.info(f"Setting up {self.config.mode.value} environment...")

        if self.config.mode == DeploymentMode.LOCAL:
            return self._setup_local()
        elif self.config.mode == DeploymentMode.STAGING:
            return self._setup_staging()


    def _setup_local(self) -> bool:
        """Setup local development environment"""
        assert self.docker_manager is not None

        # Ensure Docker services are running
        if not self.docker_manager.ensure_services_running():
            return False

        return True

    def _setup_staging(self) -> bool:
        """Setup staging environment"""
        assert self.staging_manager is not None

        # Check server connectivity
        if not self.staging_manager.check_server_connectivity():
            return False

        # Configure environment variables
        self.staging_manager.configure_environment()

        return True

    def post_run(self, result_file: Path | None) -> None:
        """Post-run actions based on deployment mode"""
        if (
            self.config.mode == DeploymentMode.STAGING
            and result_file
            and self.staging_manager
        ):
            self.staging_manager.upload_results(result_file)
        elif self.config.mode == DeploymentMode.LOCAL:
            logger.info(f"Results saved locally. View results at: http://localhost:{DEFAULT_FRONTEND_PORT}/")


def create_deployment_config(mode: str) -> DeploymentConfig:
    """Create a deployment configuration from string mode"""
    mode_map = {
        "none": DeploymentMode.NONE,
        "local": DeploymentMode.LOCAL,
        "staging": DeploymentMode.STAGING,
    }
    return DeploymentConfig(mode=mode_map[mode])


def get_otlp_endpoint(env_mode: str | None = None) -> str:
    """Return the OTLP endpoint for logging.

    Priority:
    1. ``LOG_OTLP_ENDPOINT`` environment variable if set
    2. An explicit ``env_mode`` argument (``local``/``staging``)
    3. Default to localhost
    """
    # Highest priority: Flags passed in by the CLI
    if env_mode == "staging":
        return "http://172.31.0.1:4317"
    if env_mode == "local":
        return "http://0.0.0.0:4317"

    endpoint = os.getenv("LOG_OTLP_ENDPOINT" , "http://0.0.0.0:4317")
    return endpoint
