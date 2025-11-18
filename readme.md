# Rocq Agent Deployment Guide

This guide outlines the three primary deployment options for running the Rocq agent and visualizing its results.

*   **Local Development:** Run everything (agent, backend, frontend, observability) on your local machine. Ideal for development and testing.
*   **Staging Server Deployment:** Run the agent locally, but automatically publish logs and results to the central staging server (Khawarizmi) for review.
*   **CI Deployment:** Automatically run the agent via a CI/CD pipeline when you create a pull request or tag a commit.

---

## 1. 📍 Local Development Workflow

This is a self-contained setup for local development. The agent, observability services, and the frontend/backend all run on your local machine using Docker.

### Running the Agent Locally

Run your agent using the `--local` flag. This is the recommended way to manage the local environment.

```
uv run code-proof-agent \
  --task-file ../../data/brick_groundtruth/examples/loopcorpus/tasks.yaml \
  --output-dir results \
  --local
```
**What the `--local` flag does:**

  * **Checks Services:** Verifies if the local Docker containers (Loki, Alloy, frontend, backend) are running.
  * **Sets Up Environment (if needed):** If the services are not running, it will prompt you to automatically set them up.
  * **Runs Agent:** Executes the agent, which writes logs and the `.jsonl` results file locally.
  * **Opens Browser:** Automatically opens your default browser to **`http://localhost:3005`**. Click the refresh button on the frontend to load your new results.

### Optional: Manual Environment Setup

If you prefer to manage the local services yourself (or if the automatic setup fails), you can run the prerequisites manually.

1.  **Start Local Observability Services:**

    ```
    # Navigate to the observability compose directory
    cd psi_verifier/observability/observability_docker_compose

    # Start Alloy and Loki
    docker compose -f docker-compose.yml -f docker-compose.rocq.yml up --build -d alloy loki
    ```

2.  **Start Local Frontend/Backend:**

    ```
    # Navigate to the toolkit directory
    cd ../../../rocq_agent_toolkit

    # Start the frontend and backend services
    docker compose up --build -d
    ```

    > **Note:** The `docker-compose.yml` file is configured to look for agent results in the `brick_agents` directory. If your agent outputs files to a different location, you must update the volume mount path in the `docker-compose.yml`.

-----

## 2\. 🚀 Staging Server Deployment (Khawarizmi)

This approach runs the agent locally but automatically sends logs and publishes results to the central staging server, where the backend, frontend, and observability stack are already running.

### Prerequisites (One-Time Setup)

1.  **Connect to VPN:** You **must** be connected to the **Khawarzimi VPN**.
2.  **Configure SSH:** Your machine needs SSH access to the server for the automatic `scp` file upload. Add the following to your `~/.ssh/config` file:
    
    Host 172.31.0.1
      HostName 172.31.0.1
      User 
      Port 1223
      IdentityFile 
    

### Running the Agent for Staging

Use the `--staging` flag to run the agent and automatically publish to the remote server.
```
uv run code-proof-agent \
  --task-file ../../data/brick_groundtruth/examples/loopcorpus/tasks.yaml \
  --output-dir results \
  --staging
```
**What the `--staging` flag does:**

1.  **Configures Logging:** Automatically sets the log endpoint to the remote server (`LOG_OTLP_ENDPOINT=http://172.31.0.1:4317`).
2.  **Runs Agent:** Executes the agent locally.
3.  **Uploads Results:** After the run, it automatically uploads the generated `.jsonl` file to the staging server via `scp` (e.g., `scp ... 172.31.0.1:/data/skylabs/rocq-agent-runner/data/`).

### View Results

You and your team can view the published results on the centralized frontend:
**[http://172.31.0.1:3005/](http://172.31.0.1:3005/)**

> **Note:** After the run completes, click the refresh button on the frontend to fetch the updated data.

-----

## 3\. CI (Continuous Integration) Deployment

This workflow is for automated agent runs within our CI pipeline (e.g., GitHub Actions). It is triggered by code changes, not run manually from your terminal.

The backend, observability, and frontend for this workflow run on our self-hosted CI runner (which may also be Khawarizmi).

### Process

1.  **Develop:** Make changes to your agent code in a local branch.
2.  **Commit & Push:** Push your changes to GitHub.
3.  **Create Pull Request:** Open a pull request (or tag a commit, depending on the CI trigger configuration).
4.  **Automatic Run:** The CI action automatically triggers. It runs the agent against a pre-configured set of tasks.
5.  **View Results:** The CI run will output a link to the results, which are published to our internal CI frontend instance.

> **Note on CI Task Configuration:**
> Currently, you can override the default tasks used by the CI runner. To do this, place a file named `tasks.yml` in the brick_agents directory of your repository. The CI will detect this file and use it for the run. This is intended for temporary testing and will likely be replaced by a more fixed configuration in the long run.