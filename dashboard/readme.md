# Rocq Agent Deployment Guide

This guide outlines the three primary deployment options for running the Rocq agent and visualizing its results.

*   **Local Development:** Run everything (agent, backend, frontend, observability) on your local machine. Ideal for development and testing.


### About Observability Stack

We use an observability stack composed of **Alloy**, **Loki**, and **Grafana**. Alloy acts as the telemetry collector/ingester, receiving logs from the Rocq agent and forwarding them to Loki, which stores and indexes the logs. Grafana provides dashboards and an interface for querying and visualizing these logs.

- **Grafana dashboard**: exposed on port `3010`.
  - Local: `http://0.0.0.0:3010`
- **Rocq Agent Toolkit dashboard** (our internal UI for visualizing runs): exposed on port `3005`:
    The Rocq Agent Toolkit provides its own frontend dashboard that visualizes these logs, while you can still use Grafana to inspect raw logs.
    - Local: `http://0.0.0.0:3010`

* **Using Grafana**
In Grafana, first set the **time range** for which you want to query logs. Then, select the log stream with service name `rocq_agent`. Once these are set, the relevant logs can be fetched. You can also write more complex **LogQL** queries to build specific filters and perform advanced analysis.


---

## 1. Local Development Workflow

This is a self-contained setup for local development. The agent, observability services, and the frontend/backend all run on your local machine using Docker.

### Running the Agent Locally

Run your agent using the `--local` flag. This can start the observability and dashboard services if not already running. 

```
uv run code-proof-agent \
  --task-file ../../data/brick_groundtruth/examples/loopcorpus/tasks.yaml \
  --output-dir results \
  --env local
```
**What the `--env local` flag does:**

  * **Checks Services:** Verifies if the local Docker containers (Loki, Alloy, Grafana, frontend, backend) are running.
  * **Sets Up Environment (if needed):** If the services are not running, it will set them up.
  * **Runs Agent:** Executes the agent, which writes logs and the `.jsonl` results file locally.
  * **Open Browser:** Go to the frontend dashbaord **`http://localhost:3005`**. Click the refresh button on the frontend to load your new results.

### Optional: Manual Local Environment Setup

If you prefer to manage the local services yourself (or if the automatic setup fails), you can run the prerequisites manually.

1.  **Start Local Observability Services:**

    ```
    # Navigate to the observability compose directory
    rocq-agent-toolkit/observability/docker_compose

    # Start Alloy and Loki
    docker compose -f docker-compose.rocq.yml up --build -d alloy loki grafana
    ```

2.  **Start Local Frontend/Backend:**

    ```
    # Navigate to the toolkit directory
    rocq-agent-toolkit/dashboard

    # Start the frontend and backend services
    docker compose up --build -d
    ```

    > **Note:** The `docker-compose.yml` file is configured to look for agent results in the `brick_agents` directory. If your agent outputs files to a different location, you must update the volume mount path in the `docker-compose.yml`.

-----