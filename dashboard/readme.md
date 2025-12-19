# Rocq Agent Dashboard - Deployment Guide

This guide outlines deployment options for running the Rocq agent and visualizing its results.
Run your agent using the `--local` flag. This can start the observability and dashboard services if not already running. 

```
uv run code-proof-agent \
  --task-file [PATH] \
  --output-dir results \
  --env local
```
**What the `--env local` flag does:**

  * **Checks Services:** Verifies if the local Docker containers (Loki, Alloy, Grafana, frontend, backend) are running.
  * **Sets Up Environment (if needed):** If the services are not running, it will set them up.
  * **Runs Agent:** Executes the agent, which writes logs and the `.jsonl` results file locally.
  * **Open Browser:** Go to the frontend dashbaord **`http://localhost:3005`**. Click the refresh button on the frontend to load your new results.


## About Observability Stack

We use an observability stack composed of **Alloy**, **Loki**, and **Grafana**. Alloy acts as the telemetry collector/ingester, receiving logs from the Rocq agent and forwarding them to Loki, which stores and indexes the logs. Grafana provides dashboards and an interface for querying and visualizing these logs.

- **Grafana dashboard**: exposed on port `3010`.
  - Local: `http://localhost:3010`


---

## Optional: Manual Local Environment Setup

If you prefer to manage the local services yourself (or if the automatic setup fails), you can run the prerequisites manually.

1.  **Start Local Observability Services:**

    ```
    # Navigate to the observability docker compose directory
    rocq-agent-toolkit/observability/docker_compose

    # Start Alloy and Loki
    docker compose -f docker-compose.rocq.yml up --build -d 
    ```

2.  **Start Local Frontend/Backend:**

    ```
    # Navigate to the toolkit directory
    rocq-agent-toolkit/dashboard

    # Start the frontend and backend services
    docker compose up --build -d
    ```

-----