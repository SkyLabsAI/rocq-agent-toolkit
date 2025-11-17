# Rocq Agent Toolkit Guide

This guide outlines three ways to run the Rocq agent and visualize its results.

---

### 1. Fully Remote Workflow (Khawarizmi Server)

This approach is for running the agent, sending logs to the central server, and publishing results for others to see. It does not require any local setup of observability servers or the Rocq Agent Toolkit frontend/backend.

**Steps:**

1.  **Run the Agent**
    Your agent will produce a `.jsonl` file containing the results. To ensure logs are sent to the central server, you need to configure the log endpoint.

2.  **Configure Centralized Logging (`.env`)**
    Your agent needs to know where to send logs.
    - Create a `.env` file in your agent's execution environment. For `rocq-pipeline`, this is `fmdeps/skylabs-fm/rocq-pipeline/.env`.
    - Add the following line:
      ```
      LOG_OTLP_ENDPOINT=http://172.31.0.1:4317
      ```
    - **Note:** You must be connected to the **Khawarzimi VPN** for this to work.

3.  **Submit Results via `scp`**
    Once your agent run is complete, upload the generated `.jsonl` file to the server.
    ```bash
    scp your_results_file.jsonl 172.31.0.1:/data/skylabs/rocq-agent-runner/data/
    ```
    This command syntax assumes that ssh config is set up. If not you might need to update the config or the command.

4.  **SSH Configuration (if needed)**
    If `scp` is not configured for `172.31.0.1`, add the following to your `~/.ssh/config` file:
    ```
    Host 172.31.0.1
      HostName 172.31.0.1
      User <your_username>
      Port 1223
      IdentityFile <path_to_your_khawarzimi_key>
    ```

5.  **View Results**
    You can view the published results on the centralized frontend:
    **[http://172.31.0.1:3005/](http://172.31.0.1:3005/)**
    **Note:** After submitting, click the refresh button on the frontend to get the updated data.

---

### 2. Hybrid Workflow (Local Review, Remote Logging)

This setup allows you to run the agent with logs sent to the Khawarizmi server, but view the results on a local instance of the Rocq Agent Toolkit before deciding whether to publish them.

**Steps:**

1.  **Configure Centralized Logging**
    Follow step 2 from the "Fully Remote Workflow" to send your agent's logs to the central server.

2.  **Start Local Frontend/Backend**
    - Navigate to the `rocq_agent_toolkit` directory.
    - To point the local toolkit to the remote Loki instance, create a `.env` file in this directory with the following content:
      ```
      OBSERVABILITY_URL=http://172.31.0.1:3100
      ```
    - Start the toolkit:
      ```bash
      docker compose up --build -d
      ```

3.  **Run Your Agent**
    The agent will produce a `.jsonl` file locally, while logs will be sent to the remote server.

4.  **Review Locally**
    You can see your run on your local frontend at `http://localhost:3005`.

5.  **Publish (Optional)**
    If you want to share your results, you can upload the local `.jsonl` file using `scp` as described in the "Fully Remote Workflow" (step 3).

---

### 3. Fully Local Workflow

This is a self-contained setup for local development. Everything, including observability services, runs on your local machine.

**Steps:**

1.  **Check Environment**
    Ensure you are not overriding the default configuration to point to Khawarizmi. Specifically, check that you are not setting `OBSERVABILITY_URL=http://172.31.0.1:3100` or `LOG_OTLP_ENDPOINT=http://172.31.0.1:4317`.
    The defualt configs are for the local systems.

2.  **Start Local Observability**
    ```bash
    cd psi_verifier/observability/observability_docker_compose
    docker compose -f docker-compose.yml -f docker-compose.rocq.yml up --build -d alloy loki
    ```

3.  **Start Local Frontend/Backend**
    ```bash
    cd ../../../rocq_agent_toolkit
    docker compose up --build -d
    ```

4.  **Run Your Agent**
    Your agent will write logs and the `.jsonl` file to your local machine.

5.  **View Results**
    Access the frontend at `http://localhost:3005`. After the run, click the refresh button on the frontend to get the updated data.

**Note:** In the `rocq_agent_toolkit/docker-compose.yml`, the volume mount is configured for `brick_agents`. Update the path if your agent's output files are written to a different location.

