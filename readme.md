## Quick Start

**From `/psi/backend`:** ( repo root )

1. Start observability:
```bash
cd psi_verifier/observability/observability_docker_compose
docker compose -f docker-compose.yml -f docker-compose.rocq.yml up --build -d alloy loki
```

2. Start Rocq Agent Toolkit:
Go to folder rocq_agent_toolkit
```bash
cd ../../../rocq_agent_toolkit
docker compose up --build -d
```

3. Access frontend: `localhost:3005`

**Note:** Update env path in `docker-compose.yml` if files are written outside `brick_agents` (currently configured for `brick_agents`).


4. Run the brick_agent pipeline the logs will be shown on the frontend. 
**Note:** After the run, click refresh button on the frontend to get the updated data.

### Centralized Logging Instructions

1. **Create a `.env` file**
   Location: `fmdeps/skylabs-fm/rocq-pipeline/.env`

2. **Set the log endpoint**

   ```
   LOG_OTLP_ENDPOINT=http://172.31.0.1:4317
   ```

   **Note:** You must be connected to the **Khawarzimi VPN** for this to work.

   Once configured, your logs will be sent to the centralized logging server.

---

## Sharing / Publishing Results

To upload results so others can access them, use `scp`:

```bash
scp tasks2_results_20251114_1548.jsonl 172.31.0.1:/data/skylabs/rocq-agent-runner/data/
# Syntax
scp filepath 172.31.0.1:/data/skylabs/rocq-agent-runner/data/
```

A centralized frontend is available at:
**[http://172.31.0.1:3005/](http://172.31.0.1:3005/)**

---

## Local-only Workflow (Without SCP)

If you're working locally and want your backend to read data directly from Loki on the Khawarzimi server:

1. Create a `.env` file next to the `docker-compose` file in `rocq_agent_toolkit` containing:

   ```
   OBSERVABILITY_URL=${OBSERVABILITY_URL:-http://loki:3100}
   ```

2. Change the Loki endpoint so it points to the remote Loki:

   ```
   http://172.31.0.1:3100
   ```

If your `docker-compose.yml` doesn't yet support `.env` overrides, you can temporarily **edit the compose file directly** and replace:

```
http://loki:3100
```

with:

```
http://172.31.0.1:3100
```

