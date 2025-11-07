## Quick Start

**From `/psi/backend`:** ( repo root )

1. Start observability:
```bash
cd psi_verifier/observability/observability_docker_compose
docker-compose -f docker-compose.yml -f docker-compose.rocq.yml up --build -d alloy loki
```

2. Start Rocq Agent Toolkit:
Go to folder rocq_agent_toolkit
```bash
cd ../../../rocq_agent_toolkit
docker-compose up --build -d
```

3. Access frontend: `localhost:3005`

**Note:** Update env path in `docker-compose.yml` if files are written outside `brick_agents` (currently configured for `brick_agents`).


4. Run the brick_agent pipeline the logs will be shown on the frontend. 
**Note:** After the run, click refresh button on the frontend to get the updated data.