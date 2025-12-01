# Build docker from repo root directory

FROM python:3.11-slim

# Set working directory
WORKDIR /app

# Install uv
RUN pip install uv

COPY . .
# COPY pyproject.toml ./
# does not need observability for now
# COPY psi_verifier/observability/ ./psi_vserviceerifier/observability/

RUN uv sync --package rocq-agent-toolkit-backend

WORKDIR /app/rocq_agent_toolkit/backend

# Run the FastAPI application with uvicorn
# Bind to 0.0.0.0 to accept connections from outside the container
CMD ["uv", "run", "uvicorn", "backend.main:app", "--host", "0.0.0.0", "--port", "8000"]
