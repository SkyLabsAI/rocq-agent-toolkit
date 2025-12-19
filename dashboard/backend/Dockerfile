# Build docker from repo root directory

FROM python:3.11-slim

# Set working directory
WORKDIR /app

# Install uv
RUN pip install uv

COPY . .
# COPY pyproject.toml ./

RUN uv sync --package rocq-agent-toolkit-backend

WORKDIR /app/dashboard/backend

# Run the FastAPI application with uvicorn
# Bind to 0.0.0.0 to accept connections from outside the container
CMD ["uv", "run", "uvicorn", "backend.main:app", "--host", "0.0.0.0", "--port", "8000"]
