#!/bin/bash

# This script follows the instructions in readme.md to start the services.

set -e # Exit immediately if a command exits with a non-zero status.

# Get the directory where the script is located.
SCRIPT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
PSI_BACKEND_DIR="$(dirname "$SCRIPT_DIR")"

echo "--- Step 1: Starting observability ---"

OBSERVABILITY_PATH="$PSI_BACKEND_DIR/psi_verifier/observability/observability_docker_compose"
echo "Changing directory to $OBSERVABILITY_PATH"
cd "$OBSERVABILITY_PATH"

echo "Starting alloy and loki containers..."
docker compose -f docker-compose.yml -f docker-compose.rocq.yml up --build -d alloy loki
echo "Observability services started."

echo ""
echo "--- Step 2: Starting Rocq Agent Toolkit ---"
echo "Changing directory to $SCRIPT_DIR"
cd "$SCRIPT_DIR"

echo "Starting Rocq Agent Toolkit container..."
docker compose up --build -d
echo "Rocq Agent Toolkit started."

echo ""
echo "--- All services are up and running! ---"
echo "3. Access frontend: http://localhost:3005"
echo ""
echo "4. Run the brick_agent pipeline the logs will be shown on the frontend."
echo "**Note:** After the run, click refresh button on the frontend to get the updated data."
