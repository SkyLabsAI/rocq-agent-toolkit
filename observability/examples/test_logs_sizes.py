#!/usr/bin/env python3
"""
Simple Log Generation Script for Loki Query Testing

Generates extensive logs using the PSI observability package to test
Loki's query performance and capabilities.

Usage:
    python test_logs_for_query_timeout.py [--count 10000]
"""

import argparse
import random
import time
import uuid

from observability import get_logger, ObservabilityConfig, setup_observability

# Sample data for realistic log generation
USERS = [f"user_{i:04d}" for i in range(1, 101)]
OPERATIONS = ["login", "logout", "payment", "registration", "password_reset", "data_sync", "file_upload"]
SERVICES = ["auth-service", "payment-service", "user-service", "notification-service", "api-gateway"]
LOG_LEVELS = ["info", "warning", "error"]
ERROR_TYPES = ["ValidationError", "DatabaseError", "NetworkTimeout", "AuthenticationError"]

def generate_logs(count: int = 6000, service_name: str = "loki-test-service_9000"):
    """Generate logs in a simple loop."""
    
    # Setup observability
    obs_config = ObservabilityConfig(
        service_name=service_name,
        log_level="DEBUG",
        enable_logging=True,
        log_format_json=True,
        otlp_endpoint="http://localhost:4317"
    )
    setup_observability(obs_config)
    
    # Get logger
    logger = get_logger(__name__)
    
    print(f"🚀 Starting to generate {count} logs for service: {service_name}")
    start_time = time.time()
    
    random_large_log_message = "This is a random large log message that should be logged in a single line. It should be long enough to test the query timeout." * 100

    for i in range(count):
        # Randomly choose log type and data
        log_level = random.choice(LOG_LEVELS)
        user_id = random.choice(USERS)
        operation = random.choice(OPERATIONS)
        service = random.choice(SERVICES)
        request_id = str(uuid.uuid4())
        
        if log_level == "debug":
            logger.debug(
                f"Processing {operation} request {i+1}",
                user_id=user_id,
                service=service,
                request_id=request_id,
                step="validation"
            )
        elif log_level == "info":
            logger.info(
                f"Successfully completed {operation}, {random_large_log_message}",
                user_id=user_id,
                operation=operation,
                service=service,
                duration_ms=random.randint(10, 500),
                request_id=request_id
            )
        elif log_level == "warning":
            logger.warning(
                f"Rate limit approaching for {operation}, {random_large_log_message}",
                user_id=user_id,
                operation=operation,
                current_requests=random.randint(80, 95),
                limit=100,
                request_id=request_id
            )
        else:  # error
            logger.error(
                f"Failed to execute {operation}, ",
                user_id=user_id,
                operation=operation,
                service=service,
                error_type=random.choice(ERROR_TYPES),
                error_code=random.randint(400, 500),
                request_id=request_id
            )
        
        # Progress indicator
        if (i + 1) % 1000 == 0:
            print(f"Generated {i + 1} logs...")
    
    elapsed_time = time.time() - start_time
    print(f"\n✅ Completed!")
    print(f"📊 Generated: {count} logs")
    print(f"⏱️  Time: {elapsed_time:.2f} seconds")
    print(f"🚀 Rate: {count / elapsed_time:.2f} logs/second")
    print(f"\n🔍 Try these Loki queries:")
    print(f'   {{service_name="{service_name}"}}')
    print(f'   {{service_name="{service_name}"}} |= "ERROR"')
    print(f'   {{service_name="{service_name}"}} | json | user_id="user_0001"')
    print(f'   {{service_name="{service_name}"}} | json | operation="login"')

def main():
    """Main function."""
    parser = argparse.ArgumentParser(description="Generate logs for Loki testing")
    parser.add_argument("--count", type=int, default=6000, help="Number of logs to generate")
    parser.add_argument("--service", type=str, default="loki-test-service_9000", help="Service name")
    
    args = parser.parse_args()
    generate_logs(args.count, args.service)

if __name__ == "__main__":
    main()

