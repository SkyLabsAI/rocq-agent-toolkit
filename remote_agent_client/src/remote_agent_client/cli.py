"""CLI entrypoint for remote-proof-agent."""
import rocq_pipeline.task_runner as RAT

from remote_agent_client import builder


def main() -> bool:
    """Main entrypoint for remote-proof-agent."""
    return RAT.agent_main(builder)


if __name__ == "__main__":
    exit(0 if main() else 1)
