"""CLI entrypoint for remote-proof-agent."""

import rocq_pipeline.prover as RAT

from rocq_remote_agent.builder import RemoteAgentBuilder


def main() -> int:
    """Main entrypoint for remote-proof-agent."""
    return 0 if RAT.agent_main(RemoteAgentBuilder()) else 1


if __name__ == "__main__":
    exit(main())
