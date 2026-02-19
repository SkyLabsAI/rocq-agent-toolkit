"""CLI entrypoint for remote-proof-agent."""

import rocq_pipeline.prover as RAT

from rocq_remote_agent.builder import RemoteAgentBuilder


def main() -> bool:
    """Main entrypoint for remote-proof-agent."""
    return RAT.agent_main(RemoteAgentBuilder())


if __name__ == "__main__":
    exit(0 if main() else 1)
