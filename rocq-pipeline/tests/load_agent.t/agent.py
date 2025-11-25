from rocq_pipeline.agent import AgentBuilder, OneShotBuilder, ProofAgent

default = AgentBuilder.of_agent(ProofAgent)
one_shot = OneShotBuilder()
