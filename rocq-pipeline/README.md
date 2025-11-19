# Rocq Agent Toolkit
A toolkit for writing and evaluating agents that interact with the [Rocq Proof Assistant](https://rocq-prover.org/).

The toolkit provides the following:
1. *Agent* -- provides an interface for implementing agents.
2. *Tasks* -- provides an interface for describing tasks that agents can perform.
3. *Pipeline* -- provides the setup for evaluating agents against tasks.
4. *Analysis* -- provides tools to analyzing the results of agents working on tasks, e.g. percentage of tasks completed successfully, total token usage, et.

## Agents
The central concept of a Rocq agent is captured in the `Agent` class in `agent.py`. See the documentation for more information.

NOTE: The *current* agent framework focuses on proof agents.

## Tasks
Tasks are JSON objects with the following scheme (here presented in YAML):

```yaml
name: my-name # optional, by default constructed by [file#locator]
file: relative/path/to/file.v # relative to the task file
locator: lemma:lemma_name # see `locator.py` for more information
tags: # free-form tags useful for filtering
- proof
- requires-induction
# [prompt] is optional
prompt: >
  complete this task.
  it might require induction.
```

Multiple tasks can be bundled into a single file (idiomatically called
`tasks.yaml`) as an array. For example,

```yaml
- task1
- task2
```

## Pipeline / Runner
To run an agent over a collection of tasks, you should create a file that sets
up your agent. This is often something as simple as:

```python
from rocq_pipeline.task_runner import agent_main
from my_agent import MyAgent

if __name__ == '__main__':
    agent_main(AgentBuilder.of_agent(MyAgent))
```

If you need extra customization for your agent that should be separately
configurable in a production environment, e.g. extra tools that your agent uses,
you can define a custom `AgentBuilder`.

```python
class MyAgentBuilder(AgentBuilder):
    def add_args(self, args: list[str]) -> None:
        # args is extra command line arguments passed to the agent, e.g. ["--tactic", "foo; bar"]
        pass

    def __call__(self) -> Agent:
        return MyAgent(self.args)

# Used with
if __name__ == '__main__':
    agent_main(MyAgentBuilder())
```

## Setting up a Data Set
A data set defines a collection of tasks as well as the infrastructure needed to
execute agents on these tasks.

A data set contains the following:

1. A tasks file (`tasks.json` or `tasks.yaml`) that contains the list of tasks
   contained within the data set.

### Task Output

Currently, the results for each task are persisted (in order) in a single `.jsonl` file.
The name of this file is of the form `<name>_results_<timestamp>.jsonl`.

If `--task-file` is used then the name is the stem of the task file; if `--task-json` is used then the name is `"tasks"`.
The `--output-dir` flag can be used to specify where the result file should be created; the working directory is used by default.

#### Schema

cf. [src/rocq_pipeline/schema/task_output.atd](./src/rocq_pipeline/schema/task_output.atd)

#### TODO: Opentelemetry

We aspire to instrument the framework with `opentelemetry` so that rich metrics/logs/telemetry may be correlated with specific (summary) task results.

**Note**: it should be easy for custom agents to instrument additional metrics/logs/telemetry.

## Analysis
Forthcoming.
