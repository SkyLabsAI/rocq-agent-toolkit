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
file: relative/path/to/file.v
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
To run an agent over a collection of tasks, you should create a file that sets up your agent. This is often something as simple as:

```python
import task_runner
from my_agent import MyAgent

if __name__ == '__main__':
    task_runner.main(MyAgent)
```

If you need extra customization for your agent that should be separately
configurable in a production environment, e.g. extra tools that your agent uses,
you can use extra static methods on your agent class. For example,

```python
class MyRunnerAgent(MyAgent):
    @staticmethod
    def arg_parser(parser : arg_parser):
        """Add additional configuration options to the arg_parser"""
        pass

    @staticmethod
    def build(prompt : str | None, args) -> Agent:
       """args is the command line arguments"""
       return MyAgent(...extra arguments...)
```

If you do not specify a `build` method, then the default constructor is used to
construct an instance of your agent.

## Setting up a Data Set
A data set defines a collection of tasks as well as the infrastructure needed to
execute agents on these tasks.

A data set contains the following:

1. A tasks file (`tasks.json` or `tasks.yaml`) that contains the list of tasks contained within the data set.
2. A `build.py` file that contains functionality to:
   - Build the test suite, e.g. by invoking `dune b` or the appropriate `Makefile`.
   - Describe command line arguments used to interpret the Rocq documents.
   - **Optional** Construct additional arguments for agents. This is only
     necessary if a data set wants to give agents access to additional data
     sources that are **dataset specific** and not immediately accessible from the
     Rocq context. Some examples,
     - For program verification tasks, the agent might get access to the source code
     - For auto-formalization tasks it might get access to domain-specific
       reference material.

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
