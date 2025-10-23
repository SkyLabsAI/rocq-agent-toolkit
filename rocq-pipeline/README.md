# Rocq Agent Toolkit
A toolkit for writing and evaluating agents that interact with the [Rocq Proof Assistant](https://rocq-prover.org/).

The toolkit provides the following:
1. *Agent* -- provides an interface for implementing agents.
2. *Tasks* -- provides an interface for describing tasks that agents can perform.
3. *Pipeline* -- provides the setup for evaluating agents against tasks.
4. *Analysis* -- provides tools to analyzing the results of agents working on tasks, e.g. percentage of tasks completed successfully, total token usage, et.

## Agents
The central concept of a Rocq agent is captured in the `Agent` class in `agent.py`. See the documentation for more information.

NOTE: The current agent framework focuses on proof agents.

## Tasks
Tasks are described in a yaml or json file with the following format:

```yaml
- file: relative/path/to/file.v
  locator: lemma:lemma_name # see `locator.py` for more information
  tags: # free-form tags useful for filtering
   - proof
   - requires-induction
```

## Pipeline / Runner
To run an agent over a collection of tasks, you should create a file that sets up your agent. This is often something as simple as:

```python
import task_runner
from my_agent import MyAgent

if __name__ == '__main__':
    task_runner.main(MyAgent)
```

If you need extra customization for your agent that should be separately configurable in a production environment, e.g. extra tools that your agent uses, you can use extra static methods on your agent class. For example,

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

If you do not specify a `build` method, then the default constructor is used to construct an instance of your agent.

## Analysis
Forthcoming.
