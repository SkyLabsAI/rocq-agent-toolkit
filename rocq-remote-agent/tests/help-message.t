Test of the help messages of the prover infrastructure.

  $ uv run rocq-remote-agent -h
  usage: rocq-remote-agent [-h] [-o OUTPUT] [--no-partial] ROCQ_FILE -- ...agent arguments...
  
  Run a proof agent on the given Rocq source file. Extra configuration options
  can be passed to the agent after a '--'. Pass '-h' or '--help' after the '--'
  to get agent options.
  
  positional arguments:
    ROCQ_FILE            file in which to attempt proof completion
  
  options:
    -h, --help           show this help message and exit
    -o, --output OUTPUT  output file (default is the input file)
    --no-partial         discard partial proofs
  $ uv run rocq-remote-agent -- -h
  usage: rocq-remote-agent [-h] [-o OUTPUT] [--no-partial] ROCQ_FILE -- ...agent arguments...
  
  Run a proof agent on the given Rocq source file. Extra configuration options
  can be passed to the agent after a '--'. Pass '-h' or '--help' after the '--'
  to get agent options.
  
  positional arguments:
    ROCQ_FILE            file in which to attempt proof completion
  
  options:
    -h, --help           show this help message and exit
    -o, --output OUTPUT  output file (default is the input file)
    --no-partial         discard partial proofs
  
  usage: ...agent arguments... [-h] [--server SERVER]
                               [--remote-agent REMOTE_AGENT]
                               [--remote-param REMOTE_PARAM]
                               [--provider PROVIDER] [--api-key-env API_KEY_ENV]
                               [--github-login]
  
  options:
    -h, --help            show this help message and exit
    --server SERVER       Remote agent server base URL
    --remote-agent REMOTE_AGENT
                          Server-side agent script name
    --remote-param REMOTE_PARAM
                          KEY=VALUE parameter passed to the server-side agent.
                          Specify multiple times for multiple params (e.g.,
                          --remote-param max_llm_calls=25 --remote-param
                          max_tool_calls=25).
    --provider PROVIDER   LLM provider name (e.g. openrouter).
    --api-key-env API_KEY_ENV
                          Name of the environment variable containing the API
                          Key. Defaults to 'OPENROUTER_API_KEY'.
    --github-login        Force an interactive GitHub device-flow login
                          (overrides cached token).
