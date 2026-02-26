Test of the help messages of the prover infrastructure.

  $ uv run auto-prover -h
  usage: auto-prover [-h] [-o OUTPUT] [--no-partial]
                     [--progress | --no-progress]
                     ROCQ_FILE -- ...agent arguments...
  
  Run a proof agent on the given Rocq source file. Extra configuration options
  can be passed to the agent after a '--'. Pass '-h' or '--help' after the '--'
  to get agent options.
  
  positional arguments:
    ROCQ_FILE             file in which to attempt proof completion
  
  options:
    -h, --help            show this help message and exit
    -o, --output OUTPUT   output file (default is the input file)
    --no-partial          discard partial proofs
    --progress, --no-progress
                          show proof progress
  $ uv run auto-prover -- -h
  usage: auto-prover [-h] [-o OUTPUT] [--no-partial]
                     [--progress | --no-progress]
                     ROCQ_FILE -- ...agent arguments...
  
  Run a proof agent on the given Rocq source file. Extra configuration options
  can be passed to the agent after a '--'. Pass '-h' or '--help' after the '--'
  to get agent options.
  
  positional arguments:
    ROCQ_FILE             file in which to attempt proof completion
  
  options:
    -h, --help            show this help message and exit
    -o, --output OUTPUT   output file (default is the input file)
    --no-partial          discard partial proofs
    --progress, --no-progress
                          show proof progress
  
