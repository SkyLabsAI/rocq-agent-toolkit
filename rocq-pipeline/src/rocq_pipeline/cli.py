from pathlib import Path
import click
from typing import list

from rocq_pipeline import find_tasks, task_runner
from rocq_pipeline.auto_agent import AutoAgent

# --- Main Command Group ---
@click.group()
def cli():
    """
    A simple CLI for data processing with 'ingest' and 'run' subcommands.
    """
    pass

# --- Ingest Subcommand ---
@cli.command()
@click.argument('output_path', type=click.Path(writable=True), required=True)
@click.argument('filenames', nargs=-1, type=click.Path(exists=True))
def ingest(output_path: str, filenames: list[Path]):
    """
    Ingests data from a list of files and saves the processed output.

    OUTPUT_PATH: The path where the processed output will be saved.
    FILENAMES: A list of one or more input files to ingest (positional).
    """
    if filenames:
        find_tasks.run(output_path, filenames)
    else:
        click.echo("No input files provided")

# --- Run Subcommand ---
@cli.command(context_settings=dict(ignore_unknown_options=True))
@click.argument('agent', type=click.STRING,required=True)
@click.argument('j', type=click.IntRange(min=1,clamp=True))
@click.argument('trace', type=click.BOOL)
@click.argument('output-dir', type=click.Path(writable=True))
@click.argument('task-file', type=click.Path(exists=True, dir_okay=False))
@click.pass_context
def run(ctx, agent:str, output_path: Path, input_file: Path):
    """
    Runs a processing job using a single input file.

    OUTPUT_PATH: The path where the job's result will be saved.
    INPUT_FILE: The path to the single input file (positional).
    """
    agent_args:list[str] = []
    try:
        agent_args = ctx.args[ctx.args.index('--')+1:]
    except:
        pass
    task_runner.agent_main(AutoAgent, agent_args)

# --- Entry Point ---
if __name__ == '__main__':
    # Setting 'obj={}' is a common practice when using a group
    # to ensure the context object is initialized, though optional here.
    cli(obj={})
