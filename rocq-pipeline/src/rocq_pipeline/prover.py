import argparse
import asyncio
import logging
import sys
from argparse import ArgumentParser
from collections.abc import Awaitable, Callable, Sequence
from pathlib import Path

from rocq_doc_manager import RocqCursor, rc_sess
from rocq_doc_manager import rocq_doc_manager_api as rdm_api
from rocq_doc_manager.cursor import DelimitedRocqCursor, GoalRocqCursor
from rocq_dune_util import DuneError, rocq_args_for

from rocq_pipeline.agent import AgentBuilder
from rocq_pipeline.agent.proof.auto import AutoAgent
from rocq_pipeline.args_util import adapt_usage, split_args, valid_file
from rocq_pipeline.prover_ui.ui import Controller, build_ui
from rocq_pipeline.status_cursor import WatchingCursor

# TODOs:
# - proof formatter
# - parallel tasks


def is_real_command(data: rdm_api.VernacData) -> bool:
    return all(c not in data.controls for c in ["Fail", "Succeed"])


def has_kind(data: rdm_api.VernacData, kind: str) -> bool:
    return data.kind == kind and is_real_command(data)


def starts_proof(item: rdm_api.PrefixItem | rdm_api.SuffixItem) -> bool:
    return item.data is not None and (
        has_kind(item.data, "StartTheoremProof")
        or (has_kind(item.data, "Definition") and item.data.attrs["proof"])
    )


def ends_proof(item: rdm_api.PrefixItem | rdm_api.SuffixItem) -> bool:
    return item.data is not None and has_kind(item.data, "EndProof")


def is_admitted(item: rdm_api.PrefixItem | rdm_api.SuffixItem) -> bool:
    return (
        item.data is not None
        and has_kind(item.data, "EndProof")
        and item.data.attrs["kind"] == "Admitted"
    )


def is_admit(item: rdm_api.PrefixItem | rdm_api.SuffixItem) -> bool:
    return (
        item.data is not None
        and has_kind(item.data, "Extend")
        and item.text == "admit."  # NOTE could relax blanks.
    )


def statement_index_from_proof_end(
    items: list[rdm_api.PrefixItem | rdm_api.SuffixItem], proof_end_index: int
) -> int:
    """
    Returns the index of the item of that starts the proof ending at index
    `proof_end_index`. It is assumed that the `items` correspond to a correct
    Rocq document, and that `proof_end_index` is indeed the index of a proof
    ending command (like "Qed" or "Admitted").

    @param items: full list of items in the document
    @param proof_end_index: index of a proof ending command in `items`
    @return: the index of the matching proof starting command in `items`
    @raise ValueError: if either of `proof_end` or `item` is invalid
    """
    if not (0 <= proof_end_index < len(items)):
        raise ValueError(f"Invalid proof end index {proof_end_index}")
    proof_end = items[proof_end_index]
    if proof_end.data is None or proof_end.data.kind != "EndProof":
        raise ValueError(
            f"No proof terminator at index {proof_end_index} (found {proof_end})"
        )
    nested = 0
    for i in range(proof_end_index - 1, -1, -1):
        item = items[i]
        if ends_proof(item):
            nested += 1
        elif starts_proof(item):
            if nested == 0:
                return i
            nested -= 1
    raise ValueError("Could not locate the start of the proof")


async def delimited_cursor_for_next_admitted(
    rc: RocqCursor,
) -> DelimitedRocqCursor | None:
    """
    Creates a delimited cursor spanning the next admitted proof in the suffix
    of cursor `rc`. The statement and the terminating `Admitted` command are
    respectively the first and last command of the cursor's region. Note that
    the returned cursor overlays `rc`, so `rc` itself is fully owned by the
    returned cursor while it is in use. This means that modifications made in
    the delimited cursor will take effect in `rc` as well.

    @param rc: the underlying cursor, "fully borrowed" by the operation
    @return: a delimited cursor for the next admitted proof if any
    @raise Exception: in case of document processing error
    """
    prefix = await rc.doc_prefix()
    suffix = await rc.doc_suffix()
    index = await rc.cursor_index()
    contents = prefix + suffix
    # Find the next admitted item.
    admitted_index = next(
        (index + i for i, item in enumerate(suffix) if is_admitted(item)), None
    )
    if admitted_index is None:
        return None
    # Find the corresponding proof start.
    try:
        start = statement_index_from_proof_end(contents, admitted_index)
    except ValueError as e:
        raise AssertionError() from e
    # Build a delimited cursor for the proof.
    cursor = await DelimitedRocqCursor.make(
        rc, start=start, end=admitted_index, clone=False
    )
    if isinstance(cursor, rdm_api.Err):
        raise Exception("Unable to process the document further: {cursor}")
    return cursor


async def step_over_proof(cursor: RocqCursor) -> None:
    suffix = await cursor.doc_suffix()
    if len(suffix) == 0:
        raise ValueError("No item left")
    if not starts_proof(suffix.pop(0)):
        raise ValueError("Not on a proof starting item")
    res = await cursor.run_step()
    if isinstance(res, rdm_api.Err):
        raise ValueError("Invalid document (cannot process statement)")
    level = 0
    for item in suffix:
        res = await cursor.run_step()
        if isinstance(res, rdm_api.Err):
            raise ValueError("Invalid document (cannot process statement)")
        elif starts_proof(item):
            level += 1
        elif ends_proof(item):
            level -= 1
            if level == 0:
                return
    raise ValueError("Not enough commands to leave the proof.")


async def next_focus_command(cursor: RocqCursor) -> str | None:
    proof_state = await cursor.current_goal()
    if proof_state is None:
        raise ValueError("Not in a proof")
    if len(proof_state.focused_goals) != 0:
        raise ValueError("There are focused goals")
    res = await cursor.query("idtac.")
    assert isinstance(res, rdm_api.Err)
    no_such_goal = "No such goal."
    assert res.message.startswith(no_such_goal)
    if res.message == no_such_goal:
        return None
    reason = res.message.split()
    return "}" if reason[-2] != "bullet" else reason[-1][:-1]


async def try_solve_with_goal_cursor(
    cursor: DelimitedRocqCursor,
    try_solve_goal: Callable[[GoalRocqCursor], Awaitable[None]],
) -> None:
    proof_state = await cursor.current_goal()
    assert proof_state is not None
    needs_focus = len(proof_state.focused_goals) != 1
    if needs_focus:
        res = await cursor.insert_command("{")
        assert not isinstance(res, rdm_api.Err)
        await cursor.insert_blanks(" ")
    # Create an empty goal cursor.
    index = await cursor.cursor_index()
    goal_cursor = await GoalRocqCursor.make(cursor, start=index, count=0, clone=False)
    assert isinstance(goal_cursor, GoalRocqCursor)
    await try_solve_goal(goal_cursor)
    # Make sure the goal cursor has no trailing suffix.
    await goal_cursor.clear_suffix()
    # Close remaining sub-goals with admits.
    while not await goal_cursor.closed():
        proof_state = await goal_cursor.current_goal()
        assert proof_state is not None
        nb_focused = len(proof_state.focused_goals)
        if nb_focused != 0:
            # Close all focused goals.
            for _ in range(nb_focused):
                res = await goal_cursor.insert_command("admit.")
                assert not isinstance(res, rdm_api.Err)
        else:
            # No focused goal, figure out how to pop the stack.
            next_text = await next_focus_command(goal_cursor)
            assert next_text is not None
            await cursor.insert_blanks(" ")
            res = await goal_cursor.run_command(next_text)
    # Unfocus if needed.
    if needs_focus:
        await cursor.insert_blanks(" ")
        res = await cursor.insert_command("}")
        assert not isinstance(res, rdm_api.Err)


async def process_admitted_proof(
    cursor: DelimitedRocqCursor,
    try_solve_goal: Callable[[GoalRocqCursor], Awaitable[None]],
) -> bool:
    """
    Attempts to prove the admitted proof that is contained in `cursor`. It is
    expected that the cursor prefix starts with the statement, and that the
    last item of the cursor suffix is an `Admitted` command. If the function
    returns successfully, the cursor is placed after the closing command with
    no left-over commands in the suffix.
    """
    suffix = await cursor.doc_suffix()
    # Process the proof statement.
    assert len(suffix) != 0
    assert starts_proof(suffix.pop(0))
    res = await cursor.run_step()
    if isinstance(res, rdm_api.Err):
        raise ValueError("Invalid document (cannot process statement)")
    # Process the rest of the commands.
    for item in suffix:
        if starts_proof(item):
            await step_over_proof(cursor)
        elif ends_proof(item):
            # We must have reached the "Admitted".
            break
        elif is_admit(item):
            # Remove the admitted.
            await cursor.clear_suffix(count=1)
            # Try solving the goal.
            await try_solve_with_goal_cursor(cursor, try_solve_goal)
        else:
            res = await cursor.run_step()
            if isinstance(res, rdm_api.Err):
                raise ValueError("Invalid document (cannot process item)")
    assert len(await cursor.doc_suffix()) == 1
    # Solve remaining goals.
    while True:
        proof_state = await cursor.current_goal()
        assert proof_state is not None
        # Focused goal.
        if len(proof_state.focused_goals) > 0:
            for _ in proof_state.focused_goals:
                await try_solve_with_goal_cursor(cursor, try_solve_goal)
            continue
        # Unfocused goals.
        if sum(proof_state.unfocused_goals) > 0:
            next_text = await next_focus_command(cursor)
            assert next_text is not None
            await cursor.insert_blanks(" ")
            res = await cursor.run_command(next_text)
            assert not isinstance(res, rdm_api.Err)
            continue
        # Shelved goals.
        if proof_state.shelved_goals != 0:
            await cursor.insert_blanks(" ")
            res = await cursor.run_command("Unshelve.")
            assert not isinstance(res, rdm_api.Err)
            continue
        break
    # Try to replace the proof terminator by a "Qed".
    res = await cursor.insert_command("Qed.")
    if isinstance(res, rdm_api.Err):
        # Failure, we keep the "Admitted".
        res = await cursor.run_step()
        assert not isinstance(res, rdm_api.Err)
        return False
    else:
        # Success, clear the "Admitted" from the suffix.
        await cursor.clear_suffix()
        return True


async def run_proving_agent(
    rc: RocqCursor,
    agent_cls: AgentBuilder,
    output: Path,
    *,
    status: Controller,
    partial: bool = False,
) -> None:
    """Run the proving agent, delegating admitted proof tasks to agent_cls.

    Arguments:
        rc: the RocqCursor to use
        agent_cls: the AgentBuilder used to construct an Agent instance for each admitted proof task
        output: the Path where the result of the interaction should be committed
        partial (optional): whether or not the persist partial proof progress for each admitted proof task
    """
    suffix = await rc.doc_suffix()
    nb_admitted = sum(1 for item in suffix if is_admitted(item))

    if nb_admitted == 0:
        status.print("No admitted proofs.")
        return

    def show_count(n: int, name: str) -> str:
        return f"{n} {name}{'' if n == 1 else 's'}"

    status.print(
        f"Running the proving agent on {show_count(nb_admitted, 'admitted proof')}; "
        f"partial proofs will be {'retained' if partial else 'discarded'}."
    )

    nb_success = 0
    nb_failure = 0
    while True:
        # Get a cursor for the next admitted.
        cursor = await delimited_cursor_for_next_admitted(rc)
        if cursor is None:
            break

        # Try solving the admitted.
        async def try_solve_goal(goal_cursor: GoalRocqCursor) -> None:
            nonlocal status
            nonlocal agent_cls
            await run_prover_agent(agent_cls, goal_cursor, status=status)

        if await process_admitted_proof(cursor, try_solve_goal):
            nb_success += 1
        else:
            nb_failure += 1

    if nb_success != 0:
        status.print(f"Completed {show_count(nb_success, 'proof')}")
    if nb_failure != 0:
        status.print(f"Failed to complete {show_count(nb_success, 'proof')}")
    remaining = nb_admitted - nb_success - nb_failure
    if remaining != 0:
        status.print(f"Could not attempt {show_count(remaining, 'proof')}")

    await rc.commit(str(output), include_suffix=True)


async def run_prover_agent(
    agent_cls: AgentBuilder,
    rc: RocqCursor,
    *,
    status: Controller,
) -> None:
    """Use agent_cls to attempt the admitted proof task captured by the state of main_rc.

    Arguments:
        agent_cls: the AgentBuilder used to construct an Agent instance for the admitted proof task
        rc: the (shared) RocqCursor to use for the admitted proof task
        status: ...
    """
    await print_admitted_proof_task(rc)
    status.proof_visible(True)

    if status:

        def print_status(text: str, result: bool | None):
            nonlocal status
            if result is None:
                icon = "🔃"
            elif result:
                icon = "✅"
            else:
                icon = "❌"
            status.set_active(f"{icon} {text}")

        rc = await WatchingCursor.create(
            rc,
            on_start_command=lambda text: print_status(text, None),
            on_finish_command=lambda text, ok: print_status(text, ok),
            proof_script=lambda script: status.set_proof_script(script),
        )

    task_result = await agent_cls().run(rc=rc)

    # Print task_result and persistence
    if task_result.success:
        msg = "Agent succeeded"
    else:
        msg = "Agent failed"

    if task_result.message:
        status.print(f"{msg}:\n{task_result.message}")
    else:
        status.print(f"{msg}.")
    status.proof_visible(False)


async def try_replay(
    rc: RocqCursor,
    interaction: Sequence[rdm_api.PrefixItem],
    *,
    include_ghost: bool = True,
) -> bool:
    """Try to replay the interaction in rc.

    Arguments:
        rc: RocqCursor that will try to replay the interaction
        interaction: sequence of `rdm_api.PrefixItem`s
        include_ghost (optional): whether or not to include ghost interactions as comments
    Side Effect:
        rc: replay as much of the interaction as possible:
        - blanks: inserted as-is
        - commands:
          + ghost=False: inserted as-is, or as comments iff a previous insertion failed
          + ghost=True: inserted as comments; ignored iff include_ghost=False
    """
    for i, prefix_item in enumerate(interaction):
        if prefix_item.kind == "blanks":
            await rc.insert_blanks(text=prefix_item.text)
        elif prefix_item.kind == "ghost" and include_ghost:
            await rc.insert_blanks(text=f"(* {prefix_item.text} *)")
        elif prefix_item.kind == "command":
            insert_result = await rc.insert_command(text=prefix_item.text)

            if isinstance(insert_result, rdm_api.Err):
                await rc.insert_blanks(
                    text=(
                        "(*"
                        + prefix_item.text
                        + "".join(x.text for x in interaction[i + 1 :])
                        + "*)"
                    )
                )
                return False

    return True


async def print_admitted_proof_task(cursor: RocqCursor) -> None:
    """Print the admitted proof task captured by the state of main_rc."""

    goal = await cursor.current_goal()
    assert goal is not None
    position = await cursor.cursor_offset()
    print(
        f"\nFound admit at line {position.line + 1}, column {position.col} (offset={position.offset})."
    )
    for i, g in enumerate(goal.focused_goals):
        print(f"Goal {i}:{g.replace('\n', '\n  ')}")


def agent_main(agent_builder: AgentBuilder) -> int:
    parser = ArgumentParser(
        description="""Run a proof agent on the given Rocq source file.
        Extra configuration options can be passed to the agent after a '--'.
        Pass '-h' or '--help' after the '--' to get agent options.""",
        exit_on_error=False,
    )
    parser.add_argument(
        "rocq_file",
        metavar="ROCQ_FILE",
        type=valid_file(exists=True, allowed_suffixes=[".v"]),
        help="file in which to attempt proof completion",
    )
    parser.add_argument(
        "-o",
        "--output",
        metavar="OUTPUT",
        type=valid_file(check_creatable=True, allowed_suffixes=[".v"]),
        help="output file (default is the input file)",
    )
    parser.add_argument(
        "--no-partial",
        action="store_true",
        help="discard partial proofs",
    )
    parser.add_argument(
        "--progress",
        action=argparse.BooleanOptionalAction,
        help="show proof progress",
    )
    adapt_usage(parser, "agent")

    prover_args, agent_args = split_args()
    try:
        args = parser.parse_args(prover_args)
    except argparse.ArgumentError:
        parser.print_help()
        print()
        agent_builder.add_args(["--help"])
        return 0
    rocq_file = args.rocq_file
    if args.output is None:
        output: Path = rocq_file.name
    else:
        output = args.output
        if output.anchor == rocq_file.anchor:
            output = output.resolve()
    agent_builder.add_args(agent_args)
    logging.basicConfig(level=logging.ERROR)
    with build_ui(kind="tui" if args.progress else "status") as controller:
        try:
            controller.print("Gathering Rocq configuration...")
            rocq_args = rocq_args_for(rocq_file, cwd=rocq_file.parent, build=True)

            async def _run() -> None:
                controller.print("Loading file...")
                async with rc_sess(
                    str(rocq_file),
                    rocq_args=rocq_args,
                    cwd=str(rocq_file.parent),
                    dune=True,
                    load_file=True,
                ) as rc:
                    await run_proving_agent(
                        rc,
                        agent_builder,
                        output,
                        partial=not args.no_partial,
                        status=controller,
                    )

            asyncio.run(_run())
            return 0
        except DuneError as e:
            sys.exit(
                f"Error: could not find Rocq arguments for {rocq_file}.\n{e.stderr}"
            )
        except Exception as e:
            sys.exit(f"Error: failed with {e}.")


def auto_prover() -> int:
    return agent_main(AgentBuilder.of_agent(AutoAgent))
