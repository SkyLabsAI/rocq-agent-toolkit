from contextlib import contextmanager, _GeneratorContextManager
from typing import Any, Callable, Iterator, Literal

from rocq_doc_manager import RocqDocManager


class RocqMacros:
    # TODO: these should be exposed directly within [RocqDocManager]
    class UPSTREAM:
        @staticmethod
        def insert_command(
                rdm: RocqDocManager,
                cmd: str,
        ) -> RocqDocManager.Resp | RocqDocManager.Err:
            return rdm.request("insert_command", [cmd])

        @staticmethod
        def command(
                rdm: RocqDocManager,
                cmd: str,
                insert: bool = False,
        ) -> RocqDocManager.Resp | RocqDocManager.Err:
            if insert:
                return RocqMacros.UPSTREAM.insert_command(rdm, cmd)
            else:
                return rdm.run_command(cmd)

        @staticmethod
        def get_feedback(
                rdm: RocqDocManager
        ) -> list[dict[str, Any]] | RocqDocManager.Err:
            feedback_reply = rdm.request("get_feedback", [])
            if isinstance(feedback_reply, RocqDocManager.Err):
                return feedback_reply
            return feedback_reply.result

        # TODO: cf. https://github.com/SkylabsAI/skylabs-fm/issues/86
        @staticmethod
        def text_query_all(
                rdm: RocqDocManager,
                cmd: str,
                insert: bool = False,
        ) -> list[str] | RocqDocManager.Err:
            cmd_reply = RocqMacros.UPSTREAM.command(rdm, cmd, insert=insert)
            if isinstance(cmd_reply, RocqDocManager.Err):
                return cmd_reply
            feedback_reply = RocqMacros.UPSTREAM.get_feedback(rdm)
            if isinstance(feedback_reply, RocqDocManager.Err):
                return feedback_reply
            return [
                feedback["text"]
                for feedback in feedback_reply
                if feedback["kind"].lower() in {"info", "notice"}
            ]

        @staticmethod
        def text_query(
                rdm: RocqDocManager,
                cmd: str,
                index: int = 1,
                insert: bool = False,
        ) -> str | RocqDocManager.Err:
            feedbacks = RocqMacros.UPSTREAM.text_query_all(
                rdm,
                cmd,
                insert=insert
            )
            if isinstance(feedbacks, RocqDocManager.Err):
                return feedbacks
            elif len(feedbacks) < index:
                return RocqDocManager.Err(
                    message=f"Index {index} out of bounds for feedback list",
                    data=feedbacks,
                )
            else:
                return feedbacks[index]

    @contextmanager
    @staticmethod
    def identity_ctx(rdm: RocqDocManager) -> Iterator[RocqDocManager]:
        yield rdm

    @contextmanager
    @staticmethod
    def rollback_ctx(rdm: RocqDocManager) -> Iterator[RocqDocManager]:
        current_idx: int = rdm.cursor_index()
        yield rdm
        revert_reply = rdm.revert_before(True, current_idx)
        if isinstance(revert_reply, RocqDocManager.Err):
            raise RuntimeError(" ".join([
                "RocqDocManager failed to rollback to",
                f"{current_idx}: {revert_reply}",
            ]))

    @staticmethod
    def ctx(
            rdm: RocqDocManager,
            rollback: bool = True,
    ) -> _GeneratorContextManager[RocqDocManager, None, None]:
        if rollback:
            return RocqMacros.rollback_ctx(rdm)
        else:
            return RocqMacros.identity_ctx(rdm)

    @contextmanager
    @staticmethod
    def aborted_goal_ctx(
            rdm: RocqDocManager,
            goal: str = "True",
            rollback: bool = True,
    ) -> Iterator[RocqDocManager]:
        with RocqMacros.ctx(rdm, rollback=rollback) as rdm_ctx:
            RocqMacros.UPSTREAM.command(
                rdm_ctx,
                f"Goal {goal}.",
                insert=not rollback,
            )
            yield rdm_ctx
            RocqMacros.UPSTREAM.command(
                rdm_ctx,
                "Abort.",
                insert=not rollback,
            )

    @staticmethod
    def import_export_cmd(
            rdm: RocqDocManager,
            kind: Literal["Import"] | Literal["Export"],
            logpath: str,
            require: bool = True,
            insert: bool = False,
            strict: bool = False,
    ) -> RocqDocManager.Err | None:
        cmd_str = f"{'Require ' if require else ''}{kind} {logpath}."
        reply = RocqMacros.UPSTREAM.command(rdm, cmd_str, insert=insert)
        if isinstance(reply, RocqDocManager.Err):
            if strict:
                raise RuntimeError("Failued to process [{cmd_str}]: {reply}")
            else:
                return reply
        else:
            return None

    @staticmethod
    def Import(
            rdm: RocqDocManager,
            logpath: str,
            require: bool = True,
            insert: bool = False,
            strict: bool = False,
    ) -> RocqDocManager.Err | None:
        return RocqMacros.import_export_cmd(
            rdm=rdm,
            kind="Import",
            logpath=logpath,
            require=require,
            insert=insert,
            strict=strict,
        )

    @staticmethod
    def Export(
            rdm: RocqDocManager,
            logpath: str,
            require: bool = True,
            insert: bool = False,
            strict: bool = False,
    ) -> RocqDocManager.Err | None:
        return RocqMacros.import_export_cmd(
            rdm=rdm,
            kind="Export",
            logpath=logpath,
            require=require,
            insert=insert,
            strict=strict,
        )

    @staticmethod
    def Compute(
            rdm: RocqDocManager,
            term: str,
            result_ctor_inj: str | None = None,
            rollback: bool = True,
    ) -> tuple[str, str]:
        """Run [Compute {term}.] and return the resulting value and type.

        Arguments:
            - mgr (RocqDocManager): the document manager to send the request to
            - term (str): the term to compute

        Raises:
            - RocqDocManager.Error: if inserting the requested command fails

        Returns:
            - a tuple containing:
                - the computed value
                - the type of the computed value
        """
        with RocqMacros.aborted_goal_ctx(
                rdm,
                goal=f"exists v, v = ({term})",
                rollback=rollback,
        ) as rdm_ctx:
            RocqMacros.UPSTREAM.command(
                rdm_ctx,
                "vm_compute.",
                insert=not rollback,
            )
            equality: str
            if result_ctor_inj is None:
                equality = "x = ?RESULT"
            else:
                equality = f"{result_ctor_inj} x = {result_ctor_inj} ?RESULT"
            RocqMacros.UPSTREAM.command(
                rdm_ctx,
                f"""match goal with
| |- context[@ex ?TY (fun x => {equality})] => idtac RESULT; idtac TY
end.
""",
                insert=not rollback,
            )
            feedback_reply = RocqMacros.UPSTREAM.get_feedback(rdm_ctx)
            if isinstance(feedback_reply, RocqDocManager.Err):
                raise RocqDocManager.Error(feedback_reply)
            feedback: list[dict[str, Any]] = feedback_reply

            if len(feedback) != 2:
                raise RocqDocManager.Error(
                    "expting a 2-tuple with the result+type of [Compute {term}]"
                )
            return (feedback[0]["text"], feedback[1]["text"])

    @staticmethod
    def fresh_ident(rdm: RocqDocManager, ident: str) -> str | RocqDocManager.Err:
        """Return a fresh name based on [ident].

        Arguments:
            - mgr (RocqDocManager): the document manager to send the request to
            - ident (str): the base for the fresh name

        Raises:
            - RocqDocManager.Error: if inserting the requested command fails.

        Returns:
            - a Rocq name which is guaranteed to be fresh at the
                  current loc. within [mgr]
        """
        return RocqMacros.UPSTREAM.text_query(
            rdm,
            f'Eval lazy in ltac:(let nm := fresh "{ident}" in idtac nm).'
        )
