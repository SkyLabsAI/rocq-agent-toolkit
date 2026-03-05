"""This module provides type-driven deserialization. It supports
- Builtin types
- Literal[]
- Union[]
- Generics
- Dataclasses
- Any registered type

It avoids the need for creating unique identifiers for types.

It assumes that classes are encoded as dictionaries with an extra key that
contains the class' name (which does not need to be unique).

Types that need custom deserialization logic can register decoding functions in
`decoders`.

cf. ../cursor/websocket.py for an example use of the encoder/decoder
"""

#####################################################
### TODO: move this to a centralized utils module ###
#####################################################

from __future__ import annotations

import builtins
import dataclasses
import json
import pprint
import traceback
import types
import typing
from collections.abc import Callable, Sequence
from typing import Any, Protocol

from pydantic import BaseModel, ValidationError

from rocq_doc_manager import rocq_doc_manager_api as rdm_api

# TODO: Maybe we could simply derive this entire file using pydantic serialization?


def TypeMismatch(
    *,
    expected: type,
    actual: type | Any,
    infer_expectation: bool = True,
    notes: str | Sequence[str] | None = None,
) -> TypeError:
    e: TypeError

    if infer_expectation:
        if isinstance(actual, type):
            e = TypeError(
                f"expected type {expected.__qualname__} but got: {actual.__qualname__}"
            )
        else:
            e = TypeError(
                f"expected value of type {expected.__qualname__} but got: {repr(actual)}"
            )
    else:
        e = TypeError(
            f"expected type {expected.__qualname__} does not match: {repr(actual)}"
        )

    if notes is not None:
        if isinstance(notes, str):
            notes = [notes]
        for note in notes:
            e.add_note(note)

    return e


def assert_typevar(
    p: typing.TypeVar | typing.ParamSpec | typing.TypeVarTuple,
) -> typing.TypeVar:
    assert isinstance(p, typing.TypeVar)
    return p


class EncoderAPI(Protocol):
    def encode(self, o: Any) -> Any:
        pass


class Encoder(json.JSONEncoder, EncoderAPI):
    def default(self, o: Any):
        if isinstance(o, Exception):
            # Note: we can't easily (de)serialize Traceback objects so we instead
            # add the formatted traceback as a note.
            e_notes: list[str] = getattr(o, "__notes__", [])
            e_notes.extend(traceback.format_tb(o.__traceback__))

            return {
                "_ty": type(o).__qualname__,
                "args": list(map(super().encode, o.args)),
                "notes": list(getattr(o, "__notes__", [])),
            }
        elif isinstance(o, BaseModel):
            return o.model_dump()
        elif dataclasses.is_dataclass(type(o)):
            result = dataclasses.asdict(o)
            assert "_ty" not in result
            result["_ty"] = type(o).__qualname__
            return result
        else:
            return super().default(o)


encoder = Encoder()


class DecoderAPI(Protocol):
    type Val = Any
    type Ty = Any  # we would like to use [type Ty = type] but special types
    # such as [Literal] and [Union] are not [type]s

    type Env = dict[typing.TypeVar, Ty]
    type Params = list[Ty]

    """The type of generic decoders"""
    type DecoderFn = Callable[[Any, Ty, Params, Env], Any]

    """The type of registered decoders. Unlike the generic decoder, registered
    decoders receive a generic decoder as their first argument.

    """
    type RegisteredFn = Callable[[DecoderFn, Val, Ty, Params, Env], Any]

    def add_decoder(self, ty: Ty, decoder: RegisteredFn) -> None:
        """Add decoder function dec for type ty to be used automatically be decode"""
        ...

    def add_decoders(self, decoders: dict[Ty, RegisteredFn]) -> None:
        """Add multiple decoders at once"""
        for ty, fn in decoders.items():
            self.add_decoder(ty, fn)

    def decode_rec(self, value: Val, ty: Ty, params: Params, env: Env) -> Any:
        """Does the actual decoding work and can be used in registered decoders to
        perform recursive decoding of subterms. May raise TypeError"""
        ...

    def decode(self, value: Val, ty: Ty) -> Any:
        """Wrapper around decode_rec that starts decoding with an empty list of parameters and an empty type environment"""
        return self.decode_rec(value, ty, [], {})


class Decoder(DecoderAPI):
    decoders: dict[type, DecoderAPI.RegisteredFn] = {}

    def add_decoder(self, ty: DecoderAPI.Ty, decoder: DecoderAPI.RegisteredFn):
        self.decoders[ty] = decoder

    def decode_rec(
        self,
        value: DecoderAPI.Val,
        ty: DecoderAPI.Ty,
        params: DecoderAPI.Params,
        env: DecoderAPI.Env,
    ) -> Any:
        def _TypeMismatch(*, notes: str | Sequence[str] | None = None) -> TypeError:
            return TypeMismatch(expected=ty, actual=value, notes=notes)

        if ty in self.decoders:
            # print(f"decoder found for {ty}")
            return self.decoders[ty](self.decode_rec, value, ty, params[:], env)
        args = typing.get_args(ty)
        # print(f"origin: {origin}")
        # print(f"args: {args}")
        # print(repr(ty))
        # print(isinstance(ty, type) and isinstance(ty, types.UnionType))
        match ty:
            # invariant: all parameters are in [params]
            case _ if args != ():
                # print("-> Generic")
                assert params == []
                origin = typing.get_origin(ty)
                assert origin is not None
                params = list(typing.get_args(ty))
                return self.decode_rec(value, origin, params, env)
            # zero parameters
            case typing.TypeVar():
                assert params == []
                var = env.get(ty, None)
                assert ty is not None
                assert var != ty, f"TypeVar {var} maps to itself"
                return self.decode_rec(value, env[ty], params, env)
            case typing.Literal:
                # print("-> Literal")
                return value
            case typing.Any:
                # print("-> Any")
                assert params == []
                return value
            case types.NoneType:
                # print("-> NoneType")
                assert params == []
                if value is not None:
                    raise _TypeMismatch()
                return value
            case builtins.str | builtins.bool | builtins.int | builtins.float:
                assert params == []
                if not isinstance(value, ty):
                    raise _TypeMismatch()
                return value
            case _ if isinstance(ty, type) and issubclass(ty, BaseModel):
                # print("-> BaseModel")
                try:
                    return ty.model_validate(value, strict=True, extra="forbid")
                except ValidationError as e:
                    notes = [pprint.pformat(error) for error in e.errors()]
                    raise _TypeMismatch(notes=notes) from e
            case _ if dataclasses.is_dataclass(ty):
                # print("-> DataClassJsonMixin")
                if not isinstance(value, dict):
                    raise _TypeMismatch()
                name = value.get("_ty", None)
                assert isinstance(ty, type)  # to silence type errors about [ty]
                if not name == ty.__name__:
                    raise _TypeMismatch()
                del value["_ty"]
                params_expected = list(map(assert_typevar, ty.__type_params__))
                assert len(params_expected) == len(params)
                subst = dict(zip(params_expected, params, strict=True))
                env = dict(env)
                env.update(subst)
                fields = dataclasses.fields(ty)
                field_types = typing.get_type_hints(ty)
                kwargs = {}
                for field in fields:
                    # print(repr(field))
                    # print(f"original field: {repr(field.type)}")
                    # print(f"original annot: {field_types[field.name]}")
                    field_ty = field_types[field.name]
                    # print(f"substituted: {repr(ty)}")
                    # todo default values
                    kwargs[field.name] = self.decode_rec(
                        value[field.name], field_ty, [], env
                    )
                return ty(**kwargs)
            # fixed number of parameters
            case builtins.list:
                # print("-> List")
                assert len(params) == 1
                if not isinstance(value, list):
                    raise _TypeMismatch()
                return [self.decode_rec(val, params[0], [], env) for val in value]
            case builtins.dict:
                assert len(params) == 2
                (key_ty, val_ty) = params
                if not isinstance(value, dict):
                    raise _TypeMismatch()
                return {
                    self.decode_rec(k, key_ty, [], env): self.decode_rec(
                        v, val_ty, [], env
                    )
                    for k, v in value.items()
                }
            # dynamic arity
            case typing.Union | types.UnionType:
                # print("-> UnionType")
                for o in params:
                    try:
                        # print(f"trying {o}")
                        return self.decode_rec(value, o, [], env)
                    except TypeError:
                        # print(f"failed {o}")
                        continue
                raise _TypeMismatch()
            case _:
                raise _TypeMismatch()

    # Uncomment code below for debug output

    # decode_rec_orig = decode_rec
    # def decode_rec(self, value, ty, params, env):
    #     print(f"value: {value}")
    #     print(f"ty: {ty}")
    #     print("params:", " ,".join(map(repr, params)))
    #     print(f"env: {env}")
    #     try:
    #         result = self.decode_rec_orig(value, ty, params, env)
    #         print(f"result: {repr(result)}")
    #         return result
    #     except TypeError as e:
    #         print("type error!")
    #         raise


decoder = Decoder()


def decode_exception(decode, payload, ty, params, env) -> Exception:
    KNOWN_CUSTOM_EXCEPTION_TYPES: dict[str, type[Exception]] = {
        rdm_api.Error.__qualname__: rdm_api.Error,
    }

    assert params == []
    match payload:
        case {
            "_ty": e_ty,
            "args": e_args,
            "notes": e_notes,
        }:

            def _early_Exception(msg: str) -> Exception:
                e = Exception(msg)
                e.add_note(f"e_ty: {repr(e_ty)}")
                e.add_note(f"e_args: {repr(e_args)}")
                e.add_note(f"e_notes: {repr(e_notes)}")
                return e

            # 0. sanity-check serialized data
            for guard_thunk, msg in [
                (lambda: isinstance(e_ty, str), "e_ty is not a string"),
                (lambda: isinstance(e_args, Sequence), "e_args is not a Sequence"),
                (lambda: isinstance(e_notes, Sequence), "e_notes is not a Sequence"),
                (
                    lambda: all(isinstance(note, str) for note in e_notes),
                    "e_notes is not a Sequence[str]",
                ),
            ]:
                if not guard_thunk():
                    return _early_Exception(msg)

            e: Exception | None = None

            # 1. Try custom exceptions first, annotating in case of failure
            if e_ty in KNOWN_CUSTOM_EXCEPTION_TYPES:
                try:
                    e = KNOWN_CUSTOM_EXCEPTION_TYPES[e_ty](*e_args)
                except Exception:
                    e_notes.append(traceback.format_exc())

            # 2. Gracefully fall back to a plain Exception, annotating if the fall back
            #    was caused by a failure to use a more specific exception type.
            if e is None:
                if e_ty in KNOWN_CUSTOM_EXCEPTION_TYPES:
                    # Note: we must have raised an error in (1) after trying to use the more specific type
                    e_notes.append(f"Fallback to Exception from {e_ty}")
                e = Exception(*e_args)

            # 3. Setup notes & return the error object
            #
            # Note: original traceback is stored in notes
            assert e is not None
            for note in e_notes:
                e.add_note(note)
            return e
        case _:
            raise TypeMismatch(
                expected=ty,
                actual=payload,
                infer_expectation=False,
                notes="decode_exception from raw payload",
            )


decoder.add_decoders(
    {
        Exception: decode_exception,
    }
)


class UnguidedDecoder:
    """Ad-hoc, extensible json decoding support for objects without an expected
    type. Used only for exceptions."""

    type DecoderFn = Callable[[Any], Any]
    decoders: dict[str, DecoderFn] = {}

    def object_hook(self, obj: dict[str, Any]):
        match obj.get("_ty", None):
            case None:
                return obj
            case ty:
                del obj["_ty"]
                return self.decoders[ty](obj)

    def add_decoder(self, ty: Any, decoder: DecoderFn):
        self.decoders[ty] = decoder

    def add_decoders(self, decoders: dict[Any, DecoderFn]) -> None:
        for ty, fn in decoders.items():
            self.add_decoder(ty, fn)


unguided_decoder = UnguidedDecoder()


def ug_decode_exception(payload: Any) -> Exception:
    match payload:
        case {"args": args}:
            return Exception(*args)
        case _:
            raise TypeMismatch(
                expected=Exception,
                actual=payload,
                infer_expectation=False,
                notes="ug_decode_exception from raw payload",
            )


unguided_decoder.add_decoder("Exception", ug_decode_exception)
