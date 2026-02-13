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

"""

from __future__ import annotations

import builtins
import dataclasses
import types
import typing
from collections.abc import Callable
from typing import Any, Protocol

# TODO: Maybe we could simply derive this entire file using pydantic serialization?


class TypeMismatch(Exception):
    pass


def assert_typevar(
    p: typing.TypeVar | typing.ParamSpec | typing.TypeVarTuple,
) -> typing.TypeVar:
    assert isinstance(p, typing.TypeVar)
    return p


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
        perform recursive decoding of subterms. May raise TypeMismatch"""
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
                    raise TypeMismatch
                return value
            case builtins.str | builtins.bool | builtins.int | builtins.float:
                assert params == []
                if not isinstance(value, ty):
                    raise TypeMismatch()
                return value
            case _ if dataclasses.is_dataclass(ty):
                # print("-> DataClassJsonMixin")
                if not isinstance(value, dict):
                    raise TypeMismatch()
                name = value.get("_ty", None)
                assert isinstance(ty, type)  # to silence type errors about [ty]
                if not name == ty.__name__:
                    raise TypeMismatch()
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
                    raise TypeMismatch()
                return [self.decode_rec(val, params[0], [], env) for val in value]
            case builtins.dict:
                assert len(params) == 2
                (key_ty, val_ty) = params
                if not isinstance(value, dict):
                    raise TypeMismatch()
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
                    except TypeMismatch:
                        # print(f"failed {o}")
                        continue
                raise TypeMismatch()
            case _:
                raise TypeMismatch()

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
    #     except TypeMismatch as e:
    #         print("type error!")
    #         raise e from e


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


class EncoderProtocol(Protocol):
    def encode(self, o: Any) -> Any:
        pass
