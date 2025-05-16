open Ltac2_plugin

type deriver = Tac2expr.type_constant list -> Tac2expr.strexpr list

val register_deriver : string -> deriver -> unit

val list_derivers : unit -> unit

val derive : Attributes.vernac_flags -> Names.Id.t list ->
    Libnames.qualid list -> unit
