(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type source = Loc.source =
  | InFile of { dirpath : string option; file : string }
  | ToplevelInput

type t = Loc.t = {
  fname : source;
  line_nb : int;
  bol_pos : int;
  line_nb_last : int;
  bol_pos_last : int;
  bp : int;
  ep : int;
}

val to_yojson : t -> Yojson.Safe.t

val of_yojson : Yojson.Safe.t -> (t, string) result
