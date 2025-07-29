(** Splitting Rocq Files Into Sentences

    This API calls the sentence splitter executable, so one does not have to
    deal fear corruption in Rocq's internal state. *)

(** [get_raw ~args ~file] calls the sentence splitter on [file], with the
    arguments [args], and returns the raw output (a string containing JSON
    data). In case of failure, an error message is given. *)
val get_raw : args:string list -> file:string -> (string, string) result

(** Type of JSON data. *)
type json = Yojson.Safe.t

(** [get_json ~args ~file] calls the sentence splitter on [file], with the
    arguments [args], and returns the parsed JSON output. In case of failure,
    an error message is given. *)
val get_json : args:string list -> file:string -> (json, json) result

(** Rocq sentence (a vernacular command, or a sequence of blank caracters. *)
type sentence = {
  kind : string;
  (** Sentence kind: "blanks", "synterp:<desc>", or "synpure:<desc>". *)
  text : string;
  (** Full text of the sentence. *)
  bp : int;
  (** Byte offset of the first character of the sentence in the file. *)
  ep : int;
  (** Byte offset of the first character after the sentence in the file. *)
}

(** Error. *)
type error = {
  message : string;
  loc : Rocq_loc.t option;
}

(** [get ~args ~file] calls the sentence splitter on [file], with the
    arguments [args], and returns the list of parsed sentences. In case of
    failure, an error is given. *)
val get : args:string list -> file:string -> (sentence list, error) result
