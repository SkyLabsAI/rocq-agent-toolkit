(** Splitting Rocq Files Into Sentences

    Note that this library can only work on a single file, specified via the
    [argv] parameter of the [init] function. *)

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

(** [sentence_to_yojson sentence] turns [sentence] into JSON data. *)
val sentence_to_yojson : sentence -> Yojson.Safe.t

(** [sentence_of_yojson json] attempts to turns [json] into a sentence, or
    give an error message. *)
val sentence_of_yojson : Yojson.Safe.t -> (sentence, string) result

(** Internal, imperative state of the library. *)
type state

(** [init ~argv] initializes the library. The [args] argument gives the Rocq
    command line arguments with which to run, including the file to split. The
    function can currently only be called once in a given program. In case of
    initialization error, an error message is returned. *)
val init : argv:string array -> (state, string) result

(** [get_file state] gives the path to the file on which the library has been
    initialized. *)
val get_file : state -> string

(** [get_dirpath state] gives the Rocq directory path corresponding to the
    file on which the library has been initialized. *)
val get_dirpath : state -> Names.DirPath.t

(** List of Rocq feedback items. *)
type feedback = Feedback.feedback list

(** Optional Rocq source code location. *)
type loc = Loc.t option

(** [get state] splits the current contents of the file the library has been
    initialized on into sentences. Feedback from Rocq is also provided, and
    a location and error message is given in case of parse error. *)
val get : state -> (sentence list, loc * string) result * feedback
