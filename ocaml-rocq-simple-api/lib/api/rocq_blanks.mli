(** Result of parsing blanks. *)
type t = {
  valid_until : int;
  (** Indicates the maximum offset until which the blanks are valid. *)
  stopped_at : int;
  (** Maximum index reached while processing the blanks. *)
  leading_whitespaces : bool;
  (** Indicates if processed blanks are prefixed with spacing character. *)
  unclosed_comments : int list;
  (** Indices of the opening character of unclosed (nested) comments. *)
  unclosed_string : int option;
  (** Index of the opening character of an unclosed string litteral. *)
}

(** [parse text ~offset] parses as many blank characters from [text], starting
    at index [offset]. The returned parsing data can be used to determine what
    amout of blanks can be successfully skipped, and to identify issues like a
    comment not being closed. *)
val parse : string -> offset:int -> t
