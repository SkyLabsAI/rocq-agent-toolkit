(** [document_to_yojson d] gives a JSON representation of the current document
    state. It includes: the list of items that were already processed (prefix,
    items before the cursor), the list of remaining items (suffix, items after
    the cursor), and information about open goals if any. *)
val document_to_yojson : Document.t -> Yojson.Safe.t
