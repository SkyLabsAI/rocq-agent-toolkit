type status = {
  valid_until : int;
  stopped_at : int;
  leading_whitespaces : bool;
  unclosed_comments : int list;
  unclosed_string : int option;
}

let skip_blanks : string -> offset:int -> status = fun text ~offset ->
  let len = String.length text in
  let rec skip state stack i =
    if i >= len then (state, stack, i) else
    match (state, text.[i], stack) with
    (* Blank characters (outside of comments) *)
    | (`Init, ' ' , []        )
    | (`Init, '\t', []        )
    | (`Init, '\r', []        )
    | (`Init, '\n', []        ) -> skip `Init stack (i+1)
    (* String literals (within comment) *)
    | (`Init, '"' , _ :: _    ) -> skip `Strg (i :: stack) (i+1)
    | (`Strg, '"' , _ :: stack) -> skip `Init stack (i+1)
    | (`Strg, _   , _         ) -> skip `Strg stack (i+1)
    (* Opening comment. *)
    | (`Init, '(' , _         ) -> skip `Open stack (i+1)
    | (`Open, '*' , _         ) -> skip `Init (i-1 :: stack) (i+1)
    | (`Open, _   , []        ) -> (`Init, stack, i - 1)
    | (`Open, '(' , _         ) -> skip `Open stack (i+1)
    | (`Open, '"' , _         ) -> skip `Strg stack (i+1)
    | (`Open, _   , _         ) -> skip `Init stack (i+1)
    (* End of blanks. *)
    | (`Init, _   , []        ) -> (`Init, stack, i)
    (* Closing comment. *)
    | (`Init, '*' , _ :: _    ) -> skip `Clos stack (i+1)
    | (`Clos, ')' , _ :: stack) -> skip `Init stack (i+1)
    | (`Clos, '*' , _         ) -> skip `Clos stack (i+1)
    | (`Clos, '"' , _         ) -> skip `Strg stack (i+1)
    | (`Clos, _   , _         ) -> skip `Init stack (i+1)
    (* Any other character in a comment. *)
    | (`Init, _   , _ :: _    ) -> skip `Init stack (i+1)
  in
  let (state, stack, stopped_at) = skip `Init [] offset in
  let (unclosed_string, unclosed_comments) =
    match (state, stack) with
    | (`Strg, []        ) -> assert false
    | (`Strg, i :: stack) -> (Some(i), List.rev stack)
    | (_    , _         ) -> (None   , List.rev stack)
  in
  let valid_until =
    match List.rev stack with
    | []     -> stopped_at
    | i :: _ -> i
  in
  let leading_whitespaces =
    offset < len &&
    match text.[offset] with
    | ' ' | '\t' | '\r' | '\n' -> true
    | _                        -> false
  in
  { valid_until; stopped_at; leading_whitespaces;
    unclosed_comments; unclosed_string }

let is_blanks : string -> bool = fun text ->
  (skip_blanks text ~offset:0).valid_until = String.length text
