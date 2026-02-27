include Rocq_split_data

let run_raw : config -> res = fun config ->
  let prog = "rocq-split.private" in
  let (ic, oc) = Unix.open_process_args prog [|prog|] in
  Marshal.to_channel oc config [];
  Out_channel.flush oc;
  let res = Marshal.from_channel ic in
  ignore (Unix.close_process (ic, oc));
  res

type res = (split_data, string * split_error) result

let get_sentences : config -> command list -> Rocq_loc.t option ->
    sentence list = fun config cmds loc ->
  let with_stream f =
    match config.contents with
    | None           ->
        let run ic =
          let input_char () = In_channel.input_char ic in
          let input_all () = In_channel.input_all ic in
          f (input_char, input_all)
        in
        In_channel.with_open_text config.file run
    | Some(contents) ->
        let len = String.length contents in
        let pos = ref 0 in
        let input_char () =
          match !pos < len with
          | false -> None
          | true  -> let c = contents.[!pos] in incr pos; Some(c)
        in
        let input_all () =
          let off = !pos in
          pos := len;
          String.sub contents off (len - off)
        in
        f (input_char, input_all)
  in
  with_stream @@ fun (input_char, input_all) ->
  let cur_offset = ref 0 in
  let buf = Buffer.create 73 in
  let rev_items = ref [] in
  let add_blanks text bp ep =
    let item = {kind = `Blanks; text; bp; ep} in
    rev_items := item :: !rev_items
  in
  let add_command cmd Loc.{bp; ep; _} text =
    let item = {kind = `Command(cmd); text; bp; ep} in
    rev_items := item :: !rev_items
  in
  let handle_cmd cmd =
    let loc = Option.get cmd.CAst.loc in
    (* Parse blanks up to the beginning position. *)
    Buffer.clear buf;
    let bp = !cur_offset in
    while !cur_offset < loc.Loc.bp do
      incr cur_offset;
      match input_char () with
      | None   -> invalid_arg "position error xxx"
      | Some c -> Buffer.add_char buf c
    done;
    let blanks = Buffer.contents buf in
    if blanks <> "" then add_blanks blanks bp !cur_offset;
    (* Parse the actual command. *)
    Buffer.clear buf;
    while !cur_offset < loc.Loc.ep do
      incr cur_offset;
      match input_char () with
      | None   -> invalid_arg "position error yyy"
      | Some c -> Buffer.add_char buf c
    done;
    add_command cmd loc (Buffer.contents buf)
  in
  List.iter handle_cmd cmds;
  let _ =
    match loc with
    | Some(_) -> ()
    | None    ->
    match input_all () with
    | ""   -> ()
    | text -> add_blanks text !cur_offset (!cur_offset + String.length text)
  in
  List.rev !rev_items

let run : config -> res = fun config ->
  let res = run_raw config in
  match res.result with
  | Ok(dirpath)    ->
      let sentences = get_sentences config res.commands None in
      Ok({dirpath; sentences})
  | Error(s, None) ->
      assert (res.commands = []);
      Error(s, {parsed_sentences = []; error_loc = None})
  | Error(s, loc ) ->
      let parsed_sentences = get_sentences config res.commands loc in
      Error(s, {parsed_sentences; error_loc = loc})

let split_file : file:string -> args:string list -> res = fun ~file ~args ->
  run {file; args; contents = None}

let split_string : file:string -> args:string list -> string -> res =
    fun ~file ~args contents ->
  run {file; args; contents = Some(contents)}
