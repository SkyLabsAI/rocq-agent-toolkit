let print_args argv =
  for i = 1 to Array.length argv - 1 do
    if argv.(i) = "-topfile" || argv.(i-1) = "-topfile" then () else
    Printf.printf "%s\n%!" argv.(i)
  done

let _ =
  print_args Sys.argv
