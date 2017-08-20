let _ =
  let branch = String.sub Sys.ocaml_version 0 (String.rindex Sys.ocaml_version '.') ^ ".X" in
  if not (List.mem branch ["4.02.X"; "4.04.X"; "4.05.X"]) then
    failwith ("Unsupported version of OCaml:" ^ Sys.ocaml_version);
  print_endline branch
