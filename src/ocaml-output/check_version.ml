let _ =
  let versions = [ "4.04.1"; "4.02.3" ] in
  if not (List.mem Sys.ocaml_version versions) then begin
    Printf.printf "The only supported OCaml versions are: %s\nPlease upgrade!\n" (String.concat ", " versions);
    exit 1
  end
