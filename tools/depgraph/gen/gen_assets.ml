(* Generates an OCaml module holding the viewer assets as string constants,
   so that the tool ships as a single self-contained executable. *)

let ident_of_file (f : string) : string =
  let b = Filename.basename f in
  String.map (fun c -> if c = '.' || c = '-' then '_' else c) (String.lowercase_ascii b)

let read (f : string) : string =
  let ic = open_in_bin f in
  let n = in_channel_length ic in
  let s = really_input_string ic n in
  close_in ic; s

let () =
  print_string "(* generated from tools/depgraph/assets - do not edit *)\n";
  for i = 1 to Array.length Sys.argv - 1 do
    let f = Sys.argv.(i) in
    Printf.printf "let %s = \"%s\"\n" (ident_of_file f) (String.escaped (read f))
  done
