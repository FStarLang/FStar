open Printf


let generate_string (s:string) : string =
  let v = ref "" in
  for i = 0 to String.length s - 1 do
    v := !v ^ sprintf "0x%02xl; " (Char.code (String.get s i));
    if i mod 8 = 7 then v := !v ^ "\n"
  done;
  "createL [\n" ^ !v ^ "0l\n]\n"


let _ =
  let usage = sprintf
{| Generates a createL initializer from a string.contents

 Usage: %s string. |} Sys.argv.(0)  in
  let spec = Arg.align [] in
  let string_list:(string list) ref = ref [] in
  Arg.parse spec (fun s -> string_list := (!string_list)@[s]) usage;
  if List.length !string_list = 0 then printf "%s\n" usage;
  List.iter (fun s -> print_string (generate_string s)) !string_list
