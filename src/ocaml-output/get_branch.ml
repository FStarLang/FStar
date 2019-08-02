let starts_with (input: string) (prefix: string) =
  let len_prefix = String.length prefix in
  String.length input >= len_prefix &&
  String.sub input 0 len_prefix = prefix
  
let _ =
  let version = Sys.ocaml_version in
  let check_version x = starts_with (version ^ ".") (x ^ ".") in
  let rec find_branch = function
    | [] -> failwith ("Unsupported version of OCaml:" ^ version)
    | v :: q -> if check_version v then v ^ ".X" else find_branch q
  in
  let branch = find_branch ["4.02"; "4.04"; "4.05"; "4.06"; "4.07"] in
  print_endline branch
