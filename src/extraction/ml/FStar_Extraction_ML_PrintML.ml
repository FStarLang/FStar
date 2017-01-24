open Pprintast
open FStar_Extraction_ML_Syntax


let print_symbol = print_string

let print_path (syms, sym) =
  let _ = List.map print_symbol syms in
  print_symbol sym

let print_sig = function
  Some (mlsig, mlmodule) -> print_string "c"
  | None -> print_string "d"

let print_module = failwith ""


let rec print = function
  l -> List.map (fun (path, opt_sig, lib) ->
                  let _ = print_path path in
                  let _ = print_sig opt_sig in
                  print lib) l

