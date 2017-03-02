
(* TODO : this file does not have the same interface as platform.fsi *)

let exe name =
  if Sys.unix then
    name
  else
    name^".exe"

let is_fstar_compiler_using_ocaml = true
