module FStar.Exception

(* This function is uninterpreted and will not evaluate in the
normalizer. It is extracted to OCaml's Printexc.to_string. It
can also be used from tactic plugins. *)
val string_of_exn : exn -> string
