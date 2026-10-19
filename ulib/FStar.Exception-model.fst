module FStar.Exception

(* Model implementation of FStar.Exception: verified, but never extracted.
   The real string_of_exn is OCaml's Printexc.to_string. *)
let string_of_exn _ = ""
