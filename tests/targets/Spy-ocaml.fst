module Spy

(* A target-specific file can befriend the implementation of its target. *)
friend Counter

let name_is_ocaml () = ()
