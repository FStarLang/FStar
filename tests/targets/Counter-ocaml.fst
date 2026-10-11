module Counter

(* OcamlOnly only exists for the ocaml target. *)
let name = "ocaml"
let double x = OcamlOnly.twice x
