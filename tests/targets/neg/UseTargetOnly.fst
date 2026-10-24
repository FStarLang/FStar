module UseTargetOnly

(* OcamlOnly only exists for the ocaml target: invisible to common code. *)
let y = OcamlOnly.twice 1
