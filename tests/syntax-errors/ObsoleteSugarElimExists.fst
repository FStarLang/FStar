module ObsoleteSugarElimExists
(* 'eliminate exists' no longer takes a 'returns' clause nor a hypothesis name. *)
let test (p:int -> prop) (_:squash (exists x. p x)) : squash True
  = eliminate exists x. p x
    returns True
    with pf. ()
