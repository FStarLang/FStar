module ObsoleteSugarElimOr
(* 'eliminate _ \/ _' no longer takes a 'returns' clause nor hypothesis names. *)
let test (p q:prop) (_:squash (p \/ q)) : squash True
  = eliminate p \/ q
    returns True
    with x. ()
    and y. ()
