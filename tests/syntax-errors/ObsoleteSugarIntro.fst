module ObsoleteSugarIntro
(* 'introduce _ ==> _' no longer binds a name for the hypothesis. *)
let test (p q:prop) (f:squash p -> squash q) : squash (p ==> q)
  = introduce p ==> q
    with h. f h
