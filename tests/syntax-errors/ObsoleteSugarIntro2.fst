module ObsoleteSugarIntro2
(* Same as ObsoleteSugarIntro, but here the obsolete form is a syntax error. *)
let test (p q:prop) (f:unit -> Lemma (requires p) (ensures q)) : squash (p ==> q)
  = introduce p ==> q
    with h. (f ())
