module A

(* Without the [irreducible] qualifier, extracting B below diverges: the
   normalizer unfolds absurd () to absurd () to ... without bound. *)
irreducible
let rec absurd #_ _ = absurd ()
