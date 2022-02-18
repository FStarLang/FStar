module Part2.Connectives.Negation
open FStar.Classical.Sugar

let neg_intro #p (f:squash p -> squash False)
  : squash (~p)
  = admit()

let neg_elim #p #q (f:squash (~p)) (lem:unit -> Lemma p)
  : squash q
  = admit()
