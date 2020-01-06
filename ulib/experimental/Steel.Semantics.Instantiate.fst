module Steel.Semantics.Instantiate

friend Steel.Memory

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

let associative () : Lemma (S.associative equiv star)
= Classical.forall_intro_3 star_associative

let commutative () : Lemma (S.commutative equiv star)
= Classical.forall_intro_2 star_commutative

let is_unit () : Lemma (S.is_unit emp equiv star)
= let aux (y:hprop) : Lemma (star emp y `equiv` y /\ star y emp `equiv` y)
    = emp_unit y; star_commutative emp y
  in
  Classical.forall_intro aux

let state_obeys_st_laws () = associative (); commutative (); is_unit ()
