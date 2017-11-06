module Bug044

type nat =
  | O : nat
  | S : nat -> nat

val lemma : n:nat -> Lemma (ensures 0 < 42)
let lemma n =
  match n with
  | O -> admit()
  | S n' -> assert(False); admit()
