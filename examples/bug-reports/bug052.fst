module Bug052

val trivial_a: x:nat -> y:nat -> Lemma (x + y = y + x)
let trivial_a x y = ()

val trivial_b: x:nat -> y:nat -> Lemma (x + y = y + x)
let trivial_b x y = trivial_a x y

val trivial_c: x:nat -> y:nat -> Lemma (x + y = y + x)
let trivial_c x y = trivial_a x y

val use_fact_and_lemma: x:nat -> y:nat -> Tot nat
let use_fact_and_lemma x y =
  trivial_c x y;
  trivial_a x y;
  let _ = trivial_b x in
  x + y

val test: unit -> Tot unit
let test () = assert (use_fact_and_lemma 0 1 = 1)
