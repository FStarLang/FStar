module ElGamal.Group

open FStar.DM4F.Heap.Random
open FStar.DM4F.Random
type group = int

//assume type group : eqtype

assume val g: group

assume val (^): group -> int -> group

assume val ( * ): group -> group -> group

assume val log: group -> elem

assume val pow_log: a:group -> Lemma (g^(log a) == a)

assume val mul_pow: x:elem -> y:elem -> Lemma ((g^x) * (g^y) == g^((x + y) % q))


assume val mod_plus_minus: a:elem -> b:elem -> Lemma
  (requires True)
  (ensures  (((a + b) % q - b) % q == a))
  [SMTPat (((a + b) % q - b) % q)]

assume val mod_minus_plus: a:elem -> b:elem -> Lemma
  (requires True)
  (ensures  (((a - b) % q + b) % q == a))
  [SMTPat (((a - b) % q + b) % q)]
