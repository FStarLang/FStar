(*--build-config
    options:--verify_module ModuloLemmas;
    other-files:axiomatic.fst intlib.fst lemmas.fst;
  --*)

module ModuloLemmas

open IntLib

val helper_lemma_0: ctr:nat -> Lemma ((ctr+2)-1 = ctr+1)
let helper_lemma_0 ctr = ()
val helper_lemma_1: ctr:nat -> Lemma ((ctr+1)-1 = ctr)
let helper_lemma_1 ctr = ()

val helper_lemma_2:
  pb:nat -> pc:pos -> a0:nat -> b:nat ->
  Lemma
    (requires (True))
    (ensures ((pb*pc) * a0/pc + (pb * (a0 % pc) + b) = pb * a0 + b))
let helper_lemma_2 pb pc a0 b = ()

val helper_lemma_3: a:int -> b:int -> c:int -> d:int -> 
  Lemma (requires (c = d /\ a - c = b - d))
	(ensures (a = b))
let helper_lemma_3 a b c d = ()	

val helper_lemma_4: a:nat -> b:nat -> c:pos -> size:pos{size > c} ->
  Lemma (requires (a < pow2 (size-1) /\ b < pow2 (size-c)))
	(ensures (a + b < pow2 size))
let helper_lemma_4 a b c size = 
  assert(a + b < pow2 (size-1) + pow2 (size - c)); 
  Lemmas.pow2_increases_2 (size-1) (size-c); 
  Lemmas.pow2_double_sum (size-1)

(* TODO : add axioms on congruences *)
assume val helper_lemma_5: a:nat -> b:nat -> c:nat -> p:pos -> 
  Lemma (requires (True))
	(ensures ( (a*b+c) % p = ((a % p) * b + c)%p))

val mod_lemma_1: a:nat -> b:pos -> Lemma (requires (a < b)) (ensures (a % b = a))
let mod_lemma_1 a b = ()
