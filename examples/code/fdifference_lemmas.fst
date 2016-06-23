module FdifferenceLemmas

val helper_lemma_2_1:
  a:int -> b:int -> c:int -> d:int ->
  Lemma ((a+b)-(c+d) = a + b - c - d)
let helper_lemma_2_1 a b c d = ()

val helper_lemma_2_2:
  a:int -> b:int -> c:int -> d:int ->
  Lemma (a-c+b-d = a + b - c - d)
let helper_lemma_2_2 a b c d = ()

val helper_lemma_2:
  a:int -> b:int -> c:int -> d:int ->
  Lemma ((a-b)+(c-d) = (a+c) - (b+d))
let helper_lemma_2 a b c d = 
  helper_lemma_2_1 a c b d;
  helper_lemma_2_2 a c b d;
  helper_lemma_2_1 a c b d

val helper_lemma_3: a:nat -> len:nat -> Lemma (requires (len>=a /\ len-a<>0)) (ensures (a < len))
let helper_lemma_3 a len = ()

val helper_lemma_5: ctr:nat -> len:nat{len > ctr} ->
  Lemma (ensures (forall (i:nat). (i >= ctr /\ i < len) ==> (i = ctr \/ (i >= ctr+1 /\ i < len))))
let helper_lemma_5 ctr len = ()
