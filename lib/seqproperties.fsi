module SeqProperties
open Seq

val lemma_append_count: a:Type -> lo:seq a -> hi:seq a -> Lemma
         (requires True)
         (ensures (forall x. count x (append lo hi) = (count x lo + count x hi)))
         (decreases (lo.length))

val lemma_append_count_aux: a:Type -> x:a -> lo:seq a -> hi:seq a -> Lemma
         (requires True)
         (ensures (count x (append lo hi) = (count x lo + count x hi)))

val lemma_mem_inversion: a:Type -> s:seq a{s.length > 0} -> Lemma (ensures (forall x. mem x s = (x=head s || mem x (tail s))))

val lemma_mem_count: a:Type -> s:seq a -> f:(a -> Tot bool) -> Lemma
         (requires (forall (i:nat{i<s.length}). f (index s i)))
         (ensures (forall (x:a). mem x s ==> f x))
         (decreases (s.length))

val lemma_count_slice: a:Type -> s:seq a -> i:nat{i<=s.length} -> Lemma
         (requires True)
         (ensures (forall x. count x s = count x (slice s 0 i) + count x (slice s i s.length)))
         (decreases (s.length))

type total_order (a:Type) (f: (a -> a -> Tot bool)) =
    (forall a. f a a)                                           (* reflexivity   *)
    /\ (forall a1 a2. (f a1 a2 /\ a1<>a2)  <==> not (f a2 a1))  (* anti-symmetry *)
    /\ (forall a1 a2 a3. f a1 a2 /\ f a2 a3 ==> f a1 a3)        (* transitivity  *)

val sorted_concat_lemma: a:Type
                      -> f:(a -> a -> Tot bool){total_order a f}
                      -> lo:seq a{sorted f lo}
                      -> pivot:a
                      -> hi:seq a{sorted f hi}
                      -> Lemma (requires (forall y. (mem y lo ==> f y pivot)
                                                 /\ (mem y hi ==> f pivot y)))
                               (ensures (sorted f (append lo (cons pivot hi))))
                               (decreases (lo.length))
