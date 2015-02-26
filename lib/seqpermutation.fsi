module SeqPermutation
open Seq
open SeqProperties

val lemma_swap_permutes_aux: a:Type -> s:seq a -> i:nat{i<s.length} -> j:nat{i <= j && j<s.length} -> x:a -> Lemma
  (requires True)
  (ensures (count x s = count x (swap s i j)))

opaque type permutation (a:Type) (s1:seq a) (s2:seq a) =
       (forall i. count i s1 = count i s2)

val lemma_swap_permutes: a:Type -> s:seq a -> i:nat{i<s.length} -> j:nat{i <= j && j<s.length} -> Lemma
  (permutation a s (swap s i j))

val cons_perm: a:Type -> tl:seq a -> s:seq a{length s > 0} ->
         Lemma (requires (permutation a tl (tail s)))
               (ensures (permutation a (cons (head s) tl) s))

