module SeqPermutation
open Seq
open SeqProperties

let lemma_swap_permutes_aux s i j x =
  if j=i
  then cut (Eq (swap s i j) s)
  else
    let frag_lo = slice s 0 i in
    let frag_i = slice s i (i + 1) in
    let frag_mid = slice s (i + 1) j in
    let frag_j = slice s j (j + 1) in
    let frag_hi = slice s (j + 1) s.length in
    cut (Eq s            (append frag_lo (append frag_i (append frag_mid (append frag_j frag_hi)))));
    lemma_append_count_aux x frag_lo (append frag_i (append frag_mid (append frag_j frag_hi)));
    lemma_append_count_aux x frag_i (append frag_mid (append frag_j frag_hi));
    lemma_append_count_aux x frag_mid (append frag_j frag_hi);
    lemma_append_count_aux x frag_j frag_hi;
    cut (Eq (swap s i j) (append frag_lo (append frag_j (append frag_mid (append frag_i frag_hi)))));
    lemma_append_count_aux x frag_lo (append frag_j (append frag_mid (append frag_i frag_hi)));
    lemma_append_count_aux x frag_j (append frag_mid (append frag_i frag_hi));
    lemma_append_count_aux x frag_mid (append frag_i frag_hi);
    lemma_append_count_aux x frag_i frag_hi

opaque type permutation (a:Type) (s1:seq a) (s2:seq a) =
       (forall i. count i s1 = count i s2)

let lemma_swap_permutes s i j = Classical.forall_intro (lemma_swap_permutes_aux s i j)

