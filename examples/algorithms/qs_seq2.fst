module QuickSort.Seq
open Seq
open SeqProperties
open SeqPermutation

val cons_perm: a:Type -> tl:seq a -> s:seq a{length s > 0} ->
         Lemma (requires (permutation a tl (tail s)))
               (ensures (permutation a (cons (head s) tl) s))
let cons_perm tl s = Seq.lemma_tl (head s) tl

(* Defining a new predicate symbol *)
type total_order (a:Type) (f: (a -> a -> Tot bool)) =
    (forall a. f a a)                                           (* reflexivity   *)
    /\ (forall a1 a2. (f a1 a2 /\ a1<>a2)  <==> not (f a2 a1))  (* anti-symmetry *)
    /\ (forall a1 a2 a3. f a1 a2 /\ f a2 a3 ==> f a1 a3)        (* transitivity  *)

opaque val partition: f:('a -> 'a -> Tot bool){total_order 'a f}
    -> s:seq 'a -> pivot:nat{pivot < s.length} -> back:nat{pivot <= back /\ back < s.length} ->
       Pure (seq 'a * seq 'a)
         (requires (forall (i:nat{i < s.length}).
                                 ((i <= pivot ==> f (index s i) (index s pivot))
                                  /\ (back < i  ==> f (index s pivot) (index s i)))))
         (ensures (fun res ->
                     (fun lo hi p ->
                         (lo.length + hi.length = s.length)
                      /\ (hi.length > 0)
                      /\ (index hi 0 = p)
                      /\ (forall x. (mem x hi ==> f p x)
                                 /\ (mem x lo ==> f x p)
                                 /\ (count x s = count x hi + count x lo)))
                     (fst res)
                     (snd res)
                     (index s pivot)))
         (decreases (back - pivot))
let rec partition f s pivot back =
  if pivot=back
  then (lemma_count_slice s pivot;
        let lo = slice s 0 pivot in
        let hi = slice s pivot s.length in
        lemma_mem_count lo (fun x -> f x (index s pivot));
        lemma_mem_count hi (f (index s pivot));
        (lo, hi))
  else let next = index s (pivot + 1) in
       let p = index s pivot in
       if f next p
       then let s' = swap s pivot (pivot + 1) in  (* the pivot moves forward *)
            let _ = lemma_swap_permutes s pivot (pivot + 1) in
            partition f s' (pivot + 1) back
       else let s' = swap s (pivot + 1) back in (* the back moves backward *)
            let _ = lemma_swap_permutes s (pivot + 1) back in
            let res = partition f s' pivot (back - 1) in
            res        

val sort: f:('a -> 'a -> Tot bool){total_order 'a f}
       -> s1:seq 'a
       -> Tot (s2:seq 'a{sorted f s2 /\ permutation 'a s1 s2})
              (decreases (s1.length))
let rec sort f s =
  if s.length <= 1 then s
  else let lo, hi = partition f s 0 (s.length - 1) in
       let pivot = head hi in

       let hi_tl = tail hi in
       let l = sort f lo in
       let h = sort f hi_tl in

       let result = Seq.append l (cons pivot h) in

       sorted_concat_lemma f l pivot h;
       lemma_append_count l (cons pivot h);
       cons_perm h hi;

       result



