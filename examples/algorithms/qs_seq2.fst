module QuickSort.Seq
open Seq

val count : 'a -> s:seq 'a -> Tot nat (decreases s.length)
let rec count x s = 
  if s.length = 0 then 0
  else if head s = x 
  then 1 + count x (tail s)
  else count x (tail s)

let mem x l = count x l > 0

val sorted: ('a -> 'a -> Tot bool) 
          -> s:seq 'a
          -> Tot bool (decreases (s.length))
let rec sorted f s =
  if s.length <= 1
  then true
  else let hd = head s in
       f hd (index s 1) && sorted f (tail s)

(* Defining a new predicate symbol *)
type total_order (a:Type) (f: (a -> a -> Tot bool)) =
    (forall a. f a a)                                           (* reflexivity   *)
    /\ (forall a1 a2. (f a1 a2 /\ a1<>a2)  <==> not (f a2 a1))  (* anti-symmetry *)
    /\ (forall a1 a2 a3. f a1 a2 /\ f a2 a3 ==> f a1 a3)        (* transitivity  *)

val swap: a:Type -> s:seq a -> i:nat{i<s.length} -> j:nat{j<s.length} -> Tot (seq a)
let swap s i j = upd i (index s j) (upd j (index s i) s)

opaque type permutation (a:Type) (s1:seq a) (s2:seq a) =
       (forall i. count i s1 = count i s2)

assume val lemma_swap_permutes: a:Type -> s:seq a -> i:nat{i<s.length} -> j:nat{j<s.length} -> Lemma (ensures (permutation a s (swap s i j)))
(* let lemma_swap_permutes s i j = () *)

assume val lemma_count_slice: a:Type -> s:seq a -> i:nat{i<=s.length} -> Lemma 
         (ensures (forall x. count x s = count x (slice s 0 i) + count x (slice s i s.length)))

assume val partition: f:('a -> 'a -> Tot bool){total_order 'a f}
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
                                 /\ (mem x lo ==> not(f p x))
                                 /\ (count x s = count x hi + count x lo)))
                     (fst res)
                     (snd res)
                     (index s pivot)))
         (decreases (back - pivot))
(* let rec partition f s pivot back = *)
(*   if pivot=back *)
(*   then (lemma_count_slice s pivot;  *)
        
(*         (slice s 0 pivot, slice s pivot s.length)) *)
(*   else let next = index s (pivot + 1) in *)
(*        let p = index s pivot in *)
(*        if f next p *)
(*        then let s' = swap s pivot (pivot + 1) in  (\* the pivot moves forward *\) *)
(*             let _ = lemma_swap_permutes s pivot (pivot + 1) in *)
(*             partition f s' (pivot + 1) back *)
(*        else let s' = swap s (pivot + 1) back in (\* the back moves backward *\) *)
(*             let _ = lemma_swap_permutes s (pivot + 1) back in *)
(*             let res = partition f s' pivot (back - 1) in  *)
(*             res *)



val lemma_append_count: a:Type -> lo:seq a -> hi:seq a
                    -> Lemma (requires True)
                             (ensures (forall x. count x (append lo hi) = (count x lo + count x hi)))
                             (decreases (lo.length))
let rec lemma_append_count lo hi =
  if lo.length = 0
  then cut (Eq (Seq.append lo hi) hi)
  else (cut (Eq (Seq.cons (head lo) (Seq.append (tail lo) hi))
                (Seq.append lo hi));
        lemma_append_count (tail lo) hi;
        let tl_l_h = Seq.append (tail lo) hi in
        let lh = Seq.cons (head lo) tl_l_h in
        cut (Eq (tail lh) tl_l_h))

val sorted_concat_lemma: a:Type
                      -> f:(a -> a -> Tot bool){total_order a f}
                      -> lo:seq a{sorted f lo}
                      -> pivot:a
                      -> hi:seq a{sorted f hi}
                      -> Lemma (requires (forall y. (mem y lo ==> not(f pivot y))
                                                 /\ (mem y hi ==> f pivot y)))
                               (ensures (sorted f (append lo (cons pivot hi))))
                               (decreases (lo.length))
                               (* [SMTPat  (sorted f (append lo (pivot::hi)))] *)
let rec sorted_concat_lemma f lo pivot hi =
  if lo.length = 0
  then (cut (Eq (append lo (cons pivot hi)) (cons pivot hi));
        cut (Eq (tail (cons pivot hi)) hi))
  else (sorted_concat_lemma f (tail lo) pivot hi;
        Seq.lemma_append_cons lo (cons pivot hi);
        Seq.lemma_tl (head lo) (append (tail lo) (cons pivot hi)))
        


val cons_perm: a:Type -> tl:seq a -> s:seq a{length s > 0} ->
         Lemma (requires (permutation a tl (tail s)))
               (ensures (permutation a (cons (head s) tl) s))
let cons_perm tl s = Seq.lemma_tl (head s) tl


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



