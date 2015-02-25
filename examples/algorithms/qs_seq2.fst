module QuickSort.Seq
open Seq

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

opaque type permutation (a:Type) (s1:seq a) (s2:seq a) =
       (forall i. count i s1 = count i s2)

(* val split_i: a:Type -> s:seq a -> i:nat{i<s.length} -> Pure (seq a * seq a)  *)
(*   (requires True) *)
(*   (ensures (fun res ->  *)
(*     (fun s1 s2 -> s1=slice s 0 i /\ s2=slice s i s.length /\ s=append s1 s2) *)
(*     (fst res) (snd res))) *)
(* let split_i s i =  *)
(*   let f = slice s 0 i in  *)
(*   let g = slice s i s.length in  *)
(*   cut (Eq s (append f g)); *)
(*   (f, g) *)

assume val lemma_swap_permutes_aux: a:Type -> s:seq a -> i:nat{i<s.length} -> j:nat{i <= j && j<s.length} -> x:a -> Lemma
  (requires True)
  (ensures (count x s = count x (swap s i j)))
(* let lemma_swap_permutes s i j x = *)
(*   if j=i *)
(*   then cut (Eq (swap s i j) s) *)
(*   else *)
(*     let frag_lo = slice s 0 i in *)
(*     let frag_i = slice s i (i + 1) in *)
(*     let frag_mid = slice s (i + 1) j in *)
(*     let frag_j = slice s j (j + 1) in *)
(*     let frag_hi = slice s (j + 1) s.length in *)
(*     cut (Eq s            (append frag_lo (append frag_i (append frag_mid (append frag_j frag_hi))))); *)
(*     lemma_append_count x frag_lo (append frag_i (append frag_mid (append frag_j frag_hi))); *)
(*     lemma_append_count x frag_i (append frag_mid (append frag_j frag_hi)); *)
(*     lemma_append_count x frag_mid (append frag_j frag_hi); *)
(*     lemma_append_count x frag_j frag_hi; *)
(*     cut (Eq (swap s i j) (append frag_lo (append frag_j (append frag_mid (append frag_i frag_hi))))); *)
(*     lemma_append_count x frag_lo (append frag_j (append frag_mid (append frag_i frag_hi))); *)
(*     lemma_append_count x frag_j (append frag_mid (append frag_i frag_hi)); *)
(*     lemma_append_count x frag_mid (append frag_i frag_hi); *)
(*     lemma_append_count x frag_i frag_hi *)

val lemma_swap_permutes: a:Type -> s:seq a -> i:nat{i<s.length} -> j:nat{i <= j && j<s.length} -> Lemma
  (permutation a s (swap s i j))
let lemma_swap_permutes s i j = Classical.forall_intro (lemma_swap_permutes_aux s i j)
(* assume val lemma_count_slice: a:Type -> s:seq a -> i:nat{i<=s.length} -> Lemma  *)
(*          (requires True) *)
(*          (ensures (forall x. count x s = count x (slice s 0 i) + count x (slice s i s.length))) *)
(*          (decreases (s.length)) *)
(* (\* let lemma_count_slice s i = *\) *)
(* (\*   cut (Eq s (append (slice s 0 i) (slice s i s.length))); *\) *)
(* (\*   lemma_append_count (slice s 0 i) (slice s i s.length) *\) *)


(* (\* unused *\)val lemma_mem_inversion: a:Type -> s:seq a{s.length > 0} -> Lemma (ensures (forall x. mem x s = (x=head s || mem x (tail s)))) *)
(* let lemma_mem_inversion s = () *)

(* val lemma_mem_count: a:Type -> s:seq a -> f:(a -> Tot bool) -> Lemma *)
(*          (requires (forall (i:nat{i<s.length}). f (index s i))) *)
(*          (ensures (forall (x:a). mem x s ==> f x)) *)
(*          (decreases (s.length)) *)
(* let rec lemma_mem_count s f = *)
(*   if s.length = 0 *)
(*   then () *)
(*   else (cut (forall (i:nat{i<length (tail s)}). index (tail s) i = index s (i + 1)); *)
(*         lemma_mem_count (tail s) f) *)

         
(* (\* opaque val partition: f:('a -> 'a -> Tot bool){total_order 'a f} *\) *)
(* (\*     -> s:seq 'a -> pivot:nat{pivot < s.length} -> back:nat{pivot <= back /\ back < s.length} -> *\) *)
(* (\*        Pure (seq 'a * seq 'a) *\) *)
(* (\*          (requires (forall (i:nat{i < s.length}). *\) *)
(* (\*                                  ((i <= pivot ==> f (index s i) (index s pivot)) *\) *)
(* (\*                                   /\ (back < i  ==> f (index s pivot) (index s i))))) *\) *)
(* (\*          (ensures (fun res -> *\) *)
(* (\*                      (fun lo hi p -> *\) *)
(* (\*                          (lo.length + hi.length = s.length) *\) *)
(* (\*                       /\ (hi.length > 0) *\) *)
(* (\*                       /\ (index hi 0 = p) *\) *)
(* (\*                       /\ (forall x. (mem x hi ==> f p x) *\) *)
(* (\*                                  /\ (mem x lo ==> f x p) *\) *)
(* (\*                                  /\ (count x s = count x hi + count x lo))) *\) *)
(* (\*                      (fst res) *\) *)
(* (\*                      (snd res) *\) *)
(* (\*                      (index s pivot))) *\) *)
(* (\*          (decreases (back - pivot)) *\) *)
(* (\* let rec partition f s pivot back = *\) *)
(* (\*   if pivot=back *\) *)
(* (\*   then (lemma_count_slice s pivot; *\) *)
(* (\*         let lo = slice s 0 pivot in  *\) *)
(* (\*         let hi = slice s pivot s.length in  *\) *)
(* (\*         lemma_mem_count lo (fun x -> f x (index s pivot)); *\) *)
(* (\*         lemma_mem_count hi (f (index s pivot)); *\) *)
(* (\*         (lo, hi)) *\) *)
(* (\*   else let next = index s (pivot + 1) in *\) *)
(* (\*        let p = index s pivot in *\) *)
(* (\*        if f next p *\) *)
(* (\*        then let s' = swap s pivot (pivot + 1) in  (\\* the pivot moves forward *\\) *\) *)
(* (\*             let _ = lemma_swap_permutes s pivot (pivot + 1) in *\) *)
(* (\*             partition f s' (pivot + 1) back *\) *)
(* (\*        else let s' = swap s (pivot + 1) back in (\\* the back moves backward *\\) *\) *)
(* (\*             let _ = lemma_swap_permutes s (pivot + 1) back in *\) *)
(* (\*             let res = partition f s' pivot (back - 1) in *\) *)
(* (\*             res *\) *)




(* (\* val sorted_concat_lemma: a:Type *\) *)
(* (\*                       -> f:(a -> a -> Tot bool){total_order a f} *\) *)
(* (\*                       -> lo:seq a{sorted f lo} *\) *)
(* (\*                       -> pivot:a *\) *)
(* (\*                       -> hi:seq a{sorted f hi} *\) *)
(* (\*                       -> Lemma (requires (forall y. (mem y lo ==> f y pivot) *\) *)
(* (\*                                                  /\ (mem y hi ==> f pivot y))) *\) *)
(* (\*                                (ensures (sorted f (append lo (cons pivot hi)))) *\) *)
(* (\*                                (decreases (lo.length)) *\) *)
(* (\*                                (\\* [SMTPat  (sorted f (append lo (pivot::hi)))] *\\) *\) *)
(* (\* let rec sorted_concat_lemma f lo pivot hi = *\) *)
(* (\*   if lo.length = 0 *\) *)
(* (\*   then (cut (Eq (append lo (cons pivot hi)) (cons pivot hi)); *\) *)
(* (\*         cut (Eq (tail (cons pivot hi)) hi)) *\) *)
(* (\*   else (sorted_concat_lemma f (tail lo) pivot hi; *\) *)
(* (\*         Seq.lemma_append_cons lo (cons pivot hi); *\) *)
(* (\*         Seq.lemma_tl (head lo) (append (tail lo) (cons pivot hi))) *\) *)
        


(* (\* val cons_perm: a:Type -> tl:seq a -> s:seq a{length s > 0} -> *\) *)
(* (\*          Lemma (requires (permutation a tl (tail s))) *\) *)
(* (\*                (ensures (permutation a (cons (head s) tl) s)) *\) *)
(* (\* let cons_perm tl s = Seq.lemma_tl (head s) tl *\) *)


(* (\* val sort: f:('a -> 'a -> Tot bool){total_order 'a f} *\) *)
(* (\*        -> s1:seq 'a *\) *)
(* (\*        -> Tot (s2:seq 'a{sorted f s2 /\ permutation 'a s1 s2}) *\) *)
(* (\*               (decreases (s1.length)) *\) *)
(* (\* let rec sort f s = *\) *)
(* (\*   if s.length <= 1 then s *\) *)
(* (\*   else let lo, hi = partition f s 0 (s.length - 1) in *\) *)
(* (\*        let pivot = head hi in *\) *)

(* (\*        let hi_tl = tail hi in *\) *)
(* (\*        let l = sort f lo in *\) *)
(* (\*        let h = sort f hi_tl in *\) *)

(* (\*        let result = Seq.append l (cons pivot h) in *\) *)

(* (\*        sorted_concat_lemma f l pivot h; *\) *)
(* (\*        lemma_append_count l (cons pivot h); *\) *)
(* (\*        cons_perm h hi; *\) *)

(* (\*        result *\) *)



