module Seq.QuickSort

val count : 'a -> s:seq 'a -> Tot nat (decreases s.length)
let rec count x s = 
  if s.length = 0 then 0
  else if index s 0 = x 
  then 1 + count x (slice s 1 s.length) 
  else count x (slice s 1 s.length)
 
val sorted_s: ('a -> 'a -> Tot bool) -> s:seq 'a
              -> Tot bool (decreases (s.length))
let rec sorted_s f s =
  if s.length <= 1
  then true
  else let hd = index s 0 in
       f hd (index s 1) && sorted_s f (slice s 1 s.length)

(* Defining a new predicate symbol *)
type Total_order (a:Type) (f: (a -> a -> Tot bool)) =
    (forall a. f a a)                                           (* reflexivity   *)
    /\ (forall a1 a2. (f a1 a2 /\ a1<>a2)  <==> not (f a2 a1))  (* anti-symmetry *)
    /\ (forall a1 a2 a3. f a1 a2 /\ f a2 a3 ==> f a1 a3)        (* transitivity  *)
type total_order (a:Type) = f:(a -> a -> Tot bool){Total_order a f}

assume (* opaque *) val partition: a:Type
            -> f:(a -> a -> Tot bool){Total_order a f}
            -> s:seq a{s.length > 1}
            -> pivot:nat{pivot < s.length}
            -> back:nat{pivot <= back /\ back < s.length}
            -> Pure (seq a * seq a)
                    (requires (forall (i:nat{i < s.length}).((i <= pivot ==> (f (index s i) (index s pivot)))
                                                             /\ (back < i  ==> f (index s pivot) (index s i)))))
                    (ensures (fun s1s2 ->
                              (forall s1 s2. (s1,s2) = s1s2
                               ==> ((s1.length + s2.length = s.length)
                                    /\ (s2.length > 0)
                                    /\ (forall x. count x s = count x s1 + count x s2)
                                    /\ (index s pivot = index s2 0)
                                    (* /\ (forall (x:a). count x s1 > 0 ==> f x (index s pivot)) *)
                                    (* /\ (forall (x:a). count x s2 > 0 ==> f (index s pivot) x) *)
                                    /\ (forall (i:nat).
                                        (i < s1.length ==> f (index s1 i) (index s2 0))
                                        /\  (i < s2.length ==> f (index s2 0) (index s2 i)))))))
                    (decreases (back - pivot))
(* let rec partition f s pivot back = *)
(*   if pivot=back *)
(*   then (slice s 0 (pivot + 1), slice s (pivot + 1) s.length) *)
(*   else let next = index s (pivot + 1) in *)
(*        let p = index s pivot in *)
(*        if f next p *)
(*        then let s' = upd pivot next s in *)
(*             let s' = upd (pivot + 1) p s' in *)
(*             partition f s' (pivot + 1) back *)
(*        else let b = index s back in *)
(*             let s' = upd back next s in *)
(*             let s' = upd (pivot + 1) b s' in *)
(*             partition f s' pivot (back - 1) *)
                   
assume val lemma_sort_app: a:Type -> f:(a -> a -> Tot bool){Total_order a f} -> lo:seq a -> hi:seq a
                    -> Lemma (requires (sorted_s f lo
                                        /\ sorted_s f hi
                                        (* /\ (forall (x:a). count x lo > 0 /\ 0 < hi.length ==> f x (index hi 0)) *)
                                        /\ (forall (i:nat{i < lo.length}).
                                            0 < hi.length ==> f (index lo i) (index hi 0))))
                              (ensures (sorted_s f (Seq.append lo hi)))
                              (decreases (lo.length))

(* assume val lemma_sort_app: a:Type -> f:(a -> a -> Tot bool){Total_order a f} -> lo:seq a -> hi:seq a *)
(*                     -> Lemma (requires (sorted_s f lo *)
(*                                         /\ sorted_s f hi *)
(*                                         /\ (forall (i:nat{i < lo.length}). *)
(*                                             0 < hi.length ==> f (index lo i) (index hi 0)))) *)
(*                               (ensures (sorted_s f (Seq.append lo hi))) *)
(*                               (decreases (lo.length)) *)

(* let rec lemma_sort_app f lo hi = *)
(*   if lo.length = 0 *)
(*   then cut (Eq (Seq.append lo hi) hi) *)
(*   else if hi.length = 0 *)
(*   then cut (Eq (Seq.append lo hi) lo) *)
(*   else (cut (Eq (Seq.push (index lo 0) *)
(*                           (Seq.append (Seq.slice lo 1 lo.length) hi)) *)
(*                 (Seq.append lo hi)); *)
(*         lemma_sort_app f (Seq.slice lo 1 lo.length) hi; *)
(*         let l1_h = Seq.append (Seq.slice lo 1 lo.length) hi in *)
(*         let lh = Seq.push (index lo 0) l1_h in *)
(*         cut (Eq (slice lh 1 lh.length) l1_h)) *)


assume val lemma_sort_count: a:Type -> lo:seq a -> hi:seq a 
                    -> Lemma (requires True)
                             (ensures (forall x. count x lo + count x hi = count x (append lo hi)))
                             (decreases (lo.length))
(* let rec lemma_sort_count lo hi =  *)
(*   if lo.length = 0  *)
(*   then cut (Eq (Seq.append lo hi) hi) *)
(*   else (cut (Eq (Seq.push (index lo 0) *)
(*                           (Seq.append (Seq.slice lo 1 lo.length) hi)) *)
(*                 (Seq.append lo hi)); *)
(*         lemma_sort_count (Seq.slice lo 1 lo.length) hi; *)
(*         let l1_h = Seq.append (Seq.slice lo 1 lo.length) hi in *)
(*         let lh = Seq.push (index lo 0) l1_h in *)
(*         cut (Eq (slice lh 1 lh.length) l1_h)) *)


opaque type permutation (a:Type) (s1:seq a) (s2:seq a) =
           (forall x. count x s1 = count x s2)

assume val lemma_perm_order: a:Type -> f:(a -> a -> Tot bool){Total_order a f} -> pivot:a ->
                            s1:seq a -> s2:seq a{permutation a s1 s2} ->
                            Lemma (requires (forall (i:nat{i < s1.length}). f (index s1 i) pivot))
                                  (ensures (forall (i:nat{i < s2.length}). f (index s2 i) pivot))


assume val lemma_perm_order2: a:Type -> f:(a -> a -> Tot bool){Total_order a f} -> pivot:a ->
                            s1:seq a -> s2:seq a{permutation a s1 s2} ->
                            Lemma (requires (forall (i:nat{i < s1.length}). f pivot (index s1 i)))
                                  (ensures (forall (i:nat{i < s2.length}). f pivot (index s2 i)))



val swap: a:Type -> s:seq a -> i:nat{i < s.length} -> j:nat{j < s.length} -> Tot (seq a) 
let swap s i j = upd j (index s i) (upd i (index s j) s)                 
                                                    

opaque val quicksort: a:Type
                      -> f:(a -> a -> Tot bool){Total_order a f}
                      -> s1:seq a
                      -> Pure (seq a)
                              (requires True)
                              (ensures (fun s2 -> sorted_s f s2 /\ permutation a s1 s2))
                              (decreases (s1.length))
let rec quicksort (a:Type) f s =
  if s.length <= 1 then s
  else let lo, hi = partition f s 0 (s.length - 1) in
       let pivot = index hi 0 in 
       let hi' = slice hi 1 hi.length in
       let _ = admit () in 
       let l = quicksort f lo in
       let h = quicksort f hi' in 
       let p = Seq.create 1 pivot in
       let ph = Seq.append p h in
       let result = Seq.append l ph in 

       (* let _ = admitP (forall (i:nat{i<h.length}). f pivot (index h i)) in *)
       (* let _ = assert (forall (i:nat{i<h.length}). f pivot (index h i)) in  *)
       (* let _ = admitP (forall (i:nat{i<hi'.length}). f pivot (index hi' i)) in *)
       let _ = lemma_perm_order2 f pivot hi' h in 
       let _ = lemma_sort_app f p h in
       (* let _ = admitP (b2t (sorted_s f ph)) in *)

       let _      = lemma_perm_order f pivot lo l in
       let _      = lemma_sort_app f l ph in
       let _      = lemma_sort_count l ph in

       let _  = admitP (permutation a s result) in
       result

              
