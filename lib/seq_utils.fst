module SeqUtils
open Seq

val head: a:Type -> s:seq a{length s > 0} -> Tot a
let head s = index s 0

val tail: a:Type -> s:seq a{length s > 0} -> Tot (seq a)
let tail s = slice s 1 (length s)

val cons: a:Type -> a -> seq a -> Tot (seq a)
let cons x s = append (create 1 x) s 

val split: a:Type -> s:seq a -> i:nat{(0 <= i /\ i <= length s)} -> Tot (seq a * seq a)
let split s i = slice s 0 i, slice s i (length s)

val lemma_split : a:Type -> s:seq a -> i:nat{(0 <= i /\ i <= length s)} -> Lemma
  (ensures (append (fst (split s i)) (snd (split s i)) = s))
let lemma_split s i = 
  cut (Eq (append (fst (split s i)) (snd (split s i)))  s)

val split_eq: a:Type -> s:seq a -> i:nat{(0 <= i /\ i <= length s)} -> Pure
  (seq a * seq a)
  (requires True)
  (ensures (fun x -> (append (fst x) (snd x) = s)))
let split_eq s i = 
  let x = split s i in
  lemma_split s i;
  x

val count : 'a -> s:seq 'a -> Tot nat (decreases (length s))
let rec count x s = 
  if length s = 0 then 0
  else if head s = x 
  then 1 + count x (tail s)
  else count x (tail s)

val mem: 'a -> seq 'a -> Tot bool
let mem x l = count x l > 0

val swap: a:Type -> s:seq a -> i:nat{i<length s} -> j:nat{j<length s} -> Tot (seq a)
let swap s i j = upd i (index s j) (upd j (index s i) s)

val lemma_slice_append: a:Type -> s1:seq a{length s1 >= 1} -> s2:seq a -> Lemma 
  (ensures (Eq (append s1 s2) (append (slice s1 0 1) (append (slice s1 1 (length s1)) s2))))
let lemma_slice_append s1 s2 = ()

val lemma_append_cons: a:Type -> s1:seq a{length s1 > 0} -> s2:seq a -> Lemma 
  (requires True)
  (ensures (Eq (append s1 s2) (cons (head s1) (append (tail s1) s2))))
let rec lemma_append_cons s1 s2 = ()

val lemma_tl: a:Type -> hd:a -> tl:seq a -> Lemma 
  (ensures (Eq (tail (cons hd tl)) tl))
let lemma_tl hd tl = ()

val sorted: a:Type 
          -> (a -> a -> Tot bool) 
          -> s:seq a
          -> Tot bool (decreases (length s))
let rec sorted f s =
  if length s <= 1
  then true
  else let hd = head s in
       f hd (index s 1) && sorted f (tail s)

val lemma_append_count: a:Type -> lo:seq a -> hi:seq a -> Lemma
  (requires True)
  (ensures (forall x. count x (append lo hi) = (count x lo + count x hi)))
  (decreases (length lo))
let rec lemma_append_count lo hi =
  if length lo = 0
  then cut (Eq (append lo hi) hi)
  else (cut (Eq (cons (head lo) (append (tail lo) hi))
                (append lo hi));
        lemma_append_count (tail lo) hi;
        let tl_l_h = append (tail lo) hi in
        let lh = cons (head lo) tl_l_h in
        cut (Eq (tail lh) tl_l_h))

val lemma_append_count_aux: a:Type -> x:a -> lo:seq a -> hi:seq a -> Lemma
  (requires True)
  (ensures (count x (append lo hi) = (count x lo + count x hi)))
let lemma_append_count_aux x lo hi = lemma_append_count lo hi

val lemma_mem_inversion: a:Type -> s:seq a{length s > 0} -> Lemma 
  (ensures (forall x. mem x s = (x=head s || mem x (tail s))))
let lemma_mem_inversion s = ()

val lemma_mem_count: a:Type -> s:seq a -> f:(a -> Tot bool) -> Lemma
  (requires (forall (i:nat{i<length s}). f (index s i)))
  (ensures (forall (x:a). mem x s ==> f x))
  (decreases (length s))
let rec lemma_mem_count s f =
  if length s = 0
  then ()
  else (cut (forall (i:nat{i<length (tail s)}). index (tail s) i = index s (i + 1));
        lemma_mem_count (tail s) f)

val lemma_count_slice: a:Type -> s:seq a -> i:nat{i<=length s} -> Lemma
  (requires True)
  (ensures (forall x. count x s = count x (slice s 0 i) + count x (slice s i (length s))))
  (decreases (length s))
let lemma_count_slice s i =
  cut (Eq s (append (slice s 0 i) (slice s i (length s))));
  lemma_append_count (slice s 0 i) (slice s i (length s))

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
                               (decreases (length lo))
let rec sorted_concat_lemma f lo pivot hi =
  if length lo = 0
  then (cut (Eq (append lo (cons pivot hi)) (cons pivot hi));
        cut (Eq (tail (cons pivot hi)) hi))
  else (sorted_concat_lemma f (tail lo) pivot hi;
        lemma_append_cons lo (cons pivot hi);
        lemma_tl (head lo) (append (tail lo) (cons pivot hi)))

val lemma_swap_permutes_aux: a:Type -> s:seq a -> i:nat{i<length s} -> j:nat{i <= j && j<length s} -> x:a -> Lemma
  (requires True)
  (ensures (count x s = count x (swap s i j)))
let lemma_swap_permutes_aux s i j x =
  if j=i
  then cut (Eq (swap s i j) s)
  else begin
    let frag_lo, rest  = split_eq s i in   
    let frag_i,  rest  = split_eq rest 1 in
    let frag_mid,rest  = split_eq rest (j - (i + 1)) in 
    let frag_j,frag_hi = split_eq rest 1 in
    cut (Eq s            (append frag_lo (append frag_i (append frag_mid (append frag_j frag_hi)))));
    lemma_append_count_aux x frag_lo (append frag_i (append frag_mid (append frag_j frag_hi)));
    lemma_append_count_aux x frag_i (append frag_mid (append frag_j frag_hi));
    lemma_append_count_aux x frag_mid (append frag_j frag_hi);
    lemma_append_count_aux x frag_j frag_hi;

    let s' = swap s i j in 
    let frag_lo', rest   = split_eq s' i in   
    cut (Eq  frag_lo frag_lo');


    let frag_j',  rest   = split_eq rest 1 in
    cut (Eq  frag_j frag_j');


    let frag_mid',rest   = split_eq rest (j - (i + 1)) in 
    admitP (Eq  frag_mid frag_mid');
    (* let _ = admit () in *)

    let frag_i',frag_hi' = split_eq rest 1 in
    admitP (Eq  frag_i frag_i');

    (* cut (Eq  s' (append frag_lo' (append frag_j' (append frag_mid' (append frag_i' frag_hi'))))); *)


    lemma_append_count_aux x frag_lo (append frag_j (append frag_mid (append frag_i frag_hi)));
    lemma_append_count_aux x frag_j (append frag_mid (append frag_i frag_hi));
    lemma_append_count_aux x frag_mid (append frag_i frag_hi);
    lemma_append_count_aux x frag_i frag_hi
  end

(* let lemma_swap_permutes_aux s i j x = *)
(*   if j=i *)
(*   then cut (Eq (swap s i j) s) *)
(*   else *)
(*     let frag_lo  = slice s 0 i in *)
(*     let frag_i   = slice s i (i + 1) in *)
(*     let frag_mid = slice s (i + 1) j in *)
(*     let frag_j   = slice s j (j + 1) in *)
(*     let frag_hi  = slice s (j + 1) (length s) in *)
(*     cut (Eq s            (append frag_lo (append frag_i (append frag_mid (append frag_j frag_hi))))); *)
(*     lemma_append_count_aux x frag_lo (append frag_i (append frag_mid (append frag_j frag_hi))); *)
(*     lemma_append_count_aux x frag_i (append frag_mid (append frag_j frag_hi)); *)
(*     lemma_append_count_aux x frag_mid (append frag_j frag_hi); *)
(*     lemma_append_count_aux x frag_j frag_hi; *)
(*     cut (Eq (swap s i j) (append frag_lo (append frag_j (append frag_mid (append frag_i frag_hi))))); *)
(*     lemma_append_count_aux x frag_lo (append frag_j (append frag_mid (append frag_i frag_hi))); *)
(*     lemma_append_count_aux x frag_j (append frag_mid (append frag_i frag_hi)); *)
(*     lemma_append_count_aux x frag_mid (append frag_i frag_hi); *)
(*     lemma_append_count_aux x frag_i frag_hi *)
