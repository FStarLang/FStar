module FStar.Seq.Sorted

open FStar.Seq

type sorted_pred (#a:eqtype) (f:tot_ord a) (s:seq a) : Type0 =
  forall (i j:k:nat{k<length s}). i <= j ==> f (index s i) (index s j)

val sorted_pred_tail :
  #a:eqtype ->
  f:tot_ord a ->
  s:seq a{length s > 0} ->
  Lemma (requires (sorted_pred #a f s)) (ensures (sorted_pred #a f (tail s)))
let sorted_pred_tail #a f s = ()

val sorted_pred_sorted_lemma :
  #a:eqtype ->
  f:tot_ord a ->
  s:seq a ->
  Lemma (requires (sorted_pred f s)) (ensures (sorted #a f s == true)) (decreases (length s))
let rec sorted_pred_sorted_lemma #a f s =
  if length s <= 1 then ()
  else begin
    assert (f (index s 0) (index s 1)) ;
    sorted_pred_tail #a f s;
    sorted_pred_sorted_lemma #a f (tail s)
  end

val sorted_pred_cons_lemma :
  #a:eqtype ->
  f:tot_ord a ->
  s:seq a{length s > 1} ->
  Lemma (requires (f (index s 0) (index s 1) /\ sorted_pred #a f (tail s))) (ensures (sorted_pred #a f s))
let sorted_pred_cons_lemma #a f s =
  let open FStar.Classical in
  let aux (i j : k:nat{k < length s}) (p:squash (i <= j)) : GTot (squash (f (index s i) (index s j))) =
    FStar.Squash.give_proof p ;
    if i = 0 then
      if j = 0 then ()
      else assert (f (index s 0) (index (tail s) 0) /\ f (index (tail s) 0) (index (tail s) (j-1)))
    else assert (f (index (tail s) (i - 1)) (index (tail s) (j - 1))) ;
    FStar.Squash.get_proof (f (index s i) (index s j))
  in
  FStar.Classical.forall_intro_2 (fun (i j:k:nat{k < length s}) -> FStar.Classical.arrow_to_impl (aux i j) <: Lemma (i <= j ==> f (index s i) (index s j)))

val sorted_sorted_pred_lemma :
  #a:eqtype ->
  f:tot_ord a ->
  s:seq a ->
  Lemma (requires (sorted #a f s == true)) (ensures (sorted_pred #a f s)) (decreases (length s))
let rec sorted_sorted_pred_lemma #a f s =
  if length s = 0 then ()
  else if length s = 1 then ()
  else (sorted_sorted_pred_lemma #a f (tail s) ; sorted_pred_cons_lemma #a f s)

val sorted_pred_slice_lemma :
  #a:eqtype ->
  f:tot_ord a ->
  s:seq a ->
  i:nat{i < length s} ->
  j:nat{i <= j /\ j <= length s} ->
  Lemma (requires (sorted_pred #a f s)) (ensures (sorted_pred #a f (slice s i j)))
let sorted_pred_slice_lemma #a f s i j = ()

val sorted_slice_lemma :
  #a:eqtype ->
  f:tot_ord a ->
  s:seq a ->
  i:nat{i < length s} ->
  j:nat{i <= j /\ j <= length s} ->
  Lemma (requires (sorted #a f s == true)) (ensures (sorted #a f (slice s i j) == true))
let sorted_slice_lemma #a f s i j =
  sorted_sorted_pred_lemma #a f s ;
  sorted_pred_slice_lemma #a f s i j ;
  sorted_pred_sorted_lemma #a f (slice s i j)

val sorted_split_lemma :
  #a:eqtype ->
  f:tot_ord a ->
  s:seq a ->
  i:nat{i < length s} ->
  Lemma (requires (sorted #a f s == true))
    (ensures (let s1, s2 = split s i in sorted #a f s1 == true /\ sorted #a f s2 == true))
let sorted_split_lemma #a f s i =
  sorted_slice_lemma #a f s 0 i ;
  sorted_slice_lemma #a f s i (length s)
