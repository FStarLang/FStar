(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module FStar.Seq.Properties

open FStar.Seq.Base
module Seq = FStar.Seq.Base

let lemma_append_inj_l #_ s1 s2 t1 t2 i =
  assert (index s1 i == (index (append s1 s2) i));
  assert (index t1 i == (index (append t1 t2) i))

let lemma_append_inj_r #_ s1 s2 t1 t2 i =
  assert (index s2 i == (index (append s1 s2) (i + length s1)));
  assert (index t2 i == (index (append t1 t2) (i + length t1)))

let lemma_append_len_disj #_ s1 s2 t1 t2 =
  cut (length (append s1 s2) == length s1 + length s2);
  cut (length (append t1 t2) == length t1 + length t2)

let lemma_append_inj #_ s1 s2 t1 t2 =
  lemma_append_len_disj s1 s2 t1 t2;
  FStar.Classical.forall_intro #(i:nat{i < length s1}) #(fun i -> index s1 i == index t1 i) (lemma_append_inj_l s1 s2 t1 t2);
  FStar.Classical.forall_intro #(i:nat{i < length s2}) #(fun i -> index s2 i == index t2 i) (lemma_append_inj_r s1 s2 t1 t2)

let lemma_head_append #_ _ _ = ()

let lemma_tail_append #_ s1 s2 = cut (equal (tail (append s1 s2)) (append (tail s1) s2))

let lemma_cons_inj #_ v1 v2 s1 s2 =
  let t1 = create 1 v1 in
  let t2 = create 1 v2 in
  lemma_append_inj t1 s1 t2 s2;
  assert(index t1 0 == index t2 0)

let lemma_split #_ s i =
  cut (equal (append (fst (split s i)) (snd (split s i)))  s)

let rec mem_index' (#a:eqtype) (x:a) (s:seq a)
    : Lemma (requires (mem x s))
            (ensures (exists i. index s i == x))
            (decreases (length s))
    = if length s = 0 then ()
      else if head s = x then ()
      else mem_index' x (tail s)

let mem_index = mem_index'

let lemma_slice_append #_ _ _ = ()

let rec lemma_slice_first_in_append' (#a:Type) (s1:seq a) (s2:seq a)
  (i:nat{i <= length s1})
: Lemma
  (ensures (equal (slice (append s1 s2) i (length (append s1 s2))) (append (slice s1 i (length s1)) s2)))
  (decreases (length s1))
= if i = 0 then ()
  else lemma_slice_first_in_append' (tail s1) s2 (i - 1)

let lemma_slice_first_in_append = lemma_slice_first_in_append'

let slice_upd #_ s i j k v =
  lemma_eq_intro (slice (upd s k v) i j) (slice s i j)

let upd_slice #_ s i j k v =
  lemma_eq_intro (upd (slice s i j) k v) (slice (upd s (i + k) v) i j)

let lemma_append_cons #_ _ _ = ()

let lemma_tl #_ _ _ = ()

let rec sorted_feq' (#a:Type)
               (f g : (a -> a -> Tot bool))
               (s:seq a{forall x y. f x y == g x y})
   : Lemma (ensures (sorted f s <==> sorted g s))
           (decreases (length s))
   = if length s <= 1 then ()
     else sorted_feq' f g (tail s)

let sorted_feq = sorted_feq'

let rec lemma_append_count' (#a:eqtype) (lo:seq a) (hi:seq a)
: Lemma
  (requires True)
  (ensures (forall x. count x (append lo hi) = (count x lo + count x hi)))
  (decreases (length lo))
= if length lo = 0
  then cut (equal (append lo hi) hi)
  else (cut (equal (cons (head lo) (append (tail lo) hi))
                (append lo hi));
        lemma_append_count' (tail lo) hi;
        let tl_l_h = append (tail lo) hi in
        let lh = cons (head lo) tl_l_h in
        cut (equal (tail lh) tl_l_h))

let lemma_append_count = lemma_append_count'

let lemma_append_count_aux #_ _ lo hi = lemma_append_count lo hi

let lemma_mem_inversion #_ _ = ()

let rec lemma_mem_count' (#a:eqtype) (s:seq a) (f:a -> Tot bool)
: Lemma
  (requires (forall (i:nat{i<length s}). f (index s i)))
  (ensures (forall (x:a). mem x s ==> f x))
  (decreases (length s))
= if length s = 0
  then ()
  else (let t = i:nat{i<length (tail s)} in
        cut (forall (i:t). index (tail s) i = index s (i + 1));
        lemma_mem_count' (tail s) f)

let lemma_mem_count = lemma_mem_count'

let lemma_count_slice #_ s i =
  cut (equal s (append (slice s 0 i) (slice s i (length s))));
  lemma_append_count (slice s 0 i) (slice s i (length s))

let rec sorted_concat_lemma': #a:eqtype
                      -> f:(a -> a -> Tot bool){total_order a f}
                      -> lo:seq a{sorted f lo}
                      -> pivot:a
                      -> hi:seq a{sorted f hi}
                      -> Lemma (requires (forall y. (mem y lo ==> f y pivot)
                                                 /\ (mem y hi ==> f pivot y)))
                               (ensures (sorted f (append lo (cons pivot hi))))
                               (decreases (length lo))
= fun #_ f lo pivot hi ->
  if length lo = 0
  then (cut (equal (append lo (cons pivot hi)) (cons pivot hi));
        cut (equal (tail (cons pivot hi)) hi))
  else (sorted_concat_lemma' f (tail lo) pivot hi;
        lemma_append_cons lo (cons pivot hi);
        lemma_tl (head lo) (append (tail lo) (cons pivot hi)))

let sorted_concat_lemma = sorted_concat_lemma'

let split_5 #a s i j =
  let frag_lo = slice s 0 i in
  let frag_i = slice s i (i + 1) in
  let frag_mid = slice s (i + 1) j in
  let frag_j = slice s j (j + 1) in
  let frag_hi = slice s (j + 1) (length s) in
  upd (upd (upd (upd (create 5 frag_lo) 1 frag_i) 2 frag_mid) 3 frag_j) 4 frag_hi

let lemma_swap_permutes_aux_frag_eq #a s i j i' j' =
  cut (equal (slice s i' j') (slice (swap s i j) i' j'));
  cut (equal (slice s i (i + 1))  (slice (swap s i j) j (j + 1)));
  cut (equal (slice s j (j + 1))  (slice (swap s i j) i (i + 1)))

#push-options "--z3rlimit 20"
let lemma_swap_permutes_aux #_ s i j x =
  if j=i
  then cut (equal (swap s i j) s)
  else begin
      let s5 = split_5 s i j in
      let frag_lo, frag_i, frag_mid, frag_j, frag_hi =
        index s5 0, index s5 1, index s5 2, index s5 3, index s5 4 in
      lemma_append_count_aux x frag_lo (append frag_i (append frag_mid (append frag_j frag_hi)));
      lemma_append_count_aux x frag_i (append frag_mid (append frag_j frag_hi));
      lemma_append_count_aux x frag_mid (append frag_j frag_hi);
      lemma_append_count_aux x frag_j frag_hi;

      let s' = swap s i j in
      let s5' = split_5 s' i j in
      let frag_lo', frag_j', frag_mid', frag_i', frag_hi' =
        index s5' 0, index s5' 1, index s5' 2, index s5' 3, index s5' 4 in

      lemma_swap_permutes_aux_frag_eq s i j 0 i;
      lemma_swap_permutes_aux_frag_eq s i j (i + 1) j;
      lemma_swap_permutes_aux_frag_eq s i j (j + 1) (length s);

      lemma_append_count_aux x frag_lo (append frag_j (append frag_mid (append frag_i frag_hi)));
      lemma_append_count_aux x frag_j (append frag_mid (append frag_i frag_hi));
      lemma_append_count_aux x frag_mid (append frag_i frag_hi);
      lemma_append_count_aux x frag_i frag_hi
  end
#pop-options  

let append_permutations #a s1 s2 s1' s2' =
  (
    lemma_append_count s1 s2;
    lemma_append_count s1' s2'
  )

let lemma_swap_permutes #a s i j
  = FStar.Classical.forall_intro
                    #a
                    #(fun x -> count x s = count x (swap s i j))
                    (lemma_swap_permutes_aux s i j)

(* perm_len:
     A lemma that shows that two sequences that are permutations
     of each other also have the same length
*)
//a proof optimization: Z3 only needs to unfold the recursive definition of `count` once
#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
let rec perm_len' (#a:eqtype) (s1 s2: seq a)
  : Lemma (requires (permutation a s1 s2))
          (ensures  (length s1 == length s2))
          (decreases (length s1))
  = if length s1 = 0 then begin
       if length s2 = 0 then ()
       else assert (count (index s2 0) s2 > 0)
    end
    else let s1_hd = head s1 in
         let s1_tl = tail s1 in
         assert (count s1_hd s1 > 0);
         assert (count s1_hd s2 > 0);
         assert (length s2 > 0);
         let s2_hd = head s2 in
         let s2_tl = tail s2 in
         if s1_hd = s2_hd
         then (assert (permutation a s1_tl s2_tl); perm_len' s1_tl s2_tl)
         else let i = index_mem s1_hd s2 in
              let s_pfx, s_sfx = split_eq s2 i in
              assert (equal s_sfx (append (create 1 s1_hd) (tail s_sfx)));
              let s2' = append s_pfx (tail s_sfx) in
              lemma_append_count s_pfx s_sfx;
              lemma_append_count (create 1 s1_hd) (tail s_sfx);
              lemma_append_count s_pfx (tail s_sfx);
              assert (permutation a s1_tl s2');
              perm_len' s1_tl s2'
#pop-options

let perm_len = perm_len'

let cons_perm #_ tl s = lemma_tl (head s) tl

let lemma_mem_append #_ s1 s2 = lemma_append_count s1 s2

let lemma_slice_cons #_ s i j =
  cut (equal (slice s i j) (append (create 1 (index s i)) (slice s (i + 1) j)));
  lemma_mem_append (create 1 (index s i)) (slice s (i + 1) j)

let lemma_slice_snoc #_ s i j =
  cut (equal (slice s i j) (append (slice s i (j - 1)) (create 1 (index s (j - 1)))));
  lemma_mem_append (slice s i (j - 1)) (create 1 (index s (j - 1)))

let lemma_ordering_lo_snoc #_ f s i j pv =
  cut (equal (slice s i (j + 1)) (append (slice s i j) (create 1 (index s j))));
  lemma_mem_append (slice s i j) (create 1 (index s j))

let lemma_ordering_hi_cons #_ f s back len pv =
  cut (equal (slice s back len) (append (create 1 (index s back)) (slice s (back + 1) len)));
  lemma_mem_append (create 1 (index s back)) (slice s (back + 1) len)

let swap_frame_lo #_ s lo i j = cut (equal (slice s lo i) (slice (swap s i j) lo i))

let swap_frame_lo' #_ s lo i' i j = cut (equal (slice s lo i') (slice (swap s i j) lo i'))

let swap_frame_hi #_ s i j k hi = cut (equal (slice s k hi) (slice (swap s i j) k hi))

let lemma_swap_slice_commute #_ s start i j len =
  cut (equal (slice (swap s i j) start len) (swap (slice s start len) (i - start) (j - start)))

let lemma_swap_permutes_slice #_ s start i j len =
  lemma_swap_slice_commute s start i j len;
  lemma_swap_permutes (slice s start len) (i - start) (j - start)

let splice_refl #_ s i j = cut (equal s (splice s i s j))

let lemma_swap_splice #_ s start i j len = cut (equal (swap s i j) (splice s start (swap s i j) len))

let lemma_seq_frame_hi #_ s1 s2 i j m n =
  cut (equal (slice s1 m n) (slice s2 m n))

let lemma_seq_frame_lo #_ s1 s2 i j m n =
  cut (equal (slice s1 i j) (slice s2 i j))

let lemma_tail_slice #_ s i j =
  cut (equal (tail (slice s i j)) (slice s (i + 1) j))

let lemma_weaken_frame_right #_ s1 s2 i j k = cut (equal s1 (splice s2 i s1 k))

let lemma_weaken_frame_left #_ s1 s2 i j k = cut (equal s1 (splice s2 i s1 k))

let lemma_trans_frame #_ s1 s2 s3 i j = cut (equal s1 (splice s3 i s1 j))

let lemma_weaken_perm_left #_ s1 s2 i j k =
  cut (equal (slice s2 i k) (append (slice s2 i j)
                                 (slice s2 j k)));
  cut (equal (slice s1 i k) (append (slice s2 i j)
                                 (slice s1 j k)));
  lemma_append_count (slice s2 i j) (slice s2 j k);
  lemma_append_count (slice s2 i j) (slice s1 j k)

let lemma_weaken_perm_right #_ s1 s2 i j k =
  cut (equal (slice s2 i k) (append (slice s2 i j)
                                 (slice s2 j k)));
  cut (equal (slice s1 i k) (append (slice s1 i j)
                                 (slice s2 j k)));
  lemma_append_count (slice s2 i j) (slice s2 j k);
  lemma_append_count (slice s1 i j) (slice s2 j k)

let lemma_trans_perm #_ _ _ _ _ _ = ()


let lemma_cons_snoc #_ _ _ _ = ()

let lemma_tail_snoc #_ s x = lemma_slice_first_in_append s (Seq.create 1 x) 1

let lemma_snoc_inj #_ s1 s2 v1 v2 =
  let t1 = create 1 v1 in
  let t2 = create 1 v2 in
  lemma_append_inj s1 t1 s2 t2;
  assert(head t1  == head t2)

let lemma_mem_snoc #_ s x = lemma_append_count s (Seq.create 1 x)

let rec find_append_some': #a:Type -> s1:seq a -> s2:seq a -> f:(a -> Tot bool) -> Lemma
  (requires (Some? (find_l f s1)))
  (ensures (find_l f (append s1 s2) == find_l f s1))
  (decreases (length s1))
= fun #_ s1 s2 f ->
  if f (head s1) then ()
  else
    let _ = cut (equal (tail (append s1 s2)) (append (tail s1) s2)) in
    find_append_some' (tail s1) s2 f

let find_append_some = find_append_some'

let rec find_append_none': #a:Type -> s1:seq a -> s2:seq a -> f:(a -> Tot bool) -> Lemma
  (requires (None? (find_l f s1)))
  (ensures (find_l f (append s1 s2) == find_l f s2))
  (decreases (length s1))
= fun #_ s1 s2 f ->
  if Seq.length s1 = 0 then cut (equal (append s1 s2) s2)
  else
    let _ = cut (equal (tail (append s1 s2)) (append (tail s1) s2)) in
    find_append_none' (tail s1) s2 f

let find_append_none = find_append_none'

let rec find_append_none_s2': #a:Type -> s1:seq a -> s2:seq a -> f:(a -> Tot bool) -> Lemma
  (requires (None? (find_l f s2)))
  (ensures  (find_l f (append s1 s2) == find_l f s1))
  (decreases (length s1))
= fun #_ s1 s2 f ->
  if Seq.length s1 = 0 then cut (equal (append s1 s2) s2)
  else if f (head s1) then ()
  else begin
    find_append_none_s2' (tail s1) s2 f;
    cut (equal (tail (append s1 s2)) (append (tail s1) s2))
  end

let find_append_none_s2 = find_append_none_s2'

let find_snoc #_ s x f =
  if Some? (find_l f s) then find_append_some s (Seq.create 1 x) f
  else find_append_none s (Seq.create 1 x) f

let un_snoc_snoc #_ s x =
  let s', x = un_snoc (snoc s x) in
  assert (Seq.equal s s')

let find_mem #_ s f x
   = match seq_find f s with
     | None -> mem_index x s
     | Some _ -> ()

let rec seq_mem_k': #a:eqtype -> s:seq a -> n:nat{n < Seq.length s} ->
    Lemma (requires True)
          (ensures (mem (Seq.index s n) s))
          (decreases n)
= fun #_ s n ->          
  if n = 0 then ()
  else let tl = tail s in
       seq_mem_k' tl (n - 1)

let seq_mem_k = seq_mem_k'

module L = FStar.List.Tot

let lemma_seq_of_list_induction #_ l
  = match l with
    | [] -> ()
    | hd::tl -> lemma_tl hd (seq_of_list tl)

let rec lemma_seq_list_bij': #a:Type -> s:seq a -> Lemma
  (requires (True))
  (ensures  (seq_of_list (seq_to_list s) == s))
  (decreases (length s))
= fun #_ s ->
  let l = seq_to_list s in
  lemma_seq_of_list_induction l;
  if length s = 0 then (
    assert (equal s (seq_of_list l))
  )
  else (
    lemma_seq_list_bij' (slice s 1 (length s));
    assert (equal s (seq_of_list (seq_to_list s)))
  )

let lemma_seq_list_bij = lemma_seq_list_bij'

let rec lemma_list_seq_bij': #a:Type -> l:list a -> Lemma
  (requires (True))
  (ensures  (seq_to_list (seq_of_list l) == l))
  (decreases (L.length l))
= fun #_ l ->  
  lemma_seq_of_list_induction l;
  if L.length l = 0 then ()
  else (
    lemma_list_seq_bij' (L.tl l);
    assert(equal (seq_of_list (L.tl l)) (slice (seq_of_list l) 1 (length (seq_of_list l))))
  )

let lemma_list_seq_bij = lemma_list_seq_bij'

let rec lemma_index_is_nth': #a:Type -> s:seq a -> i:nat{i < length s} -> Lemma
  (requires True)
  (ensures  (L.index (seq_to_list s) i == index s i))
  (decreases i)
= fun #_ s i ->
  assert (s `equal` cons (head s) (tail s));
  if i = 0 then ()
  else (
    lemma_index_is_nth' (slice s 1 (length s)) (i-1)
  )

let lemma_index_is_nth = lemma_index_is_nth'

let contains #a s x =
  exists (k:nat). k < Seq.length s /\ Seq.index s k == x

let contains_intro #_ _ _ _ = ()

let contains_elim #_ _ _ = ()

let lemma_contains_empty #_ = ()

let lemma_contains_singleton #_ _ = ()

private let intro_append_contains_from_disjunction (#a:Type) (s1:seq a) (s2:seq a) (x:a)
    : Lemma (requires s1 `contains` x \/ s2 `contains` x)
            (ensures (append s1 s2) `contains` x)
    = let open FStar.Classical in
      let open FStar.Squash in
      or_elim #(s1 `contains` x) #(s2 `contains` x) #(fun _ -> (append s1 s2) `contains` x)
        (fun _ -> ())
	(fun _ -> let s = append s1 s2 in
               exists_elim (s `contains` x) (get_proof (s2 `contains` x)) (fun k ->
               assert (Seq.index s (Seq.length s1 + k) == x)))

let append_contains_equiv #_ s1 s2 x
  = FStar.Classical.move_requires (intro_append_contains_from_disjunction s1 s2) x

let contains_snoc #_ s x =
  FStar.Classical.forall_intro (append_contains_equiv s (Seq.create 1 x))

let rec lemma_find_l_contains' (#a:Type) (f:a -> Tot bool) (l:seq a)
  : Lemma (requires True) (ensures Some? (find_l f l) ==> l `contains` (Some?.v (find_l f l)))
          (decreases (Seq.length l))
  = if length l = 0 then ()
    else if f (head l) then ()
    else lemma_find_l_contains' f (tail l)

let lemma_find_l_contains = lemma_find_l_contains'

let contains_cons #_ hd tl x
  = append_contains_equiv (Seq.create 1 hd) tl x

let append_cons_snoc #_ _ _ _ = ()

let append_slices #_ _ _ = ()

let rec find_l_none_no_index' (#a:Type) (s:Seq.seq a) (f:(a -> Tot bool)) :
  Lemma (requires (None? (find_l f s)))
        (ensures (forall (i:nat{i < Seq.length s}). not (f (Seq.index s i))))
        (decreases (Seq.length s))
= if Seq.length s = 0
  then ()
  else (assert (not (f (head s)));
        assert (None? (find_l f (tail s)));
        find_l_none_no_index' (tail s) f;
        assert (Seq.equal s (cons (head s) (tail s)));
        find_append_none (create 1 (head s)) (tail s) f)

let find_l_none_no_index = find_l_none_no_index'

let cons_head_tail #_ s =
  let _ : squash (slice s 0 1 == create 1 (index s 0)) =
      lemma_index_slice s 0 1 0;
      lemma_index_create 1 (index s 0) 0;
      lemma_eq_elim (slice s 0 1) (create 1 (index s 0))
  in
  lemma_split s 1

let head_cons #_ _ _ = ()

let suffix_of_tail #_ s = cons_head_tail s

let index_cons_l #_ _ _ = ()

let index_cons_r #_ _ _ _ = ()

let append_cons #_ c s1 s2 = lemma_eq_elim (append (cons c s1) s2) (cons c (append s1 s2))

let index_tail #_ _ _ = ()

let mem_cons #_ x s = lemma_append_count (create 1 x) s

let snoc_slice_index #_ s i j = lemma_eq_elim (snoc (slice s i j) (index s j)) (slice s i (j + 1))

let cons_index_slice #_ s i j _ = lemma_eq_elim (cons (index s i) (slice s (i + 1) j)) (slice s i j)

let slice_is_empty #_ s i = lemma_eq_elim (slice s i i) Seq.empty

let slice_length #_ s = lemma_eq_elim (slice s 0 (length s)) s

let slice_slice #_ s i1 j1 i2 j2 = lemma_eq_elim (slice (slice s i1 j1) i2 j2) (slice s (i1 + i2) (i1 + j2))

let rec lemma_seq_of_list_index #_ l i
  = lemma_seq_of_list_induction l;
    match l with
    | []    -> ()
    | hd::tl -> if i = 0 then () else lemma_seq_of_list_index tl (i - 1)

let seq_of_list_tl #_ l = lemma_seq_of_list_induction l

let rec mem_seq_of_list #_ x l
= lemma_seq_of_list_induction l;
  match l with
  | [] -> ()
  | y :: q ->
    let _ : squash (head (seq_of_list l) == y) = () in
    let _ : squash (tail (seq_of_list l) == seq_of_list q) = seq_of_list_tl l in
    let _ : squash (mem x (seq_of_list l) == (x = y || mem x (seq_of_list q))) =
     lemma_mem_inversion (seq_of_list l)
    in
    mem_seq_of_list x q

let rec intro_of_list'': #a:Type ->
  i:nat ->
  s:seq a ->
  l:list a ->
  Lemma
    (requires (
      List.Tot.length l + i = length s /\
      i <= length s /\
      explode_and i s l))
    (ensures (
      equal (seq_of_list l) (slice s i (length s))))
    (decreases (
      List.Tot.length l))
= fun #_ i s l ->
  lemma_seq_of_list_induction l;
  match l with
  | [] -> ()
  | hd :: tl -> intro_of_list'' (i + 1) s tl

let intro_of_list' = intro_of_list''

let intro_of_list #_ s l = intro_of_list' 0 s l

#push-options "--z3rlimit 20"
let rec elim_of_list'': #a:Type ->
  i:nat ->
  s:seq a ->
  l:list a ->
  Lemma
    (requires (
      List.Tot.length l + i = length s /\
      i <= length s /\
      slice s i (length s) == seq_of_list l))
    (ensures (
      explode_and i s l))
    (decreases (
      List.Tot.length l))
= fun #_ i s l ->
  match l with
  | [] -> ()
  | hd :: tl ->
      lemma_seq_of_list_induction l;
      elim_of_list'' (i + 1) s tl
#pop-options

let elim_of_list' = elim_of_list''

let elim_of_list #_ l = elim_of_list' 0 (seq_of_list l) l

let rec lemma_seq_to_list_permutation' (#a:eqtype) (s:seq a)
  :Lemma (requires True) (ensures (forall x. count x s == List.Tot.Base.count x (seq_to_list s))) (decreases (length s))
  = if length s > 0 then (
      assert (equal s (cons (head s) (tail s)));
      lemma_seq_to_list_permutation' (slice s 1 (length s))
    )

let lemma_seq_to_list_permutation = lemma_seq_to_list_permutation'

let rec lemma_seq_of_list_permutation #a l
  =
    lemma_seq_of_list_induction l;
    match l with
    | []   -> ()
    | _::tl -> lemma_seq_of_list_permutation tl

let rec lemma_seq_of_list_sorted #a f l
  =
    lemma_seq_of_list_induction l;
    if List.Tot.length l > 1 then begin
      lemma_seq_of_list_induction (List.Tot.Base.tl l);
      lemma_seq_of_list_sorted f (List.Tot.Base.tl l)      
    end


let lemma_seq_sortwith_correctness #_ f s
  = let l = seq_to_list s in
    let l' = List.Tot.Base.sortWith f l in
    let s' = seq_of_list l' in
    let cmp = List.Tot.Base.bool_of_compare f in

    (* sortedness *)
    List.Tot.Properties.sortWith_sorted f l;  //the list returned by List.sortWith is sorted
    lemma_seq_of_list_sorted cmp l';  //seq_of_list preserves sortedness

    (* permutation *)
    lemma_seq_to_list_permutation s;  //seq_to_list is a permutation
    List.Tot.Properties.sortWith_permutation f l;  //List.sortWith is a permutation
    lemma_seq_of_list_permutation l'  //seq_of_list is a permutation


(****** Seq map ******)

let rec map_seq #a #b f s : Tot (Seq.seq b) (decreases Seq.length s) =
  if Seq.length s = 0
  then Seq.empty
  else let hd, tl = head s, tail s in
       cons (f hd) (map_seq f tl)

let rec map_seq_len #a #b f s
  : Lemma (ensures Seq.length (map_seq f s) == Seq.length s) (decreases Seq.length s)
  = if Seq.length s = 0
    then ()
    else map_seq_len f (tail s)

let rec map_seq_index #a #b f s i
  : Lemma (ensures (map_seq_len f s; Seq.index (map_seq f s) i == f (Seq.index s i))) (decreases Seq.length s)
  = map_seq_len f s;
    if Seq.length s = 0
    then ()
    else if i = 0
    then ()
    else map_seq_index f (tail s) (i-1)

let map_seq_append #a #b f s1 s2 =
  map_seq_len f s1;
  map_seq_len f s2;
  map_seq_len f (Seq.append s1 s2);
  Classical.forall_intro (map_seq_index f s1);
  Classical.forall_intro (map_seq_index f s2);
  Classical.forall_intro (map_seq_index f (Seq.append s1 s2));
  assert (Seq.equal (map_seq f (Seq.append s1 s2))
                    (Seq.append (map_seq f s1) (map_seq f s2)))
