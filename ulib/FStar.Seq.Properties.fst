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

#set-options "--max_fuel 0 --initial_fuel 0 --initial_ifuel 0 --max_ifuel 0"
open FStar.Seq.Base
module Seq = FStar.Seq.Base

let lseq (a: Type) (l: nat) : Type =
    s: Seq.seq a { Seq.length s == l }

let indexable (#a:Type) (s:Seq.seq a) (j:int) = 0 <= j /\ j < Seq.length s

val lemma_append_inj_l: #a:Type -> s1:seq a -> s2:seq a -> t1:seq a -> t2:seq a{length s1 = length t1 /\ equal (append s1 s2) (append t1 t2)} -> i:nat{i < length s1}
  -> Lemma (index s1 i == index t1 i)
let lemma_append_inj_l #a s1 s2 t1 t2 i =
  assert (index s1 i == (index (append s1 s2) i));
  assert (index t1 i == (index (append t1 t2) i))

val lemma_append_inj_r: #a:Type -> s1:seq a -> s2:seq a -> t1:seq a -> t2:seq a{length s1 = length t1 /\ length s2 = length t2 /\ equal (append s1 s2) (append t1 t2)} -> i:nat{i < length s2}
  -> Lemma (ensures  (index s2 i == index t2 i))
let lemma_append_inj_r #a s1 s2 t1 t2 i =
  assert (index s2 i == (index (append s1 s2) (i + length s1)));
  assert (index t2 i == (index (append t1 t2) (i + length t1)))

val lemma_append_len_disj: #a:Type -> s1:seq a -> s2:seq a -> t1:seq a -> t2:seq a {(length s1 = length t1 \/ length s2 = length t2) /\ (equal (append s1 s2) (append t1 t2))}
  -> Lemma (ensures (length s1 = length t1 /\ length s2 = length t2))
let lemma_append_len_disj #a s1 s2 t1 t2 =
  cut (length (append s1 s2) == length s1 + length s2);
  cut (length (append t1 t2) == length t1 + length t2)

val lemma_append_inj: #a:Type -> s1:seq a -> s2:seq a -> t1:seq a -> t2:seq a {length s1 = length t1 \/ length s2 = length t2}
  -> Lemma (requires (equal (append s1 s2) (append t1 t2)))
           (ensures (equal s1 t1 /\ equal s2 t2))
let lemma_append_inj #a s1 s2 t1 t2 =
  lemma_append_len_disj s1 s2 t1 t2;
  FStar.Classical.forall_intro #(i:nat{i < length s1}) #(fun i -> index s1 i == index t1 i) (lemma_append_inj_l s1 s2 t1 t2);
  FStar.Classical.forall_intro #(i:nat{i < length s2}) #(fun i -> index s2 i == index t2 i) (lemma_append_inj_r s1 s2 t1 t2)

val head: #a:Type -> s:seq a{length s > 0} -> Tot a
let head #a s = index s 0

val tail: #a:Type -> s:seq a{length s > 0} -> Tot (seq a)
let tail #a s = slice s 1 (length s)

val lemma_head_append: #a:Type -> s1:seq a{length s1 > 0} -> s2:seq a -> Lemma
  (head (append s1 s2) == head s1)
let lemma_head_append #a s1 s2 = ()

val lemma_tail_append: #a:Type -> s1:seq a{length s1 > 0} -> s2:seq a -> Lemma
  (tail (append s1 s2) == append (tail s1) s2)
let lemma_tail_append #a s1 s2 = cut (equal (tail (append s1 s2)) (append (tail s1) s2))

val last: #a:Type -> s:seq a{length s > 0} -> Tot a
let last #a s = index s (length s - 1)

val cons: #a:Type -> a -> seq a -> Tot (seq a)
let cons #a x s = append (create 1 x) s

val lemma_cons_inj: #a:Type -> v1:a -> v2:a -> s1:seq a -> s2:seq a
  -> Lemma (requires (equal (cons v1 s1) (cons v2 s2)))
          (ensures (v1 == v2 /\ equal s1 s2))
let lemma_cons_inj #a v1 v2 s1 s2 =
  let t1 = create 1 v1 in
  let t2 = create 1 v2 in
  lemma_append_inj t1 s1 t2 s2;
  assert(index t1 0 == index t2 0)

val split: #a:Type -> s:seq a -> i:nat{(0 <= i /\ i <= length s)} -> Tot (seq a * seq a)
let split #a s i = slice s 0 i, slice s i (length s)

val lemma_split : #a:Type -> s:seq a -> i:nat{(0 <= i /\ i <= length s)} -> Lemma
  (ensures (append (fst (split s i)) (snd (split s i)) == s))
let lemma_split #a s i =
  cut (equal (append (fst (split s i)) (snd (split s i)))  s)

val split_eq: #a:Type -> s:seq a -> i:nat{(0 <= i /\ i <= length s)} -> Pure
  (seq a * seq a)
  (requires True)
  (ensures (fun x -> (append (fst x) (snd x) == s)))
let split_eq #a s i =
  let x = split s i in
  lemma_split s i;
  x

val count : #a:eqtype -> a -> s:seq a -> Tot nat (decreases (length s))
let rec count #a x s =
  if length s = 0 then 0
  else if head s = x
  then 1 + count x (tail s)
  else count x (tail s)

val mem: #a:eqtype -> a -> seq a -> Tot bool
let mem #a x l = count x l > 0

#set-options "--max_fuel 1 --initial_fuel 1"
let rec mem_index (#a:eqtype) (x:a) (s:seq a)
    : Lemma (requires (mem x s))
            (ensures (exists i. index s i == x))
            (decreases (length s))
    = if length s = 0 then ()
      else if head s = x then ()
      else mem_index x (tail s)

(* index_mem:
   A utility function that finds the first index of
   `x` in `s`, given that we know the `x` is actually contained in `s` *)
let rec index_mem (#a:eqtype) (x:a) (s:seq a)
    : Pure nat
           (requires (mem x s))
           (ensures (fun i -> i < length s /\ index s i == x))
           (decreases (length s))
    = if head s = x then 0
      else 1 + index_mem x (tail s)

#set-options "--max_fuel 0 --initial_fuel 0 --initial_ifuel 0 --max_ifuel 0"
val swap: #a:Type -> s:seq a -> i:nat{i<length s} -> j:nat{j<length s} -> Tot (seq a)
let swap #a s i j = upd (upd s j (index s i)) i (index s j)

val lemma_slice_append: #a:Type -> s1:seq a{length s1 >= 1} -> s2:seq a -> Lemma
  (ensures (equal (append s1 s2) (append (slice s1 0 1) (append (slice s1 1 (length s1)) s2))))
let lemma_slice_append #a s1 s2 = ()

val lemma_slice_first_in_append: #a:Type -> s1:seq a -> s2:seq a -> i:nat{i <= length s1} -> Lemma
  (ensures (equal (slice (append s1 s2) i (length (append s1 s2))) (append (slice s1 i (length s1)) s2)))
  (decreases (length s1))
let rec lemma_slice_first_in_append #a s1 s2 i =
  if i = 0 then ()
  else lemma_slice_first_in_append #a (tail s1) s2 (i - 1)

val slice_upd: #a:Type -> s:seq a -> i:nat -> j:nat{i <= j /\ j <= length s}
  -> k:nat{k < length s} -> v:a -> Lemma
  (requires k < i \/ j <= k)
  (ensures  slice (upd s k v) i j == slice s i j)
  [SMTPat (slice (upd s k v) i j)]
let slice_upd #a s i j k v =
  lemma_eq_intro (slice (upd s k v) i j) (slice s i j)

val upd_slice: #a:Type -> s:seq a -> i:nat -> j:nat{i <= j /\ j <= length s}
  -> k:nat{k < j - i} -> v:a -> Lemma
  (requires i + k < j)
  (ensures  upd (slice s i j) k v == slice (upd s (i + k) v) i j)
  [SMTPat (upd (slice s i j) k v)]
let upd_slice #a s i j k v =
  lemma_eq_intro (upd (slice s i j) k v) (slice (upd s (i + k) v) i j)

// TODO: should be renamed cons_head_append, or something like that (because it is NOT related to (append (cons _ _) _))
val lemma_append_cons: #a:Type -> s1:seq a{length s1 > 0} -> s2:seq a -> Lemma
  (requires True)
  (ensures (equal (append s1 s2) (cons (head s1) (append (tail s1) s2))))
let rec lemma_append_cons #a s1 s2 = ()

val lemma_tl: #a:Type -> hd:a -> tl:seq a -> Lemma
  (ensures (equal (tail (cons hd tl)) tl))
let lemma_tl #a hd tl = ()

val sorted: #a:Type
          -> (a -> a -> Tot bool)
          -> s:seq a
          -> Tot bool (decreases (length s))
let rec sorted #a f s =
  if length s <= 1
  then true
  else let hd = head s in
       f hd (index s 1) && sorted f (tail s)

module F = FStar.FunctionalExtensionality

#set-options "--max_fuel 1 --initial_fuel 1"
let rec sorted_feq (#a:Type)
               (f g : (a -> a -> Tot bool))
               (s:seq a{forall x y. f x y == g x y})
   : Lemma (ensures (sorted f s <==> sorted g s))
           (decreases (length s))
   = if length s <= 1 then ()
     else sorted_feq f g (tail s)


val lemma_append_count: #a:eqtype -> lo:seq a -> hi:seq a -> Lemma
  (requires True)
  (ensures (forall x. count x (append lo hi) = (count x lo + count x hi)))
  (decreases (length lo))
let rec lemma_append_count #a lo hi =
  if length lo = 0
  then cut (equal (append lo hi) hi)
  else (cut (equal (cons (head lo) (append (tail lo) hi))
                (append lo hi));
        lemma_append_count (tail lo) hi;
        let tl_l_h = append (tail lo) hi in
        let lh = cons (head lo) tl_l_h in
        cut (equal (tail lh) tl_l_h))

val lemma_append_count_aux: #a:eqtype -> x:a -> lo:seq a -> hi:seq a -> Lemma
  (requires True)
  (ensures (count x (append lo hi) = (count x lo + count x hi)))
let lemma_append_count_aux #a x lo hi = lemma_append_count lo hi

val lemma_mem_inversion: #a:eqtype -> s:seq a{length s > 0} -> Lemma
  (ensures (forall x. mem x s = (x=head s || mem x (tail s))))
let lemma_mem_inversion #a s = ()

val lemma_mem_count: #a:eqtype -> s:seq a -> f:(a -> Tot bool) -> Lemma
  (requires (forall (i:nat{i<length s}). f (index s i)))
  (ensures (forall (x:a). mem x s ==> f x))
  (decreases (length s))
let rec lemma_mem_count #a s f =
  if length s = 0
  then ()
  else (let t = i:nat{i<length (tail s)} in
        cut (forall (i:t). index (tail s) i = index s (i + 1));
        lemma_mem_count (tail s) f)

val lemma_count_slice: #a:eqtype -> s:seq a -> i:nat{i<=length s} -> Lemma
  (requires True)
  (ensures (forall x. count x s = count x (slice s 0 i) + count x (slice s i (length s))))
  (decreases (length s))
let lemma_count_slice #a s i =
  cut (equal s (append (slice s 0 i) (slice s i (length s))));
  lemma_append_count (slice s 0 i) (slice s i (length s))

type total_order (a:eqtype) (f: (a -> a -> Tot bool)) =
    (forall a. f a a)                                           (* reflexivity   *)
    /\ (forall a1 a2. (f a1 a2 /\ a1<>a2)  <==> not (f a2 a1))  (* anti-symmetry *)
    /\ (forall a1 a2 a3. f a1 a2 /\ f a2 a3 ==> f a1 a3)        (* transitivity  *)
type tot_ord (a:eqtype) = f:(a -> a -> Tot bool){total_order a f}

val sorted_concat_lemma: #a:eqtype
                      -> f:(a -> a -> Tot bool){total_order a f}
                      -> lo:seq a{sorted f lo}
                      -> pivot:a
                      -> hi:seq a{sorted f hi}
                      -> Lemma (requires (forall y. (mem y lo ==> f y pivot)
                                                 /\ (mem y hi ==> f pivot y)))
                               (ensures (sorted f (append lo (cons pivot hi))))
                               (decreases (length lo))
let rec sorted_concat_lemma #a f lo pivot hi =
  if length lo = 0
  then (cut (equal (append lo (cons pivot hi)) (cons pivot hi));
        cut (equal (tail (cons pivot hi)) hi))
  else (sorted_concat_lemma f (tail lo) pivot hi;
        lemma_append_cons lo (cons pivot hi);
        lemma_tl (head lo) (append (tail lo) (cons pivot hi)))

abstract val split_5 : #a:Type -> s:seq a -> i:nat -> j:nat{i < j && j < length s} -> Pure (seq (seq a))
  (requires True)
  (ensures (fun x ->
            (length x = 5
             /\ equal s (append (index x 0) (append (index x 1) (append (index x 2) (append (index x 3) (index x 4)))))
             /\ equal (index x 0) (slice s 0 i)
             /\ equal (index x 1) (slice s i (i+1))
             /\ equal (index x 2) (slice s (i+1) j)
             /\ equal (index x 3) (slice s j (j + 1))
             /\ equal (index x 4) (slice s (j + 1) (length s)))))
let split_5 #a s i j =
  let frag_lo = slice s 0 i in
  let frag_i = slice s i (i + 1) in
  let frag_mid = slice s (i + 1) j in
  let frag_j = slice s j (j + 1) in
  let frag_hi = slice s (j + 1) (length s) in
  upd (upd (upd (upd (create 5 frag_lo) 1 frag_i) 2 frag_mid) 3 frag_j) 4 frag_hi

val lemma_swap_permutes_aux_frag_eq: #a:Type -> s:seq a -> i:nat{i<length s} -> j:nat{i <= j && j<length s}
                          -> i':nat -> j':nat{i' <= j' /\ j'<=length s /\
                                              (j < i'  //high slice
                                              \/ j' <= i //low slice
                                              \/ (i < i' /\ j' <= j)) //mid slice
                                              }
                          -> Lemma (ensures (slice s i' j' == slice (swap s i j) i' j'
                                            /\ slice s i (i + 1) == slice (swap s i j) j (j + 1)
                                            /\ slice s j (j + 1) == slice (swap s i j) i (i + 1)))
let lemma_swap_permutes_aux_frag_eq #a s i j i' j' =
  cut (equal (slice s i' j') (slice (swap s i j) i' j'));
  cut (equal (slice s i (i + 1))  (slice (swap s i j) j (j + 1)));
  cut (equal (slice s j (j + 1))  (slice (swap s i j) i (i + 1)))

#set-options "--z3rlimit 20"
val lemma_swap_permutes_aux: #a:eqtype -> s:seq a -> i:nat{i<length s} -> j:nat{i <= j && j<length s} -> x:a -> Lemma
  (requires True)
  (ensures (count x s = count x (swap s i j)))
let lemma_swap_permutes_aux #a s i j x =
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
#reset-options

#set-options "--max_fuel 0 --initial_fuel 0"
type permutation (a:eqtype) (s1:seq a) (s2:seq a) =
       (forall i. count i s1 = count i s2)
let lemma_swap_permutes (#a:eqtype) (s:seq a) (i:nat{i<length s}) (j:nat{i <= j && j<length s})
  : Lemma (permutation a s (swap s i j))
  = FStar.Classical.forall_intro
                    #a
                    #(fun x -> count x s = count x (swap s i j))
                    (lemma_swap_permutes_aux s i j)

(* perm_len:
     A lemma that shows that two sequences that are permutations
     of each other also have the same length
*)
//a proof optimization: Z3 only needs to unfold the recursive definition of `count` once
#set-options "--initial_fuel 1 --max_fuel 1"
let rec perm_len (#a:eqtype) (s1 s2: seq a)
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
         then (assert (permutation a s1_tl s2_tl); perm_len s1_tl s2_tl)
         else let i = index_mem s1_hd s2 in
              let s_pfx, s_sfx = split_eq s2 i in
              assert (equal s_sfx (append (create 1 s1_hd) (tail s_sfx)));
              let s2' = append s_pfx (tail s_sfx) in
              lemma_append_count s_pfx s_sfx;
              lemma_append_count (create 1 s1_hd) (tail s_sfx);
              lemma_append_count s_pfx (tail s_sfx);
              assert (permutation a s1_tl s2');
              perm_len s1_tl s2'


val cons_perm: #a:eqtype -> tl:seq a -> s:seq a{length s > 0} ->
         Lemma (requires (permutation a tl (tail s)))
               (ensures (permutation a (cons (head s) tl) s))
let cons_perm #a tl s = lemma_tl (head s) tl

#set-options "--max_fuel 2 --initial_fuel 2"
val lemma_mem_append : #a:eqtype -> s1:seq a -> s2:seq a
      -> Lemma (ensures (forall x. mem x (append s1 s2) <==> (mem x s1 || mem x s2)))
let lemma_mem_append #a s1 s2 = lemma_append_count s1 s2

val lemma_slice_cons: #a:eqtype -> s:seq a -> i:nat -> j:nat{i < j && j <= length s}
  -> Lemma (ensures (forall x. mem x (slice s i j) <==> (x = index s i || mem x (slice s (i + 1) j))))
let lemma_slice_cons #a s i j =
  cut (equal (slice s i j) (append (create 1 (index s i)) (slice s (i + 1) j)));
  lemma_mem_append (create 1 (index s i)) (slice s (i + 1) j)

val lemma_slice_snoc: #a:eqtype -> s:seq a -> i:nat -> j:nat{i < j && j <= length s}
  -> Lemma (ensures (forall x. mem x (slice s i j) <==> (x = index s (j - 1) || mem x (slice s i (j - 1)))))
let lemma_slice_snoc #a s i j =
  cut (equal (slice s i j) (append (slice s i (j - 1)) (create 1 (index s (j - 1)))));
  lemma_mem_append (slice s i (j - 1)) (create 1 (index s (j - 1)))

val lemma_ordering_lo_snoc: #a:eqtype -> f:tot_ord a -> s:seq a -> i:nat -> j:nat{i <= j && j < length s} -> pv:a
   -> Lemma (requires ((forall y. mem y (slice s i j) ==> f y pv) /\ f (index s j) pv))
            (ensures ((forall y. mem y (slice s i (j + 1)) ==> f y pv)))
let lemma_ordering_lo_snoc #a f s i j pv =
  cut (equal (slice s i (j + 1)) (append (slice s i j) (create 1 (index s j))));
  lemma_mem_append (slice s i j) (create 1 (index s j))

val lemma_ordering_hi_cons: #a:eqtype -> f:tot_ord a -> s:seq a -> back:nat -> len:nat{back < len && len <= length s} -> pv:a
   -> Lemma (requires ((forall y. mem y (slice s (back + 1) len) ==> f pv y) /\ f pv (index s back)))
            (ensures ((forall y. mem y (slice s back len) ==> f pv y)))
let lemma_ordering_hi_cons #a f s back len pv =
  cut (equal (slice s back len) (append (create 1 (index s back)) (slice s (back + 1) len)));
  lemma_mem_append (create 1 (index s back)) (slice s (back + 1) len)

#set-options "--max_fuel 0 --initial_fuel 0"
val swap_frame_lo : #a:Type -> s:seq a -> lo:nat -> i:nat{lo <= i} -> j:nat{i <= j && j < length s}
     -> Lemma (ensures (slice s lo i == slice (swap s i j) lo i))
let swap_frame_lo #a s lo i j = cut (equal (slice s lo i) (slice (swap s i j) lo i))

val swap_frame_lo' : #a:Type -> s:seq a -> lo:nat -> i':nat {lo <= i'} -> i:nat{i' <= i} -> j:nat{i <= j && j < length s}
     -> Lemma (ensures (slice s lo i' == slice (swap s i j) lo i'))
let swap_frame_lo' #a s lo i' i j = cut (equal (slice s lo i') (slice (swap s i j) lo i'))

val swap_frame_hi : #a:Type -> s:seq a -> i:nat -> j:nat{i <= j} -> k:nat{j < k} -> hi:nat{k <= hi /\ hi <= length s}
     -> Lemma (ensures (slice s k hi == slice (swap s i j) k hi))
let swap_frame_hi #a s i j k hi = cut (equal (slice s k hi) (slice (swap s i j) k hi))

val lemma_swap_slice_commute  : #a:Type -> s:seq a -> start:nat -> i:nat{start <= i} -> j:nat{i <= j} -> len:nat{j < len && len <= length s}
    -> Lemma (ensures (slice (swap s i j) start len == (swap (slice s start len) (i - start) (j - start))))
let lemma_swap_slice_commute #a s start i j len = cut (equal (slice (swap s i j) start len) (swap (slice s start len) (i - start) (j - start)))

val lemma_swap_permutes_slice : #a:eqtype -> s:seq a -> start:nat -> i:nat{start <= i} -> j:nat{i <= j} -> len:nat{j < len && len <= length s}
   -> Lemma (ensures (permutation a (slice s start len) (slice (swap s i j) start len)))
let lemma_swap_permutes_slice #a s start i j len =
  lemma_swap_slice_commute s start i j len;
  lemma_swap_permutes (slice s start len) (i - start) (j - start)

#set-options "--initial_fuel 0 --max_fuel 0"
(* replaces the [i,j) sub-sequence of s1 with the corresponding sub-sequence of s2 *)
val splice: #a:Type -> s1:seq a -> i:nat -> s2:seq a{length s1=length s2} -> j:nat{i <= j /\ j <= (length s2)} -> Tot (seq a)
let splice #a s1 i s2 j = Seq.append (slice s1 0 i) (Seq.append (slice s2 i j) (slice s1 j (length s1)))

(* replace with sub *)
let replace_subseq (#a:Type0) (s:Seq.seq a) (i:nat) (j:nat{i <= j /\ j <= length s}) (sub:Seq.seq a{length sub == j - i}) :Tot (Seq.seq a)
  = Seq.append (Seq.slice s 0 i) (Seq.append sub (Seq.slice s j (Seq.length s)))

val splice_refl : #a:Type -> s:seq a -> i:nat -> j:nat{i <= j && j <= length s}
  -> Lemma
  (ensures (s == splice s i s j))
let splice_refl #a s i j = cut (equal s (splice s i s j))

val lemma_swap_splice : #a:Type -> s:seq a -> start:nat -> i:nat{start <= i} -> j:nat{i <= j} -> len:nat{j < len && len <= length s}
   -> Lemma
        (ensures (swap s i j == splice s start (swap s i j) len))
let lemma_swap_splice #a s start i j len = cut (equal (swap s i j) (splice s start (swap s i j) len))

val lemma_seq_frame_hi: #a:Type -> s1:seq a -> s2:seq a{length s1 = length s2} -> i:nat -> j:nat{i <= j} -> m:nat{j <= m} -> n:nat{m < n && n <= length s1}
  -> Lemma
  (requires (s1 == (splice s2 i s1 j)))
  (ensures  ((slice s1 m n == slice s2 m n) /\ (index s1 m == index s2 m)))
let lemma_seq_frame_hi #a s1 s2 i j m n =
  cut (equal (slice s1 m n) (slice s2 m n))

val lemma_seq_frame_lo: #a:Type -> s1:seq a -> s2:seq a{length s1 = length s2} -> i:nat -> j:nat{i <= j} -> m:nat{j < m} -> n:nat{m <= n && n <= length s1}
  -> Lemma
  (requires (s1 == (splice s2 m s1 n)))
  (ensures  ((slice s1 i j == slice s2 i j) /\ (index s1 j == index s2 j)))
let lemma_seq_frame_lo #a s1 s2 i j m n =
  cut (equal (slice s1 i j) (slice s2 i j))

val lemma_tail_slice: #a:Type -> s:seq a -> i:nat -> j:nat{i < j && j <= length s}
  -> Lemma
  (requires True)
  (ensures (tail (slice s i j) == slice s (i + 1) j))
  [SMTPat (tail (slice s i j))]
let lemma_tail_slice #a s i j =
  cut (equal (tail (slice s i j)) (slice s (i + 1) j))

val lemma_weaken_frame_right : #a:Type -> s1:seq a -> s2:seq a{length s1 = length s2} -> i:nat -> j:nat -> k:nat{i <= j && j <= k && k <= length s1}
  -> Lemma
  (requires (s1 == splice s2 i s1 j))
  (ensures (s1 == splice s2 i s1 k))
let lemma_weaken_frame_right #a s1 s2 i j k = cut (equal s1 (splice s2 i s1 k))

val lemma_weaken_frame_left : #a:Type -> s1:seq a -> s2:seq a{length s1 = length s2} -> i:nat -> j:nat -> k:nat{i <= j && j <= k && k <= length s1}
  -> Lemma
  (requires (s1 == splice s2 j s1 k))
  (ensures (s1 == splice s2 i s1 k))
let lemma_weaken_frame_left #a s1 s2 i j k = cut (equal s1 (splice s2 i s1 k))

val lemma_trans_frame : #a:Type -> s1:seq a -> s2:seq a -> s3:seq a{length s1 = length s2 /\ length s2 = length s3} -> i:nat -> j:nat{i <= j && j <= length s1}
  -> Lemma
  (requires ((s1 == splice s2 i s1 j) /\ s2 == splice s3 i s2 j))
  (ensures (s1 == splice s3 i s1 j))
let lemma_trans_frame #a s1 s2 s3 i j = cut (equal s1 (splice s3 i s1 j))

val lemma_weaken_perm_left: #a:eqtype -> s1:seq a -> s2:seq a{length s1 = length s2} -> i:nat -> j:nat -> k:nat{i <= j /\ j <= k /\ k <= length s1}
  -> Lemma
  (requires (s1 == splice s2 j s1 k /\ permutation a (slice s2 j k) (slice s1 j k)))
  (ensures (permutation a (slice s2 i k) (slice s1 i k)))
let lemma_weaken_perm_left #a s1 s2 i j k =
  cut (equal (slice s2 i k) (append (slice s2 i j)
                                 (slice s2 j k)));
  cut (equal (slice s1 i k) (append (slice s2 i j)
                                 (slice s1 j k)));
  lemma_append_count (slice s2 i j) (slice s2 j k);
  lemma_append_count (slice s2 i j) (slice s1 j k)

val lemma_weaken_perm_right: #a:eqtype -> s1:seq a -> s2:seq a{length s1 = length s2} -> i:nat -> j:nat -> k:nat{i <= j /\ j <= k /\ k <= length s1}
  -> Lemma
  (requires (s1 == splice s2 i s1 j /\ permutation a (slice s2 i j) (slice s1 i j)))
  (ensures (permutation a (slice s2 i k) (slice s1 i k)))
let lemma_weaken_perm_right #a s1 s2 i j k =
  cut (equal (slice s2 i k) (append (slice s2 i j)
                                 (slice s2 j k)));
  cut (equal (slice s1 i k) (append (slice s1 i j)
                                 (slice s2 j k)));
  lemma_append_count (slice s2 i j) (slice s2 j k);
  lemma_append_count (slice s1 i j) (slice s2 j k)

val lemma_trans_perm: #a:eqtype -> s1:seq a -> s2:seq a -> s3:seq a{length s1 = length s2 /\ length s2 = length s3} -> i:nat -> j:nat{i<=j && j <= length s1}
 -> Lemma
  (requires (permutation a (slice s1 i j) (slice s2 i j)
             /\ permutation a (slice s2 i j) (slice s3 i j)))
  (ensures (permutation a (slice s1 i j) (slice s3 i j)))
let lemma_trans_perm #a s1 s2 s3 i j = ()


(*New addtions, please review*)

val snoc : #a:Type -> seq a -> a -> Tot (seq a)
let snoc #a s x = Seq.append s (Seq.create 1 x)

let lemma_cons_snoc (#a:Type) (hd:a) (s:Seq.seq a) (tl:a)
  : Lemma (requires True)
          (ensures (Seq.equal (cons hd (snoc s tl))
                              (snoc (cons hd s) tl)))
  = ()

val lemma_tail_snoc: #a:Type -> s:Seq.seq a{Seq.length s > 0} -> x:a
                     -> Lemma (ensures (tail (snoc s x) == snoc (tail s) x))
let lemma_tail_snoc #a s x = lemma_slice_first_in_append s (Seq.create 1 x) 1

val lemma_snoc_inj: #a:Type -> s1:seq a -> s2:seq a -> v1:a -> v2:a
  -> Lemma (requires (equal (snoc s1 v1) (snoc s2 v2)))
          (ensures (v1 == v2 /\ equal s1 s2))
let lemma_snoc_inj #a s1 s2 v1 v2 =
  let t1 = create 1 v1 in
  let t2 = create 1 v2 in
  lemma_append_inj s1 t1 s2 t2;
  assert(head t1  == head t2)

#set-options "--initial_fuel 2 --max_fuel 2"
val lemma_mem_snoc : #a:eqtype -> s:Seq.seq a -> x:a ->
   Lemma (ensures (forall y. mem y (snoc s x) <==> mem y s \/ x=y))
let lemma_mem_snoc #a s x = lemma_append_count s (Seq.create 1 x)

val find_l: #a:Type -> f:(a -> Tot bool) -> l:seq a -> Tot (o:option a{Some? o ==> f (Some?.v o)})
  (decreases (Seq.length l))
let rec find_l #a f l =
  if Seq.length l = 0 then None
  else if f (head l) then Some (head l)
  else find_l f (tail l)

val ghost_find_l: #a:Type -> f:(a -> GTot bool) -> l:seq a -> GTot (o:option a{Some? o ==> f (Some?.v o)})
  (decreases (Seq.length l))
let rec ghost_find_l #a f l =
  if Seq.length l = 0 then None
  else if f (head l) then Some (head l)
  else ghost_find_l f (tail l)

val find_append_some: #a:Type -> s1:seq a -> s2:seq a -> f:(a -> Tot bool) -> Lemma
  (requires (Some? (find_l f s1)))
  (ensures (find_l f (append s1 s2) == find_l f s1))
  (decreases (length s1))
let rec find_append_some #a s1 s2 f =
  if f (head s1) then ()
  else
    let _ = cut (equal (tail (append s1 s2)) (append (tail s1) s2)) in
    find_append_some (tail s1) s2 f

val find_append_none: #a:Type -> s1:seq a -> s2:seq a -> f:(a -> Tot bool) -> Lemma
  (requires (None? (find_l f s1)))
  (ensures (find_l f (append s1 s2) == find_l f s2))
  (decreases (length s1))
let rec find_append_none #a s1 s2 f =
  if Seq.length s1 = 0 then cut (equal (append s1 s2) s2)
  else
    let _ = cut (equal (tail (append s1 s2)) (append (tail s1) s2)) in
    find_append_none (tail s1) s2 f

val find_append_none_s2: #a:Type -> s1:seq a -> s2:seq a -> f:(a -> Tot bool) -> Lemma
  (requires (None? (find_l f s2)))
  (ensures  (find_l f (append s1 s2) == find_l f s1))
  (decreases (length s1))
let rec find_append_none_s2 #a s1 s2 f =
  if Seq.length s1 = 0 then cut (equal (append s1 s2) s2)
  else if f (head s1) then ()
  else begin
    find_append_none_s2 (tail s1) s2 f;
    cut (equal (tail (append s1 s2)) (append (tail s1) s2))
  end

val find_snoc: #a:Type -> s:Seq.seq a -> x:a -> f:(a -> Tot bool)
               -> Lemma (ensures (let res = find_l f (snoc s x) in
                                 match res with
                                 | None -> find_l f s == None /\ not (f x)
                                 | Some y -> res == find_l f s \/ (f x /\ x==y)))
                 (decreases (Seq.length s))
let find_snoc #a s x f =
  if Some? (find_l f s) then find_append_some s (Seq.create 1 x) f
  else find_append_none s (Seq.create 1 x) f

let un_snoc (#a:Type) (s:seq a{length s <> 0}) : Tot (r:(seq a * a){s == snoc (fst r) (snd r)}) =
  let s', a = split s (length s - 1) in
  assert (Seq.equal (snoc s' (Seq.index a 0)) s);
  s', Seq.index a 0

let un_snoc_snoc (#a:Type) (s:seq a) (x:a) : Lemma (un_snoc (snoc s x) == (s, x)) =
  let s', x = un_snoc (snoc s x) in
  assert (Seq.equal s s')

val find_r: #a:Type -> f:(a -> Tot bool) -> l:seq a -> Tot (o:option a{Some? o ==> f (Some?.v o)})
  (decreases (Seq.length l))
let rec find_r #a f l =
  if Seq.length l = 0 then None
  else let prefix, last = un_snoc l in
       if f last then Some last
       else find_r f prefix

#set-options "--initial_ifuel 1 --max_ifuel 1 --initial_fuel 0 --max_fuel 0"
type found (i:nat) = True
val seq_find_aux : #a:Type -> f:(a -> Tot bool) -> l:seq a
                   -> ctr:nat{ctr <= Seq.length l}
                   -> Pure (option a)
                      (requires (forall (i:nat{ i < Seq.length l /\ i >= ctr}).
                                        not (f (Seq.index l i) )))
                      (ensures (function
                                  | None -> forall (i:nat{i < Seq.length l}).  not (f (Seq.index l i))
                                  | Some x -> f x /\  (exists (i:nat{i < Seq.length l}). {:pattern (found i)}
                                                            found i /\
                                                            x == Seq.index l i)))

let rec seq_find_aux #a f l ctr =
  match ctr with
  | 0 -> None
  | _ -> let i = ctr - 1 in
  if f (Seq.index l i)
  then (
     cut (found i);
     Some (Seq.index l i))
  else seq_find_aux f l i

val seq_find: #a:Type -> f:(a -> Tot bool) -> l:seq a ->
                     Pure (option a)
                          (requires True)
                          (ensures (function
                                      | None -> forall (i:nat{i < Seq.length l}). not (f (Seq.index l i))
                                      | Some x -> f x /\ (exists (i:nat{i < Seq.length l}).{:pattern (found i)}
                                                          found i /\ x == Seq.index l i)))

let seq_find #a f l =
  seq_find_aux f l (Seq.length l)

let find_mem (#a:eqtype) (s:seq a) (f:a -> Tot bool) (x:a{f x})
   : Lemma (requires (mem x s))
           (ensures (Some? (seq_find f s) /\ f (Some?.v (seq_find f s))))
   = match seq_find f s with
     | None -> mem_index x s
     | Some _ -> ()

let for_all
  (#a: Type)
  (f: (a -> Tot bool))
  (l: seq a)
: Pure bool
  (requires True)
  (ensures (fun b -> (b == true <==> (forall (i: nat {i < Seq.length l} ) . f (index l i) == true))))
= None? (seq_find (fun i -> not (f i)) l)

#set-options "--initial_ifuel 1 --max_ifuel 1 --initial_fuel 1 --max_fuel 1"
val seq_mem_k: #a:eqtype -> s:seq a -> n:nat{n < Seq.length s} ->
    Lemma (requires True)
          (ensures (mem (Seq.index s n) s))
          (decreases n)
          [SMTPat (mem (Seq.index s n) s)]
let rec seq_mem_k #a s n =
  if n = 0 then ()
  else let tl = tail s in
       seq_mem_k tl (n - 1)

module L = FStar.List.Tot

val seq_to_list: #a:Type -> s:seq a -> Tot (l:list a{L.length l = length s}) (decreases (length s))
let rec seq_to_list #a s =
  if length s = 0 then []
  else index s 0::seq_to_list (slice s 1 (length s))

val seq_of_list: #a:Type -> l:list a -> Tot (s:seq a{L.length l = length s})
let rec seq_of_list #a l =
  match l with
  | [] -> Seq.empty #a
  | hd::tl -> create 1 hd @| seq_of_list tl

val lemma_seq_list_bij: #a:Type -> s:seq a -> Lemma
  (requires (True))
  (ensures  (seq_of_list (seq_to_list s) == s))
  (decreases (length s))
let rec lemma_seq_list_bij #a s =
  if length s = 0 then (
    Seq.lemma_eq_intro s (seq_of_list (seq_to_list s))
  )
  else (
    lemma_seq_list_bij (slice s 1 (length s));
    lemma_eq_intro s (seq_of_list (seq_to_list s))
  )

val lemma_list_seq_bij: #a:Type -> l:list a -> Lemma
  (requires (True))
  (ensures  (seq_to_list (seq_of_list l) == l))
  (decreases (L.length l))
let rec lemma_list_seq_bij #a l =
  if L.length l = 0 then ()
  else (
    lemma_list_seq_bij #a (L.tl l);
    let hd = L.hd l in let tl = L.tl l in
    cut (seq_to_list (seq_of_list tl) == tl);
    cut (seq_of_list l == create 1 hd @| seq_of_list tl);
    lemma_eq_intro (seq_of_list tl) (slice (seq_of_list l) 1 (length (seq_of_list l)))
  )

unfold let createL_post (#a:Type0) (l:list a) (s:seq a) : GTot Type0 =
  normalize (L.length l = length s) /\ seq_to_list s == l /\ seq_of_list l == s

val createL: #a:Type0 -> l:list a -> Pure (seq a)
  (requires True)
  (ensures (fun s -> createL_post #a l s))
let createL #a l =
  let s = seq_of_list l in
  lemma_list_seq_bij l;
  s

val lemma_index_is_nth: #a:Type -> s:seq a -> i:nat{i < length s} -> Lemma
  (requires True)
  (ensures  (L.index (seq_to_list s) i == index s i))
  (decreases i)
let rec lemma_index_is_nth #a s i =
  if i = 0 then ()
  else (
    lemma_index_is_nth (slice s 1 (length s)) (i-1)
  )

////////////////////////////////////////////////////////////////////////////////
//s `contains` x : Type0
//    An undecidable version of `mem`,
//    for when the sequence payload is not an eqtype
////////////////////////////////////////////////////////////////////////////////
abstract let contains (#a:Type) (s:seq a) (x:a) : Tot Type0 =
  exists (k:nat). k < Seq.length s /\ Seq.index s k == x

let contains_intro (#a:Type) (s:seq a) (k:nat) (x:a)
  : Lemma (k < Seq.length s /\ Seq.index s k == x
            ==>
           s `contains` x)
  = ()

let contains_elim (#a:Type) (s:seq a) (x:a)
  : Lemma (s `contains` x
            ==>
          (exists (k:nat). k < Seq.length s /\ Seq.index s k == x))
  = ()

let lemma_contains_empty (#a:Type) : Lemma (forall (x:a). ~ (contains Seq.empty x)) = ()

let lemma_contains_singleton (#a:Type) (x:a) : Lemma (forall (y:a). contains (create 1 x) y ==> y == x) = ()

private let intro_append_contains_from_disjunction (#a:Type) (s1:seq a) (s2:seq a) (x:a)
    : Lemma (requires s1 `contains` x \/ s2 `contains` x)
            (ensures (append s1 s2) `contains` x)
    = let open FStar.Classical in
      let open FStar.StrongExcludedMiddle in
      let open FStar.Squash in
      if strong_excluded_middle (s1 `contains` x)
      then ()
      else let s = append s1 s2 in
           exists_elim (s `contains` x) (get_proof (s2 `contains` x)) (fun k ->
           assert (Seq.index s (Seq.length s1 + k) == x))

let append_contains_equiv (#a:Type) (s1:seq a) (s2:seq a) (x:a)
  : Lemma ((append s1 s2) `contains` x
            <==>
           (s1 `contains` x \/ s2 `contains` x))
  = FStar.Classical.move_requires (intro_append_contains_from_disjunction s1 s2) x

val contains_snoc : #a:Type -> s:Seq.seq a -> x:a ->
   Lemma (ensures (forall y. (snoc s x) `contains` y  <==> s `contains` y \/ x==y))
let contains_snoc #a s x =
  FStar.Classical.forall_intro (append_contains_equiv s (Seq.create 1 x))

let rec lemma_find_l_contains (#a:Type) (f:a -> Tot bool) (l:seq a)
  : Lemma (requires True) (ensures Some? (find_l f l) ==> l `contains` (Some?.v (find_l f l)))
          (decreases (Seq.length l))
  = if length l = 0 then ()
    else if f (head l) then ()
    else lemma_find_l_contains f (tail l)

let contains_cons (#a:Type) (hd:a) (tl:Seq.seq a) (x:a)
  : Lemma ((cons hd tl) `contains` x
           <==>
           (x==hd \/ tl `contains` x))
  = append_contains_equiv (Seq.create 1 hd) tl x

let append_cons_snoc (#a:Type) (u: Seq.seq a) (x:a) (v:Seq.seq a)
    : Lemma (Seq.equal (Seq.append u (cons x v))
                       (Seq.append (snoc u x) v))
    = ()

let append_slices (#a:Type) (s1:Seq.seq a) (s2:Seq.seq a)
   : Lemma ( Seq.equal s1 (Seq.slice (Seq.append s1 s2) 0 (Seq.length s1)) /\
             Seq.equal s2 (Seq.slice (Seq.append s1 s2) (Seq.length s1) (Seq.length s1 + Seq.length s2)) /\
             (forall (i:nat) (j:nat).
                i <= j /\ j <= Seq.length s2 ==>
                Seq.equal (Seq.slice s2 i j)
                          (Seq.slice (Seq.append s1 s2) (Seq.length s1 + i) (Seq.length s1 + j))))
   = ()


val find_l_none_no_index (#a:Type) (s:Seq.seq a) (f:(a -> Tot bool)) :
  Lemma (requires (None? (find_l f s)))
        (ensures (forall (i:nat{i < Seq.length s}). not (f (Seq.index s i))))
        (decreases (Seq.length s))
#reset-options
let rec find_l_none_no_index #a s f =
  if Seq.length s = 0
  then ()
  else (assert (not (f (head s)));
        assert (None? (find_l f (tail s)));
        find_l_none_no_index (tail s) f;
        assert (Seq.equal s (cons (head s) (tail s)));
        find_append_none (create 1 (head s)) (tail s) f)

(** More properties, with new naming conventions *)

let suffix_of
  (#a: Type)
  (s_suff s: seq a)
= exists s_pref . (s == append s_pref s_suff)

let cons_head_tail
  (#a: Type)
  (s: seq a {length s > 0})
: Lemma
  (requires True)
  (ensures (s == cons (head s) (tail s)))
  [SMTPat (cons (head s) (tail s))]
= let _ : squash (slice s 0 1 == create 1 (index s 0)) =
      lemma_index_slice s 0 1 0;
      lemma_index_create 1 (index s 0) 0;
      lemma_eq_elim (slice s 0 1) (create 1 (index s 0))
  in
  lemma_split s 1

let head_cons
  (#a: Type)
  (x: a)
  (s: seq a)
: Lemma
  (ensures (head (cons x s) == x))
= ()

let suffix_of_tail
  (#a: Type)
  (s: seq a {length s > 0})
: Lemma
  (requires True)
  (ensures ((tail s) `suffix_of` s))
  [SMTPat ((tail s) `suffix_of` s)]
= cons_head_tail s

let index_cons_l
  (#a: Type)
  (c: a)
  (s: seq a)
: Lemma
  (ensures (index (cons c s) 0 == c))
= ()

let index_cons_r
  (#a: Type)
  (c: a)
  (s: seq a)
  (i: nat {1 <= i /\ i <= length s})
: Lemma
  (ensures (index (cons c s) i == index s (i - 1)))
= ()

let append_cons
  (#a: Type)
  (c: a)
  (s1 s2: seq a)
: Lemma
  (ensures (append (cons c s1) s2 == cons c (append s1 s2)))
= lemma_eq_elim (append (cons c s1) s2) (cons c (append s1 s2))

let index_tail
  (#a: Type)
  (s: seq a {length s > 0})
  (i: nat {i < length s - 1} )
: Lemma
  (ensures (index (tail s) i == index s (i + 1)))
= ()

let mem_cons
  (#a:eqtype)
  (x:a)
  (s:seq a)
: Lemma
  (ensures (forall y. mem y (cons x s) <==> mem y s \/ x=y))
= lemma_append_count (create 1 x) s

let snoc_slice_index
  (#a: Type)
  (s: seq a)
  (i: nat)
  (j: nat {i <= j /\ j < length s} )
: Lemma
  (requires True)
  (ensures (snoc (slice s i j) (index s j) == slice s i (j + 1)))
  [SMTPat (snoc (slice s i j) (index s j))]
= lemma_eq_elim (snoc (slice s i j) (index s j)) (slice s i (j + 1))

let cons_index_slice
  (#a: Type)
  (s: seq a)
  (i: nat)
  (j: nat {i < j /\ j <= length s} )
: Lemma
  (requires True)
  (ensures (cons (index s i) (slice s (i + 1) j) == slice s i j))
  [SMTPat (cons (index s i) (slice s (i + 1) j))]
= lemma_eq_elim (cons (index s i) (slice s (i + 1) j)) (slice s i j)

let slice_is_empty
  (#a: Type)
  (s: seq a)
  (i: nat {i <= length s})
: Lemma
  (requires True)
  (ensures (slice s i i == Seq.empty))
  [SMTPat (slice s i i)]
= lemma_eq_elim (slice s i i) Seq.empty

let slice_length
  (#a: Type)
  (s: seq a)
: Lemma
  (requires True)
  (ensures (slice s 0 (length s) == s))
  [SMTPat (slice s 0 (length s))]
= lemma_eq_elim (slice s 0 (length s)) s

let slice_slice
  (#a: Type)
  (s: seq a)
  (i1: nat)
  (j1: nat {i1 <= j1 /\ j1 <= length s} )
  (i2: nat)
  (j2: nat {i2 <= j2 /\ j2 <= j1 - i1} )
: Lemma
  (requires True)
  (ensures (slice (slice s i1 j1) i2 j2 == slice s (i1 + i2) (i1 + j2)))
  [SMTPat (slice (slice s i1 j1) i2 j2)]
= lemma_eq_elim (slice (slice s i1 j1) i2 j2) (slice s (i1 + i2) (i1 + j2))

let lemma_seq_of_list_induction (#a:Type) (l:list a)
  :Lemma (requires True)
         (ensures (let s = seq_of_list l in
                   match l with
                   | []    -> Seq.equal s empty
                   | hd::tl -> head s == hd /\ tail s == seq_of_list tl))
  = if List.Tot.length l > 0 then lemma_tl (List.Tot.hd l) (seq_of_list (List.Tot.tl l))

let rec lemma_seq_of_list_index (#a:Type) (l:list a) (i:nat{i < List.Tot.length l})
  :Lemma (requires True)
         (ensures  (index (seq_of_list l) i == List.Tot.index l i))
         [SMTPat (index (seq_of_list l) i)]
  = match l with
    | []    -> ()
    | hd::tl -> if i = 0 then () else lemma_seq_of_list_index tl (i - 1)

[@(deprecated "seq_of_list")]
let of_list (#a:Type) (l:list a) :seq a = seq_of_list l

let seq_of_list_tl
  (#a: Type)
  (l: list a { List.Tot.length l > 0 } )
: Lemma
  (requires True)
  (ensures (seq_of_list (List.Tot.tl l) == tail (seq_of_list l))) =
  lemma_seq_of_list_induction l;
  ()

let rec mem_seq_of_list
  (#a: eqtype)
  (x: a)
  (l: list a)
: Lemma
  (requires True)
  (ensures (mem x (seq_of_list l) == List.Tot.mem x l))
  [SMTPat (mem x (seq_of_list l))]
= match l with
  | [] -> ()
  | y :: q ->
    let _ : squash (head (seq_of_list l) == y) = () in
    let _ : squash (tail (seq_of_list l) == seq_of_list q) = seq_of_list_tl l in
    let _ : squash (mem x (seq_of_list l) == (x = y || mem x (seq_of_list q))) =
     lemma_mem_inversion (seq_of_list l)
    in
    mem_seq_of_list x q

(** Dealing efficiently with `seq_of_list` by meta-evaluating conjunctions over
an entire list. *)
#set-options "--max_fuel 1"

let rec explode_and (#a: Type)
  (i: nat)
  (s: seq a { i <= length s })
  (l: list a { List.Tot.length l + i = length s }):
  Tot Type
  (decreases (List.Tot.length l))
=
  match l with
  | [] -> True
  | hd :: tl ->
      index s i == hd /\ explode_and (i + 1) s tl

unfold
let pointwise_and s l =
  norm [ iota; zeta; primops; delta_only [ `%(explode_and) ] ] (explode_and 0 s l)

val intro_of_list': #a:Type ->
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

let rec intro_of_list' #a i s l =
  match l with
  | [] -> ()
  | hd :: tl ->
      intro_of_list' (i + 1) s tl

let intro_of_list (#a: Type) (s: seq a) (l: list a):
  Lemma
    (requires (
      List.Tot.length l = length s /\
      pointwise_and s l))
    (ensures (
      s == seq_of_list l))
=
  intro_of_list' 0 s l

val elim_of_list': #a:Type ->
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

let rec elim_of_list' #a i s l =
  match l with
  | [] -> ()
  | hd :: tl ->
      lemma_seq_of_list_induction l;
      elim_of_list' (i + 1) s tl

let elim_of_list (#a: Type) (l: list a):
  Lemma
    (ensures (
      let s = seq_of_list l in
      pointwise_and s l))
=
  elim_of_list' 0 (seq_of_list l) l

#reset-options

(****** sortWith ******)
let sortWith (#a:eqtype) (f:a -> a -> Tot int) (s:seq a) :seq a
  = seq_of_list (List.Tot.Base.sortWith f (seq_to_list s))

let rec lemma_seq_to_list_permutation (#a:eqtype) (s:seq a)
  :Lemma (requires True) (ensures (forall x. count x s == List.Tot.Base.count x (seq_to_list s))) (decreases (length s))
  = if length s > 0 then lemma_seq_to_list_permutation (slice s 1 (length s))

let rec lemma_seq_of_list_permutation (#a:eqtype) (l:list a)
  :Lemma (forall x. List.Tot.Base.count x l == count x (seq_of_list l))
  =
    lemma_seq_of_list_induction l;
    match l with
    | []   -> ()
    | _::tl -> lemma_seq_of_list_permutation tl

let rec lemma_seq_of_list_sorted (#a:Type) (f:a -> a -> Tot bool) (l:list a)
  :Lemma (requires (List.Tot.Properties.sorted f l)) (ensures  (sorted f (seq_of_list l)))
  =
    lemma_seq_of_list_induction l;
    if length (seq_of_list l) > 1 then lemma_seq_of_list_sorted f (List.Tot.Base.tl l)


let lemma_seq_sortwith_correctness (#a:eqtype) (f:a -> a -> Tot int) (s:seq a)
  :Lemma (requires (total_order a (List.Tot.Base.bool_of_compare f)))
         (ensures  (let s' = sortWith f s in sorted (List.Tot.Base.bool_of_compare f) s' /\ permutation a s s'))
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


(* sort_lseq:
   A wrapper of Seq.sortWith which proves that the output sequences
   is a sorted permutation of the input sequence with the same length
*)
let sort_lseq (#a:eqtype) #n (f:tot_ord a) (s:lseq a n)
  : s':lseq a n{sorted f s' /\ permutation a s s'} =
  lemma_seq_sortwith_correctness (L.compare_of_bool f) s;
  let s' = sortWith (L.compare_of_bool f) s in
  perm_len s s';
  sorted_feq f (L.bool_of_compare (L.compare_of_bool f)) s';
  s'
