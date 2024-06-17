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

let lseq (a: Type) (l: nat) : Tot Type =
    s: Seq.seq a { Seq.length s == l }

let indexable (#a:Type) (s:Seq.seq a) (j:int) = 0 <= j /\ j < Seq.length s

val lemma_append_inj_l: #a:Type -> s1:seq a -> s2:seq a -> t1:seq a -> t2:seq a{length s1 = length t1 /\ equal (append s1 s2) (append t1 t2)} -> i:nat{i < length s1}
  -> Lemma (index s1 i == index t1 i)

val lemma_append_inj_r: #a:Type -> s1:seq a -> s2:seq a -> t1:seq a -> t2:seq a{length s1 = length t1 /\ length s2 = length t2 /\ equal (append s1 s2) (append t1 t2)} -> i:nat{i < length s2}
  -> Lemma (ensures  (index s2 i == index t2 i))

val lemma_append_len_disj: #a:Type -> s1:seq a -> s2:seq a -> t1:seq a -> t2:seq a {(length s1 = length t1 \/ length s2 = length t2) /\ (equal (append s1 s2) (append t1 t2))}
  -> Lemma (ensures (length s1 = length t1 /\ length s2 = length t2))

val lemma_append_inj: #a:Type -> s1:seq a -> s2:seq a -> t1:seq a -> t2:seq a {length s1 = length t1 \/ length s2 = length t2}
  -> Lemma (requires (equal (append s1 s2) (append t1 t2)))
           (ensures (equal s1 t1 /\ equal s2 t2))

let head (#a:Type) (s:seq a{length s > 0}) : Tot a = index s 0

let tail (#a:Type) (s:seq a{length s > 0}) : Tot (seq a) = slice s 1 (length s)

val lemma_head_append: #a:Type -> s1:seq a{length s1 > 0} -> s2:seq a -> Lemma
  (head (append s1 s2) == head s1)

val lemma_tail_append: #a:Type -> s1:seq a{length s1 > 0} -> s2:seq a -> Lemma
  (tail (append s1 s2) == append (tail s1) s2)

let last (#a:Type) (s:seq a{length s > 0}) : Tot a = index s (length s - 1)

val lemma_cons_inj: #a:Type -> v1:a -> v2:a -> s1:seq a -> s2:seq a
  -> Lemma (requires (equal (cons v1 s1) (cons v2 s2)))
          (ensures (v1 == v2 /\ equal s1 s2))

let split (#a:Type) (s:seq a) (i:nat{(0 <= i /\ i <= length s)}) : Tot (seq a & seq a)
  = slice s 0 i, slice s i (length s)

val lemma_split : #a:Type -> s:seq a -> i:nat{(0 <= i /\ i <= length s)} -> Lemma
  (ensures (append (fst (split s i)) (snd (split s i)) == s))

let split_eq (#a:Type) (s:seq a) (i:nat{(0 <= i /\ i <= length s)})
: Pure
  (seq a & seq a)
  (requires True)
  (ensures (fun x -> (append (fst x) (snd x) == s)))
= let x = split s i in
  lemma_split s i;
  x

let rec count (#a:eqtype) (x:a) (s:seq a) : Tot nat (decreases (length s))
= if length s = 0 then 0
  else if head s = x
  then 1 + count x (tail s)
  else count x (tail s)

let mem (#a:eqtype) (x:a) (l:seq a) : Tot bool = count x l > 0

val mem_index (#a:eqtype) (x:a) (s:seq a)
    : Lemma (requires (mem x s))
            (ensures (exists i. index s i == x))

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

let swap (#a:Type) (s:seq a) (i:nat{i<length s}) (j:nat{j<length s}) : Tot (seq a)
= upd (upd s j (index s i)) i (index s j)

val lemma_slice_append: #a:Type -> s1:seq a{length s1 >= 1} -> s2:seq a -> Lemma
  (ensures (equal (append s1 s2) (append (slice s1 0 1) (append (slice s1 1 (length s1)) s2))))

val lemma_slice_first_in_append: #a:Type -> s1:seq a -> s2:seq a -> i:nat{i <= length s1} -> Lemma
  (ensures (equal (slice (append s1 s2) i (length (append s1 s2))) (append (slice s1 i (length s1)) s2)))

val slice_upd: #a:Type -> s:seq a -> i:nat -> j:nat{i <= j /\ j <= length s}
  -> k:nat{k < length s} -> v:a -> Lemma
  (requires k < i \/ j <= k)
  (ensures  slice (upd s k v) i j == slice s i j)
  [SMTPat (slice (upd s k v) i j)]

val upd_slice: #a:Type -> s:seq a -> i:nat -> j:nat{i <= j /\ j <= length s}
  -> k:nat{k < j - i} -> v:a -> Lemma
  (requires i + k < j)
  (ensures  upd (slice s i j) k v == slice (upd s (i + k) v) i j)
  [SMTPat (upd (slice s i j) k v)]

// TODO: should be renamed cons_head_append, or something like that (because it is NOT related to (append (cons _ _) _))
val lemma_append_cons: #a:Type -> s1:seq a{length s1 > 0} -> s2:seq a -> Lemma
  (requires True)
  (ensures (equal (append s1 s2) (cons (head s1) (append (tail s1) s2))))

val lemma_tl: #a:Type -> hd:a -> tl:seq a -> Lemma
  (ensures (equal (tail (cons hd tl)) tl))

let rec sorted (#a:Type) (f:a -> a -> Tot bool) (s:seq a)
: Tot bool (decreases (length s))
= if length s <= 1
  then true
  else let hd = head s in
       f hd (index s 1) && sorted f (tail s)

val sorted_feq (#a:Type)
               (f g : (a -> a -> Tot bool))
               (s:seq a{forall x y. f x y == g x y})
   : Lemma (ensures (sorted f s <==> sorted g s))


val lemma_append_count: #a:eqtype -> lo:seq a -> hi:seq a -> Lemma
  (requires True)
  (ensures (forall x. count x (append lo hi) = (count x lo + count x hi)))

val lemma_append_count_aux: #a:eqtype -> x:a -> lo:seq a -> hi:seq a -> Lemma
  (requires True)
  (ensures (count x (append lo hi) = (count x lo + count x hi)))

val lemma_mem_inversion: #a:eqtype -> s:seq a{length s > 0} -> Lemma
  (ensures (forall x. mem x s = (x=head s || mem x (tail s))))

val lemma_mem_count: #a:eqtype -> s:seq a -> f:(a -> Tot bool) -> Lemma
  (requires (forall (i:nat{i<length s}). f (index s i)))
  (ensures (forall (x:a). mem x s ==> f x))

val lemma_count_slice: #a:eqtype -> s:seq a -> i:nat{i<=length s} -> Lemma
  (requires True)
  (ensures (forall x. count x s = count x (slice s 0 i) + count x (slice s i (length s))))

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

val split_5 : #a:Type -> s:seq a -> i:nat -> j:nat{i < j && j < length s} -> Pure (seq (seq a))
  (requires True)
  (ensures (fun x ->
            (length x = 5
             /\ equal s (append (index x 0) (append (index x 1) (append (index x 2) (append (index x 3) (index x 4)))))
             /\ equal (index x 0) (slice s 0 i)
             /\ equal (index x 1) (slice s i (i+1))
             /\ equal (index x 2) (slice s (i+1) j)
             /\ equal (index x 3) (slice s j (j + 1))
             /\ equal (index x 4) (slice s (j + 1) (length s)))))

val lemma_swap_permutes_aux_frag_eq: #a:Type -> s:seq a -> i:nat{i<length s} -> j:nat{i <= j && j<length s}
                          -> i':nat -> j':nat{i' <= j' /\ j'<=length s /\
                                              (j < i'  //high slice
                                              \/ j' <= i //low slice
                                              \/ (i < i' /\ j' <= j)) //mid slice
                                              }
                          -> Lemma (ensures (slice s i' j' == slice (swap s i j) i' j'
                                            /\ slice s i (i + 1) == slice (swap s i j) j (j + 1)
                                            /\ slice s j (j + 1) == slice (swap s i j) i (i + 1)))

val lemma_swap_permutes_aux: #a:eqtype -> s:seq a -> i:nat{i<length s} -> j:nat{i <= j && j<length s} -> x:a -> Lemma
  (requires True)
  (ensures (count x s = count x (swap s i j)))

type permutation (a:eqtype) (s1:seq a) (s2:seq a) =
       (forall i. count i s1 = count i s2)

val append_permutations: #a:eqtype -> s1:seq a -> s2:seq a -> s1':seq a -> s2':seq a -> Lemma
    (requires permutation a s1 s1' /\ permutation a s2 s2')
    (ensures permutation a (append s1 s2) (append s1' s2'))

val lemma_swap_permutes (#a:eqtype) (s:seq a) (i:nat{i<length s}) (j:nat{i <= j && j<length s})
  : Lemma (permutation a s (swap s i j))

(* perm_len:
     A lemma that shows that two sequences that are permutations
     of each other also have the same length
*)
val perm_len (#a:eqtype) (s1 s2: seq a)
  : Lemma (requires (permutation a s1 s2))
          (ensures  (length s1 == length s2))

val cons_perm: #a:eqtype -> tl:seq a -> s:seq a{length s > 0} ->
         Lemma (requires (permutation a tl (tail s)))
               (ensures (permutation a (cons (head s) tl) s))

val lemma_mem_append : #a:eqtype -> s1:seq a -> s2:seq a
      -> Lemma (ensures (forall x. mem x (append s1 s2) <==> (mem x s1 || mem x s2)))

val lemma_slice_cons: #a:eqtype -> s:seq a -> i:nat -> j:nat{i < j && j <= length s}
  -> Lemma (ensures (forall x. mem x (slice s i j) <==> (x = index s i || mem x (slice s (i + 1) j))))

val lemma_slice_snoc: #a:eqtype -> s:seq a -> i:nat -> j:nat{i < j && j <= length s}
  -> Lemma (ensures (forall x. mem x (slice s i j) <==> (x = index s (j - 1) || mem x (slice s i (j - 1)))))

val lemma_ordering_lo_snoc: #a:eqtype -> f:tot_ord a -> s:seq a -> i:nat -> j:nat{i <= j && j < length s} -> pv:a
   -> Lemma (requires ((forall y. mem y (slice s i j) ==> f y pv) /\ f (index s j) pv))
            (ensures ((forall y. mem y (slice s i (j + 1)) ==> f y pv)))

val lemma_ordering_hi_cons: #a:eqtype -> f:tot_ord a -> s:seq a -> back:nat -> len:nat{back < len && len <= length s} -> pv:a
   -> Lemma (requires ((forall y. mem y (slice s (back + 1) len) ==> f pv y) /\ f pv (index s back)))
            (ensures ((forall y. mem y (slice s back len) ==> f pv y)))

val swap_frame_lo : #a:Type -> s:seq a -> lo:nat -> i:nat{lo <= i} -> j:nat{i <= j && j < length s}
     -> Lemma (ensures (slice s lo i == slice (swap s i j) lo i))

val swap_frame_lo' : #a:Type -> s:seq a -> lo:nat -> i':nat {lo <= i'} -> i:nat{i' <= i} -> j:nat{i <= j && j < length s}
     -> Lemma (ensures (slice s lo i' == slice (swap s i j) lo i'))

val swap_frame_hi : #a:Type -> s:seq a -> i:nat -> j:nat{i <= j} -> k:nat{j < k} -> hi:nat{k <= hi /\ hi <= length s}
     -> Lemma (ensures (slice s k hi == slice (swap s i j) k hi))

val lemma_swap_slice_commute  : #a:Type -> s:seq a -> start:nat -> i:nat{start <= i} -> j:nat{i <= j} -> len:nat{j < len && len <= length s}
    -> Lemma (ensures (slice (swap s i j) start len == (swap (slice s start len) (i - start) (j - start))))

val lemma_swap_permutes_slice : #a:eqtype -> s:seq a -> start:nat -> i:nat{start <= i} -> j:nat{i <= j} -> len:nat{j < len && len <= length s}
   -> Lemma (ensures (permutation a (slice s start len) (slice (swap s i j) start len)))

(* replaces the [i,j) sub-sequence of s1 with the corresponding sub-sequence of s2 *)
let splice (#a:Type) (s1:seq a) (i:nat) (s2:seq a{length s1=length s2}) (j:nat{i <= j /\ j <= (length s2)})
: Tot (seq a)
= Seq.append (slice s1 0 i) (Seq.append (slice s2 i j) (slice s1 j (length s1)))

(* replace with sub *)
let replace_subseq (#a:Type0) (s:Seq.seq a) (i:nat) (j:nat{i <= j /\ j <= length s}) (sub:Seq.seq a{length sub == j - i}) :Tot (Seq.seq a)
  = Seq.append (Seq.slice s 0 i) (Seq.append sub (Seq.slice s j (Seq.length s)))

val splice_refl : #a:Type -> s:seq a -> i:nat -> j:nat{i <= j && j <= length s}
  -> Lemma
  (ensures (s == splice s i s j))

val lemma_swap_splice : #a:Type -> s:seq a -> start:nat -> i:nat{start <= i} -> j:nat{i <= j} -> len:nat{j < len && len <= length s}
   -> Lemma
        (ensures (swap s i j == splice s start (swap s i j) len))

val lemma_seq_frame_hi: #a:Type -> s1:seq a -> s2:seq a{length s1 = length s2} -> i:nat -> j:nat{i <= j} -> m:nat{j <= m} -> n:nat{m < n && n <= length s1}
  -> Lemma
  (requires (s1 == (splice s2 i s1 j)))
  (ensures  ((slice s1 m n == slice s2 m n) /\ (index s1 m == index s2 m)))

val lemma_seq_frame_lo: #a:Type -> s1:seq a -> s2:seq a{length s1 = length s2} -> i:nat -> j:nat{i <= j} -> m:nat{j < m} -> n:nat{m <= n && n <= length s1}
  -> Lemma
  (requires (s1 == (splice s2 m s1 n)))
  (ensures  ((slice s1 i j == slice s2 i j) /\ (index s1 j == index s2 j)))

val lemma_tail_slice: #a:Type -> s:seq a -> i:nat -> j:nat{i < j && j <= length s}
  -> Lemma
  (requires True)
  (ensures (tail (slice s i j) == slice s (i + 1) j))
  [SMTPat (tail (slice s i j))]

val lemma_weaken_frame_right : #a:Type -> s1:seq a -> s2:seq a{length s1 = length s2} -> i:nat -> j:nat -> k:nat{i <= j && j <= k && k <= length s1}
  -> Lemma
  (requires (s1 == splice s2 i s1 j))
  (ensures (s1 == splice s2 i s1 k))

val lemma_weaken_frame_left : #a:Type -> s1:seq a -> s2:seq a{length s1 = length s2} -> i:nat -> j:nat -> k:nat{i <= j && j <= k && k <= length s1}
  -> Lemma
  (requires (s1 == splice s2 j s1 k))
  (ensures (s1 == splice s2 i s1 k))

val lemma_trans_frame : #a:Type -> s1:seq a -> s2:seq a -> s3:seq a{length s1 = length s2 /\ length s2 = length s3} -> i:nat -> j:nat{i <= j && j <= length s1}
  -> Lemma
  (requires ((s1 == splice s2 i s1 j) /\ s2 == splice s3 i s2 j))
  (ensures (s1 == splice s3 i s1 j))

val lemma_weaken_perm_left: #a:eqtype -> s1:seq a -> s2:seq a{length s1 = length s2} -> i:nat -> j:nat -> k:nat{i <= j /\ j <= k /\ k <= length s1}
  -> Lemma
  (requires (s1 == splice s2 j s1 k /\ permutation a (slice s2 j k) (slice s1 j k)))
  (ensures (permutation a (slice s2 i k) (slice s1 i k)))

val lemma_weaken_perm_right: #a:eqtype -> s1:seq a -> s2:seq a{length s1 = length s2} -> i:nat -> j:nat -> k:nat{i <= j /\ j <= k /\ k <= length s1}
  -> Lemma
  (requires (s1 == splice s2 i s1 j /\ permutation a (slice s2 i j) (slice s1 i j)))
  (ensures (permutation a (slice s2 i k) (slice s1 i k)))

val lemma_trans_perm: #a:eqtype -> s1:seq a -> s2:seq a -> s3:seq a{length s1 = length s2 /\ length s2 = length s3} -> i:nat -> j:nat{i<=j && j <= length s1}
 -> Lemma
  (requires (permutation a (slice s1 i j) (slice s2 i j)
             /\ permutation a (slice s2 i j) (slice s3 i j)))
  (ensures (permutation a (slice s1 i j) (slice s3 i j)))


(*New additions, please review*)

let snoc (#a:Type) (s:seq a) (x:a) : Tot (seq a) = Seq.append s (Seq.create 1 x)

val lemma_cons_snoc (#a:Type) (hd:a) (s:Seq.seq a) (tl:a)
  : Lemma (requires True)
          (ensures (Seq.equal (cons hd (snoc s tl))
                              (snoc (cons hd s) tl)))

val lemma_tail_snoc: #a:Type -> s:Seq.seq a{Seq.length s > 0} -> x:a
                     -> Lemma (ensures (tail (snoc s x) == snoc (tail s) x))

val lemma_snoc_inj: #a:Type -> s1:seq a -> s2:seq a -> v1:a -> v2:a
  -> Lemma (requires (equal (snoc s1 v1) (snoc s2 v2)))
          (ensures (v1 == v2 /\ equal s1 s2))

val lemma_mem_snoc : #a:eqtype -> s:Seq.seq a -> x:a ->
   Lemma (ensures (forall y. mem y (snoc s x) <==> mem y s \/ x=y))

let rec find_l (#a:Type) (f:a -> Tot bool) (l:seq a)
: Tot (o:option a{Some? o ==> f (Some?.v o)})
  (decreases (Seq.length l))
= if Seq.length l = 0 then None
  else if f (head l) then Some (head l)
  else find_l f (tail l)

let rec ghost_find_l (#a:Type) (f:a -> GTot bool) (l:seq a)
: GTot (o:option a{Some? o ==> f (Some?.v o)})
  (decreases (Seq.length l))
= if Seq.length l = 0 then None
  else if f (head l) then Some (head l)
  else ghost_find_l f (tail l)

val find_append_some: #a:Type -> s1:seq a -> s2:seq a -> f:(a -> Tot bool) -> Lemma
  (requires (Some? (find_l f s1)))
  (ensures (find_l f (append s1 s2) == find_l f s1))

val find_append_none: #a:Type -> s1:seq a -> s2:seq a -> f:(a -> Tot bool) -> Lemma
  (requires (None? (find_l f s1)))
  (ensures (find_l f (append s1 s2) == find_l f s2))

val find_append_none_s2: #a:Type -> s1:seq a -> s2:seq a -> f:(a -> Tot bool) -> Lemma
  (requires (None? (find_l f s2)))
  (ensures  (find_l f (append s1 s2) == find_l f s1))

val find_snoc: #a:Type -> s:Seq.seq a -> x:a -> f:(a -> Tot bool)
               -> Lemma (ensures (let res = find_l f (snoc s x) in
                                 match res with
                                 | None -> find_l f s == None /\ not (f x)
                                 | Some y -> res == find_l f s \/ (f x /\ x==y)))

let un_snoc (#a:Type) (s:seq a{length s <> 0}) : Tot (r:(seq a & a){s == snoc (fst r) (snd r)}) =
  let s', a = split s (length s - 1) in
  assert (Seq.equal (snoc s' (Seq.index a 0)) s);
  s', Seq.index a 0

val un_snoc_snoc (#a:Type) (s:seq a) (x:a) : Lemma (un_snoc (snoc s x) == (s, x))

let rec find_r (#a:Type) (f:a -> Tot bool) (l:seq a)
: Tot (o:option a{Some? o ==> f (Some?.v o)})
  (decreases (Seq.length l))
= if Seq.length l = 0 then None
  else let prefix, last = un_snoc l in
       if f last then Some last
       else find_r f prefix

type found (i:nat) = True

let rec seq_find_aux (#a:Type) (f:a -> Tot bool) (l:seq a) (ctr:nat{ctr <= Seq.length l})
: Pure (option a)
  (requires (forall (i:nat{ i < Seq.length l /\ i >= ctr}).
               not (f (Seq.index l i) )))
  (ensures (function
            | None -> forall (i:nat{i < Seq.length l}).  not (f (Seq.index l i))
            | Some x -> f x /\  (exists (i:nat{i < Seq.length l}). {:pattern (found i)}
                                 found i /\ x == Seq.index l i)))
= match ctr with
  | 0 -> None
  | _ -> let i = ctr - 1 in
  if f (Seq.index l i)
  then (
     cut (found i);
     Some (Seq.index l i))
  else seq_find_aux f l i

let seq_find (#a:Type) (f:a -> Tot bool) (l:seq a)
: Pure (option a)
  (requires True)
  (ensures (function
            | None -> forall (i:nat{i < Seq.length l}). not (f (Seq.index l i))
            | Some x -> f x /\ (exists (i:nat{i < Seq.length l}).{:pattern (found i)}
                                 found i /\ x == Seq.index l i)))
= seq_find_aux f l (Seq.length l)

val find_mem (#a:eqtype) (s:seq a) (f:a -> Tot bool) (x:a{f x})
   : Lemma (requires (mem x s))
           (ensures (Some? (seq_find f s) /\ f (Some?.v (seq_find f s))))

let for_all
  (#a: Type)
  (f: (a -> Tot bool))
  (l: seq a)
: Pure bool
  (requires True)
  (ensures (fun b -> (b == true <==> (forall (i: nat {i < Seq.length l} ) . f (index l i) == true))))
= None? (seq_find (fun i -> not (f i)) l)

val seq_mem_k: #a:eqtype -> s:seq a -> n:nat{n < Seq.length s} ->
    Lemma (requires True)
          (ensures (mem (Seq.index s n) s))
          [SMTPat (mem (Seq.index s n) s)]

module L = FStar.List.Tot

val lemma_seq_of_list_induction (#a:Type) (l:list a)
  :Lemma (requires True)
         (ensures (let s = seq_of_list l in
                   match l with
                   | []    -> Seq.equal s empty
                   | hd::tl -> s == cons hd (seq_of_list tl) /\
		             head s == hd /\ tail s == (seq_of_list tl)))

val lemma_seq_list_bij: #a:Type -> s:seq a -> Lemma
  (requires (True))
  (ensures  (seq_of_list (seq_to_list s) == s))

val lemma_list_seq_bij: #a:Type -> l:list a -> Lemma
  (requires (True))
  (ensures  (seq_to_list (seq_of_list l) == l))

unfold let createL_post (#a:Type0) (l:list a) (s:seq a) : GTot Type0 =
  normalize (L.length l = length s) /\ seq_to_list s == l /\ seq_of_list l == s

let createL (#a:Type0) (l:list a)
: Pure (seq a)
  (requires True)
  (ensures (fun s -> createL_post #a l s))
= let s = seq_of_list l in
  lemma_list_seq_bij l;
  s
  
val lemma_index_is_nth: #a:Type -> s:seq a -> i:nat{i < length s} -> Lemma
  (requires True)
  (ensures  (L.index (seq_to_list s) i == index s i))

////////////////////////////////////////////////////////////////////////////////
//s `contains` x : Type0
//    An undecidable version of `mem`,
//    for when the sequence payload is not an eqtype
////////////////////////////////////////////////////////////////////////////////
[@@ remove_unused_type_parameters [0; 1; 2]]
val contains (#a:Type) (s:seq a) (x:a) : Tot Type0

val contains_intro (#a:Type) (s:seq a) (k:nat) (x:a)
  : Lemma (k < Seq.length s /\ Seq.index s k == x
            ==>
           s `contains` x)

val contains_elim (#a:Type) (s:seq a) (x:a)
  : Lemma (s `contains` x
            ==>
          (exists (k:nat). k < Seq.length s /\ Seq.index s k == x))

val lemma_contains_empty (#a:Type) : Lemma (forall (x:a). ~ (contains Seq.empty x))

val lemma_contains_singleton (#a:Type) (x:a) : Lemma (forall (y:a). contains (create 1 x) y ==> y == x)

val append_contains_equiv (#a:Type) (s1:seq a) (s2:seq a) (x:a)
  : Lemma ((append s1 s2) `contains` x
            <==>
           (s1 `contains` x \/ s2 `contains` x))

val contains_snoc : #a:Type -> s:Seq.seq a -> x:a ->
   Lemma (ensures (forall y. (snoc s x) `contains` y  <==> s `contains` y \/ x==y))

val lemma_find_l_contains (#a:Type) (f:a -> Tot bool) (l:seq a)
  : Lemma (requires True) (ensures Some? (find_l f l) ==> l `contains` (Some?.v (find_l f l)))

val contains_cons (#a:Type) (hd:a) (tl:Seq.seq a) (x:a)
  : Lemma ((cons hd tl) `contains` x
           <==>
           (x==hd \/ tl `contains` x))

val append_cons_snoc (#a:Type) (u: Seq.seq a) (x:a) (v:Seq.seq a)
    : Lemma (Seq.equal (Seq.append u (cons x v))
                       (Seq.append (snoc u x) v))

val append_slices (#a:Type) (s1:Seq.seq a) (s2:Seq.seq a)
   : Lemma ( Seq.equal s1 (Seq.slice (Seq.append s1 s2) 0 (Seq.length s1)) /\
             Seq.equal s2 (Seq.slice (Seq.append s1 s2) (Seq.length s1) (Seq.length s1 + Seq.length s2)) /\
             (forall (i:nat) (j:nat).
                i <= j /\ j <= Seq.length s2 ==>
                Seq.equal (Seq.slice s2 i j)
                          (Seq.slice (Seq.append s1 s2) (Seq.length s1 + i) (Seq.length s1 + j))))


val find_l_none_no_index (#a:Type) (s:Seq.seq a) (f:(a -> Tot bool)) :
  Lemma (requires (None? (find_l f s)))
        (ensures (forall (i:nat{i < Seq.length s}). not (f (Seq.index s i))))
        (decreases (Seq.length s))

(** More properties, with new naming conventions *)

let suffix_of
  (#a: Type)
  (s_suff s: seq a)
= exists s_pref . (s == append s_pref s_suff)

val cons_head_tail
  (#a: Type)
  (s: seq a {length s > 0})
: Lemma
  (requires True)
  (ensures (s == cons (head s) (tail s)))
  [SMTPat (cons (head s) (tail s))]

val head_cons
  (#a: Type)
  (x: a)
  (s: seq a)
: Lemma
  (ensures (head (cons x s) == x))

val suffix_of_tail
  (#a: Type)
  (s: seq a {length s > 0})
: Lemma
  (requires True)
  (ensures ((tail s) `suffix_of` s))
  [SMTPat ((tail s) `suffix_of` s)]

val index_cons_l
  (#a: Type)
  (c: a)
  (s: seq a)
: Lemma
  (ensures (index (cons c s) 0 == c))

val index_cons_r
  (#a: Type)
  (c: a)
  (s: seq a)
  (i: nat {1 <= i /\ i <= length s})
: Lemma
  (ensures (index (cons c s) i == index s (i - 1)))

val append_cons
  (#a: Type)
  (c: a)
  (s1 s2: seq a)
: Lemma
  (ensures (append (cons c s1) s2 == cons c (append s1 s2)))

val index_tail
  (#a: Type)
  (s: seq a {length s > 0})
  (i: nat {i < length s - 1} )
: Lemma
  (ensures (index (tail s) i == index s (i + 1)))

val mem_cons
  (#a:eqtype)
  (x:a)
  (s:seq a)
: Lemma
  (ensures (forall y. mem y (cons x s) <==> mem y s \/ x=y))

val snoc_slice_index
  (#a: Type)
  (s: seq a)
  (i: nat)
  (j: nat {i <= j /\ j < length s} )
: Lemma
  (requires True)
  (ensures (snoc (slice s i j) (index s j) == slice s i (j + 1)))
  [SMTPat (snoc (slice s i j) (index s j))]

val cons_index_slice
  (#a: Type)
  (s: seq a)
  (i: nat)
  (j: nat {i < j /\ j <= length s} )
  (k:nat{k == i+1})
: Lemma
  (requires True)
  (ensures (cons (index s i) (slice s k j) == slice s i j))
  [SMTPat (cons (index s i) (slice s k j))]

val slice_is_empty
  (#a: Type)
  (s: seq a)
  (i: nat {i <= length s})
: Lemma
  (requires True)
  (ensures (slice s i i == Seq.empty))
  [SMTPat (slice s i i)]

val slice_length
  (#a: Type)
  (s: seq a)
: Lemma
  (requires True)
  (ensures (slice s 0 (length s) == s))
  [SMTPat (slice s 0 (length s))]

val slice_slice
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

val lemma_seq_of_list_index (#a:Type) (l:list a) (i:nat{i < List.Tot.length l})
  :Lemma (requires True)
         (ensures  (index (seq_of_list l) i == List.Tot.index l i))
         [SMTPat (index (seq_of_list l) i)]

[@@(deprecated "seq_of_list")]
let of_list (#a:Type) (l:list a) :seq a = seq_of_list l

val seq_of_list_tl
  (#a: Type)
  (l: list a { List.Tot.length l > 0 } )
: Lemma
  (requires True)
  (ensures (seq_of_list (List.Tot.tl l) == tail (seq_of_list l)))

val mem_seq_of_list
  (#a: eqtype)
  (x: a)
  (l: list a)
: Lemma
  (requires True)
  (ensures (mem x (seq_of_list l) == List.Tot.mem x l))
  [SMTPat (mem x (seq_of_list l))]

(** Dealing efficiently with `seq_of_list` by meta-evaluating conjunctions over
an entire list. *)

let rec explode_and (#a: Type)
  (i: nat)
  (s: seq a { i <= length s })
  (l: list a { List.Tot.length l + i = length s }):
  Tot Type
  (decreases (List.Tot.length l))
= match l with
  | [] -> True
  | hd :: tl -> index s i == hd /\ explode_and (i + 1) s tl

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

val intro_of_list (#a: Type) (s: seq a) (l: list a):
  Lemma
    (requires (
      List.Tot.length l = length s /\
      pointwise_and s l))
    (ensures (
      s == seq_of_list l))

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

val elim_of_list (#a: Type) (l: list a):
  Lemma
    (ensures (
      let s = seq_of_list l in
      pointwise_and s l))

(****** sortWith ******)
let sortWith (#a:eqtype) (f:a -> a -> Tot int) (s:seq a) :Tot (seq a)
  = seq_of_list (List.Tot.Base.sortWith f (seq_to_list s))

val lemma_seq_to_list_permutation (#a:eqtype) (s:seq a)
  :Lemma (requires True) (ensures (forall x. count x s == List.Tot.Base.count x (seq_to_list s))) (decreases (length s))

val lemma_seq_of_list_permutation (#a:eqtype) (l:list a)
  :Lemma (forall x. List.Tot.Base.count x l == count x (seq_of_list l))

val lemma_seq_of_list_sorted (#a:Type) (f:a -> a -> Tot bool) (l:list a)
  :Lemma (requires (List.Tot.Properties.sorted f l)) (ensures  (sorted f (seq_of_list l)))

val lemma_seq_sortwith_correctness (#a:eqtype) (f:a -> a -> Tot int) (s:seq a)
  :Lemma (requires (total_order a (List.Tot.Base.bool_of_compare f)))
         (ensures  (let s' = sortWith f s in sorted (List.Tot.Base.bool_of_compare f) s' /\ permutation a s s'))

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

let rec foldr (#a #b:Type) (f:b -> a -> Tot a) (s:seq b) (init:a)
  : Tot a (decreases (length s))
  = if length s = 0 then init
    else f (head s) (foldr f (tail s) init)

let rec foldr_snoc (#a #b:Type) (f:b -> a -> Tot a) (s:seq b) (init:a)
  : Tot a (decreases (length s))
  = if length s = 0 then init
    else let s, last = un_snoc s in
         f last (foldr_snoc f s init)

(****** Seq map ******)

val map_seq (#a #b:Type) (f:a -> Tot b) (s:Seq.seq a) : Tot (Seq.seq b)

val map_seq_len (#a #b:Type) (f:a -> Tot b) (s:Seq.seq a)
  : Lemma (ensures Seq.length (map_seq f s) == Seq.length s)

val map_seq_index (#a #b:Type) (f:a -> Tot b) (s:Seq.seq a) (i:nat{i < Seq.length s})
  : Lemma (ensures (map_seq_len f s; Seq.index (map_seq f s) i == f (Seq.index s i)))

val map_seq_append (#a #b:Type) (f:a -> Tot b) (s1 s2:Seq.seq a)
  : Lemma (ensures (map_seq f (Seq.append s1 s2) ==
                    Seq.append (map_seq f s1) (map_seq f s2)))
