module Relational.UnionFind.Forest

open FStar.Seq
open FStar.OrdSet

open FStar.DM4F.Heap
open FStar.DM4F.Heap.ST

type subtree_t = ordset nat (fun x y -> x <= y)

(***** some boring set lemmas *****)
assume val minus: subtree_t -> subtree_t -> Tot subtree_t
assume val strict_subset: subtree_t -> subtree_t -> Tot bool
assume val set_n (n:nat): subtree_t

let lemma_strict_subset_size (s1:subtree_t) (s2:subtree_t)
  :Lemma (requires (strict_subset s1 s2))
         (ensures  (subset s1 s2 /\ size s1 < size s2))
   [SMTPat (strict_subset s1 s2)]
  = admit ()

let lemma_minus_mem (s1:subtree_t) (s2:subtree_t) (x:nat)
  :Lemma (requires True) (ensures (mem x (minus s1 s2) = (mem x s1 && not (mem x s2))))
   [SMTPat (mem x (minus s1 s2))]
  = admit ()

let lemma_strict_subset_minus_size (s:subtree_t) (s1:subtree_t) (s2:subtree_t)
  :Lemma (requires (strict_subset s1 s2 /\ subset s1 s /\ subset s2 s))
         (ensures  (size (minus s s2) < size (minus s s1)))
   [SMTPat (strict_subset s1 s2); SMTPat (subset s1 s); SMTPat (subset s2 s)]
  = admit ()

let lemma_disjoint_union_subset (s1:subtree_t) (s2:subtree_t)
  :Lemma (requires (~ (s1 == empty) /\ ~ (s2 == empty) /\ intersect s1 s2 == empty))
         (ensures  (strict_subset s1 (union s1 s2) /\ strict_subset s2 (union s1 s2)))
   [SMTPatOr [[SMTPat (strict_subset s1 (union s1 s2))]; [SMTPat (strict_subset s2 (union s1 s2))]]]
  = admit ()

let lemma_subset_union (s1:subtree_t) (s2:subtree_t) (n:nat)
  :Lemma (requires (subset s1 (set_n n) /\ subset s2 (set_n n)))
         (ensures  (subset (union s1 s2) (set_n n)))
   [SMTPat (subset (union s1 s2) (set_n n))]
  = ()

let lemma_strict_subset_transitive (s1:subtree_t) (s2:subtree_t) (s3:subtree_t)
  :Lemma (requires (strict_subset s1 s2 /\ strict_subset s2 s3))
         (ensures  (strict_subset s1 s3))
   [SMTPat (strict_subset s1 s2); SMTPat (strict_subset s2 s3)]
  = admit ()

let lemma_intersect_transitive (s1:subtree_t) (s2:subtree_t)
  :Lemma (requires True) (ensures (intersect s1 s2 == intersect s2 s1))
   [SMTPatOr [[SMTPat (intersect s1 s2)]; [SMTPat (intersect s2 s1)]]]
  = admit ()

let lemma_intersect_union_empty (s1:subtree_t) (s2:subtree_t) (s3:subtree_t)
  :Lemma (requires (intersect s1 s3 == empty /\ intersect s2 s3 == empty))
         (ensures  (intersect (union s1 s2) s3 == empty))
   [SMTPat (intersect (union s1 s2) s3)]
  = admit ()
(***** end boring set lemmas *****)

type id (n:nat) = i:nat{i < n}

(*
 * each node maintains its parent id, height, and subtree nodes (including itself)
 * the subtree is used as the decreasing metric in recursive calls
 *)
type elt (n:nat) = id n * nat * subtree_t

type uf_forest (n:nat) = s:seq (ref (elt n)){length s = n}

(* liveness and separation condition for the unionfind forest *)
let live (#n:nat) (uf:uf_forest n) (h:heap) :Type0 =
  (forall (i:id n).{:pattern addr_of (index uf i)} forall (j:id n).{:pattern addr_of (index uf j)}
               i <> j ==> addr_of (index uf i) <> addr_of (index uf j)) /\  //all the refs in the forest are distinct
  (forall (i:id n).{:pattern (h `contains_a_well_typed` (index uf i))}
               h `contains_a_well_typed` (index uf i))  //all the refs in the forest are well typed

reifiable let get (#n:nat) (uf:uf_forest n) (i:id n)
  :ST (elt n) (requires (fun h0      -> live uf h0))
              (ensures  (fun h0 r h1 -> r = sel h0 (index uf i) /\ h0 == h1))
  = let h = STATE?.get () in
    sel_tot h (index uf i)

reifiable let set (#n:nat) (uf:uf_forest n) (i:id n) (elt:elt n)
  :ST unit (requires (fun h0      -> live uf h0))
           (ensures  (fun h0 _ h1 -> h1 == upd h0 (index uf i) elt))
  = let h0 = STATE?.get () in
    STATE?.put (upd_tot h0 (index uf i) elt)
