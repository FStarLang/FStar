(*
   Copyright 2025 Microsoft Research

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

module Pulse.Lib.PriorityQueue

#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.TotalOrder
open Pulse.Lib.ResizableVec
open FStar.Order

module Seq = FStar.Seq
module SZ = FStar.SizeT
module RV = Pulse.Lib.ResizableVec

//
// Total order helpers - connect negation of <? to <=?
//
let not_lt_implies_ge #t {| o:total_order t |} (x y:t)
  : Lemma (requires not (x <? y))
          (ensures y <=? x)
  = // not (lt (compare x y)) means compare x y is Eq or Gt
    // compare y x = flip_order (compare x y)
    // If compare x y = Eq, then compare y x = Eq, so le (compare y x)
    // If compare x y = Gt, then compare y x = Lt, so le (compare y x)
    ()

let not_le_implies_lt #t {| o:total_order t |} (x y:t)
  : Lemma (requires not (x <=? y))
          (ensures y <? x)
  = // not (le (compare x y)) means compare x y is Gt
    // compare y x = flip_order (Gt) = Lt, so lt (compare y x)
    ()

let le_lt_trans #t {| o:total_order t |} (x y z:t)
  : Lemma (requires x <=? y /\ y <? z)
          (ensures x <? z)
  = // le (compare x y) means Lt or Eq
    // lt (compare y z) means Lt
    // By transitivity: x <= y < z implies x < z
    ()

let lt_implies_le #t {| o:total_order t |} (x y:t)
  : Lemma (requires x <? y)
          (ensures x <=? y)
  = // lt implies le
    ()

let le_le_trans #t {| o:total_order t |} (x y z:t)
  : Lemma (requires x <=? y /\ y <=? z)
          (ensures x <=? z)
  = // le is transitive
    ()

//
// Concrete representation
//
let pqueue t {| total_order t |} = rvec t

//
// Index functions
//
let parent_idx (i:nat{i > 0}) : nat = (i - 1) / 2
let left_idx (i:nat) : nat = op_Multiply 2 i + 1
let right_idx (i:nat) : nat = op_Multiply 2 i + 2

// Index relationship lemmas
let left_idx_parent_of (i:nat{i > 0}) : Lemma (left_idx (parent_idx i) = i \/ right_idx (parent_idx i) = i) = ()

// If left_idx i = j, then parent_idx j = i (assuming j > 0)
let left_idx_inj (i j:nat) : Lemma (requires left_idx i = j /\ j > 0) (ensures parent_idx j = i) = ()

// If right_idx i = j, then parent_idx j = i (assuming j > 0)  
let right_idx_inj (i j:nat) : Lemma (requires right_idx i = j /\ j > 0) (ensures parent_idx j = i) = ()

// left_idx i can never equal right_idx j for any i, j  (2i+1 = 2j+2 impossible)
let left_neq_right (i j:nat) : Lemma (left_idx i <> right_idx j) = ()

//
// Heap property: each node <= its children
//
let is_heap #t {| total_order t |} (s:Seq.seq t) : prop =
  forall (i:nat). i < Seq.length s ==>
    (left_idx i < Seq.length s ==> Seq.index s i <=? Seq.index s (left_idx i)) /\
    (right_idx i < Seq.length s ==> Seq.index s i <=? Seq.index s (right_idx i))

//
// Almost-heap: heap property holds except node at position `bad` might be < its parent
// This is the invariant for sift_up
//
let almost_heap_up #t {| total_order t |} (s:Seq.seq t) (bad:nat) : prop =
  bad < Seq.length s /\
  // Every node satisfies: node <= its children (full heap property for children)
  (forall (i:nat). i < Seq.length s ==>
    (left_idx i < Seq.length s ==> Seq.index s i <=? Seq.index s (left_idx i)) /\
    (right_idx i < Seq.length s ==> Seq.index s i <=? Seq.index s (right_idx i)))
  // The node at `bad` might be smaller than parent, but that's the ONLY violation
  // Actually, this definition says it's a full heap! Let me reconsider.

// Let me define it differently:
// heap_up_at s i = node i satisfies heap relation with parent (i.e., parent <= i)
let heap_up_at #t {| total_order t |} (s:Seq.seq t) (i:nat{i < Seq.length s}) : prop =
  i = 0 \/ Seq.index s (parent_idx i) <=? Seq.index s i

// heap_down_at s i = node i satisfies heap relation with children (i.e., i <= children)
let heap_down_at #t {| total_order t |} (s:Seq.seq t) (i:nat{i < Seq.length s}) : prop =
  (left_idx i < Seq.length s ==> Seq.index s i <=? Seq.index s (left_idx i)) /\
  (right_idx i < Seq.length s ==> Seq.index s i <=? Seq.index s (right_idx i))

// Full heap = heap_down_at holds for all nodes
let is_heap_alt #t {| total_order t |} (s:Seq.seq t) : prop =
  forall (i:nat). i < Seq.length s ==> heap_down_at s i

// Almost heap for sift_up: node at `bad` might be smaller than its parent
// - All heap_up_at hold except at `bad`
// - All heap_down_at hold except possibly at parent(bad) with respect to `bad`
// Equivalently: all ordering relations hold EXCEPT maybe parent(bad) > bad
let almost_heap_sift_up #t {| total_order t |} (s:Seq.seq t) (bad:nat{bad < Seq.length s}) : prop =
  // All heap_up_at hold except at bad
  (forall (i:nat). i < Seq.length s /\ i <> bad ==> heap_up_at s i) /\
  // For all nodes, heap_down_at holds for children other than `bad`
  (forall (i:nat). i < Seq.length s ==>
    (left_idx i < Seq.length s /\ left_idx i <> bad ==> Seq.index s i <=? Seq.index s (left_idx i)) /\
    (right_idx i < Seq.length s /\ right_idx i <> bad ==> Seq.index s i <=? Seq.index s (right_idx i)))

// Lemma: if almost_heap_sift_up and bad satisfies heap_up_at, then full heap
// Helper: bad is left_idx or right_idx of its parent
let bad_is_child_of_parent (bad:nat{bad > 0})
  : Lemma (left_idx (parent_idx bad) = bad \/ right_idx (parent_idx bad) = bad)
  = let p = parent_idx bad in
    // bad = (bad - 1) / 2 * 2 + 1 (if bad is odd => left child)
    // bad = (bad - 1) / 2 * 2 + 2 (if bad is even => right child)
    // left_idx p = 2*p + 1, right_idx p = 2*p + 2
    // p = (bad - 1) / 2
    // 2*p + 1 = 2*((bad-1)/2) + 1
    // 2*p + 2 = 2*((bad-1)/2) + 2
    // If bad is odd: bad = 2k+1 for some k, p = k, left_idx p = 2k+1 = bad
    // If bad is even: bad = 2k+2 for some k, p = k (since (2k+1)/2 = k), right_idx p = 2k+2 = bad
    ()

// Helper: left_idx i = bad implies i = parent_idx bad
let left_idx_parent (bad:nat{bad > 0}) (i:nat)
  : Lemma (requires left_idx i = bad)
          (ensures i = parent_idx bad)
  = // left_idx i = 2*i + 1 = bad
    // i = (bad - 1) / 2 = parent_idx bad
    ()

// Helper: right_idx i = bad implies i = parent_idx bad  
let right_idx_parent (bad:nat{bad > 0}) (i:nat)
  : Lemma (requires right_idx i = bad)
          (ensures i = parent_idx bad)
  = // right_idx i = 2*i + 2 = bad
    // i = (bad - 2) / 2
    // parent_idx bad = (bad - 1) / 2
    // For even bad: bad = 2k+2, (bad-2)/2 = k, (bad-1)/2 = k
    // These are equal
    ()

// Show that for any i, heap_down_at s i holds
let almost_up_implies_heap_down #t {| total_order t |} 
  (s:Seq.seq t) (bad:nat{bad < Seq.length s}) (i:nat{i < Seq.length s})
  : Lemma (requires almost_heap_sift_up s bad /\ heap_up_at s bad)
          (ensures heap_down_at s i)
  = if bad = 0 then (
      // bad = 0 is not anyone's child (left_idx j >= 1, right_idx j >= 2)
      // So the exclusions in almost_heap_sift_up don't apply to any real child
      // For any i: left_idx i <> 0 (since left_idx i = 2i+1 >= 1)
      //            right_idx i <> 0 (since right_idx i = 2i+2 >= 2)
      // So from almost_heap_sift_up, we directly get heap_down_at s i
      assert (forall (j:nat). j < Seq.length s ==> left_idx j <> 0);
      assert (forall (j:nat). j < Seq.length s ==> right_idx j <> 0);
      ()
    )
    else (
      let p = parent_idx bad in
      bad_is_child_of_parent bad;
      
      if i = p then (
        // i = parent of bad. Need: s[i] <= s[left_idx i] /\ s[i] <= s[right_idx i]
        // Case 1: left_idx i = bad. Then s[i] <= s[bad] from heap_up_at bad.
        //         Also s[i] <= s[right_idx i] from almost_heap_sift_up (right_idx i <> bad if left_idx i = bad)
        // Case 2: right_idx i = bad. Then s[i] <= s[bad] from heap_up_at bad.
        //         Also s[i] <= s[left_idx i] from almost_heap_sift_up
        // Wait, we need to check: if left_idx i = bad, can right_idx i = bad too? No, since left <> right.
        if left_idx i = bad then (
          // s[i] <= s[bad] from heap_up_at
          // s[i] <= s[right_idx i] when right_idx i <> bad, which is true
          assert (right_idx i <> bad)  // because left_idx i <> right_idx i
        ) else if right_idx i = bad then (
          // s[i] <= s[bad] from heap_up_at  
          // s[i] <= s[left_idx i] when left_idx i <> bad, which is true by this branch
          ()
        ) else (
          // Neither child is bad, direct from almost_heap_sift_up
          ()
        )
      )
      else (
        // i <> p. Need to show left_idx i <> bad and right_idx i <> bad.
        if left_idx i = bad then (
          left_idx_parent bad i;  // proves i = p, contradiction with i <> p
          assert False
        );
        if right_idx i = bad then (
          right_idx_parent bad i;  // proves i = p, contradiction with i <> p
          assert False
        )
        // Now SMT should see left_idx i <> bad /\ right_idx i <> bad
        // and apply almost_heap_sift_up
      )
    )

// When heap_up_at bad holds, it means parent(bad) <= bad, which fills in the missing
// ordering relation in almost_heap_sift_up  
#push-options "--z3rlimit 10 --fuel 1 --ifuel 1"
let almost_to_full_heap #t {| total_order t |} (s:Seq.seq t) (bad:nat{bad < Seq.length s})
  : Lemma (requires almost_heap_sift_up s bad /\ heap_up_at s bad)
          (ensures is_heap s)
  = // Call the helper for all valid indices
    let rec aux (n:nat) 
      : Lemma (requires n <= Seq.length s /\ almost_heap_sift_up s bad /\ heap_up_at s bad)
              (ensures forall (i:nat). i < n ==> heap_down_at s i)
              (decreases n) =
      if n = 0 then ()
      else (
        aux (n - 1);
        almost_up_implies_heap_down s bad (n - 1)
      )
    in
    aux (Seq.length s)
#pop-options

// Lemma: is_heap is equivalent to is_heap_alt
let heap_equiv #t {| total_order t |} (s:Seq.seq t)
  : Lemma (is_heap s <==> is_heap_alt s)
  = ()

// Lemma: empty is heap
let empty_is_heap #t {| total_order t |} () : Lemma (is_heap #t Seq.empty) = ()

// Lemma: parent_idx decreases
let parent_idx_lt (i:nat{i > 0}) : Lemma (parent_idx i < i) = ()

//
// Swap (defined here because mem_swap uses it)
//
let swap_seq #t (s:Seq.seq t) (i j:nat{i < Seq.length s /\ j < Seq.length s}) : Seq.seq t =
  Seq.upd (Seq.upd s i (Seq.index s j)) j (Seq.index s i)

let swap_length #t (s:Seq.seq t) (i j:nat{i < Seq.length s /\ j < Seq.length s})
  : Lemma (Seq.length (swap_seq s i j) == Seq.length s)
  = ()

let swap_index_i #t (s:Seq.seq t) (i j:nat{i < Seq.length s /\ j < Seq.length s})
  : Lemma (Seq.index (swap_seq s i j) i == Seq.index s j)
  = ()

let swap_index_j #t (s:Seq.seq t) (i j:nat{i < Seq.length s /\ j < Seq.length s /\ i <> j})
  : Lemma (Seq.index (swap_seq s i j) j == Seq.index s i)
  = ()

let swap_index_other #t (s:Seq.seq t) (i j k:nat{i < Seq.length s /\ j < Seq.length s /\ k < Seq.length s /\ k <> i /\ k <> j})
  : Lemma (Seq.index (swap_seq s i j) k == Seq.index s k)
  = ()

//
// Root is minimum: the element at index 0 is <= all elements in a heap
//
let rec root_le_element #t {| total_order t |} (s:Seq.seq t) (i:nat)
  : Lemma (requires is_heap s /\ Seq.length s > 0 /\ i < Seq.length s)
          (ensures Seq.index s 0 <=? Seq.index s i)
          (decreases i)
  = if i = 0 then (
      // reflexivity: s[0] <=? s[0]
      ()
    ) else (
      let p = parent_idx i in
      parent_idx_lt i;
      root_le_element s p;  // s[0] <=? s[p]
      // From is_heap: s[p] <=? s[i] (since i is left or right child of p)
      bad_is_child_of_parent i;
      // Transitivity: s[0] <=? s[p] /\ s[p] <=? s[i] ==> s[0] <=? s[i]
      le_le_trans (Seq.index s 0) (Seq.index s p) (Seq.index s i)
    )

// FStar.Seq.Properties module alias for lemmas
module SeqP = FStar.Seq.Properties

// count, is_minimum, and extends are defined in the .fsti

let heap_root_is_minimum #t {| total_order t |} (s:Seq.seq t)
  : Lemma (requires is_heap s /\ Seq.length s > 0)
          (ensures is_minimum (Seq.index s 0) s)
  = let root = Seq.index s 0 in
    let aux (i:nat{i < Seq.length s}) : Lemma (root <=? Seq.index s i) =
      root_le_element s i
    in
    Classical.forall_intro aux

// Predicate: element x is in sequence s
let mem #t (x:t) (s:Seq.seq t) : prop =
  exists (i:nat). i < Seq.length s /\ Seq.index s i == x

// Lemma: snoc extends
let snoc_extends (#t:eqtype) (s:Seq.seq t) (x:t)
  : Lemma (extends s (Seq.snoc s x) x)
  = let s' = Seq.snoc s x in
    // Use lemma_append_count_aux for snoc (which is append s (create 1 x))
    SeqP.lemma_append_count_aux x s (Seq.create 1 x);
    let aux (y:t) : Lemma (requires y =!= x) (ensures count y s' == count y s) =
      SeqP.lemma_append_count_aux y s (Seq.create 1 x)
    in
    Classical.forall_intro (Classical.move_requires aux)

// Lemma: count after swap is unchanged
let count_swap (#t:eqtype) (s:Seq.seq t) (i j:nat{i < Seq.length s /\ j < Seq.length s}) (x:t)
  : Lemma (ensures count x (swap_seq s i j) == count x s)
  = swap_length s i j;
    if i <= j then (
      // swap_seq uses Seq.upd twice, need to relate to Seq.swap
      // Seq.swap s i j = upd (upd s i s[j]) j s[i]
      // which is exactly swap_seq
      assert (Seq.equal (swap_seq s i j) (Seq.swap s i j));
      SeqP.lemma_swap_permutes_aux s i j x
    ) else (
      // j < i case
      assert (Seq.equal (swap_seq s i j) (Seq.swap s j i));
      SeqP.lemma_swap_permutes_aux s j i x
    )

// Lemma: swap preserves extends relation
let swap_preserves_extends (#t:eqtype) (s0 s1:Seq.seq t) (x:t) 
  (i j:nat{i < Seq.length s1 /\ j < Seq.length s1})
  : Lemma (requires extends s0 s1 x)
          (ensures extends s0 (swap_seq s1 i j) x)
  = count_swap s1 i j x;
    let aux (y:t) : Lemma (requires y =!= x) 
                          (ensures count y (swap_seq s1 i j) == count y s0) =
      count_swap s1 i j y
    in
    Classical.forall_intro (Classical.move_requires aux)

// Lemma: if we insert x at the end, x is in the sequence
let mem_snoc #t (s:Seq.seq t) (x:t)
  : Lemma (mem x (Seq.snoc s x))
  = let s' = Seq.snoc s x in
    assert (Seq.index s' (Seq.length s) == x)

// Lemma: permutation preserves membership
let mem_swap #t (s:Seq.seq t) (i j:nat{i < Seq.length s /\ j < Seq.length s}) (x:t)
  : Lemma (mem x s <==> mem x (swap_seq s i j))
  = let s' = swap_seq s i j in
    // Forward: if x in s, then x in s'
    let fwd () : Lemma (requires mem x s) (ensures mem x s') =
      eliminate exists (k:nat). k < Seq.length s /\ Seq.index s k == x
      returns mem x s'
      with _. (
        if k = i then (
          assert (Seq.index s' j == x)
        ) else if k = j then (
          assert (Seq.index s' i == x)
        ) else (
          assert (Seq.index s' k == x)
        )
      )
    in
    // Backward: if x in s', then x in s (by symmetry)
    let bwd () : Lemma (requires mem x s') (ensures mem x s) =
      eliminate exists (k:nat). k < Seq.length s' /\ Seq.index s' k == x
      returns mem x s
      with _. (
        if k = i then (
          assert (Seq.index s j == x)
        ) else if k = j then (
          assert (Seq.index s i == x)
        ) else (
          assert (Seq.index s k == x)
        )
      )
    in
    Classical.move_requires fwd ();
    Classical.move_requires bwd ()

// Helper for sift_up_swap_heap_up_at: case i = child
let sift_up_swap_heap_up_at_child #t {| total_order t |}
  (s:Seq.seq t) (child:nat{child > 0 /\ child < Seq.length s})
  (i:nat{i < Seq.length s /\ i = child})
  : Lemma (requires almost_heap_sift_up s child /\
                    Seq.index s child <? Seq.index s (parent_idx child))
          (ensures heap_up_at (swap_seq s child (parent_idx child)) i)
  = let p = parent_idx child in
    swap_length s child p;
    swap_index_i s child p;
    swap_index_j s child p;
    lt_implies_le (Seq.index s child) (Seq.index s p)

// Helper for sift_up_swap_heap_up_at: case parent_idx i = parent_idx child (i is sibling of child)
let sift_up_swap_heap_up_at_sibling #t {| total_order t |}
  (s:Seq.seq t) (child:nat{child > 0 /\ child < Seq.length s})
  (i:nat{i < Seq.length s /\ i <> 0 /\ i <> child /\ parent_idx i = parent_idx child})
  : Lemma (requires almost_heap_sift_up s child /\
                    Seq.index s child <? Seq.index s (parent_idx child))
          (ensures heap_up_at (swap_seq s child (parent_idx child)) i)
  = let p = parent_idx child in
    let v = Seq.index s child in
    let u = Seq.index s p in
    swap_length s child p;
    swap_index_i s child p;
    swap_index_j s child p;
    swap_index_other s child p i;
    lt_implies_le v u;
    // From almost_heap_sift_up part 2: s[p] <=? s[i] when i <> child
    // v <=? u and u <=? s[i], so v <=? s[i]
    le_le_trans v u (Seq.index s i)

// Helper for sift_up_swap_heap_up_at: case parent_idx i = child (i is grandchild)
#push-options "--z3rlimit 10 --fuel 1 --ifuel 1 --split_queries always"
let sift_up_swap_heap_up_at_gchild #t {| total_order t |}
  (s:Seq.seq t) (child:nat{child > 0 /\ child < Seq.length s})
  (i:nat{i < Seq.length s /\ i <> 0 /\ i <> child /\ parent_idx i = child})
  : Lemma (requires almost_heap_sift_up s child /\
                    Seq.index s child <? Seq.index s (parent_idx child) /\
                    (left_idx child < Seq.length s ==> 
                      Seq.index s (parent_idx child) <=? Seq.index s (left_idx child)) /\
                    (right_idx child < Seq.length s ==> 
                      Seq.index s (parent_idx child) <=? Seq.index s (right_idx child)))
          (ensures heap_up_at (swap_seq s child (parent_idx child)) i)
  = let p = parent_idx child in
    let u = Seq.index s p in
    swap_length s child p;
    swap_index_i s child p;
    swap_index_other s child p i;
    // i is grandchild: parent_idx i = child, so i = left_idx child or i = right_idx child
    bad_is_child_of_parent i;
    // From precondition: u <=? s[left_idx child] and u <=? s[right_idx child]
    // s'[child] = u, s'[i] = s[i]
    assert (left_idx child = i \/ right_idx child = i)
#pop-options

// Helper: instantiate heap_up_at from almost_heap_sift_up
let heap_up_at_from_almost_heap_sift_up #t {| total_order t |} 
  (s:Seq.seq t) (child:nat{child > 0 /\ child < Seq.length s})
  (i:nat{i < Seq.length s /\ i <> child})
  : Lemma (requires almost_heap_sift_up s child)
          (ensures heap_up_at s i)
  = ()

// Helper for sift_up_swap_heap_up_at: case i is elsewhere
// Precondition: i is not 0, child, p = parent child, and parent_idx i is not p or child
#push-options "--z3rlimit 10 --fuel 1 --ifuel 1"
let sift_up_swap_heap_up_at_other #t {| total_order t |}
  (s:Seq.seq t) (child:nat{child > 0 /\ child < Seq.length s})
  (i:nat{i < Seq.length s /\ i <> 0 /\ i <> child /\ i <> parent_idx child /\ parent_idx i <> parent_idx child /\ parent_idx i <> child})
  : Lemma (requires almost_heap_sift_up s child)
          (ensures heap_up_at (swap_seq s child (parent_idx child)) i)
  = let p = parent_idx child in
    let pi = parent_idx i in
    swap_length s child p;
    swap_index_other s child p i;
    swap_index_other s child p pi;
    // Explicitly instantiate heap_up_at s i from almost_heap_sift_up
    heap_up_at_from_almost_heap_sift_up s child i
#pop-options

// Helper for sift_up_swap_lemma: heap_up_at after swap
#push-options "--z3rlimit 10 --fuel 1 --ifuel 1"
let sift_up_swap_heap_up_at #t {| total_order t |}
  (s:Seq.seq t) (child:nat{child > 0 /\ child < Seq.length s})
  (i:nat{i < Seq.length s})
  : Lemma (requires almost_heap_sift_up s child /\
                    Seq.index s child <? Seq.index s (parent_idx child) /\
                    (left_idx child < Seq.length s ==> 
                      Seq.index s (parent_idx child) <=? Seq.index s (left_idx child)) /\
                    (right_idx child < Seq.length s ==> 
                      Seq.index s (parent_idx child) <=? Seq.index s (right_idx child)) /\
                    i <> parent_idx child)
          (ensures heap_up_at (swap_seq s child (parent_idx child)) i)
  = let p = parent_idx child in
    if i = 0 then ()
    else if i = child then sift_up_swap_heap_up_at_child s child i
    else if parent_idx i = p then sift_up_swap_heap_up_at_sibling s child i
    else if parent_idx i = child then sift_up_swap_heap_up_at_gchild s child i
    else (
      // At this point: i <> 0, i <> child, parent_idx i <> p, parent_idx i <> child
      // From precondition: i <> p
      // All conditions for sift_up_swap_heap_up_at_other are satisfied
      sift_up_swap_heap_up_at_other s child i
    )
#pop-options

// Helper for sift_up_swap_lemma: part 2 (parent->child ordering except at bad)
#push-options "--z3rlimit 10 --fuel 0 --ifuel 1"
let sift_up_swap_part2 #t {| total_order t |}
  (s:Seq.seq t) (child:nat{child > 0 /\ child < Seq.length s})
  (i:nat{i < Seq.length s})
  : Lemma (requires almost_heap_sift_up s child /\
                    Seq.index s child <? Seq.index s (parent_idx child) /\
                    (left_idx child < Seq.length s ==> 
                      Seq.index s (parent_idx child) <=? Seq.index s (left_idx child)) /\
                    (right_idx child < Seq.length s ==> 
                      Seq.index s (parent_idx child) <=? Seq.index s (right_idx child)))
          (ensures (left_idx i < Seq.length s /\ left_idx i <> parent_idx child ==> 
                     Seq.index (swap_seq s child (parent_idx child)) i <=? 
                     Seq.index (swap_seq s child (parent_idx child)) (left_idx i)) /\
                   (right_idx i < Seq.length s /\ right_idx i <> parent_idx child ==> 
                     Seq.index (swap_seq s child (parent_idx child)) i <=? 
                     Seq.index (swap_seq s child (parent_idx child)) (right_idx i)))
  = let p = parent_idx child in
    let v = Seq.index s child in
    let u = Seq.index s p in
    let s' = swap_seq s child p in
    swap_length s child p;
    swap_index_i s child p;
    swap_index_j s child p;
    lt_implies_le v u;
    
    // For left child of i (when it exists and <> p):
    if left_idx i < Seq.length s && left_idx i <> p then (
      let li = left_idx i in
      if i = p then (
        if li = child then ()
        else (
          swap_index_other s child p li;
          lt_implies_le v u;
          le_le_trans v u (Seq.index s li)
        )
      )
      else if i = child then (
        // s'[child] = u, s'[li] = s[li] (since li > child > p).
        // Need u <=? s[li]. From additional precondition. ✓
        swap_index_other s child p li;
        ()
      )
      else (
        // i <> p, i <> child. s'[i] = s[i], s'[li] = s[li] (since li <> p).
        // Need to prove li <> child. If li = child, then i = parent_idx child = p. But i <> p.
        // So li <> child. We can prove this using: left_idx i = li = child implies parent_idx child = i.
        // But parent_idx child = p. So i = p. Contradiction with i <> p.
        assert (li = child ==> parent_idx child = i);  // from left_idx_inj
        // But parent_idx child = p and i <> p, so li <> child.
        assert (li <> child);
        swap_index_other s child p i;
        swap_index_other s child p li;
        ()
      )
    );
    // Similarly for right child
    if right_idx i < Seq.length s && right_idx i <> p then (
      let ri = right_idx i in
      if i = p then (
        if ri = child then ()
        else (
          swap_index_other s child p ri;
          lt_implies_le v u;
          le_le_trans v u (Seq.index s ri)
        )
      )
      else if i = child then (
        swap_index_other s child p ri;
        ()
      )
      else (
        // Same reasoning as for left child
        assert (ri = child ==> parent_idx child = i);
        assert (ri <> child);
        swap_index_other s child p i;
        swap_index_other s child p ri;
        ()
      )
    )
#pop-options

//
// Key lemma for sift_up: after swapping child with parent, 
// the almost_heap property shifts to the parent
//
let sift_up_swap_lemma #t {| total_order t |} 
  (s:Seq.seq t) (child:nat{child > 0 /\ child < Seq.length s})
  : Lemma (requires almost_heap_sift_up s child /\
                    Seq.index s child <? Seq.index s (parent_idx child) /\
                    (left_idx child < Seq.length s ==> 
                      Seq.index s (parent_idx child) <=? Seq.index s (left_idx child)) /\
                    (right_idx child < Seq.length s ==> 
                      Seq.index s (parent_idx child) <=? Seq.index s (right_idx child)))
          (ensures almost_heap_sift_up (swap_seq s child (parent_idx child)) (parent_idx child))
  = let p = parent_idx child in
    let s' = swap_seq s child p in
    swap_length s child p;
    
    // Part 1: heap_up_at for all i <> p
    let aux1 (i:nat{i < Seq.length s' /\ i <> p}) : Lemma (heap_up_at s' i)
      = sift_up_swap_heap_up_at s child i
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux1);
    
    // Part 2: parent-child ordering except at p
    let aux2 (i:nat{i < Seq.length s'})
      : Lemma ((left_idx i < Seq.length s' /\ left_idx i <> p ==> Seq.index s' i <=? Seq.index s' (left_idx i)) /\
               (right_idx i < Seq.length s' /\ right_idx i <> p ==> Seq.index s' i <=? Seq.index s' (right_idx i)))
      = sift_up_swap_part2 s child i
    in
    FStar.Classical.forall_intro aux2

// Helper: After sift_up swap, the new parent->grandchildren property holds
// New grandchildren (children of new bad = parent of child) = children of child's parent = child and sibling
// New parent = grandparent. We need s'[gp] <=? s'[child] and s'[gp] <=? s'[sibling].
// Helper for sift_up: After swapping idx with parent, establish the grandparent->children property
// for the recursive call. The recursive call has new idx = parent, new sequence = swap_seq.
// The invariant requires: swap_seq[gp] <=? swap_seq[children of parent].
#push-options "--z3rlimit 10 --fuel 1 --ifuel 1"
let grandparent_up_after_swap #t {| total_order t |} 
  (s:Seq.seq t) (child:nat{child > 0 /\ child < Seq.length s})
  : Lemma (requires almost_heap_sift_up s child /\
                    Seq.index s child <? Seq.index s (parent_idx child))
          (ensures (parent_idx child > 0 ==>
                     (left_idx (parent_idx child) < Seq.length s ==> 
                       Seq.index (swap_seq s child (parent_idx child)) (parent_idx (parent_idx child)) <=? 
                       Seq.index (swap_seq s child (parent_idx child)) (left_idx (parent_idx child))) /\
                     (right_idx (parent_idx child) < Seq.length s ==> 
                       Seq.index (swap_seq s child (parent_idx child)) (parent_idx (parent_idx child)) <=? 
                       Seq.index (swap_seq s child (parent_idx child)) (right_idx (parent_idx child)))))
  = let p = parent_idx child in
    let s' = swap_seq s child p in
    swap_length s child p;
    if p > 0 then (
      let gp = parent_idx p in
      // s'[gp] = s[gp] (gp < p < child, so gp <> child, gp <> p)
      swap_index_other s child p gp;
      // From almost_heap_sift_up part 2 for gp: s[gp] <=? s[p] (since p <> child = bad)
      assert (Seq.index s gp <=? Seq.index s p);
      
      // For left child of p:
      if left_idx p < Seq.length s then (
        if left_idx p = child then (
          // s'[child] = s[p] (from swap)
          swap_index_i s child p;
          // Need s'[gp] <=? s'[child] = s[gp] <=? s[p]. ✓
          ()
        ) else (
          // left_idx p <> child, and left_idx p <> p (since left_idx p > p)
          // s'[left_idx p] = s[left_idx p]
          swap_index_other s child p (left_idx p);
          // From almost_heap_sift_up part 2 for p: s[p] <=? s[left_idx p] (since left_idx p <> child)
          // By transitivity: s[gp] <=? s[p] <=? s[left_idx p]
          le_le_trans (Seq.index s gp) (Seq.index s p) (Seq.index s (left_idx p))
        )
      );
      // Similarly for right child
      if right_idx p < Seq.length s then (
        if right_idx p = child then (
          swap_index_i s child p;
          ()
        ) else (
          swap_index_other s child p (right_idx p);
          le_le_trans (Seq.index s gp) (Seq.index s p) (Seq.index s (right_idx p))
        )
      )
    )
#pop-options

//
// The is_pqueue predicate - includes capacity
//
let is_pqueue #t {| total_order t |} (pq:pqueue t) (s:Seq.seq t) (cap:nat) : slprop =
  is_rvec pq s cap ** pure (is_heap s /\ Seq.length s <= cap)

//
// Implementation
//

fn create (#t:Type0) {| total_order t |} (capacity:SZ.t{SZ.v capacity > 0})
  returns pq : pqueue t
  ensures is_pqueue pq Seq.empty (SZ.v capacity)
{
  let pq = RV.create #t capacity;
  empty_is_heap #t ();
  fold (is_pqueue pq Seq.empty (SZ.v capacity));
  pq
}

fn is_empty (#t:Type0) {| total_order t |} (pq:pqueue t) (#cap:erased nat)
  preserves is_pqueue pq 's0 cap
  returns b:bool
  ensures pure (b <==> Seq.length 's0 == 0)
{
  unfold (is_pqueue pq 's0 cap);
  let n = RV.len pq;
  let b = (n = 0sz);
  fold (is_pqueue pq 's0 cap);
  b
}

fn size (#t:Type0) {| total_order t |} (pq:pqueue t) (#cap:erased nat)
  preserves is_pqueue pq 's0 cap
  returns n:SZ.t
  ensures pure (SZ.v n == Seq.length 's0)
{
  unfold (is_pqueue pq 's0 cap);
  let n = RV.len pq;
  fold (is_pqueue pq 's0 cap);
  n
}

fn get_capacity (#t:Type0) {| total_order t |} (pq:pqueue t) (#s0:erased (Seq.seq t)) (#cap:erased nat)
  preserves is_pqueue pq s0 cap
  returns n:SZ.t
  ensures pure (SZ.v n == cap)
{
  unfold (is_pqueue pq s0 cap);
  let n = RV.get_capacity pq;
  fold (is_pqueue pq s0 cap);
  n
}

/// Swap helper
fn swap (#t:Type0) {| total_order t |} (pq:rvec t) (i j:SZ.t)
  (#s:erased (Seq.seq t){SZ.v i < Seq.length s /\ SZ.v j < Seq.length s})
  (#cap:erased nat)
  requires is_rvec pq s cap
  ensures is_rvec pq (swap_seq s (SZ.v i) (SZ.v j)) cap
{
  let vi = RV.get pq i;
  let vj = RV.get pq j;
  RV.set pq i vj;
  RV.set pq j vi;
  swap_length s (SZ.v i) (SZ.v j);
  ()
}

// Helper lemma for sift_up: swap preserves membership for all elements
let swap_preserves_mem_forall #t {| total_order t |} (s:Seq.seq t) (i j:nat{i < Seq.length s /\ j < Seq.length s})
  : Lemma (forall (y:t). mem y s <==> mem y (swap_seq s i j))
  = let aux (y:t) : Lemma (mem y s <==> mem y (swap_seq s i j)) =
      mem_swap s i j y
    in
    Classical.forall_intro aux

// Lemma: swap preserves all counts (permutation)
let swap_preserves_counts (#t:eqtype) (s:Seq.seq t) (i j:nat{i < Seq.length s /\ j < Seq.length s})
  : Lemma (forall (y:t). count y (swap_seq s i j) == count y s)
  = let aux (y:t) : Lemma (count y (swap_seq s i j) == count y s) =
      count_swap s i j y
    in
    Classical.forall_intro aux

/// Sift up with proper invariant
/// Postcondition: s' is a permutation of s (same counts for all elements)
fn rec sift_up (#t:eqtype) {| total_order t |} (pq:rvec t) (idx:SZ.t)
  (#s:erased (Seq.seq t){SZ.v idx < Seq.length s})
  (#cap:erased nat)
  requires is_rvec pq s cap
  requires pure (almost_heap_sift_up s (SZ.v idx) /\
                                 (SZ.v idx > 0 ==>
                                   (left_idx (SZ.v idx) < Seq.length s ==> 
                                     Seq.index s (parent_idx (SZ.v idx)) <=? Seq.index s (left_idx (SZ.v idx))) /\
                                   (right_idx (SZ.v idx) < Seq.length s ==> 
                                     Seq.index s (parent_idx (SZ.v idx)) <=? Seq.index s (right_idx (SZ.v idx)))))
  ensures exists* s'. is_rvec pq s' cap ** pure (Seq.length s' == Seq.length s /\ is_heap s' /\
                                              (forall (y:t). count y s' == count y s))
{
  if (idx = 0sz) {
    // At root, heap_up_at is trivially satisfied
    heap_equiv s;
    almost_to_full_heap s 0;
    ()
  } else {
    let parent : SZ.t = SZ.div (SZ.sub idx 1sz) 2sz;
    let current_val = RV.get pq idx;
    let parent_val = RV.get pq parent;
    
    if (current_val <? parent_val) {
      // Need to swap
      // Note: parent = parent_idx idx
      assert (pure (SZ.v parent == parent_idx (SZ.v idx)));
      swap pq idx parent;
      // After swap, the almost_heap property moves to parent
      sift_up_swap_lemma s (SZ.v idx);
      // Establish the grandparent->children property for recursive call
      grandparent_up_after_swap s (SZ.v idx);
      // Swap preserves counts
      swap_preserves_counts s (SZ.v idx) (SZ.v parent);
      sift_up pq parent #(swap_seq s (SZ.v idx) (SZ.v parent)) #cap
    } else {
      // Current >= parent, so heap_up_at holds at idx
      // Combined with almost_heap_sift_up, we have full heap
      almost_to_full_heap s (SZ.v idx);
      ()
    }
  }
}

// Lemma: after appending to a heap, we get almost_heap_sift_up at the last position
let snoc_almost_heap #t {| total_order t |} (s:Seq.seq t) (x:t)
  : Lemma (requires is_heap s)
          (ensures almost_heap_sift_up (Seq.snoc s x) (Seq.length s))
  = ()

// Helper: at the last position of snoc, children don't exist
let snoc_no_children #t (s:Seq.seq t) (x:t)
  : Lemma (requires Seq.length s >= 0)
          (ensures left_idx (Seq.length s) >= Seq.length (Seq.snoc s x) /\ 
                   right_idx (Seq.length s) >= Seq.length (Seq.snoc s x))
  = // left_idx n = 2*n + 1 >= n + 1 = Seq.length (snoc s x)
    // right_idx n = 2*n + 2 >= n + 1
    ()

/// Sift down - the invariant is:
/// - All heap_down_at hold except at `bad`
/// - All heap_up_at hold except for children of `bad`
/// This allows the node at `bad` to be larger than its children
let almost_heap_sift_down #t {| total_order t |} (s:Seq.seq t) (bad:nat{bad < Seq.length s}) : prop =
  // All heap_up_at hold except for direct children of bad
  (forall (i:nat). i < Seq.length s /\ (i = 0 \/ parent_idx i <> bad) ==> heap_up_at s i) /\
  // All heap_down_at hold except at bad
  (forall (i:nat). i < Seq.length s /\ i <> bad ==> heap_down_at s i)

let almost_down_to_full_heap #t {| total_order t |} (s:Seq.seq t) (bad:nat{bad < Seq.length s})
  : Lemma (requires almost_heap_sift_down s bad /\ heap_down_at s bad)
          (ensures is_heap s)
  = // When heap_down_at bad holds, the only possible heap_up_at violations are at children of bad.
    // But heap_down_at bad says s[bad] <= s[children], which combined with heap_up_at definition
    // (parent <= node) gives us heap_up_at for children of bad.
    // So all heap_down_at and heap_up_at hold, meaning is_heap s.
    ()

// Helper for sift_down_swap_heap_up_at: case i = child
let sift_down_swap_heap_up_at_child #t {| total_order t |}
  (s:Seq.seq t) (parent:nat{parent < Seq.length s}) (child:nat{child < Seq.length s /\ parent <> child})
  (i:nat{i < Seq.length s /\ i = child})
  : Lemma (requires almost_heap_sift_down s parent /\
                    (child = left_idx parent \/ child = right_idx parent) /\
                    Seq.index s child <? Seq.index s parent /\
                    (i = 0 \/ parent_idx i <> child))
          (ensures heap_up_at (swap_seq s parent child) i)
  = // i = child means parent_idx i = parent_idx child = parent
    // heap_up_at s' i means s'[parent] <=? s'[i]
    // s'[parent] = s[child] (from swap), s'[i] = s'[child] = s[parent] (from swap)
    // Need: s[child] <=? s[parent] - true from precondition (child <? parent implies child <=? parent)
    swap_length s parent child;
    swap_index_i s parent child;
    swap_index_j s parent child;
    lt_implies_le (Seq.index s child) (Seq.index s parent)

// Helper for sift_down_swap_heap_up_at: case i = parent
let sift_down_swap_heap_up_at_parent #t {| total_order t |}
  (s:Seq.seq t) (parent:nat{parent < Seq.length s}) (child:nat{child < Seq.length s /\ parent <> child})
  (i:nat{i < Seq.length s /\ i = parent /\ i > 0})
  : Lemma (requires almost_heap_sift_down s parent /\
                    (child = left_idx parent \/ child = right_idx parent) /\
                    Seq.index s child <? Seq.index s parent /\
                    (parent > 0 ==> Seq.index s (parent_idx parent) <=? Seq.index s child))
          (ensures heap_up_at (swap_seq s parent child) i)
  = // i = parent, so parent_idx i = parent_idx parent = grandparent
    // heap_up_at s' i means s'[gp] <=? s'[parent]
    // s'[gp] = s[gp] (gp <> parent and gp <> child since gp < parent < child)
    // s'[parent] = s[child] (from swap)
    // Need: s[gp] <=? s[child] - this is the precondition
    let gp = parent_idx parent in
    swap_length s parent child;
    swap_index_j s parent child; // s'[parent] = s[child]
    swap_index_other s parent child gp // s'[gp] = s[gp]

// Helper for sift_down_swap_heap_up_at: case parent_idx i = parent
// In this case, i is a sibling of child (the other child of parent)
#push-options "--z3rlimit 10 --fuel 1 --ifuel 1"
let sift_down_swap_heap_up_at_gchild #t {| total_order t |}
  (s:Seq.seq t) (parent:nat{parent < Seq.length s}) (child:nat{child < Seq.length s /\ parent <> child})
  (i:nat{i < Seq.length s /\ i <> 0 /\ i <> child /\ i <> parent /\ parent_idx i = parent})
  : Lemma (requires almost_heap_sift_down s parent /\
                    (child = left_idx parent \/ child = right_idx parent) /\
                    Seq.index s child <? Seq.index s parent /\
                    (left_idx parent < Seq.length s /\ left_idx parent <> child ==> 
                      Seq.index s child <=? Seq.index s (left_idx parent)) /\
                    (right_idx parent < Seq.length s /\ right_idx parent <> child ==> 
                      Seq.index s child <=? Seq.index s (right_idx parent)) /\
                    (parent_idx i <> child))
          (ensures heap_up_at (swap_seq s parent child) i)
  = // parent_idx i = parent, so i is a child of parent
    // i <> child, so i is the other child of parent (sibling of child)
    // heap_up_at s' i means s'[parent] <=? s'[i]
    // s'[parent] = s[child] (from swap), s'[i] = s[i] (since i <> parent and i <> child)
    // Need: s[child] <=? s[i]
    swap_length s parent child;
    swap_index_j s parent child; // s'[parent] = s[child]
    swap_index_other s parent child i; // s'[i] = s[i]
    // Now we need to show s[child] <=? s[i]
    // Since parent_idx i = parent and i > 0, i is a child of parent
    bad_is_child_of_parent i; // gives: left_idx parent = i \/ right_idx parent = i
    if i = left_idx parent then ()
    else ()  // i = right_idx parent
#pop-options

// Helper for sift_down_swap_heap_up_at: case i is elsewhere (not child, not parent, parent_idx i <> parent)
let sift_down_swap_heap_up_at_other #t {| total_order t |}
  (s:Seq.seq t) (parent:nat{parent < Seq.length s}) (child:nat{child < Seq.length s /\ parent <> child})
  (i:nat{i < Seq.length s /\ i <> 0 /\ i <> child /\ i <> parent /\ parent_idx i <> parent})
  : Lemma (requires almost_heap_sift_down s parent /\
                    (child = left_idx parent \/ child = right_idx parent) /\
                    Seq.index s child <? Seq.index s parent /\
                    (parent_idx i <> child))
          (ensures heap_up_at (swap_seq s parent child) i)
  = // i is not child, not parent, parent_idx i <> parent
    // heap_up_at s' i means s'[parent_idx i] <=? s'[i]
    // s'[i] = s[i] (since i <> parent, i <> child)
    // s'[parent_idx i] = s[parent_idx i] (since parent_idx i <> parent, parent_idx i <> child)
    // Need: s[parent_idx i] <=? s[i]
    // From almost_heap_sift_down: heap_up_at s i holds if parent_idx i <> parent
    // Actually: we need (i = 0 \/ parent_idx i <> parent) for heap_up_at
    // Here i <> 0 and parent_idx i <> parent, so from almost_heap_sift_down, heap_up_at s i holds
    let pi = parent_idx i in
    swap_length s parent child;
    swap_index_other s parent child i;
    swap_index_other s parent child pi

// Helper for sift_down_swap_lemma: heap_up_at after swap
#push-options "--z3rlimit 10 --fuel 1 --ifuel 1"
let sift_down_swap_heap_up_at #t {| total_order t |}
  (s:Seq.seq t) (parent:nat{parent < Seq.length s}) (child:nat{child < Seq.length s /\ parent <> child})
  (i:nat{i < Seq.length s})
  : Lemma (requires almost_heap_sift_down s parent /\
                    (child = left_idx parent \/ child = right_idx parent) /\
                    Seq.index s child <? Seq.index s parent /\
                    (left_idx parent < Seq.length s /\ left_idx parent <> child ==> 
                      Seq.index s child <=? Seq.index s (left_idx parent)) /\
                    (right_idx parent < Seq.length s /\ right_idx parent <> child ==> 
                      Seq.index s child <=? Seq.index s (right_idx parent)) /\
                    (parent > 0 ==> Seq.index s (parent_idx parent) <=? Seq.index s child) /\
                    (i = 0 \/ parent_idx i <> child))
          (ensures heap_up_at (swap_seq s parent child) i)
  = if i = 0 then ()
    else if i = child then sift_down_swap_heap_up_at_child s parent child i
    else if i = parent then (
      if parent > 0 then sift_down_swap_heap_up_at_parent s parent child i
    )
    else if parent_idx i = parent then sift_down_swap_heap_up_at_gchild s parent child i
    else sift_down_swap_heap_up_at_other s parent child i
#pop-options

// Helper for sift_down_swap_lemma: heap_down_at after swap
#push-options "--z3rlimit 10 --fuel 1 --ifuel 1"
let sift_down_swap_heap_down_at #t {| total_order t |}
  (s:Seq.seq t) (parent:nat{parent < Seq.length s}) (child:nat{child < Seq.length s /\ parent <> child})
  (i:nat{i < Seq.length s})
  : Lemma (requires almost_heap_sift_down s parent /\
                    (child = left_idx parent \/ child = right_idx parent) /\
                    Seq.index s child <? Seq.index s parent /\
                    (left_idx parent < Seq.length s /\ left_idx parent <> child ==> 
                      Seq.index s child <=? Seq.index s (left_idx parent)) /\
                    (right_idx parent < Seq.length s /\ right_idx parent <> child ==> 
                      Seq.index s child <=? Seq.index s (right_idx parent)) /\
                    (parent > 0 ==> Seq.index s (parent_idx parent) <=? Seq.index s child) /\
                    i <> child)
          (ensures heap_down_at (swap_seq s parent child) i)
  = let s' = swap_seq s parent child in
    let v = Seq.index s child in
    let u = Seq.index s parent in
    swap_length s parent child;
    swap_index_i s parent child;
    swap_index_j s parent child;
    lt_implies_le v u;
    
    if i = parent then ()
    else (
      let li = left_idx i in
      let ri = right_idx i in
      // Prove li <> child
      // child = left_idx parent or child = right_idx parent
      // If li = child = left_idx parent, then i = parent (by injectivity of left_idx)
      // If li = child = right_idx parent, then left_idx i = right_idx parent which is impossible
      // So li <> child
      (if child = left_idx parent then
         (if li = child then left_idx_inj parent child)  // forces parent_idx child = parent, so i = parent, contradiction
       else
         (if li = child then left_neq_right i parent));  // li = left, child = right, impossible
      assert (li <> child);
      
      // Similarly ri <> child
      (if child = left_idx parent then
         (if ri = child then left_neq_right parent i)  // ri = right, child = left, impossible
       else
         (if ri = child then right_idx_inj parent child));  // forces parent_idx child = parent, so i = parent, contradiction
      assert (ri <> child);
      
      if li < Seq.length s then (
        if li = parent then (
          // i is grandparent. Need s'[i] <= s'[li] = v
          // s'[i] = s[i], s'[li] = v
          // From precondition: parent > 0 ==> s[gp] <= s[child] = v
          // li = parent means left_idx i = parent, so i = parent_idx parent = gp
          swap_index_other s parent child i;
          left_idx_inj i parent;
          assert (parent_idx parent = i);
          ()
        )
        else (
          // li <> parent, li <> child
          swap_index_other s parent child i;
          swap_index_other s parent child li;
          ()
        )
      );
      if ri < Seq.length s then (
        if ri = parent then (
          swap_index_other s parent child i;
          right_idx_inj i parent;
          assert (parent_idx parent = i);
          ()
        )
        else (
          swap_index_other s parent child i;
          swap_index_other s parent child ri;
          ()
        )
      )
    )
#pop-options

// Main lemma: after swapping parent with smaller child during sift_down, 
// the almost_heap_sift_down invariant shifts to the child
let sift_down_swap_lemma #t {| total_order t |} 
  (s:Seq.seq t) (parent:nat{parent < Seq.length s}) (child:nat{child < Seq.length s})
  : Lemma (requires almost_heap_sift_down s parent /\
                    (child = left_idx parent \/ child = right_idx parent) /\
                    Seq.index s child <? Seq.index s parent /\
                    (left_idx parent < Seq.length s /\ left_idx parent <> child ==> 
                      Seq.index s child <=? Seq.index s (left_idx parent)) /\
                    (right_idx parent < Seq.length s /\ right_idx parent <> child ==> 
                      Seq.index s child <=? Seq.index s (right_idx parent)) /\
                    (parent > 0 ==> Seq.index s (parent_idx parent) <=? Seq.index s child))
          (ensures almost_heap_sift_down (swap_seq s parent child) child)
  = let s' = swap_seq s parent child in
    swap_length s parent child;
    
    // Prove part 1: heap_up_at for all i where (i=0 or parent_idx i <> child)
    let aux1 (i:nat{i < Seq.length s' /\ (i = 0 \/ parent_idx i <> child)})
      : Lemma (heap_up_at s' i)
      = sift_down_swap_heap_up_at s parent child i
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux1);
    
    // Prove part 2: heap_down_at for all i where i <> child
    let aux2 (i:nat{i < Seq.length s' /\ i <> child})
      : Lemma (heap_down_at s' i)
      = sift_down_swap_heap_down_at s parent child i
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux2)

// Helper: grandparent property after swap
// After swapping parent with child, the value at new grandparent (=parent) is s[child].
// This value satisfies heap_down_at in the original sequence.
let grandparent_after_swap #t {| total_order t |} 
  (s:Seq.seq t) (parent:nat{parent < Seq.length s}) (child:nat{child < Seq.length s})
  : Lemma (requires almost_heap_sift_down s parent /\
                    (child = left_idx parent \/ child = right_idx parent) /\
                    parent <> child)
          (ensures (left_idx child < Seq.length s ==> 
                     Seq.index s child <=? Seq.index s (left_idx child)) /\
                   (right_idx child < Seq.length s ==> 
                     Seq.index s child <=? Seq.index s (right_idx child)))
  = // From almost_heap_sift_down s parent: heap_down_at s child (since child <> parent)
    // heap_down_at s child means: s[child] <=? s[left_idx child] and s[child] <=? s[right_idx child]
    ()

#push-options "--z3rlimit 10 --fuel 1 --ifuel 1"
fn rec sift_down (#t:eqtype) {| total_order t |} (pq:rvec t) (idx:SZ.t) (len:SZ.t)
  (#s:erased (Seq.seq t){SZ.v idx < Seq.length s /\ SZ.v len == Seq.length s /\ 
                          SZ.fits (op_Multiply 2 (Seq.length s) + 2)})
  (#cap:erased nat)
  requires is_rvec pq s cap
  requires pure (almost_heap_sift_down s (SZ.v idx) /\
                                 (SZ.v idx > 0 ==> 
                                   (left_idx (SZ.v idx) < SZ.v len ==> 
                                     Seq.index s (parent_idx (SZ.v idx)) <=? Seq.index s (left_idx (SZ.v idx))) /\
                                   (right_idx (SZ.v idx) < SZ.v len ==> 
                                     Seq.index s (parent_idx (SZ.v idx)) <=? Seq.index s (right_idx (SZ.v idx)))))
  ensures exists* s'. is_rvec pq s' cap ** pure (Seq.length s' == Seq.length s /\ is_heap s' /\
                                              (forall (y:t). count y s' == count y s))
{
  // We know: fits(2*len + 2), so fits(2*idx + 1) since idx < len
  let left : SZ.t = SZ.add (SZ.mul 2sz idx) 1sz;
  
  if (SZ.gte left len) {
    // Leaf node - heap_down_at is trivially satisfied
    almost_down_to_full_heap s (SZ.v idx);
    ()
  } else {
    // Compute right directly from idx for SMT clarity
    let right : SZ.t = SZ.add (SZ.mul 2sz idx) 2sz;
    let current_val = RV.get pq idx;
    let left_val = RV.get pq left;
    
    if (SZ.lt right len) {
      // Two children
      let right_val = RV.get pq right;
      if (left_val <=? right_val) {
        if (left_val <? current_val) {
          // left = left_idx idx, left is smallest child and smaller than current
          assert (pure (SZ.v left == left_idx (SZ.v idx)));
          assert (pure (SZ.v right == right_idx (SZ.v idx)));
          // Preconditions of sift_down_swap_lemma:
          assert (pure (Seq.index s (SZ.v left) <? Seq.index s (SZ.v idx)));
          assert (pure (Seq.index s (SZ.v left) <=? Seq.index s (SZ.v right)));
          // Grandparent precondition: from function precondition if idx > 0, vacuous if idx = 0
          sift_down_swap_lemma s (SZ.v idx) (SZ.v left);
          // Establish grandparent precondition for recursive call
          grandparent_after_swap s (SZ.v idx) (SZ.v left);
          swap pq idx left;
          // Swap preserves counts
          swap_preserves_counts s (SZ.v idx) (SZ.v left);
          sift_down pq left len #(swap_seq s (SZ.v idx) (SZ.v left)) #cap
        } else {
          // !(left_val < current) means current <= left_val by total order
          not_lt_implies_ge left_val current_val;
          // Now we know current_val <=? left_val
          // And left_val <=? right_val (from the if condition)
          // By transitivity: current_val <=? right_val
          le_le_trans current_val left_val right_val;
          // heap_down_at holds: current_val <=? left_val and current_val <=? right_val
          almost_down_to_full_heap s (SZ.v idx);
          ()
        }
      } else {
        if (right_val <? current_val) {
          // right = right_idx idx, right is smallest child and smaller than current
          assert (pure (SZ.v left == left_idx (SZ.v idx)));
          assert (pure (SZ.v right == right_idx (SZ.v idx)));
          // right is smaller, so establish: right <=? left
          // !(left <=? right) means right <? left, so right <=? left
          not_le_implies_lt left_val right_val;
          lt_implies_le right_val left_val;
          // Key assertions to help SMT prove preconditions for sift_down_swap_lemma
          assert (pure (Seq.index s (SZ.v right) <? Seq.index s (SZ.v idx)));
          assert (pure (Seq.index s (SZ.v right) <=? Seq.index s (SZ.v left)));
          sift_down_swap_lemma s (SZ.v idx) (SZ.v right);
          grandparent_after_swap s (SZ.v idx) (SZ.v right);
          swap pq idx right;
          // Swap preserves counts
          swap_preserves_counts s (SZ.v idx) (SZ.v right);
          sift_down pq right len #(swap_seq s (SZ.v idx) (SZ.v right)) #cap
        } else {
          // !(right_val < current) means current <= right_val
          not_lt_implies_ge right_val current_val;
          // !(left_val <= right_val) means right_val < left_val
          not_le_implies_lt left_val right_val;
          // Now: current_val <=? right_val and right_val <? left_val
          // By transitivity: current_val <? left_val, hence current_val <=? left_val
          le_lt_trans current_val right_val left_val;
          lt_implies_le current_val left_val;
          almost_down_to_full_heap s (SZ.v idx);
          ()
        }
      }
    } else {
      // Only left child
      if (left_val <? current_val) {
        assert (pure (SZ.v left == left_idx (SZ.v idx)));
        // No right child, so "smallest child" condition is vacuously satisfied
        sift_down_swap_lemma s (SZ.v idx) (SZ.v left);
        grandparent_after_swap s (SZ.v idx) (SZ.v left);
        swap pq idx left;
        // Swap preserves counts
        swap_preserves_counts s (SZ.v idx) (SZ.v left);
        sift_down pq left len #(swap_seq s (SZ.v idx) (SZ.v left)) #cap
      } else {
        // !(left_val < current) means current <= left_val
        not_lt_implies_ge left_val current_val;
        almost_down_to_full_heap s (SZ.v idx);
        ()
      }
    }
  }
}
#pop-options

// After setting root to last element and popping, we get almost_heap_sift_down at 0
#push-options "--z3rlimit 10 --fuel 1 --ifuel 1"
let extract_almost_heap #t {| total_order t |} (s:Seq.seq t) (v:t)
  : Lemma (requires is_heap s /\ Seq.length s > 1)
          (ensures almost_heap_sift_down (Seq.slice (Seq.upd s 0 v) 0 (Seq.length s - 1)) 0)
  = let s1 = Seq.upd s 0 v in
    let s' = Seq.slice s1 0 (Seq.length s - 1) in
    // s' has length = len s - 1 > 0
    // s'[0] = v (the new root value)
    // s'[i] = s[i] for 0 < i < len s - 1
    
    // Need to show almost_heap_sift_down s' 0:
    // 1. forall i. i < len s' /\ (i = 0 \/ parent_idx i <> 0) ==> heap_up_at s' i
    //    - i = 0: heap_up_at trivially holds
    //    - parent_idx i <> 0 means i > 2 (grandchildren+). For these, heap_up_at involves
    //      s'[parent i] and s'[i]. Since parent i > 0 and i < len s', these values are
    //      unchanged from original s, so heap_up_at preserved.
    //
    // 2. forall i. i < len s' /\ i <> 0 ==> heap_down_at s' i
    //    - For i > 0: s'[i] = s[i], and children of i (if they exist in s') are also
    //      unchanged from s. Original heap had heap_down_at s i, so heap_down_at s' i holds.
    //      (We need children to exist in s' which requires 2i+1 < len s - 1)
    
    // The proof should go through by SMT
    ()
#pop-options

// Lemma: count after removing one element (for extract_min)
// After: set s[0] to s[n-1], then slice to 0..(n-1)
// This removes s[0] and keeps s[1..n-1], with s[n-1] moved to position 0
// Net effect: one copy of s[0] is removed, one copy of s[n-1] is removed and added back at position 0
// So count of s[0] decreases by 1, count of s[n-1] stays same, other counts stay same
let extract_count_lemma (#t:eqtype) (s:Seq.seq t{Seq.length s > 1})
  : Lemma (let v = Seq.index s (Seq.length s - 1) in
           let s' = Seq.slice (Seq.upd s 0 v) 0 (Seq.length s - 1) in
           let x = Seq.index s 0 in
           count x s' == count x s - 1 /\
           (forall (y:t). y =!= x ==> count y s' == count y s))
  = let n = Seq.length s in
    let v = Seq.index s (n - 1) in
    let s1 = Seq.upd s 0 v in
    let s' = Seq.slice s1 0 (n - 1) in
    let x = Seq.index s 0 in
    // s' = [v, s[1], s[2], ..., s[n-2]]
    // s  = [x, s[1], s[2], ..., s[n-2], v]
    // count y s' = (y=v?1:0) + sum_{i=1}^{n-2} (y=s[i]?1:0)
    // count y s  = (y=x?1:0) + sum_{i=1}^{n-2} (y=s[i]?1:0) + (y=v?1:0)
    // 
    // If y = x and x <> v:
    //   count x s' = 0 + sum_{i=1}^{n-2} (x=s[i]?1:0) = sum
    //   count x s  = 1 + sum + 0 = 1 + sum
    //   So count x s' = count x s - 1 ✓
    //
    // If y = x and x = v:
    //   count x s' = 1 + sum
    //   count x s  = 1 + sum + 1 = 2 + sum
    //   So count x s' = count x s - 1 ✓
    //
    // If y <> x and y = v:
    //   count v s' = 1 + sum_{i=1}^{n-2} (v=s[i]?1:0)
    //   count v s  = 0 + sum + 1 = 1 + sum
    //   So count v s' = count v s ✓
    //
    // If y <> x and y <> v:
    //   count y s' = 0 + sum
    //   count y s  = 0 + sum + 0 = sum
    //   So count y s' = count y s ✓
    SeqP.lemma_count_slice s 1;
    SeqP.lemma_count_slice s (n - 1);
    ()

// Lemma: extract transforms extends relationship
// If s' has the property that count x s' = count x s - 1 for x and count y s' = count y s for y <> x,
// then extends s' s x
let extract_extends (#t:eqtype) (s s':Seq.seq t) (x:t)
  : Lemma (requires count x s' == count x s - 1 /\ 
                    (forall (y:t). y =!= x ==> count y s' == count y s))
          (ensures extends s' s x)
  = ()

// Lemma: if s1 extends s0 with x, and s2 is a permutation of s1 (same counts),
// then s2 also extends s0 with x
let extends_permutation (#t:eqtype) (s0 s1 s2:Seq.seq t) (x:t)
  : Lemma (requires extends s0 s1 x /\ (forall (y:t). count y s2 == count y s1))
          (ensures extends s0 s2 x)
  = ()

fn insert (#t:eqtype) {| total_order t |} (pq:pqueue t) (x:t) (#cap:erased nat)
  requires is_pqueue pq 's0 cap
  returns b:bool
  ensures (if b 
           then exists* s1. is_pqueue pq s1 cap ** pure (extends 's0 s1 x /\ Seq.length 's0 < cap)
           else is_pqueue pq 's0 cap ** pure (Seq.length 's0 == cap))
{
  unfold (is_pqueue pq 's0 cap);
  
  let success = RV.push pq x;
  
  if success {
    let new_len = RV.len pq;
    let last_idx = SZ.sub new_len 1sz;
    // After push, we have almost_heap_sift_up at last position
    snoc_almost_heap 's0 x;
    // snoc extends 's0 with x
    snoc_extends 's0 x;
    sift_up pq last_idx;
    with s1. _;
    // sift_up preserves counts, so s1 is a permutation of (snoc 's0 x)
    // Combined with snoc_extends: extends 's0 s1 x
    extends_permutation 's0 (Seq.snoc 's0 x) s1 x;
    fold (is_pqueue pq s1 cap);
    true
  } else {
    fold (is_pqueue pq 's0 cap);
    false
  }
}

fn peek_min (#t:Type0) {| total_order t |} (pq:pqueue t)
  (#s0:erased (Seq.seq t){Seq.length s0 > 0})
  (#cap:erased nat)
  preserves is_pqueue pq s0 cap
  returns x:t
  ensures pure (x == Seq.index s0 0 /\ is_minimum x s0)
{
  unfold (is_pqueue pq s0 cap);
  let x = RV.get pq 0sz;
  heap_root_is_minimum s0;
  fold (is_pqueue pq s0 cap);
  x
}

fn extract_min (#t:eqtype) {| total_order t |} (pq:pqueue t)
  (#s0:erased (Seq.seq t){Seq.length s0 > 0 /\ SZ.fits (op_Multiply 2 (Seq.length s0) + 2)})
  (#cap:erased nat)
  requires is_pqueue pq s0 cap
  returns x:t
  ensures exists* s1. is_pqueue pq s1 cap ** 
          pure (x == Seq.index s0 0 /\ is_minimum x s0 /\ extends s1 s0 x)
{
  unfold (is_pqueue pq s0 cap);
  
  let min_val = RV.get pq 0sz;
  heap_root_is_minimum s0;
  let len = RV.len pq;
  
  if (len = 1sz) {
    let _ = RV.pop pq;
    empty_is_heap #t ();
    // For singleton: extends Seq.empty s0 (Seq.index s0 0)
    // count (s0[0]) Seq.empty = 0 = count (s0[0]) s0 - 1 = 1 - 1 ✓
    // forall y <> s0[0]: count y Seq.empty = 0 = count y s0 ✓ (since s0 has only s0[0])
    fold (is_pqueue pq Seq.empty cap);
    min_val
  } else {
    let last_idx = SZ.sub len 1sz;
    let last_val = RV.get pq last_idx;
    RV.set pq 0sz last_val;
    // After set: is_rvec pq (Seq.upd s0 0 last_val)
    let _ = RV.pop pq;
    // After pop: is_rvec pq (Seq.slice (Seq.upd s0 0 last_val) 0 (Seq.length s0 - 1))
    let new_len = RV.len pq;
    // The lemma extract_almost_heap gives us almost_heap_sift_down for the current sequence
    extract_almost_heap s0 last_val;
    // Prove the count relationship before sift_down
    extract_count_lemma s0;
    // The current sequence in is_rvec matches what extract_almost_heap produces
    let extracted_seq : erased (Seq.seq t) = Seq.slice (Seq.upd s0 0 last_val) 0 (Seq.length s0 - 1);
    with curr_seq. assert (is_rvec pq curr_seq cap);
    // curr_seq = extracted_seq by the slprop
    sift_down pq 0sz new_len #curr_seq;
    with s1. _;
    // sift_down preserves counts, so s1 is permutation of curr_seq
    // curr_seq satisfies: count x curr_seq = count x s0 - 1 for x = s0[0], others same
    // Therefore extends s1 s0 (Seq.index s0 0)
    // We need to prove extends s1 s0 x where x = Seq.index s0 0
    // From extract_count_lemma: count x extracted_seq = count x s0 - 1, others same
    // curr_seq = extracted_seq, so count x curr_seq = count x s0 - 1
    // From sift_down: count y s1 = count y curr_seq for all y
    // So count x s1 = count x s0 - 1, others same
    // This means extends s1 s0 x
    fold (is_pqueue pq s1 cap);
    min_val
  }
}

fn free (#t:Type0) {| total_order t |} (pq:pqueue t) (#cap:erased nat)
  requires is_pqueue pq 's0 cap
{
  unfold (is_pqueue pq 's0 cap);
  RV.free pq;
  ()
}
