(*
   Generic Bubble Sort Implementation in Pulse - Fully Verified
   
   This module implements bubble sort for any type with a total order,
   with a complete formal proof of correctness, proving that the result 
   is both sorted and a permutation of the input.
   
   Key Implementation Details:
   
   1. **Generic over Total Orders**: Works with any type that has an instance
      of the total_order typeclass from Pulse.Lib.TotalOrder.
   
   2. **Strong Loop Invariants**: The outer loop tracks that after k passes, the last k
      elements are in their final sorted positions and are >= all preceding elements.
      The inner loop tracks that the maximum element in the unprocessed range bubbles
      to the right position.
   
   3. **Permutation Tracking**: Uses Seq.Properties.permutation from F*'s standard library.
   
   4. **Sortedness Proof**: Uses comparison operators from total_order typeclass,
      proven through carefully constructed invariants.
   
   5. **No Axioms or Admits**: This implementation contains no assume val or admit(),
      demonstrating a complete verification of the generic bubble sort algorithm.
*)

module PulseExample.BubbleSort
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open Pulse.Lib.TotalOrder
open FStar.SizeT
open Pulse.Lib.BoundedIntegers

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module Seq = FStar.Seq
module Classical = FStar.Classical

// Generic sorted definition using total_order
let sorted (#t:eqtype) {| total_order t |} (s: Seq.seq t)
  = forall (i j: nat). i <= j /\ j < Seq.length s ==> Seq.index s i <=? Seq.index s j

// Generic permutation (opaque)
[@@"opaque_to_smt"]
let permutation (#t:eqtype) s1 s2 : prop = (Seq.Properties.permutation t s1 s2)

// Permutation lemmas
let permutation_same_length (#t:eqtype) (s1 s2 : Seq.seq t)
  : Lemma (requires permutation s1 s2)
          (ensures Seq.length s1 == Seq.length s2)
          [SMTPat (permutation s1 s2)]
  = 
  reveal_opaque (`%permutation) (permutation s1 s2);
  Seq.Properties.perm_len s1 s2

let permutation_refl (#t:eqtype) (s: Seq.seq t)
  : Lemma (ensures permutation s s)
    [SMTPat (permutation s s)]
   =
   (
      reveal_opaque (`%permutation) (permutation s s);
      ()
   )

let compose_permutations (#t:eqtype) (s1 s2 s3: Seq.seq t)
  : Lemma (requires permutation s1 s2 /\ permutation s2 s3)
    (ensures permutation s1 s3)
    [SMTPat (permutation s1 s2); SMTPat (permutation s2 s3)]
   = (
      reveal_opaque (`%permutation) (permutation s1 s2);
      reveal_opaque (`%permutation) (permutation s2 s3);
      reveal_opaque (`%permutation) (permutation s1 s3);
      Seq.perm_len s1 s2;
      Seq.perm_len s1 s3;
      Seq.lemma_trans_perm s1 s2 s3 0 (Seq.length s1);
      ()
   )

// Helper lemma: Seq.swap produces the same result as two updates
let lemma_swap_is_two_upds (#t:eqtype) (s: Seq.seq t) (i j: nat)
  : Lemma (requires i < Seq.length s /\ j < Seq.length s /\ i <> j)
          (ensures (let vi = Seq.index s i in
                    let vj = Seq.index s j in
                    let s1 = Seq.upd s i vj in
                    let s2 = Seq.upd s1 j vi in
                    Seq.swap s i j == s2))
  = let vi = Seq.index s i in
    let vj = Seq.index s j in
    let s1 = Seq.upd s i vj in
    let s2 = Seq.upd s1 j vi in
    let sw = Seq.swap s i j in
    assert (Seq.length s2 == Seq.length sw);
    let aux (k: nat{k < Seq.length s})
      : Lemma (Seq.index s2 k == Seq.index sw k)
      = if k = i then ()
        else if k = j then ()
        else ()
    in
    Classical.forall_intro aux;
    Seq.lemma_eq_elim s2 sw

// Helper: after a swap at positions i and j, we get a permutation
let swap_is_permutation (#t:eqtype) (s: Seq.seq t) (i j: nat)
  : Lemma (requires i < Seq.length s /\ j < Seq.length s)
          (ensures (let s1 = Seq.upd s i (Seq.index s j) in
                    let s2 = Seq.upd s1 j (Seq.index s i) in
                    permutation s s2))
  = let vi = Seq.index s i in
    let vj = Seq.index s j in
    let s1 = Seq.upd s i vj in
    let s2 = Seq.upd s1 j vi in
    reveal_opaque (`%permutation) (permutation s s2);
    if i = j then (
      Seq.lemma_index_upd1 s i vj;
      Seq.lemma_eq_elim s1 s;
      Seq.lemma_index_upd1 s1 j vi;
      Seq.lemma_eq_elim s2 s1
    ) else (
      lemma_swap_is_two_upds s i j;
      if i < j then
        Seq.Properties.lemma_swap_permutes s i j
      else
        Seq.Properties.lemma_swap_permutes s j i
    )

// Property: suffix of sequence starting at position k is sorted
let suffix_sorted (#t:eqtype) {| total_order t |} (s: Seq.seq t) (k: nat) : prop =
  k <= Seq.length s /\
  (forall (i j: nat). k <= i /\ i <= j /\ j < Seq.length s ==> Seq.index s i <=? Seq.index s j)

// Property: all elements before position k are <= all elements from k onwards
let prefix_le_suffix (#t:eqtype) {| total_order t |} (s: Seq.seq t) (k: nat) : prop =
  k <= Seq.length s /\
  (forall (i j: nat). i < k /\ k <= j /\ j < Seq.length s ==> Seq.index s i <=? Seq.index s j)

// Property: element at position k is >= all elements before position k
let is_max_up_to (#t:eqtype) {| total_order t |} (s: Seq.seq t) (k: nat) : prop =
  k < Seq.length s /\
  (forall (i: nat). i <= k ==> Seq.index s i <=? Seq.index s k)

// Lemma: swapping elements within [0..limit] preserves suffix_sorted and prefix_le_suffix
let lemma_swap_preserves_suffix_properties (#t:eqtype) {| total_order t |} (s: Seq.seq t) (i j limit: nat)
  : Lemma (requires i <= limit /\ j <= limit /\ i < Seq.length s /\ j < Seq.length s /\
                     limit < Seq.length s /\
                     suffix_sorted s (limit + 1) /\
                     prefix_le_suffix s (limit + 1))
          (ensures (let s' = if i = j then s else Seq.upd (Seq.upd s i (Seq.index s j)) j (Seq.index s i) in
                     suffix_sorted s' (limit + 1) /\
                     prefix_le_suffix s' (limit + 1)))
  = ()

// Lemma: extending the sorted suffix after a bubble pass
let lemma_bubble_extends_sorted_suffix (#t:eqtype) {| total_order t |} (s: Seq.seq t) (limit: nat)
  : Lemma (requires limit < Seq.length s /\
                     suffix_sorted s (limit + 1) /\
                     prefix_le_suffix s (limit + 1) /\
                     (forall (k: nat). k < limit ==> Seq.index s k <=? Seq.index s limit))
          (ensures suffix_sorted s limit /\ prefix_le_suffix s limit)
  = ()

// Helper function: performs a single comparison and swap if needed
fn bubble_step
  (#t:eqtype)
  {| total_order t |}
  (a: array t)
  (#s: Ghost.erased (Seq.seq t))
  (j: SZ.t)
  (limit: SZ.t)
  requires 
    A.pts_to a s ** 
    pure (SZ.v j + 1 <= SZ.v limit /\
          SZ.v limit < Seq.length s /\
          Seq.length s <= A.length a /\
          (SZ.v j > 0 ==> is_max_up_to s (SZ.v j)) /\
          suffix_sorted s (SZ.v limit + 1) /\
          prefix_le_suffix s (SZ.v limit + 1))
  ensures exists* s'. 
    A.pts_to a s' ** 
    pure (
      Seq.length s' == Seq.length s /\
      permutation s s' /\
      is_max_up_to s' (SZ.v j + 1) /\
      suffix_sorted s' (SZ.v limit + 1) /\
      prefix_le_suffix s' (SZ.v limit + 1)
    )
{
  let val_j = a.(j);
  let j1 = j + 1sz;
  let val_j1 = a.(j1);
  
  if (val_j >? val_j1) {
    a.(j) <- val_j1;
    a.(j1) <- val_j;
    
    with s_swapped. assert (A.pts_to a s_swapped);
    swap_is_permutation s (SZ.v j) (SZ.v j + 1);
    lemma_swap_preserves_suffix_properties s (SZ.v j) (SZ.v j + 1) (SZ.v limit);
    ()
  }
  else {
    ()
  }
}

// Generic bubble sort with complete formal specification and proof
fn bubble_sort
  (#t:eqtype)
  {| total_order t |}
  (a: array t)
  (#s0: Ghost.erased (Seq.seq t))
  (len: SZ.t)
  requires A.pts_to a s0 ** pure (
    SZ.v len == Seq.length s0 /\
    Seq.length s0 <= A.length a /\
    SZ.v len > 0
    )
  ensures exists* s. A.pts_to a s ** pure (
    Seq.length s == Seq.length s0 /\
    sorted s /\
    permutation s0 s
  )
{
  // Outer loop: each pass fixes one more element at the end
  let mut i: SZ.t = len - 1sz;
  
  while (!i >^ 0sz)
  invariant exists* vi s.
    R.pts_to i vi **
    A.pts_to a s **
    pure (
      SZ.v vi < SZ.v len /\
      Seq.length s == Seq.length s0 /\
      Seq.length s <= A.length a /\
      permutation s0 s /\
      suffix_sorted s (SZ.v vi + 1) /\
      prefix_le_suffix s (SZ.v vi + 1)
    )
  {
    let vi = !i;
    
    // Inner loop: bubble the maximum element to position vi
    let mut j: SZ.t = 0sz;
    
    while (!j <^ vi)
    invariant exists* vj s_inner.
      R.pts_to i vi **
      R.pts_to j vj **
      A.pts_to a s_inner **
      pure (
        SZ.v vj <= SZ.v vi /\
        SZ.v vi < SZ.v len /\
        Seq.length s_inner == Seq.length s0 /\
        Seq.length s_inner <= A.length a /\
        permutation s0 s_inner /\
        suffix_sorted s_inner (SZ.v vi + 1) /\
        prefix_le_suffix s_inner (SZ.v vi + 1) /\
        (SZ.v vj > 0 ==> is_max_up_to s_inner (SZ.v vj))
      )
    {
      let vj = !j;
      
      with s_pre. assert (A.pts_to a s_pre);
      assert (pure (Seq.length s_pre <= A.length a));
      assert (pure (permutation s0 s_pre));
      
      bubble_step a vj vi;
      
      with s_post. assert (A.pts_to a s_post);
      assert (pure (is_max_up_to s_post (SZ.v vj + 1)));
      assert (pure (permutation s_pre s_post));
      
      // Compose permutations: s0 ~ s_pre ~ s_post ==> s0 ~ s_post
      compose_permutations s0 s_pre s_post;
      
      j := vj + 1sz;
      
      // Help F* see that SZ.v (vj + 1sz) = SZ.v vj + 1
      assert (pure (SZ.v (vj + 1sz) == SZ.v vj + 1))
    };
    
    with s_after_inner. assert (A.pts_to a s_after_inner);
    
    lemma_bubble_extends_sorted_suffix s_after_inner (SZ.v vi);
    
    i := vi - 1sz;
  };
    
  // After loop: vi = 0, so we have suffix_sorted s_final 1 and prefix_le_suffix s_final 1
  
  ()
}
