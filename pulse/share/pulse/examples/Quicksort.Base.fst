(*
   Copyright 2023 Microsoft Research

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

module Quicksort.Base

open Pulse.Lib.Pervasives
module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT

(* Base module with proof of correctness of Quicksort, partition, etc.
Actual implementations are Quicksort.Sequential, Quicksort.Parallel and
Quicksort.Task. *)

let nat_smaller (n: nat) = i:nat{i < n}

let seq_swap (#a: Type) (s: Seq.seq a) (i j: nat_smaller (Seq.length s)) =
  Seq.swap s j i

let larger_than (s: Seq.seq int) (lb: int)
  = forall (k: int). 0 <= k /\ k < Seq.length s ==> lb <= Seq.index s k

let smaller_than (s: Seq.seq int) (rb: int)
  = forall (k: int). 0 <= k /\ k < Seq.length s ==> Seq.index s k <= rb

let between_bounds (s: Seq.seq int) (lb rb: int)
  = larger_than s lb /\ smaller_than s rb

let sorted (s: Seq.seq int)
  = forall (i j: nat). i <= j /\ j < Seq.length s ==> Seq.index s i <= Seq.index s j

#push-options "--retry 5"
let lemma_sorted_append
  (s1 s2 : Seq.seq int)
  (l1 r1 l2 r2 : int)
  : Lemma
    (requires sorted s1 /\ between_bounds s1 l1 r1 /\
              sorted s2 /\ between_bounds s2 l2 r2 /\
              r1 >= l1 /\ r2 >= l2 /\ // silly, but needed since the seqs may be empty
              r1 <= l2)
    (ensures sorted (Seq.append s1 s2) /\ between_bounds (Seq.append s1 s2) l1 r2)
  = ()

let lemma_sorted_append_squash
  (s1 s2 : Seq.seq int)
  (l1 r1 l2 r2 : int)
    (_ : squash (sorted s1 /\ between_bounds s1 l1 r1 /\
              sorted s2 /\ between_bounds s2 l2 r2 /\
              r1 >= l1 /\ r2 >= l2 /\ // silly, but needed since the seqs may be empty
              r1 <= l2))
    : squash (sorted (Seq.append s1 s2) /\ between_bounds (Seq.append s1 s2) l1 r2)
  = ()
#pop-options

let to_nat (x: int{x >= 0}): nat = x
(** Permutation reasoning **)

[@@"opaque_to_smt"]
let permutation s1 s2 : prop = (Seq.Properties.permutation int s1 s2)

let permutation_same_length (s1 s2 : Seq.seq int)
  : Lemma (requires permutation s1 s2)
          (ensures Seq.length s1 == Seq.length s2)
          [SMTPat (permutation s1 s2)]
  = 
  reveal_opaque (`%permutation) (permutation s1 s2);
  Seq.Properties.perm_len s1 s2

let append_permutations_3 (s1 s2 s3 s1' s3': Seq.seq int):
  Lemma
    (requires permutation s1 s1' /\ permutation s3 s3')
    (ensures permutation (Seq.append s1 (Seq.append s2 s3)) (Seq.append s1' (Seq.append s2 s3')))
= (
  reveal_opaque (`%permutation) (permutation s1 s1');
  reveal_opaque (`%permutation) (permutation s2 s2);
  reveal_opaque (`%permutation) (permutation s3 s3');
  Seq.Properties.append_permutations s2 s3 s2 s3';
  reveal_opaque (`%permutation) (permutation (Seq.append s1 (Seq.append s2 s3)) (Seq.append s1' (Seq.append s2 s3')));
  Seq.Properties.append_permutations s1 (Seq.append s2 s3) s1' (Seq.append s2 s3')
  )

(* workaround for #151 *)
let append_permutations_3_squash (s1 s2 s3 s1' s3': Seq.seq int)
  (_ : squash (permutation s1 s1' /\ permutation s3 s3'))
  : squash (permutation (Seq.append s1 (Seq.append s2 s3)) (Seq.append s1' (Seq.append s2 s3')))
= append_permutations_3 s1 s2 s3 s1' s3'

let seq_swap_commute (s: Seq.seq int) (i j: nat_smaller (Seq.length s)):
  Lemma (seq_swap s i j == seq_swap s j i)
  = (
    let sij = seq_swap s i j in
    let sji = seq_swap s j i in
    assert (Seq.length sij = Seq.length sji);
    assert (forall (k:nat{k < Seq.length sij}). (Seq.index sij k == Seq.index sji k));
    Seq.lemma_eq_elim sij sji;
    ()
  )

let permutation_swap (s: Seq.seq int) (i j: nat_smaller (Seq.length s)):
  Lemma (permutation s (seq_swap s i j))
    [SMTPat (permutation s (seq_swap s i j))]
    = (
      reveal_opaque (`%permutation) (permutation s (seq_swap s i j));
      if i <= j
        then (Seq.Properties.lemma_swap_permutes s i j; seq_swap_commute s i j)
        else Seq.Properties.lemma_swap_permutes s j i)

let assert_prop (p: prop) : Pure unit (requires p) (ensures fun _ -> p) = ()

let compose_permutations (s1 s2 s3: Seq.seq int)
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

let permutation_refl (s: Seq.seq int)
  : Lemma (ensures permutation s s)
    [SMTPat (permutation s s)]
   =
   (
      reveal_opaque (`%permutation) (permutation s s);
      ()
   )

(** Overriding array accesses and assignment with the pts_to_range version **)

let op_Array_Access
  (#t: Type)
  (a: A.array t)
  (i: SZ.t)
  (#l: nat{l <= SZ.v i})
  (#r: nat{SZ.v i < r})
  (#s: Ghost.erased (Seq.seq t))
  (#p: perm)
: stt t
    (requires
      A.pts_to_range a l r #p s)
    (ensures fun res ->
      A.pts_to_range a l r #p s **
      pure (Seq.length s == r - l /\
            res == Seq.index s (SZ.v i - l)))
= pts_to_range_index a i #l #r #s #p

let op_Array_Assignment
  (#t: Type)
  (a: A.array t)
  (i: SZ.t)
  (v: t)
  (#l: nat{l <= SZ.v i})
  (#r: nat{SZ.v i < r})
  (#s0: Ghost.erased (Seq.seq t))
: stt unit
    (requires A.pts_to_range a l r s0)
    (ensures fun _ -> 
      exists* s.
        A.pts_to_range a l r s **
        pure(
          Seq.length s0 == r - l /\ s == Seq.upd s0 (SZ.v i - l) v
        ))
= pts_to_range_upd a i v #l #r

(** Partitioning **)

```pulse
fn swap (a: A.array int) (i j: nat) (#l:nat{l <= i /\ l <= j}) (#r:nat{i < r /\ j < r})
  (#s0: Ghost.erased (Seq.seq int))
  requires A.pts_to_range a l r s0
  ensures
    exists* s. 
      A.pts_to_range a l r s **
      pure (Seq.length s0 = r - l /\
            s == seq_swap s0 (i - l) (j - l) /\
            permutation s0 s)
{
  A.pts_to_range_prop a;
  let vi = a.(SZ.uint_to_t i);
  let vj = a.(SZ.uint_to_t j);
  (a.(SZ.uint_to_t i) <- vj);
  (a.(SZ.uint_to_t j) <- vi);
  ()
}
```

```pulse
fn partition (a: A.array int) (lo: nat) (hi:(hi:nat{lo < hi}))
  (lb rb: erased int)
  (#s0: Ghost.erased (Seq.seq int))
  requires (
    A.pts_to_range a lo hi s0 **
    pure (
      hi <= A.length a /\
      Seq.length s0 = hi - lo /\
      between_bounds s0 lb rb
      )
  )
  returns r: nat & nat & int // left index, right index, pivot value
  ensures exists* s.
    A.pts_to_range a lo hi s **
    pure (
      Seq.length s = hi - lo /\ Seq.length s0 = hi - lo
      /\ lo <= r._1 /\ r._1 < r._2 /\ r._2 <= hi /\ hi <= A.length a
      /\ lb <= r._3 /\ r._3 <= rb
      /\ (forall (k: nat).   lo <= k /\ k < r._1  ==> Seq.index s (k - lo) <  r._3)
      /\ (forall (k: nat). r._1 <= k /\ k < r._2  ==> Seq.index s (k - lo) == r._3)
      /\ (forall (k: nat). r._2 <= k /\ k < hi    ==> Seq.index s (k - lo) >  r._3)
      /\ between_bounds s lb rb
      /\ permutation s0 s
    )
{
  let pivot = a.(SZ.uint_to_t (hi - 1));
  let mut i = lo;
  let mut j = lo;
  let mut k = lo;
  while (let vk = !k; (vk < hi - 1))
    invariant b . exists* s vi vj vk. (
      A.pts_to_range a lo hi s **
      R.pts_to i vi **
      R.pts_to j vj **
      R.pts_to k vk **
      pure (
        b == (vk < hi - 1) /\
        //eq2_prop #bool b (vk < hi - 1) /\
        lo <= vk /\ vk <= hi - 1 /\
        lo <= vi /\ vi <= vj /\ vj <= vk /\
        lb <= pivot /\ pivot <= rb /\
        Seq.length s = hi - lo /\
        Seq.index s (hi - 1 - lo) = pivot
        /\ (forall (l: nat). lo <= l /\ l < vi ==> Seq.index s (l - lo) <  pivot)
        /\ (forall (l: nat). vi <= l /\ l < vj ==> Seq.index s (l - lo) == pivot)
        /\ (forall (l: nat). vj <= l /\ l < vk ==> Seq.index s (l - lo) >  pivot)
        /\ permutation s0 s
        /\ between_bounds s lb rb
      ))
  {
    let vk = !k;
    let ak = a.(SZ.uint_to_t vk);
    if (ak < pivot) {
      let vi = !i;
      let vj = !j;
      swap a vj vk;
      swap a vi vj;
      i := vi + 1;
      j := vj + 1;
      k := vk + 1;
    } else if (ak = pivot) {
      let vj = !j;
      swap a vj vk;
      j := vj + 1;
      k := vk + 1;
    } else {
      k := vk + 1;
    };
  };

  let vi  : nat = !i;
  let vj  : nat = !j;
  let vj' : nat = vj + 1;

  // swap j with hi, essentially transition from shape
  //  [ < < < < = = = = > > > > p ]
  // to shape:
  //  [ < < < < = = = = p > > > > ]
  // where < = > represent values that are less than, equal, and greater than the pivot p
  swap a vj (hi - 1);
  (vi, vj', pivot)
}
```

#restart-solver
#push-options "--retry 5"
let transfer_larger_slice
  (s : Seq.seq int)
  (shift : nat)
  (l : nat{shift <= l})
  (r : nat{l <= r /\ r <= shift + Seq.length s})
  (lb: int)
: Lemma
    (requires 
      forall (k: int). l <= k /\ k < r ==> (lb <= Seq.index s (k - shift))
    )
    (ensures larger_than (Seq.slice s (l - shift) (r - shift)) lb)
= assert (forall (k: int). l <= k /\ k < r ==> (lb <= Seq.index s (k - shift)));
  assert (forall (k: int). l <= (k+shift) /\ (k+shift) < r ==> (lb <= Seq.index s ((k+shift) - shift)));
  assert (forall (k: int). l - shift <= k /\ k < r - shift ==> (lb <= Seq.index s k));
  ()

#push-options "--z3rlimit_factor 4 --split_queries no"
let transfer_smaller_slice
  (s : Seq.seq int)
  (shift : nat)
  (l : nat{shift <= l})
  (r : nat{l <= r /\ r <= shift + Seq.length s})
  (rb: int)
: Lemma
    (requires 
      forall (k: int). l <= k /\ k < r ==> (Seq.index s (k - shift) <= rb)
    )
    (ensures smaller_than (Seq.slice s (l - shift) (r - shift)) rb)
= assert (forall (k: int). l <= k /\ k < r ==> (Seq.index s (k - shift) <= rb));
  assert (forall (k: int). l <= (k+shift) /\ (k+shift) < r ==> (Seq.index s ((k+shift) - shift) <= rb));
  assert (forall (k: int). l - shift <= k /\ k < r - shift ==> (Seq.index s k <= rb));
  ()
#pop-options
#pop-options

let transfer_equal_slice
  (s : Seq.seq int)
  (shift : nat)
  (l : nat{shift <= l})
  (r : nat{l <= r /\ r <= shift + Seq.length s})
  (rb: int)
: Lemma
    (requires 
      forall (k: int). l <= k /\ k < r ==> (Seq.index s (k - shift) == rb)
    )
    (ensures larger_than (Seq.slice s (l-shift) (r-shift)) rb /\
             smaller_than (Seq.slice s (l - shift) (r - shift)) rb)
= transfer_smaller_slice s shift l r rb;
  transfer_larger_slice s shift l r rb;
  ()

#push-options "--z3rlimit_factor 8 --retry 5"
```pulse
fn partition_wrapper (a: A.array int) (lo: nat) (hi:(hi:nat{lo < hi}))
  (lb rb: erased int)
  (#s0: Ghost.erased (Seq.seq int))
  requires (
    A.pts_to_range a lo hi s0 **
    pure (
      hi <= A.length a /\
      Seq.length s0 = hi - lo /\
      between_bounds s0 lb rb
      )
  )
  returns r: nat & nat & int // left index, right index, pivot value
  ensures exists* s1 s2 s3. (
    A.pts_to_range a lo   r._1 s1 **
    A.pts_to_range a r._1 r._2 s2 **
    A.pts_to_range a r._2 hi   s3 **
    pure (
      lo <= r._1 /\ r._1 < r._2 /\ r._2 <= hi /\ hi <= A.length a /\
      lb <= r._3 /\ r._3 <= rb /\
      Seq.length s1 == r._1 - lo /\ Seq.length s2 == r._2 - r._1 /\ Seq.length s3 == hi - r._2
      /\ between_bounds s1 lb r._3
      /\ between_bounds s2 r._3 r._3
      /\ between_bounds s3 r._3 rb
      /\ permutation s0 (Seq.append s1 (Seq.append s2 s3))
   ))
{
  let r = partition a lo hi lb rb #s0;
  with s. assert (A.pts_to_range a lo hi s);

  pts_to_range_split a lo r._1 hi;
  pts_to_range_split a r._1 r._2 hi;
  with s1. assert (A.pts_to_range a lo r._1 s1);
  with s2. assert (A.pts_to_range a r._1 r._2 s2);
  with s3. assert (A.pts_to_range a r._2 hi s3);
  
  assert (pure (Seq.length s1 == r._1 - lo));
  assert (pure (Seq.length s2 == r._2 - r._1));
  assert (pure (Seq.length s3 == hi - r._2));
  
  assert pure (squash (permutation s0 (Seq.append s1 (Seq.append s2 s3))));
  
  transfer_smaller_slice s lo lo r._1 r._3;
  assert (pure (between_bounds s1 lb r._3));

  transfer_equal_slice s lo r._1 r._2 r._3;
  assert (pure (between_bounds s2 r._3 r._3));

  transfer_larger_slice s lo r._2 hi r._3;
  assert (pure (between_bounds s3 r._3 rb));
  
  r
}
```
#pop-options

(** QuickSort **)

unfold
let pure_pre_quicksort (a: A.array int) (lo: nat) (hi:(hi:nat{lo <= hi})) (lb rb: int) (s0: Seq.seq int)
  = hi <= A.length a /\
    between_bounds s0 lb rb /\
    Seq.length s0 = hi - lo /\
    lo <= A.length a /\
    lb <= rb

unfold
let pure_post_quicksort (a: A.array int) (lo: nat) (hi:(hi:nat{lo <= hi})) (lb rb: int) (s0 s: Seq.seq int)
  = hi <= A.length a /\
    Seq.length s0 = hi - lo /\
    Seq.length s = hi - lo /\
    sorted s /\
    between_bounds s lb rb /\
    permutation s0 s

```pulse
// this could probably be refactored into just joining two adjacent sorted arrays, and then define this calling that function twice
ghost
fn quicksort_proof
  (a: A.array int)
  (lo: nat)
  (c1:(c1:nat{lo <= c1}))
  (c2:(c2:nat{c1 <= c2}))
  (hi:(hi:nat{c2 <= hi}))
  (lb rb pivot : int)
  (#s0: erased (Seq.seq int))
  (s1 s2 s3 : Seq.seq int)
  requires
    (exists* s1'. (A.pts_to_range a lo c1 s1' ** pure (pure_post_quicksort a lo c1 lb pivot s1 s1'))) **
    (exists* s3'. (A.pts_to_range a c2 hi s3' ** pure (pure_post_quicksort a c2 hi pivot rb s3 s3'))) **
    A.pts_to_range a c1 c2 s2 **
    pure (Seq.length s0 == hi - lo
          /\ lb <= pivot /\ pivot <= rb
          /\ permutation s0 (Seq.append s1 (Seq.append s2 s3))
          /\ between_bounds s2 pivot pivot)
  ensures
    exists* s.
      A.pts_to_range a lo hi s **
      pure (pure_post_quicksort a lo hi lb rb s0 s)
{
  with s1'. assert (A.pts_to_range a lo c1 s1');
  with s3'. assert (A.pts_to_range a c2 hi s3');

  pts_to_range_join a c1 c2 hi;
  pts_to_range_join a lo c1 hi;

  let _ = append_permutations_3_squash s1 s2 s3 s1' s3' ();
  let _ = lemma_sorted_append_squash s2 s3' pivot pivot pivot rb ();
  let _ = lemma_sorted_append_squash s1' (Seq.append s2 s3') lb pivot pivot rb ();
  ()
}
```

let quicksort_pre a lo hi s0 lb rb : vprop =
  A.pts_to_range a lo hi s0 ** pure (pure_pre_quicksort a lo hi lb rb s0)

let quicksort_post a lo hi s0 lb rb : vprop =
  exists* s. (A.pts_to_range a lo hi s ** pure (pure_post_quicksort a lo hi lb rb s0 s))
