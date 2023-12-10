module QuickSortParallel
open Pulse.Lib.Pervasives
module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module T = FStar.Tactics
module SZ = FStar.SizeT

let nat_smaller (n: nat) = i:nat{i < n}
let seqn (n: nat) = (s:Seq.seq int{Seq.length s = n})
let arrayn (n: nat) = (a:A.array int{A.length a = n})
let nat_fits = n:nat{SZ.fits n}

let seq_swap (#a: Type) (s: Seq.seq a) (i j: nat_smaller (Seq.length s)) =
  Seq.swap s j i

let larger_than (s: Seq.seq int) (lb: int)
  = forall (k: nat). k < Seq.length s ==> lb <= Seq.index s k

let larger_than_slice (s: Seq.seq int) (lo: nat) (hi: nat{lo <= hi /\ hi <= Seq.length s}) (lb: int):
  Lemma (requires larger_than s lb)
  (ensures larger_than (Seq.slice s lo hi) lb)
= ()

let smaller_than (s: Seq.seq int) (rb: int)
  = forall (k: nat). k < Seq.length s ==> Seq.index s k <= rb

let between_bounds (s: Seq.seq int) (lb rb: int)
  = larger_than s lb /\ smaller_than s rb

(** Permutation reasoning **)

[@@"opaque_to_smt"]
let permutation = Seq.Properties.permutation int

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
  //(#s: Ghost.erased (Seq.seq t) {US.v i < Seq.length s})
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
fn swap (a: A.array int) (i j: nat_fits) (#l:(l:nat{l <= i /\ l <= j})) (#r:(r:nat{i < r /\ j < r}))
  (#s0: Ghost.erased (Seq.seq int))
  requires A.pts_to_range a l r s0
  ensures exists s. (A.pts_to_range a l r s
    ** pure (Seq.length s0 = r - l /\ Seq.length s = r - l /\
      s = seq_swap s0 (i - l) (j - l) /\ permutation s0 s
    ))
{
  let vi = a.(SZ.uint_to_t i);
  let vj = a.(SZ.uint_to_t j);
  (a.(SZ.uint_to_t i) <- vj);
  (a.(SZ.uint_to_t j) <- vi);
  ()
}
```

let sorted (s: Seq.seq int)
  = forall (i j: nat). 0 <= i /\ i <= j /\ j < Seq.length s ==> Seq.index s i <= Seq.index s j

let to_nat (x: int{x >= 0}): nat = x

#push-options "--z3rlimit 30"

(* Proof below is flaky for whatever reason on 4.8.5, but not
4.12.3. Use this for now. *)
#restart-solver

```pulse
fn partition (a: A.array int) (lo: nat) (hi:(hi:nat{lo < hi - 1})) (n: nat) (lb rb: int) (#s0: Ghost.erased (Seq.seq int))
  requires (
    A.pts_to_range a lo hi s0 **
    pure (
      hi - 1 < n /\
      n = A.length a /\ SZ.fits n /\
      Seq.length s0 = hi - lo /\
      between_bounds s0 lb rb
      )
  )
  returns r: nat & nat & int // left, right, pivot
  ensures exists s. (
    A.pts_to_range a lo hi s
     **
    pure (
      Seq.length s = hi - lo /\ Seq.length s0 = hi - lo
      /\ lo <= r._1 /\ r._1 < r._2 /\ r._2 <= hi /\ hi - 1 < n
      /\ lb <= r._3 /\ r._3 <= rb
      /\ (forall (k: nat). k < r._1 - lo ==> Seq.index s k < r._3)
      /\ (forall (k: nat). r._1 - lo <= k /\ k <= r._2 - 1 - lo ==> Seq.index s k == r._3)
      /\ (forall (k: nat). r._2 - lo <= k /\ k <= hi - 1 - lo ==> Seq.index s k > r._3)
      /\ between_bounds s lb rb
      /\ permutation s0 s
   ))
{
  let pivot = a.(SZ.uint_to_t (hi - 1));
  let mut i = lo - 1;
  let mut j = lo - 1;
  let mut k = lo;
  while (let vk = !k; (vk < hi - 1))
    invariant b . exists s vi vj vk. (
      A.pts_to_range a lo hi s **
      R.pts_to i vi **
      R.pts_to j vj **
      R.pts_to k vk **
      pure (
        b == (vk < hi - 1) /\
        //eq2_prop #bool b (vk < hi - 1) /\
        lo <= vk /\ vk <= hi - 1 /\
        lo - 1 <= vi /\ vi <= vj /\ vj < vk /\
        lb <= pivot /\ pivot <= rb /\
        Seq.length s = hi - lo /\
        Seq.index s (hi - 1 - lo) = pivot
        /\ (forall (l:nat). 0 <= l /\ l <= vi - lo ==> Seq.index s l < pivot)
        /\ (forall (l:nat). vi + 1 - lo <= l /\ l <= vj - lo ==> Seq.index s l == pivot)
        /\ (forall (l:nat). vj + 1 - lo <= l /\ l <= vk - 1 - lo ==> Seq.index s l > pivot)
        /\ permutation s0 s
        /\ between_bounds s lb rb
      ))
  {
    let vk = !k;
    let ak = a.(SZ.uint_to_t vk);
    if (ak < pivot) {
      let vi = !i;
      i := vi + 1;
      let vj = !j;
      j := vj + 1;
      swap a (vj + 1) vk;
      swap a (vi + 1) (vj + 1);
      k := vk + 1;
      ()
    }
    else {
      if (ak = pivot) {
        let vj = !j;
        j := vj + 1;
        swap a (vj + 1) vk;
        k := vk + 1;
        ()
      }
      else {
        k := vk + 1;
        ()
      };
    };
  };

  let vj = !j;
  j := vj + 1;

  // swap j with hi
  swap a (vj + 1) (hi - 1);

  let vi = !i;
  i := vi + 1;
  let vi' = to_nat (vi + 1);
  let vj' = to_nat (vj + 2);
  (vi', vj', pivot)
}
```
#pop-options

let transfer_larger_slice (s: Seq.seq int) (l: nat) (r: nat{l <= r /\ r <= Seq.length s}) (lb: int):
  Lemma
    (requires (forall (k: nat). l <= k /\ k < r ==> (lb <= Seq.index s k)))
    (ensures larger_than (Seq.slice s l r) lb)
= ()

let transfer_smaller_slice (s: Seq.seq int) (l: nat) (r: nat{l <= r /\ r <= Seq.length s}) (rb: int):
  Lemma
    (requires (forall (k: nat). l <= k /\ k < r ==> (Seq.index s k <= rb)))
    (ensures smaller_than (Seq.slice s l r) rb)
= ()

#push-options "--z3rlimit 30"
```pulse
fn partition_wrapper (a: A.array int) (lo: nat) (hi:(hi:nat{lo < hi - 1})) (n: nat) (lb rb: int) (#s0: Ghost.erased (Seq.seq int))
  requires (
    A.pts_to_range a lo hi s0 **
    pure (hi - 1 < n /\ n = A.length a /\ SZ.fits n /\ between_bounds s0 lb rb
      /\ Seq.length s0 = hi - lo)
  )
  returns r: nat & nat & int // left, right, pivot
  ensures exists s1 s2 s3. (
    A.pts_to_range a lo r._1 s1 **
    A.pts_to_range a r._1 r._2 s2 **
    A.pts_to_range a r._2 hi s3 **
    pure (
      lo <= r._1 /\ r._1 < r._2 /\ r._2 <= hi /\ hi - 1 < n /\
      lb <= r._3 /\ r._3 <= rb /\
      Seq.length s1 = r._1 - lo /\ Seq.length s2 = r._2 - r._1 /\ Seq.length s3 = hi - r._2
      /\ between_bounds s1 lb r._3
      /\ between_bounds s2 r._3 r._3
      /\ between_bounds s3 r._3 rb
      /\ permutation s0 (Seq.append s1 (Seq.append s2 s3))
   ))
{
  let r = partition a lo hi n lb rb #s0;
  with s. assert (A.pts_to_range a lo hi s);

  transfer_smaller_slice s 0 (r._1 - lo) r._3;
  transfer_larger_slice s (r._2 - lo) (hi - lo) r._3;

  let pivot = r._3;
  pts_to_range_split a lo r._1 hi;
  with s1. assert (A.pts_to_range a lo r._1 s1);
  assert_prop (s1 == Seq.slice s 0 (r._1 - lo));

  assert_prop (between_bounds s1 lb r._3);

  with s23. assert (A.pts_to_range a r._1 hi s23);
  assert_prop (s23 == Seq.slice s (r._1 - lo) (Seq.length s));

  assert (A.pts_to_range a lo r._1 s1);
  pts_to_range_split a r._1 r._2 hi;

  with s2. assert (A.pts_to_range a r._1 r._2 s2);
  assert_prop (s2 == Seq.slice s23 0 (r._2 - r._1));
  assert_prop (s2 == Seq.slice s (r._1 - lo) (r._2 - lo));
  with s3. assert (A.pts_to_range a r._2 hi s3);
  assert_prop (s3 == Seq.slice s (r._2 - lo) (hi - lo));
  assert_prop (Seq.length s1 = r._1 - lo);
  assert_prop (Seq.length s2 = r._2 - r._1);
  assert_prop (Seq.length s3 = hi - r._2);
  assert_prop (s == Seq.append s1 (Seq.append s2 s3));
  r
}
```
#pop-options

(** QuickSort **)

unfold
let pure_pre_quicksort (a: A.array int) (lo: nat) (hi:(hi:int{-1 <= hi - 1 /\ lo <= hi})) (lb rb: int) (n: nat) (s0: Seq.seq int)
  = hi - 1 < n /\ between_bounds s0 lb rb /\ Seq.length s0 = hi - lo /\ SZ.fits n /\ A.length a = n /\ lo <= n /\ lb <= rb

unfold
let pure_post_quicksort (a: A.array int) (lo: nat) (hi:(hi:int{-1 <= hi - 1 /\ lo <= hi})) (lb rb: int) (n: nat) (s0 s: Seq.seq int)
  = hi - 1 < n /\ Seq.length s0 = hi - lo /\ Seq.length s = hi - lo /\ SZ.fits n /\ A.length a = n
      /\ sorted s /\ between_bounds s lb rb /\ permutation s0 s

(* Assuming recursion *)
```pulse
fn quicksort' (a: A.array int) (lo: nat)
(hi:(hi:int{-1 <= hi - 1 /\ lo <= hi}))
(lb rb: int) (n: nat) (#s0: Ghost.erased (Seq.seq int))
  requires A.pts_to_range a lo hi s0 ** pure (pure_pre_quicksort a lo hi lb rb n s0)
  ensures exists s. (A.pts_to_range a lo hi s ** pure (pure_post_quicksort a lo hi lb rb n s0 s))
{ admit() }
```

#push-options "--z3rlimit 50"
```pulse
fn quicksort (a: A.array int) (lo: nat) (hi:(hi:int{-1 <= hi - 1 /\ lo <= hi})) (lb rb: int) (n: nat) (#s0: Ghost.erased (Seq.seq int))
  requires A.pts_to_range a lo hi s0 ** pure (pure_pre_quicksort a lo hi lb rb n s0)
  ensures exists s. (A.pts_to_range a lo hi s ** pure (pure_post_quicksort a lo hi lb rb n s0 s))
  // decreases hi + 1 - lo
{
  if (lo < hi - 1)
  {
    let r = partition_wrapper a lo hi n lb rb;
    let pivot = r._3;
    with s1. assert (A.pts_to_range a lo r._1 s1);
    with s2. assert (A.pts_to_range a r._1 r._2 s2);
    with s3. assert (A.pts_to_range a r._2 hi s3);
    //assert_prop (squash (permutation s0 (Seq.append s1 (Seq.append s2 s3))));

    if (lo < hi + 1000) // worth parallelizing
    {
      parallel
      requires (A.pts_to_range a lo r._1 s1 ** pure (pure_pre_quicksort a lo r._1 lb pivot n s1))
          and (A.pts_to_range a r._2 hi s3 ** pure (pure_pre_quicksort a r._2 hi pivot rb n s3))
      ensures (exists s. (A.pts_to_range a lo r._1 s ** pure (pure_post_quicksort a lo r._1 lb pivot n s1 s)))
          and (exists s. (A.pts_to_range a r._2 hi s ** pure (pure_post_quicksort a r._2 hi pivot rb n s3 s)))
      {
        // termination check
        assert_prop (hi - lo > (r._1 - 1) + 1 - lo);
        quicksort' a lo r._1 lb pivot n;// (Ghost.hide s1);
      }
      {
        // termination check
        assert_prop (hi - lo > hi - r._2);
        quicksort' a r._2 hi pivot rb n;
      };

      with s1'. assert (A.pts_to_range a lo r._1 s1');
      with s3'. assert (A.pts_to_range a r._2 hi s3');
      pts_to_range_join a lo r._1 r._2;
      pts_to_range_join a lo r._2 hi;
      Seq.append_assoc s1' s2 s3';
      append_permutations_3 s1 s2 s3 s1' s3';
      ()
    }
    else // sequential
    {
      // termination check
      assert_prop (hi - lo > (r._1 - 1) + 1 - lo);
      quicksort' a lo r._1 lb pivot n;

      // termination check
      assert_prop (hi - lo > hi - r._2);
      quicksort' a r._2 hi pivot rb n;
  
      with s1'. assert (A.pts_to_range a lo r._1 s1');
      with s3'. assert (A.pts_to_range a r._2 hi s3');
      pts_to_range_join a lo r._1 r._2;
      pts_to_range_join a lo r._2 hi;
      Seq.append_assoc s1' s2 s3';
      append_permutations_3 s1 s2 s3 s1' s3';
      ()
    }
  }
  else {
    ()
  }
}
```
#pop-options
