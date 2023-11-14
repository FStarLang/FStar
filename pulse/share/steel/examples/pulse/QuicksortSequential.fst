module QuickSortSequential
module T = FStar.Tactics
module PM = Pulse.Main
//open Steel.ST.Util 
//open Steel.FractionalPermission
module U32 = FStar.UInt32
module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
open Pulse.Lib.Pervasives

#set-options "--ide_id_info_off"
#push-options "--using_facts_from '* -FStar.Tactics -FStar.Reflection'"
#restart-solver

let nat_smaller (n: nat) = i:nat{i < n}
let seqn (n: nat) = (s:Seq.seq int{Seq.length s = n})
let arrayn (n: nat) = (a:A.array int{A.length a = n})
let nat_fits = n:nat{SZ.fits n}

let seq_swap (#a: Type) (s: Seq.seq a) (i j: nat_smaller (Seq.length s)) =
  Seq.upd (Seq.upd s i (Seq.index s j)) j (Seq.index s i)

type permutation (#a: Type): Seq.seq a -> Seq.seq a -> Type =
  | Refl : s: Seq.seq a -> permutation s s
  | Swap : s1: Seq.seq a -> s2: Seq.seq a -> i: nat_smaller (Seq.length s2) -> j: nat_smaller (Seq.length s2) ->
   permutation s1 s2 -> permutation s1 (seq_swap s2 i j)

let permutation_swap (#a: eqtype) (s: Seq.seq a) (i j: nat_smaller (Seq.length s)):
  Lemma (permutation s (seq_swap s i j))
    [SMTPat (permutation s (seq_swap s i j))]
  = Squash.return_squash (Swap s s i j (Refl s))

let assert_prop (p: prop) : Pure unit (requires p) (ensures fun _ -> p) = ()
let assume_prop (p: prop) : Pure unit (requires True) (ensures fun _ -> p) = admit()

let rec compose_perm_aux (#a: eqtype) (s1 s2 s3: Seq.seq a) (#p12: permutation s1 s2) (#p23: permutation s2 s3):
  Tot (permutation s1 s3)
  (decreases p23)
  = match p23 with
  | Refl _ -> p12
  | Swap _ s4 i j p24 -> (
    assert (s3 = seq_swap s4 i j);
    let p14 = compose_perm_aux s1 s2 s4 #p12 #p24 in
    Swap s1 s4 i j p14)

let compose_permutations (#a:eqtype) (s1 s2 s3: Seq.seq a)
  : Lemma (requires permutation s1 s2 /\ permutation s2 s3)
    (ensures permutation s1 s3)
    [SMTPat (permutation s1 s2); SMTPat (permutation s2 s3)]
   = (let s12: squash (permutation s1 s2) = () in let s23: squash (permutation s2 s3) = () in
   Squash.bind_squash s12 (fun p12 -> Squash.bind_squash s23 (fun p23 -> Squash.return_squash (compose_perm_aux s1 s2 s3 #p12 #p23))))

let permutation_refl (#a:eqtype) (s: Seq.seq a)
  : Lemma (ensures permutation s s)
    [SMTPat (permutation s s)]
   = Squash.return_squash (Refl s)


```pulse
fn swap 
  (n: nat_fits) (a: arrayn n)
  (i j: nat_smaller n)
  (#s0: Ghost.erased (Seq.seq int))
  requires A.pts_to a s0 ** pure (Seq.length s0 == n)
  ensures exists s. (A.pts_to a #full_perm s **
    pure (Seq.length s0 = n /\ Seq.length s = n /\ s = seq_swap s0 i j
    /\ permutation s0 s))
{
  let vi = a.(SZ.uint_to_t i);
  let vj = a.(SZ.uint_to_t j);
  (a.(SZ.uint_to_t i) <- vj);
  (a.(SZ.uint_to_t j) <- vi);
  ()
}
```

let sorted_between (s: Seq.seq int) (a b: int)
  = forall (i j: nat). 0 <= i /\ a <= i /\ i < j /\ j <= b /\ j < Seq.length s ==> Seq.index s i <= Seq.index s j

let same_between (n: nat) (s0 s: seqn n) (lo hi: int)
  = forall (k: nat). 0 <= k /\ lo <= k /\ k <= hi /\ k < n ==> Seq.index s0 k = Seq.index s k

let between_bounds (n: nat) (s: seqn n) (lo hi: int) (lb rb: int)
  = forall (k: nat). 0 <= k /\ lo <= k /\ k <= hi /\ k < n ==> lb <= Seq.index s k /\ Seq.index s k <= rb

#push-options "--split_queries always --z3rlimit 20"
```pulse
fn partition (a: A.array int) (lo hi: int) (n: nat) (lb rb: int) (#s0: Ghost.erased (Seq.seq int))
  requires (
    A.pts_to a s0 **
    pure (
      0 <= hi /\ hi < n /\
      0 <= lo /\ lo < hi /\
      n = A.length a /\ SZ.fits n /\
      n = Seq.length s0
      /\ between_bounds n s0 lo hi lb rb
      )
  )
  returns r: int & int & int // left, right, pivot
  ensures exists s. (
    A.pts_to a s **
    pure (
      Seq.length s = n /\ Seq.length s0 = n /\ A.length a = n
      /\ lo <= r._1 /\ r._1 <= r._2 /\ r._2 <= hi /\ hi < n
      /\ (forall (k: nat). lo <= k /\ k < r._1 ==> Seq.index s k < r._3)
      /\ (forall (k: nat). r._1 <= k /\ k <= r._2 ==> Seq.index s k == r._3)
      /\ (forall (k: nat). r._2 + 1 <= k /\ k <= hi ==> Seq.index s k > r._3)
      /\ same_between n s0 s 0 (lo - 1) /\ same_between n s0 s (hi + 1) (n - 1)
      /\ between_bounds n s lo hi lb rb
      /\ permutation s0 s
    )
   )
{
  let pivot = a.(SZ.uint_to_t hi);
  let mut i = lo - 1;
  let mut j = lo - 1;
  let mut k = lo;
  while (let vk = !k; (vk < hi))
    invariant b . exists s vi vj vk. (
      A.pts_to a s **
      R.pts_to i vi **
      R.pts_to j vj **
      R.pts_to k vk **
      pure (
        //eq2_prop #bool b (vk < hi) /\
        b == (vk < hi) /\
        lo <= vk /\ vk <= hi /\
        lo - 1 <= vi /\ vi <= vj /\ vj < vk /\
        A.length a = n /\
        n = Seq.length s0
        /\ n = Seq.length s
        /\ Seq.index s hi = pivot
        /\ (forall (l:nat). lo <= l /\ l <= vi ==> Seq.index s l < pivot)
        /\ (forall (l:nat). vi + 1 <= l /\ l <= vj ==> Seq.index s l == pivot)
        /\ (forall (l:nat). vj + 1 <= l /\ l <= vk - 1 ==> Seq.index s l > pivot)
        /\ same_between n s0 s 0 (lo - 1) /\ same_between n s0 s (hi + 1) (n - 1)
        /\ between_bounds n s lo hi lb rb
        /\ permutation s0 s
      ))
  {
    let vk = !k;
    let ak = a.(SZ.uint_to_t vk);
    if (ak < pivot) {
      let vi = !i;
      i := vi + 1;
      let vj = !j;
      j := vj + 1;
      swap n a (vj + 1) vk;
      swap n a (vi + 1) (vj + 1);
      k := vk + 1;
      ()
    }
    else {
      if (ak = pivot) {
        let vj = !j;
        j := vj + 1;
        swap n a (vj + 1) vk;
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
  swap n a (vj + 1) hi;

  let vi = !i;
  i := vi + 1;
  let vi' = vi + 1;
  let vj' = vj + 1;
  (vi', vj', pivot)
}
```
#pop-options


```pulse
fn quicksort' (a: A.array int) (lo hi: int) (lb rb: int) (n: nat) (#s0: (s0:Ghost.erased (Seq.seq int){Seq.length s0 = n}))
  requires A.pts_to a s0 ** pure (
    0 <= lo /\ hi < n /\ Seq.length s0 = n /\ SZ.fits n /\ A.length a = n
    /\ hi >= -1 /\ lo <= n /\ lb <= rb
    /\ between_bounds n s0 lo hi lb rb
    )
  ensures exists s. (
    A.pts_to a s ** pure (
      0 <= lo /\ hi < n /\ Seq.length s0 = n /\ Seq.length s = n /\ SZ.fits n /\ A.length a = n
      /\ same_between n s0 s 0 (lo - 1) /\ same_between n s0 s (hi + 1) (n - 1)
      /\ sorted_between s lo hi
      /\ between_bounds n s lo hi lb rb
      /\ permutation s0 s
    )
  )
{ admit() }
```

```pulse
fn quicksort (a: A.array int) (lo hi: int) (lb rb: int) (n: nat) (#s0: (s0:Ghost.erased (Seq.seq int){Seq.length s0 = n}))
  requires A.pts_to a s0 ** pure (
    0 <= lo /\ hi < n /\ Seq.length s0 = n /\ SZ.fits n /\ A.length a = n
    /\ hi >= -1 /\ lo <= n /\ lb <= rb
    /\ between_bounds n s0 lo hi lb rb
    )
  ensures exists s. (
    A.pts_to a s ** pure (
      0 <= lo /\ hi < n /\ Seq.length s0 = n /\ Seq.length s = n /\ SZ.fits n /\ A.length a = n
      /\ same_between n s0 s 0 (lo - 1) /\ same_between n s0 s (hi + 1) (n - 1)
      /\ sorted_between s lo hi
      /\ between_bounds n s lo hi lb rb
      /\ permutation s0 s
    )
  )
  // decreases hi - lo (>= -2n)
{
  if (lo < hi)
  {
    let r = partition a lo hi n lb rb;
    let pivot = r._3;
    quicksort' a lo (r._1 - 1) lb pivot n;
    quicksort' a (r._2 + 1) hi pivot rb n;
    ()
  }
  else {
    ()
  }
}
```
