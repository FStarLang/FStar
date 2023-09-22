module PulseByExample

module PM = Pulse.Main
open Pulse.Lib.Core

(* 
  Things to note:
  - syntax extension notation
  - 1 or more arguments
  - precondition and postcondition
*)

let my_list : list int = [1;2;3]

```pulse
fn five (_:unit)
  requires emp
  returns n:int
  ensures  pure (n == 5)
{ 
  5
}
```

open Pulse.Lib.Reference
module R = Pulse.Lib.Reference

(* 
  Things to note:
  - separating conjunction
  - tick for erased, implicit values
  - default full permission
  - heap reference, read and write
*)
```pulse
fn ref_swap (r1 r2:ref int)
  requires R.pts_to r1 'n1 
        ** R.pts_to r2 'n2
  ensures  R.pts_to r1 'n2
        ** R.pts_to r2 'n1
{
  let v1 = !r1;
  let v2 = !r2;
  r1 := v2;
  r2 := v1
}
```

open Pulse.Lib.Array
module A = Pulse.Lib.Array
module SZ = FStar.SizeT
open Pulse.Class.BoundedIntegers

(* 
  Things to note:
  - heap array, read and write
  - exists and forall in spec
  - machine integers, ops on bounded integers
*)

```pulse
fn arr_swap (#t:Type0) (n i j:SZ.t) (a:larray t (v n))
  requires 
    A.pts_to a 's0 **
    pure (Seq.length 's0 == v n /\ i < n /\ j < n)
  ensures exists s. 
    A.pts_to a s **
    pure (Seq.length 's0 == v n /\ Seq.length s == v n /\ i < n /\ j < n
       /\ (forall (k:nat). k < v n /\ k <> v i /\ k <> v j ==> Seq.index 's0 k == Seq.index s k)
       /\ Seq.index 's0 (v i) == Seq.index s (v j)
       /\ Seq.index 's0 (v j) == Seq.index s (v i))
{
  let vi = a.(i);
  let vj = a.(j);
  a.(i) <- vj;
  a.(j) <- vi;
}
```

(* 
  Things to note:
  - control flow: while loop, if
  - mutable local reference, read and write
  - variable permission
*)
```pulse
fn max (n:SZ.t) (a:larray nat (v n))
  requires A.pts_to a #'p 's ** pure (Seq.length 's == v n)
  returns r:nat
  ensures A.pts_to a #'p 's
       ** pure (Seq.length 's == v n
             /\ (forall (i:nat). i < v n ==> Seq.index 's i <= r))
{
  let mut i : SZ.t = 0sz;
  let mut max : nat = 0; //Note: without that `nat` annotation, this fails with very poor feedback. "SMT query failed"
  while (let vi = !i; (vi < n))
  invariant b. exists (vi:SZ.t) (vmax:nat).
    A.pts_to a #'p 's **
    R.pts_to i vi **
    R.pts_to max vmax **
    pure (vi <= n
       /\ (forall (j:nat). j < v vi ==> Seq.index 's j <= vmax)
       /\ b == (vi < n))
  {
    let vi = !i;
    let vmax = !max;
    let v = a.(vi);
    i := vi + 1sz;
    if (v > vmax) {
      max := v;
    }
  };
  with (vi:SZ.t) (vmax:nat). assert (
    R.pts_to i vi **
    R.pts_to max vmax **
    pure (vi = n
       /\ (forall (j:nat). j < v vi ==> Seq.index 's j <= vmax))
  );
  let vmax = !max;
  vmax
}
```
//this option should become the default, once I shake out the handling of address-taking
#push-options "--ext 'pulse:rvalues'"
```pulse
fn max_alt (n:SZ.t) (a:larray nat (v n))
  requires A.pts_to a #'p 's ** pure (Seq.length 's == v n)
  returns r:nat
  ensures A.pts_to a #'p 's
       ** pure (Seq.length 's == v n
             /\ (forall (i:nat). i < v n ==> Seq.index 's i <= r))
{
  let mut i = 0sz;
  let mut max : nat = 0;
  while ((i < n))
  invariant b. exists (vi:SZ.t) (vmax:nat).
    A.pts_to a #'p 's **
    R.pts_to i vi **
    R.pts_to max vmax **
    pure (vi <= n
       /\ (forall (j:nat). j < v vi ==> Seq.index 's j <= vmax)
       /\ b == (vi < n))
  {
    let v = a.(i);
    i := i + 1sz;
    if (v > max) {
      max := v;
    }
  };
  max
}
```
#pop-options

(* 
- some more mature example (e.g. sorting alg)

- some simple record data structure along with a library of functions on this DS
  (e.g. library of functions on 2D points)

- build up to explaining the pulse implementation of lpht? -- emphasis on connecting
  pure implementation to imperative code
- pulse linked list? -- more traditional sep logic example 

- concurrency, e.g. par incr of a ctr
*)