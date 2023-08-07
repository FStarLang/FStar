module EOIPulseByExample
module PM = Pulse.Main
open Pulse.Lib.Core
open FStar.Ghost
open Steel.FractionalPermission
open Pulse.Class.BoundedIntegers
open Pulse.Lib.Reference
module R = Pulse.Lib.Reference

(* 
  The following three examples cover
  - heap references and arrays, read/write
  - mutable local reference, read/write
  - separating conjunction
  - erased, implict arguments
  - permissions
  - exists and forall in a spec
  - machine integers, ops on bounded integers
  - control flow: while loop and if

  NOT covered:
  1. local heap allocation, e.g. `let r = R.alloc 0`
  2. match control flow
  3. interacting with the sep logic context via
    - fold/unfold
    - introduce exists...assert...
    - with...assert...
  4. par

  DPE snippets can cover 1-3
*)



(* 
- heap reference
- separating conjunction
- erased, implict argument
- permissions
- reference read and write
*)
```pulse
fn ref_swap (r1 r2:ref int) (#n1 #n2:erased int)
  requires pts_to r1 full_perm n1
        ** pts_to r2 full_perm n2
  ensures  pts_to r1 full_perm n2
        ** pts_to r2 full_perm n1
{
  let x = !r1;
  let y = !r2;
  r1 := y;
  r2 := x
}
```

open Pulse.Lib.Array
open Pulse.Lib.Array.Core
module A = Pulse.Lib.Array
module SZ = FStar.SizeT

(* 
- heap array
- exists and forall in spec
- machine integers, ops on bounded integers
- array read and write
*)
```pulse
fn arr_swap (a:array int) (n i j:SZ.t) (#s0:erased (Seq.seq int))
  requires 
    A.pts_to a full_perm s0 **
    pure (Seq.length s0 == v n /\ i < n /\ j < n)
  ensures exists s. 
    A.pts_to a full_perm s **
    pure (Seq.length s0 == v n /\ Seq.length s == v n /\ i < n /\ j < n
       /\ (forall (k:nat). k < v n /\ k <> v i /\ k <> v j ==> Seq.index s0 k == Seq.index s k)
       /\ Seq.index s0 (v i) == Seq.index s (v j)
       /\ Seq.index s0 (v j) == Seq.index s (v i)
    )
{
  let vi = a.(i);
  let vj = a.(j);
  (a.(i) <- vj);
  (a.(j) <- vi);
}
```

(* 
- control flow: while loop, if
- mutable local reference, read/write
*)
```pulse
fn compare (#t:eqtype) (n:SZ.t) (a1 a2:array t)
           (#p1 #p2:perm) (#s1 #s2:erased (Seq.seq t))
  requires A.pts_to a1 p1 s1
        ** A.pts_to a2 p2 s2
        ** pure (Seq.length s1 == v n /\ Seq.length s2 == v n)
  returns res:bool
  ensures A.pts_to a1 p1 s1
       ** A.pts_to a2 p2 s2
       ** pure (res <==> Seq.equal s1 s2)
{
  let mut i = 0sz;
  while (let vi = !i; 
    if (vi < n) { 
      let v1 = a1.(vi); 
      let v2 = a2.(vi); 
      (v1 = v2) } 
    else { false } )
  invariant b. exists vi. (
    R.pts_to i full_perm vi **
    A.pts_to a1 p1 s1 **
    A.pts_to a2 p2 s2 **
    pure (vi <= n
       /\ (forall (j:nat). j < v vi ==> Seq.index s1 j == Seq.index s2 j)
       /\ (b == (vi < n && Seq.index s1 (v vi) = Seq.index s2 (v vi))))
  )
  {
    let vi = !i; 
    i := vi + 1sz;
  };
  let vi = !i;
  let res = (vi = n);
  res
}
```