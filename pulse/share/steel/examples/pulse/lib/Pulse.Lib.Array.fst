module Pulse.Lib.Array
module PM = Pulse.Main
open Pulse.Lib.Core
open Pulse.Lib.Reference
open Pulse.Lib.Array.Core
open FStar.Ghost
module US = FStar.SizeT
module U8 = FStar.UInt8
open Pulse.Class.BoundedIntegers
module A = Pulse.Lib.Array.Core
module R = Pulse.Lib.Reference

```pulse
fn compare' (#t:eqtype) (l:US.t) (a1 a2:larray t (US.v l))
  requires pts_to a1 #'p1 's1
        ** pts_to a2 #'p2 's2
  returns res:bool
  ensures pts_to a1 #'p1 's1
       ** pts_to a2 #'p2 's2
       ** (pure (res <==> Seq.equal 's1 's2))
{
  pts_to_len a1 #'p1 #'s1;
  pts_to_len a2 #'p2 #'s2;
  let mut i = 0sz;
  while (let vi = !i; 
    if (vi < l) { 
      let v1 = a1.(vi); 
      let v2 = a2.(vi); 
      (v1 = v2) } 
    else { false } )
  invariant b. exists (vi:US.t). ( 
    R.pts_to i vi **
    A.pts_to a1 #'p1 's1 **
    A.pts_to a2 #'p2 's2 **
    pure (vi <= l
       /\ (b == (vi < l && Seq.index 's1 (US.v vi) = Seq.index 's2 (US.v vi)))
       /\ (forall (i:nat). i < US.v vi ==> Seq.index 's1 i == Seq.index 's2 i)))
  {
    let vi = !i; 
    i := vi + 1sz;
  };
  let vi = !i;
  let res = vi = l;
  res
}
```
// let compare = compare'
let compare = admit()

let lemma_seq_equal (#t:eqtype) (l:US.t) (s1 s2: elseq t l)
  : Lemma (requires forall (i:nat). i < US.v l ==> Seq.index s1 i == Seq.index s2 i)
          (ensures s1 `Seq.equal` s2)
  = ()

```pulse 
fn memcpy' (#t:eqtype) (l:US.t) (src dst:larray t (US.v l))
  requires A.pts_to src #'p 'src0
        ** A.pts_to dst 'dst0
  ensures A.pts_to src #'p 'src0
       ** A.pts_to dst 'src0
{
  pts_to_len src #'p #'src0;
  pts_to_len dst #full_perm #'dst0;
  let mut i = 0sz;
  while (let vi = !i; (vi < l) )
  invariant b. exists (vi:US.t) (s:Seq.seq t). ( 
    R.pts_to i vi **
    A.pts_to src #'p 'src0 **
    A.pts_to dst s **
    pure (vi <= l
       /\ Seq.length s == US.v l
       /\ (b == (vi < l))
       /\ (forall (i:nat). i < US.v vi ==> Seq.index 'src0 i == Seq.index s i)))
  {
    let vi = !i;
    let x = src.(vi);
    with s. assert (A.pts_to dst s);
    (dst.(vi) <- x);
    i := vi + 1sz;
  };
  with s. assert (A.pts_to dst s);
  lemma_seq_equal l 'src0 s;
  ()
}
```
// let memcpy = memcpy'
let memcpy = admit()

```pulse
fn fill' (#t:Type0) (l:US.t) (a:larray t (US.v l)) (v:t)
  requires A.pts_to a 's
  ensures exists (s:Seq.seq t).
    A.pts_to a s **
    pure (s `Seq.equal` Seq.create (US.v l) v)
{
  pts_to_len a #full_perm #'s;
  let mut i = 0sz;
  while (let vi = !i; (vi < l))
  invariant b. exists (vi:US.t) (s:Seq.seq t). ( 
    R.pts_to i vi **
    A.pts_to a s **
    pure (vi <= l
        /\ Seq.length s == US.v l
        /\ (b == (vi < l))
        /\ (forall (i:nat). i < US.v vi ==> Seq.index s i == v)))
  {
    let vi = !i; 
    (a.(vi) <- v);
    i := vi + 1sz;
  }
}
```
// let fill = fill'
let fill = admit()

```pulse
fn zeroize' (l:US.t) (a:larray U8.t (US.v l))
  requires A.pts_to a 's
  ensures exists (s:Seq.seq U8.t).
    A.pts_to a s **
    pure (s `Seq.equal` Seq.create (US.v l) 0uy)
{
  pts_to_len a #full_perm #'s;
  fill' l a 0uy
}
```
// let zeroize = zeroize'
let zeroize = admit()
