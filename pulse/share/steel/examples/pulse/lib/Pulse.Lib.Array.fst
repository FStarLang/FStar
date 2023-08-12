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
let coerce (#t:Type) (l:US.t) (s:Ghost.erased (elseq t l)) : Ghost.erased (Seq.seq t)
  = let s_ = reveal s in 
    hide s_

```pulse
fn compare_ (#t:eqtype) (l:US.t) (a1 a2:larray t (US.v l))
           (#p1 #p2:perm) (#s1 #s2:Ghost.erased (elseq t l))
  requires (
    A.pts_to a1 #p1 s1 **
    A.pts_to a2 #p2 s2
  )
  returns res:bool
  ensures (
    A.pts_to a1 #p1 s1 **
    A.pts_to a2 #p2 s2 **
    (pure (res <==> Seq.equal s1 s2))
  )
{
  let mut i = 0sz;
  while (let vi = !i; 
    if (vi < l) { 
      let v1 = op_Array_Access a1 vi #p1 #(coerce l s1); 
      let v2 = op_Array_Access a2 vi #p2 #(coerce l s2); 
      (v1 = v2) } 
    else { false } )
  invariant b. exists (vi:US.t). ( 
    R.pts_to i vi **
    A.pts_to a1 #p1 s1 **
    A.pts_to a2 #p2 s2 **
    pure (
      vi <= l /\
      (b == (vi < l && Seq.index s1 (US.v vi) = Seq.index s2 (US.v vi))) /\
      (forall (i:nat). i < US.v vi ==> Seq.index s1 i == Seq.index s2 i)
    )
  )
  {
    let vi = !i; 
    i := vi + 1sz;
    ()
  };
  let vi = !i;
  let res = vi = l;
  res
}
```

let compare = compare_
let lemma_seq_equal (#t:eqtype) (l:US.t) (s1 s2: elseq t l)
  : Lemma (requires forall (i:nat). i < US.v l ==> Seq.index s1 i == Seq.index s2 i)
          (ensures s1 `Seq.equal` s2)
  = ()

```pulse 
fn memcpy_ (#t:eqtype) (l:US.t) (src dst:larray t (US.v l))
          (#p:perm) (#src0 #dst0:Ghost.erased (elseq t l))
  requires (
    A.pts_to src #p src0 **
    A.pts_to dst dst0
  )
  ensures (
    A.pts_to src #p src0 **
    A.pts_to dst src0
  )
{
  let mut i = 0sz;
  while (let vi = !i; (vi < l) )
  invariant b. exists (vi:US.t) (s:elseq t l). ( 
    R.pts_to i vi **
    A.pts_to src #p src0 **
    A.pts_to dst s **
    pure (
      vi <= l /\
      (b == (vi < l)) /\
      (forall (i:nat). i < US.v vi ==> Seq.index src0 i == Seq.index s i)
    )
  )
  {
    let vi = !i;
    let x = op_Array_Access src vi #p #(coerce l src0);
    with s. assert (A.pts_to dst s);
    op_Array_Assignment dst vi x #(coerce l s);
    i := vi + 1sz;
    ()
  };
  with s. assert (A.pts_to dst s);
  lemma_seq_equal l src0 s;
  ()
}
```

let memcpy = memcpy_

```pulse
fn fill_ (#t:Type0) (l:US.t) (a:(a:array t{ US.v l == A.length a })) (v:t)
               (#s:Ghost.erased (elseq t l))
  requires (A.pts_to a s)
  ensures exists (s:Seq.seq t). (
    A.pts_to a s **
    pure (s `Seq.equal` Seq.create (US.v l) v)
  )
{
   let mut i = 0sz;
   while (let vi = !i; (vi < l))
   invariant b. exists (s:Seq.seq t) (vi:US.t). ( 
      A.pts_to a s **
      R.pts_to i vi **
      pure ((b == (vi < l)) /\
            vi <= l /\
            Seq.length s == A.length a /\
            (forall (i:nat). i < US.v vi ==> Seq.index s i == v))
   )
   {
      let vi = !i; 
      (a.(vi) <- v);
      i := vi + 1sz;
      ()
   };
   ()
}
```
let fill = fill_

```pulse
fn zeroize_ (l:US.t) (a:(a:A.array U8.t{ US.v l == A.length a }))
                 (#s:Ghost.erased (elseq U8.t l))
  requires A.pts_to a s
  ensures exists (s:Seq.seq U8.t). (
    A.pts_to a s **
    pure (s `Seq.equal` Seq.create (US.v l) 0uy)
  )
{
  fill l a 0uy
}
```
let zeroize = zeroize_
