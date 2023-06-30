module Array
module A = Steel.ST.Array
module R = Steel.ST.Reference
module PM = Pulse.Main
open Steel.ST.Array
open Steel.FractionalPermission
open Steel.ST.Util
open FStar.Ghost
open Pulse.Steel.Wrapper
module US = FStar.SizeT
module U8 = FStar.UInt8

let elseq (a:Type) (l:nat) = s:Ghost.erased (Seq.seq a) { Seq.length s == l }

```pulse
fn compare (#t:eqtype) (l:US.t) (a1 a2:A.larray t (US.v l))
           (#p1 #p2:perm) (#s1 #s2:elseq t (US.v l))
  requires (
    A.pts_to a1 p1 s1 `star`
    A.pts_to a2 p2 s2
  )
  returns res:bool
  ensures (
    A.pts_to a1 p1 s1 `star`
    A.pts_to a2 p2 s2 `star`
    (pure (res <==> Seq.equal s1 s2))
  )
{
  let mut i = 0sz;
  while (let vi = !i; if US.(vi <^ l) { let v1 = a1.(vi); let v2 = a2.(vi); (v1 = v2) } else { false } )
  invariant b. exists (vi:US.t). ( 
    R.pts_to i full_perm vi `star`
    A.pts_to a1 p1 s1 `star`
    A.pts_to a2 p2 s2 `star`
    pure (
      US.v vi <= US.v l /\
      (b == (US.(vi <^ l) && Seq.index s1 (US.v vi) = Seq.index s2 (US.v vi))) /\
      (forall (i:nat). i < US.v vi ==> Seq.index s1 i == Seq.index s2 i)
    )
  )
  {
    let vi = !i; 
    i := US.(vi +^ 1sz);
    ()
  };
  let vi = !i;
  let res = vi = l;
  res
}
```

```pulse
fn fill_array (#t:Type0) (l:US.t) (a:(a:A.array t{ US.v l == A.length a })) (v:t)
              (#s:(s:Ghost.erased (Seq.seq t) { Seq.length s == US.v l }))
   requires (A.pts_to a full_perm s)
   ensures 
      exists (s:Seq.seq t). (
         A.pts_to a full_perm s `star`
         pure (s `Seq.equal` Seq.create (US.v l) v)
      )
{
   let mut i = 0sz;
   while (let vi = !i; US.(vi <^ l))
   invariant b. exists (s:Seq.seq t) (vi:US.t). ( 
      A.pts_to a full_perm s `star`
      R.pts_to i full_perm vi `star`
      pure ((b == US.(vi <^ l)) /\
            US.v vi <= US.v l /\
            Seq.length s == A.length a /\
            (forall (i:nat). i < US.v vi ==> Seq.index s i == v))
   )
   {
      let vi = !i; 
      (a.(vi) <- v);
      i := US.(vi +^ 1sz);
      ()
   };
   ()
}
```