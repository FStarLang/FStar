module UnificationVariableEscapes
open Pulse.Lib.Pervasives
module U32 = FStar.UInt32
module A = Pulse.Lib.Array
module US = FStar.SizeT
module R = Pulse.Lib.Reference

```pulse
fn fill_array (#t:Type0) (a:A.array t) (l:(l:US.t { US.v l == A.length a })) (v:t)
              (#s:(s:Ghost.erased (Seq.seq t) { Seq.length s == A.length a }))
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