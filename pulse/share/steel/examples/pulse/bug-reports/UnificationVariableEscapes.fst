module UnificationVariableEscapes
module PM = Pulse.Main
open Steel.ST.Util 
open Steel.ST.Array
open Steel.FractionalPermission
open FStar.Ghost
module U32 = FStar.UInt32
open Pulse.Steel.Wrapper
module A = Steel.ST.Array
module US = FStar.SizeT
module R = Steel.ST.Reference

//This fails almost silently with just a 
// proof-state: State dump @ depth 0 (at the time of failure):
// Location: UnificationVariableEscapes.fst(13,8-13,8)
// 1 error was reported (see above)
//What's happening is that there is an escaped unification variable in the invariant
//and F* fails to check it, and no error is reported properly
//If you run it with --debug UnificationVariableEscapes --debug_level refl_tc_callbacks
//you see this:
//Calling instantiate_implicits on Prims.l_and (Prims.l_and (Prims.l_and (Prims.eq2 (FStar.Ghost.hide (FStar.SizeT.op_Less_Hat (FStar.SizeT.__uint_to_t
//                         0)
//                       l))
//               (FStar.SizeT.op_Less_Hat (FStar.Ghost.hide (FStar.SizeT.__uint_to_t 0)) l))
//           (Prims.op_LessThanOrEqual (FStar.SizeT.v (FStar.Ghost.hide (FStar.SizeT.__uint_to_t 0)))
//               (FStar.SizeT.v l)))
//       (Prims.eq2 (FStar.Seq.Base.length (FStar.Ghost.hide (FStar.Ghost.reveal s)))
//           (Steel.ST.Array.length a)))
//   (Prims.l_Forall (fun i ->
//           Prims.l_imp (Prims.op_LessThan i (FStar.SizeT.v __pulse_embedded_uvar__.vi))
//             (Prims.eq2 (FStar.Seq.Base.index __pulse_embedded_uvar__.s i) v)))
// And you see the embedded uvars for s and vi remain in there
//Also strange, if I put the [expect_failure] on it, that actually fails, saying the definition succeeded
//so something is going wrong there too with the way the error is being reported
// [@@expect_failure]
// ```pulse
// fn fill_array (#t:Type0) (a:A.array t) (l:(l:US.t { US.v l == A.length a })) (v:t)
//               (#s:(s:Ghost.erased (Seq.seq t) { Seq.length s == A.length a }))
//    requires (A.pts_to a full_perm s)
//    ensures 
//       exists (s:Seq.seq t). (
//          A.pts_to a full_perm s `star`
//          pure (s `Seq.equal` Seq.create (US.v l) v)
//       )
// {
//    let mut i = 0sz;
//    while (let vi = !i; US.(vi <^ l))
//    invariant b. exists (s:Seq.seq t) (vi:US.t). ( 
//       A.pts_to a full_perm s `star`
//       R.pts_to i full_perm vi `star`
//       pure ((b == US.(vi <^ l)) /\
//             US.v vi <= US.v l /\
//             Seq.length s == A.length a /\
//             (forall (i:nat). i < US.v vi ==> Seq.index s i == v))
//    )
//    {
//       let vi = !i; 
//       (a.(vi) <- v);
//       i := US.(vi +^ 1sz);
//       ()
//    };
//    ()
// }
// ```

//Writing it this way and hoising the forall out of the invariant works
let seq_constant_until (#t:Type) (s:Seq.seq t) (v:t) (n:nat) =
    forall (i:nat). i < n /\ i < Seq.length s ==> Seq.index s i == v

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
            seq_constant_until s v (US.v vi))
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