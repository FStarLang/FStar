module IncrPair
open Steel.Memory
open Steel.Effect
open Steel.Reference
open Steel.FractionalPermission
open Steel.Effect.Atomic
open FStar.Ghost
assume
val pts_to (#a:Type u#0)
           (r:ref a)
           ([@@@ smt_fallback] v:a)
  : slprop u#1

assume
val read (#a:Type) (#v:Ghost.erased a) (r:ref a)
  : Steel a (pts_to r v) (fun x -> pts_to r x)
            (requires fun _ -> True)
            (ensures fun _ x _ -> x == Ghost.reveal v)

assume
val write (#a:Type0) (#v:Ghost.erased a) (r:ref a) (x:a)
  : SteelT unit (pts_to r v)
                (fun _ -> pts_to r x)

//
let incr (#v:Ghost.erased int) (r:ref int) ()
  : SteelT unit (pts_to r v)
                (fun _ -> pts_to r (v + 1))
  = let x = read r in
    write #_ #(Ghost.hide x) r (x + 1);
    change_slprop (pts_to r (x + 1)) (pts_to r (v + 1)) (fun _ -> ())

//SNIPPET_START: par_incr
let par_incr (#v0 #v1:erased int) (r0 r1:ref int)
  : SteelT _ (pts_to r0 v0 `star` pts_to r1 v1)
             (fun _ -> pts_to r0 (v0 + 1) `star` pts_to r1 (v1 + 1))
  = par (incr r0) (incr r1)
//SNIPPET_END: par_incr
