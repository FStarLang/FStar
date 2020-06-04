module Steel.PCM.MonotonicHigherReference
open FStar.PCM
open Steel.PCM.Effect
open Steel.PCM.Effect.Atomic
open Steel.PCM.Memory
open Steel.PCM.FractionalPermission
open FStar.Ghost
module Preorder = FStar.Preorder

val ref (a:Type u#1) (p:Preorder.preorder a)
  : Type u#0

val pts_to (#a:Type) (#p:Preorder.preorder a) (r:ref a p) (f:perm) (v:Ghost.erased a)
  : slprop u#1

val alloc (#a:Type) (p:Preorder.preorder a) (v:a)
  : SteelT (ref a p) emp (fun r -> pts_to r full_perm v)

val read_refine (#a:Type) (#q:perm) (#p:Preorder.preorder a) (#frame:a -> slprop)
                (r:ref a p)
  : SteelT a (h_exists (fun (v:a) -> pts_to r q v `star` frame v))
             (fun v -> pts_to r q v `star` frame v)

val write (#a:Type) (#p:Preorder.preorder a) (#v:erased a)
          (r:ref a p) (x:a{p v x})
  : SteelT unit (pts_to r full_perm v)
                (fun v -> pts_to r full_perm x)

let property (a:Type)
  = a -> prop

val witnessed (#a:Type u#1) (#p:Preorder.preorder a) (r:ref a p) (fact:property a)
  : prop

let stable_property (#a:Type) (p:Preorder.preorder a)
  = fact:property a { Preorder.stable fact p }

val witness (#a:Type) (#q:perm) (#p:Preorder.preorder a) (r:ref a p)
            (fact:stable_property p)
            (v:Ghost.erased a)
            (_:squash (fact v))
  : SteelT unit (pts_to r q v)
                (fun _ -> pts_to r q v `star` pure (witnessed r fact))

val recall (#a:Type u#1) (#q:perm) (#p:Preorder.preorder a) (#fact:property a)
           (r:ref a p) (v:(Ghost.erased a))
  : SteelT unit (pts_to r q v `star` pure (witnessed r fact))
                (fun _ -> pts_to r q v `star` pure (fact v))
