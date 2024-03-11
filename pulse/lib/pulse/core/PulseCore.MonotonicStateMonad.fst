module PulseCore.MonotonicStateMonad
open FStar.Preorder
module PST = PulseCore.PreorderStateMonad
let mst (#s:Type u#s)
         (rel:FStar.Preorder.preorder s)
         (a:Type u#a)
         (pre:s -> prop)
         (post:s -> a -> s -> prop)
  = PST.pst a rel pre post

let lift_pst
    (#s:Type u#s)
    (#rel:FStar.Preorder.preorder s)
    (#a:Type u#a)
    (#pre:s -> prop)
    (#post:s -> a -> s -> prop)
    (pst:PST.pst a rel pre post)
: mst rel a pre post
= pst

let return = PST.return
let bind = PST.bind
let weaken = PST.weaken
let get = PST.get
let put = PST.put

let witness p = admit()
let recall p w = admit()
let with_get #s #a #rel #req_f #ens_f f = fun m0 -> f m0 m0