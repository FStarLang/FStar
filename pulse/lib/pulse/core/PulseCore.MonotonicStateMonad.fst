module PulseCore.MonotonicStateMonad
open FStar.Preorder
module PST = PulseCore.PreorderStateMonad
module M = FStar.MSTTotal
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

assume (* to interoperate with a definition of a similar module in FStar.MSTTotal *)
val reify_ (#s:Type u#2) (#rel:FStar.Preorder.preorder s)
           (#a:Type u#a) (#pre:s -> prop) (#post:s -> a -> s -> prop)
           ($f:unit -> M.MSTATETOT a s rel pre post)
: M.repr a s rel pre post

let of_msttotal (#s:Type u#2) (rel:FStar.Preorder.preorder s)
                (a:Type u#a) (pre:s -> prop) (post:s -> a -> s -> prop)
                (f:unit -> M.MSTATETOT a s rel pre post)
: mst rel a pre post
= let f = reify_ f in
  fun s -> f s

let to_msttotal (#s:Type u#2) (rel:FStar.Preorder.preorder s)
                (a:Type u#a) (pre:s -> prop) (post:s -> a -> s -> prop)
                (f:mst rel a pre post)
: M.MSTATETOT a s rel pre post
= M.MSTATETOT?.reflect (fun s -> f s)

let return = PST.return
let bind = PST.bind
let weaken = PST.weaken
let get = PST.get
let put = PST.put

let witnessed p
= unit

let witness p
= fun s -> (), s

let recall p w
= fun s ->
    assume (p s);
    (), s