module PulseCore.MonotonicStateMonad
open FStar.Preorder
module M = FStar.MSTTotal
let mst (#s:Type u#s)
         (rel:FStar.Preorder.preorder s)
         (a:Type u#a)
         (pre:s -> prop)
         (post:s -> a -> s -> prop)
  = s0:s { pre s0 }
    -> Tot (
        res:(a & s) {
            post s0 res._1 res._2 /\
            rel s0 res._2
        }
    )

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

let return x
= fun s0 -> x, s0

let bind f g
= fun s0 ->
    let x, s1 = f s0 in
    g x s1

let weaken f
= fun s -> f s

let get _
= fun s -> s, s

let put v
= fun _  -> (), v

let witnessed p
= unit

let witness p
= fun s -> (), s

let recall p w
= fun s -> assume (p s); (), s