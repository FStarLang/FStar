module Pulse.MonotonicStateMonad
open FStar.Preorder

#push-options "--print_universes"

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