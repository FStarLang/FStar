module Steel.ST.PCMReference

module C = Steel.ST.Coercions
module P = Steel.PCMReference

let read r v0 = C.coerce_steel (fun _ -> P.read r v0)

let write r v0 v1 = C.coerce_steel (fun _ -> P.write r v0 v1)

let alloc x = C.coerce_steel (fun _ -> P.alloc x)

let free r x = C.coerce_steel (fun _ -> P.free r x)

let split r v v0 v1 = C.coerce_ghost (fun _ -> P.split r v v0 v1)

let gather r v0 v1 = C.coerce_ghost (fun _ -> P.gather r v0 v1)

let witness' (#inames: _) (#a:Type) (#pcm:pcm a)
            (r:ref a pcm)
            (fact:stable_property pcm)
            (v:erased a)
            (_:fact_valid_compat fact v)
            ()
  : Steel.Effect.Atomic.SteelGhost unit inames (pts_to r v)
               (fun _ -> pts_to r v)
               (requires fun _ -> True)
               (ensures fun _ _ _ -> witnessed r fact)
= P.witness r fact v ()

let witness r fact v vc = C.coerce_ghost (witness' r fact v vc)

let recall fact r v = C.coerce_ghost (fun _ -> P.recall fact r v)

let select_refine r x f = C.coerce_steel (fun _ -> P.select_refine r x f)

let upd_gen r x y f = C.coerce_steel (fun _ -> P.upd_gen r x y f)

let atomic_read r v0 = C.coerce_atomic (fun _ -> P.atomic_read r v0)

let atomic_write r v0 v1 = C.coerce_atomic (fun _ -> P.atomic_write r v0 v1)
