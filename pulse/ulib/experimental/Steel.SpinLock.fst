module Steel.SpinLock
open Steel.Effect
//open Steel.Effect.Atomic
open Steel.Permissions
open Steel.Reference
open Steel.Actions

let available = false
let locked = true

let lockinv (p:hprop) (r:ref bool) : hprop =
  h_or (pts_to r full_permission available `star` p) (pts_to r full_permission locked)

let lock (p:hprop) = (r:ref bool) & inv (lockinv p r)

assume
val new_inv (p:hprop) : SteelT (inv p) p (fun _ -> emp)

assume
val h_admit (#a:_) (p:hprop) (q:a -> hprop)
  : SteelT a p q

assume
val h_assert (p:hprop)
  : SteelT unit p (fun _ -> p)

assume
val intro_h_or_left (p:hprop) (q:hprop)
  : SteelT unit p (fun _ -> h_or p q)

val intro_lockinv_left (p:hprop) (r:ref bool)
  : SteelT unit (pts_to r full_permission available `star` p) (fun _ -> lockinv p r)

let intro_lockinv_left p r =
  intro_h_or_left (pts_to r full_permission available `star` p) (pts_to r full_permission locked)

let new_lock (p:hprop)
  : SteelT (lock p) p (fun _ -> emp) =
  let r:ref bool =
    steel_frame_t (fun _ -> alloc available) in
  intro_lockinv_left p r;
  let i:inv (lockinv p r) = new_inv (lockinv p r) in
  let l:lock p = (| r, i |) in
  l
