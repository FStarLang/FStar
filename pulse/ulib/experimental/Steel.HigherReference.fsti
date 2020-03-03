module Steel.HigherReference
open Steel.Effect
open Steel.Effect.Atomic
open Steel.Memory
open FStar.Ghost

let perm = p:perm{readable p}
let full : perm = full_perm
let trivial_preorder #a : Preorder.preorder a = fun _ _ -> True
let ref (a:Type u#1) = reference a trivial_preorder
let is_ref (#a:Type u#1) (r:ref a) (p:perm) = ref_perm r p
let pts_to (#a:Type u#1) (r:ref a) (p:perm) (v:erased a) : hprop = pts_to_ref r p v

val alloc (#a:Type) (x:a)
  : SteelT (ref a) emp (fun r -> pts_to r full x)

val read (#a:Type) (#p:perm) (#v:erased a) (r:ref a)
  : SteelT a (pts_to r p v) (fun x -> pts_to r p x)

val read_refine (#a:Type) (#p:perm) (q:a -> hprop) (r:ref a)
  : SteelT a (h_exists (fun (v:a) -> pts_to r p v `star` q v))
             (fun v -> pts_to r p v `star` q v)

val write (#a:Type) (#v:erased a) (r:ref a) (x:a)
  : SteelT unit (pts_to r full v) (fun _ -> pts_to r full x)

val free (#a:Type) (#v:erased a) (r:ref a)
  : SteelT unit (pts_to r full v) (fun _ -> emp)

val share (#a:Type) (#p:perm) (#v:erased a) (r:ref a)
  : SteelT unit
    (pts_to r p v)
    (fun _ -> pts_to r (half_perm p) v `star` pts_to r (half_perm p) v)

val gather (#a:Type) (#p0:perm) (#p1:perm) (#v0 #v1:erased a) (r:ref a)
  : SteelT unit
    (pts_to r p0 v0 `star` pts_to r p1 v1)
    (fun _ -> pts_to r (sum_perm p0 p1) v0)

val ghost_read (#a:Type) (#uses:Set.set lock_addr) (#p:perm) (#v:Ghost.erased a) (r:ref a)
  : SteelAtomic a uses true
    (pts_to r p v)
    (fun x -> pts_to r p x)

val ghost_read_refine (#a:Type) (#uses:Set.set lock_addr) (#p:perm) (r:ref a)
  (q:a -> hprop)
  : SteelAtomic a uses true
    (h_exists (fun (v:a) -> pts_to r p v `star` q v))
    (fun v -> pts_to r p v `star` q v)

////////////////////////////////////////////////////////////////////////////////

val alloc_monotonic_ref (#a:Type) (p:Preorder.preorder a) (v:a)
  : SteelT (reference a p) emp (fun r -> pts_to_ref r full v)

val read_monotonic_ref (#a:Type) (#q:perm) (#p:Preorder.preorder a) (#frame:a -> hprop)
                       (r:reference a p)
  : SteelT a (h_exists (fun (v:a) -> pts_to_ref r q v `star` frame v))
             (fun v -> pts_to_ref r q v `star` frame v)

val write_monotonic_ref (#a:Type) (#p:Preorder.preorder a) (#v:erased a)
                       (r:reference a p) (x:a{p v x})
  : SteelT unit (pts_to_ref r full v)
                (fun v -> pts_to_ref r full x)

val pure (p:prop) : hprop

let property (a:Type) = a -> prop

val witnessed (#a:Type u#1) (#p:Preorder.preorder a) (r:reference a p)
              (fact:property a) : prop

let stable_property (#a:Type) (p:Preorder.preorder a) = fact:property a { Preorder.stable fact p }

val witness (#a:Type) (#q:perm) (#p:Preorder.preorder a) (r:reference a p)
            (fact:stable_property p)
            (v:(Ghost.erased a))
            (_:squash (fact v))
  : SteelT unit (pts_to_ref r q v)
                (fun _ -> pts_to_ref r q v `star` pure (witnessed r fact))

val recall (#a:Type u#1) (#q:perm) (#p:Preorder.preorder a) (#fact:property a)
           (r:reference a p) (v:(Ghost.erased a))
  : SteelT unit (pts_to_ref r q v `star` pure (witnessed r fact))
                (fun _ -> pts_to_ref r q v `star` pure (fact v))
