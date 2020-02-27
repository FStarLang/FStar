module Steel.Reference
open Steel.Effect
open Steel.Effect.Atomic
open Steel.Memory
open Steel.Permissions
open FStar.Ghost

let perm = p:permission{allows_read p}
let full : perm = full_permission
let trivial_preorder #a : Preorder.preorder a = fun _ _ -> True
let ref (a:Type0) = reference a trivial_preorder
let is_ref (#a:Type0) (r:ref a) (p:perm) = ref_perm r p
let pts_to (#a:Type0) (r:ref a) (p:perm) (v:erased a) : hprop = pts_to_ref r p v

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
    (fun _ -> pts_to r (half_permission p) v `star` pts_to r (half_permission p) v)

val gather (#a:Type) (#p0:perm) (#p1:perm{summable_permissions p0 p1}) (#v0 #v1:erased a) (r:ref a)
  : SteelT unit
    (pts_to r p0 v0 `star` pts_to r p1 v1)
    (fun _ -> pts_to r (sum_permissions p0 p1) v0)

val ghost_read (#a:Type) (#uses:Set.set lock_addr) (#p:perm) (#v:Ghost.erased a) (r:ref a)
  : SteelAtomic a uses true
    (pts_to r p v)
    (fun x -> pts_to r p x)

val ghost_read_refine (#a:Type) (#uses:Set.set lock_addr) (#p:perm) (r:ref a)
  (q:a -> hprop)
  : SteelAtomic a uses true
    (h_exists (fun (v:a) -> pts_to r p v `star` q v))
    (fun v -> pts_to r p v `star` q v)

val cas
  (#t:eqtype)
  (#uses:Set.set lock_addr)
  (r:ref t)
  (v:Ghost.erased t)
  (v_old:t)
  (v_new:t)
  : SteelAtomic
    (b:bool{b <==> (Ghost.reveal v == v_old)})
    uses
    false
    (pts_to r full_permission v)
    (fun b -> if b then pts_to r full_permission v_new else pts_to r full_permission v)
