module Steel.Reference

open Steel.Actions
open Steel.SteelAtomic.Basics
module Sem = Steel.Semantics.Hoare.MST

#push-options "--fuel 0 --ifuel 1"
let alloc (#a:Type) (x:a)
  : SteelT (ref a) emp (fun r -> pts_to r full x)
  = Steel?.reflect (fun _ ->
      let m0 = mst_get () in
      let act = alloc_ref x trivial_preorder in
      let (| x, m1 |) = act m0 in
      act_preserves_frame_and_preorder act m0;
      mst_put m1;
      x)

let read_core (#a:Type) (#uses:Set.set lock_addr) (#p:perm) (r:ref a)
  : SteelAtomic a uses false (ref_perm r p) (fun x -> pts_to r p x)
  = SteelAtomic?.reflect (fun _ ->
      let m0 = mst_get () in
      let act = get_ref uses r p in
      let (| x, m1 |) = act m0 in
      atomic_preserves_frame_and_preorder act m0;
      mst_put m1;
      x)


let read_atomic (#a:Type) (#uses:Set.set lock_addr) (#p:perm) (#v:erased a) (r:ref a)
  : SteelAtomic a uses false (pts_to r p v) (fun x -> pts_to r p x)
  = change_hprop (pts_to r p v) (ref_perm r p) (fun m -> intro_exists v (pts_to_ref r p) m);
    read_core r

let read (#a:Type) (#p:perm) (#v:erased a) (r:ref a)
  : SteelT a (pts_to r p v) (fun x -> pts_to r p x)
  = lift_atomic_to_steelT (fun _ -> read_atomic r)

let read_refine_core_atomic (#a:Type) (#uses:Set.set lock_addr) (#p:perm) (q:a -> hprop) (r:ref a)
  : SteelAtomic a uses false
    (h_exists (fun (v:a) -> pts_to_ref r p v `star` q v))
    (fun x -> pts_to_ref r p x `star` q x)
  = SteelAtomic?.reflect (fun _ ->
      let m0 = mst_get () in
      let act = get_ref_refine uses r p q in
      let (| x, m1 |) = act m0 in
      atomic_preserves_frame_and_preorder act m0;
      mst_put m1;
      x)

let read_refine_atomic (#a:Type) (#uses:Set.set lock_addr) (#p:perm) (q:a -> hprop) (r:ref a)
  : SteelAtomic a uses false
    (h_exists (fun (v:a) -> pts_to r p v `star` q v))
    (fun x -> pts_to r p x `star` q x)
  = change_hprop
      (h_exists (fun (v:a) -> pts_to r p v `star` q v))
      (h_exists (fun (v:a) -> pts_to_ref r p v `star` q v))
      // TODO: h_exists extensionality lemma in Memory
      (fun m -> admit() );
    let x = read_refine_core_atomic q r in
    change_hprop (pts_to_ref r p x `star` q x) (pts_to r p x `star` q x) (fun m -> ());
    return_atomic x

let read_refine (#a:Type) (#p:perm) (q:a -> hprop) (r:ref a)
  : SteelT a (h_exists (fun (v:a) -> pts_to r p v `star` q v))
             (fun v -> pts_to r p v `star` q v)
  = lift_atomic_to_steelT (fun _ -> read_refine_atomic q r)

let write_atomic (#a:Type) (#uses:Set.set lock_addr) (#v:erased a) (r:ref a) (x:a)
  : SteelAtomic unit uses false (pts_to r full v) (fun _ -> pts_to r full x)
  = SteelAtomic?.reflect (fun _ ->
      let m0 = mst_get () in
      let act = set_ref uses r v x in
      let (| x, m1 |) = act m0 in
      atomic_preserves_frame_and_preorder act m0;
      mst_put m1;
      x)

let write (#a:Type) (#v:erased a) (r:ref a) (x:a)
  : SteelT unit (pts_to r full v) (fun _ -> pts_to r full x)
  = lift_atomic_to_steelT (fun _ -> write_atomic r x)

let free_core (#a:Type) (r:ref a)
  : SteelT unit (ref_perm r full) (fun _ -> emp)
  = Steel?.reflect (fun _ ->
      let m0 = mst_get () in
      let act = free_ref r in
      let (| x, m1 |) = act m0 in
      act_preserves_frame_and_preorder act m0;
      mst_put m1;
      x)

let free (#a:Type) (#v:erased a) (r:ref a)
  : SteelT unit (pts_to r full v) (fun _ -> emp)
  = lift_atomic_to_steelT (fun _ -> change_hprop (pts_to r full v) (ref_perm r full) (fun m -> intro_exists v (pts_to_ref r full) m));
    free_core r

let share_atomic (#a:Type) (#uses:Set.set lock_addr) (#p:perm) (#v:erased a) (r:ref a)
  : SteelAtomic unit
    uses
    true
    (pts_to r p v)
    (fun _ -> pts_to r (half_perm p) v `star` pts_to r (half_perm p) v)
  = change_hprop
      (pts_to r p v)
      (pts_to r (half_perm p) v `star` pts_to r (half_perm p) v)
      // TODO: Needs a lemma here. And to unify with Steel.Actions which returns a new ref
      (fun m -> admit())

let share (#a:Type) (#p:perm) (#v:erased a) (r:ref a)
  : SteelT unit
    (pts_to r p v)
    (fun _ -> pts_to r (half_perm p) v `star` pts_to r (half_perm p) v)
  = lift_atomic_to_steelT (fun _ -> share_atomic r)

let gather_atomic
  (#a:Type) (#uses:Set.set lock_addr)
  (#p0:perm) (#p1:perm) (#v0 #v1:erased a) (r:ref a)
  : SteelAtomic unit
    uses
    true
    (pts_to r p0 v0 `star` pts_to r p1 v1)
    (fun _ -> pts_to r (sum_perm p0 p1) v0)
  = change_hprop
      (pts_to r p0 v0 `star` pts_to r p1 v1)
      (pts_to r (sum_perm p0 p1) v0)
      // TODO: Needs a lemma here. And to unify with Steel.Actions
      (fun m -> admit())

let gather (#a:Type) (#p0:perm) (#p1:perm) (#v0 #v1:erased a) (r:ref a)
  : SteelT unit
    (pts_to r p0 v0 `star` pts_to r p1 v1)
    (fun _ -> pts_to r (sum_perm p0 p1) v0)
  = lift_atomic_to_steelT (fun _ -> gather_atomic r)

let ghost_read (#a:Type) (#uses:Set.set lock_addr) (#p:perm) (#v:Ghost.erased a) (r:ref a)
  : SteelAtomic a uses true
    (pts_to r p v)
    (fun x -> pts_to r p x)
  = SteelAtomic?.reflect (fun _ ->
      let m0 = mst_get () in
      // TODO: Needs to expose such an action. The ref should probably be to Ghost.erased a
      admit())

let ghost_read_refine (#a:Type) (#uses:Set.set lock_addr) (#p:perm) (r:ref a)
  (q:a -> hprop)
  : SteelAtomic a uses true
    (h_exists (fun (v:a) -> pts_to r p v `star` q v))
    (fun v -> pts_to r p v `star` q v)
  = SteelAtomic?.reflect (fun _ ->
      let m0 = mst_get () in
      // TODO: Needs to expose such an action. The ref should probably be to Ghost.erased a
      admit())

let cas
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
    (pts_to r full_perm v)
    (fun b -> if b then pts_to r full_perm v_new else pts_to r full_perm v)
  = SteelAtomic?.reflect (fun _ ->
      let m0 = mst_get () in
      let act = cas uses r v v_old v_new in
      let (| x, m1 |) = act m0 in
      atomic_preserves_frame_and_preorder act m0;
      mst_put m1;
      x)

let alloc_monotonic_ref = admit()
let read_monotonic_ref = admit()
let write_monotonic_ref = admit()
let pure (p:prop) : hprop = admit()
let witnessed  = admit()
let witness = admit()
let recall = admit()
