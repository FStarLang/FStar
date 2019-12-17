module Steel.Memory.RST

open Steel.Memory
open Steel.Actions
open Steel.Memory.Tactics
open LowStar.Permissions

new_effect GST = STATE_h mem

let gst_pre = st_pre_h mem
let gst_post' (a:Type) (pre:Type) = st_post_h' mem a pre
let gst_post (a:Type) = st_post_h mem a
let gst_wp (a:Type) = st_wp_h mem a

unfold let lift_div_gst (a:Type) (wp:pure_wp a) (p:gst_post a) (h:mem) = wp (fun a -> p a h)
sub_effect DIV ~> GST = lift_div_gst

effect ST (a:Type) (pre:gst_pre) (post: (m0:mem -> Tot (gst_post' a (pre m0)))) =
  GST a
    (fun (p:gst_post a) (h:mem) -> pre h /\ (forall a h1. (pre h /\ post h a h1) ==> p a h1))

effect Steel
  (a: Type)
  (res0: hprop)
  (res1: a -> hprop)
  (pre: mem -> prop)
  (post: mem -> a -> mem -> prop)
= ST
  a
  (fun h0 ->
    interp res0 (heap_of_mem h0) /\
    pre h0)
  (fun h0 x h1 ->
    interp res0 (heap_of_mem h0) /\
    pre h0 /\
    interp (res1 x) (heap_of_mem h1) /\
    post h0 x h1
  )

assume val get (r:hprop)
  :Steel (hmem r) (r) (fun _ -> r)
             (requires (fun m -> True))
             (ensures (fun m0 x m1 -> m0 == x /\ m1 == m0))

assume val put (r_init r_out:hprop) (m:hmem r_out)
  :Steel unit (r_init) (fun _ -> r_out)
             (requires fun m -> True)
             (ensures (fun _ _ m1 -> m1 == m))

let interp_perm_to_ptr (#a:Type) (p:permission) (r:ref a) (h:heap)
  : Lemma (requires interp (ptr_perm r p) h)
          (ensures interp (ptr r) h)
  = let lem (v:a) (h:heap) : Lemma
   (requires interp (pts_to r p v) h)
   (ensures interp (ptr r) h)
   = intro_exists v (pts_to r p) h;
     intro_exists p (ptr_perm r) h
   in Classical.forall_intro (Classical.move_requires (fun v -> lem v h));
   elim_exists (pts_to r p) (ptr r) h

let interp_pts_to_perm (#a:Type) (p:permission) (r:ref a) (v:a) (h:heap)
  : Lemma (requires interp (pts_to r p v) h)
          (ensures interp (ptr_perm r p) h)
  = let lem (v:a) (h:heap) : Lemma
     (requires interp (pts_to r p v) h)
     (ensures interp (ptr_perm r p) h)
     = intro_exists v (pts_to r p) h
     in Classical.forall_intro (Classical.move_requires (fun v -> lem v h))

let pts_to_sel (#a:Type) (p:permission) (r:ref a) (v:a) (h:heap)
  : Lemma (requires interp (pts_to r p v) h)
          (ensures interp (ptr r) h /\ sel r h == v)
  = interp_pts_to_perm p r v h; interp_perm_to_ptr p r h;
    sel_lemma r p h;
    pts_to_injective r p v (sel r h) h

val perm_to_ptr (#a:Type) (p:permission) (r:ref a) : Steel unit
  (ptr_perm r p)
  (fun _ -> ptr r)
  (fun _ -> True)
  (fun h0 _ h1 -> h0 == h1)

let perm_to_ptr #a p r =
 let h = get (ptr_perm r p) in
 interp_perm_to_ptr p r (heap_of_mem h)

val pts_to_perm (#a:Type) (p:permission) (r:ref a) (v:a) : Steel unit
  (pts_to r p v)
  (fun _ -> ptr_perm r p)
  (fun _ -> True)
  (fun h0 _ h1 -> interp (ptr r) (heap_of_mem h1) /\ h0 == h1 /\ sel r (heap_of_mem h1) == v)

let pts_to_perm  #a p r v =
 let h = get (pts_to r p v) in
 interp_pts_to_perm p r v (heap_of_mem h);
 interp_perm_to_ptr p r (heap_of_mem h);
 pts_to_sel p r v (heap_of_mem h)

val ptr_read (#a:Type) (r:ref a) : Steel a
  (ptr_perm r full_permission)
  (fun v -> pts_to r full_permission v)
  (fun _ -> True)
  (fun _ _ _ -> True)

let ptr_read #a r =
 perm_to_ptr full_permission r;
 let h = get (ptr r) in
 let v = sel r (heap_of_mem h) in
 sel_lemma r full_permission (heap_of_mem h);
 v

val ptr_update (#a:Type) (r:ref a) (v:a) : Steel unit
  (ptr_perm r full_permission)
  (fun _ -> pts_to r full_permission v)
  (fun _ -> True)
  (fun _ _ _ -> True)

let ptr_update #a r v =
  perm_to_ptr #a full_permission r;
  let h = get (ptr_perm r full_permission) in
  let (| _, h' |) = upd r v h in
  put (ptr_perm r full_permission) (pts_to r full_permission v) h'

let fptr (#a:Type) (r:ref a) : hprop = ptr_perm r full_permission

let fsel (#a:Type) (r:ref a) (h:hheap (fptr r)) : a =
  interp_perm_to_ptr full_permission r h;
  sel r h

val fread (#a:Type) (r:ref a) : Steel a
  (fptr r) (fun _ -> fptr r)
  (requires fun _ -> True)
  // TODO: Why is this assume needed?
  (ensures fun _ v m1 -> assume (interp (fptr r) (heap_of_mem m1)); fsel r (heap_of_mem m1) == v)

let fread #a r =
  let v = ptr_read #a r in
  pts_to_perm full_permission r v;
  v

val fupd (#a:Type) (r:ref a) (v:a) : Steel unit
  (fptr r) (fun _ -> fptr r)
  (requires fun _ -> True)
  // TODO: Why is this assume needed?
  (ensures fun _ _ m1 -> assume (interp (fptr r) (heap_of_mem m1)); fsel r (heap_of_mem m1) == v)

let fupd #a r v =
  ptr_update r v;
  pts_to_perm full_permission r v

assume
val frame
  (outer0:hprop)
  (#inner0:hprop)
  (#a:Type)
  (#inner1:a -> hprop)
  (#[resolve_frame()]
    delta:hprop{
      FStar.Tactics.with_tactic
      reprove_frame
      (can_be_split_into outer0 inner0 delta /\ True)})
  (#pre:mem -> prop)
  (#post:mem -> a -> mem -> prop)
  ($f:unit -> Steel a inner0 inner1 pre post)
  : Steel a outer0 (fun v -> inner1 v `star` delta) pre post

val test1 (#a:Type) (r1 r2:ref a) : Steel a
  (ptr_perm r1 full_permission `star` ptr_perm r2 full_permission)
  (fun v -> pts_to r1 full_permission v `star` ptr_perm r2 full_permission)
  (fun _ -> True)
  (fun _ _ _ -> True)

let test1 #a r1 r2 =
  frame (ptr_perm r1 full_permission `star` ptr_perm r2 full_permission)
//        #(ptr_perm r2 full_permission)
        (fun () -> ptr_read r1)

val test2 (#a:Type) (r1 r2:ref a) : Steel a
  (ptr_perm r1 full_permission `star` ptr_perm r2 full_permission)
  (fun v -> pts_to r2 full_permission v `star` ptr_perm r1 full_permission)
  (fun _ -> True)
  (fun _ v _ -> True)

let test2 #a r1 r2 =
  let v = frame (ptr_perm r1 full_permission `star` ptr_perm r2 full_permission)
        (fun () -> ptr_read r2) in
  v
