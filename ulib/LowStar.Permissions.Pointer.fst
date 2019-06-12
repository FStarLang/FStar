module LowStar.Permissions.Pointer

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module Seq = FStar.Seq

open LowStar.Permissions.References
open LowStar.Resource
open LowStar.RST

open LowStar.Permissions
open FStar.Real

abstract let ptr_view (#a:Type) (perm: Ghost.erased permission) (ptr:pointer a) : view a =
  reveal_view ();
  let fp = Ghost.hide (loc_pointer ptr) in
  let inv h =
    let (v, perm_map) = HS.sel h ptr.ptr_v in
    HS.contains h ptr.ptr_v /\ Ghost.reveal perm >. 0.0R /\ HS.is_mm ptr.ptr_v /\ (frame_of_pointer ptr) == HS.root /\
    get_permission_from_pid (Ghost.reveal perm_map) (Ghost.reveal ptr.ptr_pid) = Ghost.reveal perm /\
    v == get_snapshot_from_pid (Ghost.reveal perm_map) (Ghost.reveal ptr.ptr_pid)
  in
  let sel h =
    let (_, perm_map) = HS.sel h ptr.ptr_v in
    let perm = get_permission_from_pid (Ghost.reveal perm_map) (Ghost.reveal ptr.ptr_pid) in
    let snapshot = get_snapshot_from_pid (Ghost.reveal perm_map) (Ghost.reveal ptr.ptr_pid) in
    snapshot
  in
  let view = {
    fp = fp;
    inv = inv;
    sel = sel
  } in
  assert(sel_reads_fp view.fp view.sel);
  assert(inv_reads_fp view.fp view.inv);
  view

let ptr_resource (#a:Type) (perm: Ghost.erased permission) (ptr:pointer a) =
  as_resource (ptr_view perm ptr)

inline_for_extraction noextract let ptr_read
  (#a: Type)
  (#perm: Ghost.erased permission)
  (ptr: pointer a)
  : RST a
    (ptr_resource perm ptr)
    (fun _ -> ptr_resource perm ptr)
    (fun _ -> allows_read perm)
    (fun h0 x h1 ->
      x == sel (ptr_view perm ptr) h0 /\
      sel (ptr_view perm ptr) h0 == sel (ptr_view perm ptr) h1
    )
  =
  let open HST in
  let (x, _) = ! ptr.ptr_v in
  x

inline_for_extraction noextract let ptr_write
  (#a: Type)
  (#perm: Ghost.erased permission)
  (ptr: pointer a)
  (x: a)
  : RST unit
    (ptr_resource perm ptr)
    (fun _ -> ptr_resource perm ptr)
    (fun _ -> allows_write perm)
    (fun h0 _ h1 -> sel (ptr_view perm ptr) h1 == x)
  =
  reveal_rst_inv ();
  reveal_modifies ();
  let open HST in
  let (v', perm_map) = ! ptr.ptr_v in
  ptr.ptr_v := (x, Ghost.hide (change_snapshot #a #v' (Ghost.reveal perm_map) (Ghost.reveal ptr.ptr_pid) x));
  admit()

inline_for_extraction noextract let ptr_alloc
  (#a:Type)
  (init:a)
  : RST (pointer a)
    (empty_resource)
    (fun ptr -> ptr_resource (Ghost.hide 1.0R) ptr)
    (fun _ -> True)
    (fun _ ptr h1 -> sel (ptr_view (Ghost.hide 1.0R) ptr) h1 == init)
  =
  reveal_rst_inv ();
  reveal_modifies ();
  let perm_map_pid = Ghost.hide (
    let (vp, pid) =  new_value_perms init true in
    ((vp <: perms_rec a), pid)
  ) in
  let ptr_v = HST.ralloc_mm HS.root (init, Ghost.hide (fst (Ghost.reveal perm_map_pid))) in
  admit();
  { ptr_v = ptr_v; ptr_pid = Ghost.hide (snd (Ghost.reveal perm_map_pid)) }

inline_for_extraction noextract let ptr_free
  (#a:Type)
  (ptr:pointer a)
  : RST unit
    (ptr_resource (Ghost.hide 1.0R) ptr)
    (fun ptr -> empty_resource)
    (fun _ -> True )
    (fun _ _ _ -> True)
  =
  reveal_rst_inv ();
  reveal_modifies ();
  reveal_empty_resource ();
  HST.rfree ptr.ptr_v;
  admit()

inline_for_extraction noextract let ptr_share
  (#a: Type)
  (#p:Ghost.erased permission)
  (ptr: pointer a)
  : RST (pointer a)
    (ptr_resource p ptr)
    (fun ptr1 -> ptr_resource (half_permission p) ptr1 <*> ptr_resource (half_permission p) ptr)
    (fun _ -> allows_read p)
    (fun h0 ptr1 h1 ->
      ptr.ptr_v == ptr1.ptr_v
    )
  =
  reveal_rst_inv ();
  reveal_modifies ();
  let open HST in
  let (v, perm_map) = ! ptr.ptr_v in
  let (new_perm_map_new_pid) = Ghost.hide (
    let (vp, pid) = share_perms #a #v (Ghost.reveal perm_map) (Ghost.reveal ptr.ptr_pid) in
    ((vp <: perms_rec a), pid)
  ) in
  ptr.ptr_v := (v, Ghost.hide (fst (Ghost.reveal new_perm_map_new_pid)));
  let ptr1 = {
    ptr_v = ptr.ptr_v;
    ptr_pid = Ghost.hide (snd (Ghost.reveal new_perm_map_new_pid))
  } in
  admit();
  ptr1

inline_for_extraction noextract let ptr_merge
  (#a: Type)
  (#p1 : Ghost.erased permission)
  (#p2: Ghost.erased permission{summable_permissions p1 p2})
  (ptr1: pointer a)
  (ptr2: pointer a)
  : RST unit
    (ptr_resource p1 ptr1 <*> ptr_resource p2 ptr2)
    (fun _ -> ptr_resource (sum_permissions p1 p2) ptr1)
    (fun h ->
      allows_read p1 /\ allows_read p2 /\
      ptr1.ptr_v == ptr2.ptr_v
    )
    (fun h0 _ h1 -> True)
  =
  reveal_rst_inv ();
  reveal_modifies ();
  let open HST in
  let (v, perm_map) = !ptr1.ptr_v in
  FStar.ModifiesGen.loc_disjoint_aloc_elim #ploc #cls
  #(let r1 = frame_of_pointer ptr1 in r1)
  #(let a1 = pointer_as_addr ptr1 in a1)
  #(let r2 = frame_of_pointer ptr2 in r2)
  #(let a2 = pointer_as_addr ptr2 in a2)
  (aloc_pointer ptr1) (aloc_pointer ptr2);

  let new_perm_map = Ghost.hide (
    merge_perms #a #v (Ghost.reveal perm_map) (Ghost.reveal ptr1.ptr_pid) (Ghost.reveal ptr2.ptr_pid)
  ) in
  ptr1.ptr_v := (v, new_perm_map);
  admit()
