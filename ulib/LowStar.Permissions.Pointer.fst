module LowStar.Permissions.Pointer

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module Seq = FStar.Seq

module P = LowStar.Permissions
module PR =  LowStar.Permissions.References
module R = LowStar.Resource
module RST = LowStar.RST
module MG = FStar.ModifiesGen
open FStar.Real

abstract let ptr_view (#a:Type) (ptr:PR.pointer a) : R.view (PR.with_perm a) =
  R.reveal_view ();
  let fp = Ghost.hide (PR.loc_pointer ptr) in
  let inv h =
    let a_with_perm = PR.sel h ptr in
    let (v, _) = HS.sel h ptr.PR.ptr_v in
    PR.pointer_live ptr h /\
    a_with_perm.PR.wp_perm >. 0.0R /\
    v == a_with_perm.PR.wp_v
  in
  let sel h = PR.sel h ptr
  in
  {
    R.fp = fp;
    R.inv = inv;
    R.sel = sel
  }

let ptr_resource (#a:Type) (ptr:PR.pointer a) =
  R.as_resource (ptr_view ptr)

inline_for_extraction noextract let ptr_read
  (#a: Type)
  (ptr: PR.pointer a)
  : RST.RST a
    (ptr_resource ptr)
    (fun _ -> ptr_resource ptr)
    (fun _ -> True)
    (fun h0 x h1 ->
      x == (R.sel (ptr_view ptr) h0).PR.wp_v /\
      R.sel (ptr_view ptr) h0 == R.sel (ptr_view ptr) h1
    )
  =
  RST.reveal_rst_inv ();
  RST.reveal_modifies ();
  PR.get ptr

inline_for_extraction noextract let ptr_write
  (#a: Type)
  (ptr: PR.pointer a)
  (x: a)
  : RST.RST unit
    (ptr_resource ptr)
    (fun _ -> ptr_resource ptr)
    (fun h0 -> P.allows_write (R.sel (ptr_view ptr) h0).PR.wp_perm)
    (fun h0 _ h1 -> (
      R.sel (ptr_view ptr) h1).PR.wp_v == x /\
      (R.sel (ptr_view ptr) h1).PR.wp_perm == (R.sel (ptr_view ptr) h0).PR.wp_perm
    )
  =
  (**) RST.reveal_rst_inv ();
  (**) RST.reveal_modifies ();
  PR.upd ptr x

inline_for_extraction noextract let ptr_alloc
  (#a:Type)
  (init:a)
  : RST.RST (PR.pointer a)
    (R.empty_resource)
    (fun ptr -> ptr_resource ptr)
    (fun _ -> True)
    (fun _ ptr h1 -> R.sel (ptr_view ptr) h1 == { PR.wp_v = init; PR.wp_perm = 1.0R})
  =
  (**) RST.reveal_rst_inv ();
  (**) RST.reveal_modifies ();
  (**) R.reveal_empty_resource ();
  PR.create init

inline_for_extraction noextract let ptr_free
  (#a: Type)
  (ptr: PR.pointer a)
  : RST.RST unit
    (ptr_resource ptr)
    (fun ptr -> R.empty_resource)
    (fun h0 -> P.allows_write (R.sel (ptr_view ptr) h0).PR.wp_perm)
    (fun _ _ _ -> True)
  =
  (**) RST.reveal_rst_inv ();
  (**) RST.reveal_modifies ();
  R.reveal_empty_resource ();
  PR.free ptr


inline_for_extraction noextract let ptr_share
  (#a: Type)
  (ptr: PR.pointer a)
  : RST.RST (PR.pointer a)
    (ptr_resource ptr)
    (fun ptr1 -> R.(ptr_resource ptr1 <*> ptr_resource ptr))
    (fun h0 -> P.allows_read (R.sel (ptr_view ptr) h0).PR.wp_perm)
    (fun h0 ptr1 h1 ->
      ptr.PR.ptr_v == ptr1.PR.ptr_v /\ (
        let v0_ptr = R.sel (ptr_view ptr) h0 in
        let v1_ptr = R.sel (ptr_view ptr) h1 in
        let v1_ptr1 = R.sel (ptr_view ptr1) h1 in
        v1_ptr.PR.wp_v == v0_ptr.PR.wp_v /\ v1_ptr1.PR.wp_v == v0_ptr.PR.wp_v /\
        v1_ptr.PR.wp_perm = P.half_permission (v0_ptr.PR.wp_perm) /\
        v1_ptr1.PR.wp_perm = P.half_permission (v0_ptr.PR.wp_perm)
      )
    )
  =
  RST.reveal_rst_inv ();
  RST.reveal_modifies ();
  let open HST in
  let h0 = HST.get () in
  let (v, perm_map) = ! ptr.PR.ptr_v in
  let (new_perm_map_new_pid) = Ghost.hide (
    let (vp, pid) = P.share_perms #a #v (Ghost.reveal perm_map) (Ghost.reveal ptr.PR.ptr_pid) in
    ((vp <: P.perms_rec a), pid)
  ) in
  ptr.PR.ptr_v := (v, Ghost.hide (fst (Ghost.reveal new_perm_map_new_pid)));
  let h1 = HST.get () in
  let ptr1 = {
    PR.ptr_v = ptr.PR.ptr_v;
    PR.ptr_pid = Ghost.hide (snd (Ghost.reveal new_perm_map_new_pid))
  } in
  assert(
    ptr.PR.ptr_v == ptr1.PR.ptr_v /\ (
        let v0_ptr = R.sel (ptr_view ptr) h0 in
        let v1_ptr = R.sel (ptr_view ptr) h1 in
        let v1_ptr1 = R.sel (ptr_view ptr1) h1 in
        v1_ptr.PR.wp_v == v0_ptr.PR.wp_v /\ v1_ptr1.PR.wp_v == v0_ptr.PR.wp_v /\
        v1_ptr.PR.wp_perm = P.half_permission (v0_ptr.PR.wp_perm) /\
        v1_ptr1.PR.wp_perm = P.half_permission (v0_ptr.PR.wp_perm)
      )
  );
  assume(R.inv (R.(ptr_resource ptr1 <*> ptr_resource ptr)) h1);
  assume(RST.rst_inv (R.(ptr_resource ptr1 <*> ptr_resource ptr)) h1);
  assume(MG.modifies #PR.ploc #PR.cls (R.as_loc (R.fp (ptr_resource ptr))) h0 h1);
  assume(
         (forall frame .
               MG.loc_disjoint frame (R.as_loc (R.fp (ptr_resource ptr))) /\
               MG.loc_includes (MG.loc_not_unused_in PR.cls h0) frame
               ==>
               MG.loc_disjoint frame (R.as_loc (R.fp (R.(ptr_resource ptr1 <*> ptr_resource ptr)))) /\
               MG.loc_includes (MG.loc_not_unused_in PR.cls h1) frame)
  );
  ptr1

inline_for_extraction noextract let ptr_merge
  (#a: Type)
  (ptr1: pointer a)
  (ptr2: pointer a)
  : RST unit
    (ptr_resource ptr1 <*> ptr_resource ptr2)
    (fun _ -> ptr_resource ptr1)
    (fun h ->
      let (_, p1) = sel (ptr_view ptr1) h in
      let (_, p2) = sel (ptr_view ptr1) h in
      allows_read p1 /\ allows_read p2 /\
      summable_permissions p1 p2 /\
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
