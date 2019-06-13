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
    PR.pointer_live ptr h /\ // HS.is_mm ptr.PR.ptr_v /\ (PR.frame_of_pointer ptr) == HS.root /\
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
  let open HST in
  let (x, _) = ! ptr.PR.ptr_v in
  x

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
  let h0 = HST.get () in
  RST.reveal_rst_inv ();
  RST.reveal_modifies ();
  let open HST in
  let (v', perm_map) = !ptr.PR.ptr_v in
  let perm_map'  = Ghost.hide (P.change_snapshot #a #v' (Ghost.reveal perm_map) (Ghost.reveal ptr.PR.ptr_pid) x) in
  ptr.PR.ptr_v := (x, (perm_map' <: Ghost.erased (P.perms_rec a)));
  let h1 = HST.get () in
  assume(MG.loc_includes (MG.loc_not_unused_in PR.cls h1) (R.as_loc (R.fp (ptr_resource ptr))));
  let r = PR.frame_of_pointer ptr in
  let n = PR.pointer_as_addr ptr in
  MG.modifies_aloc_intro
    #PR.ploc #PR.cls
    #r
    #n
    (PR.aloc_pointer ptr)
    h0 h1
    (fun r -> ())
    (fun t pre b -> ())
    (fun t pre b -> ())
    (fun r n -> ())
    (fun ploc' ->
      let ploc = PR.aloc_pointer ptr in
      assert((Ghost.reveal ploc) =!= (Ghost.reveal ploc'));
      let aux (t': Type0) (ptr': PR.pointer t') : Lemma
       ((
          let pid' = Ghost.reveal ptr'.PR.ptr_pid in
          PR.pointer_live ptr' h0 /\
          PR.frame_of_pointer ptr' == r /\ // The case where r or n are different is trivial
          PR.pointer_as_addr ptr' == n /\ // So we just take the case where ptr' point to
          (Ghost.reveal ploc') == pid') ==> // a different pid' than pid.
       (PR.sel h0 ptr' == PR.sel h1 ptr' /\
          PR.pointer_live ptr' h1))
        =
        let aux' (_ : squash (let pid' = Ghost.reveal ptr'.PR.ptr_pid in
          PR.pointer_live ptr' h0 /\
          PR.frame_of_pointer ptr' == r /\
          PR.pointer_as_addr ptr' == n /\
          (Ghost.reveal ploc') == pid')) : Lemma
          (PR.sel h0 ptr' == PR.sel h1 ptr' /\
          PR.pointer_live ptr' h1)
          =
          let pid = Ghost.reveal ptr.PR.ptr_pid in
          let pid' = Ghost.reveal ptr'.PR.ptr_pid in
          P.only_one_live_pid_with_full_permission #a #x
            (Ghost.reveal perm_map')
            (Ghost.reveal ptr.PR.ptr_pid);
          assert(P.get_permission_from_pid (Ghost.reveal perm_map') pid' == P.get_permission_from_pid (Ghost.reveal perm_map) pid');
          PR.live_same_pointers_equal_types t' a ptr' ptr h0;
          PR.live_same_pointers_equal_types t' a ptr' ptr h1;
          assert(PR.sel h0 ptr' == PR.sel h1 ptr');
          ()
        in
        Classical.impl_intro aux'
      in
      Classical.forall_intro_2 aux
    )
  ;
  assert(MG.modifies #PR.ploc #PR.cls (R.as_loc (R.fp (ptr_resource ptr))) h0 h1);
  assert(
    (forall frame .
      MG.loc_disjoint frame (R.as_loc (R.fp (ptr_resource ptr))) /\
      MG.loc_includes (MG.loc_not_unused_in PR.cls h0) frame
      ==>
      MG.loc_disjoint frame (R.as_loc (R.fp (ptr_resource ptr))) /\
      MG.loc_includes (MG.loc_not_unused_in PR.cls h1) frame)
  );
  ()

inline_for_extraction noextract let ptr_alloc
  (#a:Type)
  (init:a)
  : RST (pointer a)
    (empty_resource)
    (fun ptr -> ptr_resource ptr)
    (fun _ -> True)
    (fun _ ptr h1 -> sel (ptr_view ptr) h1 = (init, 1.0R))
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
    (ptr_resource ptr)
    (fun ptr -> empty_resource)
    (fun h0 -> allows_write (snd (sel (ptr_view ptr) h0)))
    (fun _ _ _ -> True)
  =
  reveal_rst_inv ();
  reveal_modifies ();
  reveal_empty_resource ();
  HST.rfree ptr.ptr_v;
  admit()

inline_for_extraction noextract let ptr_share
  (#a: Type)
  (ptr: pointer a)
  : RST (pointer a)
    (ptr_resource ptr)
    (fun ptr1 -> ptr_resource ptr1 <*> ptr_resource ptr)
    (fun h0 -> allows_read (snd (sel (ptr_view ptr) h0)))
    (fun h0 ptr1 h1 ->
      ptr.ptr_v == ptr1.ptr_v /\
      fst (sel (ptr_view ptr) h1) == fst (sel (ptr_view ptr) h0) /\
      fst (sel (ptr_view ptr1) h1) == fst (sel (ptr_view ptr) h0) /\
      snd (sel (ptr_view ptr) h1) = half_permission (snd (sel (ptr_view ptr) h0)) /\
      snd (sel (ptr_view ptr1) h1) =  half_permission (snd (sel (ptr_view ptr) h0))
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
