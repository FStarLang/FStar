module LowStar.Permissions.References

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module Seq = FStar.Seq
module MG = FStar.ModifiesGen

open LowStar.Permissions
open FStar.Real


type value_with_perms (a: Type0) = vp : (a & Ghost.erased (perms_rec a)){
  let (v, p) = vp in
  forall (pid:live_pid (Ghost.reveal p)). get_snapshot_from_pid (Ghost.reveal p) pid == v
}

noeq type pointer (a: Type0) = {
  ptr_v: HST.reference (value_with_perms a);
  ptr_pid: Ghost.erased perm_id
}

let frame_of_pointer (#a: Type0) (ptr: pointer a) : HS.rid =
  HS.frameOf ptr.ptr_v

let pointer_as_addr (#a: Type0) (ptr: pointer a) : GTot nat =
  HS.as_addr ptr.ptr_v


type ploc_ (region: HS.rid) (addr: nat) = {
  ploc_pid: perm_id
}

type ploc (region: HS.rid) (addr: nat) = Ghost.erased (ploc_ region addr)

let ploc_includes (#r: HS.rid) (#a: nat) (ploc1 ploc2: ploc r a) =
  (Ghost.reveal ploc1).ploc_pid == (Ghost.reveal ploc2).ploc_pid

let ploc_disjoint  (#r: HS.rid) (#a: nat) (ploc1 ploc2: ploc r a) =
  (Ghost.reveal ploc1).ploc_pid =!= (Ghost.reveal ploc2).ploc_pid

let ploc_preserved  (#r: HS.rid) (#a: nat) (ploc: ploc r a) (h0 h1: HS.mem) =
  forall (t: Type0) (ptr: pointer t) .
  let pid = Ghost.reveal ptr.ptr_pid in
  let (_, vp0) = HS.sel h0 ptr.ptr_v in
  let vp0 = Ghost.reveal vp0 in
  let (_, vp1) = HS.sel h1 ptr.ptr_v in
  let vp1 = Ghost.reveal vp1 in
  begin
    (is_live_pid vp0 (Ghost.reveal ploc).ploc_pid /\ HS.contains h0 ptr.ptr_v /\
    HS.frameOf ptr.ptr_v == r /\ HS.as_addr ptr.ptr_v == a /\ (Ghost.reveal ploc).ploc_pid == pid)
    ==> begin
      get_permission_from_pid vp0 pid == get_permission_from_pid vp1 pid /\
      get_snapshot_from_pid vp0 pid == get_snapshot_from_pid vp1 pid /\
      HS.contains h1 ptr.ptr_v
    end
  end

let cls : MG.cls ploc = MG.Cls #ploc
  ploc_includes
  (fun #r #a x -> ())
  (fun #r #a x1 x2 x3 -> ())
  ploc_disjoint
  (fun #r #a x1 x2 -> ())
  (fun #r #a larger1 larger2 smaller1 smaller2 -> ())
  ploc_preserved
  (fun #r #a x h -> ())
  (fun #r #a x h1 h2 h3 -> ())
  (fun #r #a b h1 h2 f -> admit())

let loc = MG.loc cls

let aloc_pointer (#a: Type0) (ptr: pointer a) : GTot (ploc (frame_of_pointer ptr) (pointer_as_addr ptr)) =
  let r = frame_of_pointer ptr in
  let a = pointer_as_addr ptr in
  let pid =  Ghost.reveal ptr.ptr_pid in
  let out = ({
    ploc_pid = pid
  } <:  ploc_ r a) in
  Ghost.hide out

let loc_pointer (#a: Type0) (ptr: pointer a) : GTot loc =
  let r = frame_of_pointer ptr in
  let a = pointer_as_addr ptr in
  MG.loc_of_aloc #ploc #cls
  #r
  #a
  (aloc_pointer ptr)
