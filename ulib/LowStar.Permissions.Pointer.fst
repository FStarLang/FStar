module LowStar.Permissions.Pointer

module B = LowStar.Buffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module Seq = FStar.Seq

open LowStar.Resource
open LowStar.RST

open LowStar.BufferOps
open FStar.Permissions

private noeq type pointer (a: Type0) = {
  v: B.pointer (a & Ghost.erased (value_perms a));
  pid: Ghost.erased pos
}

private noeq type pointer_view (a: Type0) = {
  view_v: a;
  view_perm_kind: Ghost.erased permission_kind
}

abstract
let ptr_view (#a:Type) (ptr:pointer a) : view (pointer_view a) = 
  reveal_view ();
  let fp = Ghost.hide (B.loc_addr_of_buffer ptr.v) in 
  let inv h = 
    let (_, perm_map) = Seq.index (B.as_seq h ptr.v) 0 in
    B.live h ptr.v /\ B.freeable ptr.v /\ is_live_pid (Ghost.reveal perm_map) ptr.pid 
  in
  let sel h = 
    let (_, perm_map) = Seq.index (B.as_seq h ptr.v) 0 in
    let perm = get_permission_from_pid (Ghost.reveal perm_map) (Ghost.reveal ptr.pid) in
    let snapshot = get_snapshot_from_pid (Ghost.reveal perm_map) (Ghost.reveal ptr.pid) in
    { 
      view_v = snapshot;
      view_perm_kind = Ghost.hide (get_perm_kind_from_pid (Ghost.reveal perm_map) (Ghost.reveal ptr.pid))
    }
  in
  {
    fp = fp;
    inv = inv;
    sel = sel
  }

let ptr_resource (#a:Type) (ptr:pointer a) = 
  as_resource (ptr_view ptr)

let get_perm_kind (#a:Type) (ptr: pointer a) h0 : GTot permission_kind =
  Ghost.reveal (sel (ptr_view ptr) h0).view_perm_kind

let ptr_read 
  (#a: Type)
  (ptr: pointer a)
  : RST a 
    (ptr_resource ptr)
    (fun _ -> ptr_resource ptr)
    (fun h0 -> allows_read (get_perm_kind ptr h0))
    (fun h0 x h1 -> 
      let view0 = sel (ptr_view ptr) h0 in 
      let view1 = sel (ptr_view ptr) h1 in 
      view0 == view1 /\ view0.view_v == x
    )
  = 
  let (x, _) = !* ptr.v in
  x

let ptr_write 
  (#a: Type)
  (ptr: pointer a)
  (x: a)
  : RST unit 
    (ptr_resource ptr)
    (fun _ -> ptr_resource ptr)
    (fun h0 -> allows_write (get_perm_kind ptr h0))
    (fun h0 _ h1 -> (sel (ptr_view ptr) h1) == { sel (ptr_view ptr) h0 with view_v = x})
   =
   reveal_rst_inv ();
   reveal_modifies ();
   let (_, perm_map) = !* ptr.v in
   ptr.v *= (x, perm_map)

let ptr_alloc (#a:Type)
              (init:a)
            : RST (pointer a) (empty_resource)
                                (fun ptr -> ptr_resource ptr)
                                (fun _ -> True)
                                (fun _ ptr h1 -> 
                                   sel (ptr_view ptr) h1 == {
                                     view_v = init; 
                                     view_perm_kind = Ghost.hide FULL
                                    }
                                ) =
  reveal_rst_inv ();
  reveal_modifies ();
  let perm_map = Ghost.hide (new_value_perms init) in
  let pid = Ghost.hide 1 in
  let ptr_v = B.malloc HS.root (init, perm_map) 1ul in
  { v = ptr_v; pid = pid }

let ptr_free (#a:Type)
             (ptr:pointer a)
           : RST unit (ptr_resource ptr)
                      (fun ptr -> empty_resource)
                      (fun h0 -> get_perm_kind ptr h0 = RW )
                      (fun _ _ _ -> True) =
  reveal_rst_inv ();
  reveal_modifies ();
  reveal_empty_resource ();
  B.free ptr.v

let foo () : RST unit 
  (empty_resource)
  (fun _ -> empty_resource)
  (fun _ -> True)
  (fun _ _ _ -> True)
  = 
  let ptr = ptr_alloc 42ul in
  let x1 = ptr_read ptr in
  ptr_write ptr FStar.UInt32.(x1 +^ 1ul);
  ptr_free ptr;
  //let x2 = ptr_read ptr in
  ()

