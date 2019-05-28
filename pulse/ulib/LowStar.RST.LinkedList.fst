(*
   Copyright 2008-2019 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module LowStar.RST.LinkedList

open FStar.HyperStack.ST
module HS = FStar.HyperStack
module L = FStar.List.Tot
module B = LowStar.Buffer
module MO = LowStar.Modifies

open LowStar.Resource
open LowStar.RST

open LowStar.BufferOps

#set-options "--__no_positivity --use_two_phase_tc true"

(* The definition of linked lists comes from kremlin/test/LinkedList4.fst *)

/// We revisit the classic example of lists, but in a low-level
/// setting, using linked lists. This second version uses
/// `B.pointer_or_null`, the type of buffers of length 1 or 0.
noeq
type t (a: Type0) =
  B.pointer_or_null (cell a)

and cell (a: Type0) = {
  next: t a;
  data: a;
}

(* Ideally, this would be bootstrapped for clients to use a "t' a".
   The hidden (abstract) type definition would be a (t a) & list (cell a) *)

abstract
let empty_list (#a:Type) (ptr:t a) : resource =
  reveal_view();
  let fp = Ghost.hide (B.loc_buffer ptr) in
  let inv h = B.g_is_null ptr /\ True in
  let sel h : list a = [] in
  let (view:view (list a)) = {
    fp = fp;
    inv = inv;
    sel = sel
  } in
  {
    t = list a;
    view = view
  }

abstract
let pts_to (#a:Type) (ptr:t a) (v:cell a) : resource =
  reveal_view();
  let fp = Ghost.hide (B.loc_addr_of_buffer ptr) in
  let inv h = B.live h ptr /\ B.freeable ptr /\ Seq.index (B.as_seq h ptr) 0 == v in
  let sel (h:imem inv) = v.data in
  let (view:view a) = {
    fp = fp;
    inv = inv;
    sel = sel
  }
  in
  {
    t = a;
    view = view
  }

abstract
let rec slist (#a:Type) (ptr:t a) (l: list (cell a)) : Tot resource
  (decreases l) 
  =
  match l with
  | [] -> empty_list ptr
  | hd::tl -> pts_to ptr hd <*> slist hd.next tl

let cell_alloc (#a:Type)
              (init:cell a)
            : RST (t a) (empty_resource)
                        (fun ptr -> pts_to ptr init)
                        (fun _ -> True)
                        (fun _ ptr h1 -> True) =
  reveal_rst_inv ();
  reveal_modifies ();
  B.malloc HS.root init 1ul

let cell_free (#a:Type)
              (ptr:t a)
              (v:cell a)
           : RST unit (pts_to ptr v)
                      (fun ptr -> empty_resource)
                      (fun _ -> True)
                      (fun _ ptr h1 -> True) =
  reveal_rst_inv ();
  reveal_modifies ();
  reveal_empty_resource ();
  B.free ptr

(* We provide two versions of cons.
   The first one assumes there is an unused (dummy) node, that we can just set to be the head.
   The second performs an allocation *)

(* TODO: Needs dummy resources
let cons (#a:Type) (ptr:t a) (l:list (cell a)) (hd:t a) (v:a)
  : RST (t a)
  (dummy_cell hd <*> slist ptr l)
  (fun (ptr') -> slist ptr' ({data = v; next = ptr} :: l))
  (fun _ -> True)
  (fun _ _ _ -> True) =
  let new_cell = {data = v; next = ptr} in
  let new_head = rst_frame 
    (slist ptr l)
    (fun ret -> pts_to ret new_cell <*> slist ptr l)
    (fun _ -> cell_alloc new_cell)
  in
  new_head
*)

let cons_alloc (#a:Type) (ptr:t a) (l:list (cell a)) (v:a)
  : RST (t a)
  (slist ptr l)
  (fun ptr' -> slist ptr' ({data = v; next = ptr} :: l))
  (fun _ -> True)
  (fun _ _ _ -> True) =
  let new_cell = {data = v; next = ptr} in
  let new_head = rst_frame 
    (slist ptr l)
    (fun ret -> pts_to ret new_cell <*> slist ptr l)
    (fun _ -> cell_alloc new_cell)
  in
  new_head

(* Similarly, we provide two versions of uncons. 
   The second deallocates the node currently in head position, while the first
   returns the head and the tail *)

(* TODO: Should return a dummy resource *)
let uncons (#a:Type) (ptr:t a) (l:list (cell a){Cons? l})
  : RST (t a * t a)
        (slist ptr l)
        (fun (hd, ptr') -> pts_to hd (L.hd l) <*> slist ptr' (L.tl l))
        (requires fun _ -> True)
        (ensures fun _ _ _ -> True)
  =
  let node = !* ptr in
  let next = node.next in
  ptr, next
 
let uncons_dealloc (#a:Type) (ptr:t a) (l:list (cell a){Cons? l})
  : RST (t a)
        (slist ptr l)
        (fun ptr' -> slist ptr' (L.tl l))
        (requires fun _ -> True)
        (ensures fun _ _ _ -> True)
  =
  let node = !* ptr in
  let next = node.next in
  rst_frame 
    (pts_to ptr (L.hd l) <*> slist next (L.tl l))
    (fun _ -> slist next (L.tl l))
    (fun _ -> cell_free ptr (L.hd l));
  next

let set_cell (#a:Type) (ptr:t a) (c:cell a) (v:a)
  : RST unit
    (pts_to ptr c)
    (fun _ -> pts_to ptr ({c with data = v}))
    (fun _ -> True)
    (fun _ _ _ -> True)
  = reveal_rst_inv();
    reveal_modifies();
    let node = !* ptr in
    let node' = {node with data = v} in
    ptr *= node'

val map (#a:Type) (f:a -> a) (ptr:t a) (l:list (cell a))
  : RST unit
        (slist ptr l)
        (fun _ -> slist ptr (L.map (fun x -> ({x with data = f x.data})) l))
        (requires fun _ -> True)
        (ensures fun _ _ _ -> True)

let rec map #a f ptr l =
  if B.is_null ptr then ()
  else (
    let node = L.hd l in
    let next = node.next in
    let l_tl = L.tl l in
    rst_frame 
      (pts_to ptr node <*> slist next l_tl)
      (fun _ -> pts_to ptr ({node with data = f node.data}) <*> slist next l_tl)
      (fun _ -> set_cell ptr node (f node.data));
    rst_frame
      (pts_to ptr ({node with data = f node.data}) <*> slist next l_tl)
      (fun _ -> pts_to ptr ({node with data = f node.data}) <*> 
             slist next (L.map (fun x -> ({x with data = f x.data})) l_tl))
      #(_)
      #(pts_to ptr ({node with data = f node.data}))
      (fun _ -> map f next l_tl)
  )
