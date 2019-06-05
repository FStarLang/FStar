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
module LowStar.RST.LinkedList.Erased

open FStar.HyperStack.ST
module HS = FStar.HyperStack
module L = FStar.List.Tot
module B = LowStar.Buffer
module MO = LowStar.Modifies

open LowStar.Resource.Erased
open LowStar.RST.Erased

open LowStar.BufferOps
open FStar.Ghost

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
  hide ({
    t = list a;
    view = view
  })

abstract
let pts_to (#a:Type) (ptr:t a) (v:erased (cell a)) : resource =
  reveal_view();
  let fp = Ghost.hide (B.loc_addr_of_buffer ptr) in
  let inv h = B.live h ptr /\ B.freeable ptr /\ Seq.index (B.as_seq h ptr) 0 == reveal v in
  let sel (h:imem inv) = (reveal v).data in
  let (view:view a) = {
    fp = fp;
    inv = inv;
    sel = sel
  }
  in
  hide ({
    t = a;
    view = view
  })

abstract
let rec slist (#a:Type) (ptr:t a) (l:erased (list (cell a))) : Tot resource
  (decreases (reveal l)) 
  =
  match reveal l with
  | [] -> empty_list ptr
  | hd::tl -> pts_to ptr (hide hd) <*> slist hd.next (hide tl)

abstract
let dummy_cell (#a:Type) (ptr:t a) : resource =
  reveal_view();
  let fp = Ghost.hide (B.loc_addr_of_buffer ptr) in
  let inv h = B.live h ptr /\ B.freeable ptr in
  let sel (h:imem inv) = () in
  let view = {
    fp = fp;
    inv = inv;
    sel = sel
  } in
  hide ({
    t = unit;
    view = view
  })

let cell_alloc (#a:Type)
              (init:cell a)
            : RST (t a) (empty_resource)
                        (fun ptr -> pts_to ptr (hide init))
                        (fun _ -> True)
                        (fun _ ptr h1 -> True) =
  reveal_rst_inv ();
  reveal_modifies ();
  reveal_view ();
  B.malloc HS.root init 1ul

let cell_free (#a:Type)
              (ptr:t a)
              (v:erased (cell a))
           : RST unit (pts_to ptr v)
                      (fun ptr -> empty_resource)
                      (fun _ -> True)
                      (fun _ ptr h1 -> True) =
  reveal_rst_inv ();
  reveal_modifies ();
  reveal_empty_resource ();
  reveal_view ();
  B.free ptr

let set_dummy_cell (#a:Type) (ptr:t a) (c:cell a)
  : RST unit
    (dummy_cell ptr)
    (fun _ -> pts_to ptr (hide c))
    (fun _ -> True)
    (fun _ _ _ -> True)
  = reveal_rst_inv();
    reveal_modifies();
    reveal_view ();
    ptr *= c

let set_cell (#a:Type) (ptr:t a) (c:cell a) (v:a)
  : RST unit
    (pts_to ptr (hide c))
    (fun _ -> pts_to ptr (hide ({c with data = v})))
    (fun _ -> True)
    (fun _ _ _ -> True)
  = reveal_rst_inv();
    reveal_modifies();
    reveal_view ();
    let node = !* ptr in
    let node' = {node with data = v} in
    ptr *= node'

(* We provide two versions of cons.
   The first one assumes there is an unused (dummy) node, that we can just set to be the head.
   The second performs an allocation *)

let cons (#a:Type) (ptr:t a) (l:erased (list (cell a))) (hd:t a) (v:a)
  : RST unit
  (dummy_cell hd <*> slist ptr l)
  (fun _ -> slist hd (hide ({data = v; next = ptr} :: reveal l)))
  (fun _ -> True)
  (fun _ _ _ -> True) =
  let new_cell = {data = v; next = ptr} in
  let r = slist ptr l in                                        //TODO: due to tactics peculiarity
  rst_frame 
    (dummy_cell hd <*> r)
    (fun _ -> pts_to hd (hide new_cell) <*> r)
    (fun _ -> set_dummy_cell hd new_cell)

let cons_alloc (#a:Type) (ptr:t a) (l:erased (list (cell a))) (v:a)
  : RST (t a)
  (slist ptr l)
  (fun ptr' -> slist ptr' (hide ({data = v; next = ptr} :: (reveal l))))
  (fun _ -> True)
  (fun _ _ _ -> True) =
  let new_cell = {data = v; next = ptr} in
  let r = slist ptr l in                                        //TODO: due to tactics peculiarity
  let new_head = rst_frame 
    r
    (fun ret -> pts_to ret (hide new_cell) <*> r)
    (fun _ -> cell_alloc new_cell)
  in
  new_head

(* Similarly, we provide two versions of uncons. 
   The second deallocates the node currently in head position, while the first
   returns the head and the tail *)

let uncons (#a:Type) (ptr:t a) (l:erased (list (cell a)){Cons? (reveal l)})
  : RST (t a * t a)
        (slist ptr l)
        (fun (hd, ptr') -> pts_to hd (hide (L.hd (reveal l))) <*> slist ptr' (hide (L.tl (reveal l))))
        (requires fun _ -> True)
        (ensures fun _ _ _ -> True)
  =
  reveal_view ();
  let node = !* ptr in
  let next = node.next in
  ptr, next
 
let uncons_dealloc (#a:Type) (ptr:t a) (l:erased (list (cell a)){Cons? (reveal l)})
  : RST (t a)
        (slist ptr l)
        (fun ptr' -> slist ptr' (hide (L.tl (reveal l))))
        (requires fun _ -> True)
        (ensures fun _ _ _ -> True)
  =
  reveal_view ();
  let node = !* ptr in
  let next = node.next in
  let c = (hide (L.hd (reveal l))) in                  //TODO: due to tactics peculiarity
  let r = slist next (hide (L.tl (reveal l))) in       //TODO: due to tactics peculiarity
  rst_frame 
    (pts_to ptr c <*> r)
    (fun _ -> r)
    (fun _ -> cell_free ptr c);
  next

val map (#a:Type) (f:a -> a) (ptr:t a) (l:erased (list (cell a)))
  : RST unit
        (slist ptr l)
        (fun _ -> slist ptr (hide (L.map (fun x -> ({x with data = f x.data})) (reveal l))))
        (requires fun _ -> True)
        (ensures fun _ _ _ -> True)

let rec map #a f ptr l =
  reveal_view ();
  if B.is_null ptr then ()
  else (
    let node = !*ptr in
    let next = node.next in
    let l_tl = hide (L.tl (reveal l)) in
    let r = slist next l_tl in                                        //TODO: due to tactics peculiarity
    rst_frame 
      (pts_to ptr (hide node) <*> r)
      (fun _ -> pts_to ptr (hide ({node with data = f node.data})) <*> r)
      (fun _ -> set_cell ptr node (f node.data));
    // otherwise resolve_delta in rst_frame below fails with a
    // universe mismatch error; the error seems to be stemming
    // from the canonicalizer identifying three distinct 
    // resource-terms between the outer and inner resources 
    // instead of the expected two (which is what happens when 
    // one gives an explicit name r to pts_to ptr ... below)
    let r' = pts_to ptr (hide ({node with data = f node.data})) in    //TODO: due to tactics peculiarity
    rst_frame
      (r' <*> slist next l_tl)
      (fun _ -> r' <*> 
             slist next (hide (L.map (fun x -> ({x with data = f x.data})) (reveal l_tl))))
      (fun _ -> map f next l_tl)
  )

type llist (a: Type0) = t a & (erased (list (cell a)))

let llist_resource (#a:Type0) (x:llist a) =
  slist (fst x) (snd x)

let rec llist_view_aux (#a:Type0) (x:erased (list (cell a))) : GTot (list a) 
  (decreases (reveal x)) =
  match reveal x with
  | [] -> []
  | hd::tl -> hd.data :: llist_view_aux (hide tl)

let llist_view (#a:Type0) (x:llist a) : GTot (list a) =
  llist_view_aux (snd x)

let llist_cons #a x v =
  let init_ptr = fst x in
  let init_l = snd x in
  let ptr = cons_alloc init_ptr init_l v in
  (ptr, (hide ({data = v; next = init_ptr} :: (reveal init_l))))

let llist_head #a x =
  reveal_view ();
  let init_ptr = fst x in
  let node = !*init_ptr in
  node.data

let llist_tail #a x =
  reveal_view ();
  let init_ptr = fst x in
  let init_l = snd x in
  (uncons_dealloc init_ptr init_l, hide (L.tl (reveal init_l)))

let rec lemma_map_view_aux (#a:Type0) (f:a -> a) (init_l:erased (list (cell a)))
  : Lemma (ensures (llist_view_aux (hide (L.map (fun x -> ({x with data = f x.data})) (reveal init_l))) ==
                    L.map f (llist_view_aux init_l)))
          (decreases (reveal init_l))
   = match reveal init_l with
  | [] -> ()
  | hd :: tl -> lemma_map_view_aux f (hide tl)

let llist_map #a f x =
  let init_ptr = fst x in
  let init_l = snd x in
  map f init_ptr init_l;
  lemma_map_view_aux f init_l;
  (init_ptr, hide (L.map (fun x -> ({x with data = f x.data})) (reveal init_l)))
