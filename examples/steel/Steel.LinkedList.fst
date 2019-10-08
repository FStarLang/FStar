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
module Steel.LinkedList

open FStar.HyperStack.ST
module HS = FStar.HyperStack
module L = FStar.List.Tot
module A = Steel.Array

open Steel.RST
module P = LowStar.Permissions

//open LowStar.BufferOps
//open LowStar.RST.LinkedList.Base

#reset-options "--__no_positivity"


(* The definition of linked lists comes from kremlin/test/LinkedList4.fst *)

/// We revisit the classic example of lists, but in a low-level
/// setting, using linked lists. This second version uses
/// `B.pointer_or_null`, the type of buffers of length 1 or 0.
noeq
type t (a: Type0) =
  b:A.array (cell a){A.vlength b <= 1}

and cell (a: Type0) = {
  next: t a;
  data: a;
}

(* Ideally, this would be bootstrapped for clients to use a "t' a".
   The hidden (abstract) type definition would be a (t a) & list (cell a) *)

let empty_inv (#a:Type) (#ptr:t a) (s:rmem (A.array_resource ptr)) =
  A.vlength ptr == 0

let node_inv (#a:Type) (#ptr:t a) (s:rmem (A.array_resource ptr)) =
  P.allows_write (A.get_rperm ptr s) /\ A.vlength ptr == 1 /\ A.freeable ptr

let empty_list (#a:Type) (ptr:t a) : resource =
  hsrefine (A.array_resource ptr) empty_inv

let pts_to (#a:Type) (ptr:t a) (v:cell a) : resource =
  hsrefine (A.array_resource ptr) (fun (s:rmem (A.array_resource ptr)) -> node_inv s /\ Seq.index (A.as_rseq ptr s) 0 == v)

let rec slist' (#a:Type) (ptr:t a) (l:list (cell a)) : Tot resource
  (decreases l)
  = match l with
  | [] -> empty_list ptr
  | hd::tl -> pts_to ptr hd <*> slist' hd.next tl

[@(strict_on_arguments [2])]
let slist #a (ptr:t a) l = slist' ptr l

abstract
let dummy_cell (#a:Type) (ptr:t a) : resource =
  hsrefine (A.array_resource ptr) node_inv

let cell_alloc (#a:Type)
              (init:cell a)
            : RST (t a) (empty_resource)
                        (fun ptr -> pts_to ptr init)
                        (fun _ -> True)
                        (fun _ ptr h1 -> True) =
  reveal_rst_inv ();
  reveal_modifies ();
  A.alloc init 1ul


let cell_free (#a:Type)
              (ptr:t a)
              (v:cell a)
           : RST unit (pts_to ptr v)
                      (fun ptr -> empty_resource)
                      (fun _ -> True)
                      (fun _ ptr h1 -> True) =
  reveal_rst_inv ();
  reveal_modifies ();
  A.free ptr

let set_dummy_cell (#a:Type) (ptr:t a) (c:cell a)
  : RST unit
    (dummy_cell ptr)
    (fun _ -> pts_to ptr c)
    (fun _ -> True)
    (fun _ _ _ -> True)
  = reveal_rst_inv();
    reveal_modifies();
    A.upd ptr 0ul c

let set_cell (#a:Type) (ptr:t a) (c:cell a) (v:a)
  : RST unit
    (pts_to ptr c)
    (fun _ -> pts_to ptr ({c with data = v}))
    (fun _ -> True)
    (fun _ _ _ -> True)
  = reveal_rst_inv();
    reveal_modifies();
    let h0 = HyperStack.ST.get() in
    let node = A.index ptr 0ul in
    let node' = {node with data = v} in
    let h0' = HyperStack.ST.get() in
    A.upd ptr 0ul node';
    let h1 = HyperStack.ST.get() in
    // Unclear why modifies_trans does not trigger automatically
    assert (modifies (pts_to ptr c) (pts_to ptr c) h0 h0');
    assert (modifies (pts_to ptr c) (pts_to ptr node') h0' h1)

#reset-options "--z3rlimit 20 --max_fuel 1 --max_ifuel 1 --z3cliopt smt.QI.EAGER_THRESHOLD=2"

(* We provide two versions of cons.
   The first one assumes there is an unused (dummy) node, that we can just set to be the head.
   The second performs an allocation *)

let cons (#a:Type) (ptr:t a) (l:list (cell a)) (h:t a) (v:a) (x:a)
  : RST unit
  (dummy_cell h <*> slist ptr l)
  (fun _ -> slist h ({data = v; next = ptr} :: l))
  (fun _ -> True)
  (fun _ _ _ -> True) =
  let new_cell = {data = v; next = ptr} in
  rst_frame
    (dummy_cell h <*> slist ptr l)
    (fun _ -> pts_to h new_cell <*> slist ptr l)
    (fun _ -> set_dummy_cell h new_cell)

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

let uncons (#a:Type) (ptr:t a) (l:list (cell a){Cons? l})
  : RST (t a * t a)
        (slist ptr l)
        (fun (hd, ptr') -> pts_to hd (L.hd l) <*> slist ptr' (L.tl l))
        (requires fun _ -> True)
        (ensures fun _ _ _ -> True)
  =
  A.reveal_array();
  let node = LowStar.Array.index ptr 0ul in
  let next = node.next in
  ptr, next

let uncons_dealloc (#a:Type) (ptr:t a) (l:list (cell a){Cons? l})
  : RST (t a)
        (slist ptr l)
        (fun ptr' -> slist ptr' (L.tl l))
        (requires fun _ -> True)
        (ensures fun _ _ _ -> True)
  =
  A.reveal_array();
  let node = LowStar.Array.index ptr 0ul in
  let next = node.next in
  rst_frame
    (pts_to ptr (L.hd l) <*> slist next (L.tl l))
    (fun _ -> slist next (L.tl l))
    (fun _ -> cell_free ptr (L.hd l));
  next

val map (#a:Type) (f:a -> a) (ptr:t a) (l:list (cell a))
  : RST unit
        (slist ptr l)
        (fun _ -> slist ptr (L.map (fun x -> ({x with data = f x.data})) l))
        (requires fun _ -> True)
        (ensures fun _ _ _ -> True)


// LowStar.Array does not yet have a notion of null pointers. In the meantime, we assume this
// stateful function. It is currently incorrect as it should be y <==> g_is_null b,
// and we will also need to change the definition of an empty node to a null array
assume
val is_null (#a:Type0) (b:LowStar.Array.array a)
  :HyperStack.ST.Stack bool (requires (fun h -> A.live h b))
                  (ensures  fun h y h' -> h == h' /\ (y <==> A.vlength b == 0))

let rec map #a f ptr l =
  A.reveal_array();
  let h0 = HyperStack.ST.get() in
  if is_null ptr then ()
  else (
    let node = LowStar.Array.index ptr 0ul in
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
      (fun _ -> map f next l_tl)
  )

type llist (a: Type0) = t a & list (cell a)

let llist_resource (#a:Type0) (x:llist a) =
  slist (fst x) (snd x)

let rec llist_view_aux (#a:Type0) (x:list (cell a)) : list a =
  match x with
  | [] -> []
  | hd::tl -> hd.data :: llist_view_aux tl

let llist_view (#a:Type0) (x:llist a) : list a =
  llist_view_aux (snd x)

let llist_cons #a x v =
  let init_ptr = fst x in
  let init_l = snd x in
  let ptr = cons_alloc init_ptr init_l v in
  (ptr, ({data = v; next = init_ptr} :: init_l))

let llist_head #a x =
  A.reveal_array();
  let init_ptr = fst x in
  let node = LowStar.Array.index init_ptr 0ul in
  node.data

let llist_tail #a x =
  let init_ptr = fst x in
  let init_l = snd x in
  (uncons_dealloc init_ptr init_l, L.tl init_l)

let rec lemma_map_view_aux (#a:Type0) (f:a -> a) (init_l:list (cell a))
  : Lemma (llist_view_aux (L.map (fun x -> ({x with data = f x.data})) init_l) ==
          L.map f (llist_view_aux init_l))
   = match init_l with
  | [] -> ()
  | hd :: tl -> lemma_map_view_aux f tl

let llist_map #a f x =
  let init_ptr = fst x in
  let init_l = snd x in
  map f init_ptr init_l;
  lemma_map_view_aux f init_l;
  (init_ptr, L.map (fun x -> ({x with data = f x.data})) init_l)
