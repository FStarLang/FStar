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
module LowStar.RST.DList

open FStar.HyperStack.ST
module HS = FStar.HyperStack
module L = FStar.List.Tot
module A = LowStar.Array
module RA = LowStar.RST.Array

open LowStar.Resource
open LowStar.RST
module P = LowStar.Permissions

//open LowStar.BufferOps
//open LowStar.RST.LinkedList.Base

#reset-options "--__no_positivity --use_two_phase_tc true"


(* The definition of linked lists comes from kremlin/test/LinkedList4.fst *)

/// We revisit the classic example of lists, but in a low-level
/// setting, using linked lists. This second version uses
/// `B.pointer_or_null`, the type of buffers of length 1 or 0.
noeq
type t (a: Type0) =
  b:A.array (cell a){A.vlength b <= 1}

and cell (a: Type0) = {
  prev: t a;
  next: t a;
  data: a;
}

assume HasEqT : forall a.{:pattern (hasEq (t a))} hasEq (t a)

let ptr a : eqtype = t a

(* Ideally, this would be bootstrapped for clients to use a "t' a".
   The hidden (abstract) type definition would be a (t a) & list (cell a) *)

let empty_inv (#a:Type) (#ptr:t a) (s:rmem (RA.array_resource ptr)) =
  A.vlength ptr == 0

let node_inv (#a:Type) (#ptr:t a) (s:rmem (RA.array_resource ptr)) =
  P.allows_write (RA.get_rperm ptr s) /\ A.vlength ptr == 1 /\ A.freeable ptr

irreducible
let pts_to (#a:Type) (ptr:t a) (v:cell a) : resource =
  hsrefine (RA.array_resource ptr) (fun (s:rmem (RA.array_resource ptr)) -> 
    node_inv s /\ 
    Seq.index (RA.as_rseq ptr s) 0 == v)

irreducible
let pure (p:prop) : resource = hsrefine empty_resource (fun _ -> p)

// dlist (ptr, left, 

// left ---> {_; prev=_; next=_} 
     
//[@(strict_on_arguments [4])]
irreducible
let rec dlist (#a:Type) (left:t a) 
                        (ptr:t a)
                        (right:t a)
                        (l:list (cell a)) 
    : Tot resource
      (decreases l) 
    =
    match l with
    | [] -> pure (right == ptr)
    | hd :: tl -> 
      pure (ptr =!= right) <*>
      pts_to ptr hd <*> 
      pure (hd.prev == left) <*>
      dlist ptr hd.next right tl

// //[@(strict_on_arguments [4])]
// irrelet dlist (#a:Type) (left:t a) 
//                     (ptr:t a)
//                     (right:t a)
//                     (l:list (cell a)) =
//     dlist' left ptr right l

effect Rst (a:Type) (pre:resource) (post: a -> resource) = 
  RST a pre post (fun _ -> True) (fun _ _ _ -> True)

let unfold_dlist_nil (#a:Type) (left:t a) 
                                (ptr:t a)
                                (right:t a)
                                (l:list (cell a){Nil? l})
   : Rst unit                           
     (dlist left ptr right l)
     (fun _ -> 
       pure (right == ptr))
   = admit()       


irreducible
let dlist_cons (#a:Type) (left:t a) 
                         (ptr:t a)
                         (right:t a)
                         (l:list (cell a){Cons? l}) : resource =
    let hd = Cons?.hd l in
    pure (ptr =!= right) <*>
    pts_to ptr hd <*> 
    pure (hd.prev == left) <*>
    dlist ptr hd.next right (Cons?.tl l)
                         
let unfold_dlist_cons (#a:Type) (left:t a) 
                                (ptr:t a)
                                (right:t a)
                                (l:list (cell a){Cons? l})
   : Rst unit                           
     (requires
       dlist left ptr right l)
     (ensures fun _ -> 
       dlist_cons left ptr right l)
   = admit()       

let read_ptr (#a:_) (left ptr right:t a) (l:list (cell a){Cons? l})
  : RST (cell a)
    (dlist_cons left ptr right l)
    (fun _ -> 
      pts_to ptr (Cons?.hd l))
    (requires fun _ -> True)
    (ensures fun _ v _ ->  v == Cons?.hd l)
  = admit();
    reveal_rst_inv ();
    reveal_modifies ();
    RA.index ptr 0ul
    
  
assume val null_dlist (#a:Type) : t a

let resource_assertion (r:resource) 
  : RST unit
        r
        (fun _ -> r)
        (fun _ -> True)
        (fun _ _ _ -> True)
  = ()        

let new_dlist (#a:Type) (left:t a) (init:a) (right: t a)
  : Rst (t a)
    (requires empty_resource)
    (ensures fun ptr ->
      dlist left ptr right [{prev = left;
                             next = right;
                             data = init}])
  = reveal_rst_inv ();
    reveal_modifies ();
    reveal_empty_resource();
    reveal_star();
    let cell = {
        prev = left;
        next = right;
        data = init
    } in
    // let h0 = FStar.HyperStack.ST.get () in      
    let p = RA.alloc cell 1ul in
    assume (p =!= right);
    // let h1 = FStar.HyperStack.ST.get () in    
    // resource_assertion (pts_to p cell <*> pure (cell.prev == null_dlist));
    // resource_assertion (pts_to p cell <*> dlist p null_dlist null_dlist []);
    // resource_assertion (pts_to p cell <*> pure (cell.prev == null_dlist) <*> dlist p null_dlist null_dlist []);    
    // assert (dlist null_dlist p null_dlist [cell] ==
    //         (pts_to p cell <*> pure (cell.prev == null_dlist) <*> dlist p null_dlist null_dlist []));
    // resource_assertion (dlist null_dlist p null_dlist [cell]);
    // let h2 = FStar.HyperStack.ST.get () in
    // assert (as_loc (fp (dlist null_dlist p null_dlist [cell])) h2 ==
    //         as_loc (fp (pts_to p cell)) h2);
    // assert (modifies empty_resource (pts_to p cell) h0 h1);
    // assert (modifies empty_resource (dlist null_dlist p null_dlist [cell]) h0 h1);
    // NS: This is pretty fragile
    //     Requires reasoning about transitivity of modifies
    p

#set-options "--tactic_trace_d  1"
let rec concat (#a:Type)
               (from0:t a) (ptr0:t a) (to0: t a) (l0:list (cell a))
               (from1:t a) (ptr1:t a) (to1: t a) (l1:list (cell a))
   : RST unit                     
     (requires 
       dlist from0 ptr0 to0 l0 <*>
       dlist from1 ptr1 to1 l1)
     (ensures fun _ ->
       dlist from0 ptr0 to1 (l0@l1))
     (requires fun _ -> Cons? l0)
     (ensures fun _ _ _ -> True)
  =  reveal_rst_inv ();
     reveal_modifies ();
     reveal_empty_resource();
     reveal_star();
     if ptr0 = to0
     then assert false
     else 
       let c0 = RA.index ptr0 0ul in
       if c0.next = to0
       then //last node in l0 ...here's where we hook it up
            begin
            assert (Nil? (Cons?.tl l0));
            let _ = 
              rst_frame
                (dlist from0 ptr0 to0 l0 <*> dlist from1 ptr1 to1 l1)
                (fun _ -> dlist_cons from0 ptr0 to0 l0 <*> dlist from1 ptr1 to1 l1)
                (fun _ -> unfold_dlist_cons from0 ptr0 to0 l0)
            in
            // let c1 = 
            //   rst_frame
            //     (dlist_cons from0 ptr0 to0 l0 <*> dlist from1 ptr1 to1 l1)
            //     (fun _ -> dlist_cons from0 ptr0 to0 l0 <*> dlist from1 ptr1 to1 l1)
            //     (fun _ -> read_ptr ptr0 l0) in
            admit()
            // RA.upd c0.next 0ul c1;
            // RA.upd c1.prev 0ul c0;
            // admit()
       end
       else admit()
            
       
       

     // end
     // else admit()


// // let splice (#a:Type) (left0:t a) (ptr0:t a) (right0: t a) (l0:list a) 
// //                      (left1:t a) (ptr1:t a) (right1: t a) (l1:list a)
// //   : Rst unit      
// //     (requires
// //       dlist left0 ptr0 right0 l0 <*>
// //       dlist left1 ptr1 right1 l1)

// let make_two (#a:Type) (left:t a) (ptr:t a) (right: t a) (c0:cell a) (v:a)
//   : RST (list (cell a))
//     (requires
//        dlist left ptr right [c0])
//     (ensures fun l  ->
//       dlist left ptr right l)
//     (requires fun _ -> True)
//     (ensures fun _ l _ -> 
//       match l with 
//       | [c0'; c1] -> c0.data == c0.data /\ c1.data == v
//       | _ -> False)
//   = let hd = RA.index ptr 0ul in
//     let new_l = 
//         new_dlist ptr v right
//     in
//     RA.upd hd.next 0ul new_cell

  
//   admit()
  
// let insert_after (#a:Type) (left:t a) (ptr:t a) (right: t a{ptr =!= right)) (l:list (cell a)) (v:a)
//   : Rst unit
//     (requires 
//       dlist left ptr right l)
//     (ensures fun _ -> 
//       let hd::tl = l in
//       let new_cell = {
//           data = init;
//        }
//       in
//       dlist left ptr right (hd::
//       empty_resource)
//       // let c_v = { data = v; prev = left; next = ptr} in
//       // dlist left ptr right (c_v :: l))
//   = reveal_rst_inv ();
//     reveal_modifies ();
//     reveal_empty_resource();
//     reveal_star();
//     let hd = RA.index ptr 0ul in
//     let new_cell = 
//            RA.alloc ({
//              data = init;
//              prev = ptr;
//              next = hd.next;
//            })
//     in
//     RA.upd ptr.next 0ul new_cell;
//     if hd.next = right then ()
//     else begin
//       admit();
//       let next_cell = RA.index hd.next 0ul in
//       RA.upd next_cell.prev 0ul new_cell
//     end


          
//            new_dlist init in
//          RA.upd new_cell.prev :=
    
//       dlist null_dlist ptr null_dlist [{prev = null_dlist;
//                                         next = null_dlist;
//                                         data = init}])




// abstract
// let dummy_cell (#a:Type) (ptr:t a) : resource =
//   hsrefine (RA.array_resource ptr) node_inv

// let cell_alloc (#a:Type)
//               (init:cell a)
//             : RST (t a) (empty_resource)
//                         (fun ptr -> pts_to ptr init)
//                         (fun _ -> True)
//                         (fun _ ptr h1 -> True) =
//   reveal_rst_inv ();
//   reveal_modifies ();
//   RA.alloc init 1ul


// let cell_free (#a:Type)
//               (ptr:t a)
//               (v:cell a)
//            : RST unit (pts_to ptr v)
//                       (fun ptr -> empty_resource)
//                       (fun _ -> True)
//                       (fun _ ptr h1 -> True) =
//   reveal_rst_inv ();
//   reveal_modifies ();
//   reveal_empty_resource ();
//   RA.free ptr

// let set_dummy_cell (#a:Type) (ptr:t a) (c:cell a)
//   : RST unit
//     (dummy_cell ptr)
//     (fun _ -> pts_to ptr c)
//     (fun _ -> True)
//     (fun _ _ _ -> True)
//   = reveal_rst_inv();
//     reveal_modifies();
//     RA.upd ptr 0ul c

// let set_cell (#a:Type) (ptr:t a) (c:cell a) (v:a)
//   : RST unit
//     (pts_to ptr c)
//     (fun _ -> pts_to ptr ({c with data = v}))
//     (fun _ -> True)
//     (fun _ _ _ -> True)
//   = reveal_rst_inv();
//     reveal_modifies();
//     let h0 = HyperStack.ST.get() in
//     let node = RA.index ptr 0ul in
//     let node' = {node with data = v} in
//     let h0' = HyperStack.ST.get() in
//     RA.upd ptr 0ul node';
//     let h1 = HyperStack.ST.get() in
//     // Unclear why modifies_trans does not trigger automatically
//     assert (modifies (pts_to ptr c) (pts_to ptr c) h0 h0');
//     assert (modifies (pts_to ptr c) (pts_to ptr node') h0' h1)

// #reset-options "--z3rlimit 20 --max_fuel 1 --max_ifuel 1 --z3cliopt smt.QI.EAGER_THRESHOLD=2"

// (* We provide two versions of cons.
//    The first one assumes there is an unused (dummy) node, that we can just set to be the head.
//    The second performs an allocation *)

// let cons (#a:Type) (ptr:t a) (l:list (cell a)) (h:t a) (v:a) (x:a)
//   : RST unit
//   (dummy_cell h <*> slist ptr l)
//   (fun _ -> slist h ({data = v; next = ptr} :: l))
//   (fun _ -> True)
//   (fun _ _ _ -> True) =
//   let new_cell = {data = v; next = ptr} in
//   rst_frame
//     (dummy_cell h <*> slist ptr l)
//     (fun _ -> pts_to h new_cell <*> slist ptr l)
//     (fun _ -> set_dummy_cell h new_cell)

// let cons_alloc (#a:Type) (ptr:t a) (l:list (cell a)) (v:a)
//   : RST (t a)
//   (slist ptr l)
//   (fun ptr' -> slist ptr' ({data = v; next = ptr} :: l))
//   (fun _ -> True)
//   (fun _ _ _ -> True) =
//   let new_cell = {data = v; next = ptr} in
//   let new_head = rst_frame
//     (slist ptr l)
//     #_ #_
//     (fun ret -> pts_to ret new_cell <*> slist ptr l)
//     #_
//     #(slist ptr l)
//     (fun _ -> cell_alloc new_cell)
//   in
//   new_head

// (* Similarly, we provide two versions of uncons.
//    The second deallocates the node currently in head position, while the first
//    returns the head and the tail *)

// let uncons (#a:Type) (ptr:t a) (l:list (cell a){Cons? l})
//   : RST (t a * t a)
//         (slist ptr l)
//         (fun (hd, ptr') -> pts_to hd (L.hd l) <*> slist ptr' (L.tl l))
//         (requires fun _ -> True)
//         (ensures fun _ _ _ -> True)
//   =
//   RA.reveal_array();
//   let node = LowStar.Array.index ptr 0ul in
//   let next = node.next in
//   ptr, next

// let uncons_dealloc (#a:Type) (ptr:t a) (l:list (cell a){Cons? l})
//   : RST (t a)
//         (slist ptr l)
//         (fun ptr' -> slist ptr' (L.tl l))
//         (requires fun _ -> True)
//         (ensures fun _ _ _ -> True)
//   =
//   RA.reveal_array();
//   let node = LowStar.Array.index ptr 0ul in
//   let next = node.next in
//   rst_frame
//     (pts_to ptr (L.hd l) <*> slist next (L.tl l))
//     (fun _ -> slist next (L.tl l))
//     (fun _ -> cell_free ptr (L.hd l));
//   next

// val map (#a:Type) (f:a -> a) (ptr:t a) (l:list (cell a))
//   : RST unit
//         (slist ptr l)
//         (fun _ -> slist ptr (L.map (fun x -> ({x with data = f x.data})) l))
//         (requires fun _ -> True)
//         (ensures fun _ _ _ -> True)


// // LowStar.Array does not yet have a notion of null pointers. In the meantime, we assume this
// // stateful function. It is currently incorrect as it should be y <==> g_is_null b, 
// // and we will also need to change the definition of an empty node to a null array
// assume
// val is_null (#a:Type0) (b:LowStar.Array.array a)
//   :HyperStack.ST.Stack bool (requires (fun h -> A.live h b))
//                   (ensures  fun h y h' -> h == h' /\ (y <==> A.vlength b == 0))

// let rec map #a f ptr l =
//   RA.reveal_array();
//   let h0 = HyperStack.ST.get() in
//   if is_null ptr then ()
//   else (
//     let node = LowStar.Array.index ptr 0ul in
//     let next = node.next in
//     let l_tl = L.tl l in
//     rst_frame
//       (pts_to ptr node <*> slist next l_tl)
//       (fun _ -> pts_to ptr ({node with data = f node.data}) <*> slist next l_tl)
//       (fun _ -> set_cell ptr node (f node.data));
//     rst_frame
//       (pts_to ptr ({node with data = f node.data}) <*> slist next l_tl)
//       (fun _ -> pts_to ptr ({node with data = f node.data}) <*>
//              slist next (L.map (fun x -> ({x with data = f x.data})) l_tl))
//       (fun _ -> map f next l_tl)
//   )

// type llist (a: Type0) = t a & list (cell a)

// let llist_resource (#a:Type0) (x:llist a) =
//   slist (fst x) (snd x)

// let rec llist_view_aux (#a:Type0) (x:list (cell a)) : list a =
//   match x with
//   | [] -> []
//   | hd::tl -> hd.data :: llist_view_aux tl

// let llist_view (#a:Type0) (x:llist a) : list a =
//   llist_view_aux (snd x)

// let llist_cons #a x v =
//   let init_ptr = fst x in
//   let init_l = snd x in
//   let ptr = cons_alloc init_ptr init_l v in
//   (ptr, ({data = v; next = init_ptr} :: init_l))

// let llist_head #a x =
//   RA.reveal_array();
//   let init_ptr = fst x in
//   let node = LowStar.Array.index init_ptr 0ul in
//   node.data

// let llist_tail #a x =
//   let init_ptr = fst x in
//   let init_l = snd x in
//   (uncons_dealloc init_ptr init_l, L.tl init_l)

// let rec lemma_map_view_aux (#a:Type0) (f:a -> a) (init_l:list (cell a))
//   : Lemma (llist_view_aux (L.map (fun x -> ({x with data = f x.data})) init_l) ==
//           L.map f (llist_view_aux init_l))
//    = match init_l with
//   | [] -> ()
//   | hd :: tl -> lemma_map_view_aux f tl

// let llist_map #a f x =
//   let init_ptr = fst x in
//   let init_l = snd x in
//   map f init_ptr init_l;
//   lemma_map_view_aux f init_l;
//   (init_ptr, L.map (fun x -> ({x with data = f x.data})) init_l)
