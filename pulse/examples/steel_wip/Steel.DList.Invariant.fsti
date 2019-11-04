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
module Steel.DList.Invariant

open Steel.Liar
module L = FStar.List.Tot
module HS = FStar.HyperStack

val t (a:Type0) : Type0
val cell (a:Type0) : Type0

val prev (c:cell 'a) : t 'a
val next (c:cell 'a) : t 'a
val data (c:cell 'a) : 'a
val mk_cell (p n: t 'a) (d:'a)
  : Pure (cell 'a)
    (requires True)
    (ensures fun c ->
      prev c == p /\
      next c == n /\
      data c == d)

val hd (l:list 'a)
  : Pure 'a
  (requires
    Cons? l)
  (ensures fun x ->
    x == Cons?.hd l)

val tl (l:list 'a)
  : Pure (list 'a)
  (requires
    Cons? l)
  (ensures fun x ->
    x == Cons?.tl l)

/// Assuming a null pointer
val null_dlist (#a:Type) 
  : t a 

/// Equality on same-length pointers: an assumed primitive
val ptr_eq (#a:Type) (x y:t a)
  : Pure bool
    (requires True)
    (ensures fun b ->
      if b then x == y else x =!= y)


////////////////////////////////////////////////////////////////////////////////
//Resource invariants
////////////////////////////////////////////////////////////////////////////////

/// Pure resources
val pure (p:prop) : resource
val elim_pure (p:prop) (h:HS.mem)
  : Lemma (inv (pure p) h ==> p)

////////////////////////////////////////////////////////////////////////////////
/// Atomic pts_to resources
////////////////////////////////////////////////////////////////////////////////
val pts_to (#a:Type) (ptr:t a) (v:cell a) : resource

val pts_to_injective (#a:_) (p:t a) (v1 v2: cell a) (h:HS.mem)
  : Lemma
    (requires
      inv (pts_to p v1) h /\
      inv (pts_to p v2) h)
    (ensures
      v1 == v2)

val pts_to_non_null (#a:_) (p:t a) (v: cell a)
  : Steel unit
    (requires
      pts_to p v)
    (ensures fun _ ->
      pts_to p v)
    (requires fun _ -> True)
    (ensures fun _ _ _ ->
      p =!= null_dlist)

val read_ptr (#a:_) (ptr:t a) (c:cell a)
  : Steel (cell a)
    (requires pts_to ptr c)
    (ensures fun _ -> pts_to ptr c)
    (requires fun _ -> True)
    (ensures fun _ c' _ -> c == c')

val write_ptr (#a:_) (ptr:t a) (c0 c1:cell a)
  : St unit
    (requires
      pts_to ptr c0)
    (ensures fun _ ->
      pts_to ptr c1)

val alloc_cell (#a:_) (c:cell a)
  : Steel (t a)
    (requires
      empty_resource)
    (ensures fun p ->
      pts_to p c)
    (requires fun _ ->
      True)
    (ensures fun _ p _ ->
      p =!= null_dlist)


/// Main abstract invariant
///    A doubly linked list segment at ptr from from left to right
val dlist (#a:Type) (left ptr right:t a) (l:list (cell a)) : resource

val dlist_injective (#a:_) (left ptr right : t a)
                           (l1 l2:list (cell a))
                           (h:HS.mem)
  : Lemma
    (requires
      inv (dlist left ptr right l1) h /\
      inv (dlist left ptr right l2) h)
    (ensures
      l1 == l2)

////////////////////////////////////////////////////////////////////////////////
// dlist nil
////////////////////////////////////////////////////////////////////////////////
val intro_dlist_nil (#a:Type) (left right:t a)
   : St unit
     (requires
       empty_resource)
     (ensures fun _ ->
       dlist left right right [])

val elim_dlist_nil (#a:Type) (left ptr right:t a)
   : St unit
     (requires
       dlist left ptr right [])
     (ensures fun _ ->
       pure (right == ptr))

val invert_dlist_nil_eq (#a:Type) (left ptr right:t a) (l:list (cell a))
    : Steel unit
     (requires
       dlist left ptr right l)
     (ensures fun _ ->
       dlist left right right [])
     (requires fun _ ->
       ptr == right)
     (ensures fun _ _ _ ->
       l==[])


////////////////////////////////////////////////////////////////////////////////
// dlist cons
////////////////////////////////////////////////////////////////////////////////
val intro_dlist_cons (#a:Type) (left:t a)
                               (ptr:t a)
                               (right:t a)
                               (hd: cell a)
                               (tl: list (cell a))
   : Steel unit
     (requires
       pts_to ptr hd <*>
       dlist ptr (next hd) right tl)
     (ensures fun _ ->
       dlist left ptr right (hd::tl))
     (requires fun _ ->
       prev hd == left /\
       ptr =!= right)
     (ensures fun _ _ _ -> True)

val elim_dlist_cons (#a:Type) (left:t a)
                              (ptr:t a)
                              (right:t a)
                              (hd:cell a)
                              (tl:list (cell a))
   : Steel unit
     (requires
       dlist left ptr right (hd::tl))
     (ensures fun _ ->
       pts_to ptr hd <*>
       dlist ptr (next hd) right tl)
     (requires fun _ -> True)
     (ensures fun _ _ _ ->
       prev hd == left /\
       ptr =!= null_dlist /\
       ptr =!= right)

val invert_dlist_cons_neq (#a:Type) (left ptr right:t a) (l:list (cell a))
    : Steel unit
     (requires
       dlist left ptr right l)
     (ensures fun _ ->
       dlist left ptr right l)
     (requires fun _ ->
       ptr =!= right)
     (ensures fun _ _ _ ->
       Cons? l)


// irreducible
// let dlist_cons (#a:Type) (left:t a)
//                          (ptr:t a)
//                          (right:t a)
//                          (hd:cell a)
//                          (tl:list (cell a)) : resource =
//     pure (ptr =!= right) <*>
//     pts_to ptr hd <*>
//     pure (prev hd == left) <*>
//     dlist ptr (next hd) right tl



// #push-options "--z3rlimit_factor 20 --max_fuel 0 --initial_fuel 0 --max_ifuel 1 --initial_ifuel 1 --z3cliopt 'smt.qi.eager_threshold=100' --query_stats"
// #push-options "--log_queries"
// #restart-solver
// //#set-options "--tactic_trace_d  1"
// let new_dlist (#a:Type) (init:a)
//   : Rst (t a)
//     (requires
//       empty_resource)
//     (ensures fun ptr ->
//       dlist null_dlist ptr null_dlist [mk_cell null_dlist null_dlist init])
//   = reveal_rst_inv ();
//     // reveal_modifies ();
//     reveal_empty_resource();
//     reveal_star();
//     let cell = mk_cell null_dlist null_dlist init in
//     let h0 = FStar.HyperStack.ST.get () in
//     let p = alloc_cell cell in
//     rst_frame (pts_to p cell <*> empty_resource)
//               (fun _ -> pts_to p cell <*> dlist p null_dlist null_dlist [])
//               (fun _ -> intro_dlist_nil p null_dlist);
//     intro_dlist_cons null_dlist p null_dlist cell [];
//     resource_assertion (dlist null_dlist p null_dlist [cell]);
//     let h1 = FStar.HyperStack.ST.get () in
//     assume (modifies empty_resource (dlist null_dlist p null_dlist [cell]) h0 h1);
//     // NS: This is pretty fragile
//     //     Requires reasoning about transitivity of modifies
//     p

// assume
// val write_ptr (#a:_) (ptr:t a) (c0 c1:cell a)
//   : Rst unit
//         (requires pts_to ptr c0)
//         (ensures fun _ -> pts_to ptr c1)

// let rewrite_resource (r0 r1:resource)
//   : RST unit
//     (requires r0)
//     (ensures fun _ -> r1)
//     (requires fun _ -> r0 == r1)
//     (ensures fun _ _ _ -> True)
//   = ()

// let read_head (#a:_) (from0:t a) (ptr0:t a) (to0: t a) (hd:cell a) (tl:list (cell a))
//   : RST (cell a)
//         (requires
//           dlist from0 ptr0 to0 (hd::tl))
//         (ensures fun _ ->
//           dlist from0 ptr0 to0 (hd::tl))
//         (requires fun _ ->
//           True)
//         (ensures fun _ v _ ->
//           v == hd)
//   =  reveal_rst_inv ();
//      reveal_modifies ();
//      reveal_empty_resource();
//      reveal_star();

//      let h0 = FStar.HyperStack.ST.get () in

//      //1: unfold dlist to dlist cons
//      elim_dlist_cons from0 ptr0 to0 hd tl;

//      //2: read the ptr0 to get cell0
//      let c0 =
//        rst_frame
//          (pts_to ptr0 hd <*> dlist ptr0 (next hd) to0 tl)
//          (fun _ -> pts_to ptr0 hd <*> dlist ptr0 (next hd) to0 tl)
//          (fun _ -> read_ptr ptr0 hd) in

//      intro_dlist_cons from0 ptr0 to0 hd tl;

//      let h1 = FStar.HyperStack.ST.get () in
//      assume (modifies (dlist from0 ptr0 to0 (hd::tl))
//                       (dlist from0 ptr0 to0 (hd::tl)) h0 h1);
//      c0

// assume
// val resource_assumption (r:resource)
//   : RST unit
//         empty_resource
//         (fun _ -> r)
//         (fun _ -> True)
//         (fun _ _ _ -> True)

// #restart-solver

// let rec concat (#a:Type)
//                (from0:t a) (ptr0:t a) (to0: t a) (l0:list (cell a))
//                (from1:t a) (ptr1:t a) (l1:list (cell a))
//    : RST (list (cell a))
//      (requires
//        dlist from0 ptr0 to0 l0 <*>
//        dlist from1 ptr1 null_dlist l1)
//      (ensures fun l ->
//        dlist from0 ptr0 null_dlist l)
//      (requires fun _ -> Cons? l0 /\ Cons? l1)
//      (ensures fun _ _ _ -> True)
//    =
//      let h0 = FStar.HyperStack.ST.get () in
//      reveal_rst_inv ();
//      reveal_modifies ();
//      reveal_empty_resource();
//      reveal_star();


//      let l = l0@l1 in

//      //not naming these leads to unification failures in rst_frame
//      let hd0 = hd l0 in
//      let tl0 = tl l0 in

//      let hd1 = hd l1 in
//      let tl1 = tl l1 in
//      let to1 = null_dlist in

//      //1: read the ptr0 to get cell0
//      let c0 =
//        rst_frame
//          (dlist from0 ptr0 to0 (hd0 :: tl0) <*> dlist from1 ptr1 to1 l1)
//          (fun _ -> dlist from0 ptr0 to0 (hd0 :: tl0) <*> dlist from1 ptr1 to1 l1)
//          (fun _ -> read_head from0 ptr0 to0 hd0 tl0)
//      in


//      //2: unfold dlist to dlist cons
//      rst_frame
//        (dlist from0 ptr0 to0 (hd0 :: tl0) <*> dlist from1 ptr1 to1 l1)
//        (fun _ -> pts_to ptr0 hd0 <*> dlist ptr0 (next hd0) to0 tl0 <*> dlist from1 ptr1 to1 l1) //<--
//        (fun _ -> elim_dlist_cons from0 ptr0 to0 hd0 tl0);

//      let l =
//      if ptr_eq (next c0) to0
//      then begin //we are at the end of l0
//        // 3. invert dlist tl0 to dlist []
//        rst_frame
//          (pts_to ptr0 hd0 <*> dlist ptr0 (next hd0) to0 tl0 <*> dlist from1 ptr1 to1 l1)
//          (fun _ -> pts_to ptr0 hd0 <*> dlist ptr0 to0 to0 [] <*> dlist from1 ptr1 to1 l1)
//          (fun _ -> invert_dlist_nil_eq ptr0 ptr0 (next hd0) to0 tl0);

//        // This is a long-winded way of saying:
//        //   p0.next <- p1
//        let c0' = mk_cell (prev c0) ptr1 (data c0) in
//        rst_frame
//            (pts_to ptr0 hd0 <*> dlist from1 ptr1 to1 l1)
//            (fun _ -> pts_to ptr0 c0' <*> dlist from1 ptr1 to1 l1)
//            (fun _ -> write_ptr ptr0 hd0 c0');


//        let c1 =
//          rst_frame
//            (pts_to ptr0 c0' <*> dlist from1 ptr1 to1 (hd1::tl1))
//            (fun _ -> pts_to ptr0 c0' <*> dlist from1 ptr1 to1 (hd1::tl1))
//            (fun _ -> read_head from1 ptr1 to1 hd1 tl1) in


//        rst_frame
//            (pts_to ptr0 c0' <*> dlist from1 ptr1 to1 (hd1::tl1))
//            (fun _ -> pts_to ptr0 c0' <*> pts_to ptr1 hd1 <*> dlist ptr1 (next hd1) to1 tl1)
//            (fun _ -> elim_dlist_cons from1 ptr1 to1 hd1 tl1);

//        // This is a long-winded way of saying:
//        //   p1.prev <- p0
//        let c1' = mk_cell ptr0 (next c1) (data c1) in
//        rst_frame
//            (pts_to ptr0 c0' <*> pts_to ptr1 hd1 <*> dlist ptr1 (next hd1) to1 tl1)
//            (fun _ -> pts_to ptr0 c0' <*> pts_to ptr1 c1' <*> dlist ptr1 (next hd1) to1 tl1)
//            (fun _ -> write_ptr ptr1 hd1 c1');

//        rst_frame
//            (pts_to ptr0 c0' <*> pts_to ptr1 c1' <*> dlist ptr1 (next c1') to1 tl1)
//            (fun _ -> pts_to ptr0 c0' <*> dlist ptr0 ptr1 to1 (c1'::tl1))
//            (fun _ -> intro_dlist_cons ptr0 ptr1 to1 c1' tl1);

//        intro_dlist_cons from0 ptr0 to1 c0' (c1'::tl1);

//        let l = c0'::c1'::tl1 in
//        l
//      end
//      else begin
//        //pts_to ptr0 hd0 <*> dlist ptr0 (next hd0) to0 tl0 <*> dlist from1 ptr1 to1 l1
//        //next c0 =!= t0
//        rst_frame
//           (pts_to ptr0 hd0 <*> dlist ptr0 (next c0) to0 tl0 <*> dlist from1 ptr1 null_dlist l1)
//           (fun _ -> pts_to ptr0 hd0 <*> dlist ptr0 (next c0) to0 tl0 <*> dlist from1 ptr1 null_dlist l1)
//           (fun _ -> invert_dlist_cons_neq ptr0 (next c0) to0 tl0);

//        let l =
//          rst_frame
//            (pts_to ptr0 hd0 <*> dlist ptr0 (next c0) to0 tl0 <*> dlist from1 ptr1 null_dlist l1)
//            (fun l -> pts_to ptr0 hd0 <*> dlist ptr0 (next c0) null_dlist l)
//            (fun _ -> concat ptr0 (next c0) to0 tl0 from1 ptr1 l1)
//        in
//        intro_dlist_cons from0 ptr0 null_dlist hd0 l;
//        resource_assertion (dlist from0 ptr0 to1 (hd0::l));
//        let l = hd0::l in
//        l
//      end
//      in
//      resource_assertion (dlist from0 ptr0 null_dlist l);
//      let h1 = FStar.HyperStack.ST.get () in
//      assume (modifies (dlist from0 ptr0 to0 l0 <*> dlist from1 ptr1 null_dlist l1)
//                       (dlist from0 ptr0 null_dlist l)
//                       h0 h1);
//      l
