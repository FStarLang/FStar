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

effect Rst (a:Type) (pre:resource) (post: a -> resource) = 
  RST a pre post (fun _ -> True) (fun _ _ _ -> True)

#push-options "--__no_positivity"
noeq
type t (a: Type0) =
  b:A.array (cell a){A.vlength b <= 1}

and cell (a: Type0) = {
  prev: t a;
  next: t a;
  data: a;
}
#pop-options

irreducible
let hd (l:list 'a)
  : Pure 'a
  (requires
    Cons? l)
  (ensures fun x -> 
    x == Cons?.hd l)
  = Cons?.hd l

irreducible
let tl (l:list 'a)
  : Pure (list 'a)
  (requires
    Cons? l)
  (ensures fun x -> 
    x == Cons?.tl l)
  = Cons?.tl l

irreducible
let prev (c:cell 'a) : t 'a = c.prev

irreducible
let next (c:cell 'a) : t 'a = c.next

irreducible
let data (c:cell 'a) : 'a = c.data

assume
val mk_cell (p n: t 'a) (d:'a) 
  : Pure (cell 'a)
    (requires True)
    (ensures fun c -> 
      prev c == p /\
      next c == n /\
      data c == d)

    
assume
val ptr_eq (#a:Type) (x y:t a)
  : Pure bool
    (requires True)
    (ensures fun b ->
      if b then x == y else x =!= y)
    
let node_inv (#a:Type) (#ptr:t a) (s:rmem (RA.array_resource ptr)) =
  P.allows_write (RA.get_rperm ptr s) /\ A.vlength ptr == 1 /\ A.freeable ptr

irreducible
let pts_to (#a:Type) (ptr:t a) (v:cell a) : resource =
  hsrefine (RA.array_resource ptr) (fun (s:rmem (RA.array_resource ptr)) -> 
    node_inv s /\ 
    Seq.index (RA.as_rseq ptr s) 0 == v)

irreducible
let pure (p:prop) : resource = hsrefine empty_resource (fun _ -> p)

assume
val elim_pure (p:prop) (h:HS.mem)
  : Lemma (inv (pure p) h ==> p)

assume val null_dlist (#a:Type) : t a
   
irreducible
let rec dlist (#a:Type) (left:t a) 
                        (ptr:t a)
                        (right:t a)
                        (l:list (cell a)) 
    : Tot resource
      (decreases l) 
    =
    match l with
    | [] -> 
      pure (right == ptr)
            
    | hd :: tl -> 
      pure (right =!= ptr) <*>
      pts_to ptr hd <*> 
      pure (hd.prev == left) <*>
      dlist ptr hd.next right tl

assume
val pts_to_injective (#a:_) (p:t a) (v1 v2: cell a) (h:HS.mem)
  : Lemma 
    (requires
      inv (pts_to p v1) h /\
      inv (pts_to p v2) h)
    (ensures
      v1 == v2)


assume
val pts_to_non_null_lemma (#a:_) (p:t a) (v: cell a) (h:HS.mem)
  : Lemma
    (requires
      inv (pts_to p v) h)
    (ensures
      p =!= null_dlist)

let pts_to_non_null (#a:_) (p:t a) (v: cell a)
  : RST unit
    (requires
      pts_to p v)
    (ensures fun _ ->
      pts_to p v)
    (requires fun _ -> True)
    (ensures fun _ _ _ -> 
      p =!= null_dlist)
  = let h = FStar.HyperStack.ST.get () in
    pts_to_non_null_lemma p v h


let rec dlist_injective #a (left ptr right : t a)
                           (l1 l2:list (cell a))
                           (h:HS.mem)
  : Lemma
    (requires 
      inv (dlist left ptr right l1) h /\
      inv (dlist left ptr right l2) h)    
    (ensures
      l1 == l2)
   (decreases l1)
  = admit();
  match l1, l2 with
  | [], [] -> ()
  | hd1::tl1, hd2::tl2 -> 
    pts_to_injective ptr hd1 hd2 h; 
    assert (hd1 == hd2);
    dlist_injective ptr hd1.next right tl1 tl2 h
      
  | [], hd::tl
  | hd::tl, [] ->
    elim_pure (right == ptr) h;
    elim_pure (right =!= ptr) h


assume
val intro_dlist_nil (#a:Type) (left right:t a) 
   : Rst unit                           
     (requires
       empty_resource)
     (ensures fun _ -> 
       dlist left right right [])

assume
val invert_dlist_nil_eq (#a:Type) (left left' ptr right:t a) (l:list (cell a)) 
    : RST unit                           
     (requires
       dlist left ptr right l)
     (ensures fun _ -> 
       dlist left' right right [])
     (requires fun _ -> 
       ptr == right)
     (ensures fun _ _ _ -> 
       l==[])

assume
val invert_dlist_cons_neq (#a:Type) (left ptr right:t a) (l:list (cell a)) 
    : RST unit                           
     (requires
       dlist left ptr right l)
     (ensures fun _ -> 
       dlist left ptr right l)
     (requires fun _ -> 
       ptr =!= right)
     (ensures fun _ _ _ -> 
       Cons? l)


assume
val elim_dlist_nil (#a:Type) (left:t a) 
                             (ptr:t a)
                             (right:t a)
                             (l:list (cell a){Nil? l})
   : Rst unit                           
     (requires 
       dlist left ptr right l)
     (ensures fun _ -> 
       pure (right == ptr))


let b2p (b:bool) : prop = b == true
irreducible
let dlist_cons (#a:Type) (left:t a) 
                         (ptr:t a)
                         (right:t a)
                         (hd:cell a)
                         (tl:list (cell a)) : resource =
    pure (ptr =!= right) <*>
    pts_to ptr hd <*> 
    pure (prev hd == left) <*>
    dlist ptr (next hd) right tl

assume
val intro_dlist_cons (#a:Type) (left:t a) 
                               (ptr:t a)
                               (right:t a)
                               (hd: cell a)
                               (tl: list (cell a))
   : RST unit                           
     (requires
       pts_to ptr hd <*>
       dlist ptr (next hd) right tl)
     (ensures fun _ -> 
       dlist left ptr right (hd::tl))
     (requires fun _ ->
       prev hd == left /\
       ptr =!= right)
     (ensures fun _ _ _ -> True)

assume
val elim_dlist_cons (#a:Type) (left:t a) 
                              (ptr:t a)
                              (right:t a)
                              (hd:cell a)
                              (tl:list (cell a))
   : RST unit                           
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

assume
val read_ptr (#a:_) (ptr:t a) (c:cell a)
  : RST (cell a)
        (requires pts_to ptr c)
        (ensures fun _ -> pts_to ptr c)
        (requires fun _ -> True)
        (ensures fun _ c' _ -> c == c')
    


assume
val alloc_cell (#a:_) (c:cell a)
  : RST (t a)
    (requires
      empty_resource)
    (ensures fun p ->
      pts_to p c)
    (requires fun _ -> 
      True)
    (ensures fun _ p _ -> 
      p =!= null_dlist)

let resource_assertion (r:resource) 
  : RST unit
        r
        (fun _ -> r)
        (fun _ -> True)
        (fun _ _ _ -> True)
  = ()        

//#set-options "--tactic_trace_d  1"
let new_dlist (#a:Type) (init:a)
  : Rst (t a)
    (requires
      empty_resource)
    (ensures fun ptr ->
      dlist null_dlist ptr null_dlist [mk_cell null_dlist null_dlist init])
  = reveal_rst_inv ();
    reveal_modifies ();
    reveal_empty_resource();
    reveal_star();
    let cell = mk_cell null_dlist null_dlist init in
    let h0 = FStar.HyperStack.ST.get () in      
    let p = alloc_cell cell in
    rst_frame (pts_to p cell <*> empty_resource)
              (fun _ -> pts_to p cell <*> dlist p null_dlist null_dlist [])
              (fun _ -> intro_dlist_nil p null_dlist);
    intro_dlist_cons null_dlist p null_dlist cell [];
    resource_assertion (dlist null_dlist p null_dlist [cell]);
    let h1 = FStar.HyperStack.ST.get () in
    assume (modifies empty_resource (dlist null_dlist p null_dlist [cell]) h0 h1);
    // NS: This is pretty fragile
    //     Requires reasoning about transitivity of modifies
    p

assume
val write_ptr (#a:_) (ptr:t a) (c0 c1:cell a)
  : Rst unit
        (requires pts_to ptr c0)
        (ensures fun _ -> pts_to ptr c1)

let rewrite_resource (r0 r1:resource)
  : RST unit
    (requires r0)
    (ensures fun _ -> r1)
    (requires fun _ -> r0 == r1)
    (ensures fun _ _ _ -> True)
  = ()

let read_head (#a:_) (from0:t a) (ptr0:t a) (to0: t a) (hd:cell a) (tl:list (cell a))
  : RST (cell a)
        (requires 
          dlist from0 ptr0 to0 (hd::tl))
        (ensures fun _ ->
          dlist from0 ptr0 to0 (hd::tl))
        (requires fun _ -> 
          True)
        (ensures fun _ v _ -> 
          v == hd)
  =  reveal_rst_inv ();
     reveal_modifies ();
     reveal_empty_resource();
     reveal_star();

     let h0 = FStar.HyperStack.ST.get () in
     
     //1: unfold dlist to dlist cons
     elim_dlist_cons from0 ptr0 to0 hd tl;

     //2: read the ptr0 to get cell0
     let c0 =
       rst_frame
         (pts_to ptr0 hd <*> dlist ptr0 (next hd) to0 tl)
         (fun _ -> pts_to ptr0 hd <*> dlist ptr0 (next hd) to0 tl)
         (fun _ -> read_ptr ptr0 hd) in

     intro_dlist_cons from0 ptr0 to0 hd tl;

     let h1 = FStar.HyperStack.ST.get () in
     assume (modifies (dlist from0 ptr0 to0 (hd::tl))
                      (dlist from0 ptr0 to0 (hd::tl)) h0 h1);
     c0

assume 
val resource_assumption (r:resource) 
  : RST unit
        empty_resource
        (fun _ -> r)
        (fun _ -> True)
        (fun _ _ _ -> True)

#push-options "--z3rlimit_factor 3 --max_fuel 2 --initial_fuel 2 --max_ifuel 2 --initial_ifuel 2 --z3cliopt 'smt.qi.eager_threshold=100'"
let rec concat (#a:Type)
               (from0:t a) (ptr0:t a) (to0: t a) (l0:list (cell a))
               (from1:t a) (ptr1:t a) (l1:list (cell a))
   : RST (list (cell a))
     (requires 
       dlist from0 ptr0 to0 l0 <*>
       dlist from1 ptr1 null_dlist l1)
     (ensures fun l ->
       dlist from0 ptr0 null_dlist l)
     (requires fun _ -> Cons? l0 /\ Cons? l1)
     (ensures fun _ _ _ -> True)
  =  reveal_rst_inv ();
     reveal_modifies ();
     reveal_empty_resource();
     reveal_star();
     let h0 = FStar.HyperStack.ST.get () in

     let l = l0@l1 in

     //not naming these leads to unification failures in rst_frame
     let hd0 = hd l0 in
     let tl0 = tl l0 in
     
     let hd1 = hd l1 in
     let tl1 = tl l1 in
     let to1 = null_dlist in

     //1: read the ptr0 to get cell0
     let c0 = 
       rst_frame
         (dlist from0 ptr0 to0 (hd0 :: tl0) <*> dlist from1 ptr1 to1 l1)
         (fun _ -> dlist from0 ptr0 to0 (hd0 :: tl0) <*> dlist from1 ptr1 to1 l1)
         (fun _ -> read_head from0 ptr0 to0 hd0 tl0)
     in


     //2: unfold dlist to dlist cons
     rst_frame
       (dlist from0 ptr0 to0 (hd0 :: tl0) <*> dlist from1 ptr1 to1 l1)
       (fun _ -> pts_to ptr0 hd0 <*> dlist ptr0 (next hd0) to0 tl0 <*> dlist from1 ptr1 to1 l1) //<--
       (fun _ -> elim_dlist_cons from0 ptr0 to0 hd0 tl0);

     if ptr_eq (next c0) to0
     then begin //we are at the end of l0
       // 3. invert dlist tl0 to dlist []
       rst_frame
         (pts_to ptr0 hd0 <*> dlist ptr0 (next hd0) to0 tl0 <*> dlist from1 ptr1 to1 l1)
         (fun _ -> pts_to ptr0 hd0 <*> dlist ptr0 to0 to0 [] <*> dlist from1 ptr1 to1 l1)
         (fun _ -> invert_dlist_nil_eq ptr0 ptr0 (next hd0) to0 tl0);

     
       // This is a long-winded way of saying:
       //   p0.next <- p1
       let c0' = mk_cell (prev c0) ptr1 (data c0) in
       rst_frame 
           (pts_to ptr0 hd0 <*> dlist from1 ptr1 to1 l1)       
           (fun _ -> pts_to ptr0 c0' <*> dlist from1 ptr1 to1 l1)
           (fun _ -> write_ptr ptr0 hd0 c0');

       let c1 =
         rst_frame 
           (pts_to ptr0 c0' <*> dlist from1 ptr1 to1 (hd1::tl1))
           (fun _ -> pts_to ptr0 c0' <*> dlist from1 ptr1 to1 (hd1::tl1))
           (fun _ -> read_head from1 ptr1 to1 hd1 tl1) in

       rst_frame
           (pts_to ptr0 c0' <*> dlist from1 ptr1 to1 (hd1::tl1))
           (fun _ -> pts_to ptr0 c0' <*> pts_to ptr1 hd1 <*> dlist ptr1 (next hd1) to1 tl1)
           (fun _ -> elim_dlist_cons from1 ptr1 to1 hd1 tl1);

       // This is a long-winded way of saying:
       //   p1.prev <- p0
       let c1' = mk_cell ptr0 (next c1) (data c1) in
       rst_frame 
           (pts_to ptr0 c0' <*> pts_to ptr1 hd1 <*> dlist ptr1 (next hd1) to1 tl1)       
           (fun _ -> pts_to ptr0 c0' <*> pts_to ptr1 c1' <*> dlist ptr1 (next hd1) to1 tl1)
           (fun _ -> write_ptr ptr1 hd1 c1');

       rst_frame 
           (pts_to ptr0 c0' <*> pts_to ptr1 c1' <*> dlist ptr1 (next c1') to1 tl1)
           (fun _ -> pts_to ptr0 c0' <*> dlist ptr0 ptr1 to1 (c1'::tl1))
           (fun _ -> intro_dlist_cons ptr0 ptr1 to1 c1' tl1);

       intro_dlist_cons from0 ptr0 to1 c0' (c1'::tl1);
       
       let l = c0'::c1'::tl1 in       
       resource_assertion (dlist from0 ptr0 null_dlist l);
       admit();
       // let h1 = FStar.HyperStack.ST.get () in
       // assume (modifies (dlist from0 ptr0 to0 l0 <*> dlist from1 ptr1 null_dlist l1)
       //                  (dlist from0 ptr0 null_dlist l) 
       //                  h0 h1);
       l
     end
     else begin admit() end
       //pts_to ptr0 hd0 <*> dlist ptr0 (next hd0) to0 tl0 <*> dlist from1 ptr1 to1 l1
       //next c0 =!= t0
       rst_frame 
          (pts_to ptr0 hd0 <*> dlist ptr0 (next c0) to0 tl0 <*> dlist from1 ptr1 null_dlist l1)
          (fun _ -> pts_to ptr0 hd0 <*> dlist ptr0 (next c0) to0 tl0 <*> dlist from1 ptr1 null_dlist l1)
          (fun _ -> invert_dlist_cons_neq ptr0 (next c0) to0 tl0);

       let l = 
         rst_frame 
           (pts_to ptr0 hd0 <*> dlist ptr0 (next c0) to0 tl0 <*> dlist from1 ptr1 null_dlist l1)
           (fun l -> pts_to ptr0 hd0 <*> dlist ptr0 (next c0) null_dlist l)
           (fun _ -> concat ptr0 (next c0) to0 tl0 from1 ptr1 l1)
       in 
       intro_dlist_cons from0 ptr0 null_dlist hd0 l;
       resource_assertion (dlist from0 ptr0 to1 (hd0::l));
       let l = hd0::l in
       let h1 = FStar.HyperStack.ST.get () in
       assume (modifies (dlist from0 ptr0 to0 l0 <*> dlist from1 ptr1 to1 l1)
                        (dlist from0 ptr0 to1 l)
                        h0 h1);
       l
     end

     
     
     admit()
       //pts_to ptr0 c1 <*> dlist to0 ptr1 to1 l1
       //c1.next == ptr1
       //
       //==================================
       //dlist from0 ptr0 to1 (c::l1)
       
       assert (prev c1 == from0);
       assert (ptr0 =!= to1);
       
       //ptr0 <> to0

       admit()
       // if ptr_eq ptr1 to1
       // then begin
       //   rst_frame
       //     (pts_to ptr0 c1 <*> dlist ptr0 to0 to0 [] <*> dlist from1 ptr1 to1 l1)
       //     (fun _ -> pts_to ptr0 c1 <*> dlist ptr0 to0 to0 [] <*> dlist ptr0 to1 to1 [])  
       //     (fun _ -> invert_dlist_nil_eq from1 ptr0 ptr1 to1 l1);
  
       //   rst_frame
       //     (pts_to ptr0 c1 <*> dlist ptr0 to0 to0 [] <*> dlist ptr0 to1 to1 [])           
       //     (fun _ -> pts_to ptr0 c1 <*> dlist ptr0 to0 to0 [] <*> dlist ptr0 (next c1) to1 [])
       //     (fun _ -> rewrite_resource (dlist ptr0 to1 to1 []) (dlist ptr0 (next c1) to1 []));

       //   rst_frame
       //     (pts_to ptr0 c1 <*> dlist ptr0 to0 to0 [] <*> dlist ptr0 (next c1) to1 [])
       //     (fun _ -> dlist from0 ptr0 to1 [c1] <*> dlist ptr0 to0 to0 [])
       //     (fun _ -> intro_dlist_cons from0 ptr0 to1 c1 []);

       //   resource_assertion (dlist from0 ptr0 to1 [c1]);
       //   admit()
       // end
       // else admit()
     end
     else admit()
     in
     let h1 = FStar.HyperStack.ST.get () in
     assume (modifies (dlist from0 ptr0 to0 l0 <*> dlist from1 ptr1 to1 l1)
                      (dlist from0 ptr0 to1 (l0@l1))
                      h0 h1);
     l

     
     empty_resource (dlist null_dlist p null_dlist [cell]) h0 h1);     


     admit()

       
     
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
