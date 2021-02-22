(*
   Copyright 2020 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

   Author(s): N. Swamy
*)
module DList.Invariant
open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Steel.FractionalPermission
open Steel.Reference
module L = FStar.List.Tot
module U = Steel.Utils

#push-options "--__no_positivity"
noeq
type cell (a: Type0) = {
  prev: ref (cell a);
  next: ref (cell a);
  data: a;
}
#pop-options


let prev (c:cell 'a) : t 'a = c.prev
let next (c:cell 'a) : t 'a = c.next
let data (c:cell 'a) : 'a = c.data
let mk_cell (p n: t 'a) (d:'a) = {
  prev = p;
  next = n;
  data = d
}
let hd l = Cons?.hd l
let tl l = Cons?.tl l

let ptr_eq (#a:Type) (x y:t a) = admit()


////////////////////////////////////////////////////////////////////////////////
// Main dlist invariant
////////////////////////////////////////////////////////////////////////////////
(**
 *
 *  dlist left ptr tail right [d0;...;dn]
 *
 *  left    ptr               tail       right
 *  |        |                  |         |
 *  |        v                  v         |
 *  v       __         __       __        v
 *  <-prev-|d0|-next->|  | ... |dn|-next->
 *         |__|<-prev-|__| ..  |__|
 *
 *
 * dlist left ptr tail right []
 *   ptr
 *)

let repr (a:Type) = l:list (cell a) { Cons? l }

let rec dlist_cons (#a:Type) (previous :t a)
                             (cur  :t a)
                             (last :t a)
                             (right:t a)
                             (xs:repr a)
    : Tot slprop (decreases xs)
    = match xs with
      | [ x ]  ->
        pure (cur == last /\
              prev x == previous /\
              next x == right) `star`
        pts_to cur full_perm x

      | x :: xs' ->
        pure (prev x == previous) `star`
        pts_to cur full_perm x `star`
        dlist_cons cur (next x) last right xs'

let rec dlist_snoc (#a:Type) (left:t a)
                             (last:t a)
                             (cur:t a)
                             (nxt:t a)
                             (xs:repr a)
    : Tot slprop (decreases xs)
    = match xs with
      | [ x ]  ->
        pure (cur == last /\
              prev x == left /\
              next x == nxt) `star`
        pts_to cur full_perm x

      | x :: xs' ->
        pure (next x == nxt) `star`
        pts_to cur full_perm x `star`
        dlist_snoc left last (prev x) cur xs'

let dlist_cons_snoc_nil #a (left front back right: t a) (x:_)
  : Lemma (dlist_cons left front back right [x] `equiv`
           dlist_snoc left front back right [x])
  = calc (equiv) {
         dlist_cons left front back right [x];
      (equiv) {}
         pure (front == back /\
               prev x == left /\
               next x == right) `star`
         pts_to front full_perm x;
       (equiv) { assume (front == back) }
         pure (front == back /\
               prev x == left /\
               next x == right) `star`
         pts_to back full_perm x;
       (equiv) { admit () }
         pure (back == front /\
               prev x == left /\
               next x == right) `star`
         pts_to back full_perm x;
    }

module ST = Steel.Memory.Tactics
let dlist_snoc_snoc_1 (#a:Type) (left:t a)
                                 (last:t a)
                                 (cur:t a)
                                 (right:t a)
                                 (x0:cell a)
                                 (x:cell a)
  : Lemma (ensures
          (dlist_snoc left last cur right [x0;x] `equiv`
            (pure (prev x == left) `star`
             pts_to last full_perm x `star`
             dlist_snoc last (next x) cur right [x0])))
  = calc (equiv) {
         dlist_snoc left last cur right [x0;x];
    (equiv) { }
         pure (next x0 == right) `star`
         pts_to cur full_perm x0 `star`
         dlist_snoc left last (prev x0) cur [x];
    (equiv) { }
         pure (next x0 == right) `star`
         pts_to cur full_perm x0 `star`
         (pure (prev x0 == last /\
                prev x == left /\
                next x == cur) `star`
          pts_to (prev x0) full_perm x);
    (equiv) { admit() }
         pure (prev x == left) `star`
         pts_to last full_perm x `star`
         (pure (cur == next x /\
                prev x0 == last /\
                next x0 == right) `star`
          pts_to cur full_perm x0)                ;
    }

assume
val equiv_extensional_on_star_r (p1 p2 p3:slprop)
  : squash (p2 `equiv` p3 ==> (p1 `star` p2) `equiv` (p1 `star` p3))

assume
val gather_pure (p q:prop) : Lemma ((pure p `star` pure q) == pure (p /\ q))
assume
val rewrite_pure (p q:prop) : Lemma (requires (p <==> q)) (ensures (pure p `equiv` pure q))

#push-options "--z3rlimit_factor 4"
assume
val utils (_:unit)
  : Lemma ((forall p q r. ((p `star` q) `star` r) == (p `star` (q `star` r))) /\
           (forall p q. (p `star` q) == (q `star` p)) /\
           (forall p q.{:pattern (p `equiv` q)} (p `equiv` q) <==> p == q) /\
           (forall (a b:prop).{:pattern (pure a);(pure b)} (a <==> b) <==> (pure a == pure b)) /\
           (forall (a b:prop). {:pattern (pure a `star` pure b)} ((pure a) `star` (pure b)) `equiv` pure (a /\ b)))
#pop-options
#push-options "--query_stats --initial_fuel 2 --initial_ifuel 1 --max_fuel 2 --max_ifuel 1 --z3rlimit_factor 4"
module T = FStar.Tactics

let no_prev_cycles #a (left last cur right: _) (p:_) (v:_) (xs:repr a) (m:_)
  : Lemma (requires (interp (pts_to p full_perm v `star` dlist_snoc left last cur right xs) m))
          (ensures (forall c. List.memP c xs ==> prev c =!= p) /\ p =!= last /\ p =!= cur)
  = admit()

let no_next_cycles #a (left cur last right: _) (p:_) (v:_) (xs:repr a) (m:_)
  : Lemma (requires interp (pts_to p full_perm v `star` dlist_cons left cur last right xs) m)
          (ensures (forall c. List.memP c xs ==> next c =!= p) /\ p =!= last /\ p =!= cur)
  = admit()

let stronger (p q:slprop) = forall m. interp p m ==> interp q m
let stronger_drop (#p #q #r:slprop) : Lemma ((p `star` q) `stronger` q) = ()
let stronger_equiv (#p #q #r:slprop) : Lemma ((p `equiv` q) ==> p `stronger` q) = ()


let rec dlist_snoc_snoc (#a:Type) (left:t a)
                                  (last:t a)
                                  (cur:t a)
                                  (right:t a)
                                  (xs:repr a)
                                  (x:cell a)
  : Lemma (ensures
          (dlist_snoc left last cur right (List.snoc (xs, x)) `equiv`
            (pure (prev x == left) `star`
             pts_to last full_perm x `star`
             dlist_snoc last (next x) cur right xs)))
          (decreases (List.length xs))
  = match xs with
    | [hd] -> dlist_snoc_snoc_1 left last cur right hd x
    | hd::xs' ->
      let xs' : repr a = xs' in
      calc (equiv) {
        dlist_snoc left last cur right (List.snoc (hd::xs', x));
      (equiv) { (* defn *) }
        pure (next hd == right) `star`
        pts_to cur full_perm hd `star`
        dlist_snoc left last (prev hd) cur (List.snoc (xs', x));
      (equiv) { (* IH *)
                utils ();
                dlist_snoc_snoc left last (prev hd) cur xs' x
              }
        pure (next hd == right) `star`
        pts_to cur full_perm hd `star`
        (pure (prev x == left) `star`
         pts_to last full_perm x `star`
         dlist_snoc last (next x) (prev hd) cur xs');
      (equiv) { (* boring *) _ by (ST.canon()) }
        pure (prev x == left) `star`
        pts_to last full_perm x `star`
        (pure (next hd == right) `star`
         pts_to cur full_perm hd `star`
         dlist_snoc last (next x) (prev hd) cur xs');
      (equiv) { }
         (pure (prev x == left) `star`
          pts_to last full_perm x `star`
          dlist_snoc last (next x) cur right xs);
      }

let rev #a (r:repr a) : repr a = let x = List.rev r in assume (Cons? x); x


let rec dlist_cons_snoc (#a:Type) (left :t a)
                                  (head  :t a)
                                  (tail :t a)
                                  (right:t a)
                                  (l:repr a)
  : Lemma (ensures dlist_cons left head tail right l `equiv`
                   dlist_snoc left head tail right (rev l))
          (decreases l)
  = match l with
    | [x] -> dlist_cons_snoc_nil left head tail right x
    | x :: xs ->
      dlist_cons_snoc head (next x) tail right xs;
      assert (dlist_cons head (next x) tail right xs `equiv`
              dlist_snoc head (next x) tail right (rev xs));
      assume (rev l == List.snoc (rev xs, x));
      calc (equiv) {
        dlist_cons left head tail right (x::xs);
      (equiv) { }
          pure (prev x == left)
          `star`
          pts_to head full_perm x `star`
          dlist_cons head (next x) tail right xs;
       (equiv) { equiv_extensional_on_star_r
                         (pure (prev x == left)
                               `star`
                          pts_to head full_perm x)
                          (dlist_cons head (next x) tail right xs)
                          (dlist_snoc head (next x) tail right (rev xs))
                }
          pure (prev x == left)
          `star`
          pts_to head full_perm x `star`
          (dlist_snoc head (next x) tail right (rev xs));
      };
      dlist_snoc_snoc left head tail right (rev xs) x


// // assume
// // val dlist_injective (#a:_) (left ptr right : t a)
// //                            (l1 l2:list (cell a))
// //                            (h:mem)
// //   : Lemma
// //     (requires
// //       interp (dlist left ptr right l1) h /\
// //       interp (dlist left ptr right l2) h)
// //     (ensures
// //       l1 == l2)
// //    (decreases l1)
// //   = match l1, l2 with
// //     | [], [] -> ()
// //     | hd1::tl1, hd2::tl2 ->
// //       pts_to_injective ptr hd1 hd2 h;
// //       assert (hd1 == hd2);
// //       dlist_injective' ptr hd1.next right tl1 tl2 h

// //     | [], hd::tl
// //     | hd::tl, [] ->
// //       elim_pure (right == ptr) h;
// //       elim_pure (right =!= ptr) h
// // let dlist_injective = dlist_injective'

// #push-options "--query_stats --fuel 1,1 --ifuel 1,1"
// let intro_dlist_nil (#a:Type) (left right:t a)
//    : SteelT unit emp (fun _ -> dlist left right right [])
//    = change_slprop emp (dlist left right right [])
//                        (fun m -> pure_interp (right == right) m;
//                               norm_spec [delta;zeta] ((dlist left right right [])))

// let elim_dlist_nil (#a:Type) (left ptr right:t a)
//    : SteelT unit
//      (dlist left ptr right [])
//      (fun _ -> pure (right == ptr))
//    = change_slprop (dlist left ptr right [])
//                    (pure (right == ptr))
//                    (fun m -> pure_interp (ptr == right) m;
//                           norm_spec [delta;zeta] ((dlist left ptr right [])))


// let intro_star_pure (p:slprop) (q:prop) (h:mem)
//   : Lemma (interp p h /\ q ==> interp (p `star` pure q) h)
//   = let open Steel.Memory in
//     emp_unit p;
//     pure_star_interp p q h

// let dlist_right_right_nil (#a:Type) (left right:t a) (l:list (cell a)) (m:mem)
//   : Lemma
//     (requires interp (dlist left right right l) m)
//     (ensures interp (dlist left right right [] `star` pure (l == [])) m)
//   = pure_interp (right == right) m;
//     pure_interp (right =!= right) m;
//     pure_interp (l == []) m;
//     match l with
//     | [] -> intro_star_pure (dlist left right right []) (l == []) m
//     | hd::tl -> norm_spec [delta;zeta] (dlist left right right (hd::tl))

// let invert_dlist_nil_eq (#a:Type) (left ptr right:t a) (l:list (cell a))
//     : Steel unit
//             (dlist left ptr right l)
//             (fun _ -> dlist left right right [] `star` pure (l==[]))
//             (requires fun _ -> ptr == right)
//             (ensures fun _ _ _ -> True)
//     = change_slprop (dlist left ptr right l)
//                     (dlist left right right l)
//                     (fun _ -> ());
//       change_slprop (dlist left right right l)
//                     (dlist left right right [] `star` pure (l == []))
//                     (dlist_right_right_nil left right l)

// let intro_dlist_cons (#a:Type) (left:t a)
//                                (ptr:t a)
//                                (right:t a)
//                                (hd: cell a)
//                                (tl: list (cell a))
//    : Steel unit
//      (pts_to ptr full_perm hd `star` dlist ptr (next hd) right tl)
//      (fun _ -> dlist left ptr right (hd::tl))
//      (requires fun _ ->
//        prev hd == left /\
//        ptr =!= right)
//      (ensures fun _ _ _ -> True)
//    = change_slprop emp (pure (prev hd == left)) (fun m -> pure_interp (prev hd == left) m);
//      change_slprop emp (pure (right =!= ptr)) (fun m -> pure_interp (right =!= ptr) m);
//      change_slprop  (pure (right =!= ptr) `star`
//                      pts_to ptr full_perm hd `star`
//                      pure (prev hd == left) `star`
//                      dlist ptr (next hd) right tl)
//                     (dlist left ptr right (hd::tl))
//                     (fun _ -> norm_spec [delta;zeta] (dlist left ptr right (hd::tl)))

// let elim_dlist_cons (#a:Type) (left:t a)
//                               (ptr:t a)
//                               (right:t a)
//                               (hd:cell a)
//                               (tl:list (cell a))
//    = change_slprop  (dlist left ptr right (hd::tl))
//                     (pure (right =!= ptr) `star`
//                      pts_to ptr full_perm hd `star`
//                      pure (prev hd == left) `star`
//                      dlist ptr (next hd) right tl)
//                     (fun _ -> norm_spec [delta;zeta] (dlist left ptr right (hd::tl)));
//      U.elim_pure (right =!= ptr);
//      U.elim_pure (prev hd == left)

// let lemma_invert_dlist_cons_neq (#a:Type) (left ptr right:t a) (l:list (cell a)) (m:mem)
//   : Lemma
//     (requires interp (dlist left ptr right l) m /\ ptr =!= right)
//     (ensures interp (dlist left ptr right l `star` pure (Cons? l == true)) m)
//   = match l with
//     | [] ->
//       norm_spec [delta;zeta] (dlist left ptr right []);
//       assert (interp (dlist left ptr right []) m);
//       pure_interp (right == ptr) m
//     | hd::tl ->
//       intro_star_pure (dlist left ptr right l) (Cons? l == true) m

// let invert_dlist_cons_neq (#a:Type) (left ptr right:t a) (l:list (cell a))
//     : Steel unit
//      (requires
//        dlist left ptr right l)
//      (ensures fun _ ->
//        dlist left ptr right l)
//      (requires fun _ ->
//        ptr =!= right)
//      (ensures fun _ _ _ ->
//        Cons? l == true)
//    = change_slprop (dlist left ptr right l)
//                    (dlist left ptr right l `star` pure (Cons? l == true))
//                    (lemma_invert_dlist_cons_neq left ptr right l);
//      U.elim_pure (Cons? l == true)


// ////////////////////////////////////////////////////////////////////////////////

// let dlist_not_null (#a:Type)
//                    (#left:t a)
//                    (#right:t a)
//                    (#rep:list (cell a))
//                    (p:t a)
//   = U.lift_lemma (dlist left p right rep)
//                  ((Cons? rep) == true)
//                  (fun m -> if Cons? rep
//                         then ()
//                         else (assert (p =!= right);
//                               lemma_invert_dlist_cons_neq left p right rep m);
//                               Steel.Memory.pure_star_interp
//                                 (dlist left p right rep)
//                                 (Cons? rep == true)
//                                 m);
//     let hd :: tl = rep in
//     change_slprop (dlist left p right rep)
//                   (dlist left p right (hd :: tl))
//                   (fun _ -> ());
//     elim_dlist_cons left p right hd tl;
//     U.pts_to_not_null #_ #_ #full_perm #(Ghost.hide hd) p;
//     intro_dlist_cons left p right hd tl;
//     change_slprop (dlist left p right (hd :: tl))
//                   (dlist left p right rep)
//                   (fun _ -> ())
