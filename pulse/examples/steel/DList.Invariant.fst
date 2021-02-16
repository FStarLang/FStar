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
let rec dlist' (#a:Type) (left:t a)
                        (ptr:t a)
                        (right:t a)
                        (l:list (cell a))
    : Tot slprop (decreases l)
    =
    match l with
    | [] ->
      pure (right == ptr)

    | hd :: tl ->
      pure (right =!= ptr) `star`
      pts_to ptr full_perm hd `star`
      pure (prev hd == left) `star`
      dlist' ptr (next hd) right tl
let dlist = dlist'


// assume
// val dlist_injective (#a:_) (left ptr right : t a)
//                            (l1 l2:list (cell a))
//                            (h:mem)
//   : Lemma
//     (requires
//       interp (dlist left ptr right l1) h /\
//       interp (dlist left ptr right l2) h)
//     (ensures
//       l1 == l2)
//    (decreases l1)
//   = match l1, l2 with
//     | [], [] -> ()
//     | hd1::tl1, hd2::tl2 ->
//       pts_to_injective ptr hd1 hd2 h;
//       assert (hd1 == hd2);
//       dlist_injective' ptr hd1.next right tl1 tl2 h

//     | [], hd::tl
//     | hd::tl, [] ->
//       elim_pure (right == ptr) h;
//       elim_pure (right =!= ptr) h
// let dlist_injective = dlist_injective'

#push-options "--query_stats --fuel 1,1 --ifuel 1,1"
let intro_dlist_nil (#a:Type) (left right:t a)
   : SteelT unit emp (fun _ -> dlist left right right [])
   = change_slprop emp (dlist left right right [])
                       (fun m -> pure_interp (right == right) m;
                              norm_spec [delta;zeta] ((dlist left right right [])))

let elim_dlist_nil (#a:Type) (left ptr right:t a)
   : SteelT unit
     (dlist left ptr right [])
     (fun _ -> pure (right == ptr))
   = change_slprop (dlist left ptr right [])
                   (pure (right == ptr))
                   (fun m -> pure_interp (ptr == right) m;
                          norm_spec [delta;zeta] ((dlist left ptr right [])))


let intro_star_pure (p:slprop) (q:prop) (h:mem)
  : Lemma (interp p h /\ q ==> interp (p `star` pure q) h)
  = let open Steel.Memory in
    emp_unit p;
    pure_star_interp p q h

let dlist_right_right_nil (#a:Type) (left right:t a) (l:list (cell a)) (m:mem)
  : Lemma
    (requires interp (dlist left right right l) m)
    (ensures interp (dlist left right right [] `star` pure (l == [])) m)
  = pure_interp (right == right) m;
    pure_interp (right =!= right) m;
    pure_interp (l == []) m;
    match l with
    | [] -> intro_star_pure (dlist left right right []) (l == []) m
    | hd::tl -> norm_spec [delta;zeta] (dlist left right right (hd::tl))

let invert_dlist_nil_eq (#a:Type) (left ptr right:t a) (l:list (cell a))
    : Steel unit
            (dlist left ptr right l)
            (fun _ -> dlist left right right [] `star` pure (l==[]))
            (requires fun _ -> ptr == right)
            (ensures fun _ _ _ -> True)
    = change_slprop (dlist left ptr right l)
                    (dlist left right right l)
                    (fun _ -> ());
      change_slprop (dlist left right right l)
                    (dlist left right right [] `star` pure (l == []))
                    (dlist_right_right_nil left right l)

let intro_dlist_cons (#a:Type) (left:t a)
                               (ptr:t a)
                               (right:t a)
                               (hd: cell a)
                               (tl: list (cell a))
   : Steel unit
     (pts_to ptr full_perm hd `star` dlist ptr (next hd) right tl)
     (fun _ -> dlist left ptr right (hd::tl))
     (requires fun _ ->
       prev hd == left /\
       ptr =!= right)
     (ensures fun _ _ _ -> True)
   = change_slprop emp (pure (prev hd == left)) (fun m -> pure_interp (prev hd == left) m);
     change_slprop emp (pure (right =!= ptr)) (fun m -> pure_interp (right =!= ptr) m);
     change_slprop  (pure (right =!= ptr) `star`
                     pts_to ptr full_perm hd `star`
                     pure (prev hd == left) `star`
                     dlist ptr (next hd) right tl)
                    (dlist left ptr right (hd::tl))
                    (fun _ -> norm_spec [delta;zeta] (dlist left ptr right (hd::tl)))

let elim_dlist_cons (#a:Type) (left:t a)
                              (ptr:t a)
                              (right:t a)
                              (hd:cell a)
                              (tl:list (cell a))
   = change_slprop  (dlist left ptr right (hd::tl))
                    (pure (right =!= ptr) `star`
                     pts_to ptr full_perm hd `star`
                     pure (prev hd == left) `star`
                     dlist ptr (next hd) right tl)
                    (fun _ -> norm_spec [delta;zeta] (dlist left ptr right (hd::tl)));
     U.elim_pure (right =!= ptr);
     U.elim_pure (prev hd == left)

let lemma_invert_dlist_cons_neq (#a:Type) (left ptr right:t a) (l:list (cell a)) (m:mem)
  : Lemma
    (requires interp (dlist left ptr right l) m /\ ptr =!= right)
    (ensures interp (dlist left ptr right l `star` pure (Cons? l == true)) m)
  = match l with
    | [] ->
      norm_spec [delta;zeta] (dlist left ptr right []);
      assert (interp (dlist left ptr right []) m);
      pure_interp (right == ptr) m
    | hd::tl ->
      intro_star_pure (dlist left ptr right l) (Cons? l == true) m

let invert_dlist_cons_neq (#a:Type) (left ptr right:t a) (l:list (cell a))
    : Steel unit
     (requires
       dlist left ptr right l)
     (ensures fun _ ->
       dlist left ptr right l)
     (requires fun _ ->
       ptr =!= right)
     (ensures fun _ _ _ ->
       Cons? l == true)
   = change_slprop (dlist left ptr right l)
                   (dlist left ptr right l `star` pure (Cons? l == true))
                   (lemma_invert_dlist_cons_neq left ptr right l);
     U.elim_pure (Cons? l == true)


////////////////////////////////////////////////////////////////////////////////

let dlist_not_null (#a:Type)
                   (#[@@@ framing_implicit] left:t a)
                   (#[@@@ framing_implicit] right:t a)
                   (#[@@@ framing_implicit] rep:list (cell a))
                   (p:t a)
  = U.lift_lemma (dlist left p right rep)
                 ((Cons? rep) == true)
                 (fun m -> if Cons? rep
                        then ()
                        else (assert (p =!= right);
                              lemma_invert_dlist_cons_neq left p right rep m);
                              Steel.Memory.pure_star_interp
                                (dlist left p right rep)
                                (Cons? rep == true)
                                m);
    let hd :: tl = rep in
    change_slprop (dlist left p right rep)
                  (dlist left p right (hd :: tl))
                  (fun _ -> ());
    elim_dlist_cons left p right hd tl;
    U.pts_to_not_null #_ #full_perm #(Ghost.hide hd) p;
    intro_dlist_cons left p right hd tl;
    change_slprop (dlist left p right (hd :: tl))
                  (dlist left p right rep)
                  (fun _ -> ())
