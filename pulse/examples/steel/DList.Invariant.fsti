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
open Steel.SelEffect
open Steel.FractionalPermission
open Steel.SelReference
module L = FStar.List.Tot

let (=.=) #a (x y: a) : vprop = pure (x == y)

val cell (a:Type0) : Type0
let t a = ref (cell a)

noeq
type tt a =
  {
    head: t a;
    tail: t a;
  }

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

/// Assuming a null pointer
let null_dlist (#a:Type)
  : t a
  = Steel.SelReference.null


/// Equality on same-length pointers: an assumed primitive
val ptr_eq (#a:Type) (x y:t a)
  : Pure bool
    (requires True)
    (ensures fun b ->
      if b then x == y else x =!= y)

/// Main abstract invariant
///    A doubly linked list segment at ptr from from left to right
val dlist (#a:Type) (left ptr right:t a) (l:list (cell a)) : vprop


////////////////////////////////////////////////////////////////////////////////
// dlist nil
////////////////////////////////////////////////////////////////////////////////
val intro_dlist_nil (#a:Type) (left right:t a)
   : SteelSelT unit emp (fun _ -> dlist left right right [])

val elim_dlist_nil (#a:Type) (left ptr right:t a)
   : SteelSelT unit
     (dlist left ptr right [])
     (fun _ -> right =.= ptr)

val invert_dlist_nil_eq (#a:Type) (left ptr right:t a) (l:list (cell a))
    : SteelSel unit
            (dlist left ptr right l)
            (fun _ -> dlist left right right [] `star` (l =.= []))
            (requires fun _ -> ptr == right)
            (ensures fun _ _ _ -> True)

val intro_dlist_cons (#a:Type) (left:t a)
                               (ptr:t a)
                               (right:t a)
                               (hd: cell a)
                               (tl: list (cell a))
   : SteelSel unit
     (pts_to ptr full_perm hd `star` dlist ptr (next hd) right tl)
     (fun _ -> dlist left ptr right (hd::tl))
     (requires fun _ ->
       prev hd == left /\
       ptr =!= right)
     (ensures fun _ _ _ -> True)


val elim_dlist_cons (#a:Type) (left:t a)
                              (ptr:t a)
                              (right:t a)
                              (hd:cell a)
                              (tl:list (cell a))
   : SteelSel unit
     (requires
       dlist left ptr right (hd::tl))
     (ensures fun _ ->
       pts_to ptr full_perm hd `star`
       dlist ptr (next hd) right tl)
     (requires fun _ -> True)
     (ensures fun _ _ _ ->
       prev hd == left /\
       right =!= ptr)

val invert_dlist_cons_neq (#a:Type) (left ptr right:t a) (l:list (cell a))
    : SteelSel unit
     (requires
       dlist left ptr right l)
     (ensures fun _ ->
       dlist left ptr right l)
     (requires fun _ ->
       ptr =!= right)
     (ensures fun _ _ _ ->
       Cons? l == true)


////////////////////////////////////////////////////////////////////////////////
//dlist is not null
////////////////////////////////////////////////////////////////////////////////

val dlist_not_null (#a:Type)
                   (#left:t a)
                   (#right:t a)
                   (#rep:list (cell a))
                   (p:t a)
  : SteelSel unit
    (dlist left p right rep)
    (fun _ -> dlist left p right rep)
    (requires fun _ -> p =!= right \/ Cons? rep)
    (ensures fun _ _ _ -> p =!= null_dlist)
