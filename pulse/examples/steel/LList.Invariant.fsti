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

   Author(s): N. Swamy, A. Fromherz
*)
module LList.Invariant
open Steel.Memory
open Steel.Effect
open Steel.FractionalPermission
open Steel.Reference
module L = FStar.List.Tot

val cell (a:Type0) : Type0
let t (a:Type0) = ref (cell a)

val next (c:cell 'a) : t 'a
val data (c:cell 'a) : 'a
val mk_cell (n: t 'a) (d:'a)
  : Pure (cell 'a)
    (requires True)
    (ensures fun c ->
      next c == n /\
      data c == d)

/// Assuming a null pointer
val null_llist (#a:Type)
  : t a

/// Equality on same-length pointers: an assumed primitive
val ptr_eq (#a:Type) (x y:t a)
  : Pure bool
    (requires True)
    (ensures fun b ->
      if b then x == y else x =!= y)

/// Main abstract invariant
/// A linked list segment starting at ptr, containing cells l
val llist (#a:Type) (ptr:t a) (l:list (cell a)) : slprop u#1

(* Helper lemmas/rewritings *)

val intro_llist_nil (a:Type)
   : SteelT unit emp (fun _ -> llist (null_llist #a) [])

val intro_llist_cons (#a:Type) (ptr:t a)
                               (hd: cell a)
                               (tl: list (cell a))
   : Steel unit
     (pts_to ptr full_perm hd `star` llist (next hd) tl)
     (fun _ -> llist ptr (hd::tl))
     (requires fun _ -> ~ (is_null ptr))
     (ensures fun _ _ _ -> True)

val elim_llist_cons (#a:Type) (ptr:t a)
                              (hd:cell a)
                              (tl:list (cell a))
   : SteelT unit
     (llist ptr (hd::tl))
     (fun _ -> pts_to ptr full_perm hd `star` llist (next hd) tl)
