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
*)

module Steel.LockCoupling
open Steel.ST.Util
open Steel.ST.Reference
open Steel.FractionalPermission

(*
   This example sketches how an invariant for lock-coupling list
     (a list that stores a lock at each cell protecting its tail pointer)
   might work.

   It relies on strictly positive version of the exists and pts_to
   separation logic predicates, although the libraries are not
   currently annotated with such positivity annotations.=
*)

(* It is relatively easy to show that h_exists is strictly positive *)
val h_exists (#[@@@strictly_positive] a:Type)
             ([@@@strictly_positive] p:(a -> vprop))
   : vprop

(* the pts_to predicate is a bit more subtle. It is an instance
   of a more general form that involves assertions about a PCM,
   and it is possible to construct PCMs that are not strictly
   positive. However, the basic pts_to predicate that this refers to,
   for the fractional permission PCM, is strictly positive.
   Revising the library to enable decorating pts_to predicates derived
   from positive PCMs remains to be done. *)
val pts_to (#[@@@strictly_positive] a:Type)
           (r:ref a)
           (f:perm)
           (v:a) : vprop 

val lock ([@@@strictly_positive] p:vprop) : Type0

let half = half_perm full_perm

(* The lock at each cell holds half permission to the next pointer *)
noeq
type llist_cell (a:Type0) : Type = {
  v : a;
  next : ref (llist_cell a);
  lock : lock (h_exists (pts_to next half))
}

(* A separation list_inv holds the other half permission *)
let rec list_inv (#a:Type) (p:ref (llist_cell a)) (repr:list a) 
  : Tot vprop (decreases repr) 
  = match repr with
    | [] -> pure (p == null)
    | hd::tl ->
      h_exists (fun cell ->
        pts_to p half cell `star`
        pure (cell.v == hd) `star`
        list_inv cell.next tl)

