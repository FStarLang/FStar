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

/// An invariant for lists, where each list node stores a lock to the rest of the list.

val existsp_ (#[@@@strictly_positive] a:Type)
            ([@@@strictly_positive] p:(a -> vprop))
   : vprop
//   = fun m -> exists x. p x m
   
val pts_to (#[@@@strictly_positive] a:Type)
           (r:ref a)
           (frac:perm)
           (v:a) : vprop 

val lock ([@@@strictly_positive] p:vprop) : Type0

let half = half_perm full_perm

noeq
type llist_cell (a:Type0) : Type0 = {
     v : a;
     tl : ref (llist_cell a);
     tl_repr: lock (existsp_ (pts_to tl half))
}

let rec llist_inv (#a:Type) (repr:list a) (ptr:ref (llist_cell a)) = 
  match repr with
  | [] -> pure (ptr == null)
  | hd::tl ->
    exists_ (fun cell ->
      pts_to ptr half cell `star`
      pure (cell.v  == hd) `star`
      llist_inv tl cell.tl)

      
  


