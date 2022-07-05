(*
   Copyright 2021 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

   Author: Aseem Rastogi
*)

module Steel.ST.CancellableSpinLock

open Steel.ST.Effect
open Steel.ST.Util
open Steel.FractionalPermission
open Steel.ST.Reference
open Steel.ST.SpinLock

module G = FStar.Ghost

[@@__reduce__]
let lock_inv_pred (r:ref bool) (v:vprop) : bool -> vprop =
  fun b -> pts_to r full_perm b `star` (if b then v else emp)  

[@@__reduce__]
let lock_inv (r:ref bool) (v:vprop) : vprop = exists_ (lock_inv_pred r v)

noeq
type cancellable_lock (v:vprop) = {
  lref   : ref bool;
  llock  : lock (lock_inv lref v)
}

let new_cancellable_lock v =
  let r = alloc true in
  intro_exists true (lock_inv_pred r v);
  let l = new_lock (lock_inv r v) in
  return ({lref = r; llock = l})

[@__reduce__]
let can_release #v c = pts_to c.lref full_perm true

//#set-options "--debug Steel.ST.CancellableSpinLock --debug_level Extreme,Rel,2635,TacVerbose --print_implicits --ugly"
let acquire #v c =
  acquire c.llock;
  let b_erased = elim_exists () in
  let b = read c.lref in
  if b
  then begin
    rewrite (if b_erased then v else emp) v;
    rewrite (v `star` can_release c)
            (maybe_acquired b c)
  end
  else begin
    intro_exists (G.reveal b_erased) (lock_inv_pred c.lref v);
    release c.llock;
    rewrite emp (maybe_acquired b c)
  end;
  return b

let release #v c =
  intro_exists true (lock_inv_pred c.lref v);
  release c.llock

let cancel c = free c.lref
