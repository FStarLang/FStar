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

module Steel.Primitive.ForkJoin
open FStar.Ghost
open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
module L = Steel.SpinLock
open Steel.FractionalPermission
open Steel.Reference

////////////////////////////////////////////////////////////////////////////////

let maybe_p (p:slprop) (v:bool) = if v then p else emp

[@@__reduce__]
let lock_inv_pred (r:ref bool) (p:slprop) (v:bool) : slprop =
  pts_to r full_perm v `star` maybe_p p v

let lock_inv (r:ref bool) (p:slprop)
  : slprop
  = h_exists (lock_inv_pred r p)

noeq
type thread (p:slprop u#1) = {
  r:ref bool;
  l:L.lock (lock_inv r p)
}

let intro_maybe_p_false (p:slprop)
  : SteelT unit emp (fun _ -> maybe_p p false)
  = change_slprop emp (maybe_p p false) (fun _ -> ())

let intro_maybe_p_true (p:slprop)
  : SteelT unit p (fun _ -> maybe_p p true)
  = change_slprop p (maybe_p p true) (fun _ -> ())

let new_thread (p:slprop)
  : SteelT (thread p) emp (fun _ -> emp)
  = let r = alloc false in
    intro_maybe_p_false p;
    intro_exists false (lock_inv_pred r p);
    let l = L.new_lock (lock_inv r p) in
    let t = {r = r; l = l} in
    t

let finish (#p:slprop) (t:thread p) (v:bool)
  : SteelT unit (pts_to t.r full_perm v `star` p) (fun _ -> emp)
  = write t.r true;
    intro_maybe_p_true p;
    intro_exists true (lock_inv_pred t.r p);
    L.release t.l


let acquire (#p:slprop) (t:thread p)
  : SteelT bool emp (fun b -> pts_to t.r full_perm b)
  = L.acquire t.l;
    let b = read_refine #_ #full_perm (maybe_p p) t.r in
    drop (maybe_p p b);
    return b

let spawn (#p #q:slprop)
          ($f: (unit -> SteelT unit p (fun _ -> q)))
          (t:thread q)
          (_:unit)
  : SteelT unit p (fun _ -> emp)
  = let b = acquire t in
    f ();
    finish t b

let fork (#p #q #r #s:slprop)
      (f: (unit -> SteelT unit p (fun _ -> q)))
      (g: (thread q -> unit -> SteelT unit r (fun _ -> s)))
  : SteelT unit (p `star` r) (fun _ -> s)
  = let t : thread q = new_thread q in
    let _ = par (spawn f t) (g t) in
    ()

let rec join (#p:slprop) (t:thread p)
  : SteelT unit emp (fun _ -> p)
  = let _ = L.acquire t.l in
    let b = read_refine (maybe_p p) t.r in
    if b then
      (change_slprop (lock_inv_pred t.r p b) p (fun _ -> ()); noop ())
    else
      (change_slprop (lock_inv_pred t.r p b) (lock_inv_pred t.r p false) (fun _ -> ());
      intro_exists false (lock_inv_pred t.r p);
      L.release t.l;
      join t)
