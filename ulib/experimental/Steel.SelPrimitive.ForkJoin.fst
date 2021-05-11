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

module Steel.SelPrimitive.ForkJoin
open FStar.Ghost
open Steel.Memory
open Steel.SelEffect.Atomic
open Steel.SelEffect
module L = Steel.SelSpinLock
open Steel.FractionalPermission
open Steel.SelReference

////////////////////////////////////////////////////////////////////////////////

let maybe_p (p:vprop) (v:bool) = if v then p else emp

[@@__reduce__]
let lock_inv_pred (r:ref bool) (p:vprop) (v:bool) : vprop =
  pts_to r full_perm v `star` maybe_p p v

let lock_inv (r:ref bool) (p:vprop)
  : vprop
  = h_exists (lock_inv_pred r p)

noeq
type thread (p:vprop) = {
  r:ref bool;
  l:L.lock (lock_inv r p)
}

let intro_maybe_p_false (p:vprop)
  : SteelSelT unit emp (fun _ -> maybe_p p false)
  = rewrite_slprop emp (maybe_p p false) (fun _ -> ())

let intro_maybe_p_true (p:vprop)
  : SteelSelT unit p (fun _ -> maybe_p p true)
  = rewrite_slprop p (maybe_p p true) (fun _ -> ())

let new_thread (p:vprop)
  : SteelSelT (thread p) emp (fun _ -> emp)
  = let r = alloc_pt false in
    intro_maybe_p_false p;
    intro_exists false (lock_inv_pred r p);
    let l = L.new_lock (lock_inv r p) in
    let t = {r = r; l = l} in
    t

let finish (#p:vprop) (t:thread p) (v:bool)
  : SteelSelT unit (pts_to t.r full_perm v `star` p) (fun _ -> emp)
  = write_pt t.r true;
    intro_maybe_p_true p;
    intro_exists true (lock_inv_pred t.r p);
    L.release t.l


let acquire (#p:vprop) (t:thread p)
  : SteelSelT bool emp (fun b -> pts_to t.r full_perm b)
  = L.acquire t.l;
    let b = read_refine_pt #_ #full_perm (maybe_p p) t.r in
    drop (maybe_p p b);
    return b

let spawn (#p #q:vprop)
          ($f: (unit -> SteelSelT unit p (fun _ -> q)))
          (t:thread q)
          (_:unit)
  : SteelSelT unit p (fun _ -> emp)
  = let b = acquire t in
    f ();
    finish t b

let fork (#p #q #r #s:vprop)
      (f: (unit -> SteelSelT unit p (fun _ -> q)))
      (g: (thread q -> unit -> SteelSelT unit r (fun _ -> s)))
  : SteelSelT unit (p `star` r) (fun _ -> s)
  = let t : thread q = new_thread q in
    let _ = par (spawn f t) (g t) in
    ()

let rec join (#p:vprop) (t:thread p)
  : SteelSelT unit emp (fun _ -> p)
  = let _ = L.acquire t.l in
    let b = read_refine_pt (maybe_p p) t.r in
    if b then
      (rewrite_slprop (lock_inv_pred t.r p b) p (fun _ -> ()); noop ())
    else
      (rewrite_slprop (lock_inv_pred t.r p b) (lock_inv_pred t.r p false) (fun _ -> ());
      intro_exists false (lock_inv_pred t.r p);
      L.release t.l;
      join t)
