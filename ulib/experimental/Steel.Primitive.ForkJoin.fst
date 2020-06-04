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
open Steel.Effect
open Steel.Memory
module L = Steel.SpinLock
open Steel.FractionalPermission
open FStar.Ghost
open Steel.Reference
open Steel.SteelT.Basics

//module U = FStar.Universe

////////////////////////////////////////////////////////////////////////////////

let full = full_perm

let maybe_p (p:slprop) (v:bool) = if v then p else emp

let lock_inv_pred (r:ref bool) (p:slprop) (v:bool) : slprop =
  pts_to r full_perm v `star` maybe_p p v

let lock_inv (r:ref bool) (p:slprop)
  : slprop
  = h_exists (lock_inv_pred r p)

//#set-options "--print_universes --print_implicits"

noeq
type thread (p:slprop u#1) = {
  r:ref bool;
  l:L.lock (lock_inv r p)
}

let intro_maybe_p_false (p:slprop)
  : SteelT unit emp (fun _ -> maybe_p p false)
  = h_assert (maybe_p p false)

let intro_maybe_p_true (p:slprop)
  : SteelT unit p (fun _ -> maybe_p p true)
  = h_assert (maybe_p p true)

let new_thread (p:slprop)
  : SteelT (thread p) emp (fun _ -> emp)
  = intro_maybe_p_false p;
    h_assert (maybe_p p false);
    h_intro_emp_l (maybe_p p false);
    let r = frame #(ref bool) #emp #(fun r -> pts_to r full_perm false)
                  (fun () -> alloc false)
                  (maybe_p p false) in
    intro_h_exists false (lock_inv_pred r p);
    let l  = L.new_lock (lock_inv r p) in
    let t  =  { r = r ; l = l } in
    return t

let finish (#p:slprop) (t:thread p) (v:bool)
  : SteelT unit (pts_to t.r full v `star` p) (fun _ -> emp)
  = frame (fun _ -> write t.r true) p;
    h_assert (pts_to t.r full true `star` p);
    h_commute (pts_to t.r full true) p;
    frame (fun _ -> intro_maybe_p_true p) (pts_to t.r full true);
    h_commute (maybe_p p true) (pts_to t.r full true);
    intro_h_exists true (lock_inv_pred t.r p);
    L.release t.l

let acquire (#p:slprop) (t:thread p)
  : SteelT bool emp (fun b -> pts_to t.r full b)
  = L.acquire t.l;
    let b = read_refine (maybe_p p) t.r in
    h_affine (pts_to t.r full b) (maybe_p p b);
    return b

let spawn (#p #q:slprop)
          ($f: (unit -> SteelT unit p (fun _ -> q)))
          (t:thread q)
          (_:unit)
  : SteelT unit p (fun _ -> emp)
  = h_intro_emp_l p;
    let b  = frame (fun () -> acquire t) p in
    h_commute (pts_to t.r full b) p;
    let _ = frame f (pts_to t.r full b) in
    h_commute q (pts_to t.r full b);
    finish t b

let fork (#a:Type) (#p #q #r #s:slprop)
      (f: (unit -> SteelT unit p (fun _ -> q)))
      (g: (thread q -> unit -> SteelT unit r (fun _ -> s)))
  : SteelT unit (p `star` r) (fun _ -> s)
  = h_intro_emp_l (p `star` r);
    let t : thread q = frame (fun _ -> new_thread q) (p `star` r) in
    h_assert (emp `star` (p `star` r));
    h_elim_emp_l (p `star` r);
    par (spawn f t) (g t);
    h_elim_emp_l s

let pre (#p:slprop) (t:thread p) (b:bool) : slprop = lock_inv_pred t.r p b
let post (p:slprop) (b:bool) (_:unit) : slprop = p

let join_case_true (#p:slprop) (t:thread p) (_:unit)
  : SteelT unit (pre t true) (post p true)
  = h_commute _ (maybe_p p true);
    h_assert (maybe_p p true `star` pts_to t.r full true);
    h_affine (maybe_p p true) (pts_to t.r full true);
    h_assert (maybe_p p true)

let join_case_false (#p:slprop) (t:thread p) (loop: (t:thread p -> SteelT unit emp (fun _ -> p))) (_:unit)
  : SteelT unit (pre t false) (post p false)
  = intro_h_exists false (lock_inv_pred t.r p);
    L.release t.l;
    loop t

let rec join (#p:slprop) (t:thread p)
  : SteelT unit emp (fun _ -> p)
  = L.acquire t.l;
    let b = read_refine (maybe_p p) t.r in
    h_assert (pts_to t.r full b `star` maybe_p p b);
    h_assert (pre t b);
    cond b (pre t) (post p) (join_case_true t) (join_case_false t (join #p))
