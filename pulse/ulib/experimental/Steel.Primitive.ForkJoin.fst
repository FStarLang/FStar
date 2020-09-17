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
//open Steel.SteelT.Basics

//module U = FStar.Universe

////////////////////////////////////////////////////////////////////////////////

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

// From basics
assume
val drop (p:slprop) : SteelT unit p (fun _ -> emp)

assume val intro_exists (#a:Type) (x:a) (p:a -> slprop)
  : SteelT unit (p x) (fun _ -> h_exists p)

assume
val change_slprop
  (p q:slprop)
  (proof: (m:mem) -> Lemma (requires interp p m) (ensures interp q m))
  : SteelT unit p (fun _ -> q)

assume
val par (#preL:slprop) (#postL:unit -> slprop)
        ($f:unit -> SteelT unit preL postL)
        (#preR:slprop) (#postR:unit -> slprop)
        ($g:unit -> SteelT unit preR postR)
  : SteelT unit
    (preL `star` preR)
    (fun x -> postL () `star` postR ())

assume
val cond (#a:Type) (b:bool) (p: bool -> slprop) (q: bool -> a -> slprop)
         (then_: (unit -> SteelT a (p true) (q true)))
         (else_: (unit -> SteelT a (p false) (q false)))
  : SteelT a (p b) (q b)


let intro_maybe_p_false (p:slprop)
  : SteelT unit emp (fun _ -> maybe_p p false)
  = change_slprop emp (maybe_p p false) (fun _ -> ())

let intro_maybe_p_true (p:slprop)
  : SteelT unit p (fun _ -> maybe_p p true)
  = change_slprop p (maybe_p p true) (fun _ -> ())

let intro_lock_inv_pred (r:ref bool) (p:slprop) (v:bool)
  : SteelT unit
      (pts_to r full_perm v `star` maybe_p p v)
      (fun _ -> lock_inv_pred r p v)
  = change_slprop (pts_to r full_perm v `star` maybe_p p v) (lock_inv_pred r p v) (fun _ -> ())


let new_thread (p:slprop)
  : SteelT (thread p) emp (fun _ -> emp)
  = let r = alloc false in
    change_slprop (pts_to r full_perm false `star` emp) (lock_inv_pred r p false) (fun _ -> ());
    intro_exists false (lock_inv_pred r p);
    let l = L.new_lock (lock_inv r p) in
    let t = {r = r; l = l} in
    t

let finish (#p:slprop) (t:thread p) (v:bool)
  : SteelT unit (pts_to t.r full_perm v `star` p) (fun _ -> emp)
  = write t.r true;
    change_slprop (pts_to t.r full_perm true `star` p) (lock_inv_pred t.r p true) (fun _ -> ());
    intro_exists true (lock_inv_pred t.r p);
    L.release t.l


let acquire (#p:slprop) (t:thread p)
  : SteelT bool emp (fun b -> pts_to t.r full_perm b)
  = L.acquire t.l;
    let b = read_refine #_ #full_perm (maybe_p p) t.r in
    drop (maybe_p p b);
    b

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
    par (spawn f t) (g t)

let join_case_true (#p:slprop) (t:thread p) (_:unit)
  : SteelT unit (lock_inv_pred t.r p true) (fun _ -> p)
  = change_slprop (lock_inv_pred t.r p true) p (fun _ -> ())

let join_case_false (#p:slprop) (t:thread p)
  (loop: (t:thread p -> SteelT unit emp (fun _ -> p))) (_:unit)
  : SteelT unit (lock_inv_pred t.r p false) (fun _ -> p)
  = intro_exists false (lock_inv_pred t.r p);
    L.release t.l;
    loop t

let rec join (#p:slprop) (t:thread p)
  : SteelT unit emp (fun _ -> p)
  = let _ = L.acquire t.l in
    let b = read_refine #_ #full_perm (maybe_p p) t.r in
    cond b (lock_inv_pred t.r p) (fun _ _ -> p) (join_case_true t) (join_case_false t join)
