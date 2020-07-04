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

module Steel.Primitive.FramingForkJoin
open Steel.FramingEffect
open Steel.Memory
module L = Steel.SpinLock
open Steel.FractionalPermission
open FStar.Ghost
open Steel.FramingReference
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

// Would be provided by SpinLock
assume
val new_lock (p:slprop)
  : SteelT (L.lock p) p (fun _ -> emp)

assume
val l_acquire (#p:slprop) (l:L.lock p)
  : SteelT unit emp (fun _ -> p)

assume
val release (#p:slprop) (l:L.lock p)
  : SteelT unit p (fun _ -> emp)


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
  = //intro_maybe_p_false p;
    //h_assert (maybe_p p false);
    //h_intro_emp_l (maybe_p p false);
    let r = alloc false in
    intro_exists false (lock_inv_pred r p);
    let l = new_lock (lock_inv r p) in
    let t = {r = r; l = l} in
    t

    // let r = frame #(ref bool) #emp #(fun r -> pts_to r full_perm false)
    //               (fun () -> alloc false)
    //               (maybe_p p false) in
    // intro_h_exists false (lock_inv_pred r p);
    // let l  = L.new_lock (lock_inv r p) in
    // let t  =  { r = r ; l = l } in
    // return t

let finish (#p:slprop) (t:thread p) (v:bool)
  : SteelT unit (pts_to t.r full_perm v `star` p) (fun _ -> emp)
  = write t.r true;
//    intro_maybe_p_true p;
//    intro_lock_inv_pred t.r p true;
    intro_exists true (lock_inv_pred t.r p);
    release t.l

  // frame (fun _ -> write t.r true) p;
  //   h_assert (pts_to t.r full true `star` p);
  //   h_commute (pts_to t.r full true) p;
  //   frame (fun _ -> intro_maybe_p_true p) (pts_to t.r full true);
  //   h_commute (maybe_p p true) (pts_to t.r full true);
  //   intro_h_exists true (lock_inv_pred t.r p);
  //   L.release t.l


let acquire (#p:slprop) (t:thread p)
  : SteelT bool emp (fun b -> pts_to t.r full_perm b)
  = l_acquire t.l;
//    elim_lock_inv t.r p;
    let b = read_refine #_ #full_perm (maybe_p p) t.r in
    drop (maybe_p p b);
    b
    // h_affine (pts_to t.r full b) (maybe_p p b);
    // return b

let spawn (#p #q:slprop)
          ($f: (unit -> SteelT unit p (fun _ -> q)))
          (t:thread q)
          (_:unit)
  : SteelT unit p (fun _ -> emp)
  = let b = acquire t in
    f ();
    finish t b

  // h_intro_emp_l p;
  //   let b  = frame (fun () -> acquire t) p in
  //   h_commute (pts_to t.r full b) p;
  //   let _ = frame f (pts_to t.r full b) in
  //   h_commute q (pts_to t.r full b);
  //   finish t b

let fork (#p #q #r #s:slprop)
      (f: (unit -> SteelT unit p (fun _ -> q)))
      (g: (thread q -> unit -> SteelT unit r (fun _ -> s)))
  : SteelT unit (p `star` r) (fun _ -> s)
  = let t : thread q = new_thread q in
    par (spawn f t) (g t)

  //   h_intro_emp_l (p `star` r);
  //   let t : thread q = frame (fun _ -> new_thread q) (p `star` r) in
  //   h_assert (emp `star` (p `star` r));
  //   h_elim_emp_l (p `star` r);
  //   par (spawn f t) (g t);
  //   h_elim_emp_l s

let join_case_true (#p:slprop) (t:thread p) (_:unit)
  : SteelT unit (lock_inv_pred t.r p true) (fun _ -> p)
  = change_slprop (lock_inv_pred t.r p true) p (fun _ -> ())
  // = h_commute _ (maybe_p p true);
  //   h_assert (maybe_p p true `star` pts_to t.r full true);
  //   h_affine (maybe_p p true) (pts_to t.r full true);
  //   h_assert (maybe_p p true)

let join_case_false (#p:slprop) (t:thread p)
  (loop: (t:thread p -> SteelT unit emp (fun _ -> p))) (_:unit)
  : SteelT unit (lock_inv_pred t.r p false) (fun _ -> p)
  = intro_exists false (lock_inv_pred t.r p);
    release t.l;
    loop t

let rec join (#p:slprop) (t:thread p)
  : SteelT unit emp (fun _ -> p)
  = let _ = l_acquire t.l in
    let b = read_refine #_ #full_perm (maybe_p p) t.r in
    cond b (lock_inv_pred t.r p) (fun _ _ -> p) (join_case_true t) (join_case_false t join)

    // let b = read_refine (maybe_p p) t.r in
    // h_assert (pts_to t.r full b `star` maybe_p p b);
    // h_assert (pre t b);
    // cond b (pre t) (post p) (join_case_true t) (join_case_false t (join #p))
