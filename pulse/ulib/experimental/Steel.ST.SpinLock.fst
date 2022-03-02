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

module Steel.ST.SpinLock

open FStar.Ghost

open Steel.ST.Effect
open Steel.ST.Effect.Ghost
open Steel.ST.Effect.Atomic

open Steel.ST.Util
open Steel.ST.Loops
open Steel.ST.Reference

let locked = true
let unlocked = false

[@@ __reduce__]
let lockinv_predicate (p:vprop) (r:ref bool)
  : bool -> vprop
  = fun (b:bool) -> pts_to r full_perm b `star` (if b then emp else p)

[@@ __reduce__]
let lockinv (p:vprop) (r:ref bool) : vprop =
  exists_ (lockinv_predicate p r)

let lock_t = ref bool & erased iname
let protects l p = snd l >--> lockinv p (fst l)

let new_lock p =
  let r = alloc unlocked in
  rewrite (pts_to _ _ _ `star` p)
          (lockinv_predicate p r unlocked);
  intro_exists unlocked (lockinv_predicate p r);
  let i = new_invariant (lockinv p r) in
  return (r, i)

[@@ __reduce__]
let acquire_loop_inv (p:vprop) : bool -> vprop =
  fun b -> if b then emp else p

inline_for_extraction
let acquire_core (#opened:_) (p:vprop) (r:ref bool) ()
  : STAtomicT bool opened
      (lockinv p r `star` exists_ (acquire_loop_inv p))
      (fun b -> lockinv p r `star` acquire_loop_inv p b)
  = let w = elim_exists #_ #_ #(lockinv_predicate p r) () in
    drop (exists_ _);
    let b = cas r w unlocked locked in
    if b
    then begin
      let res = false in
      rewrite (if w then emp else p) p;
      rewrite ((if b then _ else _) `star` emp)
              (lockinv_predicate p r locked);
      intro_exists locked (lockinv_predicate p r);
      rewrite p (acquire_loop_inv p res);
      return res
    end
    else begin
      let res = true in
      rewrite (if b then _ else _)
              (pts_to r full_perm w);
      intro_exists (Ghost.reveal w) (lockinv_predicate p r);
      rewrite emp (acquire_loop_inv p res);
      return res
    end

inline_for_extraction
let acquire_loop_cond (p:vprop) (r:ref bool) (i:inv (lockinv p r)) ()
  : STT bool (exists_ (acquire_loop_inv p))
             (fun b -> acquire_loop_inv p b)
  = with_invariant i (acquire_core p r)

inline_for_extraction
let acquire_loop_body (p:vprop) (r:ref bool) ()
  : STT unit (acquire_loop_inv p true)
             (fun _ -> exists_ (acquire_loop_inv p))
  = intro_exists true (acquire_loop_inv p)

let acquire #p l =
  rewrite emp (acquire_loop_inv p true);
  intro_exists true (acquire_loop_inv p);
  while_loop
    (acquire_loop_inv p)
    (acquire_loop_cond p (fst l) (snd l))
    (acquire_loop_body p (fst l));
  rewrite (acquire_loop_inv p false) p

inline_for_extraction
let release_core (#opened:_) (p:vprop) (r:ref bool) ()
  : STAtomicT unit opened
      (lockinv p r `star` p)
      (fun _ -> lockinv p r `star` emp)
  = let _ = elim_exists () in
    drop (if _ then _ else _);
    atomic_write r unlocked;
    rewrite p (if unlocked then emp else p);
    intro_exists unlocked (lockinv_predicate p r)

let release #p l = with_invariant (snd l) (release_core p (fst l))
