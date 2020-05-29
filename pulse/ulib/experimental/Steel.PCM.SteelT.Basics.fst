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

module Steel.PCM.SteelT.Basics
open Steel.PCM.Effect
open Steel.PCM.Memory
module AB = Steel.PCM.Effect.Atomic

#push-options "--fuel 0 --ifuel 0 --z3rlimit 20"
let return (#a:Type) (#p:a -> slprop) (x:a)
  : SteelT a (p x) p
  = AB.lift_atomic_to_steelT (fun _ -> AB.return_atomic #_ #Set.empty #p x)

assume
val h_admit (#a:Type) (p:slprop) (q: a -> slprop)
  : SteelT a p q
  
let intro_h_exists (#a:Type) (x:a) (p:(a -> slprop))
  : SteelT unit (p x) (fun _ -> h_exists p)
  = AB.lift_atomic_to_steelT (fun _ -> AB.intro_h_exists x p)

let intro_h_exists_erased (#a:Type) (x:Ghost.erased a) (p:(a -> slprop))
  : SteelT unit (p x) (fun _ -> h_exists p)
  = AB.lift_atomic_to_steelT (fun _ -> AB.intro_h_exists_erased x p)

let witness_h_exists (#a:Type) (#p:a -> slprop) (_:unit)
  : SteelT (Ghost.erased a) (h_exists p) (fun x -> p x)
  = AB.lift_atomic_to_steelT AB.witness_h_exists

let intro_pure (#p:slprop) (q:prop { q })
  : SteelT unit p (fun _ -> p `star` pure q)
  = AB.lift_atomic_to_steelT (fun _ -> AB.intro_pure q)

let h_assert (p:slprop)
  : SteelT unit p (fun _ -> p)
  = AB.lift_atomic_to_steelT (fun _ -> AB.h_assert_atomic p)

let h_intro_emp_l (p:slprop)
  : SteelT unit p (fun _ -> emp `star` p)
  = AB.lift_atomic_to_steelT (fun _ -> AB.h_intro_emp_l p)

let h_commute (p q:slprop)
  : SteelT unit (p `star` q) (fun _ -> q `star` p)
  = AB.lift_atomic_to_steelT (fun _ -> AB.h_commute p q)

let h_assoc_r (#p #q #r:slprop) (_:unit)
  : SteelT unit ((p `star` q) `star` r) (fun _ -> p `star` (q `star` r))
  = AB.lift_atomic_to_steelT (fun _ -> 
    AB.change_slprop _ _ (fun m -> star_associative p q r))

let h_assoc_l (#p #q #r:slprop) (_:unit)
  : SteelT unit (p `star` (q `star` r)) (fun _ -> (p `star` q) `star` r)
  = AB.lift_atomic_to_steelT (fun _ -> 
    AB.change_slprop _ _ (fun m -> star_associative p q r))

let h_affine (p q:slprop)
  : SteelT unit (p `star` q) (fun _ -> p)
  = AB.lift_atomic_to_steelT (fun _ -> AB.h_affine p q)

let par' (#preL:slprop) (#postL:unit -> slprop)
         ($f:unit -> SteelT unit preL postL)
         (#preR:slprop) (#postR:unit -> slprop)
         ($g:unit -> SteelT unit preR postR)
  : SteelT (unit & unit)
    (preL `star` preR)
    (fun x -> postL (fst x) `star` postR (snd x))
  = par f g 

let par (#preL:slprop) (#postL:unit -> slprop)
        ($f:unit -> SteelT unit preL postL)
        (#preR:slprop) (#postR:unit -> slprop)
        ($g:unit -> SteelT unit preR postR)
  : SteelT unit
    (preL `star` preR)
    (fun x -> postL () `star` postR ())
  = let x = par' f g in return ()

let h_elim_emp_l (p:slprop)
  : SteelT unit (emp `star` p) (fun _ -> p)
  = AB.lift_atomic_to_steelT (fun _ -> AB.h_elim_emp_l p)

let frame (#a:Type) (#pre:slprop) (#post:a -> slprop)
          ($f:unit -> SteelT a pre post)
          (frame:slprop)
  : SteelT a
    (pre `star` frame)
    (fun x -> post x `star` frame)
  = Steel.PCM.Effect.frame f frame (fun _ -> True)

let noop (#p:slprop) (u:unit) : SteelT unit p (fun _ -> p)
  = return ()

let change_slprop
  (p q:slprop)
  (proof: (m:mem) -> Lemma (requires interp p m) (ensures interp q m))
  : SteelT unit p (fun _ -> q)
  = AB.lift_atomic_to_steelT (fun () -> AB.change_slprop p q proof)

let drop (p:slprop)
  : SteelT unit p (fun _ -> emp)
  = AB.lift_atomic_to_steelT (fun _ ->
    AB.change_slprop _ _ (fun m -> emp_unit p; affine_star p emp m))

let drop_r (p q:slprop)
  : SteelT unit (p `star` q) (fun _ -> p)
  = AB.lift_atomic_to_steelT (fun _ ->
    AB.change_slprop _ _ (fun m -> affine_star p q m))

let weaken_pure (f:slprop) (p:prop) (q:prop{p ==> q})
  : SteelT unit (f `star` pure p) (fun _ -> f `star` pure q)
  = AB.lift_atomic_to_steelT (fun _ ->
    AB.change_slprop _ _ (fun m -> pure_star_interp f p m; pure_star_interp f q m))

let extract_pure (p:prop)
  : SteelT (_:unit{p}) (pure p) (fun _ -> pure p)
  = let u = AB.lift_atomic_to_steelT (fun _ -> AB.elim_pure p) in
    intro_pure p;
    h_assert (emp `star` pure p);
    h_commute _ _;
    drop_r _ _;
    return u

module U = FStar.Universe
let lift_h_exists (#a:_) (p:a -> slprop)
  : SteelT unit (h_exists p)
                (fun _ -> h_exists #(U.raise_t a) (U.lift_dom p))
  = AB.lift_atomic_to_steelT (fun _ -> AB.lift_h_exists_atomic p)

let h_exists_cong (#a:_) (p:a -> slprop) (q:a -> slprop {forall x. equiv (p x) (q x) })
  : SteelT unit (h_exists p)
                (fun _ -> h_exists q)
  = AB.lift_atomic_to_steelT (fun _ -> AB.h_exists_cong_atomic p q)

