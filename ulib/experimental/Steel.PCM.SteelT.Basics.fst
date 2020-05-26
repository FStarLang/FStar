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

let h_assert (p:slprop)
  : SteelT unit p (fun _ -> p)
  = AB.lift_atomic_to_steelT (fun _ -> AB.h_assert_atomic p)

let h_intro_emp_l (p:slprop)
  : SteelT unit p (fun _ -> emp `star` p)
  = AB.lift_atomic_to_steelT (fun _ -> AB.h_intro_emp_l p)

let h_commute (p q:slprop)
  : SteelT unit (p `star` q) (fun _ -> q `star` p)
  = AB.lift_atomic_to_steelT (fun _ -> AB.h_commute p q)

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
