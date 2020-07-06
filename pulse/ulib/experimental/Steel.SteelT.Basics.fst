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

module Steel.SteelT.Basics
open Steel.Effect
open Steel.Memory
open Steel.HigherReference
module AB = Steel.SteelAtomic.Basics

#push-options "--fuel 0 --ifuel 0 --z3rlimit 20"
let return (#a:Type) (#p:a -> hprop) (x:a)
  : SteelT a (p x) p
  = AB.return_atomic #_ #Set.empty #p x

let intro_h_exists (#a:Type) (x:a) (p:(a -> hprop))
  : SteelT unit (p x) (fun _ -> h_exists p)
  = AB.intro_h_exists x p

let h_assert (p:hprop)
  : SteelT unit p (fun _ -> p)
  = AB.h_assert_atomic p

let h_intro_emp_l (p:hprop)
  : SteelT unit p (fun _ -> emp `star` p)
  = AB.h_intro_emp_l p

let h_commute (p q:hprop)
  : SteelT unit (p `star` q) (fun _ -> q `star` p)
  = AB.h_commute p q

let h_affine (p q:hprop)
  : SteelT unit (p `star` q) (fun _ -> p)
  = AB.h_affine p q

let par' (#preL:pre_t) (#postL:post_t unit)
        ($f:unit -> SteelT unit preL postL)
        (#preR:pre_t) (#postR:post_t unit)
        ($g:unit -> SteelT unit preR postR)
  : SteelT (unit & unit)
    (preL `star` preR)
    (fun x -> postL (fst x) `star` postR (snd x))
  = par f g

let par (#preL:pre_t) (#postL:post_t unit)
        ($f:unit -> SteelT unit preL postL)
        (#preR:pre_t) (#postR:post_t unit)
        ($g:unit -> SteelT unit preR postR)
  : SteelT unit
    (preL `star` preR)
    (fun x -> postL () `star` postR ())
  = let x = par' f g in return ()

let h_elim_emp_l (p:hprop)
  : SteelT unit (emp `star` p) (fun _ -> p)
  = AB.h_elim_emp_l p

let frame (#a:Type) (#pre:pre_t) (#post:post_t a)
          ($f:unit -> SteelT a pre post)
          (frame:hprop)
  : SteelT a
    (pre `star` frame)
    (fun x -> post x `star` frame)
  = steel_frame f frame (fun _ -> True)

let noop (#p:hprop) (u:unit) : SteelT unit p (fun _ -> p)
  = return ()
