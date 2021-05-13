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
   limitations under the License.o
*)

module Steel.Utils
open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Steel.FractionalPermission
open Steel.Reference

let pts_to_not_null (#a:Type)
                    (#opened:inames)
                    (#p:perm)
                    (#v:FStar.Ghost.erased a)
                    (r:ref a)
  : SteelGhost unit opened
    (pts_to r p v)
    (fun _ -> pts_to r p v)
    (fun _ -> True)
    (fun _ _ _ -> r =!= null)
  = extract_info_raw (pts_to r p v) (r =!= null)
      (fun m -> pts_to_not_null r p v m)

let change_slprop_ens (p:vprop) (q:vprop) (r:prop) (f:(m:mem -> Lemma (requires interp (hp_of p) m)
                                                                       (ensures interp (hp_of q) m /\ r)))
  : Steel unit p (fun _ -> q) (requires fun _ -> True) (ensures fun _ _ _ -> r)
  = rewrite_slprop p (q `star` pure r)
                                 (fun m -> f m;
                                        Steel.Memory.emp_unit (hp_of q);
                                        Steel.Memory.pure_star_interp (hp_of q) r m);
    elim_pure r

let pure_as_ens (#p:prop) ()
  : Steel unit (pure p) (fun _ -> pure p) (fun _ -> True) (fun _ _ _ -> p)
  = change_slprop_ens (pure p) (pure p) p (Steel.Memory.pure_interp p)

let rewrite #a (#p:a -> vprop) (x y:a)
  : Steel unit (p x) (fun _ -> p y)
    (requires fun _ -> x == y)
    (ensures fun _ _ _ -> True)
  = rewrite_slprop (p x) (p y) (fun _ -> ())

let extract_pure (p:prop)
  : Steel unit (pure p) (fun _ -> pure p) (fun _ -> True) (fun _ _ _ -> p)
  = elim_pure p;
    intro_pure p

let dup_pure (p:prop)
  : SteelT unit (pure p) (fun _ -> pure p `star` pure p)
  = extract_pure p;
    intro_pure p

let emp_unit (p:vprop)
  : Lemma (((p `star` emp) `equiv` p) /\
           ((emp `star` p) `equiv` p))
          [SMTPatOr [[SMTPat (p `star` emp)];
                     [SMTPat (emp `star` p)]]]
  = reveal_equiv (p `star` emp) p;
    reveal_equiv (emp `star` p) p;
    reveal_emp ();
    Steel.Memory.emp_unit (hp_of p);
    Steel.Memory.star_commutative Steel.Memory.emp (hp_of p)
