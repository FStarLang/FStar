(*
   Copyright 2023 Microsoft Research

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

module Pulse.Checker.Prover.Normalize

module T = FStar.Tactics.V2

open Pulse.Syntax
open Pulse.Typing
module PCP = Pulse.Checker.Pure
module PS = Pulse.Checker.Prover.Substs
open Pulse.Checker.Base

let __normalize_slprop
  (g:env)
  (v:slprop)
  : T.Tac slprop
=
  (* Keep things reduced *)
  let steps = [unascribe; primops; iota] in

  (* NOTE: whatever we unfold or reduce here will also apply for pure
  slprops and under lambdas, so be conservative. Adding fst/snd here
  to reduce into the projectors caused some breakages in pure slprops
  mentioning them (L.map fst l == ...) as it introduced hash-consed
  lambdas. *)

  (* Unfold anything marked with the "pulse_unfold" attribute. *)
  let steps = steps @ [delta_attr ["Pulse.Lib.Core.pulse_unfold"; "Pulse.Lib.Core.pulse_eager_unfold"]] in
  (* Unfold anything marked with F*'s "unfold" qualifier . *)
  let steps = steps @ [delta_qualifier ["unfold"]] in
  (* Unfold recursive definitions too, but only the ones that match the filters above. *)
  let steps = steps @ [zeta; simplify] in

  let v' = PCP.norm_well_typed_term (elab_env g) steps v in
  let v' = Pulse.Simplify.simplify v' in (* NOTE: the simplify stage is unverified *)
  v'

let normalize_slprop
  (g:env)
  (v:slprop)
  (use_rewrites_to : bool)
  : T.Tac slprop
=
  if use_rewrites_to then
    let rwr = Pulse.Checker.Prover.RewritesTo.get_subst_from_env g in
    let v' = PS.ss_term v rwr in
    let v'' = __normalize_slprop g v' in
    v''
  else
    __normalize_slprop g v

let normalize_slprop_welltyped
  (g:env)
  (v:slprop)
  : T.Tac slprop
=
  let v' = normalize_slprop g v true in
  // FIXME: prove (or add axiom) that equiv preserves typing
  v'