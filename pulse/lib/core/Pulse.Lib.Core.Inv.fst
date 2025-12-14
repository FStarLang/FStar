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
module Pulse.Lib.Core.Inv
friend PulseCore.InstantiatedSemantics
friend Pulse.Lib.Core
module I = PulseCore.InstantiatedSemantics
module A = PulseCore.Atomic
module T = FStar.Tactics.V2
open PulseCore.InstantiatedSemantics
open PulseCore.FractionalPermission
open PulseCore.Observability
module Sep = PulseCore.IndirectionTheorySep

(* Invariants, just reexport *)
module Act = PulseCore.Action

let inv = Act.inv

let on_inv_eq = Sep.on_inv_eq

////////////////////////////////////////////////////////////////////
// Invariants
////////////////////////////////////////////////////////////////////
let dup_inv = A.dup_inv
let fresh_invariant i p = A.fresh_invariant i p
let with_invariant i f = A.with_invariant i f
let invariant_name_identifies_invariant #p #q i j = A.invariant_name_identifies_invariant p q i j
