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
open Pulse.Lib.Core
open FStar.Ghost
open PulseCore.FractionalPermission
open PulseCore.Observability
open FStar.PCM
open FStar.ExtractAs
module T = FStar.Tactics.V2

val inv (i:iname) (p:slprop) : slprop

val on_inv_eq l i p : squash (on l (inv i p) == inv i p)

val dup_inv (i:iname) (p:slprop)
  : stt_ghost unit emp_inames (inv i p) (fun _ -> inv i p ** inv i p)

val fresh_invariant
    (ctx:inames { Pulse.Lib.GhostSet.is_finite ctx })
    (p:slprop)
: stt_ghost (i:iname { ~(i `GhostSet.mem` ctx) }) emp_inames p (fun i -> inv i p)

let somewhere (p: slprop) = exists* l. on l p

inline_for_extraction [@@extract_as
    (`(fun (#a:Type0) (#obs #fp #fp' #f_opens #p i:unit) (f:unit -> Dv a) ->
        f ()))]
val with_invariant
    (#a:Type u#a)
    (#obs:_)
    (#fp:slprop)
    (#fp':a -> slprop)
    (#f_opens:inames)
    (#p:slprop)
    (i:iname { not (mem_inv f_opens i) })
    (f:(unit -> stt_atomic a #obs f_opens (somewhere (later p) ** fp) (fun x -> somewhere (later p) ** fp' x)))
: stt_atomic a #obs (add_inv f_opens i) (inv i p ** fp) (fun x -> inv i p ** fp' x)

[@@allow_ambiguous]
val invariant_name_identifies_invariant
      (#p #q:slprop)
      (i:iname)
      (j:iname { i == j } )
: stt_ghost
    unit
    emp_inames
    (inv i p ** inv j q)
    (fun _ -> inv i p ** inv j q ** later (equiv p q))
