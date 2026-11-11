(*
   Copyright 2026 Microsoft Research
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
module Pulse.Extrinsic.HeapLang.Loops

(** General source-level while rule. The condition consumes inv and yields
    body_pre when true or exit when false; the body restores inv. There is no
    termination variant, retry bound, or client-visible step index.
    The implementation derives the rule from WP's guarded pure step for loop
    unrolling. An ordinary loop invariant suffices for clients. *)

open Pulse.Extrinsic.HeapLang
module S = PulseCore.IndirectionTheorySep
module P = Pulse.Extrinsic.HeapLang.Proof

let condition_post (body_pre exit:S.slprop) (b:bool) =
  if b then body_pre else exit

val while_rule (inv body_pre exit:S.slprop) (condition:expr [] TBool) (body:expr [] TUnit)
  : Lemma
      (requires P.hoare inv condition (condition_post body_pre exit) /\
        P.hoare body_pre body (P.constant_post inv))
      (ensures P.hoare inv (While condition body) (P.constant_post exit))
