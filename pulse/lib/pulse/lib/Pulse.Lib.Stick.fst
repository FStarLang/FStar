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

module Pulse.Lib.Stick

open Pulse.Lib.Pervasives
module T = Pulse.Lib.Trade

(* This lemma needed to typecheck the definitions below. *)
let emp_unit_left (p:slprop)
  : Lemma (emp ** p == p)
          [SMTPat (emp ** p)]
  = elim_slprop_equiv (slprop_equiv_unit p)

(* This module is just a special case of trades. The tactic
instantiates the implicit InvList to [] everywhere. We do not
even need to use the Pulse checker for it. *)

let stick (p q : slprop) =
  T.trade p q

let elim_stick p q =
  T.elim_trade p q

let intro_stick p q v f =
  T.intro_trade p q v f
