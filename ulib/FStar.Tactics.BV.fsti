(*
   Copyright 2008-2018 Microsoft Research

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
module FStar.Tactics.BV

open FStar.Tactics.Effect
open FStar.Tactics.BV.Lemmas {} (* bring into tc scope, since the tactic calls the lemmas *)

[@@plugin]
val arith_to_bv_tac () : Tac unit

[@@plugin]
val bv_tac () : Tac unit

[@@plugin]
val bv_tac_lt (n:int) : Tac unit

[@@plugin]
val to_bv_tac () : Tac unit