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
#light "off"
module FStar.Tactics.Embedding

open FStar.Ident
open FStar.Syntax.Syntax
open FStar.Syntax.Embeddings
open FStar.Tactics.Types
open FStar.Tactics.Result
module NBETerm = FStar.TypeChecker.NBETerm

val e_exn          : embedding<exn>
val e_proofstate   : embedding<proofstate>
val e_goal         : embedding<goal>
val e_result       : embedding<'a> -> embedding<__result<'a>>
val e_direction    : embedding<direction>
val e_guard_policy : embedding<guard_policy>

val e_exn_nbe          : NBETerm.embedding<exn>
val e_proofstate_nbe   : NBETerm.embedding<proofstate>
val e_goal_nbe         : NBETerm.embedding<goal>
val e_result_nbe       : NBETerm.embedding<'a> -> NBETerm.embedding<__result<'a>>
val e_direction_nbe    : NBETerm.embedding<direction>
val e_guard_policy_nbe : NBETerm.embedding<guard_policy>

val unfold_lazy_proofstate : lazyinfo -> term
val unfold_lazy_goal       : lazyinfo -> term

val fstar_tactics_lid' : list<string> -> FStar.Ident.lid
