(*
   Copyright 2008-2016 Microsoft Research

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

module FStarC.Tactics.Embedding

open FStarC.Ident
open FStarC.Syntax.Syntax
open FStarC.Syntax.Embeddings
open FStarC.Tactics.Types

module Core = FStarC.TypeChecker.Core

module NBETerm = FStarC.TypeChecker.NBETerm

instance val e_exn                    : embedding exn
instance val e_proofstate             : embedding proofstate
instance val e_goal                   : embedding goal
instance val e_direction              : embedding direction
instance val e_ctrl_flag              : embedding ctrl_flag
instance val e_guard_policy           : embedding guard_policy
instance val e_unfold_side            : embedding Core.side
instance val e_tot_or_ghost           : embedding Core.tot_or_ghost
instance val e_tref (#a:Type)         : Tot (embedding (tref a))
instance val e_ref_proofstate         : embedding ref_proofstate

instance val e_exn_nbe                : NBETerm.embedding exn
instance val e_proofstate_nbe         : NBETerm.embedding proofstate
instance val e_goal_nbe               : NBETerm.embedding goal
instance val e_direction_nbe          : NBETerm.embedding direction
instance val e_ctrl_flag_nbe          : NBETerm.embedding ctrl_flag
instance val e_guard_policy_nbe       : NBETerm.embedding guard_policy
instance val e_unfold_side_nbe        : NBETerm.embedding Core.side
instance val e_tot_or_ghost_nbe       : NBETerm.embedding Core.tot_or_ghost
instance val e_tref_nbe (#a:Type)     : Tot (NBETerm.embedding (tref a))
instance val e_ref_proofstate_nbe     : NBETerm.embedding ref_proofstate

val unfold_lazy_ref_proofstate : lazyinfo -> term
val unfold_lazy_proofstate   : lazyinfo -> term
val unfold_lazy_goal         : lazyinfo -> term
