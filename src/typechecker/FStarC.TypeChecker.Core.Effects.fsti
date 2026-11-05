(*
   Copyright Microsoft Research

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
module FStarC.TypeChecker.Core.Effects

(* Effects in the core typechecker (see FStarC.TypeChecker.Core): reading
   the effect of a computation type, building one from an effect, and the
   effect lattice (joins and sub-effecting), as the checker sees it (see
   [Core.Base.eff]). *)

open FStarC
open FStarC.Effect
open FStarC.Syntax.Syntax
open FStarC.TypeChecker.Core.Base
open FStarC.TypeChecker.Core.Monad
module Env = FStarC.TypeChecker.Env
module I = FStarC.Ident

(* The effect of a computation type. *)
val comp_eff (c:comp) : ML eff

(* Whether [t] is non-informative, so that a ghost computation of type [t]
   may be promoted to a total one. *)
val is_non_informative (g:Env.env) (t:typ) : ML bool

val non_informative (g:env) (t:typ) : ML bool

(* The computation type of effect [m] and result type [t], with no
   flags. *)
val mk_comp_of_eff (m:I.lident) (t:typ) : ML comp

(* The computation type of an effect and a type; a ghost one of a
   non-informative type is total. *)
val as_comp (g:env) (et: (eff & typ)) : ML comp

val comp_as_eff_and_type (c:comp) : ML (eff & typ)

val is_tot_or_ghost_eff (e:eff) : ML bool

(* [e], of type [t_e] and effect [e_eff], was expected to have effect
   [target_eff] (and type [target_t]): fail as TcTerm does. *)
val fail_effect_mismatch (#a:Type) (g:env) (e:term) (t_e:typ) (e_eff:eff) (target_t:typ) (target_eff:eff)
  : ML (result a)

(* The least effect both [e0] and [e1] lift to, if any. *)
val join_eff (g:env) (e0 e1:eff) : ML (result eff)

(* The least effect all of [es] lift to, if any; [Tot] if [es] is empty. *)
val join_eff_l (g:env) (es:list eff) : ML (result eff)

(* Whether [e0] may be used where [e1] is expected. *)
val sub_eff (g:env) (e0 e1:eff) : ML bool
