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

module FStarC.TypeChecker.TcTerm
open FStarC.Effect
open FStarC
open FStarC.TypeChecker
open FStarC.TypeChecker.Env
open FStarC.Ident
open FStarC.Syntax
open FStarC.Syntax.Syntax
open FStarC.Syntax.Subst
open FStarC.Syntax.Util
open FStarC.Const
open FStarC.TypeChecker.Rel
open FStarC.TypeChecker.Common

val value_check_expected_typ: env -> term -> either typ lcomp -> guard_t -> ML (term & lcomp & guard_t)
val comp_check_expected_typ: env -> term -> lcomp -> ML (term & lcomp & guard_t)
val check_expected_effect: env -> use_eq:bool -> option comp -> (term & comp) -> ML (term & comp & guard_t)

val tc_term: env -> term -> ML (term & lcomp & guard_t)
val tc_maybe_toplevel_term: env -> term -> ML (term & lcomp & guard_t)
val tc_tactic : typ -> typ -> env -> term -> ML (term & lcomp & guard_t)
val tc_constant: env -> FStarC.Range.t -> sconst -> ML typ
val tc_comp: env -> comp -> ML (comp & universe & guard_t)
val tc_pat : Env.env -> typ -> pat -> ML (pat & list bv & list term & Env.env & term & term & guard_t & bool)
val tc_binders: env -> binders -> ML (binders & env & guard_t & universes)
val tc_tot_or_gtot_term: env -> term -> ML (term & lcomp & guard_t)
//the last string argument is the reason to be printed in the error message
//pass "" if NA
val tc_check_tot_or_gtot_term: env -> term -> typ -> option string -> ML (term & lcomp & guard_t)
val tc_trivial_guard: env -> term -> ML (term & lcomp)
val tc_attributes: env -> list term -> ML (guard_t & list term)
val tc_check_trivial_guard: env -> term -> term -> ML term

val typeof_tot_or_gtot_term: env -> term -> must_tot:bool -> ML (term & typ & guard_t)
val level_of_type: env -> term -> typ -> ML universe //the term argument is for error reporting only
val universe_of: env -> term -> ML universe
val tc_tparams: env_t -> binders -> ML (binders & Env.env & universes)
val typeof_tot_or_gtot_term_fastpath: env -> term -> Env.must_tot -> ML (option typ)
