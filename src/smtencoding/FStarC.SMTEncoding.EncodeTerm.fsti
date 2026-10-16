(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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

module FStarC.SMTEncoding.EncodeTerm
open FStarC.Effect
open FStarC
open FStarC.TypeChecker.Env
open FStarC.Syntax
open FStarC.Syntax.Syntax
open FStarC.TypeChecker
open FStarC.SMTEncoding.Term
open FStarC.Ident
open FStarC.Const
open FStarC.SMTEncoding
open FStarC.SMTEncoding.Util
open FStarC.SMTEncoding.Env

val mkForall_fuel : string -> Range.t -> (list (list pat) & fvs & term -> ML term)  //first arg is the module name

val head_normal : env_t -> Syntax.term -> ML bool

val whnf: env_t -> Syntax.term -> ML Syntax.term
val norm: env_t -> Syntax.term -> ML Syntax.term

val mk_Apply : e:term -> vars:fvs -> ML term
val raise_arity_mismatch : head:string -> arity:int -> n_args:int -> rng:Range.t -> ML 'a
val isTotFun_axioms: Range.t -> head:term -> extra_vars:fvs -> vars:fvs -> guards:list term -> bool -> ML term
val maybe_curry_app : rng:Range.t -> head:either op term -> arity:int -> args:list term -> ML term
val maybe_curry_fvb : rng:Range.t -> head:fvar_binding -> args:list term -> ML term

val curried_arrow_formals_comp : k:Syntax.term -> ML (Syntax.binders & comp)

val encode_univ_name : Syntax.univ_name -> ML (fv & term)
val encode_universe : Syntax.universe -> ML term

val encode_binders : fuel_opt:option term
                  -> bs:Syntax.binders
                  -> env:env_t
                  -> ML (list fv & list term & env_t & decls_t & list bv)

(* [unit_refinements env t] returns [Some fs] when [t] is (a nest of
   refinements over) the unit type, where [fs] are the refinement formulas
   instantiated at the unit constant. In that case a binder of type [t] need
   not be encoded as an SMT variable at all: it can be replaced by the unit
   constant, with [fs] as its only remaining content. *)
val unit_refinements : env:env_t -> t:typ -> ML (option (list Syntax.term))

(* Encodes the conjunction of the formulas returned by [unit_refinements]. *)
val encode_unit_refinements : env:env_t -> fs:list Syntax.term -> ML (term & decls_t)

val encode_term_pred: fuel_opt:option term
                    -> t:typ
                    -> env:env_t
                    -> e:term
                    -> ML (term & decls_t)

(* As [encode_term_pred], but inlines a refinement type [x:b{phi}] as
   [HasTypeFuel fuel e b /\ phi[e/x]] rather than introducing a [Tm_refine_...]
   type constructor and relying on its interpretation axiom. Only appropriate
   where the resulting predicate is used as a guard/hypothesis or goal, not
   where the type itself is needed as a first-class term. *)
val encode_term_pred_inline_refinements
                    : fuel_opt:option term
                    -> t:typ
                    -> env:env_t
                    -> e:term
                    -> ML (term & decls_t)

val encode_term : t:typ       (* expects t to be in normal form already *)
               -> env:env_t
               -> ML (term & decls_t)

val encode_args : l:args -> env:env_t -> ML (list term & decls_t)

val encode_formula : phi:typ -> env:env_t -> ML (term & decls_t)

(* Encode the pattern of a branch against an already-encoded scrutinee.
   Returns the guard under which the branch is taken, the (opened) pattern and
   body, and an environment in which the pattern variables are bound to the
   corresponding projections of the scrutinee. *)
val encode_branch_pattern : env:env_t
                         -> scr:term
                         -> b:Syntax.branch
                         -> ML (term & Syntax.pat & Syntax.term & env_t & decls_t)

val encode_function_type_as_formula : t:typ -> env:env_t -> ML (term & decls_t)
