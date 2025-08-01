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
val isTotFun_axioms: Range.t -> head:term -> vars:fvs -> guards:list term -> bool -> term
val mk_Apply : e:term -> vars:fvs -> term
val maybe_curry_app : rng:Range.t -> head:either op term -> arity:int -> args:list term -> term
val maybe_curry_fvb : rng:Range.t -> head:fvar_binding -> args:list term -> term
val mkForall_fuel : string -> Range.t -> (list (list pat) & fvs & term -> term)  //first arg is the module name

val head_normal : env_t -> Syntax.term -> bool

val whnf: env_t -> Syntax.term -> Syntax.term
val norm: env_t -> Syntax.term -> Syntax.term

val curried_arrow_formals_comp : k:Syntax.term -> Syntax.binders & comp

val raise_arity_mismatch : head:string -> arity:int -> n_args:int -> rng:Range.t -> 'a

val encode_term : t:typ       (* expects t to be in normal form already *)
               -> env:env_t
               -> term & decls_t

val encode_term_pred: fuel_opt:option term
                    -> t:typ
                    -> env:env_t
                    -> e:term
                    -> term & decls_t

val encode_args : l:args -> env:env_t -> list term & decls_t

val encode_formula : phi:typ -> env:env_t -> term & decls_t

val encode_function_type_as_formula : t:typ -> env:env_t -> term & decls_t

val encode_binders : fuel_opt:option term
                  -> bs:Syntax.binders
                  -> env:env_t
                  -> list fv & list term & env_t & decls_t & list bv
