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
(* Small utilities for building and simplifying verification conditions,
   shared by the elaborator ([TcTerm], [TcUtil], [Rel]) and by Core, which
   generates the VCs. They depend only on the syntax, the environment and
   the normalizer. *)
module FStarC.TypeChecker.VCUtil

open FStarC
open FStarC.Effect
open FStarC.Syntax.Syntax
open FStarC.TypeChecker.CommonBase
module Env = FStarC.TypeChecker.Env

(* Label the goal [f] with an error message, at [r]. *)
val label : list Pprint.document -> Range.t -> typ -> ML typ

(* A type with at most one inhabitant: [unit] and any refinement of it,
   including [squash p]. *)
val is_unit_like (t:term) : ML bool

(* A match whose scrutinee is stuck for the SMT solver: neither a
   constructor application nor a literal. *)
val is_stuck_match (e:term) : ML bool

(* Whether the result of the computation [e] (of type [c]) is worth equating
   with [e], see the implementation. *)
val should_return (env:Env.env) (eopt:option term) (c:comp) : ML bool

(* Refine the result type of [c] with [_ == e] (in effect [m_opt], if any). *)
val assume_result_eq_pure_term_in_m (env:Env.env) (m_opt:option Ident.lident) (e:term) (c:comp) : ML comp

(* As [assume_result_eq_pure_term_in_m], if [should_return env (Some e) c]. *)
val maybe_assume_result_eq_pure_term_in_m (env:Env.env) (m_opt:option Ident.lident) (e:term) (c:comp) : ML comp

val maybe_assume_result_eq_pure_term (env:Env.env) (e:term) (c:comp) : ML comp

(* For a short-circuiting operator [head] ([&&], [||], [/\], [\/], [==>] or
   [if_then_else]), applied to [seen_args] (from right to left), the
   hypothesis under which its next argument is checked. *)
val short_circuit (head:term) (seen_args:args) : ML guard_formula

(* Whether [t] is an application of a short-circuiting operator. *)
val short_circuit_head (t:term) : ML bool

(* Whether an equation between two terms whose head symbol is [head] may be
   left to the SMT solver: [is_eq] for an equation, rather than a
   subtyping. *)
val may_relate_by_smt (env:Env.env) (is_eq:bool) (head:typ) : ML bool

(* Simplify a VC with the normalizer, without dropping it under [admit].
   With [full_norm_allowed], also reduce under binders. *)
val simplify_vc (full_norm_allowed:bool) (env:Env.env) (t:term) : ML term
