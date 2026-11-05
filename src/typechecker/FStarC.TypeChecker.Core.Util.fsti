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
module FStarC.TypeChecker.Core.Util

(* Utilities of the core typechecker (see FStarC.TypeChecker.Core) on
   terms, types and patterns, that do not call back into the checker. *)

open FStarC
open FStarC.Effect
open FStarC.Syntax.Syntax
open FStarC.TypeChecker.Core.Base
open FStarC.TypeChecker.Core.Monad

(*** Terms *)

(* Syntactic equality, up to delayed substitutions and solved uvars. *)
val equal_term (t1 t2:term) : ML bool

val mk_type (u:universe) : ML term

val mk_exists_unrefined (u:universe) (x:bv) (body:term) : ML term

(* Whether [d] occurs as a subterm of [t]. *)
val occurs_in (d:term) (t:term) : ML bool

(* Whether the SMT solver may prove the equality of terms with the head
   of [t] (see [VCUtil.may_relate_by_smt]). *)
val equatable (g:env) (t:term) : ML bool

(* Whether an argument of an application, or of an application in an
   argument and so on, binds a variable. The SMT solver cannot prove the
   equality of two such terms that differ under the binder, unless they are
   related argument-wise. *)
val args_contain_binders (t:term) : ML bool

(* Whether a formula is first-order: no quantifier, abstraction, arrow,
   refinement, match or let anywhere in it. *)
val quantifier_free (t:term) : ML bool

(* Whether [t], the type of some term, syntactically says that the term is
   a type or a proposition. *)
val is_type_or_prop (t:typ) : ML bool

(*** Shapes of types *)

(* The universe of [t], if [t] is (or unfolds to) a [Type]. *)
val is_type (g:env) (t:term) : result universe

(* The (opened) binder, effect and result type of [t], if [t] is (or
   unfolds to) an arrow, possibly refined. *)
val is_arrow (g:env) (t:term) : result (binder & eff & typ)

(*** Qualifiers *)

(* An argument qualifier [a] is compatible with the qualifier [b] of its
   binder. *)
val check_arg_qual (a:aqual) (b:bqual) : result unit

val check_bqual (b0 b1:bqual) : ML (result unit)

val check_aqual (a0 a1:aqual) : ML (result unit)

val check_positivity_qual (rel:relation) (p0 p1:option positivity_qualifier) : result unit

(*** Scoping *)

(* None of [bs] is free in [t]. *)
val check_no_escape (bs:binders) (t:term) : ML (result unit)

(*** let, functions and patterns *)

(* The type at which the body of a [let] sees its variable, of annotated
   type [lbtyp] and whose definition was synthesized the type [tdef], if
   any: [lbtyp], refined by what [tdef] says about the definition. *)
val let_binder_sort (g:env) (lbtyp:typ) (tdef:option typ) : ML typ

(* For [e = fun xs -> body] and [t] an arrow with at least as many
   binders, looking through abbreviations but not refinements: [xs],
   [body], the first [|xs|] binders of [t] and the computation type they
   abstract. *)
val abs_against_arrow (g:env) (e:term) (t:typ)
  : ML (option (binders & term & binders & comp))

(* Whether a match is syntactically exhaustive, so that its residual path
   condition needs no SMT query. *)
val match_is_syntactically_exhaustive (g:env) (t_sc:typ) (brs:list branch) : ML bool

(* The parameters of the constructor [fv]'s type, as recorded by the dot
   patterns of the elaborated pattern [fv sub_pats], if they all are. *)
val datacon_params_of_pat (g:env) (fv:fv) (sub_pats:list (pat & bool))
  : ML (option (list term))

(* For a scrutinee of type [t_sc] matched by a pattern of the constructor
   [fv]: the universes and arguments (parameters and indices) of [fv]'s
   inductive type in [t_sc], as the implicit arguments of its discriminators
   and projectors. Only looked up for an indexed type ([None] otherwise): the
   parameters alone are the pattern's dot terms. *)
val inductive_type_args (g:env) (t_sc:Thunk.t (option typ)) (fv:fv)
  : ML (option (option universes & list term))

(* The [i]th field of [scrutinee], matched by the constructor pattern
   [fv sub_pats] (at [pat_p]), and its type, if known (computed on demand:
   it is only needed for an indexed type). It is an
   application of the field's projector to its implicit arguments (from
   [type_args], see [inductive_type_args], or else the parameters recorded
   as dot patterns in [sub_pats]) and to [scrutinee], whose type is that of
   the projector's result. Only when the projector or its implicit
   arguments cannot be found is it a single-branch [match], of unknown
   type.

   The term is only well-typed if [scrutinee] is an instance of [fv]: it is
   meant to be used under that condition, e.g. conjoined with [fv]'s
   discriminator in a branch condition. The SMT encoding of projectors and
   matches is total, so it is meaningful, if unspecified, otherwise. *)
val pat_field_projection (g:env) (scrutinee:term) (pat_p:Range.t) (fv:fv) (us_opt:option universes)
                         (type_args:option (option universes & list term))
                         (sub_pats:list (pat & bool)) (i:int)
  : ML (term & Thunk.t (option typ))
