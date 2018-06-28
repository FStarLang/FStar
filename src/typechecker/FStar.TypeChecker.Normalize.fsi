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
#light "off"
// (c) Microsoft Corporation. All rights reserved

module FStar.TypeChecker.Normalize
open FStar.ST
open FStar.All

open FStar.TypeChecker
open FStar.Syntax.Syntax

type step =
  | Beta
  | Iota            //pattern matching
  | Zeta            //fixed points
  | Exclude of step //the first three kinds are included by default, unless Excluded explicity
  | Weak            //Do not descend into binders
  | HNF             //Only produce a head normal form
  | Primops         //reduce primitive operators like +, -, *, /, etc.
  | Eager_unfolding
  | Inlining
  | DoNotUnfoldPureLets
  | UnfoldUntil of delta_depth
  | UnfoldOnly  of list<FStar.Ident.lid>
  | UnfoldFully of list<FStar.Ident.lid>
  | UnfoldAttr of attribute
  | UnfoldTac
  | PureSubtermsWithinComputations
  | Simplify        //Simplifies some basic logical tautologies: not part of definitional equality!
  | EraseUniverses
  | AllowUnboundUniverses //we erase universes as we encode to SMT; so, sometimes when printing, it's ok to have some unbound universe variables
  | Reify
  | CompressUvars
  | NoFullNorm
  | CheckNoUvars
  | Unmeta
  | Unascribe
and steps = list<step>
type closure =
  | Clos of env * term * memo<(env * term)> * bool  //memo for lazy evaluation; bool marks whether or not this is a fixpoint
  | Univ of universe                                //universe terms do not have free variables
  | Dummy                                           //Dummy is a placeholder for a binder when doing strong reduction
and env = list<(option<binder> * closure)>
type cfg
type psc // primitive step context
val null_psc : psc
val psc_range : psc -> FStar.Range.range
val psc_subst : psc -> subst_t
type primitive_step = {
    name:FStar.Ident.lid;
    arity:int;
    auto_reflect:option<int>;
    strong_reduction_ok:bool;
    requires_binder_substitution:bool;
    interpretation:(psc -> FStar.Syntax.Embeddings.norm_cb -> args -> option<term>)
}

val register_plugin: primitive_step -> unit
val closure_as_term : cfg -> env -> term -> term
val eta_expand_with_type :Env.env -> term -> typ -> term
val eta_expand:           Env.env -> term -> term
val normalize:            steps -> Env.env -> term -> term
val normalize_universe:   Env.env -> universe -> universe
val normalize_comp:       steps -> Env.env -> comp -> comp
val normalize_refinement: steps -> Env.env -> typ -> typ
val unfold_whnf':         steps -> Env.env -> term -> term
val unfold_whnf:          Env.env -> term -> term
val reduce_uvar_solutions:Env.env -> term -> term
val ghost_to_pure:        Env.env -> comp -> comp
val ghost_to_pure_lcomp:  Env.env -> lcomp -> lcomp
val normalize_with_primitive_steps : list<primitive_step> -> list<step> -> Env.env -> term -> term
val term_to_string:  Env.env -> term -> string
val comp_to_string:  Env.env -> comp -> string
val elim_uvars: Env.env -> sigelt -> sigelt
val erase_universes: Env.env -> term -> term
val tr_norm_steps : list<FStar.Syntax.Embeddings.norm_step> -> list<step>

val remove_uvar_solutions: Env.env -> term -> term

val unembed_binder_knot : ref<option<FStar.Syntax.Embeddings.embedding<binder>>>
