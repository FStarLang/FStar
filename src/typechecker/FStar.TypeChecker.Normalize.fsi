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
open FStar.TypeChecker.Common
open FStar.TypeChecker.Env
open FStar.TypeChecker.Cfg

type should_unfold_res =
    | Should_unfold_no
    | Should_unfold_yes
    | Should_unfold_fully
    | Should_unfold_reify

val should_unfold : cfg
                 -> should_reify:(cfg -> bool)
                 -> fv
                 -> Env.qninfo
                 -> should_unfold_res


val eta_expand_with_type :Env.env -> term -> typ -> term
val eta_expand:           Env.env -> term -> term
val normalize:            steps -> Env.env -> term -> term
val normalize_universe:   Env.env -> universe -> universe
val normalize_comp:       steps -> Env.env -> comp -> comp
val normalize_refinement: steps -> Env.env -> typ -> typ
val whnf_steps: list<step>
val unfold_whnf':         steps -> Env.env -> term -> term
val unfold_whnf:          Env.env -> term -> term
val reduce_uvar_solutions:Env.env -> term -> term
val non_info_norm: Env.env -> term -> bool

(*
 * The maybe versions of ghost_to_pure only promote
 *   when the type of the computation is non-informative
 * else the input comp is returned as is
 *)
val maybe_ghost_to_pure:        Env.env -> comp -> comp
val maybe_ghost_to_pure_lcomp:  Env.env -> lcomp -> lcomp

(*
 * The two input computations are to be composed or related by subcomp
 * These functions first call the maybe versions of ghost_to_pure, and then
 *   if one of them is erasable, and the other is GHOST,
 *   the GHOST one is promoted to PURE, see their implementation for more details
 *)
val ghost_to_pure2 : Env.env -> (comp * comp) -> (comp * comp)
val ghost_to_pure_lcomp2 : Env.env -> (lcomp * lcomp) -> (lcomp * lcomp)

val normalize_with_primitive_steps : list<primitive_step> -> steps -> Env.env -> term -> term
val term_to_string:  Env.env -> term -> string
val comp_to_string:  Env.env -> comp -> string
val elim_uvars: Env.env -> sigelt -> sigelt
val erase_universes: Env.env -> term -> term
val tr_norm_steps : list<FStar.Syntax.Embeddings.norm_step> -> list<step>

val remove_uvar_solutions: Env.env -> term -> term

val unfold_head_once: Env.env -> term -> option<term>
val unembed_binder_knot : ref<option<FStar.Syntax.Embeddings.embedding<binder>>>

val reflection_env_hook : ref<option<Env.env>>

(* Destructs the term as an arrow type and returns its binders and
computation type. Only grabs up to [n] binders, and normalizes only as
needed to discover the shape of the arrow. The binders are opened. *)
val get_n_binders : Env.env -> int -> term -> list<binder> * comp
