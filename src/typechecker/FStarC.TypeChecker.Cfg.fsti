(*
   Copyright 2008-2014 Microsoft Research

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

module FStarC.TypeChecker.Cfg

open FStarC
open FStar.String
open FStarC.Const
open FStar.Char
open FStarC.Errors
open FStarC.Syntax
open FStarC.Syntax.Syntax
open FStarC.Syntax.Subst
open FStarC.Syntax.Util
open FStarC.TypeChecker
open FStarC.TypeChecker.Env
open FStarC.TypeChecker.Primops

open FStarC.Class.Show
open FStarC.Class.Deq

module S  = FStarC.Syntax.Syntax
module I  = FStarC.Ident
module EMB = FStarC.Syntax.Embeddings

type fsteps = {
     beta : bool;
     iota : bool;
     zeta : bool;
     zeta_full : bool;
     weak : bool;
     hnf  : bool;
     primops : bool;
     do_not_unfold_pure_lets : bool;
     unfold_until : option S.delta_depth;
     unfold_only  : option (list I.lid);
     unfold_once  : option (list I.lid);
     unfold_fully : option (list I.lid);
     unfold_attr  : option (list I.lid);
     unfold_qual  : option (list string);
     unfold_namespace: option (Path.forest string bool);
     dont_unfold_attr : option (list I.lid);
     pure_subterms_within_computations : bool;
     simplify : bool;
     erase_universes : bool;
     allow_unbound_universes : bool;
     reify_ : bool; // 'reify' is reserved
     compress_uvars : bool;
     no_full_norm : bool;
     check_no_uvars : bool;
     unmeta : bool;
     unascribe : bool;
     in_full_norm_request: bool;
     weakly_reduce_scrutinee:bool;
     nbe_step:bool;
     for_extraction:bool;
     unrefine:bool;
     default_univs_to_zero:bool; (* Default unresolved universe levels to zero *)
     tactics : bool;
}

instance val deq_fsteps : deq fsteps

val default_steps : fsteps
val fstep_add_one : step -> fsteps -> fsteps
val to_fsteps : list step -> fsteps

type debug_switches = {
    gen              : bool;
    top              : bool;
    cfg              : bool;
    primop           : bool;
    unfolding        : bool;
    b380             : bool;
    wpe              : bool;
    norm_delayed     : bool;
    print_normalized : bool;
    debug_nbe        : bool;
    erase_erasable_args: bool;
}

val no_debug_switches : debug_switches

type cfg = {
     steps: fsteps;
     tcenv: Env.env;
     debug: debug_switches;
     delta_level: list Env.delta_level;  // Controls how much unfolding of definitions should be performed
     primitive_steps:PSMap.t primitive_step;
     strong : bool;                       // under a binder
     memoize_lazy : bool;     (* What exactly is this? Seems to be always true now. *)
     normalize_pure_lets: bool;
     reifying : bool;
     compat_memo_ignore_cfg:bool; (* See #2155, #2161, #2986 *)
}

(* Profiling primitive operators *)
val primop_time_reset : unit -> unit
val primop_time_count : string -> int -> unit
val primop_time_report : unit -> string

val cfg_env: cfg -> Env.env

instance val showable_cfg : showable cfg

val log : cfg -> (unit -> unit) -> unit
val log_top : cfg -> (unit -> unit) -> unit
val log_cfg : cfg -> (unit -> unit) -> unit
val log_primops : cfg -> (unit -> unit) -> unit
val log_unfolding : cfg -> (unit -> unit) -> unit
val log_nbe : cfg -> (unit -> unit) -> unit

val is_prim_step: cfg -> fv -> bool
val find_prim_step: cfg -> fv -> option primitive_step

// val embed_simple: EMB.embedding 'a -> Range.t -> 'a -> term
// val try_unembed_simple: EMB.embedding 'a -> term -> option 'a

val built_in_primitive_steps : PSMap.t primitive_step
val simplification_steps (env:Env.env_t): PSMap.t primitive_step

val register_plugin : primitive_step -> unit
val register_extra_step : primitive_step -> unit

(* for debugging *)
val list_plugins : unit -> list primitive_step
val list_extra_steps : unit -> list primitive_step

val config': list primitive_step -> list step -> Env.env -> cfg
val config: list step -> Env.env -> cfg

val should_reduce_local_let : cfg -> letbinding -> bool

val translate_norm_steps: list NormSteps.norm_step -> list Env.step
