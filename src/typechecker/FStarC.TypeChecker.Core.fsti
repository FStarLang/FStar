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
module FStarC.TypeChecker.Core
open FStarC
open FStarC.Syntax.Syntax
open FStarC.TypeChecker.Common
module Env = FStarC.TypeChecker.Env
type guard_commit_token_cb = unit -> unit
(* The guard t is a precondition of typing computed by the core checker;
   Once the guard is proven, the caller should call commit_guard on the 
   guard_commit_token_cb to notify the core checker that the guard was
   proven, allowing it to cache the result *)
type guard_and_tok_t = typ & guard_commit_token_cb

type tot_or_ghost = 
  | E_Total
  | E_Ghost

instance val showable_tot_or_ghost : Class.Show.showable tot_or_ghost

val clear_memo_table (_:unit)
  : unit

val error : Type0

type side = 
  | Left
  | Right
  | Both
  | Neither

instance val showable_side : Class.Show.showable side

val empty_token : guard_commit_token_cb
val commit_guard (tok:guard_commit_token_cb) : unit
val commit_guard_and_tok_opt (_: option guard_and_tok_t) : unit
val maybe_relate_after_unfolding (g:Env.env) (t0 t1:term) : side

val is_non_informative (g:Env.env) (t:typ) : bool

val check_term (g:Env.env) (e:term) (t:typ) (must_tot:bool)
  : either (option guard_and_tok_t) error

val check_term_at_type (g:Env.env) (e:term) (t:typ)
  : either (tot_or_ghost & option guard_and_tok_t) error

val compute_term_type (g:Env.env) (e:term)
  : either (tot_or_ghost & typ & option guard_and_tok_t) error

val open_binders_in_term (g:Env.env) (bs:binders) (t:term)
  : Env.env & binders & term

val open_binders_in_comp (g:Env.env) (bs:binders) (c:comp)
  : Env.env & binders & comp

(* For unit testing, and exposed to tactics *)
val check_term_equality (guard_ok:bool) (unfolding_ok:bool) (g:Env.env) (t0 t1:typ)
  : either (option guard_and_tok_t) error

val check_term_subtyping (guard_ok:bool) (unfolding_ok:bool) (g:Env.env) (t0 t1:typ)
  : either (option guard_and_tok_t) error

val print_error (err:error)
  : string

val print_error_short (err:error)
  : string

val get_goal_ctr (_:unit) : int
val incr_goal_ctr (_:unit) : int
