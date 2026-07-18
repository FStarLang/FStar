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
open FStarC.Effect
open FStarC.Syntax.Syntax
open FStarC.TypeChecker.Common
open FStarC.Class.Show
module Env = FStarC.TypeChecker.Env


type guard_commit_token_cb = unit -> ML unit
(* The guard t is a precondition of typing computed by the core checker;
   Once the guard is proven, the caller should call commit_guard on the 
   guard_commit_token_cb to notify the core checker that the guard was
   proven, allowing it to cache the result *)
type guard_and_tok_t = typ & guard_commit_token_cb

type tot_or_ghost = 
  | E_Total
  | E_Ghost

type side = 
  | Left
  | Right
  | Both
  | Neither

(* val declarations ordered to match .fst definition order *)

val get_goal_ctr (_:unit) : ML int
val incr_goal_ctr (_:unit) : ML int

val error : Type0

val print_error (err:error)
  : ML string

instance val showable_error : showable error

val print_error_short (err:error)
  : ML string

val clear_memo_table (_:unit)
  : ML unit

val empty_token : guard_commit_token_cb
val commit_guard (tok:guard_commit_token_cb) : ML unit
val commit_guard_and_tok_opt (_: option guard_and_tok_t) : ML unit

val is_non_informative (g:Env.env) (t:typ) : ML bool

instance val showable_tot_or_ghost : Class.Show.showable tot_or_ghost
instance val showable_side : Class.Show.showable side

val maybe_relate_after_unfolding (g:Env.env) (t0 t1:term) : ML side

val check_term (g:Env.env) (e:term) (t:typ) (must_tot:bool)
  : ML (either (option guard_and_tok_t) error)

val check_term_at_type (g:Env.env) (e:term) (t:typ)
  : ML (either (tot_or_ghost & option guard_and_tok_t) error)

val compute_term_type (g:Env.env) (e:term)
  : ML (either (tot_or_ghost & typ & option guard_and_tok_t) error)

val open_binders_in_term (g:Env.env) (bs:binders) (t:term)
  : ML (Env.env & binders & term)

val open_binders_in_comp (g:Env.env) (bs:binders) (c:comp)
  : ML (Env.env & binders & comp)

(* For unit testing, and exposed to tactics *)
val check_term_equality (guard_ok:bool) (unfolding_ok:bool) (g:Env.env) (t0 t1:typ)
  : ML (either (option guard_and_tok_t) error)

val check_term_subtyping (guard_ok:bool) (unfolding_ok:bool) (g:Env.env) (t0 t1:typ)
  : ML (either (option guard_and_tok_t) error)
