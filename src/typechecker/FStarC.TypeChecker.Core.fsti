module FStarC.TypeChecker.Core
open FStarC
open FStarC.Util
open FStarC.Syntax.Syntax
open FStarC.TypeChecker.Common
module Env = FStarC.TypeChecker.Env

type tot_or_ghost = 
  | E_Total
  | E_Ghost

val clear_memo_table (_:unit)
  : unit

val error : Type0

type side = 
  | Left
  | Right
  | Both
  | Neither

instance val showable_side : Class.Show.showable side

val maybe_relate_after_unfolding (g:Env.env) (t0 t1:term) : side

val is_non_informative (g:Env.env) (t:typ) : bool

val check_term (g:Env.env) (e:term) (t:typ) (must_tot:bool)
  : either (option typ) error

val check_term_at_type (g:Env.env) (e:term) (t:typ)
  : either (tot_or_ghost & option typ) error

val compute_term_type_handle_guards (g:Env.env) (e:term)
                                    (discharge_guard: Env.env -> typ -> bool)
  : either (tot_or_ghost & typ) error

val open_binders_in_term (g:Env.env) (bs:binders) (t:term)
  : Env.env & binders & term

val open_binders_in_comp (g:Env.env) (bs:binders) (c:comp)
  : Env.env & binders & comp

(* For unit testing, and exposed to tactics *)
val check_term_equality (guard_ok:bool) (unfolding_ok:bool) (g:Env.env) (t0 t1:typ)
  : either (option typ) error

val check_term_subtyping (guard_ok:bool) (unfolding_ok:bool) (g:Env.env) (t0 t1:typ)
  : either (option typ) error

val print_error (err:error)
  : string

val print_error_short (err:error)
  : string

val get_goal_ctr (_:unit) : int
val incr_goal_ctr (_:unit) : int
