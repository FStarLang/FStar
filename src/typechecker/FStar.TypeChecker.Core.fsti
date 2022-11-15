module FStar.TypeChecker.Core
open FStar.Compiler.Util
open FStar.Syntax.Syntax
module Env = FStar.TypeChecker.Env
module S = FStar.Syntax.Syntax
module R = FStar.Compiler.Range
module U = FStar.Syntax.Util

val clear_memo_table (_:unit)
  : unit

val error : Type0
  
val check_term (g:Env.env) (e:term) (t:typ) (must_tot:bool)
  : either (option typ) error

val compute_term_type_handle_guards (g:Env.env) (e:term) (must_tot:bool)
                                    (discharge_guard: Env.env -> typ -> bool)
  : either typ error

val fresh_binder_in_env (g:Env.env) (ty:term)
  : Env.env & binder
  
val open_binders_in_term (g:Env.env) (bs:binders) (t:term)
  : Env.env & binders & term

val open_binders_in_comp (g:Env.env) (bs:binders) (c:comp)
  : Env.env & binders & comp

(* for unit testing *)
val check_term_equality (g:Env.env) (t0 t1:typ)
  : either (option typ) error

val check_term_subtyping (g:Env.env) (t0 t1:typ)
  : either (option typ) error

val print_error (err:error)
  : string

val print_error_short (err:error)
  : string

val get_goal_ctr (_:unit) : int
val incr_goal_ctr (_:unit) : int
