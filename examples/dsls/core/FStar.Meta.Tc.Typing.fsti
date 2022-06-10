module FStar.Meta.Tc.Typing

open FStar.Reflection.Types
open FStar.Reflection.Data
open FStar.Reflection.Builtins
open FStar.Reflection.Formula

open FStar.Meta.Tc.Subst

type guard = option typ

val t_unit   : term
val t_int    : term
val t_bool   : term
val t_string : term
val t_type   : term

val mk_conj (t1 t2:typ) : typ
val mk_const_tm (c:vconst) : term
val mk_var_tm (x:var) : term
val mk_fv_tm (x:fv) : term
val mk_arrow_tm (x:var) (t:typ) (c:comp) : term
val mk_abs_tm (x:var) (t:typ) (body:term) : term
val mk_total (t:typ) : comp

val lookup_var (g:env) (x:var) : option typ
val lookup_fv (g:env) (f:fv) : option typ
val extend_env (g:env) (x:var) (t:typ) : env

val binder_sort (b:binder) : typ

let ( ++ ) : guard -> guard -> guard = fun g1 g2 ->
  match g1, g2 with
  | None, _ -> g2
  | _, None -> g1
  | Some g1, Some g2 -> Some (mk_conj g1 g2)

[@@ erasable]
noeq
type typing_const : vconst -> typ -> Type = 
  | C_ty_unit   : typing_const C_Unit t_unit
  | C_ty_int    : n:int -> typing_const (C_Int n) t_int
  | C_ty_true   : typing_const C_True t_bool
  | C_ty_false  : typing_const C_False t_bool
  | C_ty_string : s:string -> typing_const (C_String s) t_string

[@@ erasable; no_auto_projectors]
noeq
type typing_term : env -> term -> comp -> guard -> Type =
  | T_const:
    g:env ->
    c:vconst ->
    t:typ ->
    typing_const c t ->
    typing_term g (mk_const_tm c) (mk_total t) None

  | T_var:
    g:env ->
    x:var ->
    t:typ{lookup_var g x == Some t} ->
    typing_term g (mk_var_tm x) (mk_total t) None

  | T_fvar:
    g:env ->
    f:fv ->
    t:typ{lookup_fv g f == Some t} ->
    typing_term g (mk_fv_tm f) (mk_total t) None

  | T_arrow:
    g:env ->
    x:var ->
    t:typ ->
    c:comp ->
    g_t:guard ->
    g_c:guard ->
    typing_term g t (mk_total t_type) g_t ->
    typing_comp (extend_env g x t) c g_c ->
    typing_term g (mk_arrow_tm x t c) (mk_total t_type) (g_t ++ g_c)

  | T_abs:
    g:env ->
    x:var ->
    t:typ ->
    e:term ->
    c:comp ->
    g_t:guard ->
    g_e:guard ->
    typing_term g t (mk_total t_type) g_t ->
    typing_term (extend_env g x t) e c g_e ->
    typing_term g (mk_abs_tm x t e) (mk_total (mk_arrow_tm x t c)) (g_t ++ g_e)

  | T_app:
    g:env ->
    e1:term ->
    e2:term ->
    x:binder ->
    t:typ ->
    g_e1:guard ->
    g_e2:guard ->
    typing_term g e1 (mk_total (pack_ln (Tv_Arrow x (mk_total t)))) g_e1 ->
    typing_term g e2 (mk_total (binder_sort x)) g_e2 ->
    typing_term g (pack_ln (Tv_App e1 (e2, Q_Explicit))) (mk_total (open_with t e2)) (g_e1 ++ g_e2)
    
and typing_comp : env -> comp -> guard -> Type =
  | C_total:
    g:env ->
    t:typ ->
    g_t:guard ->
    typing_term g t (mk_total t_type) g_t ->
    typing_comp g (mk_total t) g_t
