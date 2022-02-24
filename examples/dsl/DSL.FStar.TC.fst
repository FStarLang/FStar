module DSL.FStar.TC

open FStar.Reflection.Types
open FStar.Reflection.Data
open FStar.Reflection.Builtins
open FStar.Reflection.Formula

open FStar.Tactics

open DSL.Reflection

//
//Callbacks to the typechecker for tc_term
//these shouldn't be Tot
//assume an state + exception + divergence effect, with no specs
//

// abstract typing token returned by the typechecker
[@@ erasable]
assume val token (env:env) (t:term) (_:comp & guard) : Type0

assume val fstar_tc (env:env) (t:term)
  : r:(comp & guard) & token env t r

assume val fstar_tc_expected (env:env) (t:term) (c:comp)
  : g:guard & token env t (c, g)

assume val discharge_guard (#env:_) (#t:_) (#c:_) (#g:_) (_:token env t (c, g))
  : token env t (c, trivial_guard)

//following can be implemented using the API above
assume val fstar_tc_trivial (env:env) (t:term)
  : c:comp & token env t (c, trivial_guard)

assume val fstar_tc_expected_trivial (env:env) (t:term) (c:comp)
  : token env t (c, trivial_guard)

// typing derivations

[@@ erasable]
noeq
type typing_const : vconst -> typ -> Type =
  | C_ty_unit   : typing_const C_Unit t_unit
  | C_ty_int    : n:int -> typing_const (C_Int n) t_int
  | C_ty_true   : typing_const C_True t_bool
  | C_ty_false  : typing_const C_False t_bool
  | C_ty_string : s:string -> typing_const (C_String s) t_string

(*
 * G |- e : C, g
 *
 *)
#set-options "--__temp_no_proj FStar.TypingJudgment"  //else takes some time to tc
[@@ erasable]
noeq
type typing_term : env -> term -> (comp & guard) -> Type =
  | Ty_name:
    env:env ->
    bv:bv   ->
    ty:typ  ->
    #squash (lookup_name env bv == Some ty) ->
    typing_term env (mk_tm_name bv) (mk_tot ty, trivial_guard)

  | Ty_fvar:
    env:env ->
    fv:fv   ->
    ty:typ  ->
    squash (lookup_fv env fv [] == Some ty) ->
    typing_term env (mk_tm_fvar fv) (mk_tot ty, trivial_guard)

  | Ty_const:
    env:env  ->
    c:vconst ->
    ty:typ   ->
    typing_const c ty ->
    typing_term env (mk_tm_const c) (mk_tot ty, trivial_guard)

  | Ty_arrow:  //TODO: should we have n-ary binders?
    env:env   ->
    b:binder  ->
    c:comp    ->
    g_b:guard ->
    g_c:guard ->
    typing_term env (binder_sort b) (mk_tot t_type, g_b) ->
    typing_comp (push_binder env b) c g_c ->
    typing_term env (mk_tm_arrow b c) (mk_tot t_type, g_b ++ close_guard_binder g_c b)

  | Ty_abs:  //TODO: should we have n-ary binders?
    env:env    ->
    b:binder   ->
    t:term     ->
    c_t:comp   ->
    g_b:guard  ->
    g_t:guard  ->
    typing_term env (binder_sort b) (mk_tot t_type, g_b) ->
    typing_term (push_binder env b) t (c_t, g_t) ->
    typing_term env (mk_tm_abs b t) (mk_tot (mk_tm_arrow b c_t), g_b ++ close_guard_binder g_t b)

  | Ty_let:
    env:env    ->
    bv:bv      ->  //TODO: check its sort? Let's call it name
    e1:term    ->
    e2:term    ->
    c1:comp    ->
    g1:guard   ->
    c2:comp    ->
    g2:guard   ->
    typing_term env e1 (c1, g1) ->
    typing_term (extend_env env (set_bv_sort bv (comp_result_type c1))) e2 (c2, g2) ->
    c:comp     ->
    g:guard    ->
    typing_bind env (Some e1, c1) (Some bv) c2 (c, g) ->
    squash (~ (List.Tot.memP bv (free_bvs (comp_result_type c)))) ->  //x doesn't escape
    typing_term env (mk_tm_let bv e1 e2) (c, g1 ++ close_guard g2 bv ++ g)

  //TODO: could we define only Tot applications (or may be PURE/GHOST)?

  | Ty_refine:  //TODO: universes
    env:env     ->
    bv:bv       ->
    phi:term    ->
    g_bv:guard  ->
    g_phi:guard ->
    typing_term env (bv_sort bv) (mk_tot t_type, g_bv) ->
    typing_term (extend_env env bv) phi (mk_tot t_type, g_phi) ->
    typing_term env (mk_tm_refine bv phi) (mk_tot t_type, g_bv ++ close_guard g_phi bv)

  | Ty_tc:
    env:env              ->
    t:term               ->
    c:comp               ->
    g:guard              ->
    _:token env t (c, g) ->
    typing_term env t (c, g)

and typing_comp : env -> comp -> guard -> Type =  //tc returns a universe too
  | C_Ty_Tot:
    env:env ->
    t:typ ->
    g:guard ->
    typing_term env t (mk_tot t_type, trivial_guard) ->
    typing_comp env (mk_tot t) g

  | C_Ty_M:
    env:env ->
    eff_name:name ->
    t:typ ->
    args:list argv ->
    g:guard ->
    typing_term env (mk_app (mk_tm_fvar (fv_of_name eff_name)) ((term_to_arg t)::args)) (mk_tot t_effect, g) ->
    typing_comp env (mk_comp eff_name t args) g

and typing_bind : env -> (option term & comp) -> option bv -> comp -> (comp & guard) -> Type =
  | Bind_Tot_M:
    env:env ->
    e1:term ->
    t1:typ ->
    bv:bv ->
    c2:comp ->  //bv is free in c2
    typing_bind
      env
      (Some e1, mk_tot t1)
      (Some bv)
      c2
      (subst_comp bv e1 c2, trivial_guard)
    
  | Bind_M_M:
    env:env ->
    e1:option term ->
    c1:comp ->
    bv:option bv ->
    c2:comp ->
    squash (comp_effect_label env c1 == comp_effect_label env c2) ->
    typing_bind
      env
      (e1, c1)
      bv
      c2
      (apply_M_bind env e1 c1 bv c2)

//another discharge guard function, in terms of typing relation

assume val discharge_guard_typing (#env:_) (#t:_) (#c:_) (#g:_)
  (_:typing_term env t (c, g))
  : typing_term env t (c, trivial_guard)
