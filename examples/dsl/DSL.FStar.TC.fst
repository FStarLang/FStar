module DSL.FStar.TC

open FStar.Reflection.Types
open FStar.Reflection.Data
open FStar.Reflection.Builtins
open FStar.Reflection.Formula

open FStar.Tactics

open DSL.Reflection

[@@ erasable]
noeq
type typing_const : vconst -> typ -> Type =
  | C_ty_unit   : typing_const C_Unit t_unit
  | C_ty_int    : n:int -> typing_const (C_Int n) t_int
  | C_ty_true   : typing_const C_True t_bool
  | C_ty_false  : typing_const C_False t_bool
  | C_ty_string : s:string -> typing_const (C_String s) t_string

type name = bv

(*
 * G |- e : C, g
 *
 *)
[@@ erasable; no_auto_projectors]
noeq
type typing_term : env -> term -> (comp & guard) -> Type =
  | Ty_name:
    env:env   ->
    name:name ->
    ty:typ    ->
    #squash (lookup_name env name == Some ty) ->
    typing_term env (mk_tm_name name) (mk_tot ty, trivial_guard)

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

  | Ty_arrow:
    env:env   ->
    b:binder  ->
    c:comp    ->
    g_b:guard ->
    g_c:guard ->
    typing_term env (binder_sort b) (mk_tot t_type, g_b) ->
    typing_comp (push_binder env b) c g_c ->
    typing_term env (mk_tm_arrow b c) (mk_tot t_type, g_b ++ close_guard_binder g_c b)

  | Ty_abs:
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
    x:name    ->
    e1:term    ->
    e2:term    ->
    c1:comp    ->
    g1:guard   ->
    c2:comp    ->
    g2:guard   ->
    typing_term env e1 (c1, g1) ->
    typing_term (extend_env env (set_bv_sort x (comp_result_type c1))) e2 (c2, g2) ->
    c:comp     ->
    g:guard    ->
    typing_bind env (Some e1, c1) x c2 (c, g) ->
    squash (no_escape (x, c)) ->
    typing_term env (mk_tm_let x e1 e2) (c, g1 ++ close_guard g2 bv ++ g)

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

and typing_bind : env -> (term & comp) -> name -> comp -> (comp & guard) -> Type =
  | Bind_Tot_M:
    env:env ->
    e1:term ->
    t1:typ ->
    x:name ->
    c2:comp ->  //bv is free in c2
    typing_bind
      env
      (e1, mk_tot t1)
      x
      c2
      (subst_comp x e1 c2, trivial_guard)
    
  | Bind_M_M:
    env:env ->
    _e1:term ->
    c1:comp ->
    x:name ->
    c2:comp ->
    m:lid{comp_effect_label c1 == m /\
          comp_effect_label c2 == m} ->
    f:name{f `notin` env} ->
    g:name{g `notin` env} ->
    args:list term ->
    ks:list term ->
    _:typing_term
        (extend_env env [{f with sort=mk_app (repr env m) [comp_result c1; comp_args c1]};
                         {g with sort=mk_arrow x (mk_app (repr env m) (comp_result c2) (comp_args c2))}])
        (mk_app (bind env m) [comp_result c1;
                              comp_result c2;
                              args;
                              f;
                              b])
        
        (mk_tot (mk_app (repr env m) [b; ks])) ->
    typing_bind
      env
      (e1, c1)
      x
      c2
      (mk_comp m b ks)
        
    // typing_bind
    //   env
    //   (e1, c1)
    //   bv
    //   c2
    //   (apply_M_bind env e1 c1 bv c2)


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

//another discharge guard function, in terms of typing relation

assume val discharge_guard_typing (#env:_) (#t:_) (#c:_) (#g:_)
  (_:typing_term env t (c, g))
  : typing_term env t (c, trivial_guard)
