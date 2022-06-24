module FStar.Reflection.Typing

open FStar.Reflection
open FStar.Reflection.Helpers
open FStar.Reflection.Subst

open FStar.Meta.Tc.Builtins

module R = FStar.Reflection

let ( ++ ) : guard -> guard -> guard = fun g1 g2 ->
  match g1, g2 with
  | None, _ -> g2
  | _, None -> g1
  | Some g1, Some g2 -> Some (mk_conj g1 g2)

[@@ erasable]
noeq
type typing_const : vconst -> typ -> Type =
  | CT_Unit: typing_const C_Unit unit_ty
  | CT_True: typing_const C_True bool_ty
  | CT_False: typing_const C_False bool_ty


//
// TODO: should comp have universes?
//

[@@ erasable; no_auto_projectors]
noeq
type typing : env -> term -> comp -> guard -> Type =
  | T_Var : 
     g:env ->
     x:bv { Some? (lookup_bvar g (bv_index x)) } ->
     typing g (pack_ln (Tv_Var x))
              (mk_total u_unk (Some?.v (lookup_bvar g (bv_index x))))
              None

  | T_FVar :
     g:env ->
     x:fv { Some? (lookup_fvar g x) } -> 
     typing g (pack_ln (Tv_FVar x))
              (mk_total u_unk (Some?.v (lookup_fvar g x)))
              None
  | T_Const:
     g:env ->
     v:vconst ->
     t:term ->
     typing_const v t ->
     typing g (constant_as_term v) (mk_total u_unk t) None
                        
  | T_Abs :
     g:env ->
     x:var { None? (lookup_bvar g x) } ->
     t:term ->
     u_t:universe ->
     g_t:guard ->
     e:term ->
     c:comp ->
     g_e:guard ->
     typing g t (mk_total u_unk (tm_type u_t)) g_t ->
     typing (extend_env g x t) (open_term e x) c g_e ->
     typing g (pack_ln (Tv_Abs (as_binder 0 t) e))
              (mk_total u_unk (pack_ln (Tv_Arrow (as_binder 0 t) 
                                       (close_comp c x))))
              (g_t ++ close_guard g_e x)

  | T_App :
     g:env ->
     e1:term ->
     e2:term ->
     x:binder ->
     c:comp ->
     g_e1:guard ->
     g_e2:guard ->
     typing g e1 (mk_total u_unk (pack_ln (Tv_Arrow x c))) g_e1 ->
     typing g e2 (mk_total u_unk (binder_sort x)) g_e2 ->
     typing g (pack_ln (Tv_App e1 (e2, Q_Explicit)))
              (open_comp_with c e2)
              (g_e1 ++ g_e2)

  | T_Arrow:
     g:env ->
     x:var { None? (lookup_bvar g x) } ->
     t:term ->
     u_t:universe ->
     g_t:guard ->
     c:comp ->
     u_c:universe ->
     g_c:guard ->
     typing g t (mk_total u_unk (tm_type u_t)) g_t ->
     typing_comp (extend_env g x t) (open_comp c x) u_c g_c ->
     typing g (pack_ln (Tv_Arrow (as_binder 0 t) c))
              (mk_total u_unk (tm_type (pack_universe (Uv_Max [u_t; u_c]))))
              (g_t ++ close_guard g_c x)

  | T_Refine:
     g:env ->
     x:var { None? (lookup_bvar g x) } ->     
     t:term ->
     u_t:universe ->
     g_t:guard ->
     e:term ->
     u_e:universe ->
     g_e:guard ->
     typing g t (mk_total u_unk (tm_type u_t)) g_t ->
     typing (extend_env g x t) (open_term e x) (mk_total u_unk (tm_type u_e)) g_e ->
     typing g (pack_ln (Tv_Refine (pack_bv (make_bv 0 t)) e))
              (mk_total u_unk (tm_type u_t))
              (g_t ++ close_guard g_e x)

    //
    // TODO: what about well-typedness of c2?
    //

  | T_Sub:
     g:env ->
     e:term ->
     c1:comp ->
     g_e:guard ->
     c2:comp ->
     g_sub:guard ->
     typing g e c1 g_e ->
     sub_comp g c1 c2 g_sub ->
     typing g e c2 (g_e ++ g_sub)

  | T_If: 
     g:env ->
     scrutinee:term ->
     g_scrutinee:guard ->
     then_:term ->
     g_then:guard ->
     else_:term ->
     g_else:guard ->
     c:comp ->
     hyp:var { None? (lookup_bvar g hyp) } ->
     typing g scrutinee (mk_total u_unk bool_ty) g_scrutinee ->
     typing (extend_env g hyp (eq2 bool_ty scrutinee true_bool)) then_ c g_then ->
     typing (extend_env g hyp (eq2 bool_ty scrutinee false_bool)) else_ c g_else ->
     typing g (pack_ln (Tv_Match scrutinee None [(Pat_Constant C_True, then_); 
                                                 (Pat_Constant C_False, else_)]))
              c
              (g_scrutinee ++ g_then ++ g_else)

  | T_Match: 
     g:env ->
     scrutinee:term ->
     i_ty:term ->
     g_scrutinee:guard ->
     branches:list branch ->
     c:comp ->
     g_branches:guard ->
     typing g scrutinee (mk_total u_unk i_ty) g_scrutinee ->
     branches_typing g scrutinee i_ty branches c g_branches ->
     typing g (pack_ln (Tv_Match scrutinee None branches))
              c
              (g_scrutinee ++ g_branches)
    
and typing_comp : env -> comp -> universe -> guard -> Type =
  | C_Total:
     g:env ->
     t:typ ->
     u_t:universe ->
     g_t:guard ->
     typing g t (mk_total u_unk (tm_type u_t)) g_t ->
     typing_comp g (mk_total u_unk t) u_t g_t

and sub_typing : env -> term -> term -> guard -> Type0 =
  | ST_Refl: 
     g:env ->
     t:term ->
     sub_typing g t t None

  | ST_Token: 
     g:env ->
     t1:term ->
     t2:term ->      
     subtyping_token g t1 t2 ->
     sub_typing g t1 t2 None

and sub_comp : env -> comp -> comp -> guard -> Type0 =
  | SC_Total:
     g:env ->
     t1:typ ->
     t2:typ ->
     g_sub:guard ->
     sub_typing g t1 t2 g_sub ->
     sub_comp g (mk_total u_unk t1)
                (mk_total u_unk t2)
                g_sub

and branches_typing : env -> term -> term -> list branch -> comp -> guard -> Type0 =
