module Refl.Typing
open FStar.Reflection

val lookup_bvar (e:env) (x:int) : option term

val lookup_fvar (e:env) (x:fv) : option term

val extend_env (e:env) (x:var) (ty:term) : env

//replace BV 0 in t with v
val open_with (t:term) (v:term) : term
val open_term (t:term) (v:var) : term
val close_term (t:term) (v:var) : term
let as_binder (x:var) (ty:term)
  : binder 
  = pack_binder
      (pack_bv ({bv_ppname="";
                 bv_index=x;
                 bv_sort=ty}))
      Q_Explicit
      []

let bv_index (x:bv) : int = (inspect_bv x).bv_index
  
let unit_exp = pack_ln (Tv_Const C_Unit)
let unit_ty = pack_ln (Tv_FVar (pack_fv unit_lid))
let binder_sort (b:binder) =
  let bv, _ = inspect_binder b in 
  (inspect_bv bv).bv_sort
    
noeq
type typing : env -> term -> term -> Type0 =
  | T_Var : 
     g:env ->
     x:bv { Some? (lookup_bvar g (bv_index x)) } ->
     typing g (pack_ln (Tv_Var x)) (Some?.v (lookup_bvar g (bv_index x)))

  | T_Const:
     g:env ->
     typing g unit_exp unit_ty

  | T_Abs :
     g:env ->
     x:var { None? (lookup_bvar g x) } ->
     ty:term ->
     body:term ->
     body_ty:term ->
     typing (extend_env g x ty) (open_term body x) body_ty ->
     typing g (pack_ln (Tv_Abs (as_binder 0 ty) body))
              (pack_ln (Tv_Arrow (as_binder 0 ty) 
                                 (pack_comp (C_Total (close_term body_ty x) []))))

  | T_App :
     g:env ->
     e1:term ->
     e2:term ->
     x:binder ->
     t:term ->
     typing g e1 (pack_ln (Tv_Arrow x (pack_comp (C_Total t [])))) ->
     typing g e2 (binder_sort x) ->
     typing g (pack_ln (Tv_App e1 (e2, Q_Explicit)))
              (open_with t e2)
