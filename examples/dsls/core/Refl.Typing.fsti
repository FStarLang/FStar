module Refl.Typing
open FStar.Reflection

val lookup_bvar (e:env) (x:int) : option term

val lookup_fvar (e:env) (x:fv) : option term

val extend_env (e:env) (x:var) (ty:term) : env

let lookup_bvar_extend_env (g:env) (x y:var) (ty:term)
  : Lemma 
    (ensures (
           if x = y
           then lookup_bvar (extend_env g x ty) y == Some ty
           else lookup_bvar (extend_env g x ty) y == lookup_bvar g y))
    [SMTPat (lookup_bvar (extend_env g x ty) y)]
  = admit()

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

let make_bv (n:nat) (t:term) = { bv_ppname = "_"; bv_index = n; bv_sort = t}

let bv_as_binder bv = pack_binder bv Q_Explicit []

let bv_index_of_make_bv (n:nat) (t:term)
  : Lemma (ensures bv_index (pack_bv (make_bv n t)) == n)
          [SMTPat (bv_index (pack_bv (make_bv n t)))]
  = admit()

let binder_sort (b:binder) =
  let bv, _ = inspect_binder b in 
  (inspect_bv bv).bv_sort

let binder_sort_lemma (x:var) (ty:term)
  : Lemma (binder_sort (as_binder x ty) == ty)
          [SMTPat (binder_sort (as_binder x ty))]
  = admit()          

let constant_as_term (v:vconst) = pack_ln (Tv_Const v)
let unit_exp = constant_as_term C_Unit
let unit_fv = pack_fv unit_lid
let unit_ty = pack_ln (Tv_FVar unit_fv)
let bool_fv = pack_fv bool_lid
let bool_ty = pack_ln (Tv_FVar bool_fv)

let mk_total t = pack_comp (C_Total t [])
let tm_type = pack_ln (Tv_Type ())

noeq
type constant_typing: vconst -> term -> Type0 = 
  | CT_Unit: constant_typing C_Unit unit_ty
  | CT_True: constant_typing C_True bool_ty
  | CT_False: constant_typing C_False bool_ty  
  

noeq
type typing : env -> term -> term -> Type0 =
  | T_Var : 
     g:env ->
     x:bv { Some? (lookup_bvar g (bv_index x)) } ->
     typing g (pack_ln (Tv_Var x)) (Some?.v (lookup_bvar g (bv_index x)))

  | T_FVar :
     g:env ->
     x:fv { Some? (lookup_fvar g x) } -> 
     typing g (pack_ln (Tv_FVar x)) (Some?.v (lookup_fvar g x))
     
  | T_Const:
     g:env ->
     v:vconst ->
     t:term ->
     constant_typing v t ->
     typing g (constant_as_term v) t

  | T_Abs :
     g:env ->
     x:var { None? (lookup_bvar g x) } ->
     ty:term ->
     body:term ->
     body_ty:term ->
     typing g ty tm_type ->
     typing (extend_env g x ty) (open_term body x) body_ty ->
     typing g (pack_ln (Tv_Abs (as_binder 0 ty) body))
              (pack_ln (Tv_Arrow (as_binder 0 ty) 
                                 (mk_total (close_term body_ty x))))

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

  | T_Arrow:
     g:env ->
     x:var { None? (lookup_bvar g x) } ->
     t1:term ->
     t2:term ->
     typing g t1 tm_type ->
     typing (extend_env g x t1) (open_term t2 x) tm_type ->
     typing g (pack_ln (Tv_Arrow (as_binder 0 t1) (mk_total t2))) tm_type

  | T_Refine:
     g:env ->
     x:var { None? (lookup_bvar g x) } ->     
     t:term ->
     e:term ->
     typing g t tm_type ->
     typing (extend_env g x t) (open_term e x) tm_type ->
     typing g (pack_ln (Tv_Refine (pack_bv (make_bv 0 t)) e)) tm_type

  | T_Sub:
     g:env ->
     e:term ->
     t:term ->
     t':term ->
     typing g e t ->
     sub_typing g t t' ->
     typing g e t'
    
and sub_typing : env -> term -> term -> Type0 =
  | ST_Refl: 
      g:env ->
      t:term ->
      sub_typing g t t
