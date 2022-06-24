module FStar.Reflection.Helpers

open FStar.Reflection
module R = FStar.Reflection

//
// Should move to ulib
//

val inspect_pack (t:R.term_view)
  : Lemma (ensures R.(inspect_ln (pack_ln t) == t))
          [SMTPat R.(inspect_ln (pack_ln t))]

val pack_inspect (t:R.term)
  : Lemma (ensures R.(pack_ln (inspect_ln t) == t))
          [SMTPat R.(pack_ln (inspect_ln t))]

val inspect_pack_bv (t:R.bv_view)
  : Lemma (ensures R.(inspect_bv (pack_bv t) == t))
          [SMTPat R.(inspect_bv (pack_bv t))]

val pack_inspect_bv (t:R.bv)
  : Lemma (ensures R.(pack_bv (inspect_bv t) == t))
          [SMTPat R.(pack_bv (inspect_bv t))]

val inspect_pack_binder (b:_) (q:_) (a:_)
  : Lemma (ensures R.(R.inspect_binder (R.pack_binder b q a) == (b, (q, a))))
          [SMTPat R.(inspect_binder (pack_binder b q a))]

val pack_inspect_binder (t:R.binder)
  : Lemma (ensures (let b, (q, a) = R.inspect_binder t in
                    R.(pack_binder b q a == t)))

val pack_inspect_comp (t:R.comp)
  : Lemma (ensures (R.pack_comp (R.inspect_comp t) == t))
          [SMTPat (R.pack_comp (R.inspect_comp t))]

val inspect_pack_comp (t:R.comp_view)
  : Lemma (ensures (R.inspect_comp (R.pack_comp t) == t))
          [SMTPat (R.inspect_comp (R.pack_comp t))]

val lookup_bvar (e:env) (x:int) : option term

val lookup_fvar (e:env) (x:fv) : option term

val extend_env (e:env) (x:var) (ty:term) : env

val lookup_bvar_extend_env (g:env) (x y:var) (ty:term)
  : Lemma 
    (ensures (
           if x = y
           then lookup_bvar (extend_env g x ty) y == Some ty
           else lookup_bvar (extend_env g x ty) y == lookup_bvar g y))
    [SMTPat (lookup_bvar (extend_env g x ty) y)]

val lookup_fvar_extend_env (g:env) (x:fv) (y:var) (ty:term)
  : Lemma 
    (ensures lookup_fvar (extend_env g y ty) x == lookup_fvar g x)
    [SMTPat (lookup_fvar (extend_env g y ty) x)]

let as_binder (x:var) (ty:term)
  : binder 
  = pack_binder
      (pack_bv ({bv_ppname="";
                 bv_index=x;
                 bv_sort=ty}))
      Q_Explicit
      []

let bv_index (x:bv) : int = (inspect_bv x).bv_index

let binder_sort (b:binder) =
  let bv, _ = inspect_binder b in 
  (inspect_bv bv).bv_sort

let binder_sort_lemma (x:var) (ty:term)
  : Lemma (binder_sort (as_binder x ty) == ty)
          [SMTPat (binder_sort (as_binder x ty))]
  = ()

type guard = option typ

let trivial_guard = None

let bv_as_binder bv = pack_binder bv Q_Explicit []

let make_bv (n:nat) (t:term) = { bv_ppname = "_"; bv_index = n; bv_sort = t}
let var_as_bv (v:var) = pack_bv (make_bv v (pack_ln Tv_Unknown))
let var_as_term (v:var) = pack_ln (Tv_Var (var_as_bv v))

let bv_index_of_make_bv (n:nat) (t:term)
  : Lemma (ensures bv_index (pack_bv (make_bv n t)) == n)
          [SMTPat (bv_index (pack_bv (make_bv n t)))]
  = ()

let constant_as_term (v:vconst) = pack_ln (Tv_Const v)
let unit_exp = constant_as_term C_Unit
let unit_fv = pack_fv unit_lid
let unit_ty = pack_ln (Tv_FVar unit_fv)
let bool_fv = pack_fv bool_lid
let bool_ty = pack_ln (Tv_FVar bool_fv)

let mk_total u t = pack_comp (C_Total t u [])
let tm_type u = pack_ln (Tv_Type u)

let true_bool = pack_ln (Tv_Const C_True)
let false_bool = pack_ln (Tv_Const C_False)
let eq2 (t v0 v1:term) 
  : term 
  = let eq2 = pack_ln (Tv_FVar (pack_fv eq2_qn)) in
    let h = pack_ln (Tv_App eq2 (t, Q_Implicit)) in
    let h1 = pack_ln (Tv_App h (v0, Q_Explicit)) in
    let h2 = pack_ln (Tv_App h1 (v1, Q_Explicit)) in    
    h2

val mk_conj (t1 t2:typ) : typ

let bindings = list (var & term)

let rec extend_env_l (g:env) (bs:bindings) 
  : env
  = match bs with
    | [] -> g
    | (x,t)::bs -> extend_env (extend_env_l g bs) x t

let u_zero = pack_universe Uv_Zero
let typ0 = tm_type u_zero
