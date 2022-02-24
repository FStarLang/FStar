module DSL.Reflection

open FStar.Reflection.Types
open FStar.Reflection.Data
open FStar.Reflection.Builtins
open FStar.Reflection.Formula

open FStar.Tactics

type guard = typ
type univ_names = list univ_name

let mk_tm_name (bv:bv) : term =
  pack_ln (Tv_Var bv)

let mk_tm_fvar (fv:fv) : term =
  pack_ln (Tv_FVar fv)

let mk_tm_const (c:vconst) : term =
  pack_ln (Tv_Const c)

let mk_tm_arrow (b:binder) (c:comp) : term =
  pack_ln (Tv_Arrow b c)  //It closes c?

let mk_tm_abs (b:binder) (t:term) : term =
  pack_ln (Tv_Abs b t)  //It closes t?

let mk_tm_let (bv:bv) (e1 e2:term) : term =
  pack_ln (Tv_Let false [] bv e1 e2)  //It closes e2?

let mk_tm_refine (bv:bv) (phi:term) : term =
  pack_ln (Tv_Refine bv phi)  //It closes phi?

let mk_tot (t:typ) : comp =
  pack_comp (C_Total t [])

let bv_sort (bv:bv) : typ =
  (inspect_bv bv).bv_sort

let binder_sort (b:binder) : typ =
  bv_sort (fst (inspect_binder b))

let trivial_guard : term =
  formula_as_term True_

let conj_guards (g1 g2:guard) : guard =
  formula_as_term (And g1 g2)

let ( ++ ) = conj_guards

//make curried application node
assume val mk_app (t:term) (args:list argv) : term

(* Move to Reflection *)
type effect_label = name
assume val lookup_name (env:env) (bv:bv) : option typ
assume val lookup_fv (env:env) (fv:fv) (univs:univ_names) : option typ
assume val extend_env (_:env) (bv:bv) : env
assume val lookup_bind (env:env) (m:effect_label) : option typ
assume val fv_of_name (name:name) : fv
assume val term_to_arg (t:term) : argv
assume val mk_comp (eff_name:name) (t:typ) (args:list argv) : comp
assume val mk_binder (bv:bv) : binder
assume val mk_non_dep_arrow (t:typ) (c:comp) : typ

assume val push_binder_lookup1 (g:env) (b:binder) (bv:bv)
  : Lemma (Some? (lookup_name g bv) ==>
           Some? (lookup_name (push_binder g b) bv))
          [SMTPat (lookup_name (push_binder g b) bv)]
assume val push_binder_lookup2 (g:env) (bv:bv)
  : Lemma (Some? (lookup_name (push_binder g (mk_binder bv)) bv))
          [SMTPat (lookup_name (push_binder g (mk_binder bv)) bv)]

assume val fresh_bv (s:string) (t:typ) : bv:bv{bv_sort bv == t}
assume val binder_bv_sort (bv:bv)
  : Lemma (binder_sort (mk_binder bv) == bv_sort bv)
          [SMTPat (binder_sort (mk_binder bv))]

assume val t_unit   : term
assume val t_int    : term
assume val t_bool   : term
assume val t_string : term
assume val t_type   : term  //augment this with univ, see the enhancements at the top
assume val t_effect : term

(* substitutions *)
assume val close_guard (g:guard) (bv:bv) : guard
assume val close_guard_binder (g:guard) (b:binder) : guard
assume val subst_comp (name:bv) (t:term) (c:comp) : comp

assume val comp_result_type (c:comp) : typ
assume val set_bv_sort (_:bv) (t:typ) : bv
assume val comp_effect_label (env:env) (c:comp) : effect_label
assume val is_wp_effect (env:env) (eff:effect_label) : bool

//this will lookup the bind combinator for M and apply it
assume val apply_M_bind (env:env)
  (e1:option term)
  (c1:comp)
  (bv:option bv)
  (c2:comp{comp_effect_label env c1 == comp_effect_label env c2})
  : comp & guard

