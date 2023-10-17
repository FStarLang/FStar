module Pulse.Extract.CompilerLib

module R = FStar.Reflection
module T = FStar.Tactics.V2

val uenv : Type0
val mlexpr : Type0
val e_tag : Type0
val mlty  : Type0

val mlty_unit : mlty
type mlsymbol = string
type mlident  = mlsymbol
type mlpath   = list mlsymbol * mlsymbol //Path and name of a module
type mltyscheme = list mlident * mlty   //forall a1..an. t  (the list of binders can be empty)

val mllb : Type0

val mk_mllb (mllb_name:mlident)
            (mllb_tysc:mltyscheme)
            (mllb_def:mlexpr) : mllb


val mlletbinding : Type0
val mk_mlletbinding (is_rec:bool) (lbs:list mllb) : mlletbinding
val mle_unit : mlexpr
val mle_var (x:mlident) : mlexpr
val mle_name (x:mlpath) : mlexpr
val mle_let (x:mlletbinding) (b:mlexpr) : mlexpr
val mle_app (x:mlexpr) (args:list mlexpr) : mlexpr
val mke_tapp (x:mlexpr) (args:list mlty) : mlexpr
val mle_fun (formals:list (mlident * mlty)) (body:mlexpr) : mlexpr
val mle_if (guard:mlexpr) (t:mlexpr) (f:option mlexpr) : mlexpr

val mlpattern : Type0
val mlconstant : Type0

val mlconstant_of_mlexpr (e:mlexpr) : Dv (option mlconstant)
val mlp_wild : mlpattern
val mlp_var (x:mlident) : mlpattern
val mlp_const (t:mlconstant) : mlpattern
val mlp_constructor (name:mlpath) (ps:list mlpattern) : mlpattern
val mlp_tuple (ps:list mlpattern) : mlpattern

val mle_match (scrut:mlexpr) (branches:list (mlpattern & mlexpr)) : mlexpr

val e_tag_pure : e_tag
val e_tag_erasable : e_tag
val e_tag_impure : e_tag

val mlty_top : mlty

val normalize_for_extraction (g:uenv) (t:T.term) : Dv T.term
val term_as_mlexpr (g:uenv) (t:T.term) : Dv (mlexpr & e_tag & mlty)
val term_as_mlty (g:uenv) (t:T.term) : Dv mlty

module PSB = Pulse.Syntax.Base
val extend_bv (g:uenv) (np:PSB.ppname) (uniq:nat) (ty:mlty) : Dv (uenv & mlident)
val initial_core_env (g:uenv) : Pulse.Typing.Env.env
val set_tcenv (g:uenv) (e:T.env) :  uenv
val mlexpr_to_string (e:mlexpr) : Dv string
open Pulse.Syntax.Base
val sigelt_extension_data (e:T.sigelt) : option st_term

val mlmodule1 : Type0
type mlmodule = list mlmodule1

val mlm_let (is_rec:bool) (lbs:list mllb) : mlmodule1
val is_type (g:uenv) (t:R.typ) : Dv bool
val extend_ty (g:uenv) (a:R.namedv) : Dv uenv
val lookup_ty (g:uenv) (a:R.namedv) : Dv mlident

val iface : Type0
val exp_binding : Type0
val iface_of_bindings : list (R.fv & exp_binding) -> iface
val extend_fv : uenv -> R.fv -> mltyscheme -> Dv (uenv & mlident & exp_binding)
