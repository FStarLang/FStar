module PulseExtract.CompilerLib
module T = FStar.Tactics.V2
val uenv : Type0
val mlexpr : Type0
val e_tag : Type0
val mlty  : Type0

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
val mle_var (x:mlident) : mlexpr
val mle_name (x:mlpath) : mlexpr
val mle_let (x:mlletbinding) (b:mlexpr) : mlexpr
val mle_app (x:mlexpr) (args:list mlexpr) : mlexpr
val mke_tapp (x:mlexpr) (args:list mlty) : mlexpr
val mle_fun (formals:list (mlident * mlty)) (body:mlexpr) : mlexpr

val e_tag_pure : e_tag
val e_tag_erasable : e_tag
val e_tag_impure : e_tag

val mlty_top : mlty

val term_as_mlexpr (g:uenv) (t:T.term) : Dv (mlexpr & e_tag & mlty)
val term_as_mlty (g:uenv) (t:T.term) : Dv mlty

module PSB = Pulse.Syntax.Base
val extend_bv (g:uenv) (np:PSB.ppname) (uniq:nat) (ty:mlty) : Dv (uenv & mlident)
val initial_core_env (g:uenv) : Pulse.Typing.Env.env
val set_tcenv (g:uenv) (e:T.env) :  uenv
val mlexpr_to_string (e:mlexpr) : Dv string
