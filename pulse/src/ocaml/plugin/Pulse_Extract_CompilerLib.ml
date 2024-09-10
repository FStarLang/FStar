module ML = FStar_Extraction_ML_Syntax
module UEnv = FStar_Extraction_ML_UEnv
module MLTerm = FStar_Extraction_ML_Term
module MLModul = FStar_Extraction_ML_Modul
module Env = FStar_TypeChecker_Env
module PC = FStar_Parser_Const
module BU = FStar_Compiler_Util

type uenv = UEnv.uenv
type mlexpr = ML.mlexpr
type e_tag = ML.e_tag
type mlty = ML.mlty

let mlty_unit = ML.ml_unit_ty

type mlty_param = ML.ty_param

type mlsymbol = ML.mlsymbol
type mlident  = ML.mlident
type mlpath   = ML.mlpath
type mltyscheme = ML.mltyscheme
type mlbinder = ML.mlbinder

type mllb = ML.mllb

let mk_ty_param ty_param_name ty_param_attrs = {
  ML.ty_param_name = ty_param_name;
  ML.ty_param_attrs = ty_param_attrs;
}

let mk_mllb_with_attrs
  (mllb_name:mlident)
  (mllb_tysc:mltyscheme)
  (mllb_def:mlexpr)
  (mllb_attrs:mlexpr list)
  : mllb 
  = { mllb_name;
      mllb_tysc=Some mllb_tysc;
      mllb_add_unit=false;
      mllb_def;
      mllb_meta=[];
      mllb_attrs;
      print_typ=false }


let mk_mllb (mllb_name:mlident)
            (mllb_tysc:mltyscheme)
            (mllb_def:mlexpr)
  : mllb 
  = mk_mllb_with_attrs mllb_name mllb_tysc mllb_def []

let mk_mut_mllb
  (mllb_name:mlident)
  (mllb_tysc:mltyscheme)
  (mllb_def:mlexpr)
: mllb 
= { mllb_name;
    mllb_tysc=Some mllb_tysc;
    mllb_add_unit=false;
    mllb_def;
    mllb_meta=[Mutable];
    mllb_attrs=[];
    print_typ=false }

type mlletbinding = ML.mlletbinding
type mlpattern = ML.mlpattern
type mlconstant = ML.mlconstant

let mk_mlletbinding (is_rec:bool) (lbs:mllb list)
  : mlletbinding
  = let flavor = if is_rec then ML.Rec else ML.NonRec in
    flavor, lbs
    
let as_expr expr : mlexpr = 
  { expr;
    mlty = ML.MLTY_Top;
    loc = ML.dummy_loc }

let mle_unit = ML.ml_unit

let mle_var (x:mlident) : mlexpr =
    as_expr (ML.MLE_Var x)

let mle_name (x:mlpath) : mlexpr =
    as_expr (ML.MLE_Name x)

let mle_let (x:mlletbinding) (b:mlexpr) : mlexpr =
    as_expr (ML.MLE_Let (x, b))
    
let mle_app (x:mlexpr) (args:mlexpr list) : mlexpr =
    match x.expr with
    | MLE_App(head, args0) -> as_expr (ML.MLE_App(head, args0@args))
    | _ -> as_expr (ML.MLE_App(x, args))

let mle_tapp (x:mlexpr) (args:mlty list) : mlexpr =
    as_expr (ML.MLE_TApp(x, args))

let mk_binders (bs:(mlident * mlty * mlexpr list) list) : mlbinder list =
  List.map (fun (x, t, attrs) -> {
    ML.mlbinder_name=x;
    ML.mlbinder_ty=t;
    ML.mlbinder_attrs=attrs
  }) bs

let mle_fun (formals:(mlident * mlty * mlexpr list) list) (body:mlexpr) : mlexpr =
   match body.expr with
   | ML.MLE_Fun(formals', body) -> 
     as_expr (ML.MLE_Fun((mk_binders formals)@formals', body))
   | _ ->
     as_expr (ML.MLE_Fun (mk_binders formals, body))

let mle_if g t e = as_expr (ML.MLE_If (g, t, e))

let mle_match (scrut:mlexpr) (branches:(mlpattern * mlexpr) list) : mlexpr =
    as_expr (ML.MLE_Match (scrut, List.map (fun (x, y) -> x, None, y) branches))

let mlconstant_of_mlexpr (e:mlexpr) =
  match e.expr with
  | ML.MLE_Const c -> Some c
  | _ -> None

let mlp_wild = ML.MLP_Wild
let mlp_var x = ML.MLP_Var x
let mlp_constructor x ps = ML.MLP_CTor (x, ps)
let mlp_const x = ML.MLP_Const x
let mlp_tuple x = ML.MLP_Tuple x

let e_tag_pure : e_tag = ML.E_PURE
let e_tag_erasable : e_tag = ML.E_ERASABLE
let e_tag_impure : e_tag = ML.E_IMPURE

let mlty_top : mlty = ML.MLTY_Top

let normalize_for_extraction (g:uenv) (t:FStar_Syntax_Syntax.term)
  : FStar_Syntax_Syntax.term
  = (* let extra = [] in *)
    let res = FStar_Extraction_ML_Term.normalize_for_extraction g t in
    res

let term_as_mlexpr (g:uenv) (t:FStar_Syntax_Syntax.term) : (mlexpr * e_tag * mlty) =
  FStar_Extraction_ML_Term.term_as_mlexpr g t
  
let term_as_mlty (g:uenv) (t:FStar_Syntax_Syntax.term) : mlty = 
  FStar_Extraction_ML_Term.term_as_mlty g t
  
module PSB = Pulse_Syntax_Base
module S = FStar_Syntax_Syntax
let extend_bv (g:uenv) (np:PSB.ppname) (uniq:_) (ty:mlty) : (uenv * mlident) =
  let ident = FStar_Ident.mk_ident (np.name, np.range) in
  let bv : S.bv = { ppname=ident; index=uniq; sort=FStar_Syntax_Syntax.tun } in
  let uenv, mlid, _ = UEnv.extend_bv g bv ([], ty) false false in
  uenv, mlid

let initial_core_env (g:uenv) : Pulse_Typing_Env.env =
  Pulse_Typing_Env.mk_env (UEnv.tcenv_of_uenv g)

let new_uenv (e: Env.env) : uenv = UEnv.new_uenv e

let set_tcenv g e = UEnv.set_tcenv g e

let mlty_to_string (t:mlty) = FStar_Extraction_ML_Syntax.mlty_to_string t
let mlexpr_to_string (e:mlexpr) = FStar_Extraction_ML_Syntax.mlexpr_to_string e
let sigelt_extension_data (e:S.sigelt) : Pulse_Syntax_Base.st_term option =
  match FStar_Compiler_List.tryFind (fun (s, _) -> s = "pulse") e.sigmeta.sigmeta_extension_data with
  | None -> None
  | Some (_, b) -> Some (Obj.magic (Pulse_RuntimeUtils.unembed_st_term_for_extraction (Obj.magic b)))

type mlmodule1= ML.mlmodule1
type mlmodule = ML.mlmodule

let mlm_let_with_attrs (is_rec:bool) (lbs:mllb list) (attrs:mlexpr list) : mlmodule1 =
  ML.mk_mlmodule1_with_attrs
    (ML.MLM_Let ((if is_rec then ML.Rec else ML.NonRec), lbs))
    attrs

let mlm_let (is_rec:bool) (lbs:mllb list) : mlmodule1 =
  mlm_let_with_attrs is_rec lbs []

let is_type (g:uenv) (t:S.typ) = MLTerm.is_arity g t

let extend_ty (g:uenv) (a:S.bv) = UEnv.extend_ty g a false

let lookup_ty (g:uenv) (a:S.bv) = (UEnv.lookup_ty g a).ty_b_name

type iface = MLModul.iface
type exp_binding = UEnv.exp_binding
let iface_of_bindings (l:(S.fv * exp_binding) list) = MLModul.iface_of_bindings l
let extend_fv (g:uenv) (x:S.fv) (tysc:mltyscheme) = UEnv.extend_fv g x tysc false

module U = FStar_Syntax_Util
module C = FStar_Parser_Const

type const = S.sconst
type fv = S.fv
type term = S.term
type binder = S.binder
let unit_tm = S.unit_const
let unit_ty = S.t_unit
type binder_qualifier = S.binder_qualifier
let implicit_qual = S.Implicit false
type arg_qualifier = S.arg_qualifier
let implicit_arg_qual = { S.aqual_implicit = true; S.aqual_attributes = [] }
let rt_term_to_term (t:term) : term = t
let mk_binder (sort:term) (ppname:string) (q:binder_qualifier option) (attrs:term list) : S.binder =
  S.mk_binder_with_attrs (S.gen_bv ppname None sort) q None attrs
let mk_abs (b:binder) (body:term) : term =
  S.mk (S.Tm_abs {bs=[b];body=body;rc_opt=None}) FStar_Compiler_Range.dummyRange
let mk_return (t:term) : term =
  S.mk
    (S.Tm_meta {tm2=t; meta=S.Meta_monadic_lift (C.effect_PURE_lid, C.effect_DIV_lid, S.tun)})
    FStar_Compiler_Range.dummyRange
let mk_app (head:term) (aqual:arg_qualifier option) (arg:term) : term =
  S.mk
    (S.Tm_meta {tm2=S.mk_Tm_app head [arg, aqual] FStar_Compiler_Range.dummyRange; meta=S.Meta_monadic (C.effect_DIV_lid, S.tun)})
    FStar_Compiler_Range.dummyRange
let mk_let (b:binder) (head:term) (body:term) : term =
  let lb = U.mk_letbinding
    (Inl b.binder_bv) [] b.binder_bv.sort C.effect_DIV_lid head [] FStar_Compiler_Range.dummyRange in
  let tm_let =
    S.mk (S.Tm_let {lbs=(false, [lb]); body1=body}) FStar_Compiler_Range.dummyRange in
  S.mk (S.Tm_meta {tm2=tm_let; meta=S.Meta_monadic (C.effect_DIV_lid, S.tun)}) FStar_Compiler_Range.dummyRange
let mk_if (b:term) (then_:term) (else_:term) : term =
  U.if_then_else b then_ else_
type pattern = S.pat
let mk_fv (s:string list) =
  S.fvconst (FStar_Ident.lid_of_ids ((List.map FStar_Ident.id_of_text s)))
let mk_fv_tm (fv:fv) : term = S.fv_to_tm fv 
let mk_pat_cons (fv:fv) (pats:pattern list) : pattern =
  S.withinfo
    (S.Pat_cons (fv, None, (List.map (fun p -> (p, false)) pats)))
    FStar_Compiler_Range.dummyRange
let mk_pat_constant (c:const) : pattern =
  S.withinfo (S.Pat_constant c) FStar_Compiler_Range.dummyRange
let mk_pat_var (ppname:string) (sort:term) : pattern =
  S.withinfo (S.Pat_var (S.gen_bv ppname None sort)) FStar_Compiler_Range.dummyRange
let mk_dot_pat (t:term option) : pattern =
  S.withinfo (S.Pat_dot_term t) FStar_Compiler_Range.dummyRange
let mk_const (c:FStar_Reflection_V2_Data.vconst) : const =
  FStar_Reflection_V2_Builtins.pack_const c
type branch = S.branch
let mk_branch (p:pattern) (body:term) : branch =
  (p, None, body)
let mk_match (scrutinee:term) (brs:branch list) : term =
  S.mk
    (S.Tm_match { scrutinee; ret_opt=None; brs; rc_opt1=None })
    FStar_Compiler_Range.dummyRange
let term_to_string (t:term) : string = FStar_Syntax_Print.term_to_string t
let mk_arrow (bs:binder list) (t:term) : term =
  let c =
    S.mk
      (S.Comp {comp_univs=[]; effect_name=C.effect_DIV_lid; result_typ=t; effect_args=[]; flags=[]})
      FStar_Compiler_Range.dummyRange in
  S.mk (S.Tm_arrow {bs1=bs;comp=c}) FStar_Compiler_Range.dummyRange
let unk_tm : term = S.mk (S.Tm_unknown) FStar_Compiler_Range.dummyRange
type sigelt = S.sigelt
let mk_non_rec_siglet (nm:string) (t:term) (ty:term) : sigelt =
  let lbname = FStar_Pervasives.Inr
    {S.fv_name=S.withinfo (FStar_Ident.lid_of_str nm) FStar_Compiler_Range.dummyRange;
     S.fv_qual=None} in
  let lb = U.mk_letbinding lbname [] ty C.effect_PURE_lid t [] FStar_Compiler_Range.dummyRange in
  {
    sigel=S.Sig_let {lbs1=(false,[lb]); lids1=[FStar_Ident.lid_of_str nm]};
    sigquals=[];
    sigmeta=S.default_sigmeta;
    sigattrs=[];
    sigopts=None;
    sigopens_and_abbrevs=[];
    sigrng=FStar_Compiler_Range.dummyRange
  }
let sigelt_to_string (s:sigelt) : string = FStar_Syntax_Print.sigelt_to_string s
