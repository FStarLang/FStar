module ML = FStar_Extraction_ML_Syntax
module UEnv = FStar_Extraction_ML_UEnv
type uenv = UEnv.uenv
type mlexpr = ML.mlexpr
type e_tag = ML.e_tag
type mlty = ML.mlty

let mlty_unit = ML.ml_unit_ty

type mlsymbol = ML.mlsymbol
type mlident  = ML.mlident
type mlpath   = ML.mlpath
type mltyscheme = ML.mltyscheme


type mllb = ML.mllb

let mk_mllb (mllb_name:mlident)
            (mllb_tysc:mltyscheme)
            (mllb_def:mlexpr)
  : mllb 
  = { mllb_name;
      mllb_tysc=Some mllb_tysc;
      mllb_add_unit=false;
      mllb_def;
      mllb_meta=[];
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
    
let mle_fun (formals:(mlident * mlty) list) (body:mlexpr) : mlexpr =
   match body.expr with
   | ML.MLE_Fun(formals', body) -> 
     as_expr (ML.MLE_Fun(formals@formals', body))
   | _ ->
     as_expr (ML.MLE_Fun (formals, body))

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

let set_tcenv g e = UEnv.set_tcenv g e

let mlexpr_to_string (e:mlexpr) = FStar_Extraction_ML_Syntax.mlexpr_to_string e
