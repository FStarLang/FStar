open Prims
type mlsymbol = Prims.string
type mlident = mlsymbol
type mlpath = (mlsymbol Prims.list * mlsymbol)
let krml_keywords : Prims.string Prims.list= []
let ocamlkeywords : Prims.string Prims.list=
  ["and";
  "as";
  "assert";
  "asr";
  "begin";
  "class";
  "constraint";
  "do";
  "done";
  "downto";
  "else";
  "end";
  "exception";
  "external";
  "false";
  "for";
  "fun";
  "function";
  "functor";
  "if";
  "in";
  "include";
  "inherit";
  "initializer";
  "land";
  "lazy";
  "let";
  "lor";
  "lsl";
  "lsr";
  "lxor";
  "match";
  "method";
  "mod";
  "module";
  "mutable";
  "new";
  "object";
  "of";
  "open";
  "or";
  "private";
  "rec";
  "sig";
  "struct";
  "then";
  "to";
  "true";
  "try";
  "type";
  "val";
  "virtual";
  "when";
  "while";
  "with";
  "nonrec"]
let fsharpkeywords : Prims.string Prims.list=
  ["abstract";
  "and";
  "as";
  "assert";
  "base";
  "begin";
  "class";
  "default";
  "delegate";
  "do";
  "done";
  "downcast";
  "downto";
  "elif";
  "else";
  "end";
  "exception";
  "extern";
  "false";
  "finally";
  "fixed";
  "for";
  "fun";
  "function";
  "global";
  "if";
  "in";
  "inherit";
  "inline";
  "interface";
  "internal";
  "lazy";
  "let";
  "let!";
  "match";
  "member";
  "module";
  "mutable";
  "namespace";
  "new";
  "not";
  "null";
  "of";
  "open";
  "or";
  "override";
  "private";
  "public";
  "rec";
  "return";
  "return!";
  "select";
  "static";
  "struct";
  "then";
  "to";
  "true";
  "try";
  "type";
  "upcast";
  "use";
  "use!";
  "val";
  "void";
  "when";
  "while";
  "with";
  "yield";
  "yield!";
  "asr";
  "land";
  "lor";
  "lsl";
  "lsr";
  "lxor";
  "mod";
  "sig";
  "atomic";
  "break";
  "checked";
  "component";
  "const";
  "constraint";
  "constructor";
  "continue";
  "eager";
  "event";
  "external";
  "fixed";
  "functor";
  "include";
  "method";
  "mixin";
  "object";
  "parallel";
  "process";
  "protected";
  "pure";
  "sealed";
  "tailcall";
  "trait";
  "virtual";
  "volatile"]
let string_of_mlpath (uu___ : mlpath) : Prims.string=
  match uu___ with
  | (p, s) -> FStarC_String.concat "." (FStarC_List.op_At p [s])
type mlidents = mlident Prims.list
type mlsymbols = mlsymbol Prims.list
type e_tag =
  | E_PURE 
  | E_ERASABLE 
  | E_IMPURE 
let uu___is_E_PURE (projectee : e_tag) : Prims.bool=
  match projectee with | E_PURE -> true | uu___ -> false
let uu___is_E_ERASABLE (projectee : e_tag) : Prims.bool=
  match projectee with | E_ERASABLE -> true | uu___ -> false
let uu___is_E_IMPURE (projectee : e_tag) : Prims.bool=
  match projectee with | E_IMPURE -> true | uu___ -> false
type mlloc = (Prims.int * Prims.string)
let dummy_loc : mlloc= (Prims.int_zero, "")
type mlty =
  | MLTY_Var of mlident 
  | MLTY_Fun of (mlty * e_tag * mlty) 
  | MLTY_Named of (mlty Prims.list * mlpath) 
  | MLTY_Tuple of mlty Prims.list 
  | MLTY_Top 
  | MLTY_Erased 
let uu___is_MLTY_Var (projectee : mlty) : Prims.bool=
  match projectee with | MLTY_Var _0 -> true | uu___ -> false
let __proj__MLTY_Var__item___0 (projectee : mlty) : mlident=
  match projectee with | MLTY_Var _0 -> _0
let uu___is_MLTY_Fun (projectee : mlty) : Prims.bool=
  match projectee with | MLTY_Fun _0 -> true | uu___ -> false
let __proj__MLTY_Fun__item___0 (projectee : mlty) : (mlty * e_tag * mlty)=
  match projectee with | MLTY_Fun _0 -> _0
let uu___is_MLTY_Named (projectee : mlty) : Prims.bool=
  match projectee with | MLTY_Named _0 -> true | uu___ -> false
let __proj__MLTY_Named__item___0 (projectee : mlty) :
  (mlty Prims.list * mlpath)= match projectee with | MLTY_Named _0 -> _0
let uu___is_MLTY_Tuple (projectee : mlty) : Prims.bool=
  match projectee with | MLTY_Tuple _0 -> true | uu___ -> false
let __proj__MLTY_Tuple__item___0 (projectee : mlty) : mlty Prims.list=
  match projectee with | MLTY_Tuple _0 -> _0
let uu___is_MLTY_Top (projectee : mlty) : Prims.bool=
  match projectee with | MLTY_Top -> true | uu___ -> false
let uu___is_MLTY_Erased (projectee : mlty) : Prims.bool=
  match projectee with | MLTY_Erased -> true | uu___ -> false
type mlconstant =
  | MLC_Unit 
  | MLC_Bool of Prims.bool 
  | MLC_Int of (Prims.string * (FStarC_Const.signedness * FStarC_Const.width)
  FStar_Pervasives_Native.option) 
  | MLC_Float of FStarC_BaseTypes.float 
  | MLC_Char of FStarC_BaseTypes.char 
  | MLC_String of Prims.string 
let uu___is_MLC_Unit (projectee : mlconstant) : Prims.bool=
  match projectee with | MLC_Unit -> true | uu___ -> false
let uu___is_MLC_Bool (projectee : mlconstant) : Prims.bool=
  match projectee with | MLC_Bool _0 -> true | uu___ -> false
let __proj__MLC_Bool__item___0 (projectee : mlconstant) : Prims.bool=
  match projectee with | MLC_Bool _0 -> _0
let uu___is_MLC_Int (projectee : mlconstant) : Prims.bool=
  match projectee with | MLC_Int _0 -> true | uu___ -> false
let __proj__MLC_Int__item___0 (projectee : mlconstant) :
  (Prims.string * (FStarC_Const.signedness * FStarC_Const.width)
    FStar_Pervasives_Native.option)=
  match projectee with | MLC_Int _0 -> _0
let uu___is_MLC_Float (projectee : mlconstant) : Prims.bool=
  match projectee with | MLC_Float _0 -> true | uu___ -> false
let __proj__MLC_Float__item___0 (projectee : mlconstant) :
  FStarC_BaseTypes.float= match projectee with | MLC_Float _0 -> _0
let uu___is_MLC_Char (projectee : mlconstant) : Prims.bool=
  match projectee with | MLC_Char _0 -> true | uu___ -> false
let __proj__MLC_Char__item___0 (projectee : mlconstant) :
  FStarC_BaseTypes.char= match projectee with | MLC_Char _0 -> _0
let uu___is_MLC_String (projectee : mlconstant) : Prims.bool=
  match projectee with | MLC_String _0 -> true | uu___ -> false
let __proj__MLC_String__item___0 (projectee : mlconstant) : Prims.string=
  match projectee with | MLC_String _0 -> _0
type mlpattern =
  | MLP_Wild 
  | MLP_Const of mlconstant 
  | MLP_Var of mlident 
  | MLP_CTor of (mlpath * mlpattern Prims.list) 
  | MLP_Branch of mlpattern Prims.list 
  | MLP_Record of (mlsymbol Prims.list * (mlsymbol * mlpattern) Prims.list) 
  | MLP_Tuple of mlpattern Prims.list 
let uu___is_MLP_Wild (projectee : mlpattern) : Prims.bool=
  match projectee with | MLP_Wild -> true | uu___ -> false
let uu___is_MLP_Const (projectee : mlpattern) : Prims.bool=
  match projectee with | MLP_Const _0 -> true | uu___ -> false
let __proj__MLP_Const__item___0 (projectee : mlpattern) : mlconstant=
  match projectee with | MLP_Const _0 -> _0
let uu___is_MLP_Var (projectee : mlpattern) : Prims.bool=
  match projectee with | MLP_Var _0 -> true | uu___ -> false
let __proj__MLP_Var__item___0 (projectee : mlpattern) : mlident=
  match projectee with | MLP_Var _0 -> _0
let uu___is_MLP_CTor (projectee : mlpattern) : Prims.bool=
  match projectee with | MLP_CTor _0 -> true | uu___ -> false
let __proj__MLP_CTor__item___0 (projectee : mlpattern) :
  (mlpath * mlpattern Prims.list)= match projectee with | MLP_CTor _0 -> _0
let uu___is_MLP_Branch (projectee : mlpattern) : Prims.bool=
  match projectee with | MLP_Branch _0 -> true | uu___ -> false
let __proj__MLP_Branch__item___0 (projectee : mlpattern) :
  mlpattern Prims.list= match projectee with | MLP_Branch _0 -> _0
let uu___is_MLP_Record (projectee : mlpattern) : Prims.bool=
  match projectee with | MLP_Record _0 -> true | uu___ -> false
let __proj__MLP_Record__item___0 (projectee : mlpattern) :
  (mlsymbol Prims.list * (mlsymbol * mlpattern) Prims.list)=
  match projectee with | MLP_Record _0 -> _0
let uu___is_MLP_Tuple (projectee : mlpattern) : Prims.bool=
  match projectee with | MLP_Tuple _0 -> true | uu___ -> false
let __proj__MLP_Tuple__item___0 (projectee : mlpattern) :
  mlpattern Prims.list= match projectee with | MLP_Tuple _0 -> _0
type meta =
  | Mutable 
  | Assumed 
  | Private 
  | NoExtract 
  | CInline 
  | Substitute 
  | GCType 
  | PpxDerivingShow 
  | PpxDerivingShowConstant of Prims.string 
  | PpxDerivingYoJson 
  | Comment of Prims.string 
  | StackInline 
  | CPrologue of Prims.string 
  | CEpilogue of Prims.string 
  | CConst of Prims.string 
  | CCConv of Prims.string 
  | Erased 
  | CAbstract 
  | CIfDef 
  | CMacro 
  | Deprecated of Prims.string 
  | RemoveUnusedTypeParameters of (Prims.int Prims.list *
  FStarC_Range_Type.t) 
  | HasValDecl of FStarC_Range_Type.t 
  | CNoInline 
let uu___is_Mutable (projectee : meta) : Prims.bool=
  match projectee with | Mutable -> true | uu___ -> false
let uu___is_Assumed (projectee : meta) : Prims.bool=
  match projectee with | Assumed -> true | uu___ -> false
let uu___is_Private (projectee : meta) : Prims.bool=
  match projectee with | Private -> true | uu___ -> false
let uu___is_NoExtract (projectee : meta) : Prims.bool=
  match projectee with | NoExtract -> true | uu___ -> false
let uu___is_CInline (projectee : meta) : Prims.bool=
  match projectee with | CInline -> true | uu___ -> false
let uu___is_Substitute (projectee : meta) : Prims.bool=
  match projectee with | Substitute -> true | uu___ -> false
let uu___is_GCType (projectee : meta) : Prims.bool=
  match projectee with | GCType -> true | uu___ -> false
let uu___is_PpxDerivingShow (projectee : meta) : Prims.bool=
  match projectee with | PpxDerivingShow -> true | uu___ -> false
let uu___is_PpxDerivingShowConstant (projectee : meta) : Prims.bool=
  match projectee with | PpxDerivingShowConstant _0 -> true | uu___ -> false
let __proj__PpxDerivingShowConstant__item___0 (projectee : meta) :
  Prims.string= match projectee with | PpxDerivingShowConstant _0 -> _0
let uu___is_PpxDerivingYoJson (projectee : meta) : Prims.bool=
  match projectee with | PpxDerivingYoJson -> true | uu___ -> false
let uu___is_Comment (projectee : meta) : Prims.bool=
  match projectee with | Comment _0 -> true | uu___ -> false
let __proj__Comment__item___0 (projectee : meta) : Prims.string=
  match projectee with | Comment _0 -> _0
let uu___is_StackInline (projectee : meta) : Prims.bool=
  match projectee with | StackInline -> true | uu___ -> false
let uu___is_CPrologue (projectee : meta) : Prims.bool=
  match projectee with | CPrologue _0 -> true | uu___ -> false
let __proj__CPrologue__item___0 (projectee : meta) : Prims.string=
  match projectee with | CPrologue _0 -> _0
let uu___is_CEpilogue (projectee : meta) : Prims.bool=
  match projectee with | CEpilogue _0 -> true | uu___ -> false
let __proj__CEpilogue__item___0 (projectee : meta) : Prims.string=
  match projectee with | CEpilogue _0 -> _0
let uu___is_CConst (projectee : meta) : Prims.bool=
  match projectee with | CConst _0 -> true | uu___ -> false
let __proj__CConst__item___0 (projectee : meta) : Prims.string=
  match projectee with | CConst _0 -> _0
let uu___is_CCConv (projectee : meta) : Prims.bool=
  match projectee with | CCConv _0 -> true | uu___ -> false
let __proj__CCConv__item___0 (projectee : meta) : Prims.string=
  match projectee with | CCConv _0 -> _0
let uu___is_Erased (projectee : meta) : Prims.bool=
  match projectee with | Erased -> true | uu___ -> false
let uu___is_CAbstract (projectee : meta) : Prims.bool=
  match projectee with | CAbstract -> true | uu___ -> false
let uu___is_CIfDef (projectee : meta) : Prims.bool=
  match projectee with | CIfDef -> true | uu___ -> false
let uu___is_CMacro (projectee : meta) : Prims.bool=
  match projectee with | CMacro -> true | uu___ -> false
let uu___is_Deprecated (projectee : meta) : Prims.bool=
  match projectee with | Deprecated _0 -> true | uu___ -> false
let __proj__Deprecated__item___0 (projectee : meta) : Prims.string=
  match projectee with | Deprecated _0 -> _0
let uu___is_RemoveUnusedTypeParameters (projectee : meta) : Prims.bool=
  match projectee with
  | RemoveUnusedTypeParameters _0 -> true
  | uu___ -> false
let __proj__RemoveUnusedTypeParameters__item___0 (projectee : meta) :
  (Prims.int Prims.list * FStarC_Range_Type.t)=
  match projectee with | RemoveUnusedTypeParameters _0 -> _0
let uu___is_HasValDecl (projectee : meta) : Prims.bool=
  match projectee with | HasValDecl _0 -> true | uu___ -> false
let __proj__HasValDecl__item___0 (projectee : meta) : FStarC_Range_Type.t=
  match projectee with | HasValDecl _0 -> _0
let uu___is_CNoInline (projectee : meta) : Prims.bool=
  match projectee with | CNoInline -> true | uu___ -> false
type metadata = meta Prims.list
type mlletflavor =
  | Rec 
  | NonRec 
let uu___is_Rec (projectee : mlletflavor) : Prims.bool=
  match projectee with | Rec -> true | uu___ -> false
let uu___is_NonRec (projectee : mlletflavor) : Prims.bool=
  match projectee with | NonRec -> true | uu___ -> false
type mlbinder =
  {
  mlbinder_name: mlident ;
  mlbinder_ty: mlty ;
  mlbinder_attrs: mlexpr Prims.list }
and mlexpr' =
  | MLE_Const of mlconstant 
  | MLE_Var of mlident 
  | MLE_Name of mlpath 
  | MLE_Let of ((mlletflavor * mllb Prims.list) * mlexpr) 
  | MLE_App of (mlexpr * mlexpr Prims.list) 
  | MLE_TApp of (mlexpr * mlty Prims.list) 
  | MLE_Fun of (mlbinder Prims.list * mlexpr) 
  | MLE_Match of (mlexpr * (mlpattern * mlexpr FStar_Pervasives_Native.option
  * mlexpr) Prims.list) 
  | MLE_Coerce of (mlexpr * mlty * mlty) 
  | MLE_CTor of (mlpath * mlexpr Prims.list) 
  | MLE_Seq of mlexpr Prims.list 
  | MLE_Tuple of mlexpr Prims.list 
  | MLE_Record of (mlsymbol Prims.list * mlsymbol * (mlsymbol * mlexpr)
  Prims.list) 
  | MLE_Proj of (mlexpr * mlpath) 
  | MLE_If of (mlexpr * mlexpr * mlexpr FStar_Pervasives_Native.option) 
  | MLE_Raise of (mlpath * mlexpr Prims.list) 
  | MLE_Try of (mlexpr * (mlpattern * mlexpr FStar_Pervasives_Native.option *
  mlexpr) Prims.list) 
and mlexpr = {
  expr: mlexpr' ;
  mlty: mlty ;
  loc: mlloc }
and mllb =
  {
  mllb_name: mlident ;
  mllb_tysc: (ty_param Prims.list * mlty) FStar_Pervasives_Native.option ;
  mllb_add_unit: Prims.bool ;
  mllb_def: mlexpr ;
  mllb_attrs: mlexpr Prims.list ;
  mllb_meta: metadata ;
  print_typ: Prims.bool }
and ty_param = {
  ty_param_name: mlident ;
  ty_param_attrs: mlexpr Prims.list }
let __proj__Mkmlbinder__item__mlbinder_name (projectee : mlbinder) : 
  mlident=
  match projectee with
  | { mlbinder_name; mlbinder_ty; mlbinder_attrs;_} -> mlbinder_name
let __proj__Mkmlbinder__item__mlbinder_ty (projectee : mlbinder) : mlty=
  match projectee with
  | { mlbinder_name; mlbinder_ty; mlbinder_attrs;_} -> mlbinder_ty
let __proj__Mkmlbinder__item__mlbinder_attrs (projectee : mlbinder) :
  mlexpr Prims.list=
  match projectee with
  | { mlbinder_name; mlbinder_ty; mlbinder_attrs;_} -> mlbinder_attrs
let uu___is_MLE_Const (projectee : mlexpr') : Prims.bool=
  match projectee with | MLE_Const _0 -> true | uu___ -> false
let __proj__MLE_Const__item___0 (projectee : mlexpr') : mlconstant=
  match projectee with | MLE_Const _0 -> _0
let uu___is_MLE_Var (projectee : mlexpr') : Prims.bool=
  match projectee with | MLE_Var _0 -> true | uu___ -> false
let __proj__MLE_Var__item___0 (projectee : mlexpr') : mlident=
  match projectee with | MLE_Var _0 -> _0
let uu___is_MLE_Name (projectee : mlexpr') : Prims.bool=
  match projectee with | MLE_Name _0 -> true | uu___ -> false
let __proj__MLE_Name__item___0 (projectee : mlexpr') : mlpath=
  match projectee with | MLE_Name _0 -> _0
let uu___is_MLE_Let (projectee : mlexpr') : Prims.bool=
  match projectee with | MLE_Let _0 -> true | uu___ -> false
let __proj__MLE_Let__item___0 (projectee : mlexpr') :
  ((mlletflavor * mllb Prims.list) * mlexpr)=
  match projectee with | MLE_Let _0 -> _0
let uu___is_MLE_App (projectee : mlexpr') : Prims.bool=
  match projectee with | MLE_App _0 -> true | uu___ -> false
let __proj__MLE_App__item___0 (projectee : mlexpr') :
  (mlexpr * mlexpr Prims.list)= match projectee with | MLE_App _0 -> _0
let uu___is_MLE_TApp (projectee : mlexpr') : Prims.bool=
  match projectee with | MLE_TApp _0 -> true | uu___ -> false
let __proj__MLE_TApp__item___0 (projectee : mlexpr') :
  (mlexpr * mlty Prims.list)= match projectee with | MLE_TApp _0 -> _0
let uu___is_MLE_Fun (projectee : mlexpr') : Prims.bool=
  match projectee with | MLE_Fun _0 -> true | uu___ -> false
let __proj__MLE_Fun__item___0 (projectee : mlexpr') :
  (mlbinder Prims.list * mlexpr)= match projectee with | MLE_Fun _0 -> _0
let uu___is_MLE_Match (projectee : mlexpr') : Prims.bool=
  match projectee with | MLE_Match _0 -> true | uu___ -> false
let __proj__MLE_Match__item___0 (projectee : mlexpr') :
  (mlexpr * (mlpattern * mlexpr FStar_Pervasives_Native.option * mlexpr)
    Prims.list)=
  match projectee with | MLE_Match _0 -> _0
let uu___is_MLE_Coerce (projectee : mlexpr') : Prims.bool=
  match projectee with | MLE_Coerce _0 -> true | uu___ -> false
let __proj__MLE_Coerce__item___0 (projectee : mlexpr') :
  (mlexpr * mlty * mlty)= match projectee with | MLE_Coerce _0 -> _0
let uu___is_MLE_CTor (projectee : mlexpr') : Prims.bool=
  match projectee with | MLE_CTor _0 -> true | uu___ -> false
let __proj__MLE_CTor__item___0 (projectee : mlexpr') :
  (mlpath * mlexpr Prims.list)= match projectee with | MLE_CTor _0 -> _0
let uu___is_MLE_Seq (projectee : mlexpr') : Prims.bool=
  match projectee with | MLE_Seq _0 -> true | uu___ -> false
let __proj__MLE_Seq__item___0 (projectee : mlexpr') : mlexpr Prims.list=
  match projectee with | MLE_Seq _0 -> _0
let uu___is_MLE_Tuple (projectee : mlexpr') : Prims.bool=
  match projectee with | MLE_Tuple _0 -> true | uu___ -> false
let __proj__MLE_Tuple__item___0 (projectee : mlexpr') : mlexpr Prims.list=
  match projectee with | MLE_Tuple _0 -> _0
let uu___is_MLE_Record (projectee : mlexpr') : Prims.bool=
  match projectee with | MLE_Record _0 -> true | uu___ -> false
let __proj__MLE_Record__item___0 (projectee : mlexpr') :
  (mlsymbol Prims.list * mlsymbol * (mlsymbol * mlexpr) Prims.list)=
  match projectee with | MLE_Record _0 -> _0
let uu___is_MLE_Proj (projectee : mlexpr') : Prims.bool=
  match projectee with | MLE_Proj _0 -> true | uu___ -> false
let __proj__MLE_Proj__item___0 (projectee : mlexpr') : (mlexpr * mlpath)=
  match projectee with | MLE_Proj _0 -> _0
let uu___is_MLE_If (projectee : mlexpr') : Prims.bool=
  match projectee with | MLE_If _0 -> true | uu___ -> false
let __proj__MLE_If__item___0 (projectee : mlexpr') :
  (mlexpr * mlexpr * mlexpr FStar_Pervasives_Native.option)=
  match projectee with | MLE_If _0 -> _0
let uu___is_MLE_Raise (projectee : mlexpr') : Prims.bool=
  match projectee with | MLE_Raise _0 -> true | uu___ -> false
let __proj__MLE_Raise__item___0 (projectee : mlexpr') :
  (mlpath * mlexpr Prims.list)= match projectee with | MLE_Raise _0 -> _0
let uu___is_MLE_Try (projectee : mlexpr') : Prims.bool=
  match projectee with | MLE_Try _0 -> true | uu___ -> false
let __proj__MLE_Try__item___0 (projectee : mlexpr') :
  (mlexpr * (mlpattern * mlexpr FStar_Pervasives_Native.option * mlexpr)
    Prims.list)=
  match projectee with | MLE_Try _0 -> _0
let __proj__Mkmlexpr__item__expr (projectee : mlexpr) : mlexpr'=
  match projectee with | { expr; mlty = mlty1; loc;_} -> expr
let __proj__Mkmlexpr__item__mlty (projectee : mlexpr) : mlty=
  match projectee with | { expr; mlty = mlty1; loc;_} -> mlty1
let __proj__Mkmlexpr__item__loc (projectee : mlexpr) : mlloc=
  match projectee with | { expr; mlty = mlty1; loc;_} -> loc
let __proj__Mkmllb__item__mllb_name (projectee : mllb) : mlident=
  match projectee with
  | { mllb_name; mllb_tysc; mllb_add_unit; mllb_def; mllb_attrs; mllb_meta;
      print_typ;_} -> mllb_name
let __proj__Mkmllb__item__mllb_tysc (projectee : mllb) :
  (ty_param Prims.list * mlty) FStar_Pervasives_Native.option=
  match projectee with
  | { mllb_name; mllb_tysc; mllb_add_unit; mllb_def; mllb_attrs; mllb_meta;
      print_typ;_} -> mllb_tysc
let __proj__Mkmllb__item__mllb_add_unit (projectee : mllb) : Prims.bool=
  match projectee with
  | { mllb_name; mllb_tysc; mllb_add_unit; mllb_def; mllb_attrs; mllb_meta;
      print_typ;_} -> mllb_add_unit
let __proj__Mkmllb__item__mllb_def (projectee : mllb) : mlexpr=
  match projectee with
  | { mllb_name; mllb_tysc; mllb_add_unit; mllb_def; mllb_attrs; mllb_meta;
      print_typ;_} -> mllb_def
let __proj__Mkmllb__item__mllb_attrs (projectee : mllb) : mlexpr Prims.list=
  match projectee with
  | { mllb_name; mllb_tysc; mllb_add_unit; mllb_def; mllb_attrs; mllb_meta;
      print_typ;_} -> mllb_attrs
let __proj__Mkmllb__item__mllb_meta (projectee : mllb) : metadata=
  match projectee with
  | { mllb_name; mllb_tysc; mllb_add_unit; mllb_def; mllb_attrs; mllb_meta;
      print_typ;_} -> mllb_meta
let __proj__Mkmllb__item__print_typ (projectee : mllb) : Prims.bool=
  match projectee with
  | { mllb_name; mllb_tysc; mllb_add_unit; mllb_def; mllb_attrs; mllb_meta;
      print_typ;_} -> print_typ
let __proj__Mkty_param__item__ty_param_name (projectee : ty_param) : 
  mlident=
  match projectee with | { ty_param_name; ty_param_attrs;_} -> ty_param_name
let __proj__Mkty_param__item__ty_param_attrs (projectee : ty_param) :
  mlexpr Prims.list=
  match projectee with | { ty_param_name; ty_param_attrs;_} -> ty_param_attrs
type mlbranch = (mlpattern * mlexpr FStar_Pervasives_Native.option * mlexpr)
type mlletbinding = (mlletflavor * mllb Prims.list)
type mlattribute = mlexpr
type mltyscheme = (ty_param Prims.list * mlty)
type mltybody =
  | MLTD_Abbrev of mlty 
  | MLTD_Record of (mlsymbol * mlty) Prims.list 
  | MLTD_DType of (mlsymbol * (mlsymbol * mlty) Prims.list) Prims.list 
let uu___is_MLTD_Abbrev (projectee : mltybody) : Prims.bool=
  match projectee with | MLTD_Abbrev _0 -> true | uu___ -> false
let __proj__MLTD_Abbrev__item___0 (projectee : mltybody) : mlty=
  match projectee with | MLTD_Abbrev _0 -> _0
let uu___is_MLTD_Record (projectee : mltybody) : Prims.bool=
  match projectee with | MLTD_Record _0 -> true | uu___ -> false
let __proj__MLTD_Record__item___0 (projectee : mltybody) :
  (mlsymbol * mlty) Prims.list= match projectee with | MLTD_Record _0 -> _0
let uu___is_MLTD_DType (projectee : mltybody) : Prims.bool=
  match projectee with | MLTD_DType _0 -> true | uu___ -> false
let __proj__MLTD_DType__item___0 (projectee : mltybody) :
  (mlsymbol * (mlsymbol * mlty) Prims.list) Prims.list=
  match projectee with | MLTD_DType _0 -> _0
type one_mltydecl =
  {
  tydecl_assumed: Prims.bool ;
  tydecl_name: mlsymbol ;
  tydecl_ignored: mlsymbol FStar_Pervasives_Native.option ;
  tydecl_parameters: ty_param Prims.list ;
  tydecl_meta: metadata ;
  tydecl_defn: mltybody FStar_Pervasives_Native.option }
let __proj__Mkone_mltydecl__item__tydecl_assumed (projectee : one_mltydecl) :
  Prims.bool=
  match projectee with
  | { tydecl_assumed; tydecl_name; tydecl_ignored; tydecl_parameters;
      tydecl_meta; tydecl_defn;_} -> tydecl_assumed
let __proj__Mkone_mltydecl__item__tydecl_name (projectee : one_mltydecl) :
  mlsymbol=
  match projectee with
  | { tydecl_assumed; tydecl_name; tydecl_ignored; tydecl_parameters;
      tydecl_meta; tydecl_defn;_} -> tydecl_name
let __proj__Mkone_mltydecl__item__tydecl_ignored (projectee : one_mltydecl) :
  mlsymbol FStar_Pervasives_Native.option=
  match projectee with
  | { tydecl_assumed; tydecl_name; tydecl_ignored; tydecl_parameters;
      tydecl_meta; tydecl_defn;_} -> tydecl_ignored
let __proj__Mkone_mltydecl__item__tydecl_parameters
  (projectee : one_mltydecl) : ty_param Prims.list=
  match projectee with
  | { tydecl_assumed; tydecl_name; tydecl_ignored; tydecl_parameters;
      tydecl_meta; tydecl_defn;_} -> tydecl_parameters
let __proj__Mkone_mltydecl__item__tydecl_meta (projectee : one_mltydecl) :
  metadata=
  match projectee with
  | { tydecl_assumed; tydecl_name; tydecl_ignored; tydecl_parameters;
      tydecl_meta; tydecl_defn;_} -> tydecl_meta
let __proj__Mkone_mltydecl__item__tydecl_defn (projectee : one_mltydecl) :
  mltybody FStar_Pervasives_Native.option=
  match projectee with
  | { tydecl_assumed; tydecl_name; tydecl_ignored; tydecl_parameters;
      tydecl_meta; tydecl_defn;_} -> tydecl_defn
type mltydecl = one_mltydecl Prims.list
type mlmodule1' =
  | MLM_Ty of mltydecl 
  | MLM_Let of mlletbinding 
  | MLM_Exn of (mlsymbol * (mlsymbol * mlty) Prims.list) 
  | MLM_Top of mlexpr 
  | MLM_Loc of mlloc 
let uu___is_MLM_Ty (projectee : mlmodule1') : Prims.bool=
  match projectee with | MLM_Ty _0 -> true | uu___ -> false
let __proj__MLM_Ty__item___0 (projectee : mlmodule1') : mltydecl=
  match projectee with | MLM_Ty _0 -> _0
let uu___is_MLM_Let (projectee : mlmodule1') : Prims.bool=
  match projectee with | MLM_Let _0 -> true | uu___ -> false
let __proj__MLM_Let__item___0 (projectee : mlmodule1') : mlletbinding=
  match projectee with | MLM_Let _0 -> _0
let uu___is_MLM_Exn (projectee : mlmodule1') : Prims.bool=
  match projectee with | MLM_Exn _0 -> true | uu___ -> false
let __proj__MLM_Exn__item___0 (projectee : mlmodule1') :
  (mlsymbol * (mlsymbol * mlty) Prims.list)=
  match projectee with | MLM_Exn _0 -> _0
let uu___is_MLM_Top (projectee : mlmodule1') : Prims.bool=
  match projectee with | MLM_Top _0 -> true | uu___ -> false
let __proj__MLM_Top__item___0 (projectee : mlmodule1') : mlexpr=
  match projectee with | MLM_Top _0 -> _0
let uu___is_MLM_Loc (projectee : mlmodule1') : Prims.bool=
  match projectee with | MLM_Loc _0 -> true | uu___ -> false
let __proj__MLM_Loc__item___0 (projectee : mlmodule1') : mlloc=
  match projectee with | MLM_Loc _0 -> _0
type mlmodule1 =
  {
  mlmodule1_m: mlmodule1' ;
  mlmodule1_attrs: mlattribute Prims.list }
let __proj__Mkmlmodule1__item__mlmodule1_m (projectee : mlmodule1) :
  mlmodule1'=
  match projectee with | { mlmodule1_m; mlmodule1_attrs;_} -> mlmodule1_m
let __proj__Mkmlmodule1__item__mlmodule1_attrs (projectee : mlmodule1) :
  mlattribute Prims.list=
  match projectee with | { mlmodule1_m; mlmodule1_attrs;_} -> mlmodule1_attrs
let mk_mlmodule1 (m : mlmodule1') : mlmodule1=
  { mlmodule1_m = m; mlmodule1_attrs = [] }
let mk_mlmodule1_with_attrs (m : mlmodule1') (attrs : mlattribute Prims.list)
  : mlmodule1= { mlmodule1_m = m; mlmodule1_attrs = attrs }
type mlmodulebody = mlmodule1 Prims.list
type mlsig1 =
  | MLS_Mod of (mlsymbol * mlsig1 Prims.list) 
  | MLS_Ty of mltydecl 
  | MLS_Val of (mlsymbol * mltyscheme) 
  | MLS_Exn of (mlsymbol * mlty Prims.list) 
let uu___is_MLS_Mod (projectee : mlsig1) : Prims.bool=
  match projectee with | MLS_Mod _0 -> true | uu___ -> false
let __proj__MLS_Mod__item___0 (projectee : mlsig1) :
  (mlsymbol * mlsig1 Prims.list)= match projectee with | MLS_Mod _0 -> _0
let uu___is_MLS_Ty (projectee : mlsig1) : Prims.bool=
  match projectee with | MLS_Ty _0 -> true | uu___ -> false
let __proj__MLS_Ty__item___0 (projectee : mlsig1) : mltydecl=
  match projectee with | MLS_Ty _0 -> _0
let uu___is_MLS_Val (projectee : mlsig1) : Prims.bool=
  match projectee with | MLS_Val _0 -> true | uu___ -> false
let __proj__MLS_Val__item___0 (projectee : mlsig1) : (mlsymbol * mltyscheme)=
  match projectee with | MLS_Val _0 -> _0
let uu___is_MLS_Exn (projectee : mlsig1) : Prims.bool=
  match projectee with | MLS_Exn _0 -> true | uu___ -> false
let __proj__MLS_Exn__item___0 (projectee : mlsig1) :
  (mlsymbol * mlty Prims.list)= match projectee with | MLS_Exn _0 -> _0
type mlsig = mlsig1 Prims.list
let with_ty_loc (t : mlty) (e : mlexpr') (l : mlloc) : mlexpr=
  { expr = e; mlty = t; loc = l }
let with_ty (t : mlty) (e : mlexpr') : mlexpr= with_ty_loc t e dummy_loc
type mlmodule =
  (mlpath * (mlsig * mlmodulebody) FStar_Pervasives_Native.option)
let ml_unit_ty : mlty= MLTY_Erased
let ml_bool_ty : mlty= MLTY_Named ([], (["Prims"], "bool"))
let ml_int_ty : mlty= MLTY_Named ([], (["Prims"], "int"))
let ml_string_ty : mlty= MLTY_Named ([], (["Prims"], "string"))
let ml_unit : mlexpr= with_ty ml_unit_ty (MLE_Const MLC_Unit)
let apply_obj_repr (x : mlexpr) (t : mlty) : mlexpr=
  let repr_name =
    let uu___ =
      let uu___1 = FStarC_Options.codegen () in
      uu___1 = (FStar_Pervasives_Native.Some FStarC_Options.FSharp) in
    if uu___ then MLE_Name ([], "box") else MLE_Name (["Obj"], "repr") in
  let obj_repr = with_ty (MLTY_Fun (t, E_PURE, MLTY_Top)) repr_name in
  with_ty_loc MLTY_Top (MLE_App (obj_repr, [x])) x.loc
let ty_param_names (tys : ty_param Prims.list) : Prims.string Prims.list=
  FStarC_List.map
    (fun uu___ ->
       match uu___ with
       | { ty_param_name; ty_param_attrs = uu___1;_} -> ty_param_name) tys
let push_unit (eff : e_tag) (ts : mltyscheme) : mltyscheme=
  let uu___ = ts in
  match uu___ with | (vs, ty) -> (vs, (MLTY_Fun (ml_unit_ty, eff, ty)))
let pop_unit (ts : mltyscheme) : (e_tag * mltyscheme)=
  let uu___ = ts in
  match uu___ with
  | (vs, ty) ->
      (match ty with
       | MLTY_Fun (l, eff, t) ->
           if l = ml_unit_ty
           then (eff, (vs, t))
           else failwith "unexpected: pop_unit: domain was not unit"
       | uu___1 -> failwith "unexpected: pop_unit: not a function type")
let ctor' (n : Prims.string) (args : FStar_Pprint.document Prims.list) :
  FStar_Pprint.document=
  FStar_Pprint.nest (Prims.of_int (2))
    (FStar_Pprint.group
       (FStar_Pprint.parens
          (FStar_Pprint.flow (FStar_Pprint.break_ Prims.int_one)
             ((FStar_Pprint.doc_of_string n) :: args))))
let ctor (n : Prims.string) (arg : FStar_Pprint.document) :
  FStar_Pprint.document=
  FStar_Pprint.nest (Prims.of_int (2))
    (FStar_Pprint.group
       (FStar_Pprint.parens
          (FStar_Pprint.op_Hat_Slash_Hat (FStar_Pprint.doc_of_string n) arg)))
let rec mlty_to_doc (t : mlty) : FStar_Pprint.document=
  match t with
  | MLTY_Var v -> FStar_Pprint.doc_of_string v
  | MLTY_Fun (t1, uu___, t2) ->
      let uu___1 =
        let uu___2 = mlty_to_doc t1 in
        let uu___3 =
          let uu___4 = let uu___5 = mlty_to_doc t2 in [uu___5] in
          (FStar_Pprint.doc_of_string "->") :: uu___4 in
        uu___2 :: uu___3 in
      ctor' "<MLTY_Fun>" uu___1
  | MLTY_Named (ts, p) ->
      let uu___ =
        let uu___1 = FStarC_List.map mlty_to_doc ts in
        let uu___2 =
          let uu___3 =
            let uu___4 = string_of_mlpath p in
            FStar_Pprint.doc_of_string uu___4 in
          [uu___3] in
        FStarC_List.op_At uu___1 uu___2 in
      ctor' "<MLTY_Named>" uu___
  | MLTY_Tuple ts ->
      let uu___ =
        FStarC_Pprint.flow_map
          (FStar_Pprint.op_Hat_Hat (FStar_Pprint.doc_of_string " *")
             (FStar_Pprint.break_ Prims.int_one)) mlty_to_doc ts in
      ctor "<MLTY_Tuple>" uu___
  | MLTY_Top -> FStar_Pprint.doc_of_string "MLTY_Top"
  | MLTY_Erased -> FStar_Pprint.doc_of_string "MLTY_Erased"
let mlty_to_string (t : mlty) : Prims.string=
  let uu___ = mlty_to_doc t in FStar_Pprint.render uu___
let mltyscheme_to_doc (tsc : mltyscheme) : FStar_Pprint.document=
  let uu___ =
    let uu___1 =
      let uu___2 =
        let uu___3 = ty_param_names (FStar_Pervasives_Native.fst tsc) in
        FStarC_Pprint.flow_map
          (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma
             (FStar_Pprint.break_ Prims.int_one)) FStar_Pprint.doc_of_string
          uu___3 in
      FStar_Pprint.brackets uu___2 in
    let uu___2 =
      let uu___3 = mlty_to_doc (FStar_Pervasives_Native.snd tsc) in
      FStar_Pprint.op_Hat_Slash_Hat (FStar_Pprint.doc_of_string ",") uu___3 in
    FStar_Pprint.op_Hat_Hat uu___1 uu___2 in
  ctor "<MLTY_Scheme>" uu___
let mltyscheme_to_string (tsc : mltyscheme) : Prims.string=
  let uu___ = mltyscheme_to_doc tsc in FStar_Pprint.render uu___
let pair (a : FStar_Pprint.document) (b : FStar_Pprint.document) :
  FStar_Pprint.document=
  FStar_Pprint.group
    (FStar_Pprint.parens
       (FStar_Pprint.op_Hat_Hat a
          (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.comma b)))
let triple (a : FStar_Pprint.document) (b : FStar_Pprint.document)
  (c : FStar_Pprint.document) : FStar_Pprint.document=
  FStar_Pprint.group
    (FStar_Pprint.parens
       (FStar_Pprint.op_Hat_Hat a
          (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.comma
             (FStar_Pprint.op_Hat_Hat b
                (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.comma c)))))
let ctor2 (n : Prims.string) (a : FStar_Pprint.document)
  (b : FStar_Pprint.document) : FStar_Pprint.document= ctor n (pair a b)
let list_to_doc (xs : 't Prims.list) (f : 't -> FStar_Pprint.document) :
  FStar_Pprint.document=
  let uu___ =
    let uu___1 =
      let uu___2 =
        FStarC_Pprint.flow_map
          (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi
             (FStar_Pprint.break_ Prims.int_one)) f xs in
      FStar_Pprint.brackets uu___2 in
    FStar_Pprint.group uu___1 in
  FStar_Pprint.nest (Prims.of_int (2)) uu___
let option_to_doc (x : 't FStar_Pervasives_Native.option)
  (f : 't -> FStar_Pprint.document) : FStar_Pprint.document=
  match x with
  | FStar_Pervasives_Native.Some x1 ->
      let uu___ =
        let uu___1 = f x1 in
        FStar_Pprint.op_Hat_Slash_Hat (FStar_Pprint.doc_of_string "Some")
          uu___1 in
      FStar_Pprint.group uu___
  | FStar_Pervasives_Native.None -> FStar_Pprint.doc_of_string "None"
let spaced (a : FStar_Pprint.document) : FStar_Pprint.document=
  FStar_Pprint.op_Hat_Hat (FStar_Pprint.break_ Prims.int_one)
    (FStar_Pprint.op_Hat_Hat a (FStar_Pprint.break_ Prims.int_one))
let record (fs : FStar_Pprint.document Prims.list) : FStar_Pprint.document=
  FStar_Pprint.group
    (FStar_Pprint.nest (Prims.of_int (2))
       (FStar_Pprint.braces
          (spaced
             (FStar_Pprint.separate
                (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi
                   (FStar_Pprint.break_ Prims.int_one)) fs))))
let fld (n : Prims.string) (v : FStar_Pprint.document) :
  FStar_Pprint.document=
  FStar_Pprint.group
    (FStar_Pprint.nest (Prims.of_int (2))
       (FStar_Pprint.op_Hat_Slash_Hat
          (FStar_Pprint.doc_of_string (Prims.strcat n " =")) v))
let rec mlexpr_to_doc (e : mlexpr) : FStar_Pprint.document=
  match e.expr with
  | MLE_Const c -> let uu___ = mlconstant_to_doc c in ctor "MLE_Const" uu___
  | MLE_Var x -> ctor "MLE_Var" (FStar_Pprint.doc_of_string x)
  | MLE_Name (p, x) ->
      ctor2 "MLE_Name"
        (FStar_Pprint.doc_of_string (FStarC_String.concat "." p))
        (FStar_Pprint.doc_of_string x)
  | MLE_Let (lbs, e1) ->
      let uu___ = mlletbinding_to_doc lbs in
      let uu___1 = mlexpr_to_doc e1 in ctor2 "MLE_Let" uu___ uu___1
  | MLE_App (e1, es) ->
      let uu___ = mlexpr_to_doc e1 in
      let uu___1 = list_to_doc es mlexpr_to_doc in
      ctor2 "MLE_App" uu___ uu___1
  | MLE_TApp (e1, ts) ->
      let uu___ = mlexpr_to_doc e1 in
      let uu___1 = list_to_doc ts mlty_to_doc in
      ctor2 "MLE_TApp" uu___ uu___1
  | MLE_Fun (bs, e1) ->
      let uu___ =
        list_to_doc bs
          (fun b ->
             let uu___1 = mlty_to_doc b.mlbinder_ty in
             pair (FStar_Pprint.doc_of_string b.mlbinder_name) uu___1) in
      let uu___1 = mlexpr_to_doc e1 in ctor2 "MLE_Fun" uu___ uu___1
  | MLE_Match (e1, bs) ->
      let uu___ = mlexpr_to_doc e1 in
      let uu___1 = list_to_doc bs mlbranch_to_doc in
      ctor2 "MLE_Match" uu___ uu___1
  | MLE_Coerce (e1, t1, t2) ->
      let uu___ =
        let uu___1 = mlexpr_to_doc e1 in
        let uu___2 = mlty_to_doc t1 in
        let uu___3 = mlty_to_doc t2 in triple uu___1 uu___2 uu___3 in
      ctor "MLE_Coerce" uu___
  | MLE_CTor (p, es) ->
      let uu___ =
        let uu___1 = string_of_mlpath p in FStar_Pprint.doc_of_string uu___1 in
      let uu___1 = list_to_doc es mlexpr_to_doc in
      ctor2 "MLE_CTor" uu___ uu___1
  | MLE_Seq es ->
      let uu___ = list_to_doc es mlexpr_to_doc in ctor "MLE_Seq" uu___
  | MLE_Tuple es ->
      let uu___ = list_to_doc es mlexpr_to_doc in ctor "MLE_Tuple" uu___
  | MLE_Record (p, n, es) ->
      let uu___ =
        list_to_doc (FStarC_List.op_At p [n]) FStar_Pprint.doc_of_string in
      let uu___1 =
        list_to_doc es
          (fun uu___2 ->
             match uu___2 with
             | (x, e1) ->
                 let uu___3 = mlexpr_to_doc e1 in
                 pair (FStar_Pprint.doc_of_string x) uu___3) in
      ctor2 "MLE_Record" uu___ uu___1
  | MLE_Proj (e1, p) ->
      let uu___ = mlexpr_to_doc e1 in
      let uu___1 =
        let uu___2 = string_of_mlpath p in FStar_Pprint.doc_of_string uu___2 in
      ctor2 "MLE_Proj" uu___ uu___1
  | MLE_If (e1, e2, e3) ->
      let uu___ =
        let uu___1 = mlexpr_to_doc e1 in
        let uu___2 = mlexpr_to_doc e2 in
        let uu___3 = option_to_doc e3 mlexpr_to_doc in
        triple uu___1 uu___2 uu___3 in
      ctor "MLE_If" uu___
  | MLE_Raise (p, es) ->
      let uu___ =
        let uu___1 = string_of_mlpath p in FStar_Pprint.doc_of_string uu___1 in
      let uu___1 = list_to_doc es mlexpr_to_doc in
      ctor2 "MLE_Raise" uu___ uu___1
  | MLE_Try (e1, bs) ->
      let uu___ = mlexpr_to_doc e1 in
      let uu___1 = list_to_doc bs mlbranch_to_doc in
      ctor2 "MLE_Try" uu___ uu___1
and mlbranch_to_doc
  (uu___ : (mlpattern * mlexpr FStar_Pervasives_Native.option * mlexpr)) :
  FStar_Pprint.document=
  match uu___ with
  | (p, e1, e2) ->
      let uu___1 = mlpattern_to_doc p in
      let uu___2 = option_to_doc e1 mlexpr_to_doc in
      let uu___3 = mlexpr_to_doc e2 in triple uu___1 uu___2 uu___3
and mlletbinding_to_doc (lbs : (mlletflavor * mllb Prims.list)) :
  FStar_Pprint.document=
  let uu___ =
    let uu___1 =
      let uu___2 =
        list_to_doc (FStar_Pervasives_Native.__proj__Mktuple2__item___2 lbs)
          mllb_to_doc in
      FStar_Pprint.op_Hat_Hat (FStar_Pprint.doc_of_string ", ") uu___2 in
    FStar_Pprint.op_Hat_Hat
      (FStar_Pprint.doc_of_string
         (match FStar_Pervasives_Native.__proj__Mktuple2__item___1 lbs with
          | Rec -> "Rec"
          | NonRec -> "NonRec")) uu___1 in
  FStar_Pprint.parens uu___
and mllb_to_doc (lb : mllb) : FStar_Pprint.document=
  let uu___ =
    let uu___1 =
      let uu___2 =
        let uu___3 = list_to_doc lb.mllb_attrs mlexpr_to_doc in
        fld "mllb_attrs" uu___3 in
      let uu___3 =
        let uu___4 =
          let uu___5 =
            option_to_doc lb.mllb_tysc
              (fun uu___6 -> match uu___6 with | (uu___7, t) -> mlty_to_doc t) in
          fld "mllb_tysc" uu___5 in
        let uu___5 =
          let uu___6 =
            let uu___7 =
              FStarC_Class_PP.pp FStarC_Class_PP.pp_bool lb.mllb_add_unit in
            fld "mllb_add_unit" uu___7 in
          let uu___7 =
            let uu___8 =
              let uu___9 = mlexpr_to_doc lb.mllb_def in fld "mllb_def" uu___9 in
            [uu___8] in
          uu___6 :: uu___7 in
        uu___4 :: uu___5 in
      uu___2 :: uu___3 in
    (fld "mllb_name" (FStar_Pprint.doc_of_string lb.mllb_name)) :: uu___1 in
  record uu___
and mlconstant_to_doc (mlc : mlconstant) : FStar_Pprint.document=
  match mlc with
  | MLC_Unit -> FStar_Pprint.doc_of_string "MLC_Unit"
  | MLC_Bool b ->
      let uu___ = FStarC_Class_PP.pp FStarC_Class_PP.pp_bool b in
      ctor "MLC_Bool" uu___
  | MLC_Int (s, FStar_Pervasives_Native.None) ->
      ctor "MLC_Int" (FStar_Pprint.doc_of_string s)
  | MLC_Int (s, FStar_Pervasives_Native.Some (s1, s2)) ->
      ctor "MLC_Int"
        (triple (FStar_Pprint.doc_of_string s) FStar_Pprint.underscore
           FStar_Pprint.underscore)
  | MLC_Float f -> ctor "MLC_Float" FStar_Pprint.underscore
  | MLC_Char c -> ctor "MLC_Char" FStar_Pprint.underscore
  | MLC_String s -> ctor "MLC_String" (FStar_Pprint.doc_of_string s)
and mlpattern_to_doc (mlp : mlpattern) : FStar_Pprint.document=
  match mlp with
  | MLP_Wild -> FStar_Pprint.doc_of_string "MLP_Wild"
  | MLP_Const c -> let uu___ = mlconstant_to_doc c in ctor "MLP_Const" uu___
  | MLP_Var x -> ctor "MLP_Var" (FStar_Pprint.doc_of_string x)
  | MLP_CTor (p, ps) ->
      let uu___ =
        let uu___1 = string_of_mlpath p in FStar_Pprint.doc_of_string uu___1 in
      let uu___1 = list_to_doc ps mlpattern_to_doc in
      ctor2 "MLP_CTor" uu___ uu___1
  | MLP_Branch ps ->
      let uu___ = list_to_doc ps mlpattern_to_doc in ctor "MLP_Branch" uu___
  | MLP_Record (path, fields) ->
      let uu___ =
        list_to_doc fields
          (fun uu___1 ->
             match uu___1 with
             | (x, p) ->
                 let uu___2 = mlpattern_to_doc p in
                 pair (FStar_Pprint.doc_of_string x) uu___2) in
      ctor2 "MLP_Record"
        (FStar_Pprint.doc_of_string (FStarC_String.concat "." path)) uu___
  | MLP_Tuple ps ->
      let uu___ = list_to_doc ps mlpattern_to_doc in ctor "MLP_Tuple" uu___
let mlbranch_to_string (b : mlbranch) : Prims.string=
  let uu___ = mlbranch_to_doc b in FStar_Pprint.render uu___
let mlletbinding_to_string (lb : mlletbinding) : Prims.string=
  let uu___ = mlletbinding_to_doc lb in FStar_Pprint.render uu___
let mllb_to_string (lb : mllb) : Prims.string=
  let uu___ = mllb_to_doc lb in FStar_Pprint.render uu___
let mlpattern_to_string (p : mlpattern) : Prims.string=
  let uu___ = mlpattern_to_doc p in FStar_Pprint.render uu___
let mlconstant_to_string (c : mlconstant) : Prims.string=
  let uu___ = mlconstant_to_doc c in FStar_Pprint.render uu___
let mlexpr_to_string (e : mlexpr) : Prims.string=
  let uu___ = mlexpr_to_doc e in FStar_Pprint.render uu___
let mltybody_to_doc (d : mltybody) : FStar_Pprint.document=
  match d with
  | MLTD_Abbrev mlty1 ->
      let uu___ = mlty_to_doc mlty1 in ctor "MLTD_Abbrev" uu___
  | MLTD_Record l ->
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 =
              let uu___4 =
                FStarC_Pprint.flow_map
                  (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi
                     (FStar_Pprint.break_ Prims.int_one))
                  (fun uu___5 ->
                     match uu___5 with
                     | (x, t) ->
                         let uu___6 = mlty_to_doc t in
                         pair (FStar_Pprint.doc_of_string x) uu___6) l in
              spaced uu___4 in
            FStar_Pprint.braces uu___3 in
          FStar_Pprint.nest (Prims.of_int (2)) uu___2 in
        FStar_Pprint.group uu___1 in
      ctor "MLTD_Record" uu___
  | MLTD_DType l ->
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 =
              let uu___4 =
                FStarC_Pprint.flow_map
                  (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi
                     (FStar_Pprint.break_ Prims.int_one))
                  (fun uu___5 ->
                     match uu___5 with
                     | (x, l1) ->
                         let uu___6 =
                           list_to_doc l1
                             (fun uu___7 ->
                                match uu___7 with
                                | (x1, t) ->
                                    let uu___8 = mlty_to_doc t in
                                    pair (FStar_Pprint.doc_of_string x1)
                                      uu___8) in
                         pair (FStar_Pprint.doc_of_string x) uu___6) l in
              spaced uu___4 in
            FStar_Pprint.brackets uu___3 in
          FStar_Pprint.nest (Prims.of_int (2)) uu___2 in
        FStar_Pprint.group uu___1 in
      ctor "MLTD_DType" uu___
let mltybody_to_string (d : mltybody) : Prims.string=
  let uu___ = mltybody_to_doc d in FStar_Pprint.render uu___
let one_mltydecl_to_doc (d : one_mltydecl) : FStar_Pprint.document=
  let uu___ =
    let uu___1 =
      let uu___2 =
        let uu___3 =
          let uu___4 =
            let uu___5 = ty_param_names d.tydecl_parameters in
            FStarC_String.concat "," uu___5 in
          FStar_Pprint.doc_of_string uu___4 in
        fld "tydecl_parameters" uu___3 in
      let uu___3 =
        let uu___4 =
          let uu___5 = option_to_doc d.tydecl_defn mltybody_to_doc in
          fld "tydecl_defn" uu___5 in
        [uu___4] in
      uu___2 :: uu___3 in
    (fld "tydecl_name" (FStar_Pprint.doc_of_string d.tydecl_name)) :: uu___1 in
  record uu___
let one_mltydecl_to_string (d : one_mltydecl) : Prims.string=
  let uu___ = one_mltydecl_to_doc d in FStar_Pprint.render uu___
let mlmodule1_to_doc (m : mlmodule1) : FStar_Pprint.document=
  let uu___ =
    match m.mlmodule1_m with
    | MLM_Ty d ->
        let uu___1 = list_to_doc d one_mltydecl_to_doc in
        FStar_Pprint.op_Hat_Hat (FStar_Pprint.doc_of_string "MLM_Ty ") uu___1
    | MLM_Let l ->
        let uu___1 = mlletbinding_to_doc l in
        FStar_Pprint.op_Hat_Hat (FStar_Pprint.doc_of_string "MLM_Let ")
          uu___1
    | MLM_Exn (s, l) ->
        let uu___1 =
          let uu___2 =
            list_to_doc l
              (fun uu___3 ->
                 match uu___3 with
                 | (x, t) ->
                     let uu___4 = mlty_to_doc t in
                     pair (FStar_Pprint.doc_of_string x) uu___4) in
          pair (FStar_Pprint.doc_of_string s) uu___2 in
        FStar_Pprint.op_Hat_Slash_Hat (FStar_Pprint.doc_of_string "MLM_Exn")
          uu___1
    | MLM_Top e ->
        let uu___1 = mlexpr_to_doc e in
        FStar_Pprint.op_Hat_Slash_Hat (FStar_Pprint.doc_of_string "MLM_Top")
          uu___1
    | MLM_Loc _mlloc -> FStar_Pprint.doc_of_string "MLM_Loc" in
  FStar_Pprint.group uu___
let mlmodule1_to_string (m : mlmodule1) : Prims.string=
  let uu___ = mlmodule1_to_doc m in FStar_Pprint.render uu___
let mlmodulebody_to_doc (m : mlmodulebody) : FStar_Pprint.document=
  let uu___ =
    let uu___1 =
      let uu___2 =
        FStarC_Pprint.separate_map
          (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi
             (FStar_Pprint.break_ Prims.int_one)) mlmodule1_to_doc m in
      spaced uu___2 in
    FStar_Pprint.brackets uu___1 in
  FStar_Pprint.group uu___
let mlmodulebody_to_string (m : mlmodulebody) : Prims.string=
  let uu___ = mlmodulebody_to_doc m in FStar_Pprint.render uu___
let showable_mlty : mlty FStarC_Class_Show.showable=
  { FStarC_Class_Show.show = mlty_to_string }
let showable_mlconstant : mlconstant FStarC_Class_Show.showable=
  { FStarC_Class_Show.show = mlconstant_to_string }
let showable_mlexpr : mlexpr FStarC_Class_Show.showable=
  { FStarC_Class_Show.show = mlexpr_to_string }
let showable_mlmodule1 : mlmodule1 FStarC_Class_Show.showable=
  { FStarC_Class_Show.show = mlmodule1_to_string }
let showable_mlmodulebody : mlmodulebody FStarC_Class_Show.showable=
  { FStarC_Class_Show.show = mlmodulebody_to_string }
let pp_mlty : mlty FStarC_Class_PP.pretty=
  { FStarC_Class_PP.pp = mlty_to_doc }
let pp_mlconstant : mlconstant FStarC_Class_PP.pretty=
  { FStarC_Class_PP.pp = mlconstant_to_doc }
let pp_mlexpr : mlexpr FStarC_Class_PP.pretty=
  { FStarC_Class_PP.pp = mlexpr_to_doc }
let pp_mlmodule1 : mlmodule1 FStarC_Class_PP.pretty=
  { FStarC_Class_PP.pp = mlmodule1_to_doc }
let pp_mlmodulebody : mlmodulebody FStarC_Class_PP.pretty=
  { FStarC_Class_PP.pp = mlmodulebody_to_doc }
