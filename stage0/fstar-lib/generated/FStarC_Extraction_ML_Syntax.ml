open Prims
type mlsymbol = Prims.string
type mlident = mlsymbol
type mlpath = (mlsymbol Prims.list * mlsymbol)
let (krml_keywords : Prims.string Prims.list) = []
let (ocamlkeywords : Prims.string Prims.list) =
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
let (fsharpkeywords : Prims.string Prims.list) =
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
let (string_of_mlpath : mlpath -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | (p, s) ->
        FStarC_Compiler_String.concat "." (FStarC_Compiler_List.op_At p [s])
type mlidents = mlident Prims.list
type mlsymbols = mlsymbol Prims.list
type e_tag =
  | E_PURE 
  | E_ERASABLE 
  | E_IMPURE 
let (uu___is_E_PURE : e_tag -> Prims.bool) =
  fun projectee -> match projectee with | E_PURE -> true | uu___ -> false
let (uu___is_E_ERASABLE : e_tag -> Prims.bool) =
  fun projectee -> match projectee with | E_ERASABLE -> true | uu___ -> false
let (uu___is_E_IMPURE : e_tag -> Prims.bool) =
  fun projectee -> match projectee with | E_IMPURE -> true | uu___ -> false
type mlloc = (Prims.int * Prims.string)
let (dummy_loc : mlloc) = (Prims.int_zero, "")
type mlty =
  | MLTY_Var of mlident 
  | MLTY_Fun of (mlty * e_tag * mlty) 
  | MLTY_Named of (mlty Prims.list * mlpath) 
  | MLTY_Tuple of mlty Prims.list 
  | MLTY_Top 
  | MLTY_Erased 
let (uu___is_MLTY_Var : mlty -> Prims.bool) =
  fun projectee ->
    match projectee with | MLTY_Var _0 -> true | uu___ -> false
let (__proj__MLTY_Var__item___0 : mlty -> mlident) =
  fun projectee -> match projectee with | MLTY_Var _0 -> _0
let (uu___is_MLTY_Fun : mlty -> Prims.bool) =
  fun projectee ->
    match projectee with | MLTY_Fun _0 -> true | uu___ -> false
let (__proj__MLTY_Fun__item___0 : mlty -> (mlty * e_tag * mlty)) =
  fun projectee -> match projectee with | MLTY_Fun _0 -> _0
let (uu___is_MLTY_Named : mlty -> Prims.bool) =
  fun projectee ->
    match projectee with | MLTY_Named _0 -> true | uu___ -> false
let (__proj__MLTY_Named__item___0 : mlty -> (mlty Prims.list * mlpath)) =
  fun projectee -> match projectee with | MLTY_Named _0 -> _0
let (uu___is_MLTY_Tuple : mlty -> Prims.bool) =
  fun projectee ->
    match projectee with | MLTY_Tuple _0 -> true | uu___ -> false
let (__proj__MLTY_Tuple__item___0 : mlty -> mlty Prims.list) =
  fun projectee -> match projectee with | MLTY_Tuple _0 -> _0
let (uu___is_MLTY_Top : mlty -> Prims.bool) =
  fun projectee -> match projectee with | MLTY_Top -> true | uu___ -> false
let (uu___is_MLTY_Erased : mlty -> Prims.bool) =
  fun projectee ->
    match projectee with | MLTY_Erased -> true | uu___ -> false
type mlconstant =
  | MLC_Unit 
  | MLC_Bool of Prims.bool 
  | MLC_Int of (Prims.string * (FStarC_Const.signedness * FStarC_Const.width)
  FStar_Pervasives_Native.option) 
  | MLC_Float of FStarC_BaseTypes.float 
  | MLC_Char of FStarC_BaseTypes.char 
  | MLC_String of Prims.string 
  | MLC_Bytes of FStarC_BaseTypes.byte Prims.array 
let (uu___is_MLC_Unit : mlconstant -> Prims.bool) =
  fun projectee -> match projectee with | MLC_Unit -> true | uu___ -> false
let (uu___is_MLC_Bool : mlconstant -> Prims.bool) =
  fun projectee ->
    match projectee with | MLC_Bool _0 -> true | uu___ -> false
let (__proj__MLC_Bool__item___0 : mlconstant -> Prims.bool) =
  fun projectee -> match projectee with | MLC_Bool _0 -> _0
let (uu___is_MLC_Int : mlconstant -> Prims.bool) =
  fun projectee -> match projectee with | MLC_Int _0 -> true | uu___ -> false
let (__proj__MLC_Int__item___0 :
  mlconstant ->
    (Prims.string * (FStarC_Const.signedness * FStarC_Const.width)
      FStar_Pervasives_Native.option))
  = fun projectee -> match projectee with | MLC_Int _0 -> _0
let (uu___is_MLC_Float : mlconstant -> Prims.bool) =
  fun projectee ->
    match projectee with | MLC_Float _0 -> true | uu___ -> false
let (__proj__MLC_Float__item___0 : mlconstant -> FStarC_BaseTypes.float) =
  fun projectee -> match projectee with | MLC_Float _0 -> _0
let (uu___is_MLC_Char : mlconstant -> Prims.bool) =
  fun projectee ->
    match projectee with | MLC_Char _0 -> true | uu___ -> false
let (__proj__MLC_Char__item___0 : mlconstant -> FStarC_BaseTypes.char) =
  fun projectee -> match projectee with | MLC_Char _0 -> _0
let (uu___is_MLC_String : mlconstant -> Prims.bool) =
  fun projectee ->
    match projectee with | MLC_String _0 -> true | uu___ -> false
let (__proj__MLC_String__item___0 : mlconstant -> Prims.string) =
  fun projectee -> match projectee with | MLC_String _0 -> _0
let (uu___is_MLC_Bytes : mlconstant -> Prims.bool) =
  fun projectee ->
    match projectee with | MLC_Bytes _0 -> true | uu___ -> false
let (__proj__MLC_Bytes__item___0 :
  mlconstant -> FStarC_BaseTypes.byte Prims.array) =
  fun projectee -> match projectee with | MLC_Bytes _0 -> _0
type mlpattern =
  | MLP_Wild 
  | MLP_Const of mlconstant 
  | MLP_Var of mlident 
  | MLP_CTor of (mlpath * mlpattern Prims.list) 
  | MLP_Branch of mlpattern Prims.list 
  | MLP_Record of (mlsymbol Prims.list * (mlsymbol * mlpattern) Prims.list) 
  | MLP_Tuple of mlpattern Prims.list 
let (uu___is_MLP_Wild : mlpattern -> Prims.bool) =
  fun projectee -> match projectee with | MLP_Wild -> true | uu___ -> false
let (uu___is_MLP_Const : mlpattern -> Prims.bool) =
  fun projectee ->
    match projectee with | MLP_Const _0 -> true | uu___ -> false
let (__proj__MLP_Const__item___0 : mlpattern -> mlconstant) =
  fun projectee -> match projectee with | MLP_Const _0 -> _0
let (uu___is_MLP_Var : mlpattern -> Prims.bool) =
  fun projectee -> match projectee with | MLP_Var _0 -> true | uu___ -> false
let (__proj__MLP_Var__item___0 : mlpattern -> mlident) =
  fun projectee -> match projectee with | MLP_Var _0 -> _0
let (uu___is_MLP_CTor : mlpattern -> Prims.bool) =
  fun projectee ->
    match projectee with | MLP_CTor _0 -> true | uu___ -> false
let (__proj__MLP_CTor__item___0 :
  mlpattern -> (mlpath * mlpattern Prims.list)) =
  fun projectee -> match projectee with | MLP_CTor _0 -> _0
let (uu___is_MLP_Branch : mlpattern -> Prims.bool) =
  fun projectee ->
    match projectee with | MLP_Branch _0 -> true | uu___ -> false
let (__proj__MLP_Branch__item___0 : mlpattern -> mlpattern Prims.list) =
  fun projectee -> match projectee with | MLP_Branch _0 -> _0
let (uu___is_MLP_Record : mlpattern -> Prims.bool) =
  fun projectee ->
    match projectee with | MLP_Record _0 -> true | uu___ -> false
let (__proj__MLP_Record__item___0 :
  mlpattern -> (mlsymbol Prims.list * (mlsymbol * mlpattern) Prims.list)) =
  fun projectee -> match projectee with | MLP_Record _0 -> _0
let (uu___is_MLP_Tuple : mlpattern -> Prims.bool) =
  fun projectee ->
    match projectee with | MLP_Tuple _0 -> true | uu___ -> false
let (__proj__MLP_Tuple__item___0 : mlpattern -> mlpattern Prims.list) =
  fun projectee -> match projectee with | MLP_Tuple _0 -> _0
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
  FStarC_Compiler_Range_Type.range) 
  | HasValDecl of FStarC_Compiler_Range_Type.range 
  | CNoInline 
let (uu___is_Mutable : meta -> Prims.bool) =
  fun projectee -> match projectee with | Mutable -> true | uu___ -> false
let (uu___is_Assumed : meta -> Prims.bool) =
  fun projectee -> match projectee with | Assumed -> true | uu___ -> false
let (uu___is_Private : meta -> Prims.bool) =
  fun projectee -> match projectee with | Private -> true | uu___ -> false
let (uu___is_NoExtract : meta -> Prims.bool) =
  fun projectee -> match projectee with | NoExtract -> true | uu___ -> false
let (uu___is_CInline : meta -> Prims.bool) =
  fun projectee -> match projectee with | CInline -> true | uu___ -> false
let (uu___is_Substitute : meta -> Prims.bool) =
  fun projectee -> match projectee with | Substitute -> true | uu___ -> false
let (uu___is_GCType : meta -> Prims.bool) =
  fun projectee -> match projectee with | GCType -> true | uu___ -> false
let (uu___is_PpxDerivingShow : meta -> Prims.bool) =
  fun projectee ->
    match projectee with | PpxDerivingShow -> true | uu___ -> false
let (uu___is_PpxDerivingShowConstant : meta -> Prims.bool) =
  fun projectee ->
    match projectee with
    | PpxDerivingShowConstant _0 -> true
    | uu___ -> false
let (__proj__PpxDerivingShowConstant__item___0 : meta -> Prims.string) =
  fun projectee -> match projectee with | PpxDerivingShowConstant _0 -> _0
let (uu___is_PpxDerivingYoJson : meta -> Prims.bool) =
  fun projectee ->
    match projectee with | PpxDerivingYoJson -> true | uu___ -> false
let (uu___is_Comment : meta -> Prims.bool) =
  fun projectee -> match projectee with | Comment _0 -> true | uu___ -> false
let (__proj__Comment__item___0 : meta -> Prims.string) =
  fun projectee -> match projectee with | Comment _0 -> _0
let (uu___is_StackInline : meta -> Prims.bool) =
  fun projectee ->
    match projectee with | StackInline -> true | uu___ -> false
let (uu___is_CPrologue : meta -> Prims.bool) =
  fun projectee ->
    match projectee with | CPrologue _0 -> true | uu___ -> false
let (__proj__CPrologue__item___0 : meta -> Prims.string) =
  fun projectee -> match projectee with | CPrologue _0 -> _0
let (uu___is_CEpilogue : meta -> Prims.bool) =
  fun projectee ->
    match projectee with | CEpilogue _0 -> true | uu___ -> false
let (__proj__CEpilogue__item___0 : meta -> Prims.string) =
  fun projectee -> match projectee with | CEpilogue _0 -> _0
let (uu___is_CConst : meta -> Prims.bool) =
  fun projectee -> match projectee with | CConst _0 -> true | uu___ -> false
let (__proj__CConst__item___0 : meta -> Prims.string) =
  fun projectee -> match projectee with | CConst _0 -> _0
let (uu___is_CCConv : meta -> Prims.bool) =
  fun projectee -> match projectee with | CCConv _0 -> true | uu___ -> false
let (__proj__CCConv__item___0 : meta -> Prims.string) =
  fun projectee -> match projectee with | CCConv _0 -> _0
let (uu___is_Erased : meta -> Prims.bool) =
  fun projectee -> match projectee with | Erased -> true | uu___ -> false
let (uu___is_CAbstract : meta -> Prims.bool) =
  fun projectee -> match projectee with | CAbstract -> true | uu___ -> false
let (uu___is_CIfDef : meta -> Prims.bool) =
  fun projectee -> match projectee with | CIfDef -> true | uu___ -> false
let (uu___is_CMacro : meta -> Prims.bool) =
  fun projectee -> match projectee with | CMacro -> true | uu___ -> false
let (uu___is_Deprecated : meta -> Prims.bool) =
  fun projectee ->
    match projectee with | Deprecated _0 -> true | uu___ -> false
let (__proj__Deprecated__item___0 : meta -> Prims.string) =
  fun projectee -> match projectee with | Deprecated _0 -> _0
let (uu___is_RemoveUnusedTypeParameters : meta -> Prims.bool) =
  fun projectee ->
    match projectee with
    | RemoveUnusedTypeParameters _0 -> true
    | uu___ -> false
let (__proj__RemoveUnusedTypeParameters__item___0 :
  meta -> (Prims.int Prims.list * FStarC_Compiler_Range_Type.range)) =
  fun projectee -> match projectee with | RemoveUnusedTypeParameters _0 -> _0
let (uu___is_HasValDecl : meta -> Prims.bool) =
  fun projectee ->
    match projectee with | HasValDecl _0 -> true | uu___ -> false
let (__proj__HasValDecl__item___0 : meta -> FStarC_Compiler_Range_Type.range)
  = fun projectee -> match projectee with | HasValDecl _0 -> _0
let (uu___is_CNoInline : meta -> Prims.bool) =
  fun projectee -> match projectee with | CNoInline -> true | uu___ -> false
type metadata = meta Prims.list
type mlletflavor =
  | Rec 
  | NonRec 
let (uu___is_Rec : mlletflavor -> Prims.bool) =
  fun projectee -> match projectee with | Rec -> true | uu___ -> false
let (uu___is_NonRec : mlletflavor -> Prims.bool) =
  fun projectee -> match projectee with | NonRec -> true | uu___ -> false
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
let (__proj__Mkmlbinder__item__mlbinder_name : mlbinder -> mlident) =
  fun projectee ->
    match projectee with
    | { mlbinder_name; mlbinder_ty; mlbinder_attrs;_} -> mlbinder_name
let (__proj__Mkmlbinder__item__mlbinder_ty : mlbinder -> mlty) =
  fun projectee ->
    match projectee with
    | { mlbinder_name; mlbinder_ty; mlbinder_attrs;_} -> mlbinder_ty
let (__proj__Mkmlbinder__item__mlbinder_attrs :
  mlbinder -> mlexpr Prims.list) =
  fun projectee ->
    match projectee with
    | { mlbinder_name; mlbinder_ty; mlbinder_attrs;_} -> mlbinder_attrs
let (uu___is_MLE_Const : mlexpr' -> Prims.bool) =
  fun projectee ->
    match projectee with | MLE_Const _0 -> true | uu___ -> false
let (__proj__MLE_Const__item___0 : mlexpr' -> mlconstant) =
  fun projectee -> match projectee with | MLE_Const _0 -> _0
let (uu___is_MLE_Var : mlexpr' -> Prims.bool) =
  fun projectee -> match projectee with | MLE_Var _0 -> true | uu___ -> false
let (__proj__MLE_Var__item___0 : mlexpr' -> mlident) =
  fun projectee -> match projectee with | MLE_Var _0 -> _0
let (uu___is_MLE_Name : mlexpr' -> Prims.bool) =
  fun projectee ->
    match projectee with | MLE_Name _0 -> true | uu___ -> false
let (__proj__MLE_Name__item___0 : mlexpr' -> mlpath) =
  fun projectee -> match projectee with | MLE_Name _0 -> _0
let (uu___is_MLE_Let : mlexpr' -> Prims.bool) =
  fun projectee -> match projectee with | MLE_Let _0 -> true | uu___ -> false
let (__proj__MLE_Let__item___0 :
  mlexpr' -> ((mlletflavor * mllb Prims.list) * mlexpr)) =
  fun projectee -> match projectee with | MLE_Let _0 -> _0
let (uu___is_MLE_App : mlexpr' -> Prims.bool) =
  fun projectee -> match projectee with | MLE_App _0 -> true | uu___ -> false
let (__proj__MLE_App__item___0 : mlexpr' -> (mlexpr * mlexpr Prims.list)) =
  fun projectee -> match projectee with | MLE_App _0 -> _0
let (uu___is_MLE_TApp : mlexpr' -> Prims.bool) =
  fun projectee ->
    match projectee with | MLE_TApp _0 -> true | uu___ -> false
let (__proj__MLE_TApp__item___0 : mlexpr' -> (mlexpr * mlty Prims.list)) =
  fun projectee -> match projectee with | MLE_TApp _0 -> _0
let (uu___is_MLE_Fun : mlexpr' -> Prims.bool) =
  fun projectee -> match projectee with | MLE_Fun _0 -> true | uu___ -> false
let (__proj__MLE_Fun__item___0 : mlexpr' -> (mlbinder Prims.list * mlexpr)) =
  fun projectee -> match projectee with | MLE_Fun _0 -> _0
let (uu___is_MLE_Match : mlexpr' -> Prims.bool) =
  fun projectee ->
    match projectee with | MLE_Match _0 -> true | uu___ -> false
let (__proj__MLE_Match__item___0 :
  mlexpr' ->
    (mlexpr * (mlpattern * mlexpr FStar_Pervasives_Native.option * mlexpr)
      Prims.list))
  = fun projectee -> match projectee with | MLE_Match _0 -> _0
let (uu___is_MLE_Coerce : mlexpr' -> Prims.bool) =
  fun projectee ->
    match projectee with | MLE_Coerce _0 -> true | uu___ -> false
let (__proj__MLE_Coerce__item___0 : mlexpr' -> (mlexpr * mlty * mlty)) =
  fun projectee -> match projectee with | MLE_Coerce _0 -> _0
let (uu___is_MLE_CTor : mlexpr' -> Prims.bool) =
  fun projectee ->
    match projectee with | MLE_CTor _0 -> true | uu___ -> false
let (__proj__MLE_CTor__item___0 : mlexpr' -> (mlpath * mlexpr Prims.list)) =
  fun projectee -> match projectee with | MLE_CTor _0 -> _0
let (uu___is_MLE_Seq : mlexpr' -> Prims.bool) =
  fun projectee -> match projectee with | MLE_Seq _0 -> true | uu___ -> false
let (__proj__MLE_Seq__item___0 : mlexpr' -> mlexpr Prims.list) =
  fun projectee -> match projectee with | MLE_Seq _0 -> _0
let (uu___is_MLE_Tuple : mlexpr' -> Prims.bool) =
  fun projectee ->
    match projectee with | MLE_Tuple _0 -> true | uu___ -> false
let (__proj__MLE_Tuple__item___0 : mlexpr' -> mlexpr Prims.list) =
  fun projectee -> match projectee with | MLE_Tuple _0 -> _0
let (uu___is_MLE_Record : mlexpr' -> Prims.bool) =
  fun projectee ->
    match projectee with | MLE_Record _0 -> true | uu___ -> false
let (__proj__MLE_Record__item___0 :
  mlexpr' ->
    (mlsymbol Prims.list * mlsymbol * (mlsymbol * mlexpr) Prims.list))
  = fun projectee -> match projectee with | MLE_Record _0 -> _0
let (uu___is_MLE_Proj : mlexpr' -> Prims.bool) =
  fun projectee ->
    match projectee with | MLE_Proj _0 -> true | uu___ -> false
let (__proj__MLE_Proj__item___0 : mlexpr' -> (mlexpr * mlpath)) =
  fun projectee -> match projectee with | MLE_Proj _0 -> _0
let (uu___is_MLE_If : mlexpr' -> Prims.bool) =
  fun projectee -> match projectee with | MLE_If _0 -> true | uu___ -> false
let (__proj__MLE_If__item___0 :
  mlexpr' -> (mlexpr * mlexpr * mlexpr FStar_Pervasives_Native.option)) =
  fun projectee -> match projectee with | MLE_If _0 -> _0
let (uu___is_MLE_Raise : mlexpr' -> Prims.bool) =
  fun projectee ->
    match projectee with | MLE_Raise _0 -> true | uu___ -> false
let (__proj__MLE_Raise__item___0 : mlexpr' -> (mlpath * mlexpr Prims.list)) =
  fun projectee -> match projectee with | MLE_Raise _0 -> _0
let (uu___is_MLE_Try : mlexpr' -> Prims.bool) =
  fun projectee -> match projectee with | MLE_Try _0 -> true | uu___ -> false
let (__proj__MLE_Try__item___0 :
  mlexpr' ->
    (mlexpr * (mlpattern * mlexpr FStar_Pervasives_Native.option * mlexpr)
      Prims.list))
  = fun projectee -> match projectee with | MLE_Try _0 -> _0
let (__proj__Mkmlexpr__item__expr : mlexpr -> mlexpr') =
  fun projectee ->
    match projectee with | { expr; mlty = mlty1; loc;_} -> expr
let (__proj__Mkmlexpr__item__mlty : mlexpr -> mlty) =
  fun projectee ->
    match projectee with | { expr; mlty = mlty1; loc;_} -> mlty1
let (__proj__Mkmlexpr__item__loc : mlexpr -> mlloc) =
  fun projectee -> match projectee with | { expr; mlty = mlty1; loc;_} -> loc
let (__proj__Mkmllb__item__mllb_name : mllb -> mlident) =
  fun projectee ->
    match projectee with
    | { mllb_name; mllb_tysc; mllb_add_unit; mllb_def; mllb_attrs; mllb_meta;
        print_typ;_} -> mllb_name
let (__proj__Mkmllb__item__mllb_tysc :
  mllb -> (ty_param Prims.list * mlty) FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { mllb_name; mllb_tysc; mllb_add_unit; mllb_def; mllb_attrs; mllb_meta;
        print_typ;_} -> mllb_tysc
let (__proj__Mkmllb__item__mllb_add_unit : mllb -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { mllb_name; mllb_tysc; mllb_add_unit; mllb_def; mllb_attrs; mllb_meta;
        print_typ;_} -> mllb_add_unit
let (__proj__Mkmllb__item__mllb_def : mllb -> mlexpr) =
  fun projectee ->
    match projectee with
    | { mllb_name; mllb_tysc; mllb_add_unit; mllb_def; mllb_attrs; mllb_meta;
        print_typ;_} -> mllb_def
let (__proj__Mkmllb__item__mllb_attrs : mllb -> mlexpr Prims.list) =
  fun projectee ->
    match projectee with
    | { mllb_name; mllb_tysc; mllb_add_unit; mllb_def; mllb_attrs; mllb_meta;
        print_typ;_} -> mllb_attrs
let (__proj__Mkmllb__item__mllb_meta : mllb -> metadata) =
  fun projectee ->
    match projectee with
    | { mllb_name; mllb_tysc; mllb_add_unit; mllb_def; mllb_attrs; mllb_meta;
        print_typ;_} -> mllb_meta
let (__proj__Mkmllb__item__print_typ : mllb -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { mllb_name; mllb_tysc; mllb_add_unit; mllb_def; mllb_attrs; mllb_meta;
        print_typ;_} -> print_typ
let (__proj__Mkty_param__item__ty_param_name : ty_param -> mlident) =
  fun projectee ->
    match projectee with
    | { ty_param_name; ty_param_attrs;_} -> ty_param_name
let (__proj__Mkty_param__item__ty_param_attrs :
  ty_param -> mlexpr Prims.list) =
  fun projectee ->
    match projectee with
    | { ty_param_name; ty_param_attrs;_} -> ty_param_attrs
type mlbranch = (mlpattern * mlexpr FStar_Pervasives_Native.option * mlexpr)
type mlletbinding = (mlletflavor * mllb Prims.list)
type mlattribute = mlexpr
type mltyscheme = (ty_param Prims.list * mlty)
type mltybody =
  | MLTD_Abbrev of mlty 
  | MLTD_Record of (mlsymbol * mlty) Prims.list 
  | MLTD_DType of (mlsymbol * (mlsymbol * mlty) Prims.list) Prims.list 
let (uu___is_MLTD_Abbrev : mltybody -> Prims.bool) =
  fun projectee ->
    match projectee with | MLTD_Abbrev _0 -> true | uu___ -> false
let (__proj__MLTD_Abbrev__item___0 : mltybody -> mlty) =
  fun projectee -> match projectee with | MLTD_Abbrev _0 -> _0
let (uu___is_MLTD_Record : mltybody -> Prims.bool) =
  fun projectee ->
    match projectee with | MLTD_Record _0 -> true | uu___ -> false
let (__proj__MLTD_Record__item___0 :
  mltybody -> (mlsymbol * mlty) Prims.list) =
  fun projectee -> match projectee with | MLTD_Record _0 -> _0
let (uu___is_MLTD_DType : mltybody -> Prims.bool) =
  fun projectee ->
    match projectee with | MLTD_DType _0 -> true | uu___ -> false
let (__proj__MLTD_DType__item___0 :
  mltybody -> (mlsymbol * (mlsymbol * mlty) Prims.list) Prims.list) =
  fun projectee -> match projectee with | MLTD_DType _0 -> _0
type one_mltydecl =
  {
  tydecl_assumed: Prims.bool ;
  tydecl_name: mlsymbol ;
  tydecl_ignored: mlsymbol FStar_Pervasives_Native.option ;
  tydecl_parameters: ty_param Prims.list ;
  tydecl_meta: metadata ;
  tydecl_defn: mltybody FStar_Pervasives_Native.option }
let (__proj__Mkone_mltydecl__item__tydecl_assumed :
  one_mltydecl -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { tydecl_assumed; tydecl_name; tydecl_ignored; tydecl_parameters;
        tydecl_meta; tydecl_defn;_} -> tydecl_assumed
let (__proj__Mkone_mltydecl__item__tydecl_name : one_mltydecl -> mlsymbol) =
  fun projectee ->
    match projectee with
    | { tydecl_assumed; tydecl_name; tydecl_ignored; tydecl_parameters;
        tydecl_meta; tydecl_defn;_} -> tydecl_name
let (__proj__Mkone_mltydecl__item__tydecl_ignored :
  one_mltydecl -> mlsymbol FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { tydecl_assumed; tydecl_name; tydecl_ignored; tydecl_parameters;
        tydecl_meta; tydecl_defn;_} -> tydecl_ignored
let (__proj__Mkone_mltydecl__item__tydecl_parameters :
  one_mltydecl -> ty_param Prims.list) =
  fun projectee ->
    match projectee with
    | { tydecl_assumed; tydecl_name; tydecl_ignored; tydecl_parameters;
        tydecl_meta; tydecl_defn;_} -> tydecl_parameters
let (__proj__Mkone_mltydecl__item__tydecl_meta : one_mltydecl -> metadata) =
  fun projectee ->
    match projectee with
    | { tydecl_assumed; tydecl_name; tydecl_ignored; tydecl_parameters;
        tydecl_meta; tydecl_defn;_} -> tydecl_meta
let (__proj__Mkone_mltydecl__item__tydecl_defn :
  one_mltydecl -> mltybody FStar_Pervasives_Native.option) =
  fun projectee ->
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
let (uu___is_MLM_Ty : mlmodule1' -> Prims.bool) =
  fun projectee -> match projectee with | MLM_Ty _0 -> true | uu___ -> false
let (__proj__MLM_Ty__item___0 : mlmodule1' -> mltydecl) =
  fun projectee -> match projectee with | MLM_Ty _0 -> _0
let (uu___is_MLM_Let : mlmodule1' -> Prims.bool) =
  fun projectee -> match projectee with | MLM_Let _0 -> true | uu___ -> false
let (__proj__MLM_Let__item___0 : mlmodule1' -> mlletbinding) =
  fun projectee -> match projectee with | MLM_Let _0 -> _0
let (uu___is_MLM_Exn : mlmodule1' -> Prims.bool) =
  fun projectee -> match projectee with | MLM_Exn _0 -> true | uu___ -> false
let (__proj__MLM_Exn__item___0 :
  mlmodule1' -> (mlsymbol * (mlsymbol * mlty) Prims.list)) =
  fun projectee -> match projectee with | MLM_Exn _0 -> _0
let (uu___is_MLM_Top : mlmodule1' -> Prims.bool) =
  fun projectee -> match projectee with | MLM_Top _0 -> true | uu___ -> false
let (__proj__MLM_Top__item___0 : mlmodule1' -> mlexpr) =
  fun projectee -> match projectee with | MLM_Top _0 -> _0
let (uu___is_MLM_Loc : mlmodule1' -> Prims.bool) =
  fun projectee -> match projectee with | MLM_Loc _0 -> true | uu___ -> false
let (__proj__MLM_Loc__item___0 : mlmodule1' -> mlloc) =
  fun projectee -> match projectee with | MLM_Loc _0 -> _0
type mlmodule1 =
  {
  mlmodule1_m: mlmodule1' ;
  mlmodule1_attrs: mlattribute Prims.list }
let (__proj__Mkmlmodule1__item__mlmodule1_m : mlmodule1 -> mlmodule1') =
  fun projectee ->
    match projectee with | { mlmodule1_m; mlmodule1_attrs;_} -> mlmodule1_m
let (__proj__Mkmlmodule1__item__mlmodule1_attrs :
  mlmodule1 -> mlattribute Prims.list) =
  fun projectee ->
    match projectee with
    | { mlmodule1_m; mlmodule1_attrs;_} -> mlmodule1_attrs
let (mk_mlmodule1 : mlmodule1' -> mlmodule1) =
  fun m -> { mlmodule1_m = m; mlmodule1_attrs = [] }
let (mk_mlmodule1_with_attrs :
  mlmodule1' -> mlattribute Prims.list -> mlmodule1) =
  fun m -> fun attrs -> { mlmodule1_m = m; mlmodule1_attrs = attrs }
type mlmodule = mlmodule1 Prims.list
type mlsig1 =
  | MLS_Mod of (mlsymbol * mlsig1 Prims.list) 
  | MLS_Ty of mltydecl 
  | MLS_Val of (mlsymbol * mltyscheme) 
  | MLS_Exn of (mlsymbol * mlty Prims.list) 
let (uu___is_MLS_Mod : mlsig1 -> Prims.bool) =
  fun projectee -> match projectee with | MLS_Mod _0 -> true | uu___ -> false
let (__proj__MLS_Mod__item___0 : mlsig1 -> (mlsymbol * mlsig1 Prims.list)) =
  fun projectee -> match projectee with | MLS_Mod _0 -> _0
let (uu___is_MLS_Ty : mlsig1 -> Prims.bool) =
  fun projectee -> match projectee with | MLS_Ty _0 -> true | uu___ -> false
let (__proj__MLS_Ty__item___0 : mlsig1 -> mltydecl) =
  fun projectee -> match projectee with | MLS_Ty _0 -> _0
let (uu___is_MLS_Val : mlsig1 -> Prims.bool) =
  fun projectee -> match projectee with | MLS_Val _0 -> true | uu___ -> false
let (__proj__MLS_Val__item___0 : mlsig1 -> (mlsymbol * mltyscheme)) =
  fun projectee -> match projectee with | MLS_Val _0 -> _0
let (uu___is_MLS_Exn : mlsig1 -> Prims.bool) =
  fun projectee -> match projectee with | MLS_Exn _0 -> true | uu___ -> false
let (__proj__MLS_Exn__item___0 : mlsig1 -> (mlsymbol * mlty Prims.list)) =
  fun projectee -> match projectee with | MLS_Exn _0 -> _0
type mlsig = mlsig1 Prims.list
let (with_ty_loc : mlty -> mlexpr' -> mlloc -> mlexpr) =
  fun t -> fun e -> fun l -> { expr = e; mlty = t; loc = l }
let (with_ty : mlty -> mlexpr' -> mlexpr) =
  fun t -> fun e -> with_ty_loc t e dummy_loc
type mllib =
  | MLLib of (mlpath * (mlsig * mlmodule) FStar_Pervasives_Native.option *
  mllib) Prims.list 
let (uu___is_MLLib : mllib -> Prims.bool) = fun projectee -> true
let (__proj__MLLib__item___0 :
  mllib ->
    (mlpath * (mlsig * mlmodule) FStar_Pervasives_Native.option * mllib)
      Prims.list)
  = fun projectee -> match projectee with | MLLib _0 -> _0
let (ml_unit_ty : mlty) = MLTY_Erased
let (ml_bool_ty : mlty) = MLTY_Named ([], (["Prims"], "bool"))
let (ml_int_ty : mlty) = MLTY_Named ([], (["Prims"], "int"))
let (ml_string_ty : mlty) = MLTY_Named ([], (["Prims"], "string"))
let (ml_unit : mlexpr) = with_ty ml_unit_ty (MLE_Const MLC_Unit)
let (apply_obj_repr : mlexpr -> mlty -> mlexpr) =
  fun x ->
    fun t ->
      let repr_name =
        let uu___ =
          let uu___1 = FStarC_Options.codegen () in
          uu___1 = (FStar_Pervasives_Native.Some FStarC_Options.FSharp) in
        if uu___ then MLE_Name ([], "box") else MLE_Name (["Obj"], "repr") in
      let obj_repr = with_ty (MLTY_Fun (t, E_PURE, MLTY_Top)) repr_name in
      with_ty_loc MLTY_Top (MLE_App (obj_repr, [x])) x.loc
let (ty_param_names : ty_param Prims.list -> Prims.string Prims.list) =
  fun tys ->
    FStarC_Compiler_List.map
      (fun uu___ ->
         match uu___ with
         | { ty_param_name; ty_param_attrs = uu___1;_} -> ty_param_name) tys
let (push_unit : e_tag -> mltyscheme -> mltyscheme) =
  fun eff ->
    fun ts ->
      let uu___ = ts in
      match uu___ with | (vs, ty) -> (vs, (MLTY_Fun (ml_unit_ty, eff, ty)))
let (pop_unit : mltyscheme -> (e_tag * mltyscheme)) =
  fun ts ->
    let uu___ = ts in
    match uu___ with
    | (vs, ty) ->
        (match ty with
         | MLTY_Fun (l, eff, t) ->
             if l = ml_unit_ty
             then (eff, (vs, t))
             else failwith "unexpected: pop_unit: domain was not unit"
         | uu___1 -> failwith "unexpected: pop_unit: not a function type")
let (ctor' :
  Prims.string -> FStarC_Pprint.document Prims.list -> FStarC_Pprint.document)
  =
  fun n ->
    fun args ->
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 = FStarC_Pprint.break_ Prims.int_one in
            let uu___4 =
              let uu___5 = FStarC_Pprint.doc_of_string n in uu___5 :: args in
            FStarC_Pprint.flow uu___3 uu___4 in
          FStarC_Pprint.parens uu___2 in
        FStarC_Pprint.group uu___1 in
      FStarC_Pprint.nest (Prims.of_int (2)) uu___
let (ctor : Prims.string -> FStarC_Pprint.document -> FStarC_Pprint.document)
  =
  fun n ->
    fun arg ->
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 = FStarC_Pprint.doc_of_string n in
            FStarC_Pprint.op_Hat_Slash_Hat uu___3 arg in
          FStarC_Pprint.parens uu___2 in
        FStarC_Pprint.group uu___1 in
      FStarC_Pprint.nest (Prims.of_int (2)) uu___
let rec (mlty_to_doc : mlty -> FStarC_Pprint.document) =
  fun t ->
    match t with
    | MLTY_Var v -> FStarC_Pprint.doc_of_string v
    | MLTY_Fun (t1, uu___, t2) ->
        let uu___1 =
          let uu___2 = mlty_to_doc t1 in
          let uu___3 =
            let uu___4 = FStarC_Pprint.doc_of_string "->" in
            let uu___5 = let uu___6 = mlty_to_doc t2 in [uu___6] in uu___4 ::
              uu___5 in
          uu___2 :: uu___3 in
        ctor' "<MLTY_Fun>" uu___1
    | MLTY_Named (ts, p) ->
        let uu___ =
          let uu___1 = FStarC_Compiler_List.map mlty_to_doc ts in
          let uu___2 =
            let uu___3 =
              let uu___4 = string_of_mlpath p in
              FStarC_Pprint.doc_of_string uu___4 in
            [uu___3] in
          FStarC_Compiler_List.op_At uu___1 uu___2 in
        ctor' "<MLTY_Named>" uu___
    | MLTY_Tuple ts ->
        let uu___ =
          let uu___1 =
            let uu___2 = FStarC_Pprint.doc_of_string " *" in
            let uu___3 = FStarC_Pprint.break_ Prims.int_one in
            FStarC_Pprint.op_Hat_Hat uu___2 uu___3 in
          FStarC_Pprint.flow_map uu___1 mlty_to_doc ts in
        ctor "<MLTY_Tuple>" uu___
    | MLTY_Top -> FStarC_Pprint.doc_of_string "MLTY_Top"
    | MLTY_Erased -> FStarC_Pprint.doc_of_string "MLTY_Erased"
let (mlty_to_string : mlty -> Prims.string) =
  fun t -> let uu___ = mlty_to_doc t in FStarC_Pprint.render uu___
let (mltyscheme_to_doc : mltyscheme -> FStarC_Pprint.document) =
  fun tsc ->
    let uu___ =
      let uu___1 =
        let uu___2 =
          let uu___3 =
            let uu___4 = FStarC_Pprint.break_ Prims.int_one in
            FStarC_Pprint.op_Hat_Hat FStarC_Pprint.comma uu___4 in
          let uu___4 = ty_param_names (FStar_Pervasives_Native.fst tsc) in
          FStarC_Pprint.flow_map uu___3 FStarC_Pprint.doc_of_string uu___4 in
        FStarC_Pprint.brackets uu___2 in
      let uu___2 =
        let uu___3 = FStarC_Pprint.doc_of_string "," in
        let uu___4 = mlty_to_doc (FStar_Pervasives_Native.snd tsc) in
        FStarC_Pprint.op_Hat_Slash_Hat uu___3 uu___4 in
      FStarC_Pprint.op_Hat_Hat uu___1 uu___2 in
    ctor "<MLTY_Scheme>" uu___
let (mltyscheme_to_string : mltyscheme -> Prims.string) =
  fun tsc -> let uu___ = mltyscheme_to_doc tsc in FStarC_Pprint.render uu___
let (pair :
  FStarC_Pprint.document -> FStarC_Pprint.document -> FStarC_Pprint.document)
  =
  fun a ->
    fun b ->
      let uu___ =
        let uu___1 =
          let uu___2 = FStarC_Pprint.op_Hat_Slash_Hat FStarC_Pprint.comma b in
          FStarC_Pprint.op_Hat_Hat a uu___2 in
        FStarC_Pprint.parens uu___1 in
      FStarC_Pprint.group uu___
let (triple :
  FStarC_Pprint.document ->
    FStarC_Pprint.document ->
      FStarC_Pprint.document -> FStarC_Pprint.document)
  =
  fun a ->
    fun b ->
      fun c ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  FStarC_Pprint.op_Hat_Slash_Hat FStarC_Pprint.comma c in
                FStarC_Pprint.op_Hat_Hat b uu___4 in
              FStarC_Pprint.op_Hat_Slash_Hat FStarC_Pprint.comma uu___3 in
            FStarC_Pprint.op_Hat_Hat a uu___2 in
          FStarC_Pprint.parens uu___1 in
        FStarC_Pprint.group uu___
let (ctor2 :
  Prims.string ->
    FStarC_Pprint.document ->
      FStarC_Pprint.document -> FStarC_Pprint.document)
  = fun n -> fun a -> fun b -> let uu___ = pair a b in ctor n uu___
let list_to_doc :
  't .
    't Prims.list -> ('t -> FStarC_Pprint.document) -> FStarC_Pprint.document
  =
  fun xs ->
    fun f ->
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 =
              let uu___4 = FStarC_Pprint.break_ Prims.int_one in
              FStarC_Pprint.op_Hat_Hat FStarC_Pprint.semi uu___4 in
            FStarC_Pprint.flow_map uu___3 f xs in
          FStarC_Pprint.brackets uu___2 in
        FStarC_Pprint.group uu___1 in
      FStarC_Pprint.nest (Prims.of_int (2)) uu___
let option_to_doc :
  't .
    't FStar_Pervasives_Native.option ->
      ('t -> FStarC_Pprint.document) -> FStarC_Pprint.document
  =
  fun x ->
    fun f ->
      match x with
      | FStar_Pervasives_Native.Some x1 ->
          let uu___ =
            let uu___1 = FStarC_Pprint.doc_of_string "Some" in
            let uu___2 = f x1 in FStarC_Pprint.op_Hat_Slash_Hat uu___1 uu___2 in
          FStarC_Pprint.group uu___
      | FStar_Pervasives_Native.None -> FStarC_Pprint.doc_of_string "None"
let (spaced : FStarC_Pprint.document -> FStarC_Pprint.document) =
  fun a ->
    let uu___ = FStarC_Pprint.break_ Prims.int_one in
    let uu___1 =
      let uu___2 = FStarC_Pprint.break_ Prims.int_one in
      FStarC_Pprint.op_Hat_Hat a uu___2 in
    FStarC_Pprint.op_Hat_Hat uu___ uu___1
let (record : FStarC_Pprint.document Prims.list -> FStarC_Pprint.document) =
  fun fs ->
    let uu___ =
      let uu___1 =
        let uu___2 =
          let uu___3 =
            let uu___4 =
              let uu___5 = FStarC_Pprint.break_ Prims.int_one in
              FStarC_Pprint.op_Hat_Hat FStarC_Pprint.semi uu___5 in
            FStarC_Pprint.separate uu___4 fs in
          spaced uu___3 in
        FStarC_Pprint.braces uu___2 in
      FStarC_Pprint.nest (Prims.of_int (2)) uu___1 in
    FStarC_Pprint.group uu___
let (fld : Prims.string -> FStarC_Pprint.document -> FStarC_Pprint.document)
  =
  fun n ->
    fun v ->
      let uu___ =
        let uu___1 =
          let uu___2 = FStarC_Pprint.doc_of_string (Prims.strcat n " =") in
          FStarC_Pprint.op_Hat_Slash_Hat uu___2 v in
        FStarC_Pprint.nest (Prims.of_int (2)) uu___1 in
      FStarC_Pprint.group uu___
let rec (mlexpr_to_doc : mlexpr -> FStarC_Pprint.document) =
  fun e ->
    match e.expr with
    | MLE_Const c ->
        let uu___ = mlconstant_to_doc c in ctor "MLE_Const" uu___
    | MLE_Var x ->
        let uu___ = FStarC_Pprint.doc_of_string x in ctor "MLE_Var" uu___
    | MLE_Name (p, x) ->
        let uu___ =
          FStarC_Pprint.doc_of_string (FStarC_Compiler_String.concat "." p) in
        let uu___1 = FStarC_Pprint.doc_of_string x in
        ctor2 "MLE_Name" uu___ uu___1
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
               let uu___1 = FStarC_Pprint.doc_of_string b.mlbinder_name in
               let uu___2 = mlty_to_doc b.mlbinder_ty in pair uu___1 uu___2) in
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
          let uu___1 = string_of_mlpath p in
          FStarC_Pprint.doc_of_string uu___1 in
        let uu___1 = list_to_doc es mlexpr_to_doc in
        ctor2 "MLE_CTor" uu___ uu___1
    | MLE_Seq es ->
        let uu___ = list_to_doc es mlexpr_to_doc in ctor "MLE_Seq" uu___
    | MLE_Tuple es ->
        let uu___ = list_to_doc es mlexpr_to_doc in ctor "MLE_Tuple" uu___
    | MLE_Record (p, n, es) ->
        let uu___ =
          list_to_doc (FStarC_Compiler_List.op_At p [n])
            FStarC_Pprint.doc_of_string in
        let uu___1 =
          list_to_doc es
            (fun uu___2 ->
               match uu___2 with
               | (x, e1) ->
                   let uu___3 = FStarC_Pprint.doc_of_string x in
                   let uu___4 = mlexpr_to_doc e1 in pair uu___3 uu___4) in
        ctor2 "MLE_Record" uu___ uu___1
    | MLE_Proj (e1, p) ->
        let uu___ = mlexpr_to_doc e1 in
        let uu___1 =
          let uu___2 = string_of_mlpath p in
          FStarC_Pprint.doc_of_string uu___2 in
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
          let uu___1 = string_of_mlpath p in
          FStarC_Pprint.doc_of_string uu___1 in
        let uu___1 = list_to_doc es mlexpr_to_doc in
        ctor2 "MLE_Raise" uu___ uu___1
    | MLE_Try (e1, bs) ->
        let uu___ = mlexpr_to_doc e1 in
        let uu___1 = list_to_doc bs mlbranch_to_doc in
        ctor2 "MLE_Try" uu___ uu___1
and (mlbranch_to_doc :
  (mlpattern * mlexpr FStar_Pervasives_Native.option * mlexpr) ->
    FStarC_Pprint.document)
  =
  fun uu___ ->
    match uu___ with
    | (p, e1, e2) ->
        let uu___1 = mlpattern_to_doc p in
        let uu___2 = option_to_doc e1 mlexpr_to_doc in
        let uu___3 = mlexpr_to_doc e2 in triple uu___1 uu___2 uu___3
and (mlletbinding_to_doc :
  (mlletflavor * mllb Prims.list) -> FStarC_Pprint.document) =
  fun lbs ->
    let uu___ =
      let uu___1 =
        FStarC_Pprint.doc_of_string
          (match FStar_Pervasives_Native.__proj__Mktuple2__item___1 lbs with
           | Rec -> "Rec"
           | NonRec -> "NonRec") in
      let uu___2 =
        let uu___3 = FStarC_Pprint.doc_of_string ", " in
        let uu___4 =
          list_to_doc
            (FStar_Pervasives_Native.__proj__Mktuple2__item___2 lbs)
            mllb_to_doc in
        FStarC_Pprint.op_Hat_Hat uu___3 uu___4 in
      FStarC_Pprint.op_Hat_Hat uu___1 uu___2 in
    FStarC_Pprint.parens uu___
and (mllb_to_doc : mllb -> FStarC_Pprint.document) =
  fun lb ->
    let uu___ =
      let uu___1 =
        let uu___2 = FStarC_Pprint.doc_of_string lb.mllb_name in
        fld "mllb_name" uu___2 in
      let uu___2 =
        let uu___3 =
          let uu___4 = list_to_doc lb.mllb_attrs mlexpr_to_doc in
          fld "mllb_attrs" uu___4 in
        let uu___4 =
          let uu___5 =
            let uu___6 =
              option_to_doc lb.mllb_tysc
                (fun uu___7 ->
                   match uu___7 with | (uu___8, t) -> mlty_to_doc t) in
            fld "mllb_tysc" uu___6 in
          let uu___6 =
            let uu___7 =
              let uu___8 =
                let uu___9 =
                  FStarC_Compiler_Util.string_of_bool lb.mllb_add_unit in
                FStarC_Pprint.doc_of_string uu___9 in
              fld "mllb_add_unit" uu___8 in
            let uu___8 =
              let uu___9 =
                let uu___10 = mlexpr_to_doc lb.mllb_def in
                fld "mllb_def" uu___10 in
              [uu___9] in
            uu___7 :: uu___8 in
          uu___5 :: uu___6 in
        uu___3 :: uu___4 in
      uu___1 :: uu___2 in
    record uu___
and (mlconstant_to_doc : mlconstant -> FStarC_Pprint.document) =
  fun mlc ->
    match mlc with
    | MLC_Unit -> FStarC_Pprint.doc_of_string "MLC_Unit"
    | MLC_Bool b ->
        let uu___ =
          let uu___1 = FStarC_Compiler_Util.string_of_bool b in
          FStarC_Pprint.doc_of_string uu___1 in
        ctor "MLC_Bool" uu___
    | MLC_Int (s, FStar_Pervasives_Native.None) ->
        let uu___ = FStarC_Pprint.doc_of_string s in ctor "MLC_Int" uu___
    | MLC_Int (s, FStar_Pervasives_Native.Some (s1, s2)) ->
        let uu___ =
          let uu___1 = FStarC_Pprint.doc_of_string s in
          triple uu___1 FStarC_Pprint.underscore FStarC_Pprint.underscore in
        ctor "MLC_Int" uu___
    | MLC_Float f -> ctor "MLC_Float" FStarC_Pprint.underscore
    | MLC_Char c -> ctor "MLC_Char" FStarC_Pprint.underscore
    | MLC_String s ->
        let uu___ = FStarC_Pprint.doc_of_string s in ctor "MLC_String" uu___
    | MLC_Bytes b -> ctor "MLC_Bytes" FStarC_Pprint.underscore
and (mlpattern_to_doc : mlpattern -> FStarC_Pprint.document) =
  fun mlp ->
    match mlp with
    | MLP_Wild -> FStarC_Pprint.doc_of_string "MLP_Wild"
    | MLP_Const c ->
        let uu___ = mlconstant_to_doc c in ctor "MLP_Const" uu___
    | MLP_Var x ->
        let uu___ = FStarC_Pprint.doc_of_string x in ctor "MLP_Var" uu___
    | MLP_CTor (p, ps) ->
        let uu___ =
          let uu___1 = string_of_mlpath p in
          FStarC_Pprint.doc_of_string uu___1 in
        let uu___1 = list_to_doc ps mlpattern_to_doc in
        ctor2 "MLP_CTor" uu___ uu___1
    | MLP_Branch ps ->
        let uu___ = list_to_doc ps mlpattern_to_doc in
        ctor "MLP_Branch" uu___
    | MLP_Record (path, fields) ->
        let uu___ =
          FStarC_Pprint.doc_of_string
            (FStarC_Compiler_String.concat "." path) in
        let uu___1 =
          list_to_doc fields
            (fun uu___2 ->
               match uu___2 with
               | (x, p) ->
                   let uu___3 = FStarC_Pprint.doc_of_string x in
                   let uu___4 = mlpattern_to_doc p in pair uu___3 uu___4) in
        ctor2 "MLP_Record" uu___ uu___1
    | MLP_Tuple ps ->
        let uu___ = list_to_doc ps mlpattern_to_doc in ctor "MLP_Tuple" uu___
let (mlbranch_to_string : mlbranch -> Prims.string) =
  fun b -> let uu___ = mlbranch_to_doc b in FStarC_Pprint.render uu___
let (mlletbinding_to_string : mlletbinding -> Prims.string) =
  fun lb -> let uu___ = mlletbinding_to_doc lb in FStarC_Pprint.render uu___
let (mllb_to_string : mllb -> Prims.string) =
  fun lb -> let uu___ = mllb_to_doc lb in FStarC_Pprint.render uu___
let (mlpattern_to_string : mlpattern -> Prims.string) =
  fun p -> let uu___ = mlpattern_to_doc p in FStarC_Pprint.render uu___
let (mlconstant_to_string : mlconstant -> Prims.string) =
  fun c -> let uu___ = mlconstant_to_doc c in FStarC_Pprint.render uu___
let (mlexpr_to_string : mlexpr -> Prims.string) =
  fun e -> let uu___ = mlexpr_to_doc e in FStarC_Pprint.render uu___
let (mltybody_to_doc : mltybody -> FStarC_Pprint.document) =
  fun d ->
    match d with
    | MLTD_Abbrev mlty1 ->
        let uu___ = mlty_to_doc mlty1 in ctor "MLTD_Abbrev" uu___
    | MLTD_Record l ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  let uu___5 =
                    let uu___6 = FStarC_Pprint.break_ Prims.int_one in
                    FStarC_Pprint.op_Hat_Hat FStarC_Pprint.semi uu___6 in
                  FStarC_Pprint.flow_map uu___5
                    (fun uu___6 ->
                       match uu___6 with
                       | (x, t) ->
                           let uu___7 = FStarC_Pprint.doc_of_string x in
                           let uu___8 = mlty_to_doc t in pair uu___7 uu___8)
                    l in
                spaced uu___4 in
              FStarC_Pprint.braces uu___3 in
            FStarC_Pprint.nest (Prims.of_int (2)) uu___2 in
          FStarC_Pprint.group uu___1 in
        ctor "MLTD_Record" uu___
    | MLTD_DType l ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  let uu___5 =
                    let uu___6 = FStarC_Pprint.break_ Prims.int_one in
                    FStarC_Pprint.op_Hat_Hat FStarC_Pprint.semi uu___6 in
                  FStarC_Pprint.flow_map uu___5
                    (fun uu___6 ->
                       match uu___6 with
                       | (x, l1) ->
                           let uu___7 = FStarC_Pprint.doc_of_string x in
                           let uu___8 =
                             list_to_doc l1
                               (fun uu___9 ->
                                  match uu___9 with
                                  | (x1, t) ->
                                      let uu___10 =
                                        FStarC_Pprint.doc_of_string x1 in
                                      let uu___11 = mlty_to_doc t in
                                      pair uu___10 uu___11) in
                           pair uu___7 uu___8) l in
                spaced uu___4 in
              FStarC_Pprint.brackets uu___3 in
            FStarC_Pprint.nest (Prims.of_int (2)) uu___2 in
          FStarC_Pprint.group uu___1 in
        ctor "MLTD_DType" uu___
let (mltybody_to_string : mltybody -> Prims.string) =
  fun d -> let uu___ = mltybody_to_doc d in FStarC_Pprint.render uu___
let (one_mltydecl_to_doc : one_mltydecl -> FStarC_Pprint.document) =
  fun d ->
    let uu___ =
      let uu___1 =
        let uu___2 = FStarC_Pprint.doc_of_string d.tydecl_name in
        fld "tydecl_name" uu___2 in
      let uu___2 =
        let uu___3 =
          let uu___4 =
            let uu___5 =
              let uu___6 = ty_param_names d.tydecl_parameters in
              FStarC_Compiler_String.concat "," uu___6 in
            FStarC_Pprint.doc_of_string uu___5 in
          fld "tydecl_parameters" uu___4 in
        let uu___4 =
          let uu___5 =
            let uu___6 = option_to_doc d.tydecl_defn mltybody_to_doc in
            fld "tydecl_defn" uu___6 in
          [uu___5] in
        uu___3 :: uu___4 in
      uu___1 :: uu___2 in
    record uu___
let (one_mltydecl_to_string : one_mltydecl -> Prims.string) =
  fun d -> let uu___ = one_mltydecl_to_doc d in FStarC_Pprint.render uu___
let (mlmodule1_to_doc : mlmodule1 -> FStarC_Pprint.document) =
  fun m ->
    let uu___ =
      match m.mlmodule1_m with
      | MLM_Ty d ->
          let uu___1 = FStarC_Pprint.doc_of_string "MLM_Ty " in
          let uu___2 = list_to_doc d one_mltydecl_to_doc in
          FStarC_Pprint.op_Hat_Hat uu___1 uu___2
      | MLM_Let l ->
          let uu___1 = FStarC_Pprint.doc_of_string "MLM_Let " in
          let uu___2 = mlletbinding_to_doc l in
          FStarC_Pprint.op_Hat_Hat uu___1 uu___2
      | MLM_Exn (s, l) ->
          let uu___1 = FStarC_Pprint.doc_of_string "MLM_Exn" in
          let uu___2 =
            let uu___3 = FStarC_Pprint.doc_of_string s in
            let uu___4 =
              list_to_doc l
                (fun uu___5 ->
                   match uu___5 with
                   | (x, t) ->
                       let uu___6 = FStarC_Pprint.doc_of_string x in
                       let uu___7 = mlty_to_doc t in pair uu___6 uu___7) in
            pair uu___3 uu___4 in
          FStarC_Pprint.op_Hat_Slash_Hat uu___1 uu___2
      | MLM_Top e ->
          let uu___1 = FStarC_Pprint.doc_of_string "MLM_Top" in
          let uu___2 = mlexpr_to_doc e in
          FStarC_Pprint.op_Hat_Slash_Hat uu___1 uu___2
      | MLM_Loc _mlloc -> FStarC_Pprint.doc_of_string "MLM_Loc" in
    FStarC_Pprint.group uu___
let (mlmodule1_to_string : mlmodule1 -> Prims.string) =
  fun m -> let uu___ = mlmodule1_to_doc m in FStarC_Pprint.render uu___
let (mlmodule_to_doc : mlmodule -> FStarC_Pprint.document) =
  fun m ->
    let uu___ =
      let uu___1 =
        let uu___2 =
          let uu___3 =
            let uu___4 = FStarC_Pprint.break_ Prims.int_one in
            FStarC_Pprint.op_Hat_Hat FStarC_Pprint.semi uu___4 in
          FStarC_Pprint.separate_map uu___3 mlmodule1_to_doc m in
        spaced uu___2 in
      FStarC_Pprint.brackets uu___1 in
    FStarC_Pprint.group uu___
let (mlmodule_to_string : mlmodule -> Prims.string) =
  fun m -> let uu___ = mlmodule_to_doc m in FStarC_Pprint.render uu___
let (showable_mlty : mlty FStarC_Class_Show.showable) =
  { FStarC_Class_Show.show = mlty_to_string }
let (showable_mlconstant : mlconstant FStarC_Class_Show.showable) =
  { FStarC_Class_Show.show = mlconstant_to_string }
let (showable_mlexpr : mlexpr FStarC_Class_Show.showable) =
  { FStarC_Class_Show.show = mlexpr_to_string }
let (showable_mlmodule1 : mlmodule1 FStarC_Class_Show.showable) =
  { FStarC_Class_Show.show = mlmodule1_to_string }
let (showable_mlmodule : mlmodule FStarC_Class_Show.showable) =
  { FStarC_Class_Show.show = mlmodule_to_string }