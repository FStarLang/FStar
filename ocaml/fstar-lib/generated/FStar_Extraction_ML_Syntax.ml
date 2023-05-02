open Prims
type mlsymbol = Prims.string
type mlident = mlsymbol
type mlpath = (mlsymbol Prims.list * mlsymbol)
let krml_keywords : 'uuuuu . unit -> 'uuuuu Prims.list = fun uu___ -> []
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
let (string_of_mlpath : mlpath -> mlsymbol) =
  fun uu___ ->
    match uu___ with
    | (p, s) -> FStar_String.concat "." (FStar_Compiler_List.op_At p [s])
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
type mltyscheme = (mlidents * mlty)
type mlconstant =
  | MLC_Unit 
  | MLC_Bool of Prims.bool 
  | MLC_Int of (Prims.string * (FStar_Const.signedness * FStar_Const.width)
  FStar_Pervasives_Native.option) 
  | MLC_Float of FStar_BaseTypes.float 
  | MLC_Char of FStar_BaseTypes.char 
  | MLC_String of Prims.string 
  | MLC_Bytes of FStar_BaseTypes.byte Prims.array 
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
    (Prims.string * (FStar_Const.signedness * FStar_Const.width)
      FStar_Pervasives_Native.option))
  = fun projectee -> match projectee with | MLC_Int _0 -> _0
let (uu___is_MLC_Float : mlconstant -> Prims.bool) =
  fun projectee ->
    match projectee with | MLC_Float _0 -> true | uu___ -> false
let (__proj__MLC_Float__item___0 : mlconstant -> FStar_BaseTypes.float) =
  fun projectee -> match projectee with | MLC_Float _0 -> _0
let (uu___is_MLC_Char : mlconstant -> Prims.bool) =
  fun projectee ->
    match projectee with | MLC_Char _0 -> true | uu___ -> false
let (__proj__MLC_Char__item___0 : mlconstant -> FStar_BaseTypes.char) =
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
  mlconstant -> FStar_BaseTypes.byte Prims.array) =
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
  FStar_Compiler_Range_Type.range) 
  | HasValDecl of FStar_Compiler_Range_Type.range 
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
  meta -> (Prims.int Prims.list * FStar_Compiler_Range_Type.range)) =
  fun projectee -> match projectee with | RemoveUnusedTypeParameters _0 -> _0
let (uu___is_HasValDecl : meta -> Prims.bool) =
  fun projectee ->
    match projectee with | HasValDecl _0 -> true | uu___ -> false
let (__proj__HasValDecl__item___0 : meta -> FStar_Compiler_Range_Type.range)
  = fun projectee -> match projectee with | HasValDecl _0 -> _0
type metadata = meta Prims.list
type mlletflavor =
  | Rec 
  | NonRec 
let (uu___is_Rec : mlletflavor -> Prims.bool) =
  fun projectee -> match projectee with | Rec -> true | uu___ -> false
let (uu___is_NonRec : mlletflavor -> Prims.bool) =
  fun projectee -> match projectee with | NonRec -> true | uu___ -> false
type mlexpr' =
  | MLE_Const of mlconstant 
  | MLE_Var of mlident 
  | MLE_Name of mlpath 
  | MLE_Let of ((mlletflavor * mllb Prims.list) * mlexpr) 
  | MLE_App of (mlexpr * mlexpr Prims.list) 
  | MLE_TApp of (mlexpr * mlty Prims.list) 
  | MLE_Fun of ((mlident * mlty) Prims.list * mlexpr) 
  | MLE_Match of (mlexpr * (mlpattern * mlexpr FStar_Pervasives_Native.option
  * mlexpr) Prims.list) 
  | MLE_Coerce of (mlexpr * mlty * mlty) 
  | MLE_CTor of (mlpath * mlexpr Prims.list) 
  | MLE_Seq of mlexpr Prims.list 
  | MLE_Tuple of mlexpr Prims.list 
  | MLE_Record of (mlsymbol Prims.list * (mlsymbol * mlexpr) Prims.list) 
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
  mllb_tysc: mltyscheme FStar_Pervasives_Native.option ;
  mllb_add_unit: Prims.bool ;
  mllb_def: mlexpr ;
  mllb_meta: metadata ;
  print_typ: Prims.bool }
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
let (__proj__MLE_Fun__item___0 :
  mlexpr' -> ((mlident * mlty) Prims.list * mlexpr)) =
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
  mlexpr' -> (mlsymbol Prims.list * (mlsymbol * mlexpr) Prims.list)) =
  fun projectee -> match projectee with | MLE_Record _0 -> _0
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
    | { mllb_name; mllb_tysc; mllb_add_unit; mllb_def; mllb_meta;
        print_typ;_} -> mllb_name
let (__proj__Mkmllb__item__mllb_tysc :
  mllb -> mltyscheme FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { mllb_name; mllb_tysc; mllb_add_unit; mllb_def; mllb_meta;
        print_typ;_} -> mllb_tysc
let (__proj__Mkmllb__item__mllb_add_unit : mllb -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { mllb_name; mllb_tysc; mllb_add_unit; mllb_def; mllb_meta;
        print_typ;_} -> mllb_add_unit
let (__proj__Mkmllb__item__mllb_def : mllb -> mlexpr) =
  fun projectee ->
    match projectee with
    | { mllb_name; mllb_tysc; mllb_add_unit; mllb_def; mllb_meta;
        print_typ;_} -> mllb_def
let (__proj__Mkmllb__item__mllb_meta : mllb -> metadata) =
  fun projectee ->
    match projectee with
    | { mllb_name; mllb_tysc; mllb_add_unit; mllb_def; mllb_meta;
        print_typ;_} -> mllb_meta
let (__proj__Mkmllb__item__print_typ : mllb -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { mllb_name; mllb_tysc; mllb_add_unit; mllb_def; mllb_meta;
        print_typ;_} -> print_typ
type mlbranch = (mlpattern * mlexpr FStar_Pervasives_Native.option * mlexpr)
type mlletbinding = (mlletflavor * mllb Prims.list)
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
  tydecl_parameters: mlidents ;
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
  one_mltydecl -> mlidents) =
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
type mlmodule1 =
  | MLM_Ty of mltydecl 
  | MLM_Let of mlletbinding 
  | MLM_Exn of (mlsymbol * (mlsymbol * mlty) Prims.list) 
  | MLM_Top of mlexpr 
  | MLM_Loc of mlloc 
let (uu___is_MLM_Ty : mlmodule1 -> Prims.bool) =
  fun projectee -> match projectee with | MLM_Ty _0 -> true | uu___ -> false
let (__proj__MLM_Ty__item___0 : mlmodule1 -> mltydecl) =
  fun projectee -> match projectee with | MLM_Ty _0 -> _0
let (uu___is_MLM_Let : mlmodule1 -> Prims.bool) =
  fun projectee -> match projectee with | MLM_Let _0 -> true | uu___ -> false
let (__proj__MLM_Let__item___0 : mlmodule1 -> mlletbinding) =
  fun projectee -> match projectee with | MLM_Let _0 -> _0
let (uu___is_MLM_Exn : mlmodule1 -> Prims.bool) =
  fun projectee -> match projectee with | MLM_Exn _0 -> true | uu___ -> false
let (__proj__MLM_Exn__item___0 :
  mlmodule1 -> (mlsymbol * (mlsymbol * mlty) Prims.list)) =
  fun projectee -> match projectee with | MLM_Exn _0 -> _0
let (uu___is_MLM_Top : mlmodule1 -> Prims.bool) =
  fun projectee -> match projectee with | MLM_Top _0 -> true | uu___ -> false
let (__proj__MLM_Top__item___0 : mlmodule1 -> mlexpr) =
  fun projectee -> match projectee with | MLM_Top _0 -> _0
let (uu___is_MLM_Loc : mlmodule1 -> Prims.bool) =
  fun projectee -> match projectee with | MLM_Loc _0 -> true | uu___ -> false
let (__proj__MLM_Loc__item___0 : mlmodule1 -> mlloc) =
  fun projectee -> match projectee with | MLM_Loc _0 -> _0
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
let (mlp_lalloc : (Prims.string Prims.list * Prims.string)) =
  (["SST"], "lalloc")
let (apply_obj_repr : mlexpr -> mlty -> mlexpr) =
  fun x ->
    fun t ->
      let repr_name =
        let uu___ =
          let uu___1 = FStar_Options.codegen () in
          uu___1 = (FStar_Pervasives_Native.Some FStar_Options.FSharp) in
        if uu___ then MLE_Name ([], "box") else MLE_Name (["Obj"], "repr") in
      let obj_repr = with_ty (MLTY_Fun (t, E_PURE, MLTY_Top)) repr_name in
      with_ty_loc MLTY_Top (MLE_App (obj_repr, [x])) x.loc
let (push_unit : mltyscheme -> mltyscheme) =
  fun ts ->
    let uu___ = ts in
    match uu___ with | (vs, ty) -> (vs, (MLTY_Fun (ml_unit_ty, E_PURE, ty)))
let (pop_unit : mltyscheme -> mltyscheme) =
  fun ts ->
    let uu___ = ts in
    match uu___ with
    | (vs, ty) ->
        (match ty with
         | MLTY_Fun (l, E_PURE, t) ->
             if l = ml_unit_ty
             then (vs, t)
             else failwith "unexpected: pop_unit: domain was not unit"
         | uu___1 -> failwith "unexpected: pop_unit: not a function type")