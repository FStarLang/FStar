open Prims
type mlsymbol = Prims.string
type mlident = mlsymbol
type mlpath = (mlsymbol Prims.list * mlsymbol)
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
let (is_reserved : Prims.string -> Prims.bool) =
  fun k ->
    let reserved_keywords uu____366 =
      let uu____367 =
        let uu____369 = FStar_Options.codegen () in
        uu____369 = (FStar_Pervasives_Native.Some FStar_Options.FSharp) in
      if uu____367 then fsharpkeywords else ocamlkeywords in
    let uu____380 = reserved_keywords () in
    FStar_List.existsb (fun k' -> k' = k) uu____380
let (string_of_mlpath : mlpath -> mlsymbol) =
  fun uu____395 ->
    match uu____395 with
    | (p, s) -> FStar_String.concat "." (FStar_List.append p [s])
let (gensym : unit -> Prims.string) =
  fun uu____418 ->
    let i = FStar_Ident.next_id () in
    let uu____421 = FStar_Util.string_of_int i in Prims.op_Hat "_" uu____421
let rec (gensyms : Prims.int -> Prims.string Prims.list) =
  fun x ->
    match x with
    | _438 when _438 = (Prims.parse_int "0") -> []
    | n1 ->
        let uu____442 = gensym () in
        let uu____444 = gensyms (n1 - (Prims.parse_int "1")) in uu____442 ::
          uu____444
type mlidents = mlident Prims.list
type mlsymbols = mlsymbol Prims.list
type e_tag =
  | E_PURE 
  | E_GHOST 
  | E_IMPURE 
let (uu___is_E_PURE : e_tag -> Prims.bool) =
  fun projectee -> match projectee with | E_PURE -> true | uu____465 -> false
let (uu___is_E_GHOST : e_tag -> Prims.bool) =
  fun projectee ->
    match projectee with | E_GHOST -> true | uu____476 -> false
let (uu___is_E_IMPURE : e_tag -> Prims.bool) =
  fun projectee ->
    match projectee with | E_IMPURE -> true | uu____487 -> false
type mlloc = (Prims.int * Prims.string)
let (dummy_loc : mlloc) = ((Prims.parse_int "0"), "")
type mlty =
  | MLTY_Var of mlident 
  | MLTY_Fun of (mlty * e_tag * mlty) 
  | MLTY_Named of (mlty Prims.list * mlpath) 
  | MLTY_Tuple of mlty Prims.list 
  | MLTY_Top 
  | MLTY_Erased 
let (uu___is_MLTY_Var : mlty -> Prims.bool) =
  fun projectee ->
    match projectee with | MLTY_Var _0 -> true | uu____546 -> false
let (__proj__MLTY_Var__item___0 : mlty -> mlident) =
  fun projectee -> match projectee with | MLTY_Var _0 -> _0
let (uu___is_MLTY_Fun : mlty -> Prims.bool) =
  fun projectee ->
    match projectee with | MLTY_Fun _0 -> true | uu____574 -> false
let (__proj__MLTY_Fun__item___0 : mlty -> (mlty * e_tag * mlty)) =
  fun projectee -> match projectee with | MLTY_Fun _0 -> _0
let (uu___is_MLTY_Named : mlty -> Prims.bool) =
  fun projectee ->
    match projectee with | MLTY_Named _0 -> true | uu____617 -> false
let (__proj__MLTY_Named__item___0 : mlty -> (mlty Prims.list * mlpath)) =
  fun projectee -> match projectee with | MLTY_Named _0 -> _0
let (uu___is_MLTY_Tuple : mlty -> Prims.bool) =
  fun projectee ->
    match projectee with | MLTY_Tuple _0 -> true | uu____656 -> false
let (__proj__MLTY_Tuple__item___0 : mlty -> mlty Prims.list) =
  fun projectee -> match projectee with | MLTY_Tuple _0 -> _0
let (uu___is_MLTY_Top : mlty -> Prims.bool) =
  fun projectee ->
    match projectee with | MLTY_Top -> true | uu____680 -> false
let (uu___is_MLTY_Erased : mlty -> Prims.bool) =
  fun projectee ->
    match projectee with | MLTY_Erased -> true | uu____691 -> false
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
  fun projectee ->
    match projectee with | MLC_Unit -> true | uu____752 -> false
let (uu___is_MLC_Bool : mlconstant -> Prims.bool) =
  fun projectee ->
    match projectee with | MLC_Bool _0 -> true | uu____765 -> false
let (__proj__MLC_Bool__item___0 : mlconstant -> Prims.bool) =
  fun projectee -> match projectee with | MLC_Bool _0 -> _0
let (uu___is_MLC_Int : mlconstant -> Prims.bool) =
  fun projectee ->
    match projectee with | MLC_Int _0 -> true | uu____798 -> false
let (__proj__MLC_Int__item___0 :
  mlconstant ->
    (Prims.string * (FStar_Const.signedness * FStar_Const.width)
      FStar_Pervasives_Native.option))
  = fun projectee -> match projectee with | MLC_Int _0 -> _0
let (uu___is_MLC_Float : mlconstant -> Prims.bool) =
  fun projectee ->
    match projectee with | MLC_Float _0 -> true | uu____850 -> false
let (__proj__MLC_Float__item___0 : mlconstant -> FStar_BaseTypes.float) =
  fun projectee -> match projectee with | MLC_Float _0 -> _0
let (uu___is_MLC_Char : mlconstant -> Prims.bool) =
  fun projectee ->
    match projectee with | MLC_Char _0 -> true | uu____870 -> false
let (__proj__MLC_Char__item___0 : mlconstant -> FStar_BaseTypes.char) =
  fun projectee -> match projectee with | MLC_Char _0 -> _0
let (uu___is_MLC_String : mlconstant -> Prims.bool) =
  fun projectee ->
    match projectee with | MLC_String _0 -> true | uu____893 -> false
let (__proj__MLC_String__item___0 : mlconstant -> Prims.string) =
  fun projectee -> match projectee with | MLC_String _0 -> _0
let (uu___is_MLC_Bytes : mlconstant -> Prims.bool) =
  fun projectee ->
    match projectee with | MLC_Bytes _0 -> true | uu____917 -> false
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
  fun projectee ->
    match projectee with | MLP_Wild -> true | uu____996 -> false
let (uu___is_MLP_Const : mlpattern -> Prims.bool) =
  fun projectee ->
    match projectee with | MLP_Const _0 -> true | uu____1008 -> false
let (__proj__MLP_Const__item___0 : mlpattern -> mlconstant) =
  fun projectee -> match projectee with | MLP_Const _0 -> _0
let (uu___is_MLP_Var : mlpattern -> Prims.bool) =
  fun projectee ->
    match projectee with | MLP_Var _0 -> true | uu____1028 -> false
let (__proj__MLP_Var__item___0 : mlpattern -> mlident) =
  fun projectee -> match projectee with | MLP_Var _0 -> _0
let (uu___is_MLP_CTor : mlpattern -> Prims.bool) =
  fun projectee ->
    match projectee with | MLP_CTor _0 -> true | uu____1056 -> false
let (__proj__MLP_CTor__item___0 :
  mlpattern -> (mlpath * mlpattern Prims.list)) =
  fun projectee -> match projectee with | MLP_CTor _0 -> _0
let (uu___is_MLP_Branch : mlpattern -> Prims.bool) =
  fun projectee ->
    match projectee with | MLP_Branch _0 -> true | uu____1095 -> false
let (__proj__MLP_Branch__item___0 : mlpattern -> mlpattern Prims.list) =
  fun projectee -> match projectee with | MLP_Branch _0 -> _0
let (uu___is_MLP_Record : mlpattern -> Prims.bool) =
  fun projectee ->
    match projectee with | MLP_Record _0 -> true | uu____1134 -> false
let (__proj__MLP_Record__item___0 :
  mlpattern -> (mlsymbol Prims.list * (mlsymbol * mlpattern) Prims.list)) =
  fun projectee -> match projectee with | MLP_Record _0 -> _0
let (uu___is_MLP_Tuple : mlpattern -> Prims.bool) =
  fun projectee ->
    match projectee with | MLP_Tuple _0 -> true | uu____1197 -> false
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
let (uu___is_Mutable : meta -> Prims.bool) =
  fun projectee ->
    match projectee with | Mutable -> true | uu____1257 -> false
let (uu___is_Assumed : meta -> Prims.bool) =
  fun projectee ->
    match projectee with | Assumed -> true | uu____1268 -> false
let (uu___is_Private : meta -> Prims.bool) =
  fun projectee ->
    match projectee with | Private -> true | uu____1279 -> false
let (uu___is_NoExtract : meta -> Prims.bool) =
  fun projectee ->
    match projectee with | NoExtract -> true | uu____1290 -> false
let (uu___is_CInline : meta -> Prims.bool) =
  fun projectee ->
    match projectee with | CInline -> true | uu____1301 -> false
let (uu___is_Substitute : meta -> Prims.bool) =
  fun projectee ->
    match projectee with | Substitute -> true | uu____1312 -> false
let (uu___is_GCType : meta -> Prims.bool) =
  fun projectee ->
    match projectee with | GCType -> true | uu____1323 -> false
let (uu___is_PpxDerivingShow : meta -> Prims.bool) =
  fun projectee ->
    match projectee with | PpxDerivingShow -> true | uu____1334 -> false
let (uu___is_PpxDerivingShowConstant : meta -> Prims.bool) =
  fun projectee ->
    match projectee with
    | PpxDerivingShowConstant _0 -> true
    | uu____1347 -> false
let (__proj__PpxDerivingShowConstant__item___0 : meta -> Prims.string) =
  fun projectee -> match projectee with | PpxDerivingShowConstant _0 -> _0
let (uu___is_PpxDerivingYoJson : meta -> Prims.bool) =
  fun projectee ->
    match projectee with | PpxDerivingYoJson -> true | uu____1368 -> false
let (uu___is_Comment : meta -> Prims.bool) =
  fun projectee ->
    match projectee with | Comment _0 -> true | uu____1381 -> false
let (__proj__Comment__item___0 : meta -> Prims.string) =
  fun projectee -> match projectee with | Comment _0 -> _0
let (uu___is_StackInline : meta -> Prims.bool) =
  fun projectee ->
    match projectee with | StackInline -> true | uu____1402 -> false
let (uu___is_CPrologue : meta -> Prims.bool) =
  fun projectee ->
    match projectee with | CPrologue _0 -> true | uu____1415 -> false
let (__proj__CPrologue__item___0 : meta -> Prims.string) =
  fun projectee -> match projectee with | CPrologue _0 -> _0
let (uu___is_CEpilogue : meta -> Prims.bool) =
  fun projectee ->
    match projectee with | CEpilogue _0 -> true | uu____1438 -> false
let (__proj__CEpilogue__item___0 : meta -> Prims.string) =
  fun projectee -> match projectee with | CEpilogue _0 -> _0
let (uu___is_CConst : meta -> Prims.bool) =
  fun projectee ->
    match projectee with | CConst _0 -> true | uu____1461 -> false
let (__proj__CConst__item___0 : meta -> Prims.string) =
  fun projectee -> match projectee with | CConst _0 -> _0
let (uu___is_CCConv : meta -> Prims.bool) =
  fun projectee ->
    match projectee with | CCConv _0 -> true | uu____1484 -> false
let (__proj__CCConv__item___0 : meta -> Prims.string) =
  fun projectee -> match projectee with | CCConv _0 -> _0
let (uu___is_Erased : meta -> Prims.bool) =
  fun projectee ->
    match projectee with | Erased -> true | uu____1505 -> false
let (uu___is_CAbstract : meta -> Prims.bool) =
  fun projectee ->
    match projectee with | CAbstract -> true | uu____1516 -> false
let (uu___is_CIfDef : meta -> Prims.bool) =
  fun projectee ->
    match projectee with | CIfDef -> true | uu____1527 -> false
type metadata = meta Prims.list
type mlletflavor =
  | Rec 
  | NonRec 
let (uu___is_Rec : mlletflavor -> Prims.bool) =
  fun projectee -> match projectee with | Rec -> true | uu____1540 -> false
let (uu___is_NonRec : mlletflavor -> Prims.bool) =
  fun projectee ->
    match projectee with | NonRec -> true | uu____1551 -> false
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
    match projectee with | MLE_Const _0 -> true | uu____1808 -> false
let (__proj__MLE_Const__item___0 : mlexpr' -> mlconstant) =
  fun projectee -> match projectee with | MLE_Const _0 -> _0
let (uu___is_MLE_Var : mlexpr' -> Prims.bool) =
  fun projectee ->
    match projectee with | MLE_Var _0 -> true | uu____1828 -> false
let (__proj__MLE_Var__item___0 : mlexpr' -> mlident) =
  fun projectee -> match projectee with | MLE_Var _0 -> _0
let (uu___is_MLE_Name : mlexpr' -> Prims.bool) =
  fun projectee ->
    match projectee with | MLE_Name _0 -> true | uu____1850 -> false
let (__proj__MLE_Name__item___0 : mlexpr' -> mlpath) =
  fun projectee -> match projectee with | MLE_Name _0 -> _0
let (uu___is_MLE_Let : mlexpr' -> Prims.bool) =
  fun projectee ->
    match projectee with | MLE_Let _0 -> true | uu____1879 -> false
let (__proj__MLE_Let__item___0 :
  mlexpr' -> ((mlletflavor * mllb Prims.list) * mlexpr)) =
  fun projectee -> match projectee with | MLE_Let _0 -> _0
let (uu___is_MLE_App : mlexpr' -> Prims.bool) =
  fun projectee ->
    match projectee with | MLE_App _0 -> true | uu____1934 -> false
let (__proj__MLE_App__item___0 : mlexpr' -> (mlexpr * mlexpr Prims.list)) =
  fun projectee -> match projectee with | MLE_App _0 -> _0
let (uu___is_MLE_TApp : mlexpr' -> Prims.bool) =
  fun projectee ->
    match projectee with | MLE_TApp _0 -> true | uu____1977 -> false
let (__proj__MLE_TApp__item___0 : mlexpr' -> (mlexpr * mlty Prims.list)) =
  fun projectee -> match projectee with | MLE_TApp _0 -> _0
let (uu___is_MLE_Fun : mlexpr' -> Prims.bool) =
  fun projectee ->
    match projectee with | MLE_Fun _0 -> true | uu____2025 -> false
let (__proj__MLE_Fun__item___0 :
  mlexpr' -> ((mlident * mlty) Prims.list * mlexpr)) =
  fun projectee -> match projectee with | MLE_Fun _0 -> _0
let (uu___is_MLE_Match : mlexpr' -> Prims.bool) =
  fun projectee ->
    match projectee with | MLE_Match _0 -> true | uu____2091 -> false
let (__proj__MLE_Match__item___0 :
  mlexpr' ->
    (mlexpr * (mlpattern * mlexpr FStar_Pervasives_Native.option * mlexpr)
      Prims.list))
  = fun projectee -> match projectee with | MLE_Match _0 -> _0
let (uu___is_MLE_Coerce : mlexpr' -> Prims.bool) =
  fun projectee ->
    match projectee with | MLE_Coerce _0 -> true | uu____2158 -> false
let (__proj__MLE_Coerce__item___0 : mlexpr' -> (mlexpr * mlty * mlty)) =
  fun projectee -> match projectee with | MLE_Coerce _0 -> _0
let (uu___is_MLE_CTor : mlexpr' -> Prims.bool) =
  fun projectee ->
    match projectee with | MLE_CTor _0 -> true | uu____2201 -> false
let (__proj__MLE_CTor__item___0 : mlexpr' -> (mlpath * mlexpr Prims.list)) =
  fun projectee -> match projectee with | MLE_CTor _0 -> _0
let (uu___is_MLE_Seq : mlexpr' -> Prims.bool) =
  fun projectee ->
    match projectee with | MLE_Seq _0 -> true | uu____2240 -> false
let (__proj__MLE_Seq__item___0 : mlexpr' -> mlexpr Prims.list) =
  fun projectee -> match projectee with | MLE_Seq _0 -> _0
let (uu___is_MLE_Tuple : mlexpr' -> Prims.bool) =
  fun projectee ->
    match projectee with | MLE_Tuple _0 -> true | uu____2267 -> false
let (__proj__MLE_Tuple__item___0 : mlexpr' -> mlexpr Prims.list) =
  fun projectee -> match projectee with | MLE_Tuple _0 -> _0
let (uu___is_MLE_Record : mlexpr' -> Prims.bool) =
  fun projectee ->
    match projectee with | MLE_Record _0 -> true | uu____2306 -> false
let (__proj__MLE_Record__item___0 :
  mlexpr' -> (mlsymbol Prims.list * (mlsymbol * mlexpr) Prims.list)) =
  fun projectee -> match projectee with | MLE_Record _0 -> _0
let (uu___is_MLE_Proj : mlexpr' -> Prims.bool) =
  fun projectee ->
    match projectee with | MLE_Proj _0 -> true | uu____2371 -> false
let (__proj__MLE_Proj__item___0 : mlexpr' -> (mlexpr * mlpath)) =
  fun projectee -> match projectee with | MLE_Proj _0 -> _0
let (uu___is_MLE_If : mlexpr' -> Prims.bool) =
  fun projectee ->
    match projectee with | MLE_If _0 -> true | uu____2410 -> false
let (__proj__MLE_If__item___0 :
  mlexpr' -> (mlexpr * mlexpr * mlexpr FStar_Pervasives_Native.option)) =
  fun projectee -> match projectee with | MLE_If _0 -> _0
let (uu___is_MLE_Raise : mlexpr' -> Prims.bool) =
  fun projectee ->
    match projectee with | MLE_Raise _0 -> true | uu____2459 -> false
let (__proj__MLE_Raise__item___0 : mlexpr' -> (mlpath * mlexpr Prims.list)) =
  fun projectee -> match projectee with | MLE_Raise _0 -> _0
let (uu___is_MLE_Try : mlexpr' -> Prims.bool) =
  fun projectee ->
    match projectee with | MLE_Try _0 -> true | uu____2510 -> false
let (__proj__MLE_Try__item___0 :
  mlexpr' ->
    (mlexpr * (mlpattern * mlexpr FStar_Pervasives_Native.option * mlexpr)
      Prims.list))
  = fun projectee -> match projectee with | MLE_Try _0 -> _0
let (__proj__Mkmlexpr__item__expr : mlexpr -> mlexpr') =
  fun projectee -> match projectee with | { expr; mlty; loc;_} -> expr
let (__proj__Mkmlexpr__item__mlty : mlexpr -> mlty) =
  fun projectee -> match projectee with | { expr; mlty; loc;_} -> mlty
let (__proj__Mkmlexpr__item__loc : mlexpr -> mlloc) =
  fun projectee -> match projectee with | { expr; mlty; loc;_} -> loc
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
    match projectee with | MLTD_Abbrev _0 -> true | uu____2760 -> false
let (__proj__MLTD_Abbrev__item___0 : mltybody -> mlty) =
  fun projectee -> match projectee with | MLTD_Abbrev _0 -> _0
let (uu___is_MLTD_Record : mltybody -> Prims.bool) =
  fun projectee ->
    match projectee with | MLTD_Record _0 -> true | uu____2786 -> false
let (__proj__MLTD_Record__item___0 :
  mltybody -> (mlsymbol * mlty) Prims.list) =
  fun projectee -> match projectee with | MLTD_Record _0 -> _0
let (uu___is_MLTD_DType : mltybody -> Prims.bool) =
  fun projectee ->
    match projectee with | MLTD_DType _0 -> true | uu____2840 -> false
let (__proj__MLTD_DType__item___0 :
  mltybody -> (mlsymbol * (mlsymbol * mlty) Prims.list) Prims.list) =
  fun projectee -> match projectee with | MLTD_DType _0 -> _0
type one_mltydecl =
  (Prims.bool * mlsymbol * mlsymbol FStar_Pervasives_Native.option * mlidents
    * metadata * mltybody FStar_Pervasives_Native.option)
type mltydecl = one_mltydecl Prims.list
type mlmodule1 =
  | MLM_Ty of mltydecl 
  | MLM_Let of mlletbinding 
  | MLM_Exn of (mlsymbol * (mlsymbol * mlty) Prims.list) 
  | MLM_Top of mlexpr 
  | MLM_Loc of mlloc 
let (uu___is_MLM_Ty : mlmodule1 -> Prims.bool) =
  fun projectee ->
    match projectee with | MLM_Ty _0 -> true | uu____2959 -> false
let (__proj__MLM_Ty__item___0 : mlmodule1 -> mltydecl) =
  fun projectee -> match projectee with | MLM_Ty _0 -> _0
let (uu___is_MLM_Let : mlmodule1 -> Prims.bool) =
  fun projectee ->
    match projectee with | MLM_Let _0 -> true | uu____2978 -> false
let (__proj__MLM_Let__item___0 : mlmodule1 -> mlletbinding) =
  fun projectee -> match projectee with | MLM_Let _0 -> _0
let (uu___is_MLM_Exn : mlmodule1 -> Prims.bool) =
  fun projectee ->
    match projectee with | MLM_Exn _0 -> true | uu____3009 -> false
let (__proj__MLM_Exn__item___0 :
  mlmodule1 -> (mlsymbol * (mlsymbol * mlty) Prims.list)) =
  fun projectee -> match projectee with | MLM_Exn _0 -> _0
let (uu___is_MLM_Top : mlmodule1 -> Prims.bool) =
  fun projectee ->
    match projectee with | MLM_Top _0 -> true | uu____3064 -> false
let (__proj__MLM_Top__item___0 : mlmodule1 -> mlexpr) =
  fun projectee -> match projectee with | MLM_Top _0 -> _0
let (uu___is_MLM_Loc : mlmodule1 -> Prims.bool) =
  fun projectee ->
    match projectee with | MLM_Loc _0 -> true | uu____3083 -> false
let (__proj__MLM_Loc__item___0 : mlmodule1 -> mlloc) =
  fun projectee -> match projectee with | MLM_Loc _0 -> _0
type mlmodule = mlmodule1 Prims.list
type mlsig1 =
  | MLS_Mod of (mlsymbol * mlsig1 Prims.list) 
  | MLS_Ty of mltydecl 
  | MLS_Val of (mlsymbol * mltyscheme) 
  | MLS_Exn of (mlsymbol * mlty Prims.list) 
let (uu___is_MLS_Mod : mlsig1 -> Prims.bool) =
  fun projectee ->
    match projectee with | MLS_Mod _0 -> true | uu____3150 -> false
let (__proj__MLS_Mod__item___0 : mlsig1 -> (mlsymbol * mlsig1 Prims.list)) =
  fun projectee -> match projectee with | MLS_Mod _0 -> _0
let (uu___is_MLS_Ty : mlsig1 -> Prims.bool) =
  fun projectee ->
    match projectee with | MLS_Ty _0 -> true | uu____3190 -> false
let (__proj__MLS_Ty__item___0 : mlsig1 -> mltydecl) =
  fun projectee -> match projectee with | MLS_Ty _0 -> _0
let (uu___is_MLS_Val : mlsig1 -> Prims.bool) =
  fun projectee ->
    match projectee with | MLS_Val _0 -> true | uu____3214 -> false
let (__proj__MLS_Val__item___0 : mlsig1 -> (mlsymbol * mltyscheme)) =
  fun projectee -> match projectee with | MLS_Val _0 -> _0
let (uu___is_MLS_Exn : mlsig1 -> Prims.bool) =
  fun projectee ->
    match projectee with | MLS_Exn _0 -> true | uu____3255 -> false
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
      let obj_ns =
        let uu____3455 =
          let uu____3457 = FStar_Options.codegen () in
          uu____3457 = (FStar_Pervasives_Native.Some FStar_Options.FSharp) in
        if uu____3455 then "FSharp.Compatibility.OCaml.Obj" else "Obj" in
      let obj_repr =
        with_ty (MLTY_Fun (t, E_PURE, MLTY_Top))
          (MLE_Name ([obj_ns], "repr")) in
      with_ty_loc MLTY_Top (MLE_App (obj_repr, [x])) x.loc
let (avoid_keyword : Prims.string -> Prims.string) =
  fun s ->
    let uu____3487 = is_reserved s in
    if uu____3487 then Prims.op_Hat s "_" else s
let (bv_as_mlident : FStar_Syntax_Syntax.bv -> mlident) =
  fun x ->
    let uu____3502 =
      ((FStar_Util.starts_with
          (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
          FStar_Ident.reserved_prefix)
         || (FStar_Syntax_Syntax.is_null_bv x))
        || (is_reserved (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText) in
    if uu____3502
    then
      let uu____3506 =
        let uu____3508 =
          let uu____3510 =
            FStar_Util.string_of_int x.FStar_Syntax_Syntax.index in
          Prims.op_Hat "_" uu____3510 in
        Prims.op_Hat (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
          uu____3508 in
      FStar_All.pipe_left avoid_keyword uu____3506
    else
      FStar_All.pipe_left avoid_keyword
        (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
let (mlpath_of_lident : FStar_Ident.lident -> mlpath) =
  fun x ->
    let uu____3525 = FStar_Ident.lid_equals x FStar_Parser_Const.failwith_lid in
    if uu____3525
    then ([], ((x.FStar_Ident.ident).FStar_Ident.idText))
    else
      (let uu____3535 =
         FStar_List.map (fun x1 -> x1.FStar_Ident.idText) x.FStar_Ident.ns in
       let uu____3542 =
         avoid_keyword (x.FStar_Ident.ident).FStar_Ident.idText in
       (uu____3535, uu____3542))
let (push_unit : mltyscheme -> mltyscheme) =
  fun ts ->
    let uu____3554 = ts in
    match uu____3554 with
    | (vs, ty) -> (vs, (MLTY_Fun (ml_unit_ty, E_PURE, ty)))
let (pop_unit : mltyscheme -> mltyscheme) =
  fun ts ->
    let uu____3563 = ts in
    match uu____3563 with
    | (vs, ty) ->
        (match ty with
         | MLTY_Fun (l, E_PURE, t) ->
             if l = ml_unit_ty
             then (vs, t)
             else failwith "unexpected: pop_unit: domain was not unit"
         | uu____3572 -> failwith "unexpected: pop_unit: not a function type")