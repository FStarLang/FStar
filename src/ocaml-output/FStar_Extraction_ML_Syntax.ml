
open Prims
open FStar_Pervasives

type mlsymbol =
Prims.string


type mlident =
mlsymbol


type mlpath =
(mlsymbol Prims.list * mlsymbol)


let ocamlkeywords : Prims.string Prims.list = ("and")::("as")::("assert")::("asr")::("begin")::("class")::("constraint")::("do")::("done")::("downto")::("else")::("end")::("exception")::("external")::("false")::("for")::("fun")::("function")::("functor")::("if")::("in")::("include")::("inherit")::("initializer")::("land")::("lazy")::("let")::("lor")::("lsl")::("lsr")::("lxor")::("match")::("method")::("mod")::("module")::("mutable")::("new")::("object")::("of")::("open")::("or")::("private")::("rec")::("sig")::("struct")::("then")::("to")::("true")::("try")::("type")::("val")::("virtual")::("when")::("while")::("with")::("nonrec")::[]


let fsharpkeywords : Prims.string Prims.list = ("abstract")::("and")::("as")::("assert")::("base")::("begin")::("class")::("default")::("delegate")::("do")::("done")::("downcast")::("downto")::("elif")::("else")::("end")::("exception")::("extern")::("false")::("finally")::("fixed")::("for")::("fun")::("function")::("global")::("if")::("in")::("inherit")::("inline")::("interface")::("internal")::("lazy")::("let")::("let!")::("match")::("member")::("module")::("mutable")::("namespace")::("new")::("not")::("null")::("of")::("open")::("or")::("override")::("private")::("public")::("rec")::("return")::("return!")::("select")::("static")::("struct")::("then")::("to")::("true")::("try")::("type")::("upcast")::("use")::("use!")::("val")::("void")::("when")::("while")::("with")::("yield")::("yield!")::("asr")::("land")::("lor")::("lsl")::("lsr")::("lxor")::("mod")::("sig")::("atomic")::("break")::("checked")::("component")::("const")::("constraint")::("constructor")::("continue")::("eager")::("event")::("external")::("fixed")::("functor")::("include")::("method")::("mixin")::("object")::("parallel")::("process")::("protected")::("pure")::("sealed")::("tailcall")::("trait")::("virtual")::("volatile")::[]


let is_reserved : Prims.string  ->  Prims.bool = (fun k -> (

let reserved_keywords = (fun uu____366 -> (

let uu____367 = (

let uu____369 = (FStar_Options.codegen ())
in (Prims.op_Equality uu____369 (FStar_Pervasives_Native.Some (FStar_Options.FSharp))))
in (match (uu____367) with
| true -> begin
fsharpkeywords
end
| uu____378 -> begin
ocamlkeywords
end)))
in (

let uu____380 = (reserved_keywords ())
in (FStar_List.existsb (fun k' -> (Prims.op_Equality k' k)) uu____380))))


let string_of_mlpath : mlpath  ->  mlsymbol = (fun uu____395 -> (match (uu____395) with
| (p, s) -> begin
(FStar_String.concat "." (FStar_List.append p ((s)::[])))
end))


let gensym : unit  ->  Prims.string = (fun uu____418 -> (

let i = (FStar_Ident.next_id ())
in (

let uu____421 = (FStar_Util.string_of_int i)
in (Prims.op_Hat "_" uu____421))))


let rec gensyms : Prims.int  ->  Prims.string Prims.list = (fun x -> (match (x) with
| _438 when (_438 = (Prims.parse_int "0")) -> begin
[]
end
| n1 -> begin
(

let uu____442 = (gensym ())
in (

let uu____444 = (gensyms (n1 - (Prims.parse_int "1")))
in (uu____442)::uu____444))
end))


type mlidents =
mlident Prims.list


type mlsymbols =
mlsymbol Prims.list

type e_tag =
| E_PURE
| E_GHOST
| E_IMPURE


let uu___is_E_PURE : e_tag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| E_PURE -> begin
true
end
| uu____465 -> begin
false
end))


let uu___is_E_GHOST : e_tag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| E_GHOST -> begin
true
end
| uu____476 -> begin
false
end))


let uu___is_E_IMPURE : e_tag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| E_IMPURE -> begin
true
end
| uu____487 -> begin
false
end))


type mlloc =
(Prims.int * Prims.string)


let dummy_loc : mlloc = (((Prims.parse_int "0")), (""))

type mlty =
| MLTY_Var of mlident
| MLTY_Fun of (mlty * e_tag * mlty)
| MLTY_Named of (mlty Prims.list * mlpath)
| MLTY_Tuple of mlty Prims.list
| MLTY_Top
| MLTY_Erased


let uu___is_MLTY_Var : mlty  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MLTY_Var (_0) -> begin
true
end
| uu____546 -> begin
false
end))


let __proj__MLTY_Var__item___0 : mlty  ->  mlident = (fun projectee -> (match (projectee) with
| MLTY_Var (_0) -> begin
_0
end))


let uu___is_MLTY_Fun : mlty  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MLTY_Fun (_0) -> begin
true
end
| uu____574 -> begin
false
end))


let __proj__MLTY_Fun__item___0 : mlty  ->  (mlty * e_tag * mlty) = (fun projectee -> (match (projectee) with
| MLTY_Fun (_0) -> begin
_0
end))


let uu___is_MLTY_Named : mlty  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MLTY_Named (_0) -> begin
true
end
| uu____617 -> begin
false
end))


let __proj__MLTY_Named__item___0 : mlty  ->  (mlty Prims.list * mlpath) = (fun projectee -> (match (projectee) with
| MLTY_Named (_0) -> begin
_0
end))


let uu___is_MLTY_Tuple : mlty  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MLTY_Tuple (_0) -> begin
true
end
| uu____656 -> begin
false
end))


let __proj__MLTY_Tuple__item___0 : mlty  ->  mlty Prims.list = (fun projectee -> (match (projectee) with
| MLTY_Tuple (_0) -> begin
_0
end))


let uu___is_MLTY_Top : mlty  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MLTY_Top -> begin
true
end
| uu____680 -> begin
false
end))


let uu___is_MLTY_Erased : mlty  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MLTY_Erased -> begin
true
end
| uu____691 -> begin
false
end))


type mltyscheme =
(mlidents * mlty)

type mlconstant =
| MLC_Unit
| MLC_Bool of Prims.bool
| MLC_Int of (Prims.string * (FStar_Const.signedness * FStar_Const.width) FStar_Pervasives_Native.option)
| MLC_Float of FStar_BaseTypes.float
| MLC_Char of FStar_BaseTypes.char
| MLC_String of Prims.string
| MLC_Bytes of FStar_BaseTypes.byte Prims.array


let uu___is_MLC_Unit : mlconstant  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MLC_Unit -> begin
true
end
| uu____752 -> begin
false
end))


let uu___is_MLC_Bool : mlconstant  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MLC_Bool (_0) -> begin
true
end
| uu____765 -> begin
false
end))


let __proj__MLC_Bool__item___0 : mlconstant  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MLC_Bool (_0) -> begin
_0
end))


let uu___is_MLC_Int : mlconstant  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MLC_Int (_0) -> begin
true
end
| uu____798 -> begin
false
end))


let __proj__MLC_Int__item___0 : mlconstant  ->  (Prims.string * (FStar_Const.signedness * FStar_Const.width) FStar_Pervasives_Native.option) = (fun projectee -> (match (projectee) with
| MLC_Int (_0) -> begin
_0
end))


let uu___is_MLC_Float : mlconstant  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MLC_Float (_0) -> begin
true
end
| uu____850 -> begin
false
end))


let __proj__MLC_Float__item___0 : mlconstant  ->  FStar_BaseTypes.float = (fun projectee -> (match (projectee) with
| MLC_Float (_0) -> begin
_0
end))


let uu___is_MLC_Char : mlconstant  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MLC_Char (_0) -> begin
true
end
| uu____870 -> begin
false
end))


let __proj__MLC_Char__item___0 : mlconstant  ->  FStar_BaseTypes.char = (fun projectee -> (match (projectee) with
| MLC_Char (_0) -> begin
_0
end))


let uu___is_MLC_String : mlconstant  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MLC_String (_0) -> begin
true
end
| uu____893 -> begin
false
end))


let __proj__MLC_String__item___0 : mlconstant  ->  Prims.string = (fun projectee -> (match (projectee) with
| MLC_String (_0) -> begin
_0
end))


let uu___is_MLC_Bytes : mlconstant  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MLC_Bytes (_0) -> begin
true
end
| uu____917 -> begin
false
end))


let __proj__MLC_Bytes__item___0 : mlconstant  ->  FStar_BaseTypes.byte Prims.array = (fun projectee -> (match (projectee) with
| MLC_Bytes (_0) -> begin
_0
end))

type mlpattern =
| MLP_Wild
| MLP_Const of mlconstant
| MLP_Var of mlident
| MLP_CTor of (mlpath * mlpattern Prims.list)
| MLP_Branch of mlpattern Prims.list
| MLP_Record of (mlsymbol Prims.list * (mlsymbol * mlpattern) Prims.list)
| MLP_Tuple of mlpattern Prims.list


let uu___is_MLP_Wild : mlpattern  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MLP_Wild -> begin
true
end
| uu____996 -> begin
false
end))


let uu___is_MLP_Const : mlpattern  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MLP_Const (_0) -> begin
true
end
| uu____1008 -> begin
false
end))


let __proj__MLP_Const__item___0 : mlpattern  ->  mlconstant = (fun projectee -> (match (projectee) with
| MLP_Const (_0) -> begin
_0
end))


let uu___is_MLP_Var : mlpattern  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MLP_Var (_0) -> begin
true
end
| uu____1028 -> begin
false
end))


let __proj__MLP_Var__item___0 : mlpattern  ->  mlident = (fun projectee -> (match (projectee) with
| MLP_Var (_0) -> begin
_0
end))


let uu___is_MLP_CTor : mlpattern  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MLP_CTor (_0) -> begin
true
end
| uu____1056 -> begin
false
end))


let __proj__MLP_CTor__item___0 : mlpattern  ->  (mlpath * mlpattern Prims.list) = (fun projectee -> (match (projectee) with
| MLP_CTor (_0) -> begin
_0
end))


let uu___is_MLP_Branch : mlpattern  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MLP_Branch (_0) -> begin
true
end
| uu____1095 -> begin
false
end))


let __proj__MLP_Branch__item___0 : mlpattern  ->  mlpattern Prims.list = (fun projectee -> (match (projectee) with
| MLP_Branch (_0) -> begin
_0
end))


let uu___is_MLP_Record : mlpattern  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MLP_Record (_0) -> begin
true
end
| uu____1134 -> begin
false
end))


let __proj__MLP_Record__item___0 : mlpattern  ->  (mlsymbol Prims.list * (mlsymbol * mlpattern) Prims.list) = (fun projectee -> (match (projectee) with
| MLP_Record (_0) -> begin
_0
end))


let uu___is_MLP_Tuple : mlpattern  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MLP_Tuple (_0) -> begin
true
end
| uu____1197 -> begin
false
end))


let __proj__MLP_Tuple__item___0 : mlpattern  ->  mlpattern Prims.list = (fun projectee -> (match (projectee) with
| MLP_Tuple (_0) -> begin
_0
end))

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


let uu___is_Mutable : meta  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Mutable -> begin
true
end
| uu____1257 -> begin
false
end))


let uu___is_Assumed : meta  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Assumed -> begin
true
end
| uu____1268 -> begin
false
end))


let uu___is_Private : meta  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Private -> begin
true
end
| uu____1279 -> begin
false
end))


let uu___is_NoExtract : meta  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NoExtract -> begin
true
end
| uu____1290 -> begin
false
end))


let uu___is_CInline : meta  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CInline -> begin
true
end
| uu____1301 -> begin
false
end))


let uu___is_Substitute : meta  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Substitute -> begin
true
end
| uu____1312 -> begin
false
end))


let uu___is_GCType : meta  ->  Prims.bool = (fun projectee -> (match (projectee) with
| GCType -> begin
true
end
| uu____1323 -> begin
false
end))


let uu___is_PpxDerivingShow : meta  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PpxDerivingShow -> begin
true
end
| uu____1334 -> begin
false
end))


let uu___is_PpxDerivingShowConstant : meta  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PpxDerivingShowConstant (_0) -> begin
true
end
| uu____1347 -> begin
false
end))


let __proj__PpxDerivingShowConstant__item___0 : meta  ->  Prims.string = (fun projectee -> (match (projectee) with
| PpxDerivingShowConstant (_0) -> begin
_0
end))


let uu___is_PpxDerivingYoJson : meta  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PpxDerivingYoJson -> begin
true
end
| uu____1368 -> begin
false
end))


let uu___is_Comment : meta  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Comment (_0) -> begin
true
end
| uu____1381 -> begin
false
end))


let __proj__Comment__item___0 : meta  ->  Prims.string = (fun projectee -> (match (projectee) with
| Comment (_0) -> begin
_0
end))


let uu___is_StackInline : meta  ->  Prims.bool = (fun projectee -> (match (projectee) with
| StackInline -> begin
true
end
| uu____1402 -> begin
false
end))


let uu___is_CPrologue : meta  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CPrologue (_0) -> begin
true
end
| uu____1415 -> begin
false
end))


let __proj__CPrologue__item___0 : meta  ->  Prims.string = (fun projectee -> (match (projectee) with
| CPrologue (_0) -> begin
_0
end))


let uu___is_CEpilogue : meta  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CEpilogue (_0) -> begin
true
end
| uu____1438 -> begin
false
end))


let __proj__CEpilogue__item___0 : meta  ->  Prims.string = (fun projectee -> (match (projectee) with
| CEpilogue (_0) -> begin
_0
end))


let uu___is_CConst : meta  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CConst (_0) -> begin
true
end
| uu____1461 -> begin
false
end))


let __proj__CConst__item___0 : meta  ->  Prims.string = (fun projectee -> (match (projectee) with
| CConst (_0) -> begin
_0
end))


let uu___is_CCConv : meta  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CCConv (_0) -> begin
true
end
| uu____1484 -> begin
false
end))


let __proj__CCConv__item___0 : meta  ->  Prims.string = (fun projectee -> (match (projectee) with
| CCConv (_0) -> begin
_0
end))


let uu___is_Erased : meta  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Erased -> begin
true
end
| uu____1505 -> begin
false
end))


let uu___is_CAbstract : meta  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CAbstract -> begin
true
end
| uu____1516 -> begin
false
end))


let uu___is_CIfDef : meta  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CIfDef -> begin
true
end
| uu____1527 -> begin
false
end))


let uu___is_CMacro : meta  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CMacro -> begin
true
end
| uu____1538 -> begin
false
end))


type metadata =
meta Prims.list

type mlletflavor =
| Rec
| NonRec


let uu___is_Rec : mlletflavor  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Rec -> begin
true
end
| uu____1551 -> begin
false
end))


let uu___is_NonRec : mlletflavor  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NonRec -> begin
true
end
| uu____1562 -> begin
false
end))

type mlexpr' =
| MLE_Const of mlconstant
| MLE_Var of mlident
| MLE_Name of mlpath
| MLE_Let of ((mlletflavor * mllb Prims.list) * mlexpr)
| MLE_App of (mlexpr * mlexpr Prims.list)
| MLE_TApp of (mlexpr * mlty Prims.list)
| MLE_Fun of ((mlident * mlty) Prims.list * mlexpr)
| MLE_Match of (mlexpr * (mlpattern * mlexpr FStar_Pervasives_Native.option * mlexpr) Prims.list)
| MLE_Coerce of (mlexpr * mlty * mlty)
| MLE_CTor of (mlpath * mlexpr Prims.list)
| MLE_Seq of mlexpr Prims.list
| MLE_Tuple of mlexpr Prims.list
| MLE_Record of (mlsymbol Prims.list * (mlsymbol * mlexpr) Prims.list)
| MLE_Proj of (mlexpr * mlpath)
| MLE_If of (mlexpr * mlexpr * mlexpr FStar_Pervasives_Native.option)
| MLE_Raise of (mlpath * mlexpr Prims.list)
| MLE_Try of (mlexpr * (mlpattern * mlexpr FStar_Pervasives_Native.option * mlexpr) Prims.list) 
 and mlexpr =
{expr : mlexpr'; mlty : mlty; loc : mlloc} 
 and mllb =
{mllb_name : mlident; mllb_tysc : mltyscheme FStar_Pervasives_Native.option; mllb_add_unit : Prims.bool; mllb_def : mlexpr; mllb_meta : metadata; print_typ : Prims.bool}


let uu___is_MLE_Const : mlexpr'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MLE_Const (_0) -> begin
true
end
| uu____1819 -> begin
false
end))


let __proj__MLE_Const__item___0 : mlexpr'  ->  mlconstant = (fun projectee -> (match (projectee) with
| MLE_Const (_0) -> begin
_0
end))


let uu___is_MLE_Var : mlexpr'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MLE_Var (_0) -> begin
true
end
| uu____1839 -> begin
false
end))


let __proj__MLE_Var__item___0 : mlexpr'  ->  mlident = (fun projectee -> (match (projectee) with
| MLE_Var (_0) -> begin
_0
end))


let uu___is_MLE_Name : mlexpr'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MLE_Name (_0) -> begin
true
end
| uu____1861 -> begin
false
end))


let __proj__MLE_Name__item___0 : mlexpr'  ->  mlpath = (fun projectee -> (match (projectee) with
| MLE_Name (_0) -> begin
_0
end))


let uu___is_MLE_Let : mlexpr'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MLE_Let (_0) -> begin
true
end
| uu____1890 -> begin
false
end))


let __proj__MLE_Let__item___0 : mlexpr'  ->  ((mlletflavor * mllb Prims.list) * mlexpr) = (fun projectee -> (match (projectee) with
| MLE_Let (_0) -> begin
_0
end))


let uu___is_MLE_App : mlexpr'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MLE_App (_0) -> begin
true
end
| uu____1945 -> begin
false
end))


let __proj__MLE_App__item___0 : mlexpr'  ->  (mlexpr * mlexpr Prims.list) = (fun projectee -> (match (projectee) with
| MLE_App (_0) -> begin
_0
end))


let uu___is_MLE_TApp : mlexpr'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MLE_TApp (_0) -> begin
true
end
| uu____1988 -> begin
false
end))


let __proj__MLE_TApp__item___0 : mlexpr'  ->  (mlexpr * mlty Prims.list) = (fun projectee -> (match (projectee) with
| MLE_TApp (_0) -> begin
_0
end))


let uu___is_MLE_Fun : mlexpr'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MLE_Fun (_0) -> begin
true
end
| uu____2036 -> begin
false
end))


let __proj__MLE_Fun__item___0 : mlexpr'  ->  ((mlident * mlty) Prims.list * mlexpr) = (fun projectee -> (match (projectee) with
| MLE_Fun (_0) -> begin
_0
end))


let uu___is_MLE_Match : mlexpr'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MLE_Match (_0) -> begin
true
end
| uu____2102 -> begin
false
end))


let __proj__MLE_Match__item___0 : mlexpr'  ->  (mlexpr * (mlpattern * mlexpr FStar_Pervasives_Native.option * mlexpr) Prims.list) = (fun projectee -> (match (projectee) with
| MLE_Match (_0) -> begin
_0
end))


let uu___is_MLE_Coerce : mlexpr'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MLE_Coerce (_0) -> begin
true
end
| uu____2169 -> begin
false
end))


let __proj__MLE_Coerce__item___0 : mlexpr'  ->  (mlexpr * mlty * mlty) = (fun projectee -> (match (projectee) with
| MLE_Coerce (_0) -> begin
_0
end))


let uu___is_MLE_CTor : mlexpr'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MLE_CTor (_0) -> begin
true
end
| uu____2212 -> begin
false
end))


let __proj__MLE_CTor__item___0 : mlexpr'  ->  (mlpath * mlexpr Prims.list) = (fun projectee -> (match (projectee) with
| MLE_CTor (_0) -> begin
_0
end))


let uu___is_MLE_Seq : mlexpr'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MLE_Seq (_0) -> begin
true
end
| uu____2251 -> begin
false
end))


let __proj__MLE_Seq__item___0 : mlexpr'  ->  mlexpr Prims.list = (fun projectee -> (match (projectee) with
| MLE_Seq (_0) -> begin
_0
end))


let uu___is_MLE_Tuple : mlexpr'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MLE_Tuple (_0) -> begin
true
end
| uu____2278 -> begin
false
end))


let __proj__MLE_Tuple__item___0 : mlexpr'  ->  mlexpr Prims.list = (fun projectee -> (match (projectee) with
| MLE_Tuple (_0) -> begin
_0
end))


let uu___is_MLE_Record : mlexpr'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MLE_Record (_0) -> begin
true
end
| uu____2317 -> begin
false
end))


let __proj__MLE_Record__item___0 : mlexpr'  ->  (mlsymbol Prims.list * (mlsymbol * mlexpr) Prims.list) = (fun projectee -> (match (projectee) with
| MLE_Record (_0) -> begin
_0
end))


let uu___is_MLE_Proj : mlexpr'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MLE_Proj (_0) -> begin
true
end
| uu____2382 -> begin
false
end))


let __proj__MLE_Proj__item___0 : mlexpr'  ->  (mlexpr * mlpath) = (fun projectee -> (match (projectee) with
| MLE_Proj (_0) -> begin
_0
end))


let uu___is_MLE_If : mlexpr'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MLE_If (_0) -> begin
true
end
| uu____2421 -> begin
false
end))


let __proj__MLE_If__item___0 : mlexpr'  ->  (mlexpr * mlexpr * mlexpr FStar_Pervasives_Native.option) = (fun projectee -> (match (projectee) with
| MLE_If (_0) -> begin
_0
end))


let uu___is_MLE_Raise : mlexpr'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MLE_Raise (_0) -> begin
true
end
| uu____2470 -> begin
false
end))


let __proj__MLE_Raise__item___0 : mlexpr'  ->  (mlpath * mlexpr Prims.list) = (fun projectee -> (match (projectee) with
| MLE_Raise (_0) -> begin
_0
end))


let uu___is_MLE_Try : mlexpr'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MLE_Try (_0) -> begin
true
end
| uu____2521 -> begin
false
end))


let __proj__MLE_Try__item___0 : mlexpr'  ->  (mlexpr * (mlpattern * mlexpr FStar_Pervasives_Native.option * mlexpr) Prims.list) = (fun projectee -> (match (projectee) with
| MLE_Try (_0) -> begin
_0
end))


let __proj__Mkmlexpr__item__expr : mlexpr  ->  mlexpr' = (fun projectee -> (match (projectee) with
| {expr = expr; mlty = mlty; loc = loc} -> begin
expr
end))


let __proj__Mkmlexpr__item__mlty : mlexpr  ->  mlty = (fun projectee -> (match (projectee) with
| {expr = expr; mlty = mlty; loc = loc} -> begin
mlty
end))


let __proj__Mkmlexpr__item__loc : mlexpr  ->  mlloc = (fun projectee -> (match (projectee) with
| {expr = expr; mlty = mlty; loc = loc} -> begin
loc
end))


let __proj__Mkmllb__item__mllb_name : mllb  ->  mlident = (fun projectee -> (match (projectee) with
| {mllb_name = mllb_name; mllb_tysc = mllb_tysc; mllb_add_unit = mllb_add_unit; mllb_def = mllb_def; mllb_meta = mllb_meta; print_typ = print_typ} -> begin
mllb_name
end))


let __proj__Mkmllb__item__mllb_tysc : mllb  ->  mltyscheme FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {mllb_name = mllb_name; mllb_tysc = mllb_tysc; mllb_add_unit = mllb_add_unit; mllb_def = mllb_def; mllb_meta = mllb_meta; print_typ = print_typ} -> begin
mllb_tysc
end))


let __proj__Mkmllb__item__mllb_add_unit : mllb  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {mllb_name = mllb_name; mllb_tysc = mllb_tysc; mllb_add_unit = mllb_add_unit; mllb_def = mllb_def; mllb_meta = mllb_meta; print_typ = print_typ} -> begin
mllb_add_unit
end))


let __proj__Mkmllb__item__mllb_def : mllb  ->  mlexpr = (fun projectee -> (match (projectee) with
| {mllb_name = mllb_name; mllb_tysc = mllb_tysc; mllb_add_unit = mllb_add_unit; mllb_def = mllb_def; mllb_meta = mllb_meta; print_typ = print_typ} -> begin
mllb_def
end))


let __proj__Mkmllb__item__mllb_meta : mllb  ->  metadata = (fun projectee -> (match (projectee) with
| {mllb_name = mllb_name; mllb_tysc = mllb_tysc; mllb_add_unit = mllb_add_unit; mllb_def = mllb_def; mllb_meta = mllb_meta; print_typ = print_typ} -> begin
mllb_meta
end))


let __proj__Mkmllb__item__print_typ : mllb  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {mllb_name = mllb_name; mllb_tysc = mllb_tysc; mllb_add_unit = mllb_add_unit; mllb_def = mllb_def; mllb_meta = mllb_meta; print_typ = print_typ} -> begin
print_typ
end))


type mlbranch =
(mlpattern * mlexpr FStar_Pervasives_Native.option * mlexpr)


type mlletbinding =
(mlletflavor * mllb Prims.list)

type mltybody =
| MLTD_Abbrev of mlty
| MLTD_Record of (mlsymbol * mlty) Prims.list
| MLTD_DType of (mlsymbol * (mlsymbol * mlty) Prims.list) Prims.list


let uu___is_MLTD_Abbrev : mltybody  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MLTD_Abbrev (_0) -> begin
true
end
| uu____2771 -> begin
false
end))


let __proj__MLTD_Abbrev__item___0 : mltybody  ->  mlty = (fun projectee -> (match (projectee) with
| MLTD_Abbrev (_0) -> begin
_0
end))


let uu___is_MLTD_Record : mltybody  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MLTD_Record (_0) -> begin
true
end
| uu____2797 -> begin
false
end))


let __proj__MLTD_Record__item___0 : mltybody  ->  (mlsymbol * mlty) Prims.list = (fun projectee -> (match (projectee) with
| MLTD_Record (_0) -> begin
_0
end))


let uu___is_MLTD_DType : mltybody  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MLTD_DType (_0) -> begin
true
end
| uu____2851 -> begin
false
end))


let __proj__MLTD_DType__item___0 : mltybody  ->  (mlsymbol * (mlsymbol * mlty) Prims.list) Prims.list = (fun projectee -> (match (projectee) with
| MLTD_DType (_0) -> begin
_0
end))


type one_mltydecl =
(Prims.bool * mlsymbol * mlsymbol FStar_Pervasives_Native.option * mlidents * metadata * mltybody FStar_Pervasives_Native.option)


type mltydecl =
one_mltydecl Prims.list

type mlmodule1 =
| MLM_Ty of mltydecl
| MLM_Let of mlletbinding
| MLM_Exn of (mlsymbol * (mlsymbol * mlty) Prims.list)
| MLM_Top of mlexpr
| MLM_Loc of mlloc


let uu___is_MLM_Ty : mlmodule1  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MLM_Ty (_0) -> begin
true
end
| uu____2970 -> begin
false
end))


let __proj__MLM_Ty__item___0 : mlmodule1  ->  mltydecl = (fun projectee -> (match (projectee) with
| MLM_Ty (_0) -> begin
_0
end))


let uu___is_MLM_Let : mlmodule1  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MLM_Let (_0) -> begin
true
end
| uu____2989 -> begin
false
end))


let __proj__MLM_Let__item___0 : mlmodule1  ->  mlletbinding = (fun projectee -> (match (projectee) with
| MLM_Let (_0) -> begin
_0
end))


let uu___is_MLM_Exn : mlmodule1  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MLM_Exn (_0) -> begin
true
end
| uu____3020 -> begin
false
end))


let __proj__MLM_Exn__item___0 : mlmodule1  ->  (mlsymbol * (mlsymbol * mlty) Prims.list) = (fun projectee -> (match (projectee) with
| MLM_Exn (_0) -> begin
_0
end))


let uu___is_MLM_Top : mlmodule1  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MLM_Top (_0) -> begin
true
end
| uu____3075 -> begin
false
end))


let __proj__MLM_Top__item___0 : mlmodule1  ->  mlexpr = (fun projectee -> (match (projectee) with
| MLM_Top (_0) -> begin
_0
end))


let uu___is_MLM_Loc : mlmodule1  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MLM_Loc (_0) -> begin
true
end
| uu____3094 -> begin
false
end))


let __proj__MLM_Loc__item___0 : mlmodule1  ->  mlloc = (fun projectee -> (match (projectee) with
| MLM_Loc (_0) -> begin
_0
end))


type mlmodule =
mlmodule1 Prims.list

type mlsig1 =
| MLS_Mod of (mlsymbol * mlsig1 Prims.list)
| MLS_Ty of mltydecl
| MLS_Val of (mlsymbol * mltyscheme)
| MLS_Exn of (mlsymbol * mlty Prims.list)


let uu___is_MLS_Mod : mlsig1  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MLS_Mod (_0) -> begin
true
end
| uu____3161 -> begin
false
end))


let __proj__MLS_Mod__item___0 : mlsig1  ->  (mlsymbol * mlsig1 Prims.list) = (fun projectee -> (match (projectee) with
| MLS_Mod (_0) -> begin
_0
end))


let uu___is_MLS_Ty : mlsig1  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MLS_Ty (_0) -> begin
true
end
| uu____3201 -> begin
false
end))


let __proj__MLS_Ty__item___0 : mlsig1  ->  mltydecl = (fun projectee -> (match (projectee) with
| MLS_Ty (_0) -> begin
_0
end))


let uu___is_MLS_Val : mlsig1  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MLS_Val (_0) -> begin
true
end
| uu____3225 -> begin
false
end))


let __proj__MLS_Val__item___0 : mlsig1  ->  (mlsymbol * mltyscheme) = (fun projectee -> (match (projectee) with
| MLS_Val (_0) -> begin
_0
end))


let uu___is_MLS_Exn : mlsig1  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MLS_Exn (_0) -> begin
true
end
| uu____3266 -> begin
false
end))


let __proj__MLS_Exn__item___0 : mlsig1  ->  (mlsymbol * mlty Prims.list) = (fun projectee -> (match (projectee) with
| MLS_Exn (_0) -> begin
_0
end))


type mlsig =
mlsig1 Prims.list


let with_ty_loc : mlty  ->  mlexpr'  ->  mlloc  ->  mlexpr = (fun t e l -> {expr = e; mlty = t; loc = l})


let with_ty : mlty  ->  mlexpr'  ->  mlexpr = (fun t e -> (with_ty_loc t e dummy_loc))

type mllib =
| MLLib of (mlpath * (mlsig * mlmodule) FStar_Pervasives_Native.option * mllib) Prims.list


let uu___is_MLLib : mllib  ->  Prims.bool = (fun projectee -> true)


let __proj__MLLib__item___0 : mllib  ->  (mlpath * (mlsig * mlmodule) FStar_Pervasives_Native.option * mllib) Prims.list = (fun projectee -> (match (projectee) with
| MLLib (_0) -> begin
_0
end))


let ml_unit_ty : mlty = MLTY_Erased


let ml_bool_ty : mlty = MLTY_Named ((([]), (((("Prims")::[]), ("bool")))))


let ml_int_ty : mlty = MLTY_Named ((([]), (((("Prims")::[]), ("int")))))


let ml_string_ty : mlty = MLTY_Named ((([]), (((("Prims")::[]), ("string")))))


let ml_unit : mlexpr = (with_ty ml_unit_ty (MLE_Const (MLC_Unit)))


let mlp_lalloc : (Prims.string Prims.list * Prims.string) = ((("SST")::[]), ("lalloc"))


let apply_obj_repr : mlexpr  ->  mlty  ->  mlexpr = (fun x t -> (

let obj_ns = (

let uu____3466 = (

let uu____3468 = (FStar_Options.codegen ())
in (Prims.op_Equality uu____3468 (FStar_Pervasives_Native.Some (FStar_Options.FSharp))))
in (match (uu____3466) with
| true -> begin
"FSharp.Compatibility.OCaml.Obj"
end
| uu____3476 -> begin
"Obj"
end))
in (

let obj_repr = (with_ty (MLTY_Fun (((t), (E_PURE), (MLTY_Top)))) (MLE_Name ((((obj_ns)::[]), ("repr")))))
in (with_ty_loc MLTY_Top (MLE_App (((obj_repr), ((x)::[])))) x.loc))))


let avoid_keyword : Prims.string  ->  Prims.string = (fun s -> (

let uu____3498 = (is_reserved s)
in (match (uu____3498) with
| true -> begin
(Prims.op_Hat s "_")
end
| uu____3503 -> begin
s
end)))


let bv_as_mlident : FStar_Syntax_Syntax.bv  ->  mlident = (fun x -> (

let uu____3513 = (((FStar_Util.starts_with x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText FStar_Ident.reserved_prefix) || (FStar_Syntax_Syntax.is_null_bv x)) || (is_reserved x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText))
in (match (uu____3513) with
| true -> begin
(

let uu____3517 = (

let uu____3519 = (

let uu____3521 = (FStar_Util.string_of_int x.FStar_Syntax_Syntax.index)
in (Prims.op_Hat "_" uu____3521))
in (Prims.op_Hat x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText uu____3519))
in (FStar_All.pipe_left avoid_keyword uu____3517))
end
| uu____3526 -> begin
(FStar_All.pipe_left avoid_keyword x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText)
end)))


let mlpath_of_lident : FStar_Ident.lident  ->  mlpath = (fun x -> (

let uu____3536 = (FStar_Ident.lid_equals x FStar_Parser_Const.failwith_lid)
in (match (uu____3536) with
| true -> begin
(([]), (x.FStar_Ident.ident.FStar_Ident.idText))
end
| uu____3544 -> begin
(

let uu____3546 = (FStar_List.map (fun x1 -> x1.FStar_Ident.idText) x.FStar_Ident.ns)
in (

let uu____3553 = (avoid_keyword x.FStar_Ident.ident.FStar_Ident.idText)
in ((uu____3546), (uu____3553))))
end)))


let push_unit : mltyscheme  ->  mltyscheme = (fun ts -> (

let uu____3565 = ts
in (match (uu____3565) with
| (vs, ty) -> begin
((vs), (MLTY_Fun (((ml_unit_ty), (E_PURE), (ty)))))
end)))


let pop_unit : mltyscheme  ->  mltyscheme = (fun ts -> (

let uu____3574 = ts
in (match (uu____3574) with
| (vs, ty) -> begin
(match (ty) with
| MLTY_Fun (l, E_PURE, t) -> begin
(match ((Prims.op_Equality l ml_unit_ty)) with
| true -> begin
((vs), (t))
end
| uu____3580 -> begin
(failwith "unexpected: pop_unit: domain was not unit")
end)
end
| uu____3583 -> begin
(failwith "unexpected: pop_unit: not a function type")
end)
end)))




