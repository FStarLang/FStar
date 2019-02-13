
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

let reserved_keywords = (fun uu____359 -> (

let uu____360 = (

let uu____362 = (FStar_Options.codegen ())
in (Prims.op_Equality uu____362 (FStar_Pervasives_Native.Some (FStar_Options.FSharp))))
in (match (uu____360) with
| true -> begin
fsharpkeywords
end
| uu____371 -> begin
ocamlkeywords
end)))
in (

let uu____373 = (reserved_keywords ())
in (FStar_List.existsb (fun k' -> (Prims.op_Equality k' k)) uu____373))))


let string_of_mlpath : mlpath  ->  mlsymbol = (fun uu____388 -> (match (uu____388) with
| (p, s) -> begin
(FStar_String.concat "." (FStar_List.append p ((s)::[])))
end))

type gensym_t =
{gensym : unit  ->  mlident; reset : unit  ->  unit}


let __proj__Mkgensym_t__item__gensym : gensym_t  ->  unit  ->  mlident = (fun projectee -> (match (projectee) with
| {gensym = gensym; reset = reset} -> begin
gensym
end))


let __proj__Mkgensym_t__item__reset : gensym_t  ->  unit  ->  unit = (fun projectee -> (match (projectee) with
| {gensym = gensym; reset = reset} -> begin
reset
end))


let gs : gensym_t = (

let ctr = (FStar_Util.mk_ref (Prims.parse_int "0"))
in (

let n_resets = (FStar_Util.mk_ref (Prims.parse_int "0"))
in {gensym = (fun uu____491 -> ((FStar_Util.incr ctr);
(

let uu____526 = (

let uu____528 = (

let uu____530 = (FStar_ST.op_Bang n_resets)
in (FStar_Util.string_of_int uu____530))
in (

let uu____575 = (

let uu____577 = (

let uu____579 = (FStar_ST.op_Bang ctr)
in (FStar_Util.string_of_int uu____579))
in (Prims.strcat "_" uu____577))
in (Prims.strcat uu____528 uu____575)))
in (Prims.strcat "_" uu____526));
)); reset = (fun uu____628 -> ((FStar_ST.op_Colon_Equals ctr (Prims.parse_int "0"));
(FStar_Util.incr n_resets);
))}))


let gensym : unit  ->  mlident = (fun uu____713 -> (gs.gensym ()))


let reset_gensym : unit  ->  unit = (fun uu____719 -> (gs.reset ()))


let rec gensyms : Prims.int  ->  mlident Prims.list = (fun x -> (match (x) with
| _0_1 when (_0_1 = (Prims.parse_int "0")) -> begin
[]
end
| n1 -> begin
(

let uu____737 = (gensym ())
in (

let uu____739 = (gensyms (n1 - (Prims.parse_int "1")))
in (uu____737)::uu____739))
end))


let mlpath_of_lident : FStar_Ident.lident  ->  mlpath = (fun x -> (

let uu____751 = (FStar_Ident.lid_equals x FStar_Parser_Const.failwith_lid)
in (match (uu____751) with
| true -> begin
(([]), (x.FStar_Ident.ident.FStar_Ident.idText))
end
| uu____759 -> begin
(

let uu____761 = (FStar_List.map (fun x1 -> x1.FStar_Ident.idText) x.FStar_Ident.ns)
in ((uu____761), (x.FStar_Ident.ident.FStar_Ident.idText)))
end)))


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
| uu____787 -> begin
false
end))


let uu___is_E_GHOST : e_tag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| E_GHOST -> begin
true
end
| uu____798 -> begin
false
end))


let uu___is_E_IMPURE : e_tag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| E_IMPURE -> begin
true
end
| uu____809 -> begin
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
| uu____868 -> begin
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
| uu____897 -> begin
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
| uu____941 -> begin
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
| uu____981 -> begin
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
| uu____1006 -> begin
false
end))


let uu___is_MLTY_Erased : mlty  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MLTY_Erased -> begin
true
end
| uu____1017 -> begin
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
| uu____1078 -> begin
false
end))


let uu___is_MLC_Bool : mlconstant  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MLC_Bool (_0) -> begin
true
end
| uu____1091 -> begin
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
| uu____1125 -> begin
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
| uu____1178 -> begin
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
| uu____1199 -> begin
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
| uu____1223 -> begin
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
| uu____1248 -> begin
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
| uu____1328 -> begin
false
end))


let uu___is_MLP_Const : mlpattern  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MLP_Const (_0) -> begin
true
end
| uu____1340 -> begin
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
| uu____1361 -> begin
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
| uu____1390 -> begin
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
| uu____1430 -> begin
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
| uu____1470 -> begin
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
| uu____1534 -> begin
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


let uu___is_Mutable : meta  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Mutable -> begin
true
end
| uu____1595 -> begin
false
end))


let uu___is_Assumed : meta  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Assumed -> begin
true
end
| uu____1606 -> begin
false
end))


let uu___is_Private : meta  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Private -> begin
true
end
| uu____1617 -> begin
false
end))


let uu___is_NoExtract : meta  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NoExtract -> begin
true
end
| uu____1628 -> begin
false
end))


let uu___is_CInline : meta  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CInline -> begin
true
end
| uu____1639 -> begin
false
end))


let uu___is_Substitute : meta  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Substitute -> begin
true
end
| uu____1650 -> begin
false
end))


let uu___is_GCType : meta  ->  Prims.bool = (fun projectee -> (match (projectee) with
| GCType -> begin
true
end
| uu____1661 -> begin
false
end))


let uu___is_PpxDerivingShow : meta  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PpxDerivingShow -> begin
true
end
| uu____1672 -> begin
false
end))


let uu___is_PpxDerivingShowConstant : meta  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PpxDerivingShowConstant (_0) -> begin
true
end
| uu____1685 -> begin
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
| uu____1707 -> begin
false
end))


let uu___is_Comment : meta  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Comment (_0) -> begin
true
end
| uu____1720 -> begin
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
| uu____1742 -> begin
false
end))


let uu___is_CPrologue : meta  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CPrologue (_0) -> begin
true
end
| uu____1755 -> begin
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
| uu____1779 -> begin
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
| uu____1803 -> begin
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
| uu____1827 -> begin
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
| uu____1849 -> begin
false
end))


let uu___is_CAbstract : meta  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CAbstract -> begin
true
end
| uu____1860 -> begin
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
| uu____1873 -> begin
false
end))


let uu___is_NonRec : mlletflavor  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NonRec -> begin
true
end
| uu____1884 -> begin
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
| uu____2141 -> begin
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
| uu____2162 -> begin
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
| uu____2185 -> begin
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
| uu____2215 -> begin
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
| uu____2271 -> begin
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
| uu____2315 -> begin
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
| uu____2364 -> begin
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
| uu____2431 -> begin
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
| uu____2499 -> begin
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
| uu____2543 -> begin
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
| uu____2583 -> begin
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
| uu____2611 -> begin
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
| uu____2651 -> begin
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
| uu____2717 -> begin
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
| uu____2757 -> begin
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
| uu____2807 -> begin
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
| uu____2859 -> begin
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
| uu____3110 -> begin
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
| uu____3137 -> begin
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
| uu____3192 -> begin
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
| uu____3312 -> begin
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
| uu____3332 -> begin
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
| uu____3364 -> begin
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
| uu____3420 -> begin
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
| uu____3440 -> begin
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
| uu____3508 -> begin
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
| uu____3549 -> begin
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
| uu____3574 -> begin
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
| uu____3616 -> begin
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

let uu____3817 = (

let uu____3819 = (FStar_Options.codegen ())
in (Prims.op_Equality uu____3819 (FStar_Pervasives_Native.Some (FStar_Options.FSharp))))
in (match (uu____3817) with
| true -> begin
"FSharp.Compatibility.OCaml.Obj"
end
| uu____3827 -> begin
"Obj"
end))
in (

let obj_repr = (with_ty (MLTY_Fun (((t), (E_PURE), (MLTY_Top)))) (MLE_Name ((((obj_ns)::[]), ("repr")))))
in (with_ty_loc MLTY_Top (MLE_App (((obj_repr), ((x)::[])))) x.loc))))


let avoid_keyword : Prims.string  ->  Prims.string = (fun s -> (

let uu____3849 = (is_reserved s)
in (match (uu____3849) with
| true -> begin
(Prims.strcat s "_")
end
| uu____3854 -> begin
s
end)))


let bv_as_mlident : FStar_Syntax_Syntax.bv  ->  mlident = (fun x -> (

let uu____3864 = (((FStar_Util.starts_with x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText FStar_Ident.reserved_prefix) || (FStar_Syntax_Syntax.is_null_bv x)) || (is_reserved x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText))
in (match (uu____3864) with
| true -> begin
(

let uu____3868 = (

let uu____3870 = (

let uu____3872 = (FStar_Util.string_of_int x.FStar_Syntax_Syntax.index)
in (Prims.strcat "_" uu____3872))
in (Prims.strcat x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText uu____3870))
in (FStar_All.pipe_left avoid_keyword uu____3868))
end
| uu____3877 -> begin
(FStar_All.pipe_left avoid_keyword x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText)
end)))


let push_unit : mltyscheme  ->  mltyscheme = (fun ts -> (

let uu____3887 = ts
in (match (uu____3887) with
| (vs, ty) -> begin
((vs), (MLTY_Fun (((ml_unit_ty), (E_PURE), (ty)))))
end)))


let pop_unit : mltyscheme  ->  mltyscheme = (fun ts -> (

let uu____3896 = ts
in (match (uu____3896) with
| (vs, ty) -> begin
(match (ty) with
| MLTY_Fun (l, E_PURE, t) -> begin
(match ((Prims.op_Equality l ml_unit_ty)) with
| true -> begin
((vs), (t))
end
| uu____3902 -> begin
(failwith "unexpected: pop_unit: domain was not unit")
end)
end
| uu____3905 -> begin
(failwith "unexpected: pop_unit: not a function type")
end)
end)))




