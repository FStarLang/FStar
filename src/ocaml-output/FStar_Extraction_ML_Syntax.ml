
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

let reserved_keywords = (fun uu____23 -> (

let uu____24 = (

let uu____25 = (FStar_Options.codegen ())
in (Prims.op_Equality uu____25 (FStar_Pervasives_Native.Some (FStar_Options.FSharp))))
in (match (uu____24) with
| true -> begin
fsharpkeywords
end
| uu____32 -> begin
ocamlkeywords
end)))
in (

let uu____33 = (reserved_keywords ())
in (FStar_List.existsb (fun k' -> (Prims.op_Equality k' k)) uu____33))))


let string_of_mlpath : mlpath  ->  mlsymbol = (fun uu____42 -> (match (uu____42) with
| (p, s) -> begin
(FStar_String.concat "." (FStar_List.append p ((s)::[])))
end))

type gensym_t =
{gensym : unit  ->  mlident; reset : unit  ->  unit}


let __proj__Mkgensym_t__item__gensym : gensym_t  ->  unit  ->  mlident = (fun projectee -> (match (projectee) with
| {gensym = __fname__gensym; reset = __fname__reset} -> begin
__fname__gensym
end))


let __proj__Mkgensym_t__item__reset : gensym_t  ->  unit  ->  unit = (fun projectee -> (match (projectee) with
| {gensym = __fname__gensym; reset = __fname__reset} -> begin
__fname__reset
end))


let gs : gensym_t = (

let ctr = (FStar_Util.mk_ref (Prims.parse_int "0"))
in (

let n_resets = (FStar_Util.mk_ref (Prims.parse_int "0"))
in {gensym = (fun uu____121 -> ((FStar_Util.incr ctr);
(

let uu____156 = (

let uu____157 = (

let uu____158 = (FStar_ST.op_Bang n_resets)
in (FStar_Util.string_of_int uu____158))
in (

let uu____200 = (

let uu____201 = (

let uu____202 = (FStar_ST.op_Bang ctr)
in (FStar_Util.string_of_int uu____202))
in (Prims.strcat "_" uu____201))
in (Prims.strcat uu____157 uu____200)))
in (Prims.strcat "_" uu____156));
)); reset = (fun uu____246 -> ((FStar_ST.op_Colon_Equals ctr (Prims.parse_int "0"));
(FStar_Util.incr n_resets);
))}))


let gensym : unit  ->  mlident = (fun uu____326 -> (gs.gensym ()))


let reset_gensym : unit  ->  unit = (fun uu____331 -> (gs.reset ()))


let rec gensyms : Prims.int  ->  mlident Prims.list = (fun x -> (match (x) with
| _0_4 when (_0_4 = (Prims.parse_int "0")) -> begin
[]
end
| n1 -> begin
(

let uu____342 = (gensym ())
in (

let uu____343 = (gensyms (n1 - (Prims.parse_int "1")))
in (uu____342)::uu____343))
end))


let mlpath_of_lident : FStar_Ident.lident  ->  mlpath = (fun x -> (

let uu____351 = (FStar_Ident.lid_equals x FStar_Parser_Const.failwith_lid)
in (match (uu____351) with
| true -> begin
(([]), (x.FStar_Ident.ident.FStar_Ident.idText))
end
| uu____354 -> begin
(

let uu____355 = (FStar_List.map (fun x1 -> x1.FStar_Ident.idText) x.FStar_Ident.ns)
in ((uu____355), (x.FStar_Ident.ident.FStar_Ident.idText)))
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
| uu____371 -> begin
false
end))


let uu___is_E_GHOST : e_tag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| E_GHOST -> begin
true
end
| uu____377 -> begin
false
end))


let uu___is_E_IMPURE : e_tag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| E_IMPURE -> begin
true
end
| uu____383 -> begin
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
| uu____428 -> begin
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
| uu____448 -> begin
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
| uu____486 -> begin
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
| uu____520 -> begin
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
| uu____539 -> begin
false
end))


let uu___is_MLTY_Erased : mlty  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MLTY_Erased -> begin
true
end
| uu____545 -> begin
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
| uu____599 -> begin
false
end))


let uu___is_MLC_Bool : mlconstant  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MLC_Bool (_0) -> begin
true
end
| uu____606 -> begin
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
| uu____630 -> begin
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
| uu____674 -> begin
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
| uu____689 -> begin
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
| uu____706 -> begin
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
| uu____723 -> begin
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
| uu____797 -> begin
false
end))


let uu___is_MLP_Const : mlpattern  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MLP_Const (_0) -> begin
true
end
| uu____804 -> begin
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
| uu____818 -> begin
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
| uu____838 -> begin
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
| uu____872 -> begin
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
| uu____904 -> begin
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
| uu____956 -> begin
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


let uu___is_Mutable : meta  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Mutable -> begin
true
end
| uu____1005 -> begin
false
end))


let uu___is_Assumed : meta  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Assumed -> begin
true
end
| uu____1011 -> begin
false
end))


let uu___is_Private : meta  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Private -> begin
true
end
| uu____1017 -> begin
false
end))


let uu___is_NoExtract : meta  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NoExtract -> begin
true
end
| uu____1023 -> begin
false
end))


let uu___is_CInline : meta  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CInline -> begin
true
end
| uu____1029 -> begin
false
end))


let uu___is_Substitute : meta  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Substitute -> begin
true
end
| uu____1035 -> begin
false
end))


let uu___is_GCType : meta  ->  Prims.bool = (fun projectee -> (match (projectee) with
| GCType -> begin
true
end
| uu____1041 -> begin
false
end))


let uu___is_PpxDerivingShow : meta  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PpxDerivingShow -> begin
true
end
| uu____1047 -> begin
false
end))


let uu___is_PpxDerivingShowConstant : meta  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PpxDerivingShowConstant (_0) -> begin
true
end
| uu____1054 -> begin
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
| uu____1067 -> begin
false
end))


let uu___is_Comment : meta  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Comment (_0) -> begin
true
end
| uu____1074 -> begin
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
| uu____1087 -> begin
false
end))


let uu___is_CPrologue : meta  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CPrologue (_0) -> begin
true
end
| uu____1094 -> begin
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
| uu____1108 -> begin
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
| uu____1122 -> begin
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
| uu____1136 -> begin
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
| uu____1149 -> begin
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
| uu____1157 -> begin
false
end))


let uu___is_NonRec : mlletflavor  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NonRec -> begin
true
end
| uu____1163 -> begin
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
| uu____1408 -> begin
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
| uu____1422 -> begin
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
| uu____1436 -> begin
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
| uu____1460 -> begin
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
| uu____1510 -> begin
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
| uu____1548 -> begin
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
| uu____1590 -> begin
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
| uu____1648 -> begin
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
| uu____1710 -> begin
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
| uu____1748 -> begin
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
| uu____1782 -> begin
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
| uu____1804 -> begin
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
| uu____1836 -> begin
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
| uu____1890 -> begin
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
| uu____1924 -> begin
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
| uu____1968 -> begin
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
| uu____2014 -> begin
false
end))


let __proj__MLE_Try__item___0 : mlexpr'  ->  (mlexpr * (mlpattern * mlexpr FStar_Pervasives_Native.option * mlexpr) Prims.list) = (fun projectee -> (match (projectee) with
| MLE_Try (_0) -> begin
_0
end))


let __proj__Mkmlexpr__item__expr : mlexpr  ->  mlexpr' = (fun projectee -> (match (projectee) with
| {expr = __fname__expr; mlty = __fname__mlty; loc = __fname__loc} -> begin
__fname__expr
end))


let __proj__Mkmlexpr__item__mlty : mlexpr  ->  mlty = (fun projectee -> (match (projectee) with
| {expr = __fname__expr; mlty = __fname__mlty; loc = __fname__loc} -> begin
__fname__mlty
end))


let __proj__Mkmlexpr__item__loc : mlexpr  ->  mlloc = (fun projectee -> (match (projectee) with
| {expr = __fname__expr; mlty = __fname__mlty; loc = __fname__loc} -> begin
__fname__loc
end))


let __proj__Mkmllb__item__mllb_name : mllb  ->  mlident = (fun projectee -> (match (projectee) with
| {mllb_name = __fname__mllb_name; mllb_tysc = __fname__mllb_tysc; mllb_add_unit = __fname__mllb_add_unit; mllb_def = __fname__mllb_def; mllb_meta = __fname__mllb_meta; print_typ = __fname__print_typ} -> begin
__fname__mllb_name
end))


let __proj__Mkmllb__item__mllb_tysc : mllb  ->  mltyscheme FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {mllb_name = __fname__mllb_name; mllb_tysc = __fname__mllb_tysc; mllb_add_unit = __fname__mllb_add_unit; mllb_def = __fname__mllb_def; mllb_meta = __fname__mllb_meta; print_typ = __fname__print_typ} -> begin
__fname__mllb_tysc
end))


let __proj__Mkmllb__item__mllb_add_unit : mllb  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {mllb_name = __fname__mllb_name; mllb_tysc = __fname__mllb_tysc; mllb_add_unit = __fname__mllb_add_unit; mllb_def = __fname__mllb_def; mllb_meta = __fname__mllb_meta; print_typ = __fname__print_typ} -> begin
__fname__mllb_add_unit
end))


let __proj__Mkmllb__item__mllb_def : mllb  ->  mlexpr = (fun projectee -> (match (projectee) with
| {mllb_name = __fname__mllb_name; mllb_tysc = __fname__mllb_tysc; mllb_add_unit = __fname__mllb_add_unit; mllb_def = __fname__mllb_def; mllb_meta = __fname__mllb_meta; print_typ = __fname__print_typ} -> begin
__fname__mllb_def
end))


let __proj__Mkmllb__item__mllb_meta : mllb  ->  metadata = (fun projectee -> (match (projectee) with
| {mllb_name = __fname__mllb_name; mllb_tysc = __fname__mllb_tysc; mllb_add_unit = __fname__mllb_add_unit; mllb_def = __fname__mllb_def; mllb_meta = __fname__mllb_meta; print_typ = __fname__print_typ} -> begin
__fname__mllb_meta
end))


let __proj__Mkmllb__item__print_typ : mllb  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {mllb_name = __fname__mllb_name; mllb_tysc = __fname__mllb_tysc; mllb_add_unit = __fname__mllb_add_unit; mllb_def = __fname__mllb_def; mllb_meta = __fname__mllb_meta; print_typ = __fname__print_typ} -> begin
__fname__print_typ
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
| uu____2223 -> begin
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
| uu____2243 -> begin
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
| uu____2287 -> begin
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
| uu____2390 -> begin
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
| uu____2404 -> begin
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
| uu____2428 -> begin
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
| uu____2472 -> begin
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
| uu____2486 -> begin
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
| uu____2544 -> begin
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
| uu____2576 -> begin
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
| uu____2594 -> begin
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
| uu____2626 -> begin
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

let uu____2782 = (

let uu____2783 = (FStar_Options.codegen ())
in (Prims.op_Equality uu____2783 (FStar_Pervasives_Native.Some (FStar_Options.FSharp))))
in (match (uu____2782) with
| true -> begin
"FSharp.Compatibility.OCaml.Obj"
end
| uu____2788 -> begin
"Obj"
end))
in (

let obj_repr = (with_ty (MLTY_Fun (((t), (E_PURE), (MLTY_Top)))) (MLE_Name ((((obj_ns)::[]), ("repr")))))
in (with_ty_loc MLTY_Top (MLE_App (((obj_repr), ((x)::[])))) x.loc))))


let avoid_keyword : Prims.string  ->  Prims.string = (fun s -> (

let uu____2799 = (is_reserved s)
in (match (uu____2799) with
| true -> begin
(Prims.strcat s "_")
end
| uu____2800 -> begin
s
end)))


let bv_as_mlident : FStar_Syntax_Syntax.bv  ->  mlident = (fun x -> (

let uu____2806 = (((FStar_Util.starts_with x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText FStar_Ident.reserved_prefix) || (FStar_Syntax_Syntax.is_null_bv x)) || (is_reserved x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText))
in (match (uu____2806) with
| true -> begin
(

let uu____2807 = (

let uu____2808 = (

let uu____2809 = (FStar_Util.string_of_int x.FStar_Syntax_Syntax.index)
in (Prims.strcat "_" uu____2809))
in (Prims.strcat x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText uu____2808))
in (FStar_All.pipe_left avoid_keyword uu____2807))
end
| uu____2810 -> begin
(FStar_All.pipe_left avoid_keyword x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText)
end)))


let push_unit : mltyscheme  ->  mltyscheme = (fun ts -> (

let uu____2816 = ts
in (match (uu____2816) with
| (vs, ty) -> begin
((vs), (MLTY_Fun (((ml_unit_ty), (E_PURE), (ty)))))
end)))


let pop_unit : mltyscheme  ->  mltyscheme = (fun ts -> (

let uu____2824 = ts
in (match (uu____2824) with
| (vs, ty) -> begin
(match (ty) with
| MLTY_Fun (l, E_PURE, t) -> begin
(match ((Prims.op_Equality l ml_unit_ty)) with
| true -> begin
((vs), (t))
end
| uu____2829 -> begin
(failwith "unexpected: pop_unit: domain was not unit")
end)
end
| uu____2830 -> begin
(failwith "unexpected: pop_unit: not a function type")
end)
end)))




