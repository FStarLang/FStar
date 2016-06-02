
open Prims

type decl =
| DFunction of (typ * ident * binder Prims.list * expr) 
 and expr =
| EBound of var
| EOpen of binder
| EQualified of lident
| EConstant of constant
| EUnit
| EApp of (expr * expr Prims.list)
| ELet of (binder * expr * expr)
| EIfThenElse of (expr * expr * expr)
| ESequence of (expr * expr)
| EAssign of (expr * expr)
| EBufCreate of (expr * expr)
| EBufRead of (expr * expr)
| EBufWrite of (expr * expr * expr)
| EBufSub of (expr * expr * expr) 
 and constant =
| CInt of Prims.string 
 and binder =
{name : ident; typ : typ; mut : Prims.bool} 
 and typ =
| TInt32
| TBuf of typ
| TUnit 
 and program =
decl Prims.list 
 and var =
Prims.int 
 and ident =
Prims.string 
 and lident =
(ident Prims.list * ident)


let is_DFunction = (fun _discr_ -> (match (_discr_) with
| DFunction (_) -> begin
true
end
| _ -> begin
false
end))


let is_EBound = (fun _discr_ -> (match (_discr_) with
| EBound (_) -> begin
true
end
| _ -> begin
false
end))


let is_EOpen = (fun _discr_ -> (match (_discr_) with
| EOpen (_) -> begin
true
end
| _ -> begin
false
end))


let is_EQualified = (fun _discr_ -> (match (_discr_) with
| EQualified (_) -> begin
true
end
| _ -> begin
false
end))


let is_EConstant = (fun _discr_ -> (match (_discr_) with
| EConstant (_) -> begin
true
end
| _ -> begin
false
end))


let is_EUnit = (fun _discr_ -> (match (_discr_) with
| EUnit (_) -> begin
true
end
| _ -> begin
false
end))


let is_EApp = (fun _discr_ -> (match (_discr_) with
| EApp (_) -> begin
true
end
| _ -> begin
false
end))


let is_ELet = (fun _discr_ -> (match (_discr_) with
| ELet (_) -> begin
true
end
| _ -> begin
false
end))


let is_EIfThenElse = (fun _discr_ -> (match (_discr_) with
| EIfThenElse (_) -> begin
true
end
| _ -> begin
false
end))


let is_ESequence = (fun _discr_ -> (match (_discr_) with
| ESequence (_) -> begin
true
end
| _ -> begin
false
end))


let is_EAssign = (fun _discr_ -> (match (_discr_) with
| EAssign (_) -> begin
true
end
| _ -> begin
false
end))


let is_EBufCreate = (fun _discr_ -> (match (_discr_) with
| EBufCreate (_) -> begin
true
end
| _ -> begin
false
end))


let is_EBufRead = (fun _discr_ -> (match (_discr_) with
| EBufRead (_) -> begin
true
end
| _ -> begin
false
end))


let is_EBufWrite = (fun _discr_ -> (match (_discr_) with
| EBufWrite (_) -> begin
true
end
| _ -> begin
false
end))


let is_EBufSub = (fun _discr_ -> (match (_discr_) with
| EBufSub (_) -> begin
true
end
| _ -> begin
false
end))


let is_CInt = (fun _discr_ -> (match (_discr_) with
| CInt (_) -> begin
true
end
| _ -> begin
false
end))


let is_Mkbinder : binder  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkbinder"))))


let is_TInt32 = (fun _discr_ -> (match (_discr_) with
| TInt32 (_) -> begin
true
end
| _ -> begin
false
end))


let is_TBuf = (fun _discr_ -> (match (_discr_) with
| TBuf (_) -> begin
true
end
| _ -> begin
false
end))


let is_TUnit = (fun _discr_ -> (match (_discr_) with
| TUnit (_) -> begin
true
end
| _ -> begin
false
end))


let ___DFunction____0 = (fun projectee -> (match (projectee) with
| DFunction (_79_5) -> begin
_79_5
end))


let ___EBound____0 = (fun projectee -> (match (projectee) with
| EBound (_79_8) -> begin
_79_8
end))


let ___EOpen____0 = (fun projectee -> (match (projectee) with
| EOpen (_79_11) -> begin
_79_11
end))


let ___EQualified____0 = (fun projectee -> (match (projectee) with
| EQualified (_79_14) -> begin
_79_14
end))


let ___EConstant____0 = (fun projectee -> (match (projectee) with
| EConstant (_79_17) -> begin
_79_17
end))


let ___EApp____0 = (fun projectee -> (match (projectee) with
| EApp (_79_20) -> begin
_79_20
end))


let ___ELet____0 = (fun projectee -> (match (projectee) with
| ELet (_79_23) -> begin
_79_23
end))


let ___EIfThenElse____0 = (fun projectee -> (match (projectee) with
| EIfThenElse (_79_26) -> begin
_79_26
end))


let ___ESequence____0 = (fun projectee -> (match (projectee) with
| ESequence (_79_29) -> begin
_79_29
end))


let ___EAssign____0 = (fun projectee -> (match (projectee) with
| EAssign (_79_32) -> begin
_79_32
end))


let ___EBufCreate____0 = (fun projectee -> (match (projectee) with
| EBufCreate (_79_35) -> begin
_79_35
end))


let ___EBufRead____0 = (fun projectee -> (match (projectee) with
| EBufRead (_79_38) -> begin
_79_38
end))


let ___EBufWrite____0 = (fun projectee -> (match (projectee) with
| EBufWrite (_79_41) -> begin
_79_41
end))


let ___EBufSub____0 = (fun projectee -> (match (projectee) with
| EBufSub (_79_44) -> begin
_79_44
end))


let ___CInt____0 = (fun projectee -> (match (projectee) with
| CInt (_79_46) -> begin
_79_46
end))


let ___TBuf____0 = (fun projectee -> (match (projectee) with
| TBuf (_79_50) -> begin
_79_50
end))


type version =
Prims.int


let current_version : version = 1


type file =
(Prims.string * program)


type binary_format =
(version * file Prims.list)


let fst3 = (fun _79_56 -> (match (_79_56) with
| (x, _79_53, _79_55) -> begin
x
end))


let snd3 = (fun _79_62 -> (match (_79_62) with
| (_79_58, x, _79_61) -> begin
x
end))


let thd3 = (fun _79_68 -> (match (_79_68) with
| (_79_64, _79_66, x) -> begin
x
end))


let rec translate : FStar_Extraction_ML_Syntax.mllib  ->  file Prims.list = (fun _79_70 -> (match (_79_70) with
| FStar_Extraction_ML_Syntax.MLLib (modules) -> begin
(FStar_List.filter_map (fun m -> try
(match (()) with
| () -> begin
(let _169_236 = (translate_module m)
in Some (_169_236))
end)
with
| e -> begin
(

let _79_76 = (let _169_238 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Unable to translate module: %s\n%s\n" (fst3 m) _169_238))
in None)
end) modules)
end))
and translate_module : (Prims.string * (FStar_Extraction_ML_Syntax.mlsig * FStar_Extraction_ML_Syntax.mlmodule) Prims.option * FStar_Extraction_ML_Syntax.mllib)  ->  file = (fun _79_84 -> (match (_79_84) with
| (name, modul, _79_83) -> begin
(

let program = (match (modul) with
| Some (_signature, decls) -> begin
(FStar_List.filter_map translate_decl decls)
end
| _79_90 -> begin
(FStar_All.failwith "Unexpected standalone interface or nested modules")
end)
in (name, program))
end))
and translate_decl : FStar_Extraction_ML_Syntax.mlmodule1  ->  decl Prims.option = (fun d -> (match (d) with
| FStar_Extraction_ML_Syntax.MLM_Let (is_rec, {FStar_Extraction_ML_Syntax.mllb_name = (name, _79_119); FStar_Extraction_ML_Syntax.mllb_tysc = Some ([], FStar_Extraction_ML_Syntax.MLTY_Fun (_79_109, _79_111, t)); FStar_Extraction_ML_Syntax.mllb_add_unit = _79_106; FStar_Extraction_ML_Syntax.mllb_def = {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun (args, body); FStar_Extraction_ML_Syntax.mlty = _79_99; FStar_Extraction_ML_Syntax.loc = _79_97}; FStar_Extraction_ML_Syntax.print_typ = _79_95}::[]) -> begin
(

let t = (translate_type t)
in (

let binders = (translate_binders args)
in (

let body = (translate_expr body)
in Some (DFunction ((t, name, binders, body))))))
end
| FStar_Extraction_ML_Syntax.MLM_Let (_79_129) -> begin
(FStar_All.failwith "todo: translate_decl [MLM_Let]")
end
| FStar_Extraction_ML_Syntax.MLM_Loc (_79_132) -> begin
None
end
| FStar_Extraction_ML_Syntax.MLM_Ty (_79_135) -> begin
(FStar_All.failwith "todo: translate_decl [MLM_Ty]")
end
| FStar_Extraction_ML_Syntax.MLM_Top (_79_138) -> begin
(FStar_All.failwith "todo: translate_decl [MLM_Top]")
end
| FStar_Extraction_ML_Syntax.MLM_Exn (_79_141) -> begin
(FStar_All.failwith "todo: translate_decl [MLM_Exn]")
end))
and translate_type : FStar_Extraction_ML_Syntax.mlty  ->  typ = (fun t -> (match (t) with
| (FStar_Extraction_ML_Syntax.MLTY_Tuple ([])) | (FStar_Extraction_ML_Syntax.MLTY_Top) -> begin
TUnit
end
| FStar_Extraction_ML_Syntax.MLTY_Var (_79_148) -> begin
(FStar_All.failwith "todo: translate_type [MLTY_Var]")
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (_79_151) -> begin
(FStar_All.failwith "todo: translate_type [MLTY_Fun]")
end
| FStar_Extraction_ML_Syntax.MLTY_Named (_79_154, p) -> begin
(match ((FStar_Extraction_ML_Syntax.string_of_mlpath p)) with
| "Prims.unit" -> begin
TUnit
end
| _79_160 -> begin
(let _169_242 = (FStar_Util.format1 "todo: translate_type [MLTY_Named] %s" (FStar_Extraction_ML_Syntax.string_of_mlpath p))
in (FStar_All.failwith _169_242))
end)
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (_79_162) -> begin
(FStar_All.failwith "todo: translate_type [MLTY_Tuple]")
end))
and translate_binders : (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty) Prims.list  ->  binder Prims.list = (fun args -> (FStar_List.map translate_binder args))
and translate_binder : (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)  ->  binder = (fun _79_170 -> (match (_79_170) with
| ((name, _79_167), typ) -> begin
(let _169_245 = (translate_type typ)
in {name = name; typ = _169_245; mut = false})
end))
and translate_expr : FStar_Extraction_ML_Syntax.mlexpr  ->  expr = (fun e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Tuple ([]) -> begin
EUnit
end
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(translate_constant c)
end
| FStar_Extraction_ML_Syntax.MLE_Var (_79_177) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Var]")
end
| FStar_Extraction_ML_Syntax.MLE_Name (_79_180) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Name]")
end
| FStar_Extraction_ML_Syntax.MLE_Let (_79_183) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Let]")
end
| FStar_Extraction_ML_Syntax.MLE_App (_79_186) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_App]")
end
| FStar_Extraction_ML_Syntax.MLE_Fun (_79_189) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Fun]")
end
| FStar_Extraction_ML_Syntax.MLE_Match (_79_192) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Match]")
end
| FStar_Extraction_ML_Syntax.MLE_Coerce (_79_195) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Coerce]")
end
| FStar_Extraction_ML_Syntax.MLE_CTor (_79_198) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_CTor]")
end
| FStar_Extraction_ML_Syntax.MLE_Seq (_79_201) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Seq]")
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (_79_204) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Tuple]")
end
| FStar_Extraction_ML_Syntax.MLE_Record (_79_207) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Record]")
end
| FStar_Extraction_ML_Syntax.MLE_Proj (_79_210) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Proj]")
end
| FStar_Extraction_ML_Syntax.MLE_If (_79_213) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_If]")
end
| FStar_Extraction_ML_Syntax.MLE_Raise (_79_216) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Raise]")
end
| FStar_Extraction_ML_Syntax.MLE_Try (_79_219) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Try]")
end))
and translate_constant : FStar_Extraction_ML_Syntax.mlconstant  ->  expr = (fun c -> (match (c) with
| FStar_Extraction_ML_Syntax.MLC_Unit -> begin
EUnit
end
| FStar_Extraction_ML_Syntax.MLC_Bool (_79_224) -> begin
(FStar_All.failwith "todo: translate_expr [MLC_Bool]")
end
| FStar_Extraction_ML_Syntax.MLC_Int (_79_227) -> begin
(FStar_All.failwith "todo: translate_expr [MLC_Int]")
end
| FStar_Extraction_ML_Syntax.MLC_Float (_79_230) -> begin
(FStar_All.failwith "todo: translate_expr [MLC_Float]")
end
| FStar_Extraction_ML_Syntax.MLC_Char (_79_233) -> begin
(FStar_All.failwith "todo: translate_expr [MLC_Char]")
end
| FStar_Extraction_ML_Syntax.MLC_String (_79_236) -> begin
(FStar_All.failwith "todo: translate_expr [MLC_String]")
end
| FStar_Extraction_ML_Syntax.MLC_Bytes (_79_239) -> begin
(FStar_All.failwith "todo: translate_expr [MLC_Bytes]")
end))




