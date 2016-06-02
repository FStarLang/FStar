
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


let rec translate : FStar_Extraction_ML_Syntax.mllib  ->  file Prims.list = (fun _79_52 -> (match (_79_52) with
| FStar_Extraction_ML_Syntax.MLLib (modules) -> begin
(FStar_List.map translate_module modules)
end))
and translate_module : (FStar_Extraction_ML_Syntax.mlsymbol * (FStar_Extraction_ML_Syntax.mlsig * FStar_Extraction_ML_Syntax.mlmodule) Prims.option * FStar_Extraction_ML_Syntax.mllib)  ->  file = (fun _79_57 -> (match (_79_57) with
| (name, modul, _79_56) -> begin
(

let program = (match (modul) with
| Some (_signature, decls) -> begin
(FStar_List.filter_map translate_decl decls)
end
| _79_63 -> begin
(FStar_All.failwith "Unexpected standalone interface or nested modules")
end)
in (name, program))
end))
and translate_decl : FStar_Extraction_ML_Syntax.mlmodule1  ->  decl Prims.option = (fun d -> (match (d) with
| FStar_Extraction_ML_Syntax.MLM_Let (is_rec, {FStar_Extraction_ML_Syntax.mllb_name = (name, _79_92); FStar_Extraction_ML_Syntax.mllb_tysc = Some ([], FStar_Extraction_ML_Syntax.MLTY_Fun (_79_82, _79_84, t)); FStar_Extraction_ML_Syntax.mllb_add_unit = _79_79; FStar_Extraction_ML_Syntax.mllb_def = {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun (args, body); FStar_Extraction_ML_Syntax.mlty = _79_72; FStar_Extraction_ML_Syntax.loc = _79_70}; FStar_Extraction_ML_Syntax.print_typ = _79_68}::[]) -> begin
(

let t = (translate_type t)
in (

let binders = (translate_binders args)
in (

let body = (translate_expr body)
in Some (DFunction ((t, name, binders, body))))))
end
| _79_102 -> begin
None
end))
and translate_type : FStar_Extraction_ML_Syntax.mlty  ->  typ = (fun t -> (match (t) with
| (FStar_Extraction_ML_Syntax.MLTY_Tuple ([])) | (FStar_Extraction_ML_Syntax.MLTY_Top) -> begin
TUnit
end
| _79_108 -> begin
(FStar_All.failwith "todo: translate_type")
end))
and translate_binders : (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty) Prims.list  ->  binder Prims.list = (fun args -> (FStar_List.map translate_binder args))
and translate_binder : (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)  ->  binder = (fun _79_115 -> (match (_79_115) with
| ((name, _79_112), typ) -> begin
(let _169_235 = (translate_type typ)
in {name = name; typ = _169_235; mut = false})
end))
and translate_expr : FStar_Extraction_ML_Syntax.mlexpr  ->  expr = (fun e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Tuple ([]) -> begin
EUnit
end
| _79_120 -> begin
(FStar_All.failwith "todo: translate_expr")
end))




