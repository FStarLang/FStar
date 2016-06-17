
open Prims

type decl =
| DFunction of (typ * ident * binder Prims.list * expr)
| DTypeAlias of (ident * typ) 
 and expr =
| EBound of var
| EOpen of binder
| EQualified of lident
| EConstant of constant
| EUnit
| EApp of (expr * expr Prims.list)
| ELet of (binder * expr * expr)
| EIfThenElse of (expr * expr * expr)
| ESequence of expr Prims.list
| EAssign of (expr * expr)
| EBufCreate of (expr * expr)
| EBufRead of (expr * expr)
| EBufWrite of (expr * expr * expr)
| EBufSub of (expr * expr * expr)
| EMatch of (expr * branches)
| EOp of op 
 and op =
| Add
| AddW
| Sub
| Div
| Mult
| Mod
| Or
| And
| Xor
| ShiftL
| ShiftR 
 and pattern =
| PUnit 
 and constant =
| CUInt8 of Prims.string
| CUInt16 of Prims.string
| CUInt32 of Prims.string
| CUInt64 of Prims.string
| CInt8 of Prims.string
| CInt16 of Prims.string
| CInt32 of Prims.string
| CInt64 of Prims.string 
 and binder =
{name : ident; typ : typ; mut : Prims.bool} 
 and typ =
| TUInt8
| TUInt16
| TUInt32
| TUInt64
| TInt8
| TInt16
| TInt32
| TInt64
| TBuf of typ
| TUnit
| TAlias of ident 
 and program =
decl Prims.list 
 and branches =
branch Prims.list 
 and branch =
(pattern * expr) 
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


let is_DTypeAlias = (fun _discr_ -> (match (_discr_) with
| DTypeAlias (_) -> begin
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


let is_EMatch = (fun _discr_ -> (match (_discr_) with
| EMatch (_) -> begin
true
end
| _ -> begin
false
end))


let is_EOp = (fun _discr_ -> (match (_discr_) with
| EOp (_) -> begin
true
end
| _ -> begin
false
end))


let is_Add = (fun _discr_ -> (match (_discr_) with
| Add (_) -> begin
true
end
| _ -> begin
false
end))


let is_AddW = (fun _discr_ -> (match (_discr_) with
| AddW (_) -> begin
true
end
| _ -> begin
false
end))


let is_Sub = (fun _discr_ -> (match (_discr_) with
| Sub (_) -> begin
true
end
| _ -> begin
false
end))


let is_Div = (fun _discr_ -> (match (_discr_) with
| Div (_) -> begin
true
end
| _ -> begin
false
end))


let is_Mult = (fun _discr_ -> (match (_discr_) with
| Mult (_) -> begin
true
end
| _ -> begin
false
end))


let is_Mod = (fun _discr_ -> (match (_discr_) with
| Mod (_) -> begin
true
end
| _ -> begin
false
end))


let is_Or = (fun _discr_ -> (match (_discr_) with
| Or (_) -> begin
true
end
| _ -> begin
false
end))


let is_And = (fun _discr_ -> (match (_discr_) with
| And (_) -> begin
true
end
| _ -> begin
false
end))


let is_Xor = (fun _discr_ -> (match (_discr_) with
| Xor (_) -> begin
true
end
| _ -> begin
false
end))


let is_ShiftL = (fun _discr_ -> (match (_discr_) with
| ShiftL (_) -> begin
true
end
| _ -> begin
false
end))


let is_ShiftR = (fun _discr_ -> (match (_discr_) with
| ShiftR (_) -> begin
true
end
| _ -> begin
false
end))


let is_PUnit = (fun _discr_ -> (match (_discr_) with
| PUnit (_) -> begin
true
end
| _ -> begin
false
end))


let is_CUInt8 = (fun _discr_ -> (match (_discr_) with
| CUInt8 (_) -> begin
true
end
| _ -> begin
false
end))


let is_CUInt16 = (fun _discr_ -> (match (_discr_) with
| CUInt16 (_) -> begin
true
end
| _ -> begin
false
end))


let is_CUInt32 = (fun _discr_ -> (match (_discr_) with
| CUInt32 (_) -> begin
true
end
| _ -> begin
false
end))


let is_CUInt64 = (fun _discr_ -> (match (_discr_) with
| CUInt64 (_) -> begin
true
end
| _ -> begin
false
end))


let is_CInt8 = (fun _discr_ -> (match (_discr_) with
| CInt8 (_) -> begin
true
end
| _ -> begin
false
end))


let is_CInt16 = (fun _discr_ -> (match (_discr_) with
| CInt16 (_) -> begin
true
end
| _ -> begin
false
end))


let is_CInt32 = (fun _discr_ -> (match (_discr_) with
| CInt32 (_) -> begin
true
end
| _ -> begin
false
end))


let is_CInt64 = (fun _discr_ -> (match (_discr_) with
| CInt64 (_) -> begin
true
end
| _ -> begin
false
end))


let is_Mkbinder : binder  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkbinder"))))


let is_TUInt8 = (fun _discr_ -> (match (_discr_) with
| TUInt8 (_) -> begin
true
end
| _ -> begin
false
end))


let is_TUInt16 = (fun _discr_ -> (match (_discr_) with
| TUInt16 (_) -> begin
true
end
| _ -> begin
false
end))


let is_TUInt32 = (fun _discr_ -> (match (_discr_) with
| TUInt32 (_) -> begin
true
end
| _ -> begin
false
end))


let is_TUInt64 = (fun _discr_ -> (match (_discr_) with
| TUInt64 (_) -> begin
true
end
| _ -> begin
false
end))


let is_TInt8 = (fun _discr_ -> (match (_discr_) with
| TInt8 (_) -> begin
true
end
| _ -> begin
false
end))


let is_TInt16 = (fun _discr_ -> (match (_discr_) with
| TInt16 (_) -> begin
true
end
| _ -> begin
false
end))


let is_TInt32 = (fun _discr_ -> (match (_discr_) with
| TInt32 (_) -> begin
true
end
| _ -> begin
false
end))


let is_TInt64 = (fun _discr_ -> (match (_discr_) with
| TInt64 (_) -> begin
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


let is_TAlias = (fun _discr_ -> (match (_discr_) with
| TAlias (_) -> begin
true
end
| _ -> begin
false
end))


let ___DFunction____0 = (fun projectee -> (match (projectee) with
| DFunction (_79_8) -> begin
_79_8
end))


let ___DTypeAlias____0 = (fun projectee -> (match (projectee) with
| DTypeAlias (_79_11) -> begin
_79_11
end))


let ___EBound____0 = (fun projectee -> (match (projectee) with
| EBound (_79_14) -> begin
_79_14
end))


let ___EOpen____0 = (fun projectee -> (match (projectee) with
| EOpen (_79_17) -> begin
_79_17
end))


let ___EQualified____0 = (fun projectee -> (match (projectee) with
| EQualified (_79_20) -> begin
_79_20
end))


let ___EConstant____0 = (fun projectee -> (match (projectee) with
| EConstant (_79_23) -> begin
_79_23
end))


let ___EApp____0 = (fun projectee -> (match (projectee) with
| EApp (_79_26) -> begin
_79_26
end))


let ___ELet____0 = (fun projectee -> (match (projectee) with
| ELet (_79_29) -> begin
_79_29
end))


let ___EIfThenElse____0 = (fun projectee -> (match (projectee) with
| EIfThenElse (_79_32) -> begin
_79_32
end))


let ___ESequence____0 = (fun projectee -> (match (projectee) with
| ESequence (_79_35) -> begin
_79_35
end))


let ___EAssign____0 = (fun projectee -> (match (projectee) with
| EAssign (_79_38) -> begin
_79_38
end))


let ___EBufCreate____0 = (fun projectee -> (match (projectee) with
| EBufCreate (_79_41) -> begin
_79_41
end))


let ___EBufRead____0 = (fun projectee -> (match (projectee) with
| EBufRead (_79_44) -> begin
_79_44
end))


let ___EBufWrite____0 = (fun projectee -> (match (projectee) with
| EBufWrite (_79_47) -> begin
_79_47
end))


let ___EBufSub____0 = (fun projectee -> (match (projectee) with
| EBufSub (_79_50) -> begin
_79_50
end))


let ___EMatch____0 = (fun projectee -> (match (projectee) with
| EMatch (_79_53) -> begin
_79_53
end))


let ___EOp____0 = (fun projectee -> (match (projectee) with
| EOp (_79_56) -> begin
_79_56
end))


let ___CUInt8____0 = (fun projectee -> (match (projectee) with
| CUInt8 (_79_59) -> begin
_79_59
end))


let ___CUInt16____0 = (fun projectee -> (match (projectee) with
| CUInt16 (_79_62) -> begin
_79_62
end))


let ___CUInt32____0 = (fun projectee -> (match (projectee) with
| CUInt32 (_79_65) -> begin
_79_65
end))


let ___CUInt64____0 = (fun projectee -> (match (projectee) with
| CUInt64 (_79_68) -> begin
_79_68
end))


let ___CInt8____0 = (fun projectee -> (match (projectee) with
| CInt8 (_79_71) -> begin
_79_71
end))


let ___CInt16____0 = (fun projectee -> (match (projectee) with
| CInt16 (_79_74) -> begin
_79_74
end))


let ___CInt32____0 = (fun projectee -> (match (projectee) with
| CInt32 (_79_77) -> begin
_79_77
end))


let ___CInt64____0 = (fun projectee -> (match (projectee) with
| CInt64 (_79_80) -> begin
_79_80
end))


let ___TBuf____0 = (fun projectee -> (match (projectee) with
| TBuf (_79_84) -> begin
_79_84
end))


let ___TAlias____0 = (fun projectee -> (match (projectee) with
| TAlias (_79_87) -> begin
_79_87
end))


type version =
Prims.int


let current_version : version = 1


type file =
(Prims.string * program)


type binary_format =
(version * file Prims.list)


let fst3 = (fun _79_93 -> (match (_79_93) with
| (x, _79_90, _79_92) -> begin
x
end))


let snd3 = (fun _79_99 -> (match (_79_99) with
| (_79_95, x, _79_98) -> begin
x
end))


let thd3 = (fun _79_105 -> (match (_79_105) with
| (_79_101, _79_103, x) -> begin
x
end))


let is_machine_int : Prims.string  ->  Prims.bool = (fun _79_1 -> (match (_79_1) with
| ("UInt8") | ("UInt16") | ("UInt32") | ("UInt64") | ("Int8") | ("Int16") | ("Int32") | ("Int64") -> begin
true
end
| _79_116 -> begin
false
end))


type env =
{names : name Prims.list; module_name : Prims.string} 
 and name =
{pretty : Prims.string; mut : Prims.bool}


let is_Mkenv : env  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv"))))


let is_Mkname : name  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkname"))))


let empty : Prims.string  ->  env = (fun module_name -> {names = []; module_name = module_name})


let extend : env  ->  Prims.string  ->  Prims.bool  ->  env = (fun env x is_mut -> (

let _79_127 = env
in {names = ({pretty = x; mut = is_mut})::env.names; module_name = _79_127.module_name}))


let find_name : env  ->  Prims.string  ->  name = (fun env x -> (match ((FStar_List.tryFind (fun name -> (name.pretty = x)) env.names)) with
| Some (name) -> begin
name
end
| None -> begin
(FStar_All.failwith "internal error: name not found")
end))


let is_mutable : env  ->  Prims.string  ->  Prims.bool = (fun env x -> (let _170_447 = (find_name env x)
in _170_447.mut))


let find : env  ->  Prims.string  ->  Prims.int = (fun env x -> try
(match (()) with
| () -> begin
(FStar_List.index (fun name -> (name.pretty = x)) env.names)
end)
with
| _79_143 -> begin
(let _170_455 = (FStar_Util.format1 "Internal error: name not found %s\n" x)
in (FStar_All.failwith _170_455))
end)


let add_binders = (fun env binders -> (FStar_List.fold_left (fun env _79_156 -> (match (_79_156) with
| ((name, _79_152), _79_155) -> begin
(extend env name false)
end)) env binders))


let rec translate : FStar_Extraction_ML_Syntax.mllib  ->  file Prims.list = (fun _79_158 -> (match (_79_158) with
| FStar_Extraction_ML_Syntax.MLLib (modules) -> begin
(FStar_List.filter_map (fun m -> try
(match (()) with
| () -> begin
(let _170_485 = (translate_module m)
in Some (_170_485))
end)
with
| e when ((fst3 m) <> "Test") -> begin
(

let _79_164 = (let _170_487 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Unable to translate module: %s\n%s\n" (fst3 m) _170_487))
in None)
end) modules)
end))
and translate_module : (Prims.string * (FStar_Extraction_ML_Syntax.mlsig * FStar_Extraction_ML_Syntax.mlmodule) Prims.option * FStar_Extraction_ML_Syntax.mllib)  ->  file = (fun _79_172 -> (match (_79_172) with
| (module_name, modul, _79_171) -> begin
(

let program = (match (modul) with
| Some (_signature, decls) -> begin
(FStar_List.filter_map (translate_decl (empty module_name)) decls)
end
| _79_178 -> begin
(FStar_All.failwith "Unexpected standalone interface or nested modules")
end)
in (module_name, program))
end))
and translate_decl : env  ->  FStar_Extraction_ML_Syntax.mlmodule1  ->  decl Prims.option = (fun env d -> (match (d) with
| FStar_Extraction_ML_Syntax.MLM_Let (flavor, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _79_208); FStar_Extraction_ML_Syntax.mllb_tysc = Some ([], FStar_Extraction_ML_Syntax.MLTY_Fun (_79_198, _79_200, t)); FStar_Extraction_ML_Syntax.mllb_add_unit = _79_195; FStar_Extraction_ML_Syntax.mllb_def = {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun (args, body); FStar_Extraction_ML_Syntax.mlty = _79_188; FStar_Extraction_ML_Syntax.loc = _79_186}; FStar_Extraction_ML_Syntax.print_typ = _79_184})::[]) -> begin
(

let _79_214 = ()
in (

let env = if (flavor = FStar_Extraction_ML_Syntax.Rec) then begin
(extend env name false)
end else begin
env
end
in (

let rec find_return_type = (fun _79_2 -> (match (_79_2) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (_79_220, _79_222, t) -> begin
(find_return_type t)
end
| t -> begin
t
end))
in (

let t = (let _170_493 = (find_return_type t)
in (translate_type env _170_493))
in (

let binders = (translate_binders env args)
in (

let env = (add_binders env args)
in (

let body = (translate_expr env body)
in Some (DFunction ((t, name, binders, body))))))))))
end
| FStar_Extraction_ML_Syntax.MLM_Let (_79_232) -> begin
(FStar_All.failwith "todo: translate_decl [MLM_Let]")
end
| FStar_Extraction_ML_Syntax.MLM_Loc (_79_235) -> begin
None
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((name, [], Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev (t))))::[]) -> begin
(let _170_496 = (let _170_495 = (let _170_494 = (translate_type env t)
in (name, _170_494))
in DTypeAlias (_170_495))
in Some (_170_496))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (_79_246) -> begin
(FStar_All.failwith "todo: translate_decl [MLM_Ty]")
end
| FStar_Extraction_ML_Syntax.MLM_Top (_79_249) -> begin
(FStar_All.failwith "todo: translate_decl [MLM_Top]")
end
| FStar_Extraction_ML_Syntax.MLM_Exn (_79_252) -> begin
(FStar_All.failwith "todo: translate_decl [MLM_Exn]")
end))
and translate_type : env  ->  FStar_Extraction_ML_Syntax.mlty  ->  typ = (fun env t -> (match (t) with
| (FStar_Extraction_ML_Syntax.MLTY_Tuple ([])) | (FStar_Extraction_ML_Syntax.MLTY_Top) -> begin
TUnit
end
| FStar_Extraction_ML_Syntax.MLTY_Var (_79_260) -> begin
(FStar_All.failwith "todo: translate_type [MLTY_Var]")
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (_79_263) -> begin
(FStar_All.failwith "todo: translate_type [MLTY_Fun]")
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "Prims.unit") -> begin
TUnit
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.UInt8.t") -> begin
TUInt8
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.UInt16.t") -> begin
TUInt16
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.UInt32.t") -> begin
TUInt32
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.UInt64.t") -> begin
TUInt64
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Int8.t") -> begin
TInt8
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Int16.t") -> begin
TInt16
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Int32.t") -> begin
TInt32
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Int64.t") -> begin
TInt64
end
| FStar_Extraction_ML_Syntax.MLTY_Named ((arg)::[], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.buffer") -> begin
(let _170_499 = (translate_type env arg)
in TBuf (_170_499))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], ((module_name)::[], type_name)) when (module_name = env.module_name) -> begin
TAlias (type_name)
end
| FStar_Extraction_ML_Syntax.MLTY_Named (_79_314, p) -> begin
(let _170_500 = (FStar_Util.format1 "todo: translate_type [MLTY_Named] %s" (FStar_Extraction_ML_Syntax.string_of_mlpath p))
in (FStar_All.failwith _170_500))
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (_79_319) -> begin
(FStar_All.failwith "todo: translate_type [MLTY_Tuple]")
end))
and translate_binders : env  ->  (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty) Prims.list  ->  binder Prims.list = (fun env args -> (FStar_List.map (translate_binder env) args))
and translate_binder : env  ->  (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)  ->  binder = (fun env _79_329 -> (match (_79_329) with
| ((name, _79_326), typ) -> begin
(let _170_505 = (translate_type env typ)
in {name = name; typ = _170_505; mut = false})
end))
and translate_expr : env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  expr = (fun env e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Tuple ([]) -> begin
EUnit
end
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(translate_constant c)
end
| FStar_Extraction_ML_Syntax.MLE_Var (name, _79_338) -> begin
(let _170_508 = (find env name)
in EBound (_170_508))
end
| FStar_Extraction_ML_Syntax.MLE_Name (_79_342) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Name]")
end
| FStar_Extraction_ML_Syntax.MLE_Let ((flavor, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _79_354); FStar_Extraction_ML_Syntax.mllb_tysc = Some ([], typ); FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit; FStar_Extraction_ML_Syntax.mllb_def = body; FStar_Extraction_ML_Syntax.print_typ = print})::[]), continuation) -> begin
(

let _79_384 = if (flavor = FStar_Extraction_ML_Syntax.Mutable) then begin
(let _170_510 = (match (typ) with
| FStar_Extraction_ML_Syntax.MLTY_Named ((t)::[], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.HST.salloc") -> begin
t
end
| _79_368 -> begin
(FStar_All.failwith "unexpected: bad desugaring of Mutable")
end)
in (let _170_509 = (match (body) with
| {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_App (_79_374, (body)::[]); FStar_Extraction_ML_Syntax.mlty = _79_372; FStar_Extraction_ML_Syntax.loc = _79_370} -> begin
body
end
| _79_381 -> begin
(FStar_All.failwith "unexpected: bad desugaring of Mutable")
end)
in (_170_510, _170_509)))
end else begin
(typ, body)
end
in (match (_79_384) with
| (typ, body) -> begin
(

let is_mut = (flavor = FStar_Extraction_ML_Syntax.Mutable)
in (

let binder = (let _170_511 = (translate_type env typ)
in {name = name; typ = _170_511; mut = is_mut})
in (

let body = (translate_expr env body)
in (

let env = (extend env name is_mut)
in (

let continuation = (translate_expr env continuation)
in ELet ((binder, body, continuation)))))))
end))
end
| FStar_Extraction_ML_Syntax.MLE_Match (expr, branches) -> begin
(let _170_514 = (let _170_513 = (translate_expr env expr)
in (let _170_512 = (translate_branches env branches)
in (_170_513, _170_512)))
in EMatch (_170_514))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _79_397; FStar_Extraction_ML_Syntax.loc = _79_395}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Var (v, _79_407); FStar_Extraction_ML_Syntax.mlty = _79_404; FStar_Extraction_ML_Syntax.loc = _79_402})::[]) when (((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.HST.op_Bang") && (is_mutable env v)) -> begin
(let _170_515 = (find env v)
in EBound (_170_515))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _79_417; FStar_Extraction_ML_Syntax.loc = _79_415}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Var (v, _79_428); FStar_Extraction_ML_Syntax.mlty = _79_425; FStar_Extraction_ML_Syntax.loc = _79_423})::(e)::[]) when (((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.HST.op_Colon_Equals") && (is_mutable env v)) -> begin
(let _170_519 = (let _170_518 = (let _170_516 = (find env v)
in EBound (_170_516))
in (let _170_517 = (translate_expr env e)
in (_170_518, _170_517)))
in EAssign (_170_519))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _79_438; FStar_Extraction_ML_Syntax.loc = _79_436}, (e1)::(e2)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.index") -> begin
(let _170_522 = (let _170_521 = (translate_expr env e1)
in (let _170_520 = (translate_expr env e2)
in (_170_521, _170_520)))
in EBufRead (_170_522))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _79_450; FStar_Extraction_ML_Syntax.loc = _79_448}, (e1)::(e2)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.create") -> begin
(let _170_525 = (let _170_524 = (translate_expr env e1)
in (let _170_523 = (translate_expr env e2)
in (_170_524, _170_523)))
in EBufCreate (_170_525))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _79_462; FStar_Extraction_ML_Syntax.loc = _79_460}, (e1)::(e2)::(e3)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.upd") -> begin
(let _170_529 = (let _170_528 = (translate_expr env e1)
in (let _170_527 = (translate_expr env e2)
in (let _170_526 = (translate_expr env e3)
in (_170_528, _170_527, _170_526))))
in EBufWrite (_170_529))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], "op_Plus_Hat"); FStar_Extraction_ML_Syntax.mlty = _79_475; FStar_Extraction_ML_Syntax.loc = _79_473}, args) when (is_machine_int m) -> begin
(mk_op env Add args)
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], "op_Plus_Percent_Hat"); FStar_Extraction_ML_Syntax.mlty = _79_489; FStar_Extraction_ML_Syntax.loc = _79_487}, args) when (is_machine_int m) -> begin
(mk_op env AddW args)
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], "op_Subtraction_Hat"); FStar_Extraction_ML_Syntax.mlty = _79_503; FStar_Extraction_ML_Syntax.loc = _79_501}, args) when (is_machine_int m) -> begin
(mk_op env Sub args)
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], "op_Bar_Hat"); FStar_Extraction_ML_Syntax.mlty = _79_517; FStar_Extraction_ML_Syntax.loc = _79_515}, args) when (is_machine_int m) -> begin
(mk_op env Or args)
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], "op_Hat_Hat"); FStar_Extraction_ML_Syntax.mlty = _79_531; FStar_Extraction_ML_Syntax.loc = _79_529}, args) when (is_machine_int m) -> begin
(mk_op env Xor args)
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], "op_Amp_Hat"); FStar_Extraction_ML_Syntax.mlty = _79_545; FStar_Extraction_ML_Syntax.loc = _79_543}, args) when (is_machine_int m) -> begin
(mk_op env And args)
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], "op_Greater_Greater_Hat"); FStar_Extraction_ML_Syntax.mlty = _79_559; FStar_Extraction_ML_Syntax.loc = _79_557}, args) when (is_machine_int m) -> begin
(mk_op env ShiftR args)
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], "op_Less_Less_Hat"); FStar_Extraction_ML_Syntax.mlty = _79_573; FStar_Extraction_ML_Syntax.loc = _79_571}, args) when (is_machine_int m) -> begin
(mk_op env ShiftL args)
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _79_587; FStar_Extraction_ML_Syntax.loc = _79_585}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Int (c, None)); FStar_Extraction_ML_Syntax.mlty = _79_594; FStar_Extraction_ML_Syntax.loc = _79_592})::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.UInt8.uint_to_t") -> begin
EConstant (CUInt8 (c))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _79_607; FStar_Extraction_ML_Syntax.loc = _79_605}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Int (c, None)); FStar_Extraction_ML_Syntax.mlty = _79_614; FStar_Extraction_ML_Syntax.loc = _79_612})::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.UInt16.uint_to_t") -> begin
EConstant (CUInt16 (c))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _79_627; FStar_Extraction_ML_Syntax.loc = _79_625}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Int (c, None)); FStar_Extraction_ML_Syntax.mlty = _79_634; FStar_Extraction_ML_Syntax.loc = _79_632})::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.UInt32.uint_to_t") -> begin
EConstant (CUInt32 (c))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _79_647; FStar_Extraction_ML_Syntax.loc = _79_645}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Int (c, None)); FStar_Extraction_ML_Syntax.mlty = _79_654; FStar_Extraction_ML_Syntax.loc = _79_652})::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.UInt64.uint_to_t") -> begin
EConstant (CUInt64 (c))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _79_667; FStar_Extraction_ML_Syntax.loc = _79_665}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Int (c, None)); FStar_Extraction_ML_Syntax.mlty = _79_674; FStar_Extraction_ML_Syntax.loc = _79_672})::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Int8.uint_to_t") -> begin
EConstant (CInt8 (c))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _79_687; FStar_Extraction_ML_Syntax.loc = _79_685}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Int (c, None)); FStar_Extraction_ML_Syntax.mlty = _79_694; FStar_Extraction_ML_Syntax.loc = _79_692})::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Int16.uint_to_t") -> begin
EConstant (CInt16 (c))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _79_707; FStar_Extraction_ML_Syntax.loc = _79_705}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Int (c, None)); FStar_Extraction_ML_Syntax.mlty = _79_714; FStar_Extraction_ML_Syntax.loc = _79_712})::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Int32.uint_to_t") -> begin
EConstant (CInt32 (c))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _79_727; FStar_Extraction_ML_Syntax.loc = _79_725}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Int (c, None)); FStar_Extraction_ML_Syntax.mlty = _79_734; FStar_Extraction_ML_Syntax.loc = _79_732})::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Int64.uint_to_t") -> begin
EConstant (CInt64 (c))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name ((module_name)::[], function_name); FStar_Extraction_ML_Syntax.mlty = _79_747; FStar_Extraction_ML_Syntax.loc = _79_745}, args) when (module_name = env.module_name) -> begin
(let _170_531 = (let _170_530 = (FStar_List.map (translate_expr env) args)
in (EQualified (([], function_name)), _170_530))
in EApp (_170_531))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _79_760; FStar_Extraction_ML_Syntax.loc = _79_758}, args) -> begin
(let _170_533 = (let _170_532 = (FStar_Util.string_of_int (FStar_List.length args))
in (FStar_Util.format2 "todo: translate_expr [MLE_App=%s; %s]" (FStar_Extraction_ML_Syntax.string_of_mlpath p) _170_532))
in (FStar_All.failwith _170_533))
end
| FStar_Extraction_ML_Syntax.MLE_Let (_79_768) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Let]")
end
| FStar_Extraction_ML_Syntax.MLE_App (_79_771) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_App]")
end
| FStar_Extraction_ML_Syntax.MLE_Fun (_79_774) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Fun]")
end
| FStar_Extraction_ML_Syntax.MLE_Coerce (_79_777) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Coerce]")
end
| FStar_Extraction_ML_Syntax.MLE_CTor (_79_780) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_CTor]")
end
| FStar_Extraction_ML_Syntax.MLE_Seq (seqs) -> begin
(let _170_534 = (FStar_List.map (translate_expr env) seqs)
in ESequence (_170_534))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (_79_785) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Tuple]")
end
| FStar_Extraction_ML_Syntax.MLE_Record (_79_788) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Record]")
end
| FStar_Extraction_ML_Syntax.MLE_Proj (_79_791) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Proj]")
end
| FStar_Extraction_ML_Syntax.MLE_If (_79_794) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_If]")
end
| FStar_Extraction_ML_Syntax.MLE_Raise (_79_797) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Raise]")
end
| FStar_Extraction_ML_Syntax.MLE_Try (_79_800) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Try]")
end))
and translate_branches : env  ->  FStar_Extraction_ML_Syntax.mlbranch Prims.list  ->  branches = (fun env branches -> (FStar_List.map (translate_branch env) branches))
and translate_branch : env  ->  FStar_Extraction_ML_Syntax.mlbranch  ->  (pattern * expr) = (fun env _79_808 -> (match (_79_808) with
| (pat, guard, expr) -> begin
if (guard = None) then begin
(let _170_540 = (translate_pat env pat)
in (let _170_539 = (translate_expr env expr)
in (_170_540, _170_539)))
end else begin
(FStar_All.failwith "todo: translate_branch")
end
end))
and translate_pat : env  ->  FStar_Extraction_ML_Syntax.mlpattern  ->  pattern = (fun env p -> (match (p) with
| FStar_Extraction_ML_Syntax.MLP_Const (FStar_Extraction_ML_Syntax.MLC_Unit) -> begin
PUnit
end
| FStar_Extraction_ML_Syntax.MLP_Wild -> begin
(FStar_All.failwith "todo: translate_pat [MLP_Wild]")
end
| FStar_Extraction_ML_Syntax.MLP_Const (_79_815) -> begin
(FStar_All.failwith "todo: translate_pat [MLP_Const]")
end
| FStar_Extraction_ML_Syntax.MLP_Var (_79_818) -> begin
(FStar_All.failwith "todo: translate_pat [MLP_Var]")
end
| FStar_Extraction_ML_Syntax.MLP_CTor (_79_821) -> begin
(FStar_All.failwith "todo: translate_pat [MLP_CTor]")
end
| FStar_Extraction_ML_Syntax.MLP_Branch (_79_824) -> begin
(FStar_All.failwith "todo: translate_pat [MLP_Branch]")
end
| FStar_Extraction_ML_Syntax.MLP_Record (_79_827) -> begin
(FStar_All.failwith "todo: translate_pat [MLP_Record]")
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (_79_830) -> begin
(FStar_All.failwith "todo: translate_pat [MLP_Tuple]")
end))
and translate_constant : FStar_Extraction_ML_Syntax.mlconstant  ->  expr = (fun c -> (match (c) with
| FStar_Extraction_ML_Syntax.MLC_Unit -> begin
EUnit
end
| FStar_Extraction_ML_Syntax.MLC_Bool (_79_835) -> begin
(FStar_All.failwith "todo: translate_expr [MLC_Bool]")
end
| FStar_Extraction_ML_Syntax.MLC_Int (s, Some (_79_839)) -> begin
(FStar_All.failwith "impossible: machine integer not desugared to a function call")
end
| FStar_Extraction_ML_Syntax.MLC_Float (_79_844) -> begin
(FStar_All.failwith "todo: translate_expr [MLC_Float]")
end
| FStar_Extraction_ML_Syntax.MLC_Char (_79_847) -> begin
(FStar_All.failwith "todo: translate_expr [MLC_Char]")
end
| FStar_Extraction_ML_Syntax.MLC_String (_79_850) -> begin
(FStar_All.failwith "todo: translate_expr [MLC_String]")
end
| FStar_Extraction_ML_Syntax.MLC_Bytes (_79_853) -> begin
(FStar_All.failwith "todo: translate_expr [MLC_Bytes]")
end))
and mk_op : env  ->  op  ->  FStar_Extraction_ML_Syntax.mlexpr Prims.list  ->  expr = (fun env op args -> (let _170_548 = (let _170_547 = (FStar_List.map (translate_expr env) args)
in (EOp (op), _170_547))
in EApp (_170_548)))




