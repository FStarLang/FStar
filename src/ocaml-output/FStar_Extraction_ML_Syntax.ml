
open Prims
type mlsymbol =
Prims.string

type mlident =
(mlsymbol * Prims.int)

type mlpath =
(mlsymbol Prims.list * mlsymbol)

let idsym : mlident  ->  mlsymbol = (fun _74_4 -> (match (_74_4) with
| (s, _74_3) -> begin
s
end))

let string_of_mlpath : mlpath  ->  mlsymbol = (fun _74_7 -> (match (_74_7) with
| (p, s) -> begin
(FStar_String.concat "." (FStar_List.append p ((s)::[])))
end))

let mlpath_of_lident : FStar_Ident.lident  ->  (Prims.string Prims.list * Prims.string) = (fun x -> (let _177_8 = (FStar_List.map (fun x -> x.FStar_Ident.idText) x.FStar_Ident.ns)
in (_177_8, x.FStar_Ident.ident.FStar_Ident.idText)))

let as_mlident = (fun x -> (x.FStar_Absyn_Syntax.ppname.FStar_Ident.idText, 0))

type mlidents =
mlident Prims.list

type mlsymbols =
mlsymbol Prims.list

type e_tag =
| E_PURE
| E_GHOST
| E_IMPURE

let is_E_PURE : e_tag  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| E_PURE -> begin
true
end
| _ -> begin
false
end))

let is_E_GHOST : e_tag  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| E_GHOST -> begin
true
end
| _ -> begin
false
end))

let is_E_IMPURE : e_tag  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| E_IMPURE -> begin
true
end
| _ -> begin
false
end))

type mlty =
| MLTY_Var of mlident
| MLTY_Fun of (mlty * e_tag * mlty)
| MLTY_Named of (mlty Prims.list * mlpath)
| MLTY_Tuple of mlty Prims.list
| MLTY_Top

let is_MLTY_Var : mlty  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| MLTY_Var (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLTY_Fun : mlty  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| MLTY_Fun (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLTY_Named : mlty  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| MLTY_Named (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLTY_Tuple : mlty  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| MLTY_Tuple (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLTY_Top : mlty  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| MLTY_Top -> begin
true
end
| _ -> begin
false
end))

let ___MLTY_Var____0 : mlty  ->  mlident = (fun projectee -> (match (projectee) with
| MLTY_Var (_74_14) -> begin
_74_14
end))

let ___MLTY_Fun____0 : mlty  ->  (mlty * e_tag * mlty) = (fun projectee -> (match (projectee) with
| MLTY_Fun (_74_17) -> begin
_74_17
end))

let ___MLTY_Named____0 : mlty  ->  (mlty Prims.list * mlpath) = (fun projectee -> (match (projectee) with
| MLTY_Named (_74_20) -> begin
_74_20
end))

let ___MLTY_Tuple____0 : mlty  ->  mlty Prims.list = (fun projectee -> (match (projectee) with
| MLTY_Tuple (_74_23) -> begin
_74_23
end))

type mltyscheme =
(mlidents * mlty)

type mlconstant =
| MLC_Unit
| MLC_Bool of Prims.bool
| MLC_Byte of Prims.byte
| MLC_Int32 of Prims.int32
| MLC_Int64 of Prims.int64
| MLC_Int of Prims.string
| MLC_Float of Prims.float
| MLC_Char of Prims.char
| MLC_String of Prims.string
| MLC_Bytes of Prims.byte Prims.array

let is_MLC_Unit : mlconstant  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| MLC_Unit -> begin
true
end
| _ -> begin
false
end))

let is_MLC_Bool : mlconstant  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| MLC_Bool (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLC_Byte : mlconstant  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| MLC_Byte (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLC_Int32 : mlconstant  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| MLC_Int32 (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLC_Int64 : mlconstant  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| MLC_Int64 (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLC_Int : mlconstant  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| MLC_Int (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLC_Float : mlconstant  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| MLC_Float (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLC_Char : mlconstant  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| MLC_Char (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLC_String : mlconstant  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| MLC_String (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLC_Bytes : mlconstant  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| MLC_Bytes (_) -> begin
true
end
| _ -> begin
false
end))

let ___MLC_Bool____0 : mlconstant  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MLC_Bool (_74_26) -> begin
_74_26
end))

let ___MLC_Byte____0 : mlconstant  ->  Prims.byte = (fun projectee -> (match (projectee) with
| MLC_Byte (_74_29) -> begin
_74_29
end))

let ___MLC_Int32____0 : mlconstant  ->  Prims.int32 = (fun projectee -> (match (projectee) with
| MLC_Int32 (_74_32) -> begin
_74_32
end))

let ___MLC_Int64____0 : mlconstant  ->  Prims.int64 = (fun projectee -> (match (projectee) with
| MLC_Int64 (_74_35) -> begin
_74_35
end))

let ___MLC_Int____0 : mlconstant  ->  Prims.string = (fun projectee -> (match (projectee) with
| MLC_Int (_74_38) -> begin
_74_38
end))

let ___MLC_Float____0 : mlconstant  ->  Prims.float = (fun projectee -> (match (projectee) with
| MLC_Float (_74_41) -> begin
_74_41
end))

let ___MLC_Char____0 : mlconstant  ->  Prims.char = (fun projectee -> (match (projectee) with
| MLC_Char (_74_44) -> begin
_74_44
end))

let ___MLC_String____0 : mlconstant  ->  Prims.string = (fun projectee -> (match (projectee) with
| MLC_String (_74_47) -> begin
_74_47
end))

let ___MLC_Bytes____0 : mlconstant  ->  Prims.byte Prims.array = (fun projectee -> (match (projectee) with
| MLC_Bytes (_74_50) -> begin
_74_50
end))

type mlpattern =
| MLP_Wild
| MLP_Const of mlconstant
| MLP_Var of mlident
| MLP_CTor of (mlpath * mlpattern Prims.list)
| MLP_Branch of mlpattern Prims.list
| MLP_Record of (mlsymbol Prims.list * (mlsymbol * mlpattern) Prims.list)
| MLP_Tuple of mlpattern Prims.list

let is_MLP_Wild : mlpattern  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| MLP_Wild -> begin
true
end
| _ -> begin
false
end))

let is_MLP_Const : mlpattern  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| MLP_Const (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLP_Var : mlpattern  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| MLP_Var (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLP_CTor : mlpattern  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| MLP_CTor (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLP_Branch : mlpattern  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| MLP_Branch (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLP_Record : mlpattern  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| MLP_Record (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLP_Tuple : mlpattern  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| MLP_Tuple (_) -> begin
true
end
| _ -> begin
false
end))

let ___MLP_Const____0 : mlpattern  ->  mlconstant = (fun projectee -> (match (projectee) with
| MLP_Const (_74_53) -> begin
_74_53
end))

let ___MLP_Var____0 : mlpattern  ->  mlident = (fun projectee -> (match (projectee) with
| MLP_Var (_74_56) -> begin
_74_56
end))

let ___MLP_CTor____0 : mlpattern  ->  (mlpath * mlpattern Prims.list) = (fun projectee -> (match (projectee) with
| MLP_CTor (_74_59) -> begin
_74_59
end))

let ___MLP_Branch____0 : mlpattern  ->  mlpattern Prims.list = (fun projectee -> (match (projectee) with
| MLP_Branch (_74_62) -> begin
_74_62
end))

let ___MLP_Record____0 : mlpattern  ->  (mlsymbol Prims.list * (mlsymbol * mlpattern) Prims.list) = (fun projectee -> (match (projectee) with
| MLP_Record (_74_65) -> begin
_74_65
end))

let ___MLP_Tuple____0 : mlpattern  ->  mlpattern Prims.list = (fun projectee -> (match (projectee) with
| MLP_Tuple (_74_68) -> begin
_74_68
end))

type mlexpr' =
| MLE_Const of mlconstant
| MLE_Var of mlident
| MLE_Name of mlpath
| MLE_Let of (mlletbinding * mlexpr)
| MLE_App of (mlexpr * mlexpr Prims.list)
| MLE_Fun of ((mlident * mlty) Prims.list * mlexpr)
| MLE_Match of (mlexpr * mlbranch Prims.list)
| MLE_Coerce of (mlexpr * mlty * mlty)
| MLE_CTor of (mlpath * mlexpr Prims.list)
| MLE_Seq of mlexpr Prims.list
| MLE_Tuple of mlexpr Prims.list
| MLE_Record of (mlsymbol Prims.list * (mlsymbol * mlexpr) Prims.list)
| MLE_Proj of (mlexpr * mlpath)
| MLE_If of (mlexpr * mlexpr * mlexpr Prims.option)
| MLE_Raise of (mlpath * mlexpr Prims.list)
| MLE_Try of (mlexpr * mlbranch Prims.list) 
 and mlexpr =
{expr : mlexpr'; ty : mlty} 
 and mllb =
{mllb_name : mlident; mllb_tysc : mltyscheme; mllb_add_unit : Prims.bool; mllb_def : mlexpr} 
 and mlbranch =
(mlpattern * mlexpr Prims.option * mlexpr) 
 and mlletbinding =
(Prims.bool * mllb Prims.list)

let is_MLE_Const : mlexpr'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| MLE_Const (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLE_Var : mlexpr'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| MLE_Var (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLE_Name : mlexpr'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| MLE_Name (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLE_Let : mlexpr'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| MLE_Let (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLE_App : mlexpr'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| MLE_App (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLE_Fun : mlexpr'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| MLE_Fun (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLE_Match : mlexpr'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| MLE_Match (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLE_Coerce : mlexpr'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| MLE_Coerce (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLE_CTor : mlexpr'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| MLE_CTor (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLE_Seq : mlexpr'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| MLE_Seq (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLE_Tuple : mlexpr'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| MLE_Tuple (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLE_Record : mlexpr'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| MLE_Record (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLE_Proj : mlexpr'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| MLE_Proj (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLE_If : mlexpr'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| MLE_If (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLE_Raise : mlexpr'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| MLE_Raise (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLE_Try : mlexpr'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| MLE_Try (_) -> begin
true
end
| _ -> begin
false
end))

let is_Mkmlexpr : mlexpr  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkmlexpr"))))

let is_Mkmllb : mllb  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkmllb"))))

let ___MLE_Const____0 : mlexpr'  ->  mlconstant = (fun projectee -> (match (projectee) with
| MLE_Const (_74_77) -> begin
_74_77
end))

let ___MLE_Var____0 : mlexpr'  ->  mlident = (fun projectee -> (match (projectee) with
| MLE_Var (_74_80) -> begin
_74_80
end))

let ___MLE_Name____0 : mlexpr'  ->  mlpath = (fun projectee -> (match (projectee) with
| MLE_Name (_74_83) -> begin
_74_83
end))

let ___MLE_Let____0 : mlexpr'  ->  (mlletbinding * mlexpr) = (fun projectee -> (match (projectee) with
| MLE_Let (_74_86) -> begin
_74_86
end))

let ___MLE_App____0 : mlexpr'  ->  (mlexpr * mlexpr Prims.list) = (fun projectee -> (match (projectee) with
| MLE_App (_74_89) -> begin
_74_89
end))

let ___MLE_Fun____0 : mlexpr'  ->  ((mlident * mlty) Prims.list * mlexpr) = (fun projectee -> (match (projectee) with
| MLE_Fun (_74_92) -> begin
_74_92
end))

let ___MLE_Match____0 : mlexpr'  ->  (mlexpr * mlbranch Prims.list) = (fun projectee -> (match (projectee) with
| MLE_Match (_74_95) -> begin
_74_95
end))

let ___MLE_Coerce____0 : mlexpr'  ->  (mlexpr * mlty * mlty) = (fun projectee -> (match (projectee) with
| MLE_Coerce (_74_98) -> begin
_74_98
end))

let ___MLE_CTor____0 : mlexpr'  ->  (mlpath * mlexpr Prims.list) = (fun projectee -> (match (projectee) with
| MLE_CTor (_74_101) -> begin
_74_101
end))

let ___MLE_Seq____0 : mlexpr'  ->  mlexpr Prims.list = (fun projectee -> (match (projectee) with
| MLE_Seq (_74_104) -> begin
_74_104
end))

let ___MLE_Tuple____0 : mlexpr'  ->  mlexpr Prims.list = (fun projectee -> (match (projectee) with
| MLE_Tuple (_74_107) -> begin
_74_107
end))

let ___MLE_Record____0 : mlexpr'  ->  (mlsymbol Prims.list * (mlsymbol * mlexpr) Prims.list) = (fun projectee -> (match (projectee) with
| MLE_Record (_74_110) -> begin
_74_110
end))

let ___MLE_Proj____0 : mlexpr'  ->  (mlexpr * mlpath) = (fun projectee -> (match (projectee) with
| MLE_Proj (_74_113) -> begin
_74_113
end))

let ___MLE_If____0 : mlexpr'  ->  (mlexpr * mlexpr * mlexpr Prims.option) = (fun projectee -> (match (projectee) with
| MLE_If (_74_116) -> begin
_74_116
end))

let ___MLE_Raise____0 : mlexpr'  ->  (mlpath * mlexpr Prims.list) = (fun projectee -> (match (projectee) with
| MLE_Raise (_74_119) -> begin
_74_119
end))

let ___MLE_Try____0 : mlexpr'  ->  (mlexpr * mlbranch Prims.list) = (fun projectee -> (match (projectee) with
| MLE_Try (_74_122) -> begin
_74_122
end))

type mltybody =
| MLTD_Abbrev of mlty
| MLTD_Record of (mlsymbol * mlty) Prims.list
| MLTD_DType of (mlsymbol * mlty Prims.list) Prims.list

let is_MLTD_Abbrev : mltybody  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| MLTD_Abbrev (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLTD_Record : mltybody  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| MLTD_Record (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLTD_DType : mltybody  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| MLTD_DType (_) -> begin
true
end
| _ -> begin
false
end))

let ___MLTD_Abbrev____0 : mltybody  ->  mlty = (fun projectee -> (match (projectee) with
| MLTD_Abbrev (_74_127) -> begin
_74_127
end))

let ___MLTD_Record____0 : mltybody  ->  (mlsymbol * mlty) Prims.list = (fun projectee -> (match (projectee) with
| MLTD_Record (_74_130) -> begin
_74_130
end))

let ___MLTD_DType____0 : mltybody  ->  (mlsymbol * mlty Prims.list) Prims.list = (fun projectee -> (match (projectee) with
| MLTD_DType (_74_133) -> begin
_74_133
end))

type mltydecl =
(mlsymbol * mlidents * mltybody Prims.option) Prims.list

type mlmodule1 =
| MLM_Ty of mltydecl
| MLM_Let of mlletbinding
| MLM_Exn of (mlsymbol * mlty Prims.list)
| MLM_Top of mlexpr

let is_MLM_Ty : mlmodule1  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| MLM_Ty (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLM_Let : mlmodule1  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| MLM_Let (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLM_Exn : mlmodule1  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| MLM_Exn (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLM_Top : mlmodule1  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| MLM_Top (_) -> begin
true
end
| _ -> begin
false
end))

let ___MLM_Ty____0 : mlmodule1  ->  mltydecl = (fun projectee -> (match (projectee) with
| MLM_Ty (_74_136) -> begin
_74_136
end))

let ___MLM_Let____0 : mlmodule1  ->  mlletbinding = (fun projectee -> (match (projectee) with
| MLM_Let (_74_139) -> begin
_74_139
end))

let ___MLM_Exn____0 : mlmodule1  ->  (mlsymbol * mlty Prims.list) = (fun projectee -> (match (projectee) with
| MLM_Exn (_74_142) -> begin
_74_142
end))

let ___MLM_Top____0 : mlmodule1  ->  mlexpr = (fun projectee -> (match (projectee) with
| MLM_Top (_74_145) -> begin
_74_145
end))

type mlmodule =
mlmodule1 Prims.list

type mlsig1 =
| MLS_Mod of (mlsymbol * mlsig)
| MLS_Ty of mltydecl
| MLS_Val of (mlsymbol * mltyscheme)
| MLS_Exn of (mlsymbol * mlty Prims.list) 
 and mlsig =
mlsig1 Prims.list

let is_MLS_Mod : mlsig1  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| MLS_Mod (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLS_Ty : mlsig1  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| MLS_Ty (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLS_Val : mlsig1  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| MLS_Val (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLS_Exn : mlsig1  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| MLS_Exn (_) -> begin
true
end
| _ -> begin
false
end))

let ___MLS_Mod____0 : mlsig1  ->  (mlsymbol * mlsig) = (fun projectee -> (match (projectee) with
| MLS_Mod (_74_148) -> begin
_74_148
end))

let ___MLS_Ty____0 : mlsig1  ->  mltydecl = (fun projectee -> (match (projectee) with
| MLS_Ty (_74_151) -> begin
_74_151
end))

let ___MLS_Val____0 : mlsig1  ->  (mlsymbol * mltyscheme) = (fun projectee -> (match (projectee) with
| MLS_Val (_74_154) -> begin
_74_154
end))

let ___MLS_Exn____0 : mlsig1  ->  (mlsymbol * mlty Prims.list) = (fun projectee -> (match (projectee) with
| MLS_Exn (_74_157) -> begin
_74_157
end))

let with_ty : mlty  ->  mlexpr'  ->  mlexpr = (fun t e -> {expr = e; ty = t})

type mllib =
| MLLib of (mlsymbol * (mlsig * mlmodule) Prims.option * mllib) Prims.list

let is_MLLib : mllib  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| MLLib (_) -> begin
true
end
| _ -> begin
false
end))

let ___MLLib____0 : mllib  ->  (mlsymbol * (mlsig * mlmodule) Prims.option * mllib) Prims.list = (fun projectee -> (match (projectee) with
| MLLib (_74_161) -> begin
_74_161
end))

let ml_unit_ty : mlty = MLTY_Named (([], (("Prims")::[], "unit")))

let ml_bool_ty : mlty = MLTY_Named (([], (("Prims")::[], "bool")))

let ml_int_ty : mlty = MLTY_Named (([], (("Prims")::[], "int")))

let ml_string_ty : mlty = MLTY_Named (([], (("Prims")::[], "string")))

let ml_unit : mlexpr = (FStar_All.pipe_left (with_ty ml_unit_ty) (MLE_Const (MLC_Unit)))

let mlp_lalloc : (Prims.string Prims.list * Prims.string) = (("SST")::[], "lalloc")

let apply_obj_repr : mlexpr  ->  mlty  ->  mlexpr = (fun x t -> (let obj_repr = (FStar_All.pipe_left (with_ty (MLTY_Fun ((t, E_PURE, MLTY_Top)))) (MLE_Name ((("Obj")::[], "repr"))))
in (FStar_All.pipe_left (with_ty MLTY_Top) (MLE_App ((obj_repr, (x)::[]))))))




