
open Prims
type mlsymbol =
Prims.string

type mlident =
(mlsymbol * Prims.int)

type mlpath =
(mlsymbol Prims.list * mlsymbol)

let idsym = (fun _69_4 -> (match (_69_4) with
| (s, _69_3) -> begin
s
end))

let string_of_mlpath = (fun _69_7 -> (match (_69_7) with
| (p, s) -> begin
(FStar_String.concat "." (FStar_List.append p ((s)::[])))
end))

let mlpath_of_lident = (fun x -> (let _146_8 = (FStar_List.map (fun x -> x.FStar_Ident.idText) x.FStar_Ident.ns)
in (_146_8, x.FStar_Ident.ident.FStar_Ident.idText)))

let as_mlident = (fun x -> (x.FStar_Absyn_Syntax.ppname.FStar_Ident.idText, 0))

type mlidents =
mlident Prims.list

type mlsymbols =
mlsymbol Prims.list

type e_tag =
| E_PURE
| E_GHOST
| E_IMPURE

let is_E_PURE = (fun _discr_ -> (match (_discr_) with
| E_PURE -> begin
true
end
| _ -> begin
false
end))

let is_E_GHOST = (fun _discr_ -> (match (_discr_) with
| E_GHOST -> begin
true
end
| _ -> begin
false
end))

let is_E_IMPURE = (fun _discr_ -> (match (_discr_) with
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

let is_MLTY_Var = (fun _discr_ -> (match (_discr_) with
| MLTY_Var (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLTY_Fun = (fun _discr_ -> (match (_discr_) with
| MLTY_Fun (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLTY_Named = (fun _discr_ -> (match (_discr_) with
| MLTY_Named (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLTY_Tuple = (fun _discr_ -> (match (_discr_) with
| MLTY_Tuple (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLTY_Top = (fun _discr_ -> (match (_discr_) with
| MLTY_Top -> begin
true
end
| _ -> begin
false
end))

let ___MLTY_Var____0 = (fun projectee -> (match (projectee) with
| MLTY_Var (_69_14) -> begin
_69_14
end))

let ___MLTY_Fun____0 = (fun projectee -> (match (projectee) with
| MLTY_Fun (_69_17) -> begin
_69_17
end))

let ___MLTY_Named____0 = (fun projectee -> (match (projectee) with
| MLTY_Named (_69_20) -> begin
_69_20
end))

let ___MLTY_Tuple____0 = (fun projectee -> (match (projectee) with
| MLTY_Tuple (_69_23) -> begin
_69_23
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

let is_MLC_Unit = (fun _discr_ -> (match (_discr_) with
| MLC_Unit -> begin
true
end
| _ -> begin
false
end))

let is_MLC_Bool = (fun _discr_ -> (match (_discr_) with
| MLC_Bool (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLC_Byte = (fun _discr_ -> (match (_discr_) with
| MLC_Byte (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLC_Int32 = (fun _discr_ -> (match (_discr_) with
| MLC_Int32 (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLC_Int64 = (fun _discr_ -> (match (_discr_) with
| MLC_Int64 (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLC_Int = (fun _discr_ -> (match (_discr_) with
| MLC_Int (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLC_Float = (fun _discr_ -> (match (_discr_) with
| MLC_Float (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLC_Char = (fun _discr_ -> (match (_discr_) with
| MLC_Char (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLC_String = (fun _discr_ -> (match (_discr_) with
| MLC_String (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLC_Bytes = (fun _discr_ -> (match (_discr_) with
| MLC_Bytes (_) -> begin
true
end
| _ -> begin
false
end))

let ___MLC_Bool____0 = (fun projectee -> (match (projectee) with
| MLC_Bool (_69_26) -> begin
_69_26
end))

let ___MLC_Byte____0 = (fun projectee -> (match (projectee) with
| MLC_Byte (_69_29) -> begin
_69_29
end))

let ___MLC_Int32____0 = (fun projectee -> (match (projectee) with
| MLC_Int32 (_69_32) -> begin
_69_32
end))

let ___MLC_Int64____0 = (fun projectee -> (match (projectee) with
| MLC_Int64 (_69_35) -> begin
_69_35
end))

let ___MLC_Int____0 = (fun projectee -> (match (projectee) with
| MLC_Int (_69_38) -> begin
_69_38
end))

let ___MLC_Float____0 = (fun projectee -> (match (projectee) with
| MLC_Float (_69_41) -> begin
_69_41
end))

let ___MLC_Char____0 = (fun projectee -> (match (projectee) with
| MLC_Char (_69_44) -> begin
_69_44
end))

let ___MLC_String____0 = (fun projectee -> (match (projectee) with
| MLC_String (_69_47) -> begin
_69_47
end))

let ___MLC_Bytes____0 = (fun projectee -> (match (projectee) with
| MLC_Bytes (_69_50) -> begin
_69_50
end))

type mlpattern =
| MLP_Wild
| MLP_Const of mlconstant
| MLP_Var of mlident
| MLP_CTor of (mlpath * mlpattern Prims.list)
| MLP_Branch of mlpattern Prims.list
| MLP_Record of (mlsymbol Prims.list * (mlsymbol * mlpattern) Prims.list)
| MLP_Tuple of mlpattern Prims.list

let is_MLP_Wild = (fun _discr_ -> (match (_discr_) with
| MLP_Wild -> begin
true
end
| _ -> begin
false
end))

let is_MLP_Const = (fun _discr_ -> (match (_discr_) with
| MLP_Const (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLP_Var = (fun _discr_ -> (match (_discr_) with
| MLP_Var (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLP_CTor = (fun _discr_ -> (match (_discr_) with
| MLP_CTor (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLP_Branch = (fun _discr_ -> (match (_discr_) with
| MLP_Branch (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLP_Record = (fun _discr_ -> (match (_discr_) with
| MLP_Record (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLP_Tuple = (fun _discr_ -> (match (_discr_) with
| MLP_Tuple (_) -> begin
true
end
| _ -> begin
false
end))

let ___MLP_Const____0 = (fun projectee -> (match (projectee) with
| MLP_Const (_69_53) -> begin
_69_53
end))

let ___MLP_Var____0 = (fun projectee -> (match (projectee) with
| MLP_Var (_69_56) -> begin
_69_56
end))

let ___MLP_CTor____0 = (fun projectee -> (match (projectee) with
| MLP_CTor (_69_59) -> begin
_69_59
end))

let ___MLP_Branch____0 = (fun projectee -> (match (projectee) with
| MLP_Branch (_69_62) -> begin
_69_62
end))

let ___MLP_Record____0 = (fun projectee -> (match (projectee) with
| MLP_Record (_69_65) -> begin
_69_65
end))

let ___MLP_Tuple____0 = (fun projectee -> (match (projectee) with
| MLP_Tuple (_69_68) -> begin
_69_68
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

let is_MLE_Const = (fun _discr_ -> (match (_discr_) with
| MLE_Const (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLE_Var = (fun _discr_ -> (match (_discr_) with
| MLE_Var (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLE_Name = (fun _discr_ -> (match (_discr_) with
| MLE_Name (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLE_Let = (fun _discr_ -> (match (_discr_) with
| MLE_Let (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLE_App = (fun _discr_ -> (match (_discr_) with
| MLE_App (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLE_Fun = (fun _discr_ -> (match (_discr_) with
| MLE_Fun (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLE_Match = (fun _discr_ -> (match (_discr_) with
| MLE_Match (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLE_Coerce = (fun _discr_ -> (match (_discr_) with
| MLE_Coerce (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLE_CTor = (fun _discr_ -> (match (_discr_) with
| MLE_CTor (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLE_Seq = (fun _discr_ -> (match (_discr_) with
| MLE_Seq (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLE_Tuple = (fun _discr_ -> (match (_discr_) with
| MLE_Tuple (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLE_Record = (fun _discr_ -> (match (_discr_) with
| MLE_Record (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLE_Proj = (fun _discr_ -> (match (_discr_) with
| MLE_Proj (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLE_If = (fun _discr_ -> (match (_discr_) with
| MLE_If (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLE_Raise = (fun _discr_ -> (match (_discr_) with
| MLE_Raise (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLE_Try = (fun _discr_ -> (match (_discr_) with
| MLE_Try (_) -> begin
true
end
| _ -> begin
false
end))

let is_Mkmlexpr = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkmlexpr"))))

let is_Mkmllb = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkmllb"))))

let ___MLE_Const____0 = (fun projectee -> (match (projectee) with
| MLE_Const (_69_77) -> begin
_69_77
end))

let ___MLE_Var____0 = (fun projectee -> (match (projectee) with
| MLE_Var (_69_80) -> begin
_69_80
end))

let ___MLE_Name____0 = (fun projectee -> (match (projectee) with
| MLE_Name (_69_83) -> begin
_69_83
end))

let ___MLE_Let____0 = (fun projectee -> (match (projectee) with
| MLE_Let (_69_86) -> begin
_69_86
end))

let ___MLE_App____0 = (fun projectee -> (match (projectee) with
| MLE_App (_69_89) -> begin
_69_89
end))

let ___MLE_Fun____0 = (fun projectee -> (match (projectee) with
| MLE_Fun (_69_92) -> begin
_69_92
end))

let ___MLE_Match____0 = (fun projectee -> (match (projectee) with
| MLE_Match (_69_95) -> begin
_69_95
end))

let ___MLE_Coerce____0 = (fun projectee -> (match (projectee) with
| MLE_Coerce (_69_98) -> begin
_69_98
end))

let ___MLE_CTor____0 = (fun projectee -> (match (projectee) with
| MLE_CTor (_69_101) -> begin
_69_101
end))

let ___MLE_Seq____0 = (fun projectee -> (match (projectee) with
| MLE_Seq (_69_104) -> begin
_69_104
end))

let ___MLE_Tuple____0 = (fun projectee -> (match (projectee) with
| MLE_Tuple (_69_107) -> begin
_69_107
end))

let ___MLE_Record____0 = (fun projectee -> (match (projectee) with
| MLE_Record (_69_110) -> begin
_69_110
end))

let ___MLE_Proj____0 = (fun projectee -> (match (projectee) with
| MLE_Proj (_69_113) -> begin
_69_113
end))

let ___MLE_If____0 = (fun projectee -> (match (projectee) with
| MLE_If (_69_116) -> begin
_69_116
end))

let ___MLE_Raise____0 = (fun projectee -> (match (projectee) with
| MLE_Raise (_69_119) -> begin
_69_119
end))

let ___MLE_Try____0 = (fun projectee -> (match (projectee) with
| MLE_Try (_69_122) -> begin
_69_122
end))

type mltybody =
| MLTD_Abbrev of mlty
| MLTD_Record of (mlsymbol * mlty) Prims.list
| MLTD_DType of (mlsymbol * mlty Prims.list) Prims.list

let is_MLTD_Abbrev = (fun _discr_ -> (match (_discr_) with
| MLTD_Abbrev (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLTD_Record = (fun _discr_ -> (match (_discr_) with
| MLTD_Record (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLTD_DType = (fun _discr_ -> (match (_discr_) with
| MLTD_DType (_) -> begin
true
end
| _ -> begin
false
end))

let ___MLTD_Abbrev____0 = (fun projectee -> (match (projectee) with
| MLTD_Abbrev (_69_127) -> begin
_69_127
end))

let ___MLTD_Record____0 = (fun projectee -> (match (projectee) with
| MLTD_Record (_69_130) -> begin
_69_130
end))

let ___MLTD_DType____0 = (fun projectee -> (match (projectee) with
| MLTD_DType (_69_133) -> begin
_69_133
end))

type mltydecl =
(mlsymbol * mlidents * mltybody Prims.option) Prims.list

type mlmodule1 =
| MLM_Ty of mltydecl
| MLM_Let of mlletbinding
| MLM_Exn of (mlsymbol * mlty Prims.list)
| MLM_Top of mlexpr

let is_MLM_Ty = (fun _discr_ -> (match (_discr_) with
| MLM_Ty (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLM_Let = (fun _discr_ -> (match (_discr_) with
| MLM_Let (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLM_Exn = (fun _discr_ -> (match (_discr_) with
| MLM_Exn (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLM_Top = (fun _discr_ -> (match (_discr_) with
| MLM_Top (_) -> begin
true
end
| _ -> begin
false
end))

let ___MLM_Ty____0 = (fun projectee -> (match (projectee) with
| MLM_Ty (_69_136) -> begin
_69_136
end))

let ___MLM_Let____0 = (fun projectee -> (match (projectee) with
| MLM_Let (_69_139) -> begin
_69_139
end))

let ___MLM_Exn____0 = (fun projectee -> (match (projectee) with
| MLM_Exn (_69_142) -> begin
_69_142
end))

let ___MLM_Top____0 = (fun projectee -> (match (projectee) with
| MLM_Top (_69_145) -> begin
_69_145
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

let is_MLS_Mod = (fun _discr_ -> (match (_discr_) with
| MLS_Mod (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLS_Ty = (fun _discr_ -> (match (_discr_) with
| MLS_Ty (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLS_Val = (fun _discr_ -> (match (_discr_) with
| MLS_Val (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLS_Exn = (fun _discr_ -> (match (_discr_) with
| MLS_Exn (_) -> begin
true
end
| _ -> begin
false
end))

let ___MLS_Mod____0 = (fun projectee -> (match (projectee) with
| MLS_Mod (_69_148) -> begin
_69_148
end))

let ___MLS_Ty____0 = (fun projectee -> (match (projectee) with
| MLS_Ty (_69_151) -> begin
_69_151
end))

let ___MLS_Val____0 = (fun projectee -> (match (projectee) with
| MLS_Val (_69_154) -> begin
_69_154
end))

let ___MLS_Exn____0 = (fun projectee -> (match (projectee) with
| MLS_Exn (_69_157) -> begin
_69_157
end))

let with_ty = (fun t e -> {expr = e; ty = t})

type mllib =
| MLLib of (mlsymbol * (mlsig * mlmodule) Prims.option * mllib) Prims.list

let is_MLLib = (fun _discr_ -> (match (_discr_) with
| MLLib (_) -> begin
true
end
| _ -> begin
false
end))

let ___MLLib____0 = (fun projectee -> (match (projectee) with
| MLLib (_69_161) -> begin
_69_161
end))

let ml_unit_ty = MLTY_Named (([], (("Prims")::[], "unit")))

let ml_bool_ty = MLTY_Named (([], (("Prims")::[], "bool")))

let ml_int_ty = MLTY_Named (([], (("Prims")::[], "int")))

let ml_string_ty = MLTY_Named (([], (("Prims")::[], "string")))

let ml_unit = (FStar_All.pipe_left (with_ty ml_unit_ty) (MLE_Const (MLC_Unit)))

let mlp_lalloc = (("SST")::[], "lalloc")

let apply_obj_repr = (fun x t -> (let obj_repr = (FStar_All.pipe_left (with_ty (MLTY_Fun ((t, E_PURE, MLTY_Top)))) (MLE_Name ((("Obj")::[], "repr"))))
in (FStar_All.pipe_left (with_ty MLTY_Top) (MLE_App ((obj_repr, (x)::[]))))))




