
type mlsymbol =
string

type mlident =
(mlsymbol * int)

type mlpath =
(mlsymbol list * mlsymbol)

let idsym = (fun ( _55_4 ) -> (match (_55_4) with
| (s, _55_3) -> begin
s
end))

let string_of_mlpath = (fun ( _55_7 ) -> (match (_55_7) with
| (p, s) -> begin
(Support.String.concat "." (Support.List.append p ((s)::[])))
end))

let mlpath_of_lident = (fun ( x ) -> (let _119_8 = (Support.List.map (fun ( x ) -> x.Microsoft_FStar_Absyn_Syntax.idText) x.Microsoft_FStar_Absyn_Syntax.ns)
in (_119_8, x.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText)))

let as_mlident = (fun ( x ) -> (x.Microsoft_FStar_Absyn_Syntax.ppname.Microsoft_FStar_Absyn_Syntax.idText, 0))

type mlidents =
mlident list

type mlsymbols =
mlsymbol list

type e_tag =
| E_PURE
| E_IMPURE

let is_E_PURE = (fun ( _discr_ ) -> (match (_discr_) with
| E_PURE -> begin
true
end
| _ -> begin
false
end))

let is_E_IMPURE = (fun ( _discr_ ) -> (match (_discr_) with
| E_IMPURE -> begin
true
end
| _ -> begin
false
end))

type mlty =
| MLTY_Var of mlident
| MLTY_Fun of (mlty * e_tag * mlty)
| MLTY_Named of (mlty list * mlpath)
| MLTY_Tuple of mlty list
| MLTY_App of (mlty * mlty)
| MLTY_Top

let is_MLTY_Var = (fun ( _discr_ ) -> (match (_discr_) with
| MLTY_Var (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLTY_Fun = (fun ( _discr_ ) -> (match (_discr_) with
| MLTY_Fun (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLTY_Named = (fun ( _discr_ ) -> (match (_discr_) with
| MLTY_Named (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLTY_Tuple = (fun ( _discr_ ) -> (match (_discr_) with
| MLTY_Tuple (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLTY_App = (fun ( _discr_ ) -> (match (_discr_) with
| MLTY_App (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLTY_Top = (fun ( _discr_ ) -> (match (_discr_) with
| MLTY_Top -> begin
true
end
| _ -> begin
false
end))

let ___MLTY_Var____0 = (fun ( projectee ) -> (match (projectee) with
| MLTY_Var (_55_14) -> begin
_55_14
end))

let ___MLTY_Fun____0 = (fun ( projectee ) -> (match (projectee) with
| MLTY_Fun (_55_17) -> begin
_55_17
end))

let ___MLTY_Named____0 = (fun ( projectee ) -> (match (projectee) with
| MLTY_Named (_55_20) -> begin
_55_20
end))

let ___MLTY_Tuple____0 = (fun ( projectee ) -> (match (projectee) with
| MLTY_Tuple (_55_23) -> begin
_55_23
end))

let ___MLTY_App____0 = (fun ( projectee ) -> (match (projectee) with
| MLTY_App (_55_26) -> begin
_55_26
end))

type mltyscheme =
(mlidents * mlty)

type mlconstant =
| MLC_Unit
| MLC_Bool of bool
| MLC_Byte of Support.Prims.byte
| MLC_Int32 of Support.Prims.int32
| MLC_Int64 of Int64.t
| MLC_Float of Support.Prims.float
| MLC_Char of char
| MLC_String of string
| MLC_Bytes of Support.Prims.byte array

let is_MLC_Unit = (fun ( _discr_ ) -> (match (_discr_) with
| MLC_Unit -> begin
true
end
| _ -> begin
false
end))

let is_MLC_Bool = (fun ( _discr_ ) -> (match (_discr_) with
| MLC_Bool (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLC_Byte = (fun ( _discr_ ) -> (match (_discr_) with
| MLC_Byte (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLC_Int32 = (fun ( _discr_ ) -> (match (_discr_) with
| MLC_Int32 (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLC_Int64 = (fun ( _discr_ ) -> (match (_discr_) with
| MLC_Int64 (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLC_Float = (fun ( _discr_ ) -> (match (_discr_) with
| MLC_Float (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLC_Char = (fun ( _discr_ ) -> (match (_discr_) with
| MLC_Char (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLC_String = (fun ( _discr_ ) -> (match (_discr_) with
| MLC_String (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLC_Bytes = (fun ( _discr_ ) -> (match (_discr_) with
| MLC_Bytes (_) -> begin
true
end
| _ -> begin
false
end))

let ___MLC_Bool____0 = (fun ( projectee ) -> (match (projectee) with
| MLC_Bool (_55_29) -> begin
_55_29
end))

let ___MLC_Byte____0 = (fun ( projectee ) -> (match (projectee) with
| MLC_Byte (_55_32) -> begin
_55_32
end))

let ___MLC_Int32____0 = (fun ( projectee ) -> (match (projectee) with
| MLC_Int32 (_55_35) -> begin
_55_35
end))

let ___MLC_Int64____0 = (fun ( projectee ) -> (match (projectee) with
| MLC_Int64 (_55_38) -> begin
_55_38
end))

let ___MLC_Float____0 = (fun ( projectee ) -> (match (projectee) with
| MLC_Float (_55_41) -> begin
_55_41
end))

let ___MLC_Char____0 = (fun ( projectee ) -> (match (projectee) with
| MLC_Char (_55_44) -> begin
_55_44
end))

let ___MLC_String____0 = (fun ( projectee ) -> (match (projectee) with
| MLC_String (_55_47) -> begin
_55_47
end))

let ___MLC_Bytes____0 = (fun ( projectee ) -> (match (projectee) with
| MLC_Bytes (_55_50) -> begin
_55_50
end))

type mlpattern =
| MLP_Wild
| MLP_Const of mlconstant
| MLP_Var of mlident
| MLP_CTor of (mlpath * mlpattern list)
| MLP_Branch of mlpattern list
| MLP_Record of (mlsymbol list * (mlsymbol * mlpattern) list)
| MLP_Tuple of mlpattern list

let is_MLP_Wild = (fun ( _discr_ ) -> (match (_discr_) with
| MLP_Wild -> begin
true
end
| _ -> begin
false
end))

let is_MLP_Const = (fun ( _discr_ ) -> (match (_discr_) with
| MLP_Const (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLP_Var = (fun ( _discr_ ) -> (match (_discr_) with
| MLP_Var (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLP_CTor = (fun ( _discr_ ) -> (match (_discr_) with
| MLP_CTor (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLP_Branch = (fun ( _discr_ ) -> (match (_discr_) with
| MLP_Branch (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLP_Record = (fun ( _discr_ ) -> (match (_discr_) with
| MLP_Record (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLP_Tuple = (fun ( _discr_ ) -> (match (_discr_) with
| MLP_Tuple (_) -> begin
true
end
| _ -> begin
false
end))

let ___MLP_Const____0 = (fun ( projectee ) -> (match (projectee) with
| MLP_Const (_55_53) -> begin
_55_53
end))

let ___MLP_Var____0 = (fun ( projectee ) -> (match (projectee) with
| MLP_Var (_55_56) -> begin
_55_56
end))

let ___MLP_CTor____0 = (fun ( projectee ) -> (match (projectee) with
| MLP_CTor (_55_59) -> begin
_55_59
end))

let ___MLP_Branch____0 = (fun ( projectee ) -> (match (projectee) with
| MLP_Branch (_55_62) -> begin
_55_62
end))

let ___MLP_Record____0 = (fun ( projectee ) -> (match (projectee) with
| MLP_Record (_55_65) -> begin
_55_65
end))

let ___MLP_Tuple____0 = (fun ( projectee ) -> (match (projectee) with
| MLP_Tuple (_55_68) -> begin
_55_68
end))

type mlexpr =
| MLE_Const of mlconstant
| MLE_Var of mlident
| MLE_Name of mlpath
| MLE_Let of (mlletbinding * mlexpr)
| MLE_App of (mlexpr * mlexpr list)
| MLE_Fun of ((mlident * mlty option) list * mlexpr)
| MLE_Match of (mlexpr * mlbranch list)
| MLE_Coerce of (mlexpr * mlty * mlty)
| MLE_CTor of (mlpath * mlexpr list)
| MLE_Seq of mlexpr list
| MLE_Tuple of mlexpr list
| MLE_Record of (mlsymbol list * (mlsymbol * mlexpr) list)
| MLE_Proj of (mlexpr * mlpath)
| MLE_If of (mlexpr * mlexpr * mlexpr option)
| MLE_Raise of (mlpath * mlexpr list)
| MLE_Try of (mlexpr * mlbranch list) 
 and mllb =
{mllb_name : mlident; mllb_tysc : mltyscheme option; mllb_add_unit : bool; mllb_def : mlexpr} 
 and mlbranch =
(mlpattern * mlexpr option * mlexpr) 
 and mlletbinding =
(bool * mllb list)

let is_MLE_Const = (fun ( _discr_ ) -> (match (_discr_) with
| MLE_Const (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLE_Var = (fun ( _discr_ ) -> (match (_discr_) with
| MLE_Var (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLE_Name = (fun ( _discr_ ) -> (match (_discr_) with
| MLE_Name (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLE_Let = (fun ( _discr_ ) -> (match (_discr_) with
| MLE_Let (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLE_App = (fun ( _discr_ ) -> (match (_discr_) with
| MLE_App (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLE_Fun = (fun ( _discr_ ) -> (match (_discr_) with
| MLE_Fun (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLE_Match = (fun ( _discr_ ) -> (match (_discr_) with
| MLE_Match (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLE_Coerce = (fun ( _discr_ ) -> (match (_discr_) with
| MLE_Coerce (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLE_CTor = (fun ( _discr_ ) -> (match (_discr_) with
| MLE_CTor (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLE_Seq = (fun ( _discr_ ) -> (match (_discr_) with
| MLE_Seq (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLE_Tuple = (fun ( _discr_ ) -> (match (_discr_) with
| MLE_Tuple (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLE_Record = (fun ( _discr_ ) -> (match (_discr_) with
| MLE_Record (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLE_Proj = (fun ( _discr_ ) -> (match (_discr_) with
| MLE_Proj (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLE_If = (fun ( _discr_ ) -> (match (_discr_) with
| MLE_If (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLE_Raise = (fun ( _discr_ ) -> (match (_discr_) with
| MLE_Raise (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLE_Try = (fun ( _discr_ ) -> (match (_discr_) with
| MLE_Try (_) -> begin
true
end
| _ -> begin
false
end))

let is_Mkmllb = (fun ( _ ) -> (Support.All.failwith "Not yet implemented:is_Mkmllb"))

let ___MLE_Const____0 = (fun ( projectee ) -> (match (projectee) with
| MLE_Const (_55_75) -> begin
_55_75
end))

let ___MLE_Var____0 = (fun ( projectee ) -> (match (projectee) with
| MLE_Var (_55_78) -> begin
_55_78
end))

let ___MLE_Name____0 = (fun ( projectee ) -> (match (projectee) with
| MLE_Name (_55_81) -> begin
_55_81
end))

let ___MLE_Let____0 = (fun ( projectee ) -> (match (projectee) with
| MLE_Let (_55_84) -> begin
_55_84
end))

let ___MLE_App____0 = (fun ( projectee ) -> (match (projectee) with
| MLE_App (_55_87) -> begin
_55_87
end))

let ___MLE_Fun____0 = (fun ( projectee ) -> (match (projectee) with
| MLE_Fun (_55_90) -> begin
_55_90
end))

let ___MLE_Match____0 = (fun ( projectee ) -> (match (projectee) with
| MLE_Match (_55_93) -> begin
_55_93
end))

let ___MLE_Coerce____0 = (fun ( projectee ) -> (match (projectee) with
| MLE_Coerce (_55_96) -> begin
_55_96
end))

let ___MLE_CTor____0 = (fun ( projectee ) -> (match (projectee) with
| MLE_CTor (_55_99) -> begin
_55_99
end))

let ___MLE_Seq____0 = (fun ( projectee ) -> (match (projectee) with
| MLE_Seq (_55_102) -> begin
_55_102
end))

let ___MLE_Tuple____0 = (fun ( projectee ) -> (match (projectee) with
| MLE_Tuple (_55_105) -> begin
_55_105
end))

let ___MLE_Record____0 = (fun ( projectee ) -> (match (projectee) with
| MLE_Record (_55_108) -> begin
_55_108
end))

let ___MLE_Proj____0 = (fun ( projectee ) -> (match (projectee) with
| MLE_Proj (_55_111) -> begin
_55_111
end))

let ___MLE_If____0 = (fun ( projectee ) -> (match (projectee) with
| MLE_If (_55_114) -> begin
_55_114
end))

let ___MLE_Raise____0 = (fun ( projectee ) -> (match (projectee) with
| MLE_Raise (_55_117) -> begin
_55_117
end))

let ___MLE_Try____0 = (fun ( projectee ) -> (match (projectee) with
| MLE_Try (_55_120) -> begin
_55_120
end))

type mltybody =
| MLTD_Abbrev of mlty
| MLTD_Record of (mlsymbol * mlty) list
| MLTD_DType of (mlsymbol * mlty list) list

let is_MLTD_Abbrev = (fun ( _discr_ ) -> (match (_discr_) with
| MLTD_Abbrev (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLTD_Record = (fun ( _discr_ ) -> (match (_discr_) with
| MLTD_Record (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLTD_DType = (fun ( _discr_ ) -> (match (_discr_) with
| MLTD_DType (_) -> begin
true
end
| _ -> begin
false
end))

let ___MLTD_Abbrev____0 = (fun ( projectee ) -> (match (projectee) with
| MLTD_Abbrev (_55_124) -> begin
_55_124
end))

let ___MLTD_Record____0 = (fun ( projectee ) -> (match (projectee) with
| MLTD_Record (_55_127) -> begin
_55_127
end))

let ___MLTD_DType____0 = (fun ( projectee ) -> (match (projectee) with
| MLTD_DType (_55_130) -> begin
_55_130
end))

type mltydecl =
(mlsymbol * mlidents * mltybody option) list

type mlmodule1 =
| MLM_Ty of mltydecl
| MLM_Let of mlletbinding
| MLM_Exn of (mlsymbol * mlty list)
| MLM_Top of mlexpr

let is_MLM_Ty = (fun ( _discr_ ) -> (match (_discr_) with
| MLM_Ty (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLM_Let = (fun ( _discr_ ) -> (match (_discr_) with
| MLM_Let (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLM_Exn = (fun ( _discr_ ) -> (match (_discr_) with
| MLM_Exn (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLM_Top = (fun ( _discr_ ) -> (match (_discr_) with
| MLM_Top (_) -> begin
true
end
| _ -> begin
false
end))

let ___MLM_Ty____0 = (fun ( projectee ) -> (match (projectee) with
| MLM_Ty (_55_133) -> begin
_55_133
end))

let ___MLM_Let____0 = (fun ( projectee ) -> (match (projectee) with
| MLM_Let (_55_136) -> begin
_55_136
end))

let ___MLM_Exn____0 = (fun ( projectee ) -> (match (projectee) with
| MLM_Exn (_55_139) -> begin
_55_139
end))

let ___MLM_Top____0 = (fun ( projectee ) -> (match (projectee) with
| MLM_Top (_55_142) -> begin
_55_142
end))

type mlmodule =
mlmodule1 list

type mlsig1 =
| MLS_Mod of (mlsymbol * mlsig)
| MLS_Ty of mltydecl
| MLS_Val of (mlsymbol * mltyscheme)
| MLS_Exn of (mlsymbol * mlty list) 
 and mlsig =
mlsig1 list

let is_MLS_Mod = (fun ( _discr_ ) -> (match (_discr_) with
| MLS_Mod (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLS_Ty = (fun ( _discr_ ) -> (match (_discr_) with
| MLS_Ty (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLS_Val = (fun ( _discr_ ) -> (match (_discr_) with
| MLS_Val (_) -> begin
true
end
| _ -> begin
false
end))

let is_MLS_Exn = (fun ( _discr_ ) -> (match (_discr_) with
| MLS_Exn (_) -> begin
true
end
| _ -> begin
false
end))

let ___MLS_Mod____0 = (fun ( projectee ) -> (match (projectee) with
| MLS_Mod (_55_145) -> begin
_55_145
end))

let ___MLS_Ty____0 = (fun ( projectee ) -> (match (projectee) with
| MLS_Ty (_55_148) -> begin
_55_148
end))

let ___MLS_Val____0 = (fun ( projectee ) -> (match (projectee) with
| MLS_Val (_55_151) -> begin
_55_151
end))

let ___MLS_Exn____0 = (fun ( projectee ) -> (match (projectee) with
| MLS_Exn (_55_154) -> begin
_55_154
end))

type mllib =
| MLLib of (mlsymbol * (mlsig * mlmodule) option * mllib) list

let is_MLLib = (fun ( _discr_ ) -> (match (_discr_) with
| MLLib (_) -> begin
true
end
| _ -> begin
false
end))

let ___MLLib____0 = (fun ( projectee ) -> (match (projectee) with
| MLLib (_55_156) -> begin
_55_156
end))

let mlseq = (fun ( e1 ) ( e2 ) -> (match (e2) with
| MLE_Seq (s) -> begin
MLE_Seq ((e1)::s)
end
| _55_162 -> begin
MLE_Seq ((e1)::(e2)::[])
end))

let mlfun = (fun ( x ) ( e ) -> (match (e) with
| MLE_Fun ((xs, e)) -> begin
MLE_Fun ((((x, None))::xs, e))
end
| _55_170 -> begin
MLE_Fun ((((x, None))::[], e))
end))

let mlif = (fun ( b ) ( _55_174 ) -> (match (_55_174) with
| (e1, e2) -> begin
(match (e2) with
| MLE_Const (MLC_Unit) -> begin
MLE_If ((b, e1, None))
end
| _55_178 -> begin
MLE_If ((b, e1, Some (e2)))
end)
end))

let ml_unit = MLE_Const (MLC_Unit)

let ml_bool_ty = MLTY_Named (([], (("Prims")::[], "bool")))

let ml_unit_ty = MLTY_Named (([], (("Prims")::[], "unit")))

let mlp_lalloc = (("SST")::[], "lalloc")




