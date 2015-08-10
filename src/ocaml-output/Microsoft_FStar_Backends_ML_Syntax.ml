
type mlsymbol =
string

type mlident =
(mlsymbol * int)

type mlpath =
(mlsymbol list * mlsymbol)

let idsym = (fun ( _65_4 ) -> (match (_65_4) with
| (s, _65_3) -> begin
s
end))

let ptsym = (fun ( _65_7 ) -> (match (_65_7) with
| (p, s) -> begin
(let s = (match (((let _70_28486 = (Support.String.get s 0)
in (Support.Char.lowercase _70_28486)) <> (Support.String.get s 0))) with
| true -> begin
(Support.String.strcat "l__" s)
end
| false -> begin
s
end)
in (Support.String.concat "." (Support.List.append p ((s)::[]))))
end))

let ptctor = (fun ( _65_11 ) -> (match (_65_11) with
| (p, s) -> begin
(let s = (match (((let _70_28489 = (Support.String.get s 0)
in (Support.Char.uppercase _70_28489)) <> (Support.String.get s 0))) with
| true -> begin
(Support.String.strcat "U__" s)
end
| false -> begin
s
end)
in (Support.String.concat "." (Support.List.append p ((s)::[]))))
end))

let mlpath_of_lident = (fun ( x ) -> (let _70_28493 = (Support.List.map (fun ( x ) -> x.Microsoft_FStar_Absyn_Syntax.idText) x.Microsoft_FStar_Absyn_Syntax.ns)
in (_70_28493, x.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText)))

let as_mlident = (fun ( x ) -> (x.Microsoft_FStar_Absyn_Syntax.ppname.Microsoft_FStar_Absyn_Syntax.idText, 0))

type mlidents =
mlident list

type mlsymbols =
mlsymbol list

type e_tag =
| MayErase
| Keep

let is_MayErase = (fun ( _discr_ ) -> (match (_discr_) with
| MayErase -> begin
true
end
| _ -> begin
false
end))

let is_Keep = (fun ( _discr_ ) -> (match (_discr_) with
| Keep -> begin
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
| MLTY_Var (_65_19) -> begin
_65_19
end))

let ___MLTY_Fun____0 = (fun ( projectee ) -> (match (projectee) with
| MLTY_Fun (_65_22) -> begin
_65_22
end))

let ___MLTY_Named____0 = (fun ( projectee ) -> (match (projectee) with
| MLTY_Named (_65_25) -> begin
_65_25
end))

let ___MLTY_Tuple____0 = (fun ( projectee ) -> (match (projectee) with
| MLTY_Tuple (_65_28) -> begin
_65_28
end))

let ___MLTY_App____0 = (fun ( projectee ) -> (match (projectee) with
| MLTY_App (_65_31) -> begin
_65_31
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
| MLC_Bool (_65_34) -> begin
_65_34
end))

let ___MLC_Byte____0 = (fun ( projectee ) -> (match (projectee) with
| MLC_Byte (_65_37) -> begin
_65_37
end))

let ___MLC_Int32____0 = (fun ( projectee ) -> (match (projectee) with
| MLC_Int32 (_65_40) -> begin
_65_40
end))

let ___MLC_Int64____0 = (fun ( projectee ) -> (match (projectee) with
| MLC_Int64 (_65_43) -> begin
_65_43
end))

let ___MLC_Float____0 = (fun ( projectee ) -> (match (projectee) with
| MLC_Float (_65_46) -> begin
_65_46
end))

let ___MLC_Char____0 = (fun ( projectee ) -> (match (projectee) with
| MLC_Char (_65_49) -> begin
_65_49
end))

let ___MLC_String____0 = (fun ( projectee ) -> (match (projectee) with
| MLC_String (_65_52) -> begin
_65_52
end))

let ___MLC_Bytes____0 = (fun ( projectee ) -> (match (projectee) with
| MLC_Bytes (_65_55) -> begin
_65_55
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
| MLP_Const (_65_58) -> begin
_65_58
end))

let ___MLP_Var____0 = (fun ( projectee ) -> (match (projectee) with
| MLP_Var (_65_61) -> begin
_65_61
end))

let ___MLP_CTor____0 = (fun ( projectee ) -> (match (projectee) with
| MLP_CTor (_65_64) -> begin
_65_64
end))

let ___MLP_Branch____0 = (fun ( projectee ) -> (match (projectee) with
| MLP_Branch (_65_67) -> begin
_65_67
end))

let ___MLP_Record____0 = (fun ( projectee ) -> (match (projectee) with
| MLP_Record (_65_70) -> begin
_65_70
end))

let ___MLP_Tuple____0 = (fun ( projectee ) -> (match (projectee) with
| MLP_Tuple (_65_73) -> begin
_65_73
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
 and mlbranch =
(mlpattern * mlexpr option * mlexpr) 
 and mlletbinding =
(bool * (mlident * mltyscheme option * mlidents * mlexpr) list)

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

let ___MLE_Const____0 = (fun ( projectee ) -> (match (projectee) with
| MLE_Const (_65_76) -> begin
_65_76
end))

let ___MLE_Var____0 = (fun ( projectee ) -> (match (projectee) with
| MLE_Var (_65_79) -> begin
_65_79
end))

let ___MLE_Name____0 = (fun ( projectee ) -> (match (projectee) with
| MLE_Name (_65_82) -> begin
_65_82
end))

let ___MLE_Let____0 = (fun ( projectee ) -> (match (projectee) with
| MLE_Let (_65_85) -> begin
_65_85
end))

let ___MLE_App____0 = (fun ( projectee ) -> (match (projectee) with
| MLE_App (_65_88) -> begin
_65_88
end))

let ___MLE_Fun____0 = (fun ( projectee ) -> (match (projectee) with
| MLE_Fun (_65_91) -> begin
_65_91
end))

let ___MLE_Match____0 = (fun ( projectee ) -> (match (projectee) with
| MLE_Match (_65_94) -> begin
_65_94
end))

let ___MLE_Coerce____0 = (fun ( projectee ) -> (match (projectee) with
| MLE_Coerce (_65_97) -> begin
_65_97
end))

let ___MLE_CTor____0 = (fun ( projectee ) -> (match (projectee) with
| MLE_CTor (_65_100) -> begin
_65_100
end))

let ___MLE_Seq____0 = (fun ( projectee ) -> (match (projectee) with
| MLE_Seq (_65_103) -> begin
_65_103
end))

let ___MLE_Tuple____0 = (fun ( projectee ) -> (match (projectee) with
| MLE_Tuple (_65_106) -> begin
_65_106
end))

let ___MLE_Record____0 = (fun ( projectee ) -> (match (projectee) with
| MLE_Record (_65_109) -> begin
_65_109
end))

let ___MLE_Proj____0 = (fun ( projectee ) -> (match (projectee) with
| MLE_Proj (_65_112) -> begin
_65_112
end))

let ___MLE_If____0 = (fun ( projectee ) -> (match (projectee) with
| MLE_If (_65_115) -> begin
_65_115
end))

let ___MLE_Raise____0 = (fun ( projectee ) -> (match (projectee) with
| MLE_Raise (_65_118) -> begin
_65_118
end))

let ___MLE_Try____0 = (fun ( projectee ) -> (match (projectee) with
| MLE_Try (_65_121) -> begin
_65_121
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
| MLTD_Abbrev (_65_124) -> begin
_65_124
end))

let ___MLTD_Record____0 = (fun ( projectee ) -> (match (projectee) with
| MLTD_Record (_65_127) -> begin
_65_127
end))

let ___MLTD_DType____0 = (fun ( projectee ) -> (match (projectee) with
| MLTD_DType (_65_130) -> begin
_65_130
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
| MLM_Ty (_65_133) -> begin
_65_133
end))

let ___MLM_Let____0 = (fun ( projectee ) -> (match (projectee) with
| MLM_Let (_65_136) -> begin
_65_136
end))

let ___MLM_Exn____0 = (fun ( projectee ) -> (match (projectee) with
| MLM_Exn (_65_139) -> begin
_65_139
end))

let ___MLM_Top____0 = (fun ( projectee ) -> (match (projectee) with
| MLM_Top (_65_142) -> begin
_65_142
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
| MLS_Mod (_65_145) -> begin
_65_145
end))

let ___MLS_Ty____0 = (fun ( projectee ) -> (match (projectee) with
| MLS_Ty (_65_148) -> begin
_65_148
end))

let ___MLS_Val____0 = (fun ( projectee ) -> (match (projectee) with
| MLS_Val (_65_151) -> begin
_65_151
end))

let ___MLS_Exn____0 = (fun ( projectee ) -> (match (projectee) with
| MLS_Exn (_65_154) -> begin
_65_154
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
| MLLib (_65_156) -> begin
_65_156
end))

let mlseq = (fun ( e1 ) ( e2 ) -> (match (e2) with
| MLE_Seq (s) -> begin
MLE_Seq ((e1)::s)
end
| _65_162 -> begin
MLE_Seq ((e1)::(e2)::[])
end))

let mlfun = (fun ( x ) ( e ) -> (match (e) with
| MLE_Fun ((xs, e)) -> begin
MLE_Fun ((((x, None))::xs, e))
end
| _65_170 -> begin
MLE_Fun ((((x, None))::[], e))
end))

let mlif = (fun ( b ) ( _65_174 ) -> (match (_65_174) with
| (e1, e2) -> begin
(match (e2) with
| MLE_Const (MLC_Unit) -> begin
MLE_If ((b, e1, None))
end
| _65_178 -> begin
MLE_If ((b, e1, Some (e2)))
end)
end))




