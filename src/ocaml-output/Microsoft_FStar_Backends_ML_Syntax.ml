
type mlsymbol =
string

type mlident =
(mlsymbol * int)

type mlpath =
(mlsymbol list * mlsymbol)

let idsym = (fun ( _55_4 ) -> (match (_55_4) with
| (s, _) -> begin
s
end))

let string_of_mlpath = (fun ( _55_7 ) -> (match (_55_7) with
| (p, s) -> begin
(Support.String.concat "." (Support.List.append p ((s)::[])))
end))

let mlpath_of_lident = (fun ( x ) -> (let _65_23704 = (Support.List.map (fun ( x ) -> x.Microsoft_FStar_Absyn_Syntax.idText) x.Microsoft_FStar_Absyn_Syntax.ns)
in (_65_23704, x.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText)))

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

let is_Mkmllb = (fun ( _ ) -> (failwith ("Not yet implemented")))

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

type mllib =
| MLLib of (mlsymbol * (mlsig * mlmodule) option * mllib) list

let is_MLLib = (fun ( _discr_ ) -> (match (_discr_) with
| MLLib (_) -> begin
true
end
| _ -> begin
false
end))

let mlseq = (fun ( e1 ) ( e2 ) -> (match (e2) with
| MLE_Seq (s) -> begin
MLE_Seq ((e1)::s)
end
| _ -> begin
MLE_Seq ((e1)::(e2)::[])
end))

let mlfun = (fun ( x ) ( e ) -> (match (e) with
| MLE_Fun ((xs, e)) -> begin
MLE_Fun ((((x, None))::xs, e))
end
| _ -> begin
MLE_Fun ((((x, None))::[], e))
end))

let mlif = (fun ( b ) ( _55_127 ) -> (match (_55_127) with
| (e1, e2) -> begin
(match (e2) with
| MLE_Const (MLC_Unit) -> begin
MLE_If ((b, e1, None))
end
| _ -> begin
MLE_If ((b, e1, Some (e2)))
end)
end))

let ml_unit = MLE_Const (MLC_Unit)

let ml_bool_ty = MLTY_Named (([], (("Prims")::[], "bool")))

let ml_unit_ty = MLTY_Named (([], (("Prims")::[], "unit")))




