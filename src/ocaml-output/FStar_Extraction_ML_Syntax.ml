
open Prims
# 8 "FStar.Extraction.ML.Syntax.fst"
type mlsymbol =
Prims.string

# 9 "FStar.Extraction.ML.Syntax.fst"
type mlident =
(mlsymbol * Prims.int)

# 10 "FStar.Extraction.ML.Syntax.fst"
type mlpath =
(mlsymbol Prims.list * mlsymbol)

# 13 "FStar.Extraction.ML.Syntax.fst"
let idsym : mlident  ->  mlsymbol = (fun _57_4 -> (match (_57_4) with
| (s, _57_3) -> begin
s
end))

# 16 "FStar.Extraction.ML.Syntax.fst"
let string_of_mlpath : mlpath  ->  mlsymbol = (fun _57_7 -> (match (_57_7) with
| (p, s) -> begin
(FStar_String.concat "." (FStar_List.append p ((s)::[])))
end))

# 22 "FStar.Extraction.ML.Syntax.fst"
let mlpath_of_lident : FStar_Ident.lident  ->  (Prims.string Prims.list * Prims.string) = (fun x -> (let _139_8 = (FStar_List.map (fun x -> x.FStar_Ident.idText) x.FStar_Ident.ns)
in (_139_8, x.FStar_Ident.ident.FStar_Ident.idText)))

# 25 "FStar.Extraction.ML.Syntax.fst"
let as_mlident = (fun x -> (x.FStar_Absyn_Syntax.ppname.FStar_Ident.idText, 0))

# 28 "FStar.Extraction.ML.Syntax.fst"
type mlidents =
mlident Prims.list

# 29 "FStar.Extraction.ML.Syntax.fst"
type mlsymbols =
mlsymbol Prims.list

# 32 "FStar.Extraction.ML.Syntax.fst"
type e_tag =
| E_PURE
| E_GHOST
| E_IMPURE

# 33 "FStar.Extraction.ML.Syntax.fst"
let is_E_PURE = (fun _discr_ -> (match (_discr_) with
| E_PURE (_) -> begin
true
end
| _ -> begin
false
end))

# 34 "FStar.Extraction.ML.Syntax.fst"
let is_E_GHOST = (fun _discr_ -> (match (_discr_) with
| E_GHOST (_) -> begin
true
end
| _ -> begin
false
end))

# 35 "FStar.Extraction.ML.Syntax.fst"
let is_E_IMPURE = (fun _discr_ -> (match (_discr_) with
| E_IMPURE (_) -> begin
true
end
| _ -> begin
false
end))

# 38 "FStar.Extraction.ML.Syntax.fst"
type mlloc =
(Prims.int * Prims.string)

# 39 "FStar.Extraction.ML.Syntax.fst"
let dummy_loc : (Prims.int * Prims.string) = (0, "")

# 41 "FStar.Extraction.ML.Syntax.fst"
type mlty =
| MLTY_Var of mlident
| MLTY_Fun of (mlty * e_tag * mlty)
| MLTY_Named of (mlty Prims.list * mlpath)
| MLTY_Tuple of mlty Prims.list
| MLTY_Top

# 42 "FStar.Extraction.ML.Syntax.fst"
let is_MLTY_Var = (fun _discr_ -> (match (_discr_) with
| MLTY_Var (_) -> begin
true
end
| _ -> begin
false
end))

# 43 "FStar.Extraction.ML.Syntax.fst"
let is_MLTY_Fun = (fun _discr_ -> (match (_discr_) with
| MLTY_Fun (_) -> begin
true
end
| _ -> begin
false
end))

# 44 "FStar.Extraction.ML.Syntax.fst"
let is_MLTY_Named = (fun _discr_ -> (match (_discr_) with
| MLTY_Named (_) -> begin
true
end
| _ -> begin
false
end))

# 45 "FStar.Extraction.ML.Syntax.fst"
let is_MLTY_Tuple = (fun _discr_ -> (match (_discr_) with
| MLTY_Tuple (_) -> begin
true
end
| _ -> begin
false
end))

# 46 "FStar.Extraction.ML.Syntax.fst"
let is_MLTY_Top = (fun _discr_ -> (match (_discr_) with
| MLTY_Top (_) -> begin
true
end
| _ -> begin
false
end))

# 42 "FStar.Extraction.ML.Syntax.fst"
let ___MLTY_Var____0 : mlty  ->  mlident = (fun projectee -> (match (projectee) with
| MLTY_Var (_57_14) -> begin
_57_14
end))

# 43 "FStar.Extraction.ML.Syntax.fst"
let ___MLTY_Fun____0 : mlty  ->  (mlty * e_tag * mlty) = (fun projectee -> (match (projectee) with
| MLTY_Fun (_57_17) -> begin
_57_17
end))

# 44 "FStar.Extraction.ML.Syntax.fst"
let ___MLTY_Named____0 : mlty  ->  (mlty Prims.list * mlpath) = (fun projectee -> (match (projectee) with
| MLTY_Named (_57_20) -> begin
_57_20
end))

# 45 "FStar.Extraction.ML.Syntax.fst"
let ___MLTY_Tuple____0 : mlty  ->  mlty Prims.list = (fun projectee -> (match (projectee) with
| MLTY_Tuple (_57_23) -> begin
_57_23
end))

# 48 "FStar.Extraction.ML.Syntax.fst"
type mltyscheme =
(mlidents * mlty)

# 50 "FStar.Extraction.ML.Syntax.fst"
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

# 51 "FStar.Extraction.ML.Syntax.fst"
let is_MLC_Unit = (fun _discr_ -> (match (_discr_) with
| MLC_Unit (_) -> begin
true
end
| _ -> begin
false
end))

# 52 "FStar.Extraction.ML.Syntax.fst"
let is_MLC_Bool = (fun _discr_ -> (match (_discr_) with
| MLC_Bool (_) -> begin
true
end
| _ -> begin
false
end))

# 53 "FStar.Extraction.ML.Syntax.fst"
let is_MLC_Byte = (fun _discr_ -> (match (_discr_) with
| MLC_Byte (_) -> begin
true
end
| _ -> begin
false
end))

# 54 "FStar.Extraction.ML.Syntax.fst"
let is_MLC_Int32 = (fun _discr_ -> (match (_discr_) with
| MLC_Int32 (_) -> begin
true
end
| _ -> begin
false
end))

# 55 "FStar.Extraction.ML.Syntax.fst"
let is_MLC_Int64 = (fun _discr_ -> (match (_discr_) with
| MLC_Int64 (_) -> begin
true
end
| _ -> begin
false
end))

# 56 "FStar.Extraction.ML.Syntax.fst"
let is_MLC_Int = (fun _discr_ -> (match (_discr_) with
| MLC_Int (_) -> begin
true
end
| _ -> begin
false
end))

# 57 "FStar.Extraction.ML.Syntax.fst"
let is_MLC_Float = (fun _discr_ -> (match (_discr_) with
| MLC_Float (_) -> begin
true
end
| _ -> begin
false
end))

# 58 "FStar.Extraction.ML.Syntax.fst"
let is_MLC_Char = (fun _discr_ -> (match (_discr_) with
| MLC_Char (_) -> begin
true
end
| _ -> begin
false
end))

# 59 "FStar.Extraction.ML.Syntax.fst"
let is_MLC_String = (fun _discr_ -> (match (_discr_) with
| MLC_String (_) -> begin
true
end
| _ -> begin
false
end))

# 60 "FStar.Extraction.ML.Syntax.fst"
let is_MLC_Bytes = (fun _discr_ -> (match (_discr_) with
| MLC_Bytes (_) -> begin
true
end
| _ -> begin
false
end))

# 52 "FStar.Extraction.ML.Syntax.fst"
let ___MLC_Bool____0 : mlconstant  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MLC_Bool (_57_26) -> begin
_57_26
end))

# 53 "FStar.Extraction.ML.Syntax.fst"
let ___MLC_Byte____0 : mlconstant  ->  Prims.byte = (fun projectee -> (match (projectee) with
| MLC_Byte (_57_29) -> begin
_57_29
end))

# 54 "FStar.Extraction.ML.Syntax.fst"
let ___MLC_Int32____0 : mlconstant  ->  Prims.int32 = (fun projectee -> (match (projectee) with
| MLC_Int32 (_57_32) -> begin
_57_32
end))

# 55 "FStar.Extraction.ML.Syntax.fst"
let ___MLC_Int64____0 : mlconstant  ->  Prims.int64 = (fun projectee -> (match (projectee) with
| MLC_Int64 (_57_35) -> begin
_57_35
end))

# 56 "FStar.Extraction.ML.Syntax.fst"
let ___MLC_Int____0 : mlconstant  ->  Prims.string = (fun projectee -> (match (projectee) with
| MLC_Int (_57_38) -> begin
_57_38
end))

# 57 "FStar.Extraction.ML.Syntax.fst"
let ___MLC_Float____0 : mlconstant  ->  Prims.float = (fun projectee -> (match (projectee) with
| MLC_Float (_57_41) -> begin
_57_41
end))

# 58 "FStar.Extraction.ML.Syntax.fst"
let ___MLC_Char____0 : mlconstant  ->  Prims.char = (fun projectee -> (match (projectee) with
| MLC_Char (_57_44) -> begin
_57_44
end))

# 59 "FStar.Extraction.ML.Syntax.fst"
let ___MLC_String____0 : mlconstant  ->  Prims.string = (fun projectee -> (match (projectee) with
| MLC_String (_57_47) -> begin
_57_47
end))

# 60 "FStar.Extraction.ML.Syntax.fst"
let ___MLC_Bytes____0 : mlconstant  ->  Prims.byte Prims.array = (fun projectee -> (match (projectee) with
| MLC_Bytes (_57_50) -> begin
_57_50
end))

# 62 "FStar.Extraction.ML.Syntax.fst"
type mlpattern =
| MLP_Wild
| MLP_Const of mlconstant
| MLP_Var of mlident
| MLP_CTor of (mlpath * mlpattern Prims.list)
| MLP_Branch of mlpattern Prims.list
| MLP_Record of (mlsymbol Prims.list * (mlsymbol * mlpattern) Prims.list)
| MLP_Tuple of mlpattern Prims.list

# 63 "FStar.Extraction.ML.Syntax.fst"
let is_MLP_Wild = (fun _discr_ -> (match (_discr_) with
| MLP_Wild (_) -> begin
true
end
| _ -> begin
false
end))

# 64 "FStar.Extraction.ML.Syntax.fst"
let is_MLP_Const = (fun _discr_ -> (match (_discr_) with
| MLP_Const (_) -> begin
true
end
| _ -> begin
false
end))

# 65 "FStar.Extraction.ML.Syntax.fst"
let is_MLP_Var = (fun _discr_ -> (match (_discr_) with
| MLP_Var (_) -> begin
true
end
| _ -> begin
false
end))

# 66 "FStar.Extraction.ML.Syntax.fst"
let is_MLP_CTor = (fun _discr_ -> (match (_discr_) with
| MLP_CTor (_) -> begin
true
end
| _ -> begin
false
end))

# 67 "FStar.Extraction.ML.Syntax.fst"
let is_MLP_Branch = (fun _discr_ -> (match (_discr_) with
| MLP_Branch (_) -> begin
true
end
| _ -> begin
false
end))

# 69 "FStar.Extraction.ML.Syntax.fst"
let is_MLP_Record = (fun _discr_ -> (match (_discr_) with
| MLP_Record (_) -> begin
true
end
| _ -> begin
false
end))

# 70 "FStar.Extraction.ML.Syntax.fst"
let is_MLP_Tuple = (fun _discr_ -> (match (_discr_) with
| MLP_Tuple (_) -> begin
true
end
| _ -> begin
false
end))

# 64 "FStar.Extraction.ML.Syntax.fst"
let ___MLP_Const____0 : mlpattern  ->  mlconstant = (fun projectee -> (match (projectee) with
| MLP_Const (_57_53) -> begin
_57_53
end))

# 65 "FStar.Extraction.ML.Syntax.fst"
let ___MLP_Var____0 : mlpattern  ->  mlident = (fun projectee -> (match (projectee) with
| MLP_Var (_57_56) -> begin
_57_56
end))

# 66 "FStar.Extraction.ML.Syntax.fst"
let ___MLP_CTor____0 : mlpattern  ->  (mlpath * mlpattern Prims.list) = (fun projectee -> (match (projectee) with
| MLP_CTor (_57_59) -> begin
_57_59
end))

# 67 "FStar.Extraction.ML.Syntax.fst"
let ___MLP_Branch____0 : mlpattern  ->  mlpattern Prims.list = (fun projectee -> (match (projectee) with
| MLP_Branch (_57_62) -> begin
_57_62
end))

# 69 "FStar.Extraction.ML.Syntax.fst"
let ___MLP_Record____0 : mlpattern  ->  (mlsymbol Prims.list * (mlsymbol * mlpattern) Prims.list) = (fun projectee -> (match (projectee) with
| MLP_Record (_57_65) -> begin
_57_65
end))

# 70 "FStar.Extraction.ML.Syntax.fst"
let ___MLP_Tuple____0 : mlpattern  ->  mlpattern Prims.list = (fun projectee -> (match (projectee) with
| MLP_Tuple (_57_68) -> begin
_57_68
end))

# 72 "FStar.Extraction.ML.Syntax.fst"
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
{expr : mlexpr'; ty : mlty; loc : mlloc} 
 and mllb =
{mllb_name : mlident; mllb_tysc : mltyscheme Prims.option; mllb_add_unit : Prims.bool; mllb_def : mlexpr} 
 and mlbranch =
(mlpattern * mlexpr Prims.option * mlexpr) 
 and mlletbinding =
(Prims.bool * mllb Prims.list)

# 73 "FStar.Extraction.ML.Syntax.fst"
let is_MLE_Const = (fun _discr_ -> (match (_discr_) with
| MLE_Const (_) -> begin
true
end
| _ -> begin
false
end))

# 74 "FStar.Extraction.ML.Syntax.fst"
let is_MLE_Var = (fun _discr_ -> (match (_discr_) with
| MLE_Var (_) -> begin
true
end
| _ -> begin
false
end))

# 75 "FStar.Extraction.ML.Syntax.fst"
let is_MLE_Name = (fun _discr_ -> (match (_discr_) with
| MLE_Name (_) -> begin
true
end
| _ -> begin
false
end))

# 76 "FStar.Extraction.ML.Syntax.fst"
let is_MLE_Let = (fun _discr_ -> (match (_discr_) with
| MLE_Let (_) -> begin
true
end
| _ -> begin
false
end))

# 77 "FStar.Extraction.ML.Syntax.fst"
let is_MLE_App = (fun _discr_ -> (match (_discr_) with
| MLE_App (_) -> begin
true
end
| _ -> begin
false
end))

# 78 "FStar.Extraction.ML.Syntax.fst"
let is_MLE_Fun = (fun _discr_ -> (match (_discr_) with
| MLE_Fun (_) -> begin
true
end
| _ -> begin
false
end))

# 79 "FStar.Extraction.ML.Syntax.fst"
let is_MLE_Match = (fun _discr_ -> (match (_discr_) with
| MLE_Match (_) -> begin
true
end
| _ -> begin
false
end))

# 80 "FStar.Extraction.ML.Syntax.fst"
let is_MLE_Coerce = (fun _discr_ -> (match (_discr_) with
| MLE_Coerce (_) -> begin
true
end
| _ -> begin
false
end))

# 82 "FStar.Extraction.ML.Syntax.fst"
let is_MLE_CTor = (fun _discr_ -> (match (_discr_) with
| MLE_CTor (_) -> begin
true
end
| _ -> begin
false
end))

# 83 "FStar.Extraction.ML.Syntax.fst"
let is_MLE_Seq = (fun _discr_ -> (match (_discr_) with
| MLE_Seq (_) -> begin
true
end
| _ -> begin
false
end))

# 84 "FStar.Extraction.ML.Syntax.fst"
let is_MLE_Tuple = (fun _discr_ -> (match (_discr_) with
| MLE_Tuple (_) -> begin
true
end
| _ -> begin
false
end))

# 85 "FStar.Extraction.ML.Syntax.fst"
let is_MLE_Record = (fun _discr_ -> (match (_discr_) with
| MLE_Record (_) -> begin
true
end
| _ -> begin
false
end))

# 86 "FStar.Extraction.ML.Syntax.fst"
let is_MLE_Proj = (fun _discr_ -> (match (_discr_) with
| MLE_Proj (_) -> begin
true
end
| _ -> begin
false
end))

# 87 "FStar.Extraction.ML.Syntax.fst"
let is_MLE_If = (fun _discr_ -> (match (_discr_) with
| MLE_If (_) -> begin
true
end
| _ -> begin
false
end))

# 88 "FStar.Extraction.ML.Syntax.fst"
let is_MLE_Raise = (fun _discr_ -> (match (_discr_) with
| MLE_Raise (_) -> begin
true
end
| _ -> begin
false
end))

# 89 "FStar.Extraction.ML.Syntax.fst"
let is_MLE_Try = (fun _discr_ -> (match (_discr_) with
| MLE_Try (_) -> begin
true
end
| _ -> begin
false
end))

# 91 "FStar.Extraction.ML.Syntax.fst"
let is_Mkmlexpr : mlexpr  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkmlexpr"))))

# 99 "FStar.Extraction.ML.Syntax.fst"
let is_Mkmllb : mllb  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkmllb"))))

# 73 "FStar.Extraction.ML.Syntax.fst"
let ___MLE_Const____0 : mlexpr'  ->  mlconstant = (fun projectee -> (match (projectee) with
| MLE_Const (_57_78) -> begin
_57_78
end))

# 74 "FStar.Extraction.ML.Syntax.fst"
let ___MLE_Var____0 : mlexpr'  ->  mlident = (fun projectee -> (match (projectee) with
| MLE_Var (_57_81) -> begin
_57_81
end))

# 75 "FStar.Extraction.ML.Syntax.fst"
let ___MLE_Name____0 : mlexpr'  ->  mlpath = (fun projectee -> (match (projectee) with
| MLE_Name (_57_84) -> begin
_57_84
end))

# 76 "FStar.Extraction.ML.Syntax.fst"
let ___MLE_Let____0 : mlexpr'  ->  (mlletbinding * mlexpr) = (fun projectee -> (match (projectee) with
| MLE_Let (_57_87) -> begin
_57_87
end))

# 77 "FStar.Extraction.ML.Syntax.fst"
let ___MLE_App____0 : mlexpr'  ->  (mlexpr * mlexpr Prims.list) = (fun projectee -> (match (projectee) with
| MLE_App (_57_90) -> begin
_57_90
end))

# 78 "FStar.Extraction.ML.Syntax.fst"
let ___MLE_Fun____0 : mlexpr'  ->  ((mlident * mlty) Prims.list * mlexpr) = (fun projectee -> (match (projectee) with
| MLE_Fun (_57_93) -> begin
_57_93
end))

# 79 "FStar.Extraction.ML.Syntax.fst"
let ___MLE_Match____0 : mlexpr'  ->  (mlexpr * mlbranch Prims.list) = (fun projectee -> (match (projectee) with
| MLE_Match (_57_96) -> begin
_57_96
end))

# 80 "FStar.Extraction.ML.Syntax.fst"
let ___MLE_Coerce____0 : mlexpr'  ->  (mlexpr * mlty * mlty) = (fun projectee -> (match (projectee) with
| MLE_Coerce (_57_99) -> begin
_57_99
end))

# 82 "FStar.Extraction.ML.Syntax.fst"
let ___MLE_CTor____0 : mlexpr'  ->  (mlpath * mlexpr Prims.list) = (fun projectee -> (match (projectee) with
| MLE_CTor (_57_102) -> begin
_57_102
end))

# 83 "FStar.Extraction.ML.Syntax.fst"
let ___MLE_Seq____0 : mlexpr'  ->  mlexpr Prims.list = (fun projectee -> (match (projectee) with
| MLE_Seq (_57_105) -> begin
_57_105
end))

# 84 "FStar.Extraction.ML.Syntax.fst"
let ___MLE_Tuple____0 : mlexpr'  ->  mlexpr Prims.list = (fun projectee -> (match (projectee) with
| MLE_Tuple (_57_108) -> begin
_57_108
end))

# 85 "FStar.Extraction.ML.Syntax.fst"
let ___MLE_Record____0 : mlexpr'  ->  (mlsymbol Prims.list * (mlsymbol * mlexpr) Prims.list) = (fun projectee -> (match (projectee) with
| MLE_Record (_57_111) -> begin
_57_111
end))

# 86 "FStar.Extraction.ML.Syntax.fst"
let ___MLE_Proj____0 : mlexpr'  ->  (mlexpr * mlpath) = (fun projectee -> (match (projectee) with
| MLE_Proj (_57_114) -> begin
_57_114
end))

# 87 "FStar.Extraction.ML.Syntax.fst"
let ___MLE_If____0 : mlexpr'  ->  (mlexpr * mlexpr * mlexpr Prims.option) = (fun projectee -> (match (projectee) with
| MLE_If (_57_117) -> begin
_57_117
end))

# 88 "FStar.Extraction.ML.Syntax.fst"
let ___MLE_Raise____0 : mlexpr'  ->  (mlpath * mlexpr Prims.list) = (fun projectee -> (match (projectee) with
| MLE_Raise (_57_120) -> begin
_57_120
end))

# 89 "FStar.Extraction.ML.Syntax.fst"
let ___MLE_Try____0 : mlexpr'  ->  (mlexpr * mlbranch Prims.list) = (fun projectee -> (match (projectee) with
| MLE_Try (_57_123) -> begin
_57_123
end))

# 108 "FStar.Extraction.ML.Syntax.fst"
type mltybody =
| MLTD_Abbrev of mlty
| MLTD_Record of (mlsymbol * mlty) Prims.list
| MLTD_DType of (mlsymbol * mlty Prims.list) Prims.list

# 109 "FStar.Extraction.ML.Syntax.fst"
let is_MLTD_Abbrev = (fun _discr_ -> (match (_discr_) with
| MLTD_Abbrev (_) -> begin
true
end
| _ -> begin
false
end))

# 110 "FStar.Extraction.ML.Syntax.fst"
let is_MLTD_Record = (fun _discr_ -> (match (_discr_) with
| MLTD_Record (_) -> begin
true
end
| _ -> begin
false
end))

# 111 "FStar.Extraction.ML.Syntax.fst"
let is_MLTD_DType = (fun _discr_ -> (match (_discr_) with
| MLTD_DType (_) -> begin
true
end
| _ -> begin
false
end))

# 109 "FStar.Extraction.ML.Syntax.fst"
let ___MLTD_Abbrev____0 : mltybody  ->  mlty = (fun projectee -> (match (projectee) with
| MLTD_Abbrev (_57_128) -> begin
_57_128
end))

# 110 "FStar.Extraction.ML.Syntax.fst"
let ___MLTD_Record____0 : mltybody  ->  (mlsymbol * mlty) Prims.list = (fun projectee -> (match (projectee) with
| MLTD_Record (_57_131) -> begin
_57_131
end))

# 111 "FStar.Extraction.ML.Syntax.fst"
let ___MLTD_DType____0 : mltybody  ->  (mlsymbol * mlty Prims.list) Prims.list = (fun projectee -> (match (projectee) with
| MLTD_DType (_57_134) -> begin
_57_134
end))

# 116 "FStar.Extraction.ML.Syntax.fst"
type mltydecl =
(mlsymbol * mlidents * mltybody Prims.option) Prims.list

# 118 "FStar.Extraction.ML.Syntax.fst"
type mlmodule1 =
| MLM_Ty of mltydecl
| MLM_Let of mlletbinding
| MLM_Exn of (mlsymbol * mlty Prims.list)
| MLM_Top of mlexpr
| MLM_Loc of mlloc

# 119 "FStar.Extraction.ML.Syntax.fst"
let is_MLM_Ty = (fun _discr_ -> (match (_discr_) with
| MLM_Ty (_) -> begin
true
end
| _ -> begin
false
end))

# 120 "FStar.Extraction.ML.Syntax.fst"
let is_MLM_Let = (fun _discr_ -> (match (_discr_) with
| MLM_Let (_) -> begin
true
end
| _ -> begin
false
end))

# 121 "FStar.Extraction.ML.Syntax.fst"
let is_MLM_Exn = (fun _discr_ -> (match (_discr_) with
| MLM_Exn (_) -> begin
true
end
| _ -> begin
false
end))

# 122 "FStar.Extraction.ML.Syntax.fst"
let is_MLM_Top = (fun _discr_ -> (match (_discr_) with
| MLM_Top (_) -> begin
true
end
| _ -> begin
false
end))

# 123 "FStar.Extraction.ML.Syntax.fst"
let is_MLM_Loc = (fun _discr_ -> (match (_discr_) with
| MLM_Loc (_) -> begin
true
end
| _ -> begin
false
end))

# 119 "FStar.Extraction.ML.Syntax.fst"
let ___MLM_Ty____0 : mlmodule1  ->  mltydecl = (fun projectee -> (match (projectee) with
| MLM_Ty (_57_137) -> begin
_57_137
end))

# 120 "FStar.Extraction.ML.Syntax.fst"
let ___MLM_Let____0 : mlmodule1  ->  mlletbinding = (fun projectee -> (match (projectee) with
| MLM_Let (_57_140) -> begin
_57_140
end))

# 121 "FStar.Extraction.ML.Syntax.fst"
let ___MLM_Exn____0 : mlmodule1  ->  (mlsymbol * mlty Prims.list) = (fun projectee -> (match (projectee) with
| MLM_Exn (_57_143) -> begin
_57_143
end))

# 122 "FStar.Extraction.ML.Syntax.fst"
let ___MLM_Top____0 : mlmodule1  ->  mlexpr = (fun projectee -> (match (projectee) with
| MLM_Top (_57_146) -> begin
_57_146
end))

# 123 "FStar.Extraction.ML.Syntax.fst"
let ___MLM_Loc____0 : mlmodule1  ->  mlloc = (fun projectee -> (match (projectee) with
| MLM_Loc (_57_149) -> begin
_57_149
end))

# 125 "FStar.Extraction.ML.Syntax.fst"
type mlmodule =
mlmodule1 Prims.list

# 127 "FStar.Extraction.ML.Syntax.fst"
type mlsig1 =
| MLS_Mod of (mlsymbol * mlsig)
| MLS_Ty of mltydecl
| MLS_Val of (mlsymbol * mltyscheme)
| MLS_Exn of (mlsymbol * mlty Prims.list) 
 and mlsig =
mlsig1 Prims.list

# 128 "FStar.Extraction.ML.Syntax.fst"
let is_MLS_Mod = (fun _discr_ -> (match (_discr_) with
| MLS_Mod (_) -> begin
true
end
| _ -> begin
false
end))

# 129 "FStar.Extraction.ML.Syntax.fst"
let is_MLS_Ty = (fun _discr_ -> (match (_discr_) with
| MLS_Ty (_) -> begin
true
end
| _ -> begin
false
end))

# 132 "FStar.Extraction.ML.Syntax.fst"
let is_MLS_Val = (fun _discr_ -> (match (_discr_) with
| MLS_Val (_) -> begin
true
end
| _ -> begin
false
end))

# 133 "FStar.Extraction.ML.Syntax.fst"
let is_MLS_Exn = (fun _discr_ -> (match (_discr_) with
| MLS_Exn (_) -> begin
true
end
| _ -> begin
false
end))

# 128 "FStar.Extraction.ML.Syntax.fst"
let ___MLS_Mod____0 : mlsig1  ->  (mlsymbol * mlsig) = (fun projectee -> (match (projectee) with
| MLS_Mod (_57_152) -> begin
_57_152
end))

# 129 "FStar.Extraction.ML.Syntax.fst"
let ___MLS_Ty____0 : mlsig1  ->  mltydecl = (fun projectee -> (match (projectee) with
| MLS_Ty (_57_155) -> begin
_57_155
end))

# 132 "FStar.Extraction.ML.Syntax.fst"
let ___MLS_Val____0 : mlsig1  ->  (mlsymbol * mltyscheme) = (fun projectee -> (match (projectee) with
| MLS_Val (_57_158) -> begin
_57_158
end))

# 133 "FStar.Extraction.ML.Syntax.fst"
let ___MLS_Exn____0 : mlsig1  ->  (mlsymbol * mlty Prims.list) = (fun projectee -> (match (projectee) with
| MLS_Exn (_57_161) -> begin
_57_161
end))

# 137 "FStar.Extraction.ML.Syntax.fst"
let with_ty_loc : mlty  ->  mlexpr'  ->  mlloc  ->  mlexpr = (fun t e l -> {expr = e; ty = t; loc = l})

# 138 "FStar.Extraction.ML.Syntax.fst"
let with_ty : mlty  ->  mlexpr'  ->  mlexpr = (fun t e -> (with_ty_loc t e dummy_loc))

# 141 "FStar.Extraction.ML.Syntax.fst"
type mllib =
| MLLib of (mlsymbol * (mlsig * mlmodule) Prims.option * mllib) Prims.list

# 142 "FStar.Extraction.ML.Syntax.fst"
let is_MLLib = (fun _discr_ -> (match (_discr_) with
| MLLib (_) -> begin
true
end
| _ -> begin
false
end))

# 142 "FStar.Extraction.ML.Syntax.fst"
let ___MLLib____0 : mllib  ->  (mlsymbol * (mlsig * mlmodule) Prims.option * mllib) Prims.list = (fun projectee -> (match (projectee) with
| MLLib (_57_168) -> begin
_57_168
end))

# 146 "FStar.Extraction.ML.Syntax.fst"
let ml_unit_ty : mlty = MLTY_Named (([], (("Prims")::[], "unit")))

# 147 "FStar.Extraction.ML.Syntax.fst"
let ml_bool_ty : mlty = MLTY_Named (([], (("Prims")::[], "bool")))

# 148 "FStar.Extraction.ML.Syntax.fst"
let ml_int_ty : mlty = MLTY_Named (([], (("Prims")::[], "int")))

# 149 "FStar.Extraction.ML.Syntax.fst"
let ml_string_ty : mlty = MLTY_Named (([], (("Prims")::[], "string")))

# 150 "FStar.Extraction.ML.Syntax.fst"
let ml_unit : mlexpr = (with_ty ml_unit_ty (MLE_Const (MLC_Unit)))

# 151 "FStar.Extraction.ML.Syntax.fst"
let mlp_lalloc : (Prims.string Prims.list * Prims.string) = (("SST")::[], "lalloc")

# 152 "FStar.Extraction.ML.Syntax.fst"
let apply_obj_repr : mlexpr  ->  mlty  ->  mlexpr = (fun x t -> (
# 153 "FStar.Extraction.ML.Syntax.fst"
let obj_repr = (with_ty (MLTY_Fun ((t, E_PURE, MLTY_Top))) (MLE_Name ((("Obj")::[], "repr"))))
in (with_ty_loc MLTY_Top (MLE_App ((obj_repr, (x)::[]))) x.loc)))




