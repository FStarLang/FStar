
open Prims
# 27 "FStar.Extraction.ML.Syntax.fst"
type mlsymbol =
Prims.string

# 28 "FStar.Extraction.ML.Syntax.fst"
type mlident =
(mlsymbol * Prims.int)

# 29 "FStar.Extraction.ML.Syntax.fst"
type mlpath =
(mlsymbol Prims.list * mlsymbol)

# 32 "FStar.Extraction.ML.Syntax.fst"
let idsym : mlident  ->  mlsymbol = (fun _64_4 -> (match (_64_4) with
| (s, _64_3) -> begin
s
end))

# 35 "FStar.Extraction.ML.Syntax.fst"
let string_of_mlpath : mlpath  ->  mlsymbol = (fun _64_7 -> (match (_64_7) with
| (p, s) -> begin
(FStar_String.concat "." (FStar_List.append p ((s)::[])))
end))

# 38 "FStar.Extraction.ML.Syntax.fst"
type gensym_t =
{gensym : Prims.unit  ->  mlident; reset : Prims.unit  ->  Prims.unit}

# 38 "FStar.Extraction.ML.Syntax.fst"
let is_Mkgensym_t : gensym_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkgensym_t"))))

# 43 "FStar.Extraction.ML.Syntax.fst"
let gs : gensym_t = (
# 44 "FStar.Extraction.ML.Syntax.fst"
let ctr = (FStar_Util.mk_ref 0)
in (
# 45 "FStar.Extraction.ML.Syntax.fst"
let n_resets = (FStar_Util.mk_ref 0)
in {gensym = (fun _64_13 -> (match (()) with
| () -> begin
(let _148_31 = (let _148_30 = (let _148_27 = (let _148_26 = (let _148_25 = (FStar_ST.read n_resets)
in (FStar_Util.string_of_int _148_25))
in (Prims.strcat "_" _148_26))
in (Prims.strcat _148_27 "_"))
in (let _148_29 = (let _148_28 = (
# 46 "FStar.Extraction.ML.Syntax.fst"
let _64_14 = (FStar_Util.incr ctr)
in (FStar_ST.read ctr))
in (FStar_Util.string_of_int _148_28))
in (Prims.strcat _148_30 _148_29)))
in (_148_31, 0))
end)); reset = (fun _64_16 -> (match (()) with
| () -> begin
(
# 47 "FStar.Extraction.ML.Syntax.fst"
let _64_17 = (FStar_ST.op_Colon_Equals ctr 0)
in (FStar_Util.incr n_resets))
end))}))

# 49 "FStar.Extraction.ML.Syntax.fst"
let gensym : Prims.unit  ->  mlident = (fun _64_19 -> (match (()) with
| () -> begin
(gs.gensym ())
end))

# 50 "FStar.Extraction.ML.Syntax.fst"
let reset_gensym : Prims.unit  ->  Prims.unit = (fun _64_20 -> (match (()) with
| () -> begin
(gs.reset ())
end))

# 51 "FStar.Extraction.ML.Syntax.fst"
let rec gensyms : Prims.int  ->  mlident Prims.list = (fun x -> (match (x) with
| 0 -> begin
[]
end
| n -> begin
(let _148_40 = (gensym ())
in (let _148_39 = (gensyms (n - 1))
in (_148_40)::_148_39))
end))

# 56 "FStar.Extraction.ML.Syntax.fst"
let mlpath_of_lident : FStar_Ident.lident  ->  (Prims.string Prims.list * Prims.string) = (fun x -> (let _148_44 = (FStar_List.map (fun x -> x.FStar_Ident.idText) x.FStar_Ident.ns)
in (_148_44, x.FStar_Ident.ident.FStar_Ident.idText)))

# 59 "FStar.Extraction.ML.Syntax.fst"
let as_mlident = (fun x -> (x.FStar_Absyn_Syntax.ppname.FStar_Ident.idText, 0))

# 62 "FStar.Extraction.ML.Syntax.fst"
type mlidents =
mlident Prims.list

# 63 "FStar.Extraction.ML.Syntax.fst"
type mlsymbols =
mlsymbol Prims.list

# 66 "FStar.Extraction.ML.Syntax.fst"
type e_tag =
| E_PURE
| E_GHOST
| E_IMPURE

# 67 "FStar.Extraction.ML.Syntax.fst"
let is_E_PURE = (fun _discr_ -> (match (_discr_) with
| E_PURE (_) -> begin
true
end
| _ -> begin
false
end))

# 68 "FStar.Extraction.ML.Syntax.fst"
let is_E_GHOST = (fun _discr_ -> (match (_discr_) with
| E_GHOST (_) -> begin
true
end
| _ -> begin
false
end))

# 69 "FStar.Extraction.ML.Syntax.fst"
let is_E_IMPURE = (fun _discr_ -> (match (_discr_) with
| E_IMPURE (_) -> begin
true
end
| _ -> begin
false
end))

# 72 "FStar.Extraction.ML.Syntax.fst"
type mlloc =
(Prims.int * Prims.string)

# 73 "FStar.Extraction.ML.Syntax.fst"
let dummy_loc : (Prims.int * Prims.string) = (0, "")

# 75 "FStar.Extraction.ML.Syntax.fst"
type mlty =
| MLTY_Var of mlident
| MLTY_Fun of (mlty * e_tag * mlty)
| MLTY_Named of (mlty Prims.list * mlpath)
| MLTY_Tuple of mlty Prims.list
| MLTY_Top

# 76 "FStar.Extraction.ML.Syntax.fst"
let is_MLTY_Var = (fun _discr_ -> (match (_discr_) with
| MLTY_Var (_) -> begin
true
end
| _ -> begin
false
end))

# 77 "FStar.Extraction.ML.Syntax.fst"
let is_MLTY_Fun = (fun _discr_ -> (match (_discr_) with
| MLTY_Fun (_) -> begin
true
end
| _ -> begin
false
end))

# 78 "FStar.Extraction.ML.Syntax.fst"
let is_MLTY_Named = (fun _discr_ -> (match (_discr_) with
| MLTY_Named (_) -> begin
true
end
| _ -> begin
false
end))

# 79 "FStar.Extraction.ML.Syntax.fst"
let is_MLTY_Tuple = (fun _discr_ -> (match (_discr_) with
| MLTY_Tuple (_) -> begin
true
end
| _ -> begin
false
end))

# 80 "FStar.Extraction.ML.Syntax.fst"
let is_MLTY_Top = (fun _discr_ -> (match (_discr_) with
| MLTY_Top (_) -> begin
true
end
| _ -> begin
false
end))

# 76 "FStar.Extraction.ML.Syntax.fst"
let ___MLTY_Var____0 = (fun projectee -> (match (projectee) with
| MLTY_Var (_64_30) -> begin
_64_30
end))

# 77 "FStar.Extraction.ML.Syntax.fst"
let ___MLTY_Fun____0 = (fun projectee -> (match (projectee) with
| MLTY_Fun (_64_33) -> begin
_64_33
end))

# 78 "FStar.Extraction.ML.Syntax.fst"
let ___MLTY_Named____0 = (fun projectee -> (match (projectee) with
| MLTY_Named (_64_36) -> begin
_64_36
end))

# 79 "FStar.Extraction.ML.Syntax.fst"
let ___MLTY_Tuple____0 = (fun projectee -> (match (projectee) with
| MLTY_Tuple (_64_39) -> begin
_64_39
end))

# 82 "FStar.Extraction.ML.Syntax.fst"
type mltyscheme =
(mlidents * mlty)

# 84 "FStar.Extraction.ML.Syntax.fst"
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

# 85 "FStar.Extraction.ML.Syntax.fst"
let is_MLC_Unit = (fun _discr_ -> (match (_discr_) with
| MLC_Unit (_) -> begin
true
end
| _ -> begin
false
end))

# 86 "FStar.Extraction.ML.Syntax.fst"
let is_MLC_Bool = (fun _discr_ -> (match (_discr_) with
| MLC_Bool (_) -> begin
true
end
| _ -> begin
false
end))

# 87 "FStar.Extraction.ML.Syntax.fst"
let is_MLC_Byte = (fun _discr_ -> (match (_discr_) with
| MLC_Byte (_) -> begin
true
end
| _ -> begin
false
end))

# 88 "FStar.Extraction.ML.Syntax.fst"
let is_MLC_Int32 = (fun _discr_ -> (match (_discr_) with
| MLC_Int32 (_) -> begin
true
end
| _ -> begin
false
end))

# 89 "FStar.Extraction.ML.Syntax.fst"
let is_MLC_Int64 = (fun _discr_ -> (match (_discr_) with
| MLC_Int64 (_) -> begin
true
end
| _ -> begin
false
end))

# 90 "FStar.Extraction.ML.Syntax.fst"
let is_MLC_Int = (fun _discr_ -> (match (_discr_) with
| MLC_Int (_) -> begin
true
end
| _ -> begin
false
end))

# 91 "FStar.Extraction.ML.Syntax.fst"
let is_MLC_Float = (fun _discr_ -> (match (_discr_) with
| MLC_Float (_) -> begin
true
end
| _ -> begin
false
end))

# 92 "FStar.Extraction.ML.Syntax.fst"
let is_MLC_Char = (fun _discr_ -> (match (_discr_) with
| MLC_Char (_) -> begin
true
end
| _ -> begin
false
end))

# 93 "FStar.Extraction.ML.Syntax.fst"
let is_MLC_String = (fun _discr_ -> (match (_discr_) with
| MLC_String (_) -> begin
true
end
| _ -> begin
false
end))

# 94 "FStar.Extraction.ML.Syntax.fst"
let is_MLC_Bytes = (fun _discr_ -> (match (_discr_) with
| MLC_Bytes (_) -> begin
true
end
| _ -> begin
false
end))

# 86 "FStar.Extraction.ML.Syntax.fst"
let ___MLC_Bool____0 = (fun projectee -> (match (projectee) with
| MLC_Bool (_64_42) -> begin
_64_42
end))

# 87 "FStar.Extraction.ML.Syntax.fst"
let ___MLC_Byte____0 = (fun projectee -> (match (projectee) with
| MLC_Byte (_64_45) -> begin
_64_45
end))

# 88 "FStar.Extraction.ML.Syntax.fst"
let ___MLC_Int32____0 = (fun projectee -> (match (projectee) with
| MLC_Int32 (_64_48) -> begin
_64_48
end))

# 89 "FStar.Extraction.ML.Syntax.fst"
let ___MLC_Int64____0 = (fun projectee -> (match (projectee) with
| MLC_Int64 (_64_51) -> begin
_64_51
end))

# 90 "FStar.Extraction.ML.Syntax.fst"
let ___MLC_Int____0 = (fun projectee -> (match (projectee) with
| MLC_Int (_64_54) -> begin
_64_54
end))

# 91 "FStar.Extraction.ML.Syntax.fst"
let ___MLC_Float____0 = (fun projectee -> (match (projectee) with
| MLC_Float (_64_57) -> begin
_64_57
end))

# 92 "FStar.Extraction.ML.Syntax.fst"
let ___MLC_Char____0 = (fun projectee -> (match (projectee) with
| MLC_Char (_64_60) -> begin
_64_60
end))

# 93 "FStar.Extraction.ML.Syntax.fst"
let ___MLC_String____0 = (fun projectee -> (match (projectee) with
| MLC_String (_64_63) -> begin
_64_63
end))

# 94 "FStar.Extraction.ML.Syntax.fst"
let ___MLC_Bytes____0 = (fun projectee -> (match (projectee) with
| MLC_Bytes (_64_66) -> begin
_64_66
end))

# 96 "FStar.Extraction.ML.Syntax.fst"
type mlpattern =
| MLP_Wild
| MLP_Const of mlconstant
| MLP_Var of mlident
| MLP_CTor of (mlpath * mlpattern Prims.list)
| MLP_Branch of mlpattern Prims.list
| MLP_Record of (mlsymbol Prims.list * (mlsymbol * mlpattern) Prims.list)
| MLP_Tuple of mlpattern Prims.list

# 97 "FStar.Extraction.ML.Syntax.fst"
let is_MLP_Wild = (fun _discr_ -> (match (_discr_) with
| MLP_Wild (_) -> begin
true
end
| _ -> begin
false
end))

# 98 "FStar.Extraction.ML.Syntax.fst"
let is_MLP_Const = (fun _discr_ -> (match (_discr_) with
| MLP_Const (_) -> begin
true
end
| _ -> begin
false
end))

# 99 "FStar.Extraction.ML.Syntax.fst"
let is_MLP_Var = (fun _discr_ -> (match (_discr_) with
| MLP_Var (_) -> begin
true
end
| _ -> begin
false
end))

# 100 "FStar.Extraction.ML.Syntax.fst"
let is_MLP_CTor = (fun _discr_ -> (match (_discr_) with
| MLP_CTor (_) -> begin
true
end
| _ -> begin
false
end))

# 101 "FStar.Extraction.ML.Syntax.fst"
let is_MLP_Branch = (fun _discr_ -> (match (_discr_) with
| MLP_Branch (_) -> begin
true
end
| _ -> begin
false
end))

# 103 "FStar.Extraction.ML.Syntax.fst"
let is_MLP_Record = (fun _discr_ -> (match (_discr_) with
| MLP_Record (_) -> begin
true
end
| _ -> begin
false
end))

# 104 "FStar.Extraction.ML.Syntax.fst"
let is_MLP_Tuple = (fun _discr_ -> (match (_discr_) with
| MLP_Tuple (_) -> begin
true
end
| _ -> begin
false
end))

# 98 "FStar.Extraction.ML.Syntax.fst"
let ___MLP_Const____0 = (fun projectee -> (match (projectee) with
| MLP_Const (_64_69) -> begin
_64_69
end))

# 99 "FStar.Extraction.ML.Syntax.fst"
let ___MLP_Var____0 = (fun projectee -> (match (projectee) with
| MLP_Var (_64_72) -> begin
_64_72
end))

# 100 "FStar.Extraction.ML.Syntax.fst"
let ___MLP_CTor____0 = (fun projectee -> (match (projectee) with
| MLP_CTor (_64_75) -> begin
_64_75
end))

# 101 "FStar.Extraction.ML.Syntax.fst"
let ___MLP_Branch____0 = (fun projectee -> (match (projectee) with
| MLP_Branch (_64_78) -> begin
_64_78
end))

# 103 "FStar.Extraction.ML.Syntax.fst"
let ___MLP_Record____0 = (fun projectee -> (match (projectee) with
| MLP_Record (_64_81) -> begin
_64_81
end))

# 104 "FStar.Extraction.ML.Syntax.fst"
let ___MLP_Tuple____0 = (fun projectee -> (match (projectee) with
| MLP_Tuple (_64_84) -> begin
_64_84
end))

# 106 "FStar.Extraction.ML.Syntax.fst"
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
{expr : mlexpr'; mlty : mlty; loc : mlloc} 
 and mllb =
{mllb_name : mlident; mllb_tysc : mltyscheme Prims.option; mllb_add_unit : Prims.bool; mllb_def : mlexpr; print_typ : Prims.bool} 
 and mlbranch =
(mlpattern * mlexpr Prims.option * mlexpr) 
 and mlletbinding =
(Prims.bool * mllb Prims.list)

# 107 "FStar.Extraction.ML.Syntax.fst"
let is_MLE_Const = (fun _discr_ -> (match (_discr_) with
| MLE_Const (_) -> begin
true
end
| _ -> begin
false
end))

# 108 "FStar.Extraction.ML.Syntax.fst"
let is_MLE_Var = (fun _discr_ -> (match (_discr_) with
| MLE_Var (_) -> begin
true
end
| _ -> begin
false
end))

# 109 "FStar.Extraction.ML.Syntax.fst"
let is_MLE_Name = (fun _discr_ -> (match (_discr_) with
| MLE_Name (_) -> begin
true
end
| _ -> begin
false
end))

# 110 "FStar.Extraction.ML.Syntax.fst"
let is_MLE_Let = (fun _discr_ -> (match (_discr_) with
| MLE_Let (_) -> begin
true
end
| _ -> begin
false
end))

# 111 "FStar.Extraction.ML.Syntax.fst"
let is_MLE_App = (fun _discr_ -> (match (_discr_) with
| MLE_App (_) -> begin
true
end
| _ -> begin
false
end))

# 112 "FStar.Extraction.ML.Syntax.fst"
let is_MLE_Fun = (fun _discr_ -> (match (_discr_) with
| MLE_Fun (_) -> begin
true
end
| _ -> begin
false
end))

# 113 "FStar.Extraction.ML.Syntax.fst"
let is_MLE_Match = (fun _discr_ -> (match (_discr_) with
| MLE_Match (_) -> begin
true
end
| _ -> begin
false
end))

# 114 "FStar.Extraction.ML.Syntax.fst"
let is_MLE_Coerce = (fun _discr_ -> (match (_discr_) with
| MLE_Coerce (_) -> begin
true
end
| _ -> begin
false
end))

# 116 "FStar.Extraction.ML.Syntax.fst"
let is_MLE_CTor = (fun _discr_ -> (match (_discr_) with
| MLE_CTor (_) -> begin
true
end
| _ -> begin
false
end))

# 117 "FStar.Extraction.ML.Syntax.fst"
let is_MLE_Seq = (fun _discr_ -> (match (_discr_) with
| MLE_Seq (_) -> begin
true
end
| _ -> begin
false
end))

# 118 "FStar.Extraction.ML.Syntax.fst"
let is_MLE_Tuple = (fun _discr_ -> (match (_discr_) with
| MLE_Tuple (_) -> begin
true
end
| _ -> begin
false
end))

# 119 "FStar.Extraction.ML.Syntax.fst"
let is_MLE_Record = (fun _discr_ -> (match (_discr_) with
| MLE_Record (_) -> begin
true
end
| _ -> begin
false
end))

# 120 "FStar.Extraction.ML.Syntax.fst"
let is_MLE_Proj = (fun _discr_ -> (match (_discr_) with
| MLE_Proj (_) -> begin
true
end
| _ -> begin
false
end))

# 121 "FStar.Extraction.ML.Syntax.fst"
let is_MLE_If = (fun _discr_ -> (match (_discr_) with
| MLE_If (_) -> begin
true
end
| _ -> begin
false
end))

# 122 "FStar.Extraction.ML.Syntax.fst"
let is_MLE_Raise = (fun _discr_ -> (match (_discr_) with
| MLE_Raise (_) -> begin
true
end
| _ -> begin
false
end))

# 123 "FStar.Extraction.ML.Syntax.fst"
let is_MLE_Try = (fun _discr_ -> (match (_discr_) with
| MLE_Try (_) -> begin
true
end
| _ -> begin
false
end))

# 125 "FStar.Extraction.ML.Syntax.fst"
let is_Mkmlexpr : mlexpr  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkmlexpr"))))

# 133 "FStar.Extraction.ML.Syntax.fst"
let is_Mkmllb : mllb  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkmllb"))))

# 107 "FStar.Extraction.ML.Syntax.fst"
let ___MLE_Const____0 = (fun projectee -> (match (projectee) with
| MLE_Const (_64_95) -> begin
_64_95
end))

# 108 "FStar.Extraction.ML.Syntax.fst"
let ___MLE_Var____0 = (fun projectee -> (match (projectee) with
| MLE_Var (_64_98) -> begin
_64_98
end))

# 109 "FStar.Extraction.ML.Syntax.fst"
let ___MLE_Name____0 = (fun projectee -> (match (projectee) with
| MLE_Name (_64_101) -> begin
_64_101
end))

# 110 "FStar.Extraction.ML.Syntax.fst"
let ___MLE_Let____0 = (fun projectee -> (match (projectee) with
| MLE_Let (_64_104) -> begin
_64_104
end))

# 111 "FStar.Extraction.ML.Syntax.fst"
let ___MLE_App____0 = (fun projectee -> (match (projectee) with
| MLE_App (_64_107) -> begin
_64_107
end))

# 112 "FStar.Extraction.ML.Syntax.fst"
let ___MLE_Fun____0 = (fun projectee -> (match (projectee) with
| MLE_Fun (_64_110) -> begin
_64_110
end))

# 113 "FStar.Extraction.ML.Syntax.fst"
let ___MLE_Match____0 = (fun projectee -> (match (projectee) with
| MLE_Match (_64_113) -> begin
_64_113
end))

# 114 "FStar.Extraction.ML.Syntax.fst"
let ___MLE_Coerce____0 = (fun projectee -> (match (projectee) with
| MLE_Coerce (_64_116) -> begin
_64_116
end))

# 116 "FStar.Extraction.ML.Syntax.fst"
let ___MLE_CTor____0 = (fun projectee -> (match (projectee) with
| MLE_CTor (_64_119) -> begin
_64_119
end))

# 117 "FStar.Extraction.ML.Syntax.fst"
let ___MLE_Seq____0 = (fun projectee -> (match (projectee) with
| MLE_Seq (_64_122) -> begin
_64_122
end))

# 118 "FStar.Extraction.ML.Syntax.fst"
let ___MLE_Tuple____0 = (fun projectee -> (match (projectee) with
| MLE_Tuple (_64_125) -> begin
_64_125
end))

# 119 "FStar.Extraction.ML.Syntax.fst"
let ___MLE_Record____0 = (fun projectee -> (match (projectee) with
| MLE_Record (_64_128) -> begin
_64_128
end))

# 120 "FStar.Extraction.ML.Syntax.fst"
let ___MLE_Proj____0 = (fun projectee -> (match (projectee) with
| MLE_Proj (_64_131) -> begin
_64_131
end))

# 121 "FStar.Extraction.ML.Syntax.fst"
let ___MLE_If____0 = (fun projectee -> (match (projectee) with
| MLE_If (_64_134) -> begin
_64_134
end))

# 122 "FStar.Extraction.ML.Syntax.fst"
let ___MLE_Raise____0 = (fun projectee -> (match (projectee) with
| MLE_Raise (_64_137) -> begin
_64_137
end))

# 123 "FStar.Extraction.ML.Syntax.fst"
let ___MLE_Try____0 = (fun projectee -> (match (projectee) with
| MLE_Try (_64_140) -> begin
_64_140
end))

# 143 "FStar.Extraction.ML.Syntax.fst"
type mltybody =
| MLTD_Abbrev of mlty
| MLTD_Record of (mlsymbol * mlty) Prims.list
| MLTD_DType of (mlsymbol * mlty Prims.list) Prims.list

# 144 "FStar.Extraction.ML.Syntax.fst"
let is_MLTD_Abbrev = (fun _discr_ -> (match (_discr_) with
| MLTD_Abbrev (_) -> begin
true
end
| _ -> begin
false
end))

# 145 "FStar.Extraction.ML.Syntax.fst"
let is_MLTD_Record = (fun _discr_ -> (match (_discr_) with
| MLTD_Record (_) -> begin
true
end
| _ -> begin
false
end))

# 146 "FStar.Extraction.ML.Syntax.fst"
let is_MLTD_DType = (fun _discr_ -> (match (_discr_) with
| MLTD_DType (_) -> begin
true
end
| _ -> begin
false
end))

# 144 "FStar.Extraction.ML.Syntax.fst"
let ___MLTD_Abbrev____0 = (fun projectee -> (match (projectee) with
| MLTD_Abbrev (_64_145) -> begin
_64_145
end))

# 145 "FStar.Extraction.ML.Syntax.fst"
let ___MLTD_Record____0 = (fun projectee -> (match (projectee) with
| MLTD_Record (_64_148) -> begin
_64_148
end))

# 146 "FStar.Extraction.ML.Syntax.fst"
let ___MLTD_DType____0 = (fun projectee -> (match (projectee) with
| MLTD_DType (_64_151) -> begin
_64_151
end))

# 151 "FStar.Extraction.ML.Syntax.fst"
type mltydecl =
(mlsymbol * mlidents * mltybody Prims.option) Prims.list

# 153 "FStar.Extraction.ML.Syntax.fst"
type mlmodule1 =
| MLM_Ty of mltydecl
| MLM_Let of mlletbinding
| MLM_Exn of (mlsymbol * mlty Prims.list)
| MLM_Top of mlexpr
| MLM_Loc of mlloc

# 154 "FStar.Extraction.ML.Syntax.fst"
let is_MLM_Ty = (fun _discr_ -> (match (_discr_) with
| MLM_Ty (_) -> begin
true
end
| _ -> begin
false
end))

# 155 "FStar.Extraction.ML.Syntax.fst"
let is_MLM_Let = (fun _discr_ -> (match (_discr_) with
| MLM_Let (_) -> begin
true
end
| _ -> begin
false
end))

# 156 "FStar.Extraction.ML.Syntax.fst"
let is_MLM_Exn = (fun _discr_ -> (match (_discr_) with
| MLM_Exn (_) -> begin
true
end
| _ -> begin
false
end))

# 157 "FStar.Extraction.ML.Syntax.fst"
let is_MLM_Top = (fun _discr_ -> (match (_discr_) with
| MLM_Top (_) -> begin
true
end
| _ -> begin
false
end))

# 158 "FStar.Extraction.ML.Syntax.fst"
let is_MLM_Loc = (fun _discr_ -> (match (_discr_) with
| MLM_Loc (_) -> begin
true
end
| _ -> begin
false
end))

# 154 "FStar.Extraction.ML.Syntax.fst"
let ___MLM_Ty____0 = (fun projectee -> (match (projectee) with
| MLM_Ty (_64_154) -> begin
_64_154
end))

# 155 "FStar.Extraction.ML.Syntax.fst"
let ___MLM_Let____0 = (fun projectee -> (match (projectee) with
| MLM_Let (_64_157) -> begin
_64_157
end))

# 156 "FStar.Extraction.ML.Syntax.fst"
let ___MLM_Exn____0 = (fun projectee -> (match (projectee) with
| MLM_Exn (_64_160) -> begin
_64_160
end))

# 157 "FStar.Extraction.ML.Syntax.fst"
let ___MLM_Top____0 = (fun projectee -> (match (projectee) with
| MLM_Top (_64_163) -> begin
_64_163
end))

# 158 "FStar.Extraction.ML.Syntax.fst"
let ___MLM_Loc____0 = (fun projectee -> (match (projectee) with
| MLM_Loc (_64_166) -> begin
_64_166
end))

# 160 "FStar.Extraction.ML.Syntax.fst"
type mlmodule =
mlmodule1 Prims.list

# 162 "FStar.Extraction.ML.Syntax.fst"
type mlsig1 =
| MLS_Mod of (mlsymbol * mlsig)
| MLS_Ty of mltydecl
| MLS_Val of (mlsymbol * mltyscheme)
| MLS_Exn of (mlsymbol * mlty Prims.list) 
 and mlsig =
mlsig1 Prims.list

# 163 "FStar.Extraction.ML.Syntax.fst"
let is_MLS_Mod = (fun _discr_ -> (match (_discr_) with
| MLS_Mod (_) -> begin
true
end
| _ -> begin
false
end))

# 164 "FStar.Extraction.ML.Syntax.fst"
let is_MLS_Ty = (fun _discr_ -> (match (_discr_) with
| MLS_Ty (_) -> begin
true
end
| _ -> begin
false
end))

# 167 "FStar.Extraction.ML.Syntax.fst"
let is_MLS_Val = (fun _discr_ -> (match (_discr_) with
| MLS_Val (_) -> begin
true
end
| _ -> begin
false
end))

# 168 "FStar.Extraction.ML.Syntax.fst"
let is_MLS_Exn = (fun _discr_ -> (match (_discr_) with
| MLS_Exn (_) -> begin
true
end
| _ -> begin
false
end))

# 163 "FStar.Extraction.ML.Syntax.fst"
let ___MLS_Mod____0 = (fun projectee -> (match (projectee) with
| MLS_Mod (_64_169) -> begin
_64_169
end))

# 164 "FStar.Extraction.ML.Syntax.fst"
let ___MLS_Ty____0 = (fun projectee -> (match (projectee) with
| MLS_Ty (_64_172) -> begin
_64_172
end))

# 167 "FStar.Extraction.ML.Syntax.fst"
let ___MLS_Val____0 = (fun projectee -> (match (projectee) with
| MLS_Val (_64_175) -> begin
_64_175
end))

# 168 "FStar.Extraction.ML.Syntax.fst"
let ___MLS_Exn____0 = (fun projectee -> (match (projectee) with
| MLS_Exn (_64_178) -> begin
_64_178
end))

# 172 "FStar.Extraction.ML.Syntax.fst"
let with_ty_loc : mlty  ->  mlexpr'  ->  mlloc  ->  mlexpr = (fun t e l -> {expr = e; mlty = t; loc = l})

# 173 "FStar.Extraction.ML.Syntax.fst"
let with_ty : mlty  ->  mlexpr'  ->  mlexpr = (fun t e -> (with_ty_loc t e dummy_loc))

# 176 "FStar.Extraction.ML.Syntax.fst"
type mllib =
| MLLib of (mlsymbol * (mlsig * mlmodule) Prims.option * mllib) Prims.list

# 177 "FStar.Extraction.ML.Syntax.fst"
let is_MLLib = (fun _discr_ -> (match (_discr_) with
| MLLib (_) -> begin
true
end
| _ -> begin
false
end))

# 177 "FStar.Extraction.ML.Syntax.fst"
let ___MLLib____0 = (fun projectee -> (match (projectee) with
| MLLib (_64_185) -> begin
_64_185
end))

# 181 "FStar.Extraction.ML.Syntax.fst"
let ml_unit_ty : mlty = MLTY_Named (([], (("Prims")::[], "unit")))

# 182 "FStar.Extraction.ML.Syntax.fst"
let ml_bool_ty : mlty = MLTY_Named (([], (("Prims")::[], "bool")))

# 183 "FStar.Extraction.ML.Syntax.fst"
let ml_int_ty : mlty = MLTY_Named (([], (("Prims")::[], "int")))

# 184 "FStar.Extraction.ML.Syntax.fst"
let ml_string_ty : mlty = MLTY_Named (([], (("Prims")::[], "string")))

# 185 "FStar.Extraction.ML.Syntax.fst"
let ml_unit : mlexpr = (with_ty ml_unit_ty (MLE_Const (MLC_Unit)))

# 186 "FStar.Extraction.ML.Syntax.fst"
let mlp_lalloc : (Prims.string Prims.list * Prims.string) = (("SST")::[], "lalloc")

# 187 "FStar.Extraction.ML.Syntax.fst"
let apply_obj_repr : mlexpr  ->  mlty  ->  mlexpr = (fun x t -> (
# 188 "FStar.Extraction.ML.Syntax.fst"
let obj_repr = (with_ty (MLTY_Fun ((t, E_PURE, MLTY_Top))) (MLE_Name ((("Obj")::[], "repr"))))
in (with_ty_loc MLTY_Top (MLE_App ((obj_repr, (x)::[]))) x.loc)))




