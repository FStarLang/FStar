
open Prims

type mlsymbol =
Prims.string


type mlident =
(mlsymbol * Prims.int)


type mlpath =
(mlsymbol Prims.list * mlsymbol)


let idsym : mlident  ->  mlsymbol = (fun _69_4 -> (match (_69_4) with
| (s, _69_3) -> begin
s
end))


let string_of_mlpath : mlpath  ->  mlsymbol = (fun _69_7 -> (match (_69_7) with
| (p, s) -> begin
(FStar_String.concat "." (FStar_List.append p ((s)::[])))
end))


type gensym_t =
{gensym : Prims.unit  ->  mlident; reset : Prims.unit  ->  Prims.unit}


let is_Mkgensym_t : gensym_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkgensym_t"))))


let gs : gensym_t = (

let ctr = (FStar_Util.mk_ref 0)
in (

let n_resets = (FStar_Util.mk_ref 0)
in {gensym = (fun _69_13 -> (match (()) with
| () -> begin
(let _158_31 = (let _158_30 = (let _158_27 = (let _158_26 = (let _158_25 = (FStar_ST.read n_resets)
in (FStar_Util.string_of_int _158_25))
in (Prims.strcat "_" _158_26))
in (Prims.strcat _158_27 "_"))
in (let _158_29 = (let _158_28 = (

let _69_14 = (FStar_Util.incr ctr)
in (FStar_ST.read ctr))
in (FStar_Util.string_of_int _158_28))
in (Prims.strcat _158_30 _158_29)))
in (_158_31, 0))
end)); reset = (fun _69_16 -> (match (()) with
| () -> begin
(

let _69_17 = (FStar_ST.op_Colon_Equals ctr 0)
in (FStar_Util.incr n_resets))
end))}))


let gensym : Prims.unit  ->  mlident = (fun _69_19 -> (match (()) with
| () -> begin
(gs.gensym ())
end))


let reset_gensym : Prims.unit  ->  Prims.unit = (fun _69_20 -> (match (()) with
| () -> begin
(gs.reset ())
end))


let rec gensyms : Prims.int  ->  mlident Prims.list = (fun x -> (match (x) with
| 0 -> begin
[]
end
| n -> begin
(let _158_40 = (gensym ())
in (let _158_39 = (gensyms (n - 1))
in (_158_40)::_158_39))
end))


let mlpath_of_lident : FStar_Ident.lident  ->  (Prims.string Prims.list * Prims.string) = (fun x -> (let _158_44 = (FStar_List.map (fun x -> x.FStar_Ident.idText) x.FStar_Ident.ns)
in (_158_44, x.FStar_Ident.ident.FStar_Ident.idText)))


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
| E_PURE (_) -> begin
true
end
| _ -> begin
false
end))


let is_E_GHOST = (fun _discr_ -> (match (_discr_) with
| E_GHOST (_) -> begin
true
end
| _ -> begin
false
end))


let is_E_IMPURE = (fun _discr_ -> (match (_discr_) with
| E_IMPURE (_) -> begin
true
end
| _ -> begin
false
end))


type mlloc =
(Prims.int * Prims.string)


let dummy_loc : (Prims.int * Prims.string) = (0, "")


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
| MLTY_Top (_) -> begin
true
end
| _ -> begin
false
end))


let ___MLTY_Var____0 = (fun projectee -> (match (projectee) with
| MLTY_Var (_69_30) -> begin
_69_30
end))


let ___MLTY_Fun____0 = (fun projectee -> (match (projectee) with
| MLTY_Fun (_69_33) -> begin
_69_33
end))


let ___MLTY_Named____0 = (fun projectee -> (match (projectee) with
| MLTY_Named (_69_36) -> begin
_69_36
end))


let ___MLTY_Tuple____0 = (fun projectee -> (match (projectee) with
| MLTY_Tuple (_69_39) -> begin
_69_39
end))


type mltyscheme =
(mlidents * mlty)


type mlconstant =
| MLC_Unit
| MLC_Bool of Prims.bool
| MLC_Int of (Prims.string * (FStar_Const.signedness * FStar_Const.width) Prims.option)
| MLC_Float of FStar_BaseTypes.float
| MLC_Char of FStar_BaseTypes.char
| MLC_String of Prims.string
| MLC_Bytes of FStar_BaseTypes.byte Prims.array


let is_MLC_Unit = (fun _discr_ -> (match (_discr_) with
| MLC_Unit (_) -> begin
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
| MLC_Bool (_69_42) -> begin
_69_42
end))


let ___MLC_Int____0 = (fun projectee -> (match (projectee) with
| MLC_Int (_69_45) -> begin
_69_45
end))


let ___MLC_Float____0 = (fun projectee -> (match (projectee) with
| MLC_Float (_69_48) -> begin
_69_48
end))


let ___MLC_Char____0 = (fun projectee -> (match (projectee) with
| MLC_Char (_69_51) -> begin
_69_51
end))


let ___MLC_String____0 = (fun projectee -> (match (projectee) with
| MLC_String (_69_54) -> begin
_69_54
end))


let ___MLC_Bytes____0 = (fun projectee -> (match (projectee) with
| MLC_Bytes (_69_57) -> begin
_69_57
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
| MLP_Wild (_) -> begin
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
| MLP_Const (_69_60) -> begin
_69_60
end))


let ___MLP_Var____0 = (fun projectee -> (match (projectee) with
| MLP_Var (_69_63) -> begin
_69_63
end))


let ___MLP_CTor____0 = (fun projectee -> (match (projectee) with
| MLP_CTor (_69_66) -> begin
_69_66
end))


let ___MLP_Branch____0 = (fun projectee -> (match (projectee) with
| MLP_Branch (_69_69) -> begin
_69_69
end))


let ___MLP_Record____0 = (fun projectee -> (match (projectee) with
| MLP_Record (_69_72) -> begin
_69_72
end))


let ___MLP_Tuple____0 = (fun projectee -> (match (projectee) with
| MLP_Tuple (_69_75) -> begin
_69_75
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
{expr : mlexpr'; mlty : mlty; loc : mlloc} 
 and mllb =
{mllb_name : mlident; mllb_tysc : mltyscheme Prims.option; mllb_add_unit : Prims.bool; mllb_def : mlexpr; print_typ : Prims.bool} 
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


let is_Mkmlexpr : mlexpr  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkmlexpr"))))


let is_Mkmllb : mllb  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkmllb"))))


let ___MLE_Const____0 = (fun projectee -> (match (projectee) with
| MLE_Const (_69_86) -> begin
_69_86
end))


let ___MLE_Var____0 = (fun projectee -> (match (projectee) with
| MLE_Var (_69_89) -> begin
_69_89
end))


let ___MLE_Name____0 = (fun projectee -> (match (projectee) with
| MLE_Name (_69_92) -> begin
_69_92
end))


let ___MLE_Let____0 = (fun projectee -> (match (projectee) with
| MLE_Let (_69_95) -> begin
_69_95
end))


let ___MLE_App____0 = (fun projectee -> (match (projectee) with
| MLE_App (_69_98) -> begin
_69_98
end))


let ___MLE_Fun____0 = (fun projectee -> (match (projectee) with
| MLE_Fun (_69_101) -> begin
_69_101
end))


let ___MLE_Match____0 = (fun projectee -> (match (projectee) with
| MLE_Match (_69_104) -> begin
_69_104
end))


let ___MLE_Coerce____0 = (fun projectee -> (match (projectee) with
| MLE_Coerce (_69_107) -> begin
_69_107
end))


let ___MLE_CTor____0 = (fun projectee -> (match (projectee) with
| MLE_CTor (_69_110) -> begin
_69_110
end))


let ___MLE_Seq____0 = (fun projectee -> (match (projectee) with
| MLE_Seq (_69_113) -> begin
_69_113
end))


let ___MLE_Tuple____0 = (fun projectee -> (match (projectee) with
| MLE_Tuple (_69_116) -> begin
_69_116
end))


let ___MLE_Record____0 = (fun projectee -> (match (projectee) with
| MLE_Record (_69_119) -> begin
_69_119
end))


let ___MLE_Proj____0 = (fun projectee -> (match (projectee) with
| MLE_Proj (_69_122) -> begin
_69_122
end))


let ___MLE_If____0 = (fun projectee -> (match (projectee) with
| MLE_If (_69_125) -> begin
_69_125
end))


let ___MLE_Raise____0 = (fun projectee -> (match (projectee) with
| MLE_Raise (_69_128) -> begin
_69_128
end))


let ___MLE_Try____0 = (fun projectee -> (match (projectee) with
| MLE_Try (_69_131) -> begin
_69_131
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
| MLTD_Abbrev (_69_136) -> begin
_69_136
end))


let ___MLTD_Record____0 = (fun projectee -> (match (projectee) with
| MLTD_Record (_69_139) -> begin
_69_139
end))


let ___MLTD_DType____0 = (fun projectee -> (match (projectee) with
| MLTD_DType (_69_142) -> begin
_69_142
end))


type mltydecl =
(mlsymbol * mlidents * mltybody Prims.option) Prims.list


type mlmodule1 =
| MLM_Ty of mltydecl
| MLM_Let of mlletbinding
| MLM_Exn of (mlsymbol * mlty Prims.list)
| MLM_Top of mlexpr
| MLM_Loc of mlloc


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


let is_MLM_Loc = (fun _discr_ -> (match (_discr_) with
| MLM_Loc (_) -> begin
true
end
| _ -> begin
false
end))


let ___MLM_Ty____0 = (fun projectee -> (match (projectee) with
| MLM_Ty (_69_145) -> begin
_69_145
end))


let ___MLM_Let____0 = (fun projectee -> (match (projectee) with
| MLM_Let (_69_148) -> begin
_69_148
end))


let ___MLM_Exn____0 = (fun projectee -> (match (projectee) with
| MLM_Exn (_69_151) -> begin
_69_151
end))


let ___MLM_Top____0 = (fun projectee -> (match (projectee) with
| MLM_Top (_69_154) -> begin
_69_154
end))


let ___MLM_Loc____0 = (fun projectee -> (match (projectee) with
| MLM_Loc (_69_157) -> begin
_69_157
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
| MLS_Mod (_69_160) -> begin
_69_160
end))


let ___MLS_Ty____0 = (fun projectee -> (match (projectee) with
| MLS_Ty (_69_163) -> begin
_69_163
end))


let ___MLS_Val____0 = (fun projectee -> (match (projectee) with
| MLS_Val (_69_166) -> begin
_69_166
end))


let ___MLS_Exn____0 = (fun projectee -> (match (projectee) with
| MLS_Exn (_69_169) -> begin
_69_169
end))


let with_ty_loc : mlty  ->  mlexpr'  ->  mlloc  ->  mlexpr = (fun t e l -> {expr = e; mlty = t; loc = l})


let with_ty : mlty  ->  mlexpr'  ->  mlexpr = (fun t e -> (with_ty_loc t e dummy_loc))


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
| MLLib (_69_176) -> begin
_69_176
end))


let ml_unit_ty : mlty = MLTY_Named (([], (("Prims")::[], "unit")))


let ml_bool_ty : mlty = MLTY_Named (([], (("Prims")::[], "bool")))


let ml_int_ty : mlty = MLTY_Named (([], (("Prims")::[], "int")))


let ml_string_ty : mlty = MLTY_Named (([], (("Prims")::[], "string")))


let ml_unit : mlexpr = (with_ty ml_unit_ty (MLE_Const (MLC_Unit)))


let mlp_lalloc : (Prims.string Prims.list * Prims.string) = (("SST")::[], "lalloc")


let apply_obj_repr : mlexpr  ->  mlty  ->  mlexpr = (fun x t -> (

let obj_repr = (with_ty (MLTY_Fun ((t, E_PURE, MLTY_Top))) (MLE_Name ((("Obj")::[], "repr"))))
in (with_ty_loc MLTY_Top (MLE_App ((obj_repr, (x)::[]))) x.loc)))


let bv_as_mlident : FStar_Syntax_Syntax.bv  ->  (Prims.string * Prims.int) = (fun x -> if ((FStar_Util.starts_with x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText FStar_Ident.reserved_prefix) || (FStar_Syntax_Syntax.is_null_bv x)) then begin
(let _158_717 = (let _158_716 = (FStar_Util.string_of_int x.FStar_Syntax_Syntax.index)
in (Prims.strcat (Prims.strcat x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "_") _158_716))
in (_158_717, 0))
end else begin
(x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText, 0)
end)




