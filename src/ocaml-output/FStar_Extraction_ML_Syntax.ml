
open Prims

type mlsymbol =
Prims.string


type mlident =
(mlsymbol * Prims.int)


type mlpath =
(mlsymbol Prims.list * mlsymbol)


let ocamlkeywords : Prims.string Prims.list = ("and")::("as")::("assert")::("asr")::("begin")::("class")::("constraint")::("do")::("done")::("downto")::("else")::("end")::("exception")::("external")::("false")::("for")::("fun")::("function")::("functor")::("if")::("in")::("include")::("inherit")::("initializer")::("land")::("lazy")::("let")::("lor")::("lsl")::("lsr")::("lxor")::("match")::("method")::("mod")::("module")::("mutable")::("new")::("object")::("of")::("open")::("or")::("private")::("rec")::("sig")::("struct")::("then")::("to")::("true")::("try")::("type")::("val")::("virtual")::("when")::("while")::("with")::("nonrec")::[]


let is_reserved : Prims.string  ->  Prims.bool = (fun k -> (FStar_List.existsb (fun k' -> (k' = k)) ocamlkeywords))


let idsym : mlident  ->  mlsymbol = (fun _74_6 -> (match (_74_6) with
| (s, _74_5) -> begin
s
end))


let string_of_mlpath : mlpath  ->  mlsymbol = (fun _74_9 -> (match (_74_9) with
| (p, s) -> begin
(FStar_String.concat "." (FStar_List.append p ((s)::[])))
end))


type gensym_t =
{gensym : Prims.unit  ->  mlident; reset : Prims.unit  ->  Prims.unit}


let is_Mkgensym_t : gensym_t  ->  Prims.bool = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mkgensym_t"))))


let gs : gensym_t = (

let ctr = (FStar_Util.mk_ref (Prims.parse_int "0"))
in (

let n_resets = (FStar_Util.mk_ref (Prims.parse_int "0"))
in {gensym = (fun _74_15 -> (match (()) with
| () -> begin
(let _173_34 = (let _173_33 = (let _173_32 = (let _173_28 = (FStar_ST.read n_resets)
in (FStar_Util.string_of_int _173_28))
in (let _173_31 = (let _173_30 = (let _173_29 = (

let _74_16 = (FStar_Util.incr ctr)
in (FStar_ST.read ctr))
in (FStar_Util.string_of_int _173_29))
in (Prims.strcat "_" _173_30))
in (Prims.strcat _173_32 _173_31)))
in (Prims.strcat "_" _173_33))
in ((_173_34), ((Prims.parse_int "0"))))
end)); reset = (fun _74_18 -> (match (()) with
| () -> begin
(

let _74_19 = (FStar_ST.op_Colon_Equals ctr (Prims.parse_int "0"))
in (FStar_Util.incr n_resets))
end))}))


let gensym : Prims.unit  ->  mlident = (fun _74_21 -> (match (()) with
| () -> begin
(gs.gensym ())
end))


let reset_gensym : Prims.unit  ->  Prims.unit = (fun _74_22 -> (match (()) with
| () -> begin
(gs.reset ())
end))


let rec gensyms : Prims.int  ->  mlident Prims.list = (fun x -> (match (x) with
| _173_42 when (_173_42 = (Prims.parse_int "0")) -> begin
[]
end
| n -> begin
(let _173_44 = (gensym ())
in (let _173_43 = (gensyms (n - (Prims.parse_int "1")))
in (_173_44)::_173_43))
end))


let mlpath_of_lident : FStar_Ident.lident  ->  mlpath = (fun x -> if (FStar_Ident.lid_equals x FStar_Syntax_Const.failwith_lid) then begin
(([]), (x.FStar_Ident.ident.FStar_Ident.idText))
end else begin
(let _173_48 = (FStar_List.map (fun x -> x.FStar_Ident.idText) x.FStar_Ident.ns)
in ((_173_48), (x.FStar_Ident.ident.FStar_Ident.idText)))
end)


let as_mlident = (fun x -> ((x.FStar_Absyn_Syntax.ppname.FStar_Ident.idText), ((Prims.parse_int "0"))))


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


let dummy_loc : (Prims.int * Prims.string) = (((Prims.parse_int "0")), (""))


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
| MLTY_Var (_74_32) -> begin
_74_32
end))


let ___MLTY_Fun____0 = (fun projectee -> (match (projectee) with
| MLTY_Fun (_74_35) -> begin
_74_35
end))


let ___MLTY_Named____0 = (fun projectee -> (match (projectee) with
| MLTY_Named (_74_38) -> begin
_74_38
end))


let ___MLTY_Tuple____0 = (fun projectee -> (match (projectee) with
| MLTY_Tuple (_74_41) -> begin
_74_41
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
| MLC_Bool (_74_44) -> begin
_74_44
end))


let ___MLC_Int____0 = (fun projectee -> (match (projectee) with
| MLC_Int (_74_47) -> begin
_74_47
end))


let ___MLC_Float____0 = (fun projectee -> (match (projectee) with
| MLC_Float (_74_50) -> begin
_74_50
end))


let ___MLC_Char____0 = (fun projectee -> (match (projectee) with
| MLC_Char (_74_53) -> begin
_74_53
end))


let ___MLC_String____0 = (fun projectee -> (match (projectee) with
| MLC_String (_74_56) -> begin
_74_56
end))


let ___MLC_Bytes____0 = (fun projectee -> (match (projectee) with
| MLC_Bytes (_74_59) -> begin
_74_59
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
| MLP_Const (_74_62) -> begin
_74_62
end))


let ___MLP_Var____0 = (fun projectee -> (match (projectee) with
| MLP_Var (_74_65) -> begin
_74_65
end))


let ___MLP_CTor____0 = (fun projectee -> (match (projectee) with
| MLP_CTor (_74_68) -> begin
_74_68
end))


let ___MLP_Branch____0 = (fun projectee -> (match (projectee) with
| MLP_Branch (_74_71) -> begin
_74_71
end))


let ___MLP_Record____0 = (fun projectee -> (match (projectee) with
| MLP_Record (_74_74) -> begin
_74_74
end))


let ___MLP_Tuple____0 = (fun projectee -> (match (projectee) with
| MLP_Tuple (_74_77) -> begin
_74_77
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
 and c_flag =
| Mutable
| Assumed
| Private
| NoExtract
| Attribute of Prims.string 
 and mlletflavor =
| Rec
| NonRec 
 and mlbranch =
(mlpattern * mlexpr Prims.option * mlexpr) 
 and mlletbinding =
(mlletflavor * c_flags * mllb Prims.list) 
 and c_flags =
c_flag Prims.list


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


let is_Mkmlexpr : mlexpr  ->  Prims.bool = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mkmlexpr"))))


let is_Mkmllb : mllb  ->  Prims.bool = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mkmllb"))))


let is_Mutable = (fun _discr_ -> (match (_discr_) with
| Mutable (_) -> begin
true
end
| _ -> begin
false
end))


let is_Assumed = (fun _discr_ -> (match (_discr_) with
| Assumed (_) -> begin
true
end
| _ -> begin
false
end))


let is_Private = (fun _discr_ -> (match (_discr_) with
| Private (_) -> begin
true
end
| _ -> begin
false
end))


let is_NoExtract = (fun _discr_ -> (match (_discr_) with
| NoExtract (_) -> begin
true
end
| _ -> begin
false
end))


let is_Attribute = (fun _discr_ -> (match (_discr_) with
| Attribute (_) -> begin
true
end
| _ -> begin
false
end))


let is_Rec = (fun _discr_ -> (match (_discr_) with
| Rec (_) -> begin
true
end
| _ -> begin
false
end))


let is_NonRec = (fun _discr_ -> (match (_discr_) with
| NonRec (_) -> begin
true
end
| _ -> begin
false
end))


let ___MLE_Const____0 = (fun projectee -> (match (projectee) with
| MLE_Const (_74_88) -> begin
_74_88
end))


let ___MLE_Var____0 = (fun projectee -> (match (projectee) with
| MLE_Var (_74_91) -> begin
_74_91
end))


let ___MLE_Name____0 = (fun projectee -> (match (projectee) with
| MLE_Name (_74_94) -> begin
_74_94
end))


let ___MLE_Let____0 = (fun projectee -> (match (projectee) with
| MLE_Let (_74_97) -> begin
_74_97
end))


let ___MLE_App____0 = (fun projectee -> (match (projectee) with
| MLE_App (_74_100) -> begin
_74_100
end))


let ___MLE_Fun____0 = (fun projectee -> (match (projectee) with
| MLE_Fun (_74_103) -> begin
_74_103
end))


let ___MLE_Match____0 = (fun projectee -> (match (projectee) with
| MLE_Match (_74_106) -> begin
_74_106
end))


let ___MLE_Coerce____0 = (fun projectee -> (match (projectee) with
| MLE_Coerce (_74_109) -> begin
_74_109
end))


let ___MLE_CTor____0 = (fun projectee -> (match (projectee) with
| MLE_CTor (_74_112) -> begin
_74_112
end))


let ___MLE_Seq____0 = (fun projectee -> (match (projectee) with
| MLE_Seq (_74_115) -> begin
_74_115
end))


let ___MLE_Tuple____0 = (fun projectee -> (match (projectee) with
| MLE_Tuple (_74_118) -> begin
_74_118
end))


let ___MLE_Record____0 = (fun projectee -> (match (projectee) with
| MLE_Record (_74_121) -> begin
_74_121
end))


let ___MLE_Proj____0 = (fun projectee -> (match (projectee) with
| MLE_Proj (_74_124) -> begin
_74_124
end))


let ___MLE_If____0 = (fun projectee -> (match (projectee) with
| MLE_If (_74_127) -> begin
_74_127
end))


let ___MLE_Raise____0 = (fun projectee -> (match (projectee) with
| MLE_Raise (_74_130) -> begin
_74_130
end))


let ___MLE_Try____0 = (fun projectee -> (match (projectee) with
| MLE_Try (_74_133) -> begin
_74_133
end))


let ___Attribute____0 = (fun projectee -> (match (projectee) with
| Attribute (_74_138) -> begin
_74_138
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
| MLTD_Abbrev (_74_141) -> begin
_74_141
end))


let ___MLTD_Record____0 = (fun projectee -> (match (projectee) with
| MLTD_Record (_74_144) -> begin
_74_144
end))


let ___MLTD_DType____0 = (fun projectee -> (match (projectee) with
| MLTD_DType (_74_147) -> begin
_74_147
end))


type one_mltydecl =
(Prims.bool * mlsymbol * mlsymbol Prims.option * mlidents * mltybody Prims.option)


type mltydecl =
one_mltydecl Prims.list


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
| MLM_Ty (_74_150) -> begin
_74_150
end))


let ___MLM_Let____0 = (fun projectee -> (match (projectee) with
| MLM_Let (_74_153) -> begin
_74_153
end))


let ___MLM_Exn____0 = (fun projectee -> (match (projectee) with
| MLM_Exn (_74_156) -> begin
_74_156
end))


let ___MLM_Top____0 = (fun projectee -> (match (projectee) with
| MLM_Top (_74_159) -> begin
_74_159
end))


let ___MLM_Loc____0 = (fun projectee -> (match (projectee) with
| MLM_Loc (_74_162) -> begin
_74_162
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
| MLS_Mod (_74_165) -> begin
_74_165
end))


let ___MLS_Ty____0 = (fun projectee -> (match (projectee) with
| MLS_Ty (_74_168) -> begin
_74_168
end))


let ___MLS_Val____0 = (fun projectee -> (match (projectee) with
| MLS_Val (_74_171) -> begin
_74_171
end))


let ___MLS_Exn____0 = (fun projectee -> (match (projectee) with
| MLS_Exn (_74_174) -> begin
_74_174
end))


let with_ty_loc : mlty  ->  mlexpr'  ->  mlloc  ->  mlexpr = (fun t e l -> {expr = e; mlty = t; loc = l})


let with_ty : mlty  ->  mlexpr'  ->  mlexpr = (fun t e -> (with_ty_loc t e dummy_loc))


type mllib =
| MLLib of (mlpath * (mlsig * mlmodule) Prims.option * mllib) Prims.list


let is_MLLib = (fun _discr_ -> (match (_discr_) with
| MLLib (_) -> begin
true
end
| _ -> begin
false
end))


let ___MLLib____0 = (fun projectee -> (match (projectee) with
| MLLib (_74_181) -> begin
_74_181
end))


let ml_unit_ty : mlty = MLTY_Named ((([]), (((("Prims")::[]), ("unit")))))


let ml_bool_ty : mlty = MLTY_Named ((([]), (((("Prims")::[]), ("bool")))))


let ml_int_ty : mlty = MLTY_Named ((([]), (((("Prims")::[]), ("int")))))


let ml_string_ty : mlty = MLTY_Named ((([]), (((("Prims")::[]), ("string")))))


let ml_unit : mlexpr = (with_ty ml_unit_ty (MLE_Const (MLC_Unit)))


let mlp_lalloc : (Prims.string Prims.list * Prims.string) = ((("SST")::[]), ("lalloc"))


let apply_obj_repr : mlexpr  ->  mlty  ->  mlexpr = (fun x t -> (

let obj_repr = (with_ty (MLTY_Fun (((t), (E_PURE), (MLTY_Top)))) (MLE_Name (((("Obj")::[]), ("repr")))))
in (with_ty_loc MLTY_Top (MLE_App (((obj_repr), ((x)::[])))) x.loc)))


let avoid_keyword : Prims.string  ->  Prims.string = (fun s -> if (is_reserved s) then begin
(Prims.strcat s "_")
end else begin
s
end)


let bv_as_mlident : FStar_Syntax_Syntax.bv  ->  mlident = (fun x -> if (((FStar_Util.starts_with x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText FStar_Ident.reserved_prefix) || (FStar_Syntax_Syntax.is_null_bv x)) || (is_reserved x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText)) then begin
(let _173_744 = (let _173_743 = (let _173_742 = (FStar_Util.string_of_int x.FStar_Syntax_Syntax.index)
in (Prims.strcat "_" _173_742))
in (Prims.strcat x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText _173_743))
in ((_173_744), ((Prims.parse_int "0"))))
end else begin
((x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText), ((Prims.parse_int "0")))
end)




