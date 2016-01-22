
open Prims
type name =
Prims.string

type wexp =
Prims.string

type wtyp =
Prims.string

type tlet =
| Mk_tlet of (name * wtyp * wexp)

let is_Mk_tlet = (fun _discr_ -> (match (_discr_) with
| Mk_tlet (_) -> begin
true
end
| _ -> begin
false
end))

let ___Mk_tlet____0 = (fun projectee -> (match (projectee) with
| Mk_tlet (_65_2) -> begin
_65_2
end))

let fn_map = (FStar_Util.smap_create 10)

type wys_lib_fn =
{fn_name : Prims.string; rem_args : Prims.int; arity : Prims.int; extracted_fn_name : Prims.string}

let is_Mkwys_lib_fn = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkwys_lib_fn"))))

let to_wys_lib_fn = (fun s1 n1 n2 s2 -> {fn_name = s1; rem_args = n1; arity = n2; extracted_fn_name = s2})

let wys_lib_args_map = (FStar_Util.smap_create 10)

let prims_trans_map = (FStar_Util.smap_create 10)

let slice_id = "slice_id"

let compose_ids = "compose_ids"

let slice_id_sps = "slice_id_sps"

let initialize = (fun _65_12 -> (let _65_14 = (FStar_Util.smap_add fn_map "Prims.int" (slice_id, compose_ids, slice_id_sps))
in (let _65_16 = (FStar_Util.smap_add fn_map "Prims.nat" (slice_id, compose_ids, slice_id_sps))
in (let _65_18 = (FStar_Util.smap_add fn_map "Prims.list" ("slice_list", "compose_lists", "slice_list_sps"))
in (let _65_20 = (FStar_Util.smap_add fn_map "Prims.option" ("slice_option", "compose_options", "slice_option_sps"))
in (let _65_22 = (FStar_Util.smap_add fn_map "Prims.Tuple2" ("slice_tuple", "compose_tuples", "slice_tuple_sps"))
in (let _65_24 = (FStar_Util.smap_add wys_lib_args_map "as_par" (to_wys_lib_fn "as_par" 0 2 "mk_aspar"))
in (let _65_26 = (FStar_Util.smap_add wys_lib_args_map "as_sec" (to_wys_lib_fn "as_sec" 0 2 "mk_assec"))
in (let _65_28 = (FStar_Util.smap_add wys_lib_args_map "unbox_p" (to_wys_lib_fn "unbox_p" 1 1 "mk_unbox"))
in (let _65_30 = (FStar_Util.smap_add wys_lib_args_map "unbox_s" (to_wys_lib_fn "unbox_s" 1 1 "mk_unbox"))
in (let _65_32 = (FStar_Util.smap_add wys_lib_args_map "box" (to_wys_lib_fn "box" 0 2 "mk_box"))
in (let _65_34 = (FStar_Util.smap_add wys_lib_args_map "mkwire_p" (to_wys_lib_fn "mkwire_p" 1 2 "mk_mkwire"))
in (let _65_36 = (FStar_Util.smap_add wys_lib_args_map "mkwire_s" (to_wys_lib_fn "mkwire_s" 0 2 "mk_mkwire"))
in (let _65_38 = (FStar_Util.smap_add wys_lib_args_map "projwire_p" (to_wys_lib_fn "projwire_p" 1 2 "mk_projwire"))
in (let _65_40 = (FStar_Util.smap_add wys_lib_args_map "projwire_s" (to_wys_lib_fn "projwire_s" 1 2 "mk_projwire"))
in (let _65_42 = (FStar_Util.smap_add wys_lib_args_map "concat_wire" (to_wys_lib_fn "concat_wire" 2 2 "mk_concatwire"))
in (let _65_44 = (FStar_Util.smap_add prims_trans_map "Prims.op_Multiply" "Prims.( * )")
in (let _65_46 = (FStar_Util.smap_add prims_trans_map "Prims.op_Subtraction" "Prims.(-)")
in (let _65_48 = (FStar_Util.smap_add prims_trans_map "Prims.op_Addition" "Prims.(+)")
in (let _65_50 = (FStar_Util.smap_add prims_trans_map "Prims.op_LessThanOrEqual" "Prims.(<=)")
in (let _65_52 = (FStar_Util.smap_add prims_trans_map "Prims.op_GreaterThan" "Prims.(>)")
in (let _65_54 = (FStar_Util.smap_add prims_trans_map "Prims.op_GreaterThanOrEqual" "Prims.(>=)")
in (let _65_56 = (FStar_Util.smap_add prims_trans_map "Prims.op_LessThan" "Prims.(<)")
in (let _65_58 = (FStar_Util.smap_add prims_trans_map "Prims.op_Modulus" "Prims.(%)")
in ()))))))))))))))))))))))))

let lookup_ffi_map = (fun t -> (let m = (FStar_Util.smap_try_find fn_map t)
in (match (m) with
| Some (m) -> begin
m
end
| _65_65 -> begin
(FStar_All.failwith (Prims.strcat "Unknown user type: " t))
end)))

let lookup_wys_lib_map = (fun s -> (match ((FStar_Util.smap_try_find wys_lib_args_map s)) with
| Some (x) -> begin
x
end
| _65_70 -> begin
(FStar_All.failwith "Unknown wysteria library function")
end))

let translate_ffi_name = (fun s -> (match ((FStar_Util.smap_try_find prims_trans_map s)) with
| Some (x) -> begin
x
end
| None -> begin
s
end))

let rec sublist = (fun s l n -> if (n > (FStar_List.length l)) then begin
(let _132_46 = (let _132_45 = (FStar_Util.string_of_int (FStar_List.length l))
in (let _132_44 = (FStar_Util.string_of_int n)
in (FStar_Util.format3 "Error removing arguments in sublist for %s, list len is %s, n is %s " s _132_45 _132_44)))
in (FStar_All.failwith _132_46))
end else begin
if (n = 0) then begin
l
end else begin
(let _132_47 = (FStar_List.tl l)
in (sublist s _132_47 (n - 1)))
end
end)

let is_bool = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named (_65_81, p) -> begin
((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "Prims.bool")
end
| _65_86 -> begin
false
end))

let is_int = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named (_65_89, p) -> begin
((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "Prims.int")
end
| _65_94 -> begin
false
end))

let is_unit = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named (_65_97, p) -> begin
((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "Prims.unit")
end
| _65_102 -> begin
false
end))

let is_prin = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named (_65_105, p) -> begin
((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "Prins.prin")
end
| _65_110 -> begin
false
end))

let is_prins = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named (_65_113, p) -> begin
((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "Prins.prins")
end
| _65_118 -> begin
false
end))

let is_eprins = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named (_65_121, p) -> begin
((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "Prins.eprins")
end
| _65_126 -> begin
false
end))

let is_box = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named (_65_129, p) -> begin
((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "Wysteria.Box")
end
| _65_134 -> begin
false
end))

let is_wire = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named (_65_137, p) -> begin
((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "Wysteria.Wire")
end
| _65_142 -> begin
false
end))

let box_content_type = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named (l, p) -> begin
if ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "Wysteria.Box") then begin
(FStar_List.hd l)
end else begin
(FStar_All.failwith "Cannot get content for non box named type")
end
end
| _65_149 -> begin
(FStar_All.failwith "Cannot get content for non-named type")
end))

let wire_content_type = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named (l, p) -> begin
if ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "Wysteria.Wire") then begin
(FStar_List.hd l)
end else begin
(FStar_All.failwith "Cannot get content for non wire named type")
end
end
| _65_156 -> begin
(FStar_All.failwith "Cannot get content for non-named type")
end))

let is_wysteria_type = (fun t -> (((((is_prin t) || (is_prins t)) || (is_eprins t)) || (is_box t)) || (is_wire t)))

let slice_value = "Semantics.slice_v_ffi"

let slice_value_sps = "Semantics.slice_v_sps_ffi"

let compose_values = "Semantics.compose_vals_ffi"

let rec get_opaque_fns = (fun t -> if (((((is_bool t) || (is_unit t)) || (is_prin t)) || (is_prins t)) || (is_eprins t)) then begin
(slice_id, compose_ids, slice_id_sps)
end else begin
if ((is_box t) || (is_wire t)) then begin
(slice_value, compose_values, slice_value_sps)
end else begin
(match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) -> begin
(lookup_ffi_map (FStar_Extraction_ML_Syntax.string_of_mlpath p))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, p) -> begin
(let _65_170 = (get_opaque_fns (FStar_Extraction_ML_Syntax.MLTY_Named (([], p))))
in (match (_65_170) with
| (e1, e2, e3) -> begin
(FStar_List.fold_left (fun _65_174 arg -> (match (_65_174) with
| (a1, a2, a3) -> begin
(match (arg) with
| FStar_Extraction_ML_Syntax.MLTY_Named (_65_177) -> begin
(let _65_182 = (get_opaque_fns arg)
in (match (_65_182) with
| (e1_arg, e2_arg, e3_arg) -> begin
((Prims.strcat (Prims.strcat (Prims.strcat (Prims.strcat "(" a1) " ") e1_arg) ")"), (Prims.strcat (Prims.strcat (Prims.strcat (Prims.strcat "(" a2) " ") e2_arg) ")"), (Prims.strcat (Prims.strcat (Prims.strcat (Prims.strcat "(" a3) " ") e3_arg) ")"))
end))
end
| _65_184 -> begin
(FStar_All.failwith "Did not expect type argument to be something other than named type")
end)
end)) (e1, e2, e3) args)
end))
end
| _65_186 -> begin
(FStar_All.failwith "Did not expect a non named type in get_opaque_fns")
end)
end
end)

let get_injection = (fun t -> (let s = "fun x -> "
in (let s' = if (is_bool t) then begin
"D_v (const_meta, V_bool x)"
end else begin
if (is_unit t) then begin
"D_v (const_meta, V_unit)"
end else begin
if (is_prin t) then begin
"D_v (const_meta, V_prin x)"
end else begin
if ((is_prins t) || (is_eprins t)) then begin
"D_v (const_meta, V_eprins x)"
end else begin
if ((is_box t) || (is_wire t)) then begin
"x"
end else begin
(let _65_192 = (get_opaque_fns t)
in (match (_65_192) with
| (s1, s2, s3) -> begin
(Prims.strcat (Prims.strcat (Prims.strcat (Prims.strcat (Prims.strcat "mk_v_opaque x " s1) " ") s2) " ") s3)
end))
end
end
end
end
end
in (Prims.strcat s s'))))

let is_known_named_type = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named (_65_196, p) -> begin
(let s_opt = (FStar_Util.smap_try_find fn_map (FStar_Extraction_ML_Syntax.string_of_mlpath p))
in if (s_opt = None) then begin
false
end else begin
true
end)
end
| _65_202 -> begin
(FStar_All.failwith "Is_known_named_type was not called with a named type")
end))

let name_to_string = (fun s -> (Prims.strcat (Prims.strcat "\"" s) "\""))

let rec mlty_to_typ = (fun t -> if (is_bool t) then begin
"T_bool"
end else begin
if (is_unit t) then begin
"T_unit"
end else begin
if (is_prin t) then begin
"T_prin"
end else begin
if (is_prins t) then begin
"T_eprins"
end else begin
if (is_box t) then begin
(let _132_84 = (let _132_83 = (let _132_82 = (box_content_type t)
in (mlty_to_typ _132_82))
in (Prims.strcat "T_box (" _132_83))
in (Prims.strcat _132_84 ")"))
end else begin
if (is_wire t) then begin
(let _132_87 = (let _132_86 = (let _132_85 = (wire_content_type t)
in (mlty_to_typ _132_85))
in (Prims.strcat "T_wire (" _132_86))
in (Prims.strcat _132_87 ")"))
end else begin
(match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named (l, p) -> begin
(let n = (Prims.strcat "T_cons (" (name_to_string (FStar_Extraction_ML_Syntax.string_of_mlpath p)))
in (let args = (FStar_List.fold_left (fun s a -> (let _132_91 = (let _132_90 = (mlty_to_typ a)
in (Prims.strcat (Prims.strcat s " (") _132_90))
in (Prims.strcat _132_91 ");"))) "" l)
in (Prims.strcat (Prims.strcat (Prims.strcat n ", [") args) "])")))
end
| _65_214 -> begin
"T_unknown"
end)
end
end
end
end
end
end)

let get_constant_injection = (fun t x -> if (is_bool t) then begin
(Prims.strcat "C_bool " x)
end else begin
if (is_unit t) then begin
"C_unit ()"
end else begin
if (is_known_named_type t) then begin
(let _132_97 = (let _132_96 = (mlty_to_typ t)
in (Prims.strcat (Prims.strcat (Prims.strcat "C_opaque ((), Obj.magic " x) ", ") _132_96))
in (Prims.strcat _132_97 ")"))
end else begin
(FStar_All.failwith "Constant injection does not support this type")
end
end
end)

let is_ffi = (fun _65_219 -> (match (_65_219) with
| {FStar_Extraction_ML_Syntax.expr = e; FStar_Extraction_ML_Syntax.ty = t} -> begin
(match (e) with
| FStar_Extraction_ML_Syntax.MLE_Name (p, n) -> begin
(let _132_100 = (translate_ffi_name (FStar_Extraction_ML_Syntax.string_of_mlpath (p, n)))
in (((p = ("FFI")::[]) || (p = ("Prims")::[])), _132_100))
end
| _65_225 -> begin
(false, "")
end)
end))

let tag_of_mlconst = (fun c -> (match (c) with
| FStar_Extraction_ML_Syntax.MLC_Unit -> begin
"MLC_Unit"
end
| FStar_Extraction_ML_Syntax.MLC_Bool (_65_229) -> begin
"MLC_Bool"
end
| FStar_Extraction_ML_Syntax.MLC_Char (_65_232) -> begin
"MLC_Char"
end
| FStar_Extraction_ML_Syntax.MLC_Byte (_65_235) -> begin
"MLC_Byte"
end
| FStar_Extraction_ML_Syntax.MLC_Int32 (_65_238) -> begin
"MLC_Int32"
end
| FStar_Extraction_ML_Syntax.MLC_Int64 (_65_241) -> begin
"MLC_Int64"
end
| FStar_Extraction_ML_Syntax.MLC_Int (_65_244) -> begin
"MLC_Int"
end
| FStar_Extraction_ML_Syntax.MLC_Float (_65_247) -> begin
"MLC_Float"
end
| FStar_Extraction_ML_Syntax.MLC_Bytes (_65_250) -> begin
"MLC_Bytes"
end
| FStar_Extraction_ML_Syntax.MLC_String (_65_253) -> begin
"MLC_String"
end))

let extract_mlconst = (fun c -> (match (c) with
| FStar_Extraction_ML_Syntax.MLC_Unit -> begin
"C_unit ()"
end
| FStar_Extraction_ML_Syntax.MLC_Bool (b) -> begin
(Prims.strcat "C_bool " (if b then begin
"true"
end else begin
"false"
end))
end
| FStar_Extraction_ML_Syntax.MLC_Int32 (n) -> begin
(Prims.strcat (Prims.strcat "C_opaque ((), Obj.magic " (FStar_Util.string_of_int32 n)) ", T_cons (\"Prims.int\", []))")
end
| FStar_Extraction_ML_Syntax.MLC_Int64 (n) -> begin
(Prims.strcat (Prims.strcat "C_opaque ((), Obj.magic " (FStar_Util.string_of_int64 n)) ", T_cons (\"Prims.int\", []))")
end
| FStar_Extraction_ML_Syntax.MLC_Int (x) -> begin
(Prims.strcat (Prims.strcat "C_opaque ((), Obj.magic " x) ", T_cons (\"Prims.int\", []))")
end
| FStar_Extraction_ML_Syntax.MLC_String (s) -> begin
(Prims.strcat (Prims.strcat "C_opaque ((), Obj.magic (\"" s) "\"), T_unknown)")
end
| _65_268 -> begin
(FStar_All.failwith (Prims.strcat "Unsupported constant: tag: " (tag_of_mlconst c)))
end))

let is_wys_lib_fn = (fun _65_271 -> (match (_65_271) with
| {FStar_Extraction_ML_Syntax.expr = e; FStar_Extraction_ML_Syntax.ty = t} -> begin
(match (e) with
| FStar_Extraction_ML_Syntax.MLE_Name (p) -> begin
(FStar_Util.starts_with (FStar_Extraction_ML_Syntax.string_of_mlpath p) "Wysteria")
end
| _65_275 -> begin
false
end)
end))

let check_pats_for_bool = (fun l -> (let def = (false, FStar_Extraction_ML_Syntax.ml_unit, FStar_Extraction_ML_Syntax.ml_unit)
in if ((FStar_List.length l) <> 2) then begin
def
end else begin
(let _65_282 = (FStar_List.hd l)
in (match (_65_282) with
| (p1, _65_280, e1) -> begin
(let _65_287 = (let _132_109 = (FStar_List.tl l)
in (FStar_List.hd _132_109))
in (match (_65_287) with
| (p2, _65_285, e2) -> begin
(match ((p1, p2)) with
| (FStar_Extraction_ML_Syntax.MLP_Const (FStar_Extraction_ML_Syntax.MLC_Bool (_65_289)), FStar_Extraction_ML_Syntax.MLP_Const (FStar_Extraction_ML_Syntax.MLC_Bool (_65_293))) -> begin
(true, e1, e2)
end
| _65_298 -> begin
def
end)
end))
end))
end))

let mk_var = (fun s t -> (let _132_115 = (let _132_114 = (mlty_to_typ t)
in (Prims.strcat (Prims.strcat (Prims.strcat "mk_var " (name_to_string s)) " (") _132_114))
in (Prims.strcat _132_115 ")")))

let mk_varname = (fun s t -> (let _132_121 = (let _132_120 = (mlty_to_typ t)
in (Prims.strcat (Prims.strcat (Prims.strcat "mk_varname " (name_to_string s)) " (") _132_120))
in (Prims.strcat _132_121 ")")))

let rec extract_mlexp = (fun _65_305 -> (match (_65_305) with
| {FStar_Extraction_ML_Syntax.expr = e; FStar_Extraction_ML_Syntax.ty = t} -> begin
(match (e) with
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(let _132_128 = (let _132_127 = (extract_mlconst c)
in (Prims.strcat "mk_const (" _132_127))
in (Prims.strcat _132_128 ")"))
end
| FStar_Extraction_ML_Syntax.MLE_Var (x) -> begin
(mk_var (FStar_Extraction_ML_Syntax.idsym x) t)
end
| FStar_Extraction_ML_Syntax.MLE_Name (p, s) -> begin
(let ss = (FStar_Extraction_ML_Syntax.string_of_mlpath (p, s))
in (let _65_315 = if (not ((FStar_Util.starts_with ss "SMC."))) then begin
(let _132_129 = (FStar_Util.format1 "Warning: name not applied: %s\n" (FStar_Extraction_ML_Syntax.string_of_mlpath (p, s)))
in (FStar_Util.print_string _132_129))
end else begin
()
end
in (mk_var s t)))
end
| FStar_Extraction_ML_Syntax.MLE_Let ((b, l), e') -> begin
if b then begin
(FStar_All.failwith "Nested recursive lets are not supported yet")
end else begin
(let lb = (FStar_List.hd l)
in (let lbname = (FStar_Extraction_ML_Syntax.idsym lb.FStar_Extraction_ML_Syntax.mllb_name)
in (let lbbody = lb.FStar_Extraction_ML_Syntax.mllb_def
in (let _132_137 = (let _132_136 = (let _132_134 = (let _132_133 = (let _132_131 = (let _132_130 = (mk_varname lbname lbbody.FStar_Extraction_ML_Syntax.ty)
in (Prims.strcat "mk_let (" _132_130))
in (Prims.strcat _132_131 ") ("))
in (let _132_132 = (extract_mlexp lbbody)
in (Prims.strcat _132_133 _132_132)))
in (Prims.strcat _132_134 ") ("))
in (let _132_135 = (extract_mlexp e')
in (Prims.strcat _132_136 _132_135)))
in (Prims.strcat _132_137 ")")))))
end
end
| FStar_Extraction_ML_Syntax.MLE_App (f, args) -> begin
(let _65_332 = (is_ffi f)
in (match (_65_332) with
| (b, ffi) -> begin
if b then begin
(let inj = (get_injection t)
in (let args_exp = (FStar_List.fold_left (fun s a -> (let _132_141 = (let _132_140 = (extract_mlexp a)
in (Prims.strcat (Prims.strcat s " (") _132_140))
in (Prims.strcat _132_141 ");"))) "" args)
in (let _132_151 = (let _132_150 = (let _132_149 = (let _132_148 = (let _132_147 = (let _132_146 = (let _132_145 = (let _132_144 = (let _132_143 = (let _132_142 = (FStar_Util.string_of_int (FStar_List.length args))
in (Prims.strcat "mk_ffi " _132_142))
in (Prims.strcat _132_143 " "))
in (Prims.strcat _132_144 (name_to_string ffi)))
in (Prims.strcat _132_145 " ("))
in (Prims.strcat _132_146 ffi))
in (Prims.strcat _132_147 ") [ "))
in (Prims.strcat _132_148 args_exp))
in (Prims.strcat _132_149 " ] ("))
in (Prims.strcat _132_150 inj))
in (Prims.strcat _132_151 ")"))))
end else begin
if (is_wys_lib_fn f) then begin
(extract_wysteria_specific_ast f args t)
end else begin
(let s = (extract_mlexp f)
in if (s = "_assert") then begin
"mk_const (C_unit ())"
end else begin
(FStar_List.fold_left (fun s a -> (let _132_155 = (let _132_154 = (extract_mlexp a)
in (Prims.strcat (Prims.strcat (Prims.strcat "mk_app (" s) ") (") _132_154))
in (Prims.strcat _132_155 ")"))) s args)
end)
end
end
end))
end
| FStar_Extraction_ML_Syntax.MLE_Fun (bs, body) -> begin
(let body_str = (extract_mlexp body)
in (FStar_List.fold_left (fun s _65_351 -> (match (_65_351) with
| ((b, _65_348), t) -> begin
(let _132_161 = (let _132_160 = (let _132_159 = (let _132_158 = (mk_varname b t)
in (Prims.strcat "mk_abs (" _132_158))
in (Prims.strcat _132_159 ") ("))
in (Prims.strcat _132_160 s))
in (Prims.strcat _132_161 ")"))
end)) body_str (FStar_List.rev bs)))
end
| FStar_Extraction_ML_Syntax.MLE_Match (e, bs) -> begin
(let _65_359 = (check_pats_for_bool bs)
in (match (_65_359) with
| (b, e1, e2) -> begin
if b then begin
(let _132_169 = (let _132_168 = (let _132_166 = (let _132_165 = (let _132_163 = (let _132_162 = (extract_mlexp e)
in (Prims.strcat "mk_cond (" _132_162))
in (Prims.strcat _132_163 ") ("))
in (let _132_164 = (extract_mlexp e1)
in (Prims.strcat _132_165 _132_164)))
in (Prims.strcat _132_166 ") ("))
in (let _132_167 = (extract_mlexp e2)
in (Prims.strcat _132_168 _132_167)))
in (Prims.strcat _132_169 ")"))
end else begin
(FStar_All.failwith "Only if-then-else patterns are supported")
end
end))
end
| FStar_Extraction_ML_Syntax.MLE_Coerce (e, _65_362, _65_364) -> begin
(extract_mlexp e)
end
| FStar_Extraction_ML_Syntax.MLE_If (e, e1, e2_opt) -> begin
(match (e2_opt) with
| None -> begin
(FStar_All.failwith "If Then Else should have an else branch?")
end
| Some (e2) -> begin
(let _132_177 = (let _132_176 = (let _132_174 = (let _132_173 = (let _132_171 = (let _132_170 = (extract_mlexp e)
in (Prims.strcat "mk_cond (" _132_170))
in (Prims.strcat _132_171 ") ("))
in (let _132_172 = (extract_mlexp e1)
in (Prims.strcat _132_173 _132_172)))
in (Prims.strcat _132_174 ") ("))
in (let _132_175 = (extract_mlexp e2)
in (Prims.strcat _132_176 _132_175)))
in (Prims.strcat _132_177 ")"))
end)
end
| _65_376 -> begin
(FStar_All.failwith "This expression extraction is not supported yet")
end)
end))
and extract_wysteria_specific_ast = (fun _65_380 args t -> (match (_65_380) with
| {FStar_Extraction_ML_Syntax.expr = f; FStar_Extraction_ML_Syntax.ty = _65_378} -> begin
(match (f) with
| FStar_Extraction_ML_Syntax.MLE_Name (_65_384, s) -> begin
if (s = "main") then begin
(let f = (let _132_181 = (FStar_List.tl args)
in (FStar_List.hd _132_181))
in (let f_exp = (extract_mlexp f)
in (Prims.strcat (Prims.strcat "mk_app (" f_exp) ") (E_const (C_unit ()))")))
end else begin
if (s = "w_read_int") then begin
(let inj_str = (get_injection t)
in (Prims.strcat (Prims.strcat "mk_ffi 1 \"FFI.read_int\" FFI.read_int [ E_const (C_unit ()) ] (" inj_str) ")"))
end else begin
if (s = "w_read_int_tuple") then begin
(let inj_str = (get_injection t)
in (Prims.strcat (Prims.strcat "mk_ffi 1 \"FFI.read_int_tuple\" FFI.read_int_tuple [ E_const (C_unit ()) ] (" inj_str) ")"))
end else begin
if (s = "w_read_int_list") then begin
(let inj_str = (get_injection t)
in (Prims.strcat (Prims.strcat "mk_ffi 1 \"FFI.read_int_list\" FFI.read_int_list [ E_const (C_unit ()) ] (" inj_str) ")"))
end else begin
(let r = (lookup_wys_lib_map s)
in (let args = (sublist s args r.rem_args)
in (FStar_List.fold_left (fun acc arg -> (let _132_185 = (let _132_184 = (extract_mlexp arg)
in (Prims.strcat (Prims.strcat acc " (") _132_184))
in (Prims.strcat _132_185 ")"))) r.extracted_fn_name args)))
end
end
end
end
end
| _65_398 -> begin
(FStar_All.failwith "Expected wysteria lib fn to be a MLE_Name")
end)
end))

let extract_mllb = (fun _65_401 -> (match (_65_401) with
| (b, l) -> begin
if ((FStar_List.length l) <> 1) then begin
(FStar_All.failwith "Mutually recursive lets are not yet suppored")
end else begin
(let lb = (FStar_List.hd l)
in (let lbname = (FStar_Extraction_ML_Syntax.idsym lb.FStar_Extraction_ML_Syntax.mllb_name)
in (let lbbody = lb.FStar_Extraction_ML_Syntax.mllb_def
in if b then begin
(match (lbbody.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Fun (bs, e) -> begin
(let _65_411 = (let _132_189 = (FStar_List.hd bs)
in (let _132_188 = (FStar_List.tl bs)
in (_132_189, _132_188)))
in (match (_65_411) with
| (first_b, rest_bs) -> begin
(let body_exp = (extract_mlexp e)
in (let tl_abs_exp = (FStar_List.fold_left (fun e _65_416 -> (match (_65_416) with
| (bname, btyp) -> begin
(let _132_195 = (let _132_194 = (let _132_193 = (let _132_192 = (mk_varname (FStar_Extraction_ML_Syntax.idsym bname) btyp)
in (Prims.strcat "mk_abs (" _132_192))
in (Prims.strcat _132_193 ") ("))
in (Prims.strcat _132_194 e))
in (Prims.strcat _132_195 ")"))
end)) body_exp (FStar_List.rev rest_bs))
in (let fix_exp = (let _132_202 = (let _132_201 = (let _132_200 = (let _132_199 = (let _132_197 = (let _132_196 = (mk_varname lbname lbbody.FStar_Extraction_ML_Syntax.ty)
in (Prims.strcat "mk_fix (" _132_196))
in (Prims.strcat _132_197 ") ("))
in (let _132_198 = (mk_varname (FStar_Extraction_ML_Syntax.idsym (Prims.fst first_b)) (Prims.snd first_b))
in (Prims.strcat _132_199 _132_198)))
in (Prims.strcat _132_200 ") ("))
in (Prims.strcat _132_201 tl_abs_exp))
in (Prims.strcat _132_202 ")"))
in (let _132_204 = (let _132_203 = (mlty_to_typ lbbody.FStar_Extraction_ML_Syntax.ty)
in (lbname, _132_203, fix_exp))
in Mk_tlet (_132_204)))))
end))
end
| _65_420 -> begin
(FStar_All.failwith "Recursive let binding is not an abstraction ?")
end)
end else begin
(let _132_207 = (let _132_206 = (mlty_to_typ lbbody.FStar_Extraction_ML_Syntax.ty)
in (let _132_205 = (extract_mlexp lbbody)
in (lbname, _132_206, _132_205)))
in Mk_tlet (_132_207))
end)))
end
end))

let extract_mlmodule = (fun m -> (FStar_List.fold_left (fun _65_424 tld -> (match (_65_424) with
| (l, top_opt) -> begin
(match (tld) with
| FStar_Extraction_ML_Syntax.MLM_Ty (_65_427) -> begin
(l, top_opt)
end
| FStar_Extraction_ML_Syntax.MLM_Exn (_65_430) -> begin
(FStar_All.failwith "Cannot extract an exception")
end
| FStar_Extraction_ML_Syntax.MLM_Let (lb) -> begin
(let _132_214 = (let _132_213 = (let _132_212 = (extract_mllb lb)
in (_132_212)::[])
in (FStar_List.append l _132_213))
in (_132_214, top_opt))
end
| FStar_Extraction_ML_Syntax.MLM_Top (e) -> begin
(match (top_opt) with
| None -> begin
(let _132_216 = (let _132_215 = (extract_mlexp e)
in Some (_132_215))
in (l, _132_216))
end
| Some (_65_438) -> begin
(FStar_All.failwith "Impossible: more than one top expressions")
end)
end)
end)) ([], None) m))

let rec find_smc_module = (fun mllibs -> (let rec find_smc_module' = (fun mllib -> (match (mllib) with
| [] -> begin
None
end
| (x, mlsig_opt, FStar_Extraction_ML_Syntax.MLLib (mllib'))::tl -> begin
if (x = "SMC") then begin
(match (mlsig_opt) with
| Some (_65_452, m) -> begin
Some (m)
end
| None -> begin
(Prims.raise (FStar_Util.NYI ("Found the SMC module name but no module")))
end)
end else begin
(let m_opt = (find_smc_module' mllib')
in (match (m_opt) with
| Some (m) -> begin
Some (m)
end
| None -> begin
(find_smc_module' tl)
end))
end
end))
in (match (mllibs) with
| [] -> begin
None
end
| FStar_Extraction_ML_Syntax.MLLib (s)::tl -> begin
(let m_opt = (find_smc_module' s)
in (match (m_opt) with
| Some (m) -> begin
Some (m)
end
| None -> begin
(find_smc_module tl)
end))
end)))

let mltyp_to_string = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named (_65_472, p) -> begin
(FStar_Extraction_ML_Syntax.string_of_mlpath p)
end
| _65_477 -> begin
"Something other than named type"
end))

let rec get_iface_arg_ret_typ = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (arg, _65_481, ret) -> begin
(match (ret) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (_65_486, _65_488, _65_490) -> begin
(get_iface_arg_ret_typ ret)
end
| _65_494 -> begin
(arg, ret)
end)
end
| _65_496 -> begin
(FStar_All.failwith "Get wys arg ret type has a non-arrow type")
end))

let extract_smc_exports = (fun g -> (FStar_List.fold_left (fun s b -> (match (b) with
| FStar_Extraction_ML_Env.Fv (fvv, _65_502, t) -> begin
if (FStar_Util.starts_with fvv.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.str "Smciface") then begin
(let fn_name = fvv.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ident.FStar_Absyn_Syntax.idText
in (let _65_509 = (get_iface_arg_ret_typ (Prims.snd t))
in (match (_65_509) with
| (arg, ret) -> begin
(let arg_inj = (get_constant_injection arg "x")
in (let s0 = (Prims.strcat (Prims.strcat "let " fn_name) " ps p x = \n")
in (let s1 = "let e1 = mk_const (C_eprins ps) in\n"
in (let s2 = (Prims.strcat (Prims.strcat "let e2 = mk_mkwire (mk_const (C_eprins (singleton p))) (mk_box (mk_const (C_eprins (singleton p))) (mk_const (" arg_inj) "))) in\n")
in (let s3 = (let _132_230 = (let _132_229 = (mlty_to_typ (Prims.snd t))
in (Prims.strcat (Prims.strcat (Prims.strcat "let dv = Interpreteriface.run p \"" fn_name) "\" ") _132_229))
in (Prims.strcat _132_230 " [e1; e2] in\n"))
in (let s4 = "Obj.magic (Interpreteriface.project_value_content dv)\n"
in (Prims.strcat (Prims.strcat s (Prims.strcat (Prims.strcat (Prims.strcat (Prims.strcat s0 s1) s2) s3) s4)) "\n\n")))))))
end)))
end else begin
s
end
end
| _65_517 -> begin
s
end)) "" g.FStar_Extraction_ML_Env.gamma))

let extract = (fun l en -> (let _65_520 = (initialize ())
in (let _65_524 = (let _132_235 = (FStar_Extraction_ML_Env.mkContext en)
in (FStar_Util.fold_map FStar_Extraction_ML_ExtractMod.extract _132_235 l))
in (match (_65_524) with
| (c, mllibs) -> begin
(let s_exports = (extract_smc_exports c)
in (let mllibs = (FStar_List.flatten mllibs)
in (let m_opt = (find_smc_module mllibs)
in (let s_smc = (match (m_opt) with
| Some (m) -> begin
(let _65_532 = (extract_mlmodule m)
in (match (_65_532) with
| (l, m_opt) -> begin
(FStar_List.fold_left (fun s _65_538 -> (match (_65_538) with
| Mk_tlet (n, t, b) -> begin
(Prims.strcat (Prims.strcat (Prims.strcat (Prims.strcat (Prims.strcat (Prims.strcat (Prims.strcat s "(") (name_to_string n)) ", (") t) "), (") b) "));\n")
end)) "" l)
end))
end
| _65_540 -> begin
""
end)
in (let smciface = (let _132_238 = (FStar_Options.prependOutputDir "smciface.ml")
in (FStar_Util.open_file_for_writing _132_238))
in (let _65_543 = (FStar_Util.append_to_file smciface "open Ffibridge")
in (let _65_545 = (FStar_Util.append_to_file smciface "open FFI")
in (let _65_547 = (FStar_Util.append_to_file smciface "open AST")
in (let _65_549 = (FStar_Util.append_to_file smciface "\n")
in (let _65_551 = (FStar_Util.append_to_file smciface s_exports)
in (let _65_553 = (FStar_Util.close_file smciface)
in (let prog = (let _132_239 = (FStar_Options.prependOutputDir "prog.ml")
in (FStar_Util.open_file_for_writing _132_239))
in (let _65_556 = (FStar_Util.append_to_file prog "open AST")
in (let _65_558 = (FStar_Util.append_to_file prog "open FFI")
in (let _65_560 = (FStar_Util.append_to_file prog "\n")
in (let _65_562 = (FStar_Util.append_to_file prog "let const_meta = Meta ([], Can_b, [], Can_w)")
in (let _65_564 = (FStar_Util.append_to_file prog "\n")
in (let _65_566 = (FStar_Util.append_to_file prog (Prims.strcat (Prims.strcat "let program = [\n" s_smc) "]"))
in (FStar_Util.close_file prog)))))))))))))))))))
end))))




