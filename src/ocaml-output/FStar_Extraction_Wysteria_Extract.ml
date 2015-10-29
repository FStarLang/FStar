
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
| Mk_tlet (_64_2) -> begin
_64_2
end))

let fn_map = (FStar_Util.smap_create 10)

type wys_lib_fn =
{fn_name : Prims.string; rem_args : Prims.int; arity : Prims.int; extracted_fn_name : Prims.string}

let is_Mkwys_lib_fn = (Obj.magic (fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkwys_lib_fn")))

let to_wys_lib_fn = (fun s1 n1 n2 s2 -> {fn_name = s1; rem_args = n1; arity = n2; extracted_fn_name = s2})

let wys_lib_args_map = (FStar_Util.smap_create 10)

let prims_trans_map = (FStar_Util.smap_create 10)

let slice_id = "slice_id"

let compose_ids = "compose_ids"

let slice_id_sps = "slice_id_sps"

let initialize = (fun _64_12 -> (let _64_14 = (FStar_Util.smap_add fn_map "Prims.int" (slice_id, compose_ids, slice_id_sps))
in (let _64_16 = (FStar_Util.smap_add fn_map "Prims.nat" (slice_id, compose_ids, slice_id_sps))
in (let _64_18 = (FStar_Util.smap_add fn_map "Prims.list" ("slice_list", "compose_lists", "slice_list_sps"))
in (let _64_20 = (FStar_Util.smap_add fn_map "Prims.option" ("slice_option", "compose_options", "slice_option_sps"))
in (let _64_22 = (FStar_Util.smap_add fn_map "Prims.Tuple2" ("slice_tuple", "compose_tuples", "slice_tuple_sps"))
in (let _64_24 = (FStar_Util.smap_add wys_lib_args_map "as_par" (to_wys_lib_fn "as_par" 0 2 "mk_aspar"))
in (let _64_26 = (FStar_Util.smap_add wys_lib_args_map "as_sec" (to_wys_lib_fn "as_sec" 0 2 "mk_assec"))
in (let _64_28 = (FStar_Util.smap_add wys_lib_args_map "unbox_p" (to_wys_lib_fn "unbox_p" 1 1 "mk_unbox"))
in (let _64_30 = (FStar_Util.smap_add wys_lib_args_map "unbox_s" (to_wys_lib_fn "unbox_s" 1 1 "mk_unbox"))
in (let _64_32 = (FStar_Util.smap_add wys_lib_args_map "box" (to_wys_lib_fn "box" 0 2 "mk_box"))
in (let _64_34 = (FStar_Util.smap_add wys_lib_args_map "mkwire_p" (to_wys_lib_fn "mkwire_p" 1 2 "mk_mkwire"))
in (let _64_36 = (FStar_Util.smap_add wys_lib_args_map "mkwire_s" (to_wys_lib_fn "mkwire_s" 0 2 "mk_mkwire"))
in (let _64_38 = (FStar_Util.smap_add wys_lib_args_map "projwire_p" (to_wys_lib_fn "projwire_p" 1 2 "mk_projwire"))
in (let _64_40 = (FStar_Util.smap_add wys_lib_args_map "projwire_s" (to_wys_lib_fn "projwire_s" 1 2 "mk_projwire"))
in (let _64_42 = (FStar_Util.smap_add wys_lib_args_map "concat_wire" (to_wys_lib_fn "concat_wire" 2 2 "mk_concatwire"))
in (let _64_44 = (FStar_Util.smap_add prims_trans_map "Prims.op_Multiply" "Prims.( * )")
in (let _64_46 = (FStar_Util.smap_add prims_trans_map "Prims.op_Subtraction" "Prims.(-)")
in (let _64_48 = (FStar_Util.smap_add prims_trans_map "Prims.op_Addition" "Prims.(+)")
in (let _64_50 = (FStar_Util.smap_add prims_trans_map "Prims.op_LessThanOrEqual" "Prims.(<=)")
in (let _64_52 = (FStar_Util.smap_add prims_trans_map "Prims.op_GreaterThan" "Prims.(>)")
in (let _64_54 = (FStar_Util.smap_add prims_trans_map "Prims.op_GreaterThanOrEqual" "Prims.(>=)")
in (let _64_56 = (FStar_Util.smap_add prims_trans_map "Prims.op_LessThan" "Prims.(<)")
in (let _64_58 = (FStar_Util.smap_add prims_trans_map "Prims.op_Modulus" "Prims.(%)")
in ()))))))))))))))))))))))))

let lookup_ffi_map = (fun t -> (let m = (FStar_Util.smap_try_find fn_map t)
in (match (m) with
| Some (m) -> begin
m
end
| _64_65 -> begin
(FStar_All.failwith (Prims.strcat "Unknown user type: " t))
end)))

let lookup_wys_lib_map = (fun s -> (match ((FStar_Util.smap_try_find wys_lib_args_map s)) with
| Some (x) -> begin
x
end
| _64_70 -> begin
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
(let _130_46 = (let _130_45 = (FStar_Util.string_of_int (FStar_List.length l))
in (let _130_44 = (FStar_Util.string_of_int n)
in (FStar_Util.format3 "Error removing arguments in sublist for %s, list len is %s, n is %s " s _130_45 _130_44)))
in (FStar_All.failwith _130_46))
end else begin
if (n = 0) then begin
l
end else begin
(let _130_47 = (FStar_List.tl l)
in (sublist s _130_47 (n - 1)))
end
end)

let is_bool = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named (_64_81, p) -> begin
((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "Prims.bool")
end
| _64_86 -> begin
false
end))

let is_unit = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named (_64_89, p) -> begin
((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "Prims.unit")
end
| _64_94 -> begin
false
end))

let is_prin = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named (_64_97, p) -> begin
((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "Prins.prin")
end
| _64_102 -> begin
false
end))

let is_prins = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named (_64_105, p) -> begin
((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "Prins.prins")
end
| _64_110 -> begin
false
end))

let is_eprins = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named (_64_113, p) -> begin
((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "Prins.eprins")
end
| _64_118 -> begin
false
end))

let is_box = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named (_64_121, p) -> begin
((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "Wysteria.Box")
end
| _64_126 -> begin
false
end))

let is_wire = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named (_64_129, p) -> begin
((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "Wysteria.Wire")
end
| _64_134 -> begin
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
| _64_141 -> begin
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
| _64_148 -> begin
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
(let _64_162 = (get_opaque_fns (FStar_Extraction_ML_Syntax.MLTY_Named (([], p))))
in (match (_64_162) with
| (e1, e2, e3) -> begin
(FStar_List.fold_left (fun _64_166 arg -> (match (_64_166) with
| (a1, a2, a3) -> begin
(match (arg) with
| FStar_Extraction_ML_Syntax.MLTY_Named (_64_169) -> begin
(let _64_174 = (get_opaque_fns arg)
in (match (_64_174) with
| (e1_arg, e2_arg, e3_arg) -> begin
((Prims.strcat (Prims.strcat (Prims.strcat (Prims.strcat "(" a1) " ") e1_arg) ")"), (Prims.strcat (Prims.strcat (Prims.strcat (Prims.strcat "(" a2) " ") e2_arg) ")"), (Prims.strcat (Prims.strcat (Prims.strcat (Prims.strcat "(" a3) " ") e3_arg) ")"))
end))
end
| _64_176 -> begin
(FStar_All.failwith "Did not expect type argument to be something other than named type")
end)
end)) (e1, e2, e3) args)
end))
end
| _64_178 -> begin
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
(let _64_184 = (get_opaque_fns t)
in (match (_64_184) with
| (s1, s2, s3) -> begin
(Prims.strcat (Prims.strcat (Prims.strcat (Prims.strcat (Prims.strcat "mk_v_opaque x " s1) " ") s2) " ") s3)
end))
end
end
end
end
end
in (Prims.strcat s s'))))

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
(let _130_80 = (let _130_79 = (let _130_78 = (box_content_type t)
in (mlty_to_typ _130_78))
in (Prims.strcat "T_box (" _130_79))
in (Prims.strcat _130_80 ")"))
end else begin
if (is_wire t) then begin
(let _130_83 = (let _130_82 = (let _130_81 = (wire_content_type t)
in (mlty_to_typ _130_81))
in (Prims.strcat "T_wire (" _130_82))
in (Prims.strcat _130_83 ")"))
end else begin
(match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named (l, p) -> begin
(let n = (Prims.strcat "T_cons (" (name_to_string (FStar_Extraction_ML_Syntax.string_of_mlpath p)))
in (let args = (FStar_List.fold_left (fun s a -> (let _130_87 = (let _130_86 = (mlty_to_typ a)
in (Prims.strcat (Prims.strcat s " (") _130_86))
in (Prims.strcat _130_87 ");"))) "" l)
in (Prims.strcat (Prims.strcat (Prims.strcat n ", [") args) "])")))
end
| _64_197 -> begin
"T_unknown"
end)
end
end
end
end
end
end)

let is_ffi = (fun _64_200 -> (match (_64_200) with
| {FStar_Extraction_ML_Syntax.expr = e; FStar_Extraction_ML_Syntax.ty = t} -> begin
(match (e) with
| FStar_Extraction_ML_Syntax.MLE_Name (p, n) -> begin
(let _130_90 = (translate_ffi_name (FStar_Extraction_ML_Syntax.string_of_mlpath (p, n)))
in (((p = ("FFI")::[]) || (p = ("Prims")::[])), _130_90))
end
| _64_206 -> begin
(false, "")
end)
end))

let tag_of_mlconst = (fun c -> (match (c) with
| FStar_Extraction_ML_Syntax.MLC_Unit -> begin
"MLC_Unit"
end
| FStar_Extraction_ML_Syntax.MLC_Bool (_64_210) -> begin
"MLC_Bool"
end
| FStar_Extraction_ML_Syntax.MLC_Char (_64_213) -> begin
"MLC_Char"
end
| FStar_Extraction_ML_Syntax.MLC_Byte (_64_216) -> begin
"MLC_Byte"
end
| FStar_Extraction_ML_Syntax.MLC_Int32 (_64_219) -> begin
"MLC_Int32"
end
| FStar_Extraction_ML_Syntax.MLC_Int64 (_64_222) -> begin
"MLC_Int64"
end
| FStar_Extraction_ML_Syntax.MLC_Int (_64_225) -> begin
"MLC_Int"
end
| FStar_Extraction_ML_Syntax.MLC_Float (_64_228) -> begin
"MLC_Float"
end
| FStar_Extraction_ML_Syntax.MLC_Bytes (_64_231) -> begin
"MLC_Bytes"
end
| FStar_Extraction_ML_Syntax.MLC_String (_64_234) -> begin
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
(Prims.strcat (Prims.strcat "C_opaque ((), Obj.magic " (FStar_Util.string_of_int32 n)) ")")
end
| FStar_Extraction_ML_Syntax.MLC_Int64 (n) -> begin
(Prims.strcat (Prims.strcat "C_opaque ((), Obj.magic " (FStar_Util.string_of_int64 n)) ")")
end
| FStar_Extraction_ML_Syntax.MLC_Int (x) -> begin
(Prims.strcat (Prims.strcat "C_opaque ((), Obj.magic " x) ")")
end
| FStar_Extraction_ML_Syntax.MLC_String (s) -> begin
(Prims.strcat (Prims.strcat "C_opaque ((), Obj.magic (\"" s) "\"))")
end
| _64_249 -> begin
(FStar_All.failwith (Prims.strcat "Unsupported constant: tag: " (tag_of_mlconst c)))
end))

let is_wys_lib_fn = (fun _64_252 -> (match (_64_252) with
| {FStar_Extraction_ML_Syntax.expr = e; FStar_Extraction_ML_Syntax.ty = t} -> begin
(match (e) with
| FStar_Extraction_ML_Syntax.MLE_Name (p) -> begin
(FStar_Util.starts_with (FStar_Extraction_ML_Syntax.string_of_mlpath p) "Wysteria")
end
| _64_256 -> begin
false
end)
end))

let check_pats_for_bool = (fun l -> (let def = (false, FStar_Extraction_ML_Syntax.ml_unit, FStar_Extraction_ML_Syntax.ml_unit)
in if ((FStar_List.length l) <> 2) then begin
def
end else begin
(let _64_263 = (FStar_List.hd l)
in (match (_64_263) with
| (p1, _64_261, e1) -> begin
(let _64_268 = (let _130_99 = (FStar_List.tl l)
in (FStar_List.hd _130_99))
in (match (_64_268) with
| (p2, _64_266, e2) -> begin
(match ((p1, p2)) with
| (FStar_Extraction_ML_Syntax.MLP_Const (FStar_Extraction_ML_Syntax.MLC_Bool (_64_270)), FStar_Extraction_ML_Syntax.MLP_Const (FStar_Extraction_ML_Syntax.MLC_Bool (_64_274))) -> begin
(true, e1, e2)
end
| _64_279 -> begin
def
end)
end))
end))
end))

let mk_var = (fun s t -> (let _130_105 = (let _130_104 = (mlty_to_typ t)
in (Prims.strcat (Prims.strcat (Prims.strcat "mk_var " (name_to_string s)) " (") _130_104))
in (Prims.strcat _130_105 ")")))

let mk_varname = (fun s t -> (let _130_111 = (let _130_110 = (mlty_to_typ t)
in (Prims.strcat (Prims.strcat (Prims.strcat "mk_varname " (name_to_string s)) " (") _130_110))
in (Prims.strcat _130_111 ")")))

let rec extract_mlexp = (fun _64_286 -> (match (_64_286) with
| {FStar_Extraction_ML_Syntax.expr = e; FStar_Extraction_ML_Syntax.ty = t} -> begin
(match (e) with
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(let _130_118 = (let _130_117 = (extract_mlconst c)
in (Prims.strcat "mk_const (" _130_117))
in (Prims.strcat _130_118 ")"))
end
| FStar_Extraction_ML_Syntax.MLE_Var (x) -> begin
(mk_var (FStar_Extraction_ML_Syntax.idsym x) t)
end
| FStar_Extraction_ML_Syntax.MLE_Name (p, s) -> begin
(let ss = (FStar_Extraction_ML_Syntax.string_of_mlpath (p, s))
in (let _64_296 = if (not ((FStar_Util.starts_with ss "SMC."))) then begin
(let _130_119 = (FStar_Util.format1 "Warning: name not applied: %s\n" (FStar_Extraction_ML_Syntax.string_of_mlpath (p, s)))
in (FStar_Util.print_string _130_119))
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
in (let _130_127 = (let _130_126 = (let _130_124 = (let _130_123 = (let _130_121 = (let _130_120 = (mk_varname lbname lbbody.FStar_Extraction_ML_Syntax.ty)
in (Prims.strcat "mk_let (" _130_120))
in (Prims.strcat _130_121 ") ("))
in (let _130_122 = (extract_mlexp lbbody)
in (Prims.strcat _130_123 _130_122)))
in (Prims.strcat _130_124 ") ("))
in (let _130_125 = (extract_mlexp e')
in (Prims.strcat _130_126 _130_125)))
in (Prims.strcat _130_127 ")")))))
end
end
| FStar_Extraction_ML_Syntax.MLE_App (f, args) -> begin
(let _64_313 = (is_ffi f)
in (match (_64_313) with
| (b, ffi) -> begin
if b then begin
(let inj = (get_injection t)
in (let args_exp = (FStar_List.fold_left (fun s a -> (let _130_131 = (let _130_130 = (extract_mlexp a)
in (Prims.strcat (Prims.strcat s " (") _130_130))
in (Prims.strcat _130_131 ");"))) "" args)
in (let _130_141 = (let _130_140 = (let _130_139 = (let _130_138 = (let _130_137 = (let _130_136 = (let _130_135 = (let _130_134 = (let _130_133 = (let _130_132 = (FStar_Util.string_of_int (FStar_List.length args))
in (Prims.strcat "mk_ffi " _130_132))
in (Prims.strcat _130_133 " "))
in (Prims.strcat _130_134 (name_to_string ffi)))
in (Prims.strcat _130_135 " ("))
in (Prims.strcat _130_136 ffi))
in (Prims.strcat _130_137 ") [ "))
in (Prims.strcat _130_138 args_exp))
in (Prims.strcat _130_139 " ] ("))
in (Prims.strcat _130_140 inj))
in (Prims.strcat _130_141 ")"))))
end else begin
if (is_wys_lib_fn f) then begin
(extract_wysteria_specific_ast f args t)
end else begin
(let s = (extract_mlexp f)
in if (s = "_assert") then begin
"mk_const (C_unit ())"
end else begin
(FStar_List.fold_left (fun s a -> (let _130_145 = (let _130_144 = (extract_mlexp a)
in (Prims.strcat (Prims.strcat (Prims.strcat "mk_app (" s) ") (") _130_144))
in (Prims.strcat _130_145 ")"))) s args)
end)
end
end
end))
end
| FStar_Extraction_ML_Syntax.MLE_Fun (bs, body) -> begin
(let body_str = (extract_mlexp body)
in (FStar_List.fold_left (fun s _64_332 -> (match (_64_332) with
| ((b, _64_329), t) -> begin
(let _130_151 = (let _130_150 = (let _130_149 = (let _130_148 = (mk_varname b t)
in (Prims.strcat "mk_abs (" _130_148))
in (Prims.strcat _130_149 ") ("))
in (Prims.strcat _130_150 s))
in (Prims.strcat _130_151 ")"))
end)) body_str (FStar_List.rev bs)))
end
| FStar_Extraction_ML_Syntax.MLE_Match (e, bs) -> begin
(let _64_340 = (check_pats_for_bool bs)
in (match (_64_340) with
| (b, e1, e2) -> begin
if b then begin
(let _130_159 = (let _130_158 = (let _130_156 = (let _130_155 = (let _130_153 = (let _130_152 = (extract_mlexp e)
in (Prims.strcat "mk_cond (" _130_152))
in (Prims.strcat _130_153 ") ("))
in (let _130_154 = (extract_mlexp e1)
in (Prims.strcat _130_155 _130_154)))
in (Prims.strcat _130_156 ") ("))
in (let _130_157 = (extract_mlexp e2)
in (Prims.strcat _130_158 _130_157)))
in (Prims.strcat _130_159 ")"))
end else begin
(FStar_All.failwith "Only if-then-else patterns are supported")
end
end))
end
| FStar_Extraction_ML_Syntax.MLE_Coerce (e, _64_343, _64_345) -> begin
(extract_mlexp e)
end
| FStar_Extraction_ML_Syntax.MLE_If (e, e1, e2_opt) -> begin
(match (e2_opt) with
| None -> begin
(FStar_All.failwith "If Then Else should have an else branch?")
end
| Some (e2) -> begin
(let _130_167 = (let _130_166 = (let _130_164 = (let _130_163 = (let _130_161 = (let _130_160 = (extract_mlexp e)
in (Prims.strcat "mk_cond (" _130_160))
in (Prims.strcat _130_161 ") ("))
in (let _130_162 = (extract_mlexp e1)
in (Prims.strcat _130_163 _130_162)))
in (Prims.strcat _130_164 ") ("))
in (let _130_165 = (extract_mlexp e2)
in (Prims.strcat _130_166 _130_165)))
in (Prims.strcat _130_167 ")"))
end)
end
| _64_357 -> begin
(FStar_All.failwith "This expression extraction is not supported yet")
end)
end))
and extract_wysteria_specific_ast = (fun _64_361 args t -> (match (_64_361) with
| {FStar_Extraction_ML_Syntax.expr = f; FStar_Extraction_ML_Syntax.ty = _64_359} -> begin
(match (f) with
| FStar_Extraction_ML_Syntax.MLE_Name (_64_365, s) -> begin
if (s = "main") then begin
(let f = (let _130_171 = (FStar_List.tl args)
in (FStar_List.hd _130_171))
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
in (FStar_List.fold_left (fun acc arg -> (let _130_175 = (let _130_174 = (extract_mlexp arg)
in (Prims.strcat (Prims.strcat acc " (") _130_174))
in (Prims.strcat _130_175 ")"))) r.extracted_fn_name args)))
end
end
end
end
end
| _64_379 -> begin
(FStar_All.failwith "Expected wysteria lib fn to be a MLE_Name")
end)
end))

let extract_mllb = (fun _64_382 -> (match (_64_382) with
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
(let _64_392 = (let _130_179 = (FStar_List.hd bs)
in (let _130_178 = (FStar_List.tl bs)
in (_130_179, _130_178)))
in (match (_64_392) with
| (first_b, rest_bs) -> begin
(let body_exp = (extract_mlexp e)
in (let tl_abs_exp = (FStar_List.fold_left (fun e _64_397 -> (match (_64_397) with
| (bname, btyp) -> begin
(let _130_185 = (let _130_184 = (let _130_183 = (let _130_182 = (mk_varname (FStar_Extraction_ML_Syntax.idsym bname) btyp)
in (Prims.strcat "mk_abs (" _130_182))
in (Prims.strcat _130_183 ") ("))
in (Prims.strcat _130_184 e))
in (Prims.strcat _130_185 ")"))
end)) body_exp (FStar_List.rev rest_bs))
in (let fix_exp = (let _130_192 = (let _130_191 = (let _130_190 = (let _130_189 = (let _130_187 = (let _130_186 = (mk_varname lbname lbbody.FStar_Extraction_ML_Syntax.ty)
in (Prims.strcat "mk_fix (" _130_186))
in (Prims.strcat _130_187 ") ("))
in (let _130_188 = (mk_varname (FStar_Extraction_ML_Syntax.idsym (Prims.fst first_b)) (Prims.snd first_b))
in (Prims.strcat _130_189 _130_188)))
in (Prims.strcat _130_190 ") ("))
in (Prims.strcat _130_191 tl_abs_exp))
in (Prims.strcat _130_192 ")"))
in (let _130_194 = (let _130_193 = (mlty_to_typ lbbody.FStar_Extraction_ML_Syntax.ty)
in (lbname, _130_193, fix_exp))
in Mk_tlet (_130_194)))))
end))
end
| _64_401 -> begin
(FStar_All.failwith "Recursive let binding is not an abstraction ?")
end)
end else begin
(let _130_197 = (let _130_196 = (mlty_to_typ lbbody.FStar_Extraction_ML_Syntax.ty)
in (let _130_195 = (extract_mlexp lbbody)
in (lbname, _130_196, _130_195)))
in Mk_tlet (_130_197))
end)))
end
end))

let extract_mlmodule = (fun m -> (FStar_List.fold_left (fun _64_405 tld -> (match (_64_405) with
| (l, top_opt) -> begin
(match (tld) with
| FStar_Extraction_ML_Syntax.MLM_Ty (_64_408) -> begin
(l, top_opt)
end
| FStar_Extraction_ML_Syntax.MLM_Exn (_64_411) -> begin
(FStar_All.failwith "Cannot extract an exception")
end
| FStar_Extraction_ML_Syntax.MLM_Let (lb) -> begin
(let _130_204 = (let _130_203 = (let _130_202 = (extract_mllb lb)
in (_130_202)::[])
in (FStar_List.append l _130_203))
in (_130_204, top_opt))
end
| FStar_Extraction_ML_Syntax.MLM_Top (e) -> begin
(match (top_opt) with
| None -> begin
(let _130_206 = (let _130_205 = (extract_mlexp e)
in Some (_130_205))
in (l, _130_206))
end
| Some (_64_419) -> begin
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
| Some (_64_433, m) -> begin
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
(Prims.raise (FStar_Util.NYI ("Cannot find the SMC module")))
end
| FStar_Extraction_ML_Syntax.MLLib (s)::tl -> begin
(let m_opt = (find_smc_module' s)
in (match (m_opt) with
| Some (m) -> begin
m
end
| None -> begin
(find_smc_module tl)
end))
end)))

let extract = (fun l en -> (let _64_453 = (initialize ())
in (let _64_457 = (let _130_215 = (FStar_Extraction_ML_Env.mkContext en)
in (FStar_Util.fold_map FStar_Extraction_ML_ExtractMod.extract _130_215 l))
in (match (_64_457) with
| (c, mllibs) -> begin
(let mllibs = (FStar_List.flatten mllibs)
in (let m = (find_smc_module mllibs)
in (let _64_462 = (extract_mlmodule m)
in (match (_64_462) with
| (l, m_opt) -> begin
(match (m_opt) with
| None -> begin
(FStar_All.failwith "End of SMC module, no top level expression")
end
| Some (m) -> begin
(let s = (FStar_List.fold_left (fun acc _64_471 -> (match (_64_471) with
| Mk_tlet (n, t, b) -> begin
(Prims.strcat (Prims.strcat (Prims.strcat (Prims.strcat (Prims.strcat (Prims.strcat (Prims.strcat (Prims.strcat "mk_let (mk_varname " (name_to_string n)) " (") t) ")) (") b) ") (") acc) ")")
end)) m (FStar_List.rev l))
in (let _64_473 = (FStar_Util.print_string s)
in (FStar_Util.print_string "\n")))
end)
end))))
end))))




