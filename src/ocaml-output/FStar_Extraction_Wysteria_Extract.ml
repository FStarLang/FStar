
open Prims
# 28 "FStar.Extraction.Wysteria.Extract.fst"
type name =
Prims.string

# 30 "FStar.Extraction.Wysteria.Extract.fst"
type wexp =
Prims.string

# 32 "FStar.Extraction.Wysteria.Extract.fst"
type wtyp =
Prims.string

# 34 "FStar.Extraction.Wysteria.Extract.fst"
type tlet =
| Mk_tlet of (name * wtyp * wexp)

# 35 "FStar.Extraction.Wysteria.Extract.fst"
let is_Mk_tlet = (fun _discr_ -> (match (_discr_) with
| Mk_tlet (_) -> begin
true
end
| _ -> begin
false
end))

# 35 "FStar.Extraction.Wysteria.Extract.fst"
let ___Mk_tlet____0 : tlet  ->  (name * wtyp * wexp) = (fun projectee -> (match (projectee) with
| Mk_tlet (_64_2) -> begin
_64_2
end))

# 37 "FStar.Extraction.Wysteria.Extract.fst"
let fn_map : (wexp * wexp * wexp) FStar_Util.smap = (FStar_Util.smap_create 10)

# 39 "FStar.Extraction.Wysteria.Extract.fst"
type wys_lib_fn =
{fn_name : Prims.string; rem_args : Prims.int; arity : Prims.int; extracted_fn_name : Prims.string}

# 39 "FStar.Extraction.Wysteria.Extract.fst"
let is_Mkwys_lib_fn : wys_lib_fn  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkwys_lib_fn"))))

# 46 "FStar.Extraction.Wysteria.Extract.fst"
let to_wys_lib_fn : Prims.string  ->  Prims.int  ->  Prims.int  ->  Prims.string  ->  wys_lib_fn = (fun s1 n1 n2 s2 -> {fn_name = s1; rem_args = n1; arity = n2; extracted_fn_name = s2})

# 48 "FStar.Extraction.Wysteria.Extract.fst"
let wys_lib_args_map : wys_lib_fn FStar_Util.smap = (FStar_Util.smap_create 10)

# 50 "FStar.Extraction.Wysteria.Extract.fst"
let prims_trans_map : Prims.string FStar_Util.smap = (FStar_Util.smap_create 10)

# 52 "FStar.Extraction.Wysteria.Extract.fst"
let slice_id : Prims.string = "slice_id"

# 53 "FStar.Extraction.Wysteria.Extract.fst"
let compose_ids : Prims.string = "compose_ids"

# 54 "FStar.Extraction.Wysteria.Extract.fst"
let slice_id_sps : Prims.string = "slice_id_sps"

# 56 "FStar.Extraction.Wysteria.Extract.fst"
let initialize : Prims.unit  ->  Prims.unit = (fun _64_12 -> (
# 57 "FStar.Extraction.Wysteria.Extract.fst"
let _64_14 = (FStar_Util.smap_add fn_map "Prims.int" (slice_id, compose_ids, slice_id_sps))
in (
# 58 "FStar.Extraction.Wysteria.Extract.fst"
let _64_16 = (FStar_Util.smap_add fn_map "Prims.nat" (slice_id, compose_ids, slice_id_sps))
in (
# 59 "FStar.Extraction.Wysteria.Extract.fst"
let _64_18 = (FStar_Util.smap_add fn_map "Prims.list" ("slice_list", "compose_lists", "slice_list_sps"))
in (
# 60 "FStar.Extraction.Wysteria.Extract.fst"
let _64_20 = (FStar_Util.smap_add fn_map "Prims.option" ("slice_option", "compose_options", "slice_option_sps"))
in (
# 61 "FStar.Extraction.Wysteria.Extract.fst"
let _64_22 = (FStar_Util.smap_add fn_map "Prims.Tuple2" ("slice_tuple", "compose_tuples", "slice_tuple_sps"))
in (
# 63 "FStar.Extraction.Wysteria.Extract.fst"
let _64_24 = (FStar_Util.smap_add wys_lib_args_map "as_par" (to_wys_lib_fn "as_par" 0 2 "mk_aspar"))
in (
# 64 "FStar.Extraction.Wysteria.Extract.fst"
let _64_26 = (FStar_Util.smap_add wys_lib_args_map "as_sec" (to_wys_lib_fn "as_sec" 0 2 "mk_assec"))
in (
# 65 "FStar.Extraction.Wysteria.Extract.fst"
let _64_28 = (FStar_Util.smap_add wys_lib_args_map "unbox_p" (to_wys_lib_fn "unbox_p" 1 1 "mk_unbox"))
in (
# 66 "FStar.Extraction.Wysteria.Extract.fst"
let _64_30 = (FStar_Util.smap_add wys_lib_args_map "unbox_s" (to_wys_lib_fn "unbox_s" 1 1 "mk_unbox"))
in (
# 67 "FStar.Extraction.Wysteria.Extract.fst"
let _64_32 = (FStar_Util.smap_add wys_lib_args_map "box" (to_wys_lib_fn "box" 0 2 "mk_box"))
in (
# 68 "FStar.Extraction.Wysteria.Extract.fst"
let _64_34 = (FStar_Util.smap_add wys_lib_args_map "mkwire_p" (to_wys_lib_fn "mkwire_p" 1 2 "mk_mkwire"))
in (
# 69 "FStar.Extraction.Wysteria.Extract.fst"
let _64_36 = (FStar_Util.smap_add wys_lib_args_map "mkwire_s" (to_wys_lib_fn "mkwire_s" 0 2 "mk_mkwire"))
in (
# 70 "FStar.Extraction.Wysteria.Extract.fst"
let _64_38 = (FStar_Util.smap_add wys_lib_args_map "projwire_p" (to_wys_lib_fn "projwire_p" 1 2 "mk_projwire"))
in (
# 71 "FStar.Extraction.Wysteria.Extract.fst"
let _64_40 = (FStar_Util.smap_add wys_lib_args_map "projwire_s" (to_wys_lib_fn "projwire_s" 1 2 "mk_projwire"))
in (
# 72 "FStar.Extraction.Wysteria.Extract.fst"
let _64_42 = (FStar_Util.smap_add wys_lib_args_map "concat_wire" (to_wys_lib_fn "concat_wire" 2 2 "mk_concatwire"))
in (
# 73 "FStar.Extraction.Wysteria.Extract.fst"
let _64_44 = (FStar_Util.smap_add wys_lib_args_map "mk_sh" (to_wys_lib_fn "mk_sh" 0 1 "mk_mksh"))
in (
# 74 "FStar.Extraction.Wysteria.Extract.fst"
let _64_46 = (FStar_Util.smap_add wys_lib_args_map "comb_sh" (to_wys_lib_fn "comb_sh" 0 1 "mk_combsh"))
in (
# 76 "FStar.Extraction.Wysteria.Extract.fst"
let _64_48 = (FStar_Util.smap_add prims_trans_map "Prims.op_Multiply" "Prims.( * )")
in (
# 77 "FStar.Extraction.Wysteria.Extract.fst"
let _64_50 = (FStar_Util.smap_add prims_trans_map "Prims.op_Subtraction" "Prims.(-)")
in (
# 78 "FStar.Extraction.Wysteria.Extract.fst"
let _64_52 = (FStar_Util.smap_add prims_trans_map "Prims.op_Addition" "Prims.(+)")
in (
# 79 "FStar.Extraction.Wysteria.Extract.fst"
let _64_54 = (FStar_Util.smap_add prims_trans_map "Prims.op_LessThanOrEqual" "Prims.(<=)")
in (
# 80 "FStar.Extraction.Wysteria.Extract.fst"
let _64_56 = (FStar_Util.smap_add prims_trans_map "Prims.op_GreaterThan" "Prims.(>)")
in (
# 81 "FStar.Extraction.Wysteria.Extract.fst"
let _64_58 = (FStar_Util.smap_add prims_trans_map "Prims.op_GreaterThanOrEqual" "Prims.(>=)")
in (
# 82 "FStar.Extraction.Wysteria.Extract.fst"
let _64_60 = (FStar_Util.smap_add prims_trans_map "Prims.op_LessThan" "Prims.(<)")
in (
# 83 "FStar.Extraction.Wysteria.Extract.fst"
let _64_62 = (FStar_Util.smap_add prims_trans_map "Prims.op_Modulus" "Prims.(%)")
in ()))))))))))))))))))))))))))

# 87 "FStar.Extraction.Wysteria.Extract.fst"
let lookup_ffi_map : Prims.string  ->  (wexp * wexp * wexp) = (fun t -> (
# 88 "FStar.Extraction.Wysteria.Extract.fst"
let m = (FStar_Util.smap_try_find fn_map t)
in (match (m) with
| Some (m) -> begin
m
end
| _64_69 -> begin
(FStar_All.failwith (Prims.strcat "Unknown user type: " t))
end)))

# 93 "FStar.Extraction.Wysteria.Extract.fst"
let lookup_wys_lib_map : Prims.string  ->  wys_lib_fn = (fun s -> (match ((FStar_Util.smap_try_find wys_lib_args_map s)) with
| Some (x) -> begin
x
end
| _64_74 -> begin
(FStar_All.failwith "Unknown wysteria library function")
end))

# 98 "FStar.Extraction.Wysteria.Extract.fst"
let translate_ffi_name : Prims.string  ->  Prims.string = (fun s -> (match ((FStar_Util.smap_try_find prims_trans_map s)) with
| Some (x) -> begin
x
end
| None -> begin
s
end))

# 103 "FStar.Extraction.Wysteria.Extract.fst"
let rec sublist = (fun s l n -> if (n > (FStar_List.length l)) then begin
(let _146_46 = (let _146_45 = (FStar_Util.string_of_int (FStar_List.length l))
in (let _146_44 = (FStar_Util.string_of_int n)
in (FStar_Util.format3 "Error removing arguments in sublist for %s, list len is %s, n is %s " s _146_45 _146_44)))
in (FStar_All.failwith _146_46))
end else begin
if (n = 0) then begin
l
end else begin
(let _146_47 = (FStar_List.tl l)
in (sublist s _146_47 (n - 1)))
end
end)

# 108 "FStar.Extraction.Wysteria.Extract.fst"
let is_bool : FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named (_64_85, p) -> begin
((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "Prims.bool")
end
| _64_90 -> begin
false
end))

# 113 "FStar.Extraction.Wysteria.Extract.fst"
let is_int : FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named (_64_93, p) -> begin
((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "Prims.int")
end
| _64_98 -> begin
false
end))

# 118 "FStar.Extraction.Wysteria.Extract.fst"
let is_unit : FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named (_64_101, p) -> begin
((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "Prims.unit")
end
| _64_106 -> begin
false
end))

# 123 "FStar.Extraction.Wysteria.Extract.fst"
let is_prin : FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named (_64_109, p) -> begin
((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "Prins.prin")
end
| _64_114 -> begin
false
end))

# 128 "FStar.Extraction.Wysteria.Extract.fst"
let is_prins : FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named (_64_117, p) -> begin
((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "Prins.prins")
end
| _64_122 -> begin
false
end))

# 133 "FStar.Extraction.Wysteria.Extract.fst"
let is_eprins : FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named (_64_125, p) -> begin
((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "Prins.eprins")
end
| _64_130 -> begin
false
end))

# 138 "FStar.Extraction.Wysteria.Extract.fst"
let is_box : FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named (_64_133, p) -> begin
((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "Wysteria.Box")
end
| _64_138 -> begin
false
end))

# 143 "FStar.Extraction.Wysteria.Extract.fst"
let is_wire : FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named (_64_141, p) -> begin
((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "Wysteria.Wire")
end
| _64_146 -> begin
false
end))

# 148 "FStar.Extraction.Wysteria.Extract.fst"
let is_share : FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named (_64_149, p) -> begin
((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "Wysteria.Sh")
end
| _64_154 -> begin
false
end))

# 153 "FStar.Extraction.Wysteria.Extract.fst"
let box_content_type : FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named (l, p) -> begin
if ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "Wysteria.Box") then begin
(FStar_List.hd l)
end else begin
(FStar_All.failwith "Cannot get content for non box named type")
end
end
| _64_161 -> begin
(FStar_All.failwith "Cannot get content for non-named type")
end))

# 160 "FStar.Extraction.Wysteria.Extract.fst"
let wire_content_type : FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named (l, p) -> begin
if ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "Wysteria.Wire") then begin
(FStar_List.hd l)
end else begin
(FStar_All.failwith "Cannot get content for non wire named type")
end
end
| _64_168 -> begin
(FStar_All.failwith "Cannot get content for non-named type")
end))

# 167 "FStar.Extraction.Wysteria.Extract.fst"
let is_wysteria_type : FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun t -> ((((((is_prin t) || (is_prins t)) || (is_eprins t)) || (is_box t)) || (is_wire t)) || (is_share t)))

# 169 "FStar.Extraction.Wysteria.Extract.fst"
let slice_value : Prims.string = "Semantics.slice_v_ffi"

# 170 "FStar.Extraction.Wysteria.Extract.fst"
let slice_value_sps : Prims.string = "Semantics.slice_v_sps_ffi"

# 171 "FStar.Extraction.Wysteria.Extract.fst"
let compose_values : Prims.string = "Semantics.compose_vals_ffi"

# 173 "FStar.Extraction.Wysteria.Extract.fst"
let rec get_opaque_fns : FStar_Extraction_ML_Syntax.mlty  ->  (wexp * wexp * wexp) = (fun t -> if (((((is_bool t) || (is_unit t)) || (is_prin t)) || (is_prins t)) || (is_eprins t)) then begin
(slice_id, compose_ids, slice_id_sps)
end else begin
if (((is_box t) || (is_wire t)) || (is_share t)) then begin
(slice_value, compose_values, slice_value_sps)
end else begin
(match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) -> begin
(lookup_ffi_map (FStar_Extraction_ML_Syntax.string_of_mlpath p))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, p) -> begin
(
# 180 "FStar.Extraction.Wysteria.Extract.fst"
let _64_182 = (get_opaque_fns (FStar_Extraction_ML_Syntax.MLTY_Named (([], p))))
in (match (_64_182) with
| (e1, e2, e3) -> begin
(FStar_List.fold_left (fun _64_186 arg -> (match (_64_186) with
| (a1, a2, a3) -> begin
(match (arg) with
| FStar_Extraction_ML_Syntax.MLTY_Named (_64_189) -> begin
(
# 184 "FStar.Extraction.Wysteria.Extract.fst"
let _64_194 = (get_opaque_fns arg)
in (match (_64_194) with
| (e1_arg, e2_arg, e3_arg) -> begin
((Prims.strcat (Prims.strcat (Prims.strcat (Prims.strcat "(" a1) " ") e1_arg) ")"), (Prims.strcat (Prims.strcat (Prims.strcat (Prims.strcat "(" a2) " ") e2_arg) ")"), (Prims.strcat (Prims.strcat (Prims.strcat (Prims.strcat "(" a3) " ") e3_arg) ")"))
end))
end
| _64_196 -> begin
(FStar_All.failwith "Did not expect type argument to be something other than named type")
end)
end)) (e1, e2, e3) args)
end))
end
| _64_198 -> begin
(FStar_All.failwith "Did not expect a non named type in get_opaque_fns")
end)
end
end)

# 190 "FStar.Extraction.Wysteria.Extract.fst"
let get_injection : FStar_Extraction_ML_Syntax.mlty  ->  Prims.string = (fun t -> (
# 191 "FStar.Extraction.Wysteria.Extract.fst"
let s = "fun x -> "
in (
# 192 "FStar.Extraction.Wysteria.Extract.fst"
let s' = if (is_bool t) then begin
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
if (((is_box t) || (is_wire t)) || (is_share t)) then begin
"x"
end else begin
(
# 199 "FStar.Extraction.Wysteria.Extract.fst"
let _64_204 = (get_opaque_fns t)
in (match (_64_204) with
| (s1, s2, s3) -> begin
(Prims.strcat (Prims.strcat (Prims.strcat (Prims.strcat (Prims.strcat "mk_v_opaque x " s1) " ") s2) " ") s3)
end))
end
end
end
end
end
in (Prims.strcat s s'))))

# 204 "FStar.Extraction.Wysteria.Extract.fst"
let is_known_named_type : FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named (_64_208, p) -> begin
(
# 207 "FStar.Extraction.Wysteria.Extract.fst"
let s_opt = (FStar_Util.smap_try_find fn_map (FStar_Extraction_ML_Syntax.string_of_mlpath p))
in if (s_opt = None) then begin
false
end else begin
true
end)
end
| _64_214 -> begin
(FStar_All.failwith "Is_known_named_type was not called with a named type")
end))

# 211 "FStar.Extraction.Wysteria.Extract.fst"
let name_to_string : name  ->  Prims.string = (fun s -> (Prims.strcat (Prims.strcat "\"" s) "\""))

# 213 "FStar.Extraction.Wysteria.Extract.fst"
let rec mlty_to_typ : FStar_Extraction_ML_Syntax.mlty  ->  Prims.string = (fun t -> if (is_bool t) then begin
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
(let _146_86 = (let _146_85 = (let _146_84 = (box_content_type t)
in (mlty_to_typ _146_84))
in (Prims.strcat "T_box (" _146_85))
in (Prims.strcat _146_86 ")"))
end else begin
if (is_wire t) then begin
(let _146_89 = (let _146_88 = (let _146_87 = (wire_content_type t)
in (mlty_to_typ _146_87))
in (Prims.strcat "T_wire (" _146_88))
in (Prims.strcat _146_89 ")"))
end else begin
if (is_share t) then begin
"T_sh"
end else begin
(match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named (l, p) -> begin
(
# 224 "FStar.Extraction.Wysteria.Extract.fst"
let n = (Prims.strcat "T_cons (" (name_to_string (FStar_Extraction_ML_Syntax.string_of_mlpath p)))
in (
# 225 "FStar.Extraction.Wysteria.Extract.fst"
let args = (FStar_List.fold_left (fun s a -> (let _146_93 = (let _146_92 = (mlty_to_typ a)
in (Prims.strcat (Prims.strcat s " (") _146_92))
in (Prims.strcat _146_93 ");"))) "" l)
in (Prims.strcat (Prims.strcat (Prims.strcat n ", [") args) "])")))
end
| _64_226 -> begin
"T_unknown"
end)
end
end
end
end
end
end
end)

# 229 "FStar.Extraction.Wysteria.Extract.fst"
let get_constant_injection : FStar_Extraction_ML_Syntax.mlty  ->  Prims.string  ->  Prims.string = (fun t x -> if (is_bool t) then begin
(Prims.strcat "C_bool " x)
end else begin
if (is_unit t) then begin
"C_unit ()"
end else begin
if (is_known_named_type t) then begin
(let _146_99 = (let _146_98 = (mlty_to_typ t)
in (Prims.strcat (Prims.strcat (Prims.strcat "C_opaque ((), Obj.magic " x) ", ") _146_98))
in (Prims.strcat _146_99 ")"))
end else begin
(FStar_All.failwith "Constant injection does not support this type")
end
end
end)

# 236 "FStar.Extraction.Wysteria.Extract.fst"
let is_ffi : FStar_Extraction_ML_Syntax.mlexpr  ->  (Prims.bool * Prims.string) = (fun _64_233 -> (match (_64_233) with
| {FStar_Extraction_ML_Syntax.expr = e; FStar_Extraction_ML_Syntax.ty = t; FStar_Extraction_ML_Syntax.loc = _64_230} -> begin
(match (e) with
| FStar_Extraction_ML_Syntax.MLE_Name (p, n) -> begin
(let _146_102 = (translate_ffi_name (FStar_Extraction_ML_Syntax.string_of_mlpath (p, n)))
in (((p = ("FFI")::[]) || (p = ("Prims")::[])), _146_102))
end
| _64_239 -> begin
(false, "")
end)
end))

# 241 "FStar.Extraction.Wysteria.Extract.fst"
let tag_of_mlconst : FStar_Extraction_ML_Syntax.mlconstant  ->  Prims.string = (fun c -> (match (c) with
| FStar_Extraction_ML_Syntax.MLC_Unit -> begin
"MLC_Unit"
end
| FStar_Extraction_ML_Syntax.MLC_Bool (_64_243) -> begin
"MLC_Bool"
end
| FStar_Extraction_ML_Syntax.MLC_Char (_64_246) -> begin
"MLC_Char"
end
| FStar_Extraction_ML_Syntax.MLC_Byte (_64_249) -> begin
"MLC_Byte"
end
| FStar_Extraction_ML_Syntax.MLC_Int32 (_64_252) -> begin
"MLC_Int32"
end
| FStar_Extraction_ML_Syntax.MLC_Int64 (_64_255) -> begin
"MLC_Int64"
end
| FStar_Extraction_ML_Syntax.MLC_Int (_64_258) -> begin
"MLC_Int"
end
| FStar_Extraction_ML_Syntax.MLC_Float (_64_261) -> begin
"MLC_Float"
end
| FStar_Extraction_ML_Syntax.MLC_Bytes (_64_264) -> begin
"MLC_Bytes"
end
| FStar_Extraction_ML_Syntax.MLC_String (_64_267) -> begin
"MLC_String"
end))

# 254 "FStar.Extraction.Wysteria.Extract.fst"
let extract_mlconst : FStar_Extraction_ML_Syntax.mlconstant  ->  wexp = (fun c -> (match (c) with
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
| _64_282 -> begin
(FStar_All.failwith (Prims.strcat "Unsupported constant: tag: " (tag_of_mlconst c)))
end))

# 264 "FStar.Extraction.Wysteria.Extract.fst"
let is_wys_lib_fn : FStar_Extraction_ML_Syntax.mlexpr  ->  Prims.bool = (fun _64_287 -> (match (_64_287) with
| {FStar_Extraction_ML_Syntax.expr = e; FStar_Extraction_ML_Syntax.ty = t; FStar_Extraction_ML_Syntax.loc = _64_284} -> begin
(match (e) with
| FStar_Extraction_ML_Syntax.MLE_Name (p) -> begin
(FStar_Util.starts_with (FStar_Extraction_ML_Syntax.string_of_mlpath p) "Wysteria")
end
| _64_291 -> begin
false
end)
end))

# 269 "FStar.Extraction.Wysteria.Extract.fst"
let check_pats_for_bool : (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr Prims.option * FStar_Extraction_ML_Syntax.mlexpr) Prims.list  ->  (Prims.bool * FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mlexpr) = (fun l -> (
# 270 "FStar.Extraction.Wysteria.Extract.fst"
let def = (false, FStar_Extraction_ML_Syntax.ml_unit, FStar_Extraction_ML_Syntax.ml_unit)
in if ((FStar_List.length l) <> 2) then begin
def
end else begin
(
# 273 "FStar.Extraction.Wysteria.Extract.fst"
let _64_298 = (FStar_List.hd l)
in (match (_64_298) with
| (p1, _64_296, e1) -> begin
(
# 274 "FStar.Extraction.Wysteria.Extract.fst"
let _64_303 = (let _146_111 = (FStar_List.tl l)
in (FStar_List.hd _146_111))
in (match (_64_303) with
| (p2, _64_301, e2) -> begin
(match ((p1, p2)) with
| (FStar_Extraction_ML_Syntax.MLP_Const (FStar_Extraction_ML_Syntax.MLC_Bool (_64_305)), FStar_Extraction_ML_Syntax.MLP_Const (FStar_Extraction_ML_Syntax.MLC_Bool (_64_309))) -> begin
(true, e1, e2)
end
| _64_314 -> begin
def
end)
end))
end))
end))

# 279 "FStar.Extraction.Wysteria.Extract.fst"
let mk_var : Prims.string  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.string = (fun s t -> (let _146_117 = (let _146_116 = (mlty_to_typ t)
in (Prims.strcat (Prims.strcat (Prims.strcat "mk_var " (name_to_string s)) " (") _146_116))
in (Prims.strcat _146_117 ")")))

# 282 "FStar.Extraction.Wysteria.Extract.fst"
let mk_varname : Prims.string  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.string = (fun s t -> (let _146_123 = (let _146_122 = (mlty_to_typ t)
in (Prims.strcat (Prims.strcat (Prims.strcat "mk_varname " (name_to_string s)) " (") _146_122))
in (Prims.strcat _146_123 ")")))

# 285 "FStar.Extraction.Wysteria.Extract.fst"
let rec extract_mlexp : FStar_Extraction_ML_Syntax.mlexpr  ->  Prims.string = (fun _64_323 -> (match (_64_323) with
| {FStar_Extraction_ML_Syntax.expr = e; FStar_Extraction_ML_Syntax.ty = t; FStar_Extraction_ML_Syntax.loc = _64_320} -> begin
(match (e) with
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(let _146_130 = (let _146_129 = (extract_mlconst c)
in (Prims.strcat "mk_const (" _146_129))
in (Prims.strcat _146_130 ")"))
end
| FStar_Extraction_ML_Syntax.MLE_Var (x) -> begin
(mk_var (FStar_Extraction_ML_Syntax.idsym x) t)
end
| FStar_Extraction_ML_Syntax.MLE_Name (p, s) -> begin
(
# 290 "FStar.Extraction.Wysteria.Extract.fst"
let ss = (FStar_Extraction_ML_Syntax.string_of_mlpath (p, s))
in (
# 291 "FStar.Extraction.Wysteria.Extract.fst"
let _64_333 = if (not ((FStar_Util.starts_with ss "SMC."))) then begin
(let _146_131 = (FStar_Util.format1 "Warning: name not applied: %s\n" (FStar_Extraction_ML_Syntax.string_of_mlpath (p, s)))
in (FStar_Util.print_string _146_131))
end else begin
()
end
in (mk_var s t)))
end
| FStar_Extraction_ML_Syntax.MLE_Let ((b, l), e') -> begin
if b then begin
(FStar_All.failwith "Nested recursive lets are not supported yet")
end else begin
(
# 300 "FStar.Extraction.Wysteria.Extract.fst"
let lb = (FStar_List.hd l)
in (
# 301 "FStar.Extraction.Wysteria.Extract.fst"
let lbname = (FStar_Extraction_ML_Syntax.idsym lb.FStar_Extraction_ML_Syntax.mllb_name)
in (
# 302 "FStar.Extraction.Wysteria.Extract.fst"
let lbbody = lb.FStar_Extraction_ML_Syntax.mllb_def
in (let _146_139 = (let _146_138 = (let _146_136 = (let _146_135 = (let _146_133 = (let _146_132 = (mk_varname lbname lbbody.FStar_Extraction_ML_Syntax.ty)
in (Prims.strcat "mk_let (" _146_132))
in (Prims.strcat _146_133 ") ("))
in (let _146_134 = (extract_mlexp lbbody)
in (Prims.strcat _146_135 _146_134)))
in (Prims.strcat _146_136 ") ("))
in (let _146_137 = (extract_mlexp e')
in (Prims.strcat _146_138 _146_137)))
in (Prims.strcat _146_139 ")")))))
end
end
| FStar_Extraction_ML_Syntax.MLE_App (f, args) -> begin
(
# 305 "FStar.Extraction.Wysteria.Extract.fst"
let _64_350 = (is_ffi f)
in (match (_64_350) with
| (b, ffi) -> begin
if b then begin
(
# 307 "FStar.Extraction.Wysteria.Extract.fst"
let inj = (get_injection t)
in (
# 308 "FStar.Extraction.Wysteria.Extract.fst"
let args_exp = (FStar_List.fold_left (fun s a -> (let _146_143 = (let _146_142 = (extract_mlexp a)
in (Prims.strcat (Prims.strcat s " (") _146_142))
in (Prims.strcat _146_143 ");"))) "" args)
in (let _146_153 = (let _146_152 = (let _146_151 = (let _146_150 = (let _146_149 = (let _146_148 = (let _146_147 = (let _146_146 = (let _146_145 = (let _146_144 = (FStar_Util.string_of_int (FStar_List.length args))
in (Prims.strcat "mk_ffi " _146_144))
in (Prims.strcat _146_145 " "))
in (Prims.strcat _146_146 (name_to_string ffi)))
in (Prims.strcat _146_147 " ("))
in (Prims.strcat _146_148 ffi))
in (Prims.strcat _146_149 ") [ "))
in (Prims.strcat _146_150 args_exp))
in (Prims.strcat _146_151 " ] ("))
in (Prims.strcat _146_152 inj))
in (Prims.strcat _146_153 ")"))))
end else begin
if (is_wys_lib_fn f) then begin
(extract_wysteria_specific_ast f args t)
end else begin
(
# 312 "FStar.Extraction.Wysteria.Extract.fst"
let s = (extract_mlexp f)
in if (s = "_assert") then begin
"mk_const (C_unit ())"
end else begin
(FStar_List.fold_left (fun s a -> (let _146_157 = (let _146_156 = (extract_mlexp a)
in (Prims.strcat (Prims.strcat (Prims.strcat "mk_app (" s) ") (") _146_156))
in (Prims.strcat _146_157 ")"))) s args)
end)
end
end
end))
end
| FStar_Extraction_ML_Syntax.MLE_Fun (bs, body) -> begin
(
# 316 "FStar.Extraction.Wysteria.Extract.fst"
let body_str = (extract_mlexp body)
in (FStar_List.fold_left (fun s _64_369 -> (match (_64_369) with
| ((b, _64_366), t) -> begin
(let _146_163 = (let _146_162 = (let _146_161 = (let _146_160 = (mk_varname b t)
in (Prims.strcat "mk_abs (" _146_160))
in (Prims.strcat _146_161 ") ("))
in (Prims.strcat _146_162 s))
in (Prims.strcat _146_163 ")"))
end)) body_str (FStar_List.rev bs)))
end
| FStar_Extraction_ML_Syntax.MLE_Match (e, bs) -> begin
(
# 319 "FStar.Extraction.Wysteria.Extract.fst"
let _64_377 = (check_pats_for_bool bs)
in (match (_64_377) with
| (b, e1, e2) -> begin
if b then begin
(let _146_171 = (let _146_170 = (let _146_168 = (let _146_167 = (let _146_165 = (let _146_164 = (extract_mlexp e)
in (Prims.strcat "mk_cond (" _146_164))
in (Prims.strcat _146_165 ") ("))
in (let _146_166 = (extract_mlexp e1)
in (Prims.strcat _146_167 _146_166)))
in (Prims.strcat _146_168 ") ("))
in (let _146_169 = (extract_mlexp e2)
in (Prims.strcat _146_170 _146_169)))
in (Prims.strcat _146_171 ")"))
end else begin
(FStar_All.failwith "Only if-then-else patterns are supported")
end
end))
end
| FStar_Extraction_ML_Syntax.MLE_Coerce (e, _64_380, _64_382) -> begin
(extract_mlexp e)
end
| FStar_Extraction_ML_Syntax.MLE_If (e, e1, e2_opt) -> begin
(match (e2_opt) with
| None -> begin
(FStar_All.failwith "If Then Else should have an else branch?")
end
| Some (e2) -> begin
(let _146_179 = (let _146_178 = (let _146_176 = (let _146_175 = (let _146_173 = (let _146_172 = (extract_mlexp e)
in (Prims.strcat "mk_cond (" _146_172))
in (Prims.strcat _146_173 ") ("))
in (let _146_174 = (extract_mlexp e1)
in (Prims.strcat _146_175 _146_174)))
in (Prims.strcat _146_176 ") ("))
in (let _146_177 = (extract_mlexp e2)
in (Prims.strcat _146_178 _146_177)))
in (Prims.strcat _146_179 ")"))
end)
end
| _64_394 -> begin
(FStar_All.failwith "This expression extraction is not supported yet")
end)
end))
and extract_wysteria_specific_ast : FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr Prims.list  ->  FStar_Extraction_ML_Syntax.mlty  ->  wexp = (fun _64_400 args t -> (match (_64_400) with
| {FStar_Extraction_ML_Syntax.expr = f; FStar_Extraction_ML_Syntax.ty = _64_398; FStar_Extraction_ML_Syntax.loc = _64_396} -> begin
(match (f) with
| FStar_Extraction_ML_Syntax.MLE_Name (_64_404, s) -> begin
if (s = "main") then begin
(
# 335 "FStar.Extraction.Wysteria.Extract.fst"
let f = (let _146_183 = (FStar_List.tl args)
in (FStar_List.hd _146_183))
in (
# 336 "FStar.Extraction.Wysteria.Extract.fst"
let f_exp = (extract_mlexp f)
in (Prims.strcat (Prims.strcat "mk_app (" f_exp) ") (E_const (C_unit ()))")))
end else begin
if (s = "w_read_int") then begin
(
# 339 "FStar.Extraction.Wysteria.Extract.fst"
let inj_str = (get_injection t)
in (Prims.strcat (Prims.strcat "mk_ffi 1 \"FFI.read_int\" FFI.read_int [ E_const (C_unit ()) ] (" inj_str) ")"))
end else begin
if (s = "w_read_int_tuple") then begin
(
# 342 "FStar.Extraction.Wysteria.Extract.fst"
let inj_str = (get_injection t)
in (Prims.strcat (Prims.strcat "mk_ffi 1 \"FFI.read_int_tuple\" FFI.read_int_tuple [ E_const (C_unit ()) ] (" inj_str) ")"))
end else begin
if (s = "w_read_int_list") then begin
(
# 345 "FStar.Extraction.Wysteria.Extract.fst"
let inj_str = (get_injection t)
in (Prims.strcat (Prims.strcat "mk_ffi 1 \"FFI.read_int_list\" FFI.read_int_list [ E_const (C_unit ()) ] (" inj_str) ")"))
end else begin
(
# 348 "FStar.Extraction.Wysteria.Extract.fst"
let r = (lookup_wys_lib_map s)
in (
# 349 "FStar.Extraction.Wysteria.Extract.fst"
let args = (sublist s args r.rem_args)
in (FStar_List.fold_left (fun acc arg -> (let _146_187 = (let _146_186 = (extract_mlexp arg)
in (Prims.strcat (Prims.strcat acc " (") _146_186))
in (Prims.strcat _146_187 ")"))) r.extracted_fn_name args)))
end
end
end
end
end
| _64_418 -> begin
(FStar_All.failwith "Expected wysteria lib fn to be a MLE_Name")
end)
end))

# 354 "FStar.Extraction.Wysteria.Extract.fst"
let extract_mllb : FStar_Extraction_ML_Syntax.mlletbinding  ->  tlet = (fun _64_421 -> (match (_64_421) with
| (b, l) -> begin
if ((FStar_List.length l) <> 1) then begin
(FStar_All.failwith "Mutually recursive lets are not yet suppored")
end else begin
(
# 357 "FStar.Extraction.Wysteria.Extract.fst"
let lb = (FStar_List.hd l)
in (
# 358 "FStar.Extraction.Wysteria.Extract.fst"
let lbname = (FStar_Extraction_ML_Syntax.idsym lb.FStar_Extraction_ML_Syntax.mllb_name)
in (
# 359 "FStar.Extraction.Wysteria.Extract.fst"
let lbbody = lb.FStar_Extraction_ML_Syntax.mllb_def
in if b then begin
(match (lbbody.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Fun (bs, e) -> begin
(
# 364 "FStar.Extraction.Wysteria.Extract.fst"
let _64_431 = (let _146_191 = (FStar_List.hd bs)
in (let _146_190 = (FStar_List.tl bs)
in (_146_191, _146_190)))
in (match (_64_431) with
| (first_b, rest_bs) -> begin
(
# 365 "FStar.Extraction.Wysteria.Extract.fst"
let body_exp = (extract_mlexp e)
in (
# 366 "FStar.Extraction.Wysteria.Extract.fst"
let tl_abs_exp = (FStar_List.fold_left (fun e _64_436 -> (match (_64_436) with
| (bname, btyp) -> begin
(let _146_197 = (let _146_196 = (let _146_195 = (let _146_194 = (mk_varname (FStar_Extraction_ML_Syntax.idsym bname) btyp)
in (Prims.strcat "mk_abs (" _146_194))
in (Prims.strcat _146_195 ") ("))
in (Prims.strcat _146_196 e))
in (Prims.strcat _146_197 ")"))
end)) body_exp (FStar_List.rev rest_bs))
in (
# 367 "FStar.Extraction.Wysteria.Extract.fst"
let fix_exp = (let _146_204 = (let _146_203 = (let _146_202 = (let _146_201 = (let _146_199 = (let _146_198 = (mk_varname lbname lbbody.FStar_Extraction_ML_Syntax.ty)
in (Prims.strcat "mk_fix (" _146_198))
in (Prims.strcat _146_199 ") ("))
in (let _146_200 = (mk_varname (FStar_Extraction_ML_Syntax.idsym (Prims.fst first_b)) (Prims.snd first_b))
in (Prims.strcat _146_201 _146_200)))
in (Prims.strcat _146_202 ") ("))
in (Prims.strcat _146_203 tl_abs_exp))
in (Prims.strcat _146_204 ")"))
in (let _146_206 = (let _146_205 = (mlty_to_typ lbbody.FStar_Extraction_ML_Syntax.ty)
in (lbname, _146_205, fix_exp))
in Mk_tlet (_146_206)))))
end))
end
| _64_440 -> begin
(FStar_All.failwith "Recursive let binding is not an abstraction ?")
end)
end else begin
(let _146_209 = (let _146_208 = (mlty_to_typ lbbody.FStar_Extraction_ML_Syntax.ty)
in (let _146_207 = (extract_mlexp lbbody)
in (lbname, _146_208, _146_207)))
in Mk_tlet (_146_209))
end)))
end
end))

# 373 "FStar.Extraction.Wysteria.Extract.fst"
let extract_mlmodule : FStar_Extraction_ML_Syntax.mlmodule  ->  (tlet Prims.list * Prims.string Prims.option) = (fun m -> (FStar_List.fold_left (fun _64_444 tld -> (match (_64_444) with
| (l, top_opt) -> begin
(match (tld) with
| FStar_Extraction_ML_Syntax.MLM_Ty (_64_447) -> begin
(l, top_opt)
end
| FStar_Extraction_ML_Syntax.MLM_Exn (_64_450) -> begin
(FStar_All.failwith "Cannot extract an exception")
end
| FStar_Extraction_ML_Syntax.MLM_Let (lb) -> begin
(let _146_216 = (let _146_215 = (let _146_214 = (extract_mllb lb)
in (_146_214)::[])
in (FStar_List.append l _146_215))
in (_146_216, top_opt))
end
| FStar_Extraction_ML_Syntax.MLM_Top (e) -> begin
(match (top_opt) with
| None -> begin
(let _146_218 = (let _146_217 = (extract_mlexp e)
in Some (_146_217))
in (l, _146_218))
end
| Some (_64_458) -> begin
(FStar_All.failwith "Impossible: more than one top expressions")
end)
end
| FStar_Extraction_ML_Syntax.MLM_Loc (_64_461) -> begin
(l, top_opt)
end)
end)) ([], None) m))

# 386 "FStar.Extraction.Wysteria.Extract.fst"
let rec find_smc_module : FStar_Extraction_ML_Syntax.mllib Prims.list  ->  FStar_Extraction_ML_Syntax.mlmodule Prims.option = (fun mllibs -> (
# 387 "FStar.Extraction.Wysteria.Extract.fst"
let rec find_smc_module' = (fun mllib -> (match (mllib) with
| [] -> begin
None
end
| (x, mlsig_opt, FStar_Extraction_ML_Syntax.MLLib (mllib'))::tl -> begin
if (x = "SMC") then begin
(match (mlsig_opt) with
| Some (_64_475, m) -> begin
Some (m)
end
| None -> begin
(Prims.raise (FStar_Util.NYI ("Found the SMC module name but no module")))
end)
end else begin
(
# 396 "FStar.Extraction.Wysteria.Extract.fst"
let m_opt = (find_smc_module' mllib')
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
(
# 405 "FStar.Extraction.Wysteria.Extract.fst"
let m_opt = (find_smc_module' s)
in (match (m_opt) with
| Some (m) -> begin
Some (m)
end
| None -> begin
(find_smc_module tl)
end))
end)))

# 410 "FStar.Extraction.Wysteria.Extract.fst"
let mltyp_to_string : FStar_Extraction_ML_Syntax.mlty  ->  Prims.string = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named (_64_495, p) -> begin
(FStar_Extraction_ML_Syntax.string_of_mlpath p)
end
| _64_500 -> begin
"Something other than named type"
end))

# 415 "FStar.Extraction.Wysteria.Extract.fst"
let rec get_iface_arg_ret_typ : FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_Syntax.mlty * FStar_Extraction_ML_Syntax.mlty) = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (arg, _64_504, ret) -> begin
(match (ret) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (_64_509, _64_511, _64_513) -> begin
(get_iface_arg_ret_typ ret)
end
| _64_517 -> begin
(arg, ret)
end)
end
| _64_519 -> begin
(FStar_All.failwith "Get wys arg ret type has a non-arrow type")
end))

# 423 "FStar.Extraction.Wysteria.Extract.fst"
let extract_smc_exports : FStar_Extraction_ML_Env.env  ->  Prims.string = (fun g -> "")

# 449 "FStar.Extraction.Wysteria.Extract.fst"
let extract : FStar_Absyn_Syntax.modul Prims.list  ->  FStar_Tc_Env.env  ->  Prims.unit = (fun l en -> (
# 450 "FStar.Extraction.Wysteria.Extract.fst"
let _64_523 = (initialize ())
in (
# 451 "FStar.Extraction.Wysteria.Extract.fst"
let _64_527 = (let _146_233 = (FStar_Extraction_ML_Env.mkContext en)
in (FStar_Util.fold_map FStar_Extraction_ML_ExtractMod.extract _146_233 l))
in (match (_64_527) with
| (c, mllibs) -> begin
(
# 454 "FStar.Extraction.Wysteria.Extract.fst"
let mllibs = (FStar_List.flatten mllibs)
in (
# 455 "FStar.Extraction.Wysteria.Extract.fst"
let m_opt = (find_smc_module mllibs)
in (
# 456 "FStar.Extraction.Wysteria.Extract.fst"
let s_smc = (match (m_opt) with
| Some (m) -> begin
(
# 459 "FStar.Extraction.Wysteria.Extract.fst"
let _64_534 = (extract_mlmodule m)
in (match (_64_534) with
| (l, m_opt) -> begin
(FStar_List.fold_left (fun s _64_540 -> (match (_64_540) with
| Mk_tlet (n, t, b) -> begin
(Prims.strcat (Prims.strcat (Prims.strcat (Prims.strcat (Prims.strcat (Prims.strcat (Prims.strcat s "(") (name_to_string n)) ", (") t) "), (") b) "));\n")
end)) "" l)
end))
end
| _64_542 -> begin
""
end)
in (
# 472 "FStar.Extraction.Wysteria.Extract.fst"
let prog = (let _146_236 = (FStar_Options.prependOutputDir "prog.ml")
in (FStar_Util.open_file_for_writing _146_236))
in (
# 473 "FStar.Extraction.Wysteria.Extract.fst"
let _64_545 = (FStar_Util.append_to_file prog "open AST")
in (
# 474 "FStar.Extraction.Wysteria.Extract.fst"
let _64_547 = (FStar_Util.append_to_file prog "open FFI")
in (
# 475 "FStar.Extraction.Wysteria.Extract.fst"
let _64_549 = (FStar_Util.append_to_file prog "\n")
in (
# 476 "FStar.Extraction.Wysteria.Extract.fst"
let _64_551 = (FStar_Util.append_to_file prog "let const_meta = Meta ([], Can_b, [], Can_w)")
in (
# 477 "FStar.Extraction.Wysteria.Extract.fst"
let _64_553 = (FStar_Util.append_to_file prog "\n")
in (
# 478 "FStar.Extraction.Wysteria.Extract.fst"
let _64_555 = (FStar_Util.append_to_file prog (Prims.strcat (Prims.strcat "let program = [\n" s_smc) "]"))
in (FStar_Util.close_file prog)))))))))))
end))))




