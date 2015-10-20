
open Prims
type name =
Prims.string

type wexp =
Prims.string

type tlet =
| Mk_tlet of (name * wexp)

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

let rec sublist = (fun s l n -> (match ((n > (FStar_List.length l))) with
| true -> begin
(let _130_46 = (let _130_45 = (FStar_Util.string_of_int (FStar_List.length l))
in (let _130_44 = (FStar_Util.string_of_int n)
in (FStar_Util.format3 "Error removing arguments in sublist for %s, list len is %s, n is %s " s _130_45 _130_44)))
in (FStar_All.failwith _130_46))
end
| false -> begin
(match ((n = 0)) with
| true -> begin
l
end
| false -> begin
(let _130_47 = (FStar_List.tl l)
in (sublist s _130_47 (n - 1)))
end)
end))

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

let is_wysteria_type = (fun t -> (((((is_prin t) || (is_prins t)) || (is_eprins t)) || (is_box t)) || (is_wire t)))

let slice_value = "Semantics.slice_v_ffi"

let slice_value_sps = "Semantics.slice_v_sps_ffi"

let compose_values = "Semantics.compose_vals_ffi"

let rec get_opaque_fns = (fun t -> (match ((((((is_bool t) || (is_unit t)) || (is_prin t)) || (is_prins t)) || (is_eprins t))) with
| true -> begin
(slice_id, compose_ids, slice_id_sps)
end
| false -> begin
(match (((is_box t) || (is_wire t))) with
| true -> begin
(slice_value, compose_values, slice_value_sps)
end
| false -> begin
(match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) -> begin
(lookup_ffi_map (FStar_Extraction_ML_Syntax.string_of_mlpath p))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, p) -> begin
(let _64_148 = (get_opaque_fns (FStar_Extraction_ML_Syntax.MLTY_Named (([], p))))
in (match (_64_148) with
| (e1, e2, e3) -> begin
(FStar_List.fold_left (fun _64_152 arg -> (match (_64_152) with
| (a1, a2, a3) -> begin
(match (arg) with
| FStar_Extraction_ML_Syntax.MLTY_Named (_64_155) -> begin
(let _64_160 = (get_opaque_fns arg)
in (match (_64_160) with
| (e1_arg, e2_arg, e3_arg) -> begin
((Prims.strcat (Prims.strcat (Prims.strcat (Prims.strcat "(" a1) " ") e1_arg) ")"), (Prims.strcat (Prims.strcat (Prims.strcat (Prims.strcat "(" a2) " ") e2_arg) ")"), (Prims.strcat (Prims.strcat (Prims.strcat (Prims.strcat "(" a3) " ") e3_arg) ")"))
end))
end
| _64_162 -> begin
(FStar_All.failwith "Did not expect type argument to be something other than named type")
end)
end)) (e1, e2, e3) args)
end))
end
| _64_164 -> begin
(FStar_All.failwith "Did not expect a non named type in get_opaque_fns")
end)
end)
end))

let get_injection = (fun t -> (let s = "fun x -> "
in (let s' = (match ((is_bool t)) with
| true -> begin
"D_v (const_meta, V_bool x)"
end
| false -> begin
(match ((is_unit t)) with
| true -> begin
"D_v (const_meta, V_unit)"
end
| false -> begin
(match ((is_prin t)) with
| true -> begin
"D_v (const_meta, V_prin x)"
end
| false -> begin
(match (((is_prins t) || (is_eprins t))) with
| true -> begin
"D_v (const_meta, V_eprins x)"
end
| false -> begin
(match (((is_box t) || (is_wire t))) with
| true -> begin
"x"
end
| false -> begin
(let _64_170 = (get_opaque_fns t)
in (match (_64_170) with
| (s1, s2, s3) -> begin
(Prims.strcat (Prims.strcat (Prims.strcat (Prims.strcat (Prims.strcat "mk_v_opaque x " s1) " ") s2) " ") s3)
end))
end)
end)
end)
end)
end)
in (Prims.strcat s s'))))

let is_ffi = (fun _64_174 -> (match (_64_174) with
| {FStar_Extraction_ML_Syntax.expr = e; FStar_Extraction_ML_Syntax.ty = t} -> begin
(match (e) with
| FStar_Extraction_ML_Syntax.MLE_Name (p, n) -> begin
(let _130_72 = (translate_ffi_name (FStar_Extraction_ML_Syntax.string_of_mlpath (p, n)))
in (((p = ("FFI")::[]) || (p = ("Prims")::[])), _130_72))
end
| _64_180 -> begin
(false, "")
end)
end))

let extract_mlconst = (fun c -> (match (c) with
| FStar_Extraction_ML_Syntax.MLC_Unit -> begin
"C_unit ()"
end
| FStar_Extraction_ML_Syntax.MLC_Bool (b) -> begin
(Prims.strcat "C_bool " (match (b) with
| true -> begin
"true"
end
| false -> begin
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
| _64_192 -> begin
(FStar_All.failwith "Unsupported constant")
end))

let is_wys_lib_fn = (fun _64_195 -> (match (_64_195) with
| {FStar_Extraction_ML_Syntax.expr = e; FStar_Extraction_ML_Syntax.ty = t} -> begin
(match (e) with
| FStar_Extraction_ML_Syntax.MLE_Name (p) -> begin
(FStar_Util.starts_with (FStar_Extraction_ML_Syntax.string_of_mlpath p) "Wysteria")
end
| _64_199 -> begin
false
end)
end))

let check_pats_for_bool = (fun l -> (let def = (false, FStar_Extraction_ML_Syntax.ml_unit, FStar_Extraction_ML_Syntax.ml_unit)
in (match (((FStar_List.length l) <> 2)) with
| true -> begin
def
end
| false -> begin
(let _64_206 = (FStar_List.hd l)
in (match (_64_206) with
| (p1, _64_204, e1) -> begin
(let _64_211 = (let _130_79 = (FStar_List.tl l)
in (FStar_List.hd _130_79))
in (match (_64_211) with
| (p2, _64_209, e2) -> begin
(match ((p1, p2)) with
| (FStar_Extraction_ML_Syntax.MLP_Const (FStar_Extraction_ML_Syntax.MLC_Bool (_64_213)), FStar_Extraction_ML_Syntax.MLP_Const (FStar_Extraction_ML_Syntax.MLC_Bool (_64_217))) -> begin
(true, e1, e2)
end
| _64_222 -> begin
def
end)
end))
end))
end)))

let name_to_string = (fun s -> (Prims.strcat (Prims.strcat "\"" s) "\""))

let rec extract_mlexp = (fun _64_226 -> (match (_64_226) with
| {FStar_Extraction_ML_Syntax.expr = e; FStar_Extraction_ML_Syntax.ty = t} -> begin
(match (e) with
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(let _130_88 = (let _130_87 = (extract_mlconst c)
in (Prims.strcat "mk_const (" _130_87))
in (Prims.strcat _130_88 ")"))
end
| FStar_Extraction_ML_Syntax.MLE_Var (x) -> begin
(Prims.strcat "mk_var " (name_to_string (FStar_Extraction_ML_Syntax.idsym x)))
end
| FStar_Extraction_ML_Syntax.MLE_Name (p, s) -> begin
(let ss = (FStar_Extraction_ML_Syntax.string_of_mlpath (p, s))
in (let _64_236 = (match ((not ((FStar_Util.starts_with ss "SMC.")))) with
| true -> begin
(let _130_89 = (FStar_Util.format1 "Warning: name not applied: %s\n" (FStar_Extraction_ML_Syntax.string_of_mlpath (p, s)))
in (FStar_Util.print_string _130_89))
end
| false -> begin
()
end)
in (Prims.strcat "mk_var " (name_to_string s))))
end
| FStar_Extraction_ML_Syntax.MLE_Let ((b, l), e') -> begin
(match (b) with
| true -> begin
(FStar_All.failwith "Nested recursive lets are not supported yet")
end
| false -> begin
(let lb = (FStar_List.hd l)
in (let lbname = (FStar_Extraction_ML_Syntax.idsym lb.FStar_Extraction_ML_Syntax.mllb_name)
in (let lbbody = lb.FStar_Extraction_ML_Syntax.mllb_def
in (let _130_94 = (let _130_93 = (let _130_91 = (let _130_90 = (extract_mlexp lbbody)
in (Prims.strcat (Prims.strcat (Prims.strcat "mk_let " (name_to_string lbname)) " (") _130_90))
in (Prims.strcat _130_91 ") ("))
in (let _130_92 = (extract_mlexp e')
in (Prims.strcat _130_93 _130_92)))
in (Prims.strcat _130_94 ")")))))
end)
end
| FStar_Extraction_ML_Syntax.MLE_App (f, args) -> begin
(let _64_253 = (is_ffi f)
in (match (_64_253) with
| (b, ffi) -> begin
(match (b) with
| true -> begin
(let inj = (get_injection t)
in (let args_exp = (FStar_List.fold_left (fun s a -> (let _130_98 = (let _130_97 = (extract_mlexp a)
in (Prims.strcat (Prims.strcat s " (") _130_97))
in (Prims.strcat _130_98 ");"))) "" args)
in (let _130_106 = (let _130_105 = (let _130_104 = (let _130_103 = (let _130_102 = (let _130_101 = (let _130_100 = (let _130_99 = (FStar_Util.string_of_int (FStar_List.length args))
in (Prims.strcat "mk_ffi " _130_99))
in (Prims.strcat _130_100 " ("))
in (Prims.strcat _130_101 ffi))
in (Prims.strcat _130_102 ") [ "))
in (Prims.strcat _130_103 args_exp))
in (Prims.strcat _130_104 " ] ("))
in (Prims.strcat _130_105 inj))
in (Prims.strcat _130_106 ")"))))
end
| false -> begin
(match ((is_wys_lib_fn f)) with
| true -> begin
(extract_wysteria_specific_ast f args t)
end
| false -> begin
(let s = (extract_mlexp f)
in (match ((s = "_assert")) with
| true -> begin
"mk_const (C_unit ())"
end
| false -> begin
(FStar_List.fold_left (fun s a -> (let _130_110 = (let _130_109 = (extract_mlexp a)
in (Prims.strcat (Prims.strcat (Prims.strcat "mk_app (" s) ") (") _130_109))
in (Prims.strcat _130_110 ")"))) s args)
end))
end)
end)
end))
end
| FStar_Extraction_ML_Syntax.MLE_Fun (bs, body) -> begin
(let body_str = (extract_mlexp body)
in (FStar_List.fold_left (fun s _64_273 -> (match (_64_273) with
| ((b, _64_269), _64_272) -> begin
(Prims.strcat (Prims.strcat (Prims.strcat (Prims.strcat "mk_abs " (name_to_string b)) " (") s) ")")
end)) body_str (FStar_List.rev bs)))
end
| FStar_Extraction_ML_Syntax.MLE_Match (e, bs) -> begin
(let _64_281 = (check_pats_for_bool bs)
in (match (_64_281) with
| (b, e1, e2) -> begin
(match (b) with
| true -> begin
(let _130_120 = (let _130_119 = (let _130_117 = (let _130_116 = (let _130_114 = (let _130_113 = (extract_mlexp e)
in (Prims.strcat "mk_cond (" _130_113))
in (Prims.strcat _130_114 ") ("))
in (let _130_115 = (extract_mlexp e1)
in (Prims.strcat _130_116 _130_115)))
in (Prims.strcat _130_117 ") ("))
in (let _130_118 = (extract_mlexp e2)
in (Prims.strcat _130_119 _130_118)))
in (Prims.strcat _130_120 ")"))
end
| false -> begin
(FStar_All.failwith "Only if-then-else patterns are supported")
end)
end))
end
| FStar_Extraction_ML_Syntax.MLE_Coerce (e, _64_284, _64_286) -> begin
(extract_mlexp e)
end
| _64_290 -> begin
(FStar_All.failwith "This expression extraction is not supported yet")
end)
end))
and extract_wysteria_specific_ast = (fun _64_294 args t -> (match (_64_294) with
| {FStar_Extraction_ML_Syntax.expr = f; FStar_Extraction_ML_Syntax.ty = _64_292} -> begin
(match (f) with
| FStar_Extraction_ML_Syntax.MLE_Name (_64_298, s) -> begin
(match ((s = "main")) with
| true -> begin
(let f = (let _130_124 = (FStar_List.tl args)
in (FStar_List.hd _130_124))
in (let f_exp = (extract_mlexp f)
in (Prims.strcat (Prims.strcat "mk_app (" f_exp) ") (E_const (C_unit ()))")))
end
| false -> begin
(match ((s = "w_read_int")) with
| true -> begin
(let inj_str = (get_injection t)
in (Prims.strcat (Prims.strcat "mk_ffi 1 FFI.read_int [ E_const (C_unit ()) ] (" inj_str) ")"))
end
| false -> begin
(match ((s = "w_read_int_tuple")) with
| true -> begin
(let inj_str = (get_injection t)
in (Prims.strcat (Prims.strcat "mk_ffi 1 FFI.read_int_tuple [ E_const (C_unit ()) ] (" inj_str) ")"))
end
| false -> begin
(let r = (lookup_wys_lib_map s)
in (let args = (sublist s args r.rem_args)
in (FStar_List.fold_left (fun acc arg -> (let _130_128 = (let _130_127 = (extract_mlexp arg)
in (Prims.strcat (Prims.strcat acc " (") _130_127))
in (Prims.strcat _130_128 ")"))) r.extracted_fn_name args)))
end)
end)
end)
end
| _64_311 -> begin
(FStar_All.failwith "Expected wysteria lib fn to be a MLE_Name")
end)
end))

let extract_mllb = (fun _64_314 -> (match (_64_314) with
| (b, l) -> begin
(match (((FStar_List.length l) <> 1)) with
| true -> begin
(FStar_All.failwith "Mutually recursive lets are not yet suppored")
end
| false -> begin
(let lb = (FStar_List.hd l)
in (let lbname = (FStar_Extraction_ML_Syntax.idsym lb.FStar_Extraction_ML_Syntax.mllb_name)
in (let lbbody = lb.FStar_Extraction_ML_Syntax.mllb_def
in (match (b) with
| true -> begin
(match (lbbody.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Fun (bs, e) -> begin
(let _64_324 = (let _130_132 = (FStar_List.hd bs)
in (let _130_131 = (FStar_List.tl bs)
in (_130_132, _130_131)))
in (match (_64_324) with
| (first_b, rest_bs) -> begin
(let body_exp = (extract_mlexp e)
in (let tl_abs_exp = (FStar_List.fold_left (fun e _64_330 -> (match (_64_330) with
| (bname, _64_329) -> begin
(Prims.strcat (Prims.strcat (Prims.strcat (Prims.strcat "mk_abs " (name_to_string (FStar_Extraction_ML_Syntax.idsym bname))) " (") e) ")")
end)) body_exp (FStar_List.rev rest_bs))
in (let fix_exp = (Prims.strcat (Prims.strcat (Prims.strcat (Prims.strcat (Prims.strcat (Prims.strcat "mk_fix " (name_to_string lbname)) " ") (name_to_string (FStar_Extraction_ML_Syntax.idsym (Prims.fst first_b)))) " (") tl_abs_exp) ")")
in Mk_tlet ((lbname, fix_exp)))))
end))
end
| _64_334 -> begin
(FStar_All.failwith "Recursive let binding is not an abstraction ?")
end)
end
| false -> begin
(let _130_136 = (let _130_135 = (extract_mlexp lbbody)
in (lbname, _130_135))
in Mk_tlet (_130_136))
end))))
end)
end))

let extract_mlmodule = (fun m -> (FStar_List.fold_left (fun _64_338 tld -> (match (_64_338) with
| (l, top_opt) -> begin
(match (tld) with
| FStar_Extraction_ML_Syntax.MLM_Ty (_64_341) -> begin
(l, top_opt)
end
| FStar_Extraction_ML_Syntax.MLM_Exn (_64_344) -> begin
(FStar_All.failwith "Cannot extract an exception")
end
| FStar_Extraction_ML_Syntax.MLM_Let (lb) -> begin
(let _130_143 = (let _130_142 = (let _130_141 = (extract_mllb lb)
in (_130_141)::[])
in (FStar_List.append l _130_142))
in (_130_143, top_opt))
end
| FStar_Extraction_ML_Syntax.MLM_Top (e) -> begin
(match (top_opt) with
| None -> begin
(let _130_145 = (let _130_144 = (extract_mlexp e)
in Some (_130_144))
in (l, _130_145))
end
| Some (_64_352) -> begin
(FStar_All.failwith "Impossible: more than one top expressions")
end)
end)
end)) ([], None) m))

let rec find_smc_module = (fun mllibs -> (let rec find_smc_module' = (fun mllib -> (match (mllib) with
| [] -> begin
None
end
| (x, mlsig_opt, FStar_Extraction_ML_Syntax.MLLib (mllib'))::tl -> begin
(match ((x = "SMC")) with
| true -> begin
(match (mlsig_opt) with
| Some (_64_366, m) -> begin
Some (m)
end
| None -> begin
(Prims.raise (FStar_Util.NYI ("Found the SMC module name but no module")))
end)
end
| false -> begin
(let m_opt = (find_smc_module' mllib')
in (match (m_opt) with
| Some (m) -> begin
Some (m)
end
| None -> begin
(find_smc_module' tl)
end))
end)
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

let extract = (fun l en -> (let _64_386 = (initialize ())
in (let _64_390 = (let _130_154 = (FStar_Extraction_ML_Env.mkContext en)
in (FStar_Util.fold_map FStar_Extraction_ML_ExtractMod.extract _130_154 l))
in (match (_64_390) with
| (c, mllibs) -> begin
(let mllibs = (FStar_List.flatten mllibs)
in (let m = (find_smc_module mllibs)
in (let _64_395 = (extract_mlmodule m)
in (match (_64_395) with
| (l, m_opt) -> begin
(match (m_opt) with
| None -> begin
(FStar_All.failwith "End of SMC module, no top level expression")
end
| Some (m) -> begin
(let s = (FStar_List.fold_left (fun acc _64_403 -> (match (_64_403) with
| Mk_tlet (n, b) -> begin
(Prims.strcat (Prims.strcat (Prims.strcat (Prims.strcat (Prims.strcat (Prims.strcat "mk_let " (name_to_string n)) " (") b) ") (") acc) ")")
end)) m (FStar_List.rev l))
in (let _64_405 = (FStar_Util.print_string s)
in (FStar_Util.print_string "\n")))
end)
end))))
end))))




