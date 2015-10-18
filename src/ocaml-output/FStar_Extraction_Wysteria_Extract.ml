
open Prims
exception NYI of (Prims.string)

let is_NYI = (fun _discr_ -> (match (_discr_) with
| NYI (_) -> begin
true
end
| _ -> begin
false
end))

let ___NYI____0 = (fun projectee -> (match (projectee) with
| NYI (_64_2) -> begin
_64_2
end))

type ffi_type_s =
{module_name : Prims.string; type_name : Prims.string; slice_fn_n : Prims.string; compose_fn_n : Prims.string; slice_sps_fn_n : Prims.string}

let is_Mkffi_type_s = (Obj.magic (fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkffi_type_s")))

let slice_id = "slice_id"

let compose_ids = "compose_ids"

let slice_id_sps = "slice_id_sps"

let ffi_types = ({module_name = "Prims"; type_name = "int"; slice_fn_n = slice_id; compose_fn_n = compose_ids; slice_sps_fn_n = slice_id_sps})::({module_name = "Prims"; type_name = "nat"; slice_fn_n = slice_id; compose_fn_n = compose_ids; slice_sps_fn_n = slice_id_sps})::({module_name = "Prims"; type_name = "list"; slice_fn_n = "slice_list"; compose_fn_n = "compose_lists"; slice_sps_fn_n = "slice_list_sps"})::({module_name = "Prims"; type_name = "option"; slice_fn_n = "slice_option"; compose_fn_n = "compose_options"; slice_sps_fn_n = "slice_option_sps"})::({module_name = "Prims"; type_name = "Tuple2"; slice_fn_n = "slice_tuple"; compose_fn_n = "compose_tuples"; slice_sps_fn_n = "slice_tuple_sps"})::[]

let mk_fn_exp = (fun s -> (FStar_Absyn_Syntax.mk_Exp_fvar ({FStar_Absyn_Syntax.v = {FStar_Absyn_Syntax.ns = []; FStar_Absyn_Syntax.ident = {FStar_Absyn_Syntax.idText = s; FStar_Absyn_Syntax.idRange = FStar_Absyn_Syntax.dummyRange}; FStar_Absyn_Syntax.nsstr = ""; FStar_Absyn_Syntax.str = s}; FStar_Absyn_Syntax.sort = FStar_Absyn_Syntax.mk_Typ_unknown; FStar_Absyn_Syntax.p = FStar_Absyn_Syntax.dummyRange}, None) None FStar_Absyn_Syntax.dummyRange))

let slice_value_exp = (mk_fn_exp "Semantics.slice_v_ffi")

let slice_value_sps_exp = (mk_fn_exp "Semantics.slice_v_sps_ffi")

let compose_values_exp = (mk_fn_exp "Semantics.compose_vals_ffi")

type fn_mapping =
{slice_fn : FStar_Absyn_Syntax.exp; compose_fn : FStar_Absyn_Syntax.exp; slice_sps_fn : FStar_Absyn_Syntax.exp}

let is_Mkfn_mapping = (Obj.magic (fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkfn_mapping")))

let fn_map = (FStar_Util.smap_create (FStar_List.length ffi_types))

let initialize = (fun _64_14 -> (FStar_List.iter (fun r -> (let n = (Prims.strcat (Prims.strcat r.module_name ".") r.type_name)
in (let fns = (let _130_39 = (mk_fn_exp r.slice_fn_n)
in (let _130_38 = (mk_fn_exp r.compose_fn_n)
in (let _130_37 = (mk_fn_exp r.slice_sps_fn_n)
in {slice_fn = _130_39; compose_fn = _130_38; slice_sps_fn = _130_37})))
in (FStar_Util.smap_add fn_map n fns)))) ffi_types))

let rec pre_process_t = (fun t -> (let t' = (FStar_Absyn_Util.compress_typ t)
in (match (t'.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_refine (xt, _64_23) -> begin
(pre_process_t xt.FStar_Absyn_Syntax.sort)
end
| _64_27 -> begin
t'
end)))

let is_bool = (fun t -> (match ((let _130_44 = (pre_process_t t)
in _130_44.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_const (ftv) -> begin
(ftv.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.str = "Prims.bool")
end
| _64_32 -> begin
false
end))

let is_unit = (fun t -> (match ((let _130_47 = (pre_process_t t)
in _130_47.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_const (ftv) -> begin
(ftv.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.str = "Prims.unit")
end
| _64_37 -> begin
false
end))

let is_prin = (fun t -> (match ((let _130_50 = (pre_process_t t)
in _130_50.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_const (ftv) -> begin
(ftv.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.str = "Prins.prin")
end
| _64_42 -> begin
false
end))

let is_ordset = (fun t -> (match ((let _130_53 = (pre_process_t t)
in _130_53.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_const (ftv) -> begin
(ftv.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.str = "FStar.OrdSet.ordset")
end
| _64_47 -> begin
false
end))

let is_p_cmp = (fun e -> (match ((let _130_56 = (FStar_Absyn_Util.compress_exp e)
in _130_56.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_fvar (fvv, _64_51) -> begin
(fvv.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.str = "Prins.p_cmp")
end
| _64_55 -> begin
false
end))

let is_prins = (fun t -> (match ((let _130_59 = (pre_process_t t)
in _130_59.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_app (t', (FStar_Util.Inl (t''), _64_66)::(FStar_Util.Inr (f), _64_61)::[]) -> begin
(((is_ordset t') && (is_prin t'')) && (is_p_cmp f))
end
| _64_72 -> begin
false
end))

let is_eprins = is_prins

let is_box' = (fun t -> (match ((let _130_63 = (pre_process_t t)
in _130_63.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_const (ftv) -> begin
(ftv.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.str = "Wysteria.Box")
end
| _64_77 -> begin
false
end))

let is_box = (fun t -> (match ((let _130_66 = (pre_process_t t)
in _130_66.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_app (t', _64_81) -> begin
(is_box' t')
end
| _64_85 -> begin
false
end))

let is_wire' = (fun t -> (match ((let _130_69 = (pre_process_t t)
in _130_69.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_const (ftv) -> begin
(ftv.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.str = "Wysteria.Wire")
end
| _64_90 -> begin
false
end))

let is_wire = (fun t -> (match ((let _130_72 = (pre_process_t t)
in _130_72.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_app (t', _64_94) -> begin
(is_wire' t')
end
| _64_98 -> begin
false
end))

let is_wysteria_type = (fun t -> (((((is_prin t) || (is_prins t)) || (is_eprins t)) || (is_box t)) || (is_wire t)))

let lookup_ffi_map = (fun t -> (let m = (FStar_Util.smap_try_find fn_map t)
in (match (m) with
| Some (m) -> begin
(m.slice_fn, m.compose_fn, m.slice_sps_fn)
end
| _64_105 -> begin
(let _64_106 = (FStar_Util.print_string (Prims.strcat "Error in looking up ffi type: " t))
in (Prims.raise (NYI ((Prims.strcat "Error in looking up ffi type: " t)))))
end)))

let rec get_opaque_fns = (fun t -> (match ((((((is_bool t) || (is_unit t)) || (is_prin t)) || (is_prins t)) || (is_eprins t))) with
| true -> begin
(let _130_81 = (mk_fn_exp slice_id)
in (let _130_80 = (mk_fn_exp compose_ids)
in (let _130_79 = (mk_fn_exp slice_id_sps)
in (_130_81, _130_80, _130_79))))
end
| false -> begin
(match (((is_box t) || (is_wire t))) with
| true -> begin
(slice_value_exp, compose_values_exp, slice_value_sps_exp)
end
| false -> begin
(match ((let _130_82 = (pre_process_t t)
in _130_82.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_const (ftv) -> begin
(lookup_ffi_map ftv.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.str)
end
| FStar_Absyn_Syntax.Typ_app (t, args) -> begin
(let _64_118 = (get_opaque_fns t)
in (match (_64_118) with
| (e1, e2, e3) -> begin
(FStar_List.fold_left (fun _64_122 arg -> (match (_64_122) with
| (acc1, acc2, acc3) -> begin
(match (arg) with
| (FStar_Util.Inl (t'), _64_127) -> begin
(let _64_132 = (get_opaque_fns t')
in (match (_64_132) with
| (e1', e2', e3') -> begin
(let _64_136 = ((FStar_Util.Inr (e1'), None), (FStar_Util.Inr (e2'), None), (FStar_Util.Inr (e3'), None))
in (match (_64_136) with
| (e1'_arg, e2'_arg, e3'_arg) -> begin
(let _130_87 = (FStar_Absyn_Syntax.mk_Exp_app (acc1, (e1'_arg)::[]) None FStar_Absyn_Syntax.dummyRange)
in (let _130_86 = (FStar_Absyn_Syntax.mk_Exp_app (acc2, (e2'_arg)::[]) None FStar_Absyn_Syntax.dummyRange)
in (let _130_85 = (FStar_Absyn_Syntax.mk_Exp_app (acc3, (e3'_arg)::[]) None FStar_Absyn_Syntax.dummyRange)
in (_130_87, _130_86, _130_85))))
end))
end))
end
| _64_138 -> begin
(Prims.raise (NYI ("Unexpected type argument: an expression")))
end)
end)) (e1, e2, e3) args)
end))
end
| _64_140 -> begin
(Prims.raise (NYI ("Unexpected type in get slice fn")))
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
(match ((is_prins t)) with
| true -> begin
"D_v (const_meta, V_prins x)"
end
| false -> begin
(match ((is_eprins t)) with
| true -> begin
"D_v (const_meta, V_eprins x)"
end
| false -> begin
(match (((is_box t) || (is_wire t))) with
| true -> begin
"x"
end
| false -> begin
(let _64_146 = (get_opaque_fns t)
in (match (_64_146) with
| (e1, e2, e3) -> begin
(let _64_150 = (let _130_92 = (FStar_Absyn_Print.exp_to_string e1)
in (let _130_91 = (FStar_Absyn_Print.exp_to_string e2)
in (let _130_90 = (FStar_Absyn_Print.exp_to_string e3)
in (_130_92, _130_91, _130_90))))
in (match (_64_150) with
| (s1, s2, s3) -> begin
(Prims.strcat (Prims.strcat (Prims.strcat (Prims.strcat (Prims.strcat "mk_v_opaque x " s1) " ") s2) " ") s3)
end))
end))
end)
end)
end)
end)
end)
end)
in (Prims.strcat s s'))))

let filter_out_type_binders = (fun _66_95 -> (FStar_List.filter (fun a -> (match (a) with
| (FStar_Util.Inl (_64_154), _64_157) -> begin
false
end
| (FStar_Util.Inr (_64_160), _64_163) -> begin
true
end))))

let filter_out_type_args = (fun _66_95 -> (FStar_List.filter (fun a -> (match (a) with
| (FStar_Util.Inl (_64_167), _64_170) -> begin
false
end
| (FStar_Util.Inr (_64_173), _64_176) -> begin
true
end))))

let name_to_string = (fun s -> (Prims.strcat (Prims.strcat "\"" s) "\""))

let extract_binder = (fun b -> (match (b) with
| (FStar_Util.Inl (_64_181), _64_184) -> begin
(Prims.raise (NYI ("Extract binder cannot extract type arguments")))
end
| (FStar_Util.Inr (bvar), _64_189) -> begin
(name_to_string bvar.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ppname.FStar_Absyn_Syntax.idText)
end))

let extract_const = (fun c -> (match (c) with
| FStar_Absyn_Syntax.Const_unit -> begin
"C_unit ()"
end
| FStar_Absyn_Syntax.Const_bool (b) -> begin
(Prims.strcat "C_bool " (match (b) with
| true -> begin
"true"
end
| false -> begin
"false"
end))
end
| FStar_Absyn_Syntax.Const_int32 (n) -> begin
(Prims.strcat (Prims.strcat "C_opaque ((), Obj.magic " (FStar_Util.string_of_int32 n)) ")")
end
| FStar_Absyn_Syntax.Const_int (x) -> begin
(Prims.strcat (Prims.strcat "C_opaque ((), Obj.magic " x) ")")
end
| _64_200 -> begin
(Prims.raise (NYI ("Extract constant cannot extract the constant")))
end))

let typ_of_exp = (fun e -> (let t' = (let _130_106 = (let _130_105 = (FStar_Absyn_Util.compress_exp e)
in _130_105.FStar_Absyn_Syntax.tk)
in (FStar_ST.read _130_106))
in (match (t') with
| Some (t) -> begin
t
end
| _64_206 -> begin
(Prims.raise (NYI ("Type of FFI call not set!")))
end)))

let is_ffi = (fun e -> (match ((let _130_109 = (FStar_Absyn_Util.compress_exp e)
in _130_109.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_fvar (fvv, _64_210) -> begin
(match (((FStar_Util.starts_with fvv.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.str "FFI.") || (FStar_Util.starts_with fvv.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.str "Prims."))) with
| true -> begin
(true, fvv.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.str)
end
| false -> begin
(false, "")
end)
end
| _64_214 -> begin
(false, "")
end))

let check_pats_for_bool = (fun l -> (let c_unit = (FStar_Absyn_Syntax.mk_Exp_constant FStar_Absyn_Syntax.Const_unit None FStar_Absyn_Syntax.dummyRange)
in (let def = (false, c_unit, c_unit)
in (match (((FStar_List.length l) <> 2)) with
| true -> begin
def
end
| false -> begin
(let _64_222 = (FStar_List.hd l)
in (match (_64_222) with
| (p1, _64_220, e1) -> begin
(let _64_227 = (let _130_112 = (FStar_List.tl l)
in (FStar_List.hd _130_112))
in (match (_64_227) with
| (p2, _64_225, e2) -> begin
(match ((p1.FStar_Absyn_Syntax.v, p2.FStar_Absyn_Syntax.v)) with
| (FStar_Absyn_Syntax.Pat_constant (FStar_Absyn_Syntax.Const_bool (_64_229)), FStar_Absyn_Syntax.Pat_constant (FStar_Absyn_Syntax.Const_bool (_64_233))) -> begin
(true, e1, e2)
end
| _64_238 -> begin
def
end)
end))
end))
end))))

let rec extract_exp = (fun e en -> (match ((let _130_125 = (FStar_Absyn_Util.compress_exp e)
in _130_125.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_bvar (bvar) -> begin
(Prims.strcat "mk_var " (name_to_string bvar.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ppname.FStar_Absyn_Syntax.idText))
end
| FStar_Absyn_Syntax.Exp_fvar (fvar, _64_245) -> begin
(Prims.strcat "mk_var " (name_to_string fvar.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ident.FStar_Absyn_Syntax.idText))
end
| FStar_Absyn_Syntax.Exp_constant (c) -> begin
(let _130_127 = (let _130_126 = (extract_const c)
in (Prims.strcat "mk_const (" _130_126))
in (Prims.strcat _130_127 ")"))
end
| FStar_Absyn_Syntax.Exp_abs (bs, e) -> begin
(let body_str = (extract_exp e en)
in (let bs = ((filter_out_type_binders ()) bs)
in (FStar_List.fold_left (fun s b -> (let _130_133 = (let _130_132 = (let _130_131 = (let _130_130 = (extract_binder b)
in (Prims.strcat "mk_abs " _130_130))
in (Prims.strcat _130_131 " ("))
in (Prims.strcat _130_132 s))
in (Prims.strcat _130_133 ")"))) body_str (FStar_List.rev bs))))
end
| FStar_Absyn_Syntax.Exp_app (e', args) -> begin
(let args = ((filter_out_type_args ()) args)
in (let _64_265 = (is_ffi e')
in (match (_64_265) with
| (b, ffi) -> begin
(match (b) with
| true -> begin
(let t = (let _130_134 = (typ_of_exp e)
in (FStar_Tc_Normalize.normalize en _130_134))
in (let inj = (get_injection t)
in (let args_str = (FStar_List.fold_left (fun s a -> (let _130_138 = (let _130_137 = (extract_arg a en)
in (Prims.strcat (Prims.strcat s " (") _130_137))
in (Prims.strcat _130_138 ");"))) "" args)
in (let _130_146 = (let _130_145 = (let _130_144 = (let _130_143 = (let _130_142 = (let _130_141 = (let _130_140 = (let _130_139 = (FStar_Util.string_of_int (FStar_List.length args))
in (Prims.strcat "mk_ffi " _130_139))
in (Prims.strcat _130_140 " ("))
in (Prims.strcat _130_141 ffi))
in (Prims.strcat _130_142 ") [ "))
in (Prims.strcat _130_143 args_str))
in (Prims.strcat _130_144 " ] ("))
in (Prims.strcat _130_145 inj))
in (Prims.strcat _130_146 ")")))))
end
| false -> begin
(let s = (extract_exp e' en)
in (let _64_274 = (extract_wysteria_specific_ast s args e en)
in (match (_64_274) with
| (b, s') -> begin
(match (b) with
| true -> begin
s'
end
| false -> begin
(match ((s = "_assert")) with
| true -> begin
"mk_const (C_unit ())"
end
| false -> begin
(FStar_List.fold_left (fun s a -> (let _130_150 = (let _130_149 = (extract_arg a en)
in (Prims.strcat (Prims.strcat (Prims.strcat "mk_app (" s) ") (") _130_149))
in (Prims.strcat _130_150 ")"))) s args)
end)
end)
end)))
end)
end)))
end
| FStar_Absyn_Syntax.Exp_match (e, pats) -> begin
(let _64_284 = (check_pats_for_bool pats)
in (match (_64_284) with
| (b, e1, e2) -> begin
(match (b) with
| true -> begin
(let _130_158 = (let _130_157 = (let _130_155 = (let _130_154 = (let _130_152 = (let _130_151 = (extract_exp e en)
in (Prims.strcat "mk_cond (" _130_151))
in (Prims.strcat _130_152 ") ("))
in (let _130_153 = (extract_exp e1 en)
in (Prims.strcat _130_154 _130_153)))
in (Prims.strcat _130_155 ") ("))
in (let _130_156 = (extract_exp e2 en)
in (Prims.strcat _130_157 _130_156)))
in (Prims.strcat _130_158 ")"))
end
| false -> begin
(Prims.raise (NYI ("Only boolean patterns are supported")))
end)
end))
end
| FStar_Absyn_Syntax.Exp_ascribed (e, _64_287, _64_289) -> begin
(extract_exp e en)
end
| FStar_Absyn_Syntax.Exp_let (lbs, e) -> begin
(match ((Prims.fst lbs)) with
| true -> begin
(Prims.raise (NYI ("Recursive let not expected (only top level)")))
end
| false -> begin
(let lb = (FStar_List.hd (Prims.snd lbs))
in (let _130_167 = (let _130_166 = (let _130_164 = (let _130_163 = (let _130_161 = (let _130_160 = (let _130_159 = (FStar_Absyn_Print.lbname_to_string lb.FStar_Absyn_Syntax.lbname)
in (name_to_string _130_159))
in (Prims.strcat "mk_let " _130_160))
in (Prims.strcat _130_161 " ("))
in (let _130_162 = (extract_exp lb.FStar_Absyn_Syntax.lbdef en)
in (Prims.strcat _130_163 _130_162)))
in (Prims.strcat _130_164 ") ("))
in (let _130_165 = (extract_exp e en)
in (Prims.strcat _130_166 _130_165)))
in (Prims.strcat _130_167 ")")))
end)
end
| _64_298 -> begin
(let _64_299 = (let _130_169 = (let _130_168 = (FStar_Absyn_Print.tag_of_exp e)
in (Prims.strcat "Expression not expected " _130_168))
in (FStar_Util.print_string _130_169))
in (Prims.raise (NYI (""))))
end))
and extract_wysteria_specific_ast = (fun s args e en -> (match ((s = "mk_var \"main\"")) with
| true -> begin
(let f = (let _130_174 = (FStar_List.tl args)
in (FStar_List.hd _130_174))
in (let s = (match (f) with
| (FStar_Util.Inl (_64_307), _64_310) -> begin
(Prims.raise (NYI ("Main 2nd argument not expected to be a type argument")))
end
| (FStar_Util.Inr (f), _64_315) -> begin
(let _130_179 = (let _130_178 = (let _130_177 = (let _130_176 = (let _130_175 = (FStar_Absyn_Syntax.mk_Exp_constant FStar_Absyn_Syntax.Const_unit None FStar_Absyn_Syntax.dummyRange)
in (FStar_Absyn_Syntax.varg _130_175))
in (_130_176)::[])
in (f, _130_177))
in (FStar_Absyn_Syntax.mk_Exp_app _130_178 None FStar_Absyn_Syntax.dummyRange))
in (extract_exp _130_179 en))
end)
in (true, s)))
end
| false -> begin
(match (s) with
| "mk_var \"as_par\"" -> begin
(let a1 = (FStar_List.hd args)
in (let a2 = (let _130_180 = (FStar_List.tl args)
in (FStar_List.hd _130_180))
in (let _130_186 = (let _130_185 = (let _130_184 = (let _130_182 = (let _130_181 = (extract_arg a1 en)
in (Prims.strcat "mk_aspar (" _130_181))
in (Prims.strcat _130_182 ") ("))
in (let _130_183 = (extract_arg a2 en)
in (Prims.strcat _130_184 _130_183)))
in (Prims.strcat _130_185 ")"))
in (true, _130_186))))
end
| "mk_var \"as_sec\"" -> begin
(let a1 = (FStar_List.hd args)
in (let a2 = (let _130_187 = (FStar_List.tl args)
in (FStar_List.hd _130_187))
in (let _130_193 = (let _130_192 = (let _130_191 = (let _130_189 = (let _130_188 = (extract_arg a1 en)
in (Prims.strcat "mk_assec (" _130_188))
in (Prims.strcat _130_189 ") ("))
in (let _130_190 = (extract_arg a2 en)
in (Prims.strcat _130_191 _130_190)))
in (Prims.strcat _130_192 ")"))
in (true, _130_193))))
end
| "mk_var \"box\"" -> begin
(let a1 = (FStar_List.hd args)
in (let a2 = (let _130_194 = (FStar_List.tl args)
in (FStar_List.hd _130_194))
in (let _130_200 = (let _130_199 = (let _130_198 = (let _130_196 = (let _130_195 = (extract_arg a1 en)
in (Prims.strcat "mk_box (" _130_195))
in (Prims.strcat _130_196 ") ("))
in (let _130_197 = (extract_arg a2 en)
in (Prims.strcat _130_198 _130_197)))
in (Prims.strcat _130_199 ")"))
in (true, _130_200))))
end
| ("mk_var \"unbox_p\"") | ("mk_var \"unbox_s\"") -> begin
(let a = (let _130_201 = (FStar_List.tl args)
in (FStar_List.hd _130_201))
in (let _130_204 = (let _130_203 = (let _130_202 = (extract_arg a en)
in (Prims.strcat "mk_unbox (" _130_202))
in (Prims.strcat _130_203 ")"))
in (true, _130_204)))
end
| "mk_var \"mkwire_s\"" -> begin
(let a1 = (FStar_List.hd args)
in (let a2 = (let _130_205 = (FStar_List.tl args)
in (FStar_List.hd _130_205))
in (let _130_211 = (let _130_210 = (let _130_209 = (let _130_207 = (let _130_206 = (extract_arg a1 en)
in (Prims.strcat "mk_mkwire (" _130_206))
in (Prims.strcat _130_207 ") ("))
in (let _130_208 = (extract_arg a2 en)
in (Prims.strcat _130_209 _130_208)))
in (Prims.strcat _130_210 ")"))
in (true, _130_211))))
end
| "mk_var \"mkwire_p\"" -> begin
(let a1 = (let _130_212 = (FStar_List.tl args)
in (FStar_List.hd _130_212))
in (let a2 = (let _130_214 = (let _130_213 = (FStar_List.tl args)
in (FStar_List.tl _130_213))
in (FStar_List.hd _130_214))
in (let _130_220 = (let _130_219 = (let _130_218 = (let _130_216 = (let _130_215 = (extract_arg a1 en)
in (Prims.strcat "mk_mkwire (" _130_215))
in (Prims.strcat _130_216 ") ("))
in (let _130_217 = (extract_arg a2 en)
in (Prims.strcat _130_218 _130_217)))
in (Prims.strcat _130_219 ")"))
in (true, _130_220))))
end
| ("mk_var \"projwire_p\"") | ("mk_var \"projwire_s\"") -> begin
(let a1 = (let _130_221 = (FStar_List.tl args)
in (FStar_List.hd _130_221))
in (let a2 = (let _130_223 = (let _130_222 = (FStar_List.tl args)
in (FStar_List.tl _130_222))
in (FStar_List.hd _130_223))
in (let _130_229 = (let _130_228 = (let _130_227 = (let _130_225 = (let _130_224 = (extract_arg a1 en)
in (Prims.strcat "mk_projwire (" _130_224))
in (Prims.strcat _130_225 ") ("))
in (let _130_226 = (extract_arg a2 en)
in (Prims.strcat _130_227 _130_226)))
in (Prims.strcat _130_228 ")"))
in (true, _130_229))))
end
| "mk_var \"concat_wire\"" -> begin
(let a1 = (let _130_231 = (let _130_230 = (FStar_List.tl args)
in (FStar_List.tl _130_230))
in (FStar_List.hd _130_231))
in (let a2 = (let _130_234 = (let _130_233 = (let _130_232 = (FStar_List.tl args)
in (FStar_List.tl _130_232))
in (FStar_List.tl _130_233))
in (FStar_List.hd _130_234))
in (let _130_240 = (let _130_239 = (let _130_238 = (let _130_236 = (let _130_235 = (extract_arg a1 en)
in (Prims.strcat "mk_concatwire (" _130_235))
in (Prims.strcat _130_236 ") ("))
in (let _130_237 = (extract_arg a2 en)
in (Prims.strcat _130_238 _130_237)))
in (Prims.strcat _130_239 ")"))
in (true, _130_240))))
end
| "mk_var \"w_read_int\"" -> begin
(let t = (let _130_241 = (typ_of_exp e)
in (FStar_Tc_Normalize.normalize en _130_241))
in (let inj_str = (get_injection t)
in (true, (Prims.strcat (Prims.strcat "mk_ffi 1 FFI.read_int [ E_const (C_unit ()) ] (" inj_str) ")"))))
end
| "mk_var \"w_read_int_tuple\"" -> begin
(let t = (let _130_242 = (typ_of_exp e)
in (FStar_Tc_Normalize.normalize en _130_242))
in (let inj_str = (get_injection t)
in (true, (Prims.strcat (Prims.strcat "mk_ffi 1 FFI.read_int_tuple [ E_const (C_unit ()) ] (" inj_str) ")"))))
end
| _64_350 -> begin
(false, "")
end)
end))
and extract_arg = (fun a en -> (match (a) with
| (FStar_Util.Inl (_64_354), _64_357) -> begin
(Prims.raise (NYI ("Extract argument cannot extract type arguments")))
end
| (FStar_Util.Inr (e), _64_362) -> begin
(extract_exp e en)
end))
and extract_sigelt = (fun s en -> (match (s) with
| FStar_Absyn_Syntax.Sig_let (lbs, _64_368, _64_370, _64_372) -> begin
(match ((Prims.fst lbs)) with
| true -> begin
(match (((FStar_List.length (Prims.snd lbs)) <> 1)) with
| true -> begin
(Prims.raise (NYI ("Mutually recursive lets not supported")))
end
| false -> begin
(let lb = (FStar_List.hd (Prims.snd lbs))
in (let lbname = (FStar_Absyn_Print.lbname_to_string lb.FStar_Absyn_Syntax.lbname)
in (let filter_ascription = (fun e -> (match ((let _130_249 = (FStar_Absyn_Util.compress_exp e)
in _130_249.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_ascribed (e, _64_381, _64_383) -> begin
e
end
| _64_387 -> begin
e
end))
in (let lb_body = (filter_ascription lb.FStar_Absyn_Syntax.lbdef)
in (match ((let _130_250 = (FStar_Absyn_Util.compress_exp lb_body)
in _130_250.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_abs (bs, e) -> begin
(let bs = (FStar_List.filter (fun a -> (match (a) with
| (FStar_Util.Inl (_64_395), _64_398) -> begin
false
end
| (FStar_Util.Inr (_64_401), _64_404) -> begin
true
end)) bs)
in (let first_b = (FStar_List.hd bs)
in (let rest_bs = (FStar_List.tl bs)
in (let body_str = (extract_exp e en)
in (let tl_abs_str = (FStar_List.fold_left (fun s b -> (let _130_257 = (let _130_256 = (let _130_255 = (let _130_254 = (extract_binder b)
in (Prims.strcat "mk_abs " _130_254))
in (Prims.strcat _130_255 " ("))
in (Prims.strcat _130_256 s))
in (Prims.strcat _130_257 ")"))) body_str (FStar_List.rev rest_bs))
in (let fix_str = (let _130_261 = (let _130_260 = (let _130_259 = (let _130_258 = (extract_binder first_b)
in (Prims.strcat (Prims.strcat (Prims.strcat "mk_fix " (name_to_string lbname)) " ") _130_258))
in (Prims.strcat _130_259 " ("))
in (Prims.strcat _130_260 tl_abs_str))
in (Prims.strcat _130_261 ")"))
in (let let_str = (Prims.strcat (Prims.strcat (Prims.strcat (Prims.strcat "mk_let " (name_to_string lbname)) " (") fix_str) ")")
in let_str)))))))
end
| _64_416 -> begin
(Prims.raise (NYI ("Expected an abs with recursive let")))
end)))))
end)
end
| false -> begin
(let lb = (FStar_List.hd (Prims.snd lbs))
in (let _130_267 = (let _130_266 = (let _130_264 = (let _130_263 = (let _130_262 = (FStar_Absyn_Print.lbname_to_string lb.FStar_Absyn_Syntax.lbname)
in (name_to_string _130_262))
in (Prims.strcat "mk_let " _130_263))
in (Prims.strcat _130_264 " ("))
in (let _130_265 = (extract_exp lb.FStar_Absyn_Syntax.lbdef en)
in (Prims.strcat _130_266 _130_265)))
in (Prims.strcat _130_267 ")")))
end)
end
| FStar_Absyn_Syntax.Sig_main (e, _64_420) -> begin
(extract_exp e en)
end
| _64_424 -> begin
""
end))

let extract_main = (fun s en -> (match (s) with
| FStar_Absyn_Syntax.Sig_main (e, _64_429) -> begin
(extract_exp e en)
end
| _64_433 -> begin
(Prims.raise (NYI ("Extract main got some other sigelt!")))
end))

let extract_sigelts = (fun l en -> (let l = (FStar_List.rev l)
in (let main_str = (let _130_276 = (FStar_List.hd l)
in (extract_main _130_276 en))
in (let _130_279 = (FStar_List.tl l)
in (FStar_List.fold_left (fun acc s -> (let s_str = (extract_sigelt s en)
in (Prims.strcat (Prims.strcat (Prims.strcat s_str " (") acc) ")"))) main_str _130_279)))))

let extract = (fun l en -> (let _64_443 = (initialize ())
in (FStar_List.iter (fun m -> (match ((m.FStar_Absyn_Syntax.name.FStar_Absyn_Syntax.str = "SMC")) with
| true -> begin
(let s = (extract_sigelts m.FStar_Absyn_Syntax.declarations en)
in (let _64_447 = (FStar_Util.print_string s)
in (FStar_Util.print_string "\n")))
end
| false -> begin
()
end)) l)))




