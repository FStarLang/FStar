
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

let is_Mkffi_type_s = (fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkffi_type_s"))

let slice_id = "slice_id"

let compose_ids = "compose_id"

let slice_id_sps = "slice_id_sps"

let ffi_types = ({module_name = "Prims"; type_name = "int"; slice_fn_n = slice_id; compose_fn_n = compose_ids; slice_sps_fn_n = slice_id_sps})::({module_name = "Prims"; type_name = "nat"; slice_fn_n = slice_id; compose_fn_n = compose_ids; slice_sps_fn_n = slice_id_sps})::({module_name = "Prims"; type_name = "bool"; slice_fn_n = slice_id; compose_fn_n = compose_ids; slice_sps_fn_n = slice_id_sps})::({module_name = "Prims"; type_name = "list"; slice_fn_n = "slice_list"; compose_fn_n = "compose_lists"; slice_sps_fn_n = "slice_list_sps"})::({module_name = "Prims"; type_name = "option"; slice_fn_n = "slice_option"; compose_fn_n = "compose_options"; slice_sps_fn_n = "slice_option_sps"})::[]

let mk_fn_exp = (fun s -> (FStar_Absyn_Syntax.mk_Exp_fvar ({FStar_Absyn_Syntax.v = {FStar_Absyn_Syntax.ns = []; FStar_Absyn_Syntax.ident = {FStar_Absyn_Syntax.idText = s; FStar_Absyn_Syntax.idRange = FStar_Absyn_Syntax.dummyRange}; FStar_Absyn_Syntax.nsstr = ""; FStar_Absyn_Syntax.str = s}; FStar_Absyn_Syntax.sort = FStar_Absyn_Syntax.mk_Typ_unknown; FStar_Absyn_Syntax.p = FStar_Absyn_Syntax.dummyRange}, None) None FStar_Absyn_Syntax.dummyRange))

let slice_value_exp = (mk_fn_exp "slice_value")

let slice_value_sps_exp = (mk_fn_exp "slice_value_sps")

let compose_values_exp = (mk_fn_exp "compose_vals")

type fn_mapping =
{slice_fn : FStar_Absyn_Syntax.exp; compose_fn : FStar_Absyn_Syntax.exp; slice_sps_fn : FStar_Absyn_Syntax.exp}

let is_Mkfn_mapping = (fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkfn_mapping"))

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

let is_unit = (fun t -> (match ((let _130_44 = (pre_process_t t)
in _130_44.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_const (ftv) -> begin
(ftv.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.str = "Prims.unit")
end
| _64_32 -> begin
false
end))

let is_prin = (fun t -> (match ((let _130_47 = (pre_process_t t)
in _130_47.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_const (ftv) -> begin
(ftv.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.str = "Prins.prin")
end
| _64_37 -> begin
false
end))

let is_ordset = (fun t -> (match ((let _130_50 = (pre_process_t t)
in _130_50.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_const (ftv) -> begin
(ftv.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.str = "FStar.OrdSet.ordset")
end
| _64_42 -> begin
false
end))

let is_p_cmp = (fun e -> (match ((let _130_53 = (FStar_Absyn_Util.compress_exp e)
in _130_53.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_fvar (fvv, _64_46) -> begin
(fvv.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.str = "Prins.p_cmp")
end
| _64_50 -> begin
false
end))

let is_prins = (fun t -> (match ((let _130_56 = (pre_process_t t)
in _130_56.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_app (t', (FStar_Util.Inl (t''), _64_61)::(FStar_Util.Inr (f), _64_56)::[]) -> begin
(((is_ordset t') && (is_prin t'')) && (is_p_cmp f))
end
| _64_67 -> begin
false
end))

let is_eprins = is_prins

let is_box' = (fun t -> (match ((let _130_60 = (pre_process_t t)
in _130_60.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_const (ftv) -> begin
(ftv.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.str = "Wysteria.Box")
end
| _64_72 -> begin
false
end))

let is_box = (fun t -> (match ((let _130_63 = (pre_process_t t)
in _130_63.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_app (t', _64_76) -> begin
(is_box' t')
end
| _64_80 -> begin
false
end))

let is_wire' = (fun t -> (match ((let _130_66 = (pre_process_t t)
in _130_66.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_const (ftv) -> begin
(ftv.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.str = "Wysteria.Wire")
end
| _64_85 -> begin
false
end))

let is_wire = (fun t -> (match ((let _130_69 = (pre_process_t t)
in _130_69.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_app (t', _64_89) -> begin
(is_wire' t')
end
| _64_93 -> begin
false
end))

let is_wysteria_type = (fun t -> (((((is_prin t) || (is_prins t)) || (is_eprins t)) || (is_box t)) || (is_wire t)))

let lookup_ffi_map = (fun t -> (let m = (FStar_Util.smap_try_find fn_map t)
in (match (m) with
| Some (m) -> begin
(m.slice_fn, m.compose_fn, m.slice_sps_fn)
end
| _64_100 -> begin
(let _64_101 = (FStar_Util.print_string (Prims.strcat "Error in looking up ffi type: " t))
in (Prims.raise (NYI ((Prims.strcat "Error in looking up ffi type: " t)))))
end)))

let rec get_opaque_fns = (fun t -> (match (((((is_unit t) || (is_prin t)) || (is_prins t)) || (is_eprins t))) with
| true -> begin
(let _130_78 = (mk_fn_exp slice_id)
in (let _130_77 = (mk_fn_exp compose_ids)
in (let _130_76 = (mk_fn_exp slice_id_sps)
in (_130_78, _130_77, _130_76))))
end
| false -> begin
(match (((is_box t) || (is_wire t))) with
| true -> begin
(slice_value_exp, compose_values_exp, slice_value_sps_exp)
end
| false -> begin
(match ((let _130_79 = (pre_process_t t)
in _130_79.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_const (ftv) -> begin
(lookup_ffi_map ftv.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.str)
end
| FStar_Absyn_Syntax.Typ_app (t, args) -> begin
(let _64_113 = (get_opaque_fns t)
in (match (_64_113) with
| (e1, e2, e3) -> begin
(FStar_List.fold_left (fun _64_117 arg -> (match (_64_117) with
| (acc1, acc2, acc3) -> begin
(match (arg) with
| (FStar_Util.Inl (t'), _64_122) -> begin
(let _64_127 = (get_opaque_fns t')
in (match (_64_127) with
| (e1', e2', e3') -> begin
(let _64_131 = ((FStar_Util.Inr (e1'), None), (FStar_Util.Inr (e2'), None), (FStar_Util.Inr (e3'), None))
in (match (_64_131) with
| (e1'_arg, e2'_arg, e3'_arg) -> begin
(let _130_84 = (FStar_Absyn_Syntax.mk_Exp_app (acc1, (e1'_arg)::[]) None FStar_Absyn_Syntax.dummyRange)
in (let _130_83 = (FStar_Absyn_Syntax.mk_Exp_app (acc2, (e2'_arg)::[]) None FStar_Absyn_Syntax.dummyRange)
in (let _130_82 = (FStar_Absyn_Syntax.mk_Exp_app (acc3, (e3'_arg)::[]) None FStar_Absyn_Syntax.dummyRange)
in (_130_84, _130_83, _130_82))))
end))
end))
end
| _64_133 -> begin
(Prims.raise (NYI ("Unexpected type argument: an expression")))
end)
end)) (e1, e2, e3) args)
end))
end
| _64_135 -> begin
(Prims.raise (NYI ("Unexpected type in get slice fn")))
end)
end)
end))

let get_injection = (fun t -> (let s = "fun x -> "
in (let s' = (match ((is_unit t)) with
| true -> begin
"V_unit"
end
| false -> begin
(match ((is_prin t)) with
| true -> begin
"V_prin x"
end
| false -> begin
(match ((is_prins t)) with
| true -> begin
"V_prins x"
end
| false -> begin
(match ((is_eprins t)) with
| true -> begin
"V_eprins x"
end
| false -> begin
(match (((is_box t) || (is_wire t))) with
| true -> begin
"x"
end
| false -> begin
(let _64_141 = (get_opaque_fns t)
in (match (_64_141) with
| (e1, e2, e3) -> begin
(let _64_145 = (let _130_89 = (FStar_Absyn_Print.exp_to_string e1)
in (let _130_88 = (FStar_Absyn_Print.exp_to_string e2)
in (let _130_87 = (FStar_Absyn_Print.exp_to_string e3)
in (_130_89, _130_88, _130_87))))
in (match (_64_145) with
| (s1, s2, s3) -> begin
(Prims.strcat (Prims.strcat (Prims.strcat (Prims.strcat (Prims.strcat (Prims.strcat "V_opaque () x" " ") s1) " ") s2) " ") s3)
end))
end))
end)
end)
end)
end)
end)
in (Prims.strcat s s'))))

let filter_out_type_binders = (fun _66_982 -> (FStar_List.filter (fun a -> (match (a) with
| (FStar_Util.Inl (_64_149), _64_152) -> begin
false
end
| (FStar_Util.Inr (_64_155), _64_158) -> begin
true
end))))

let filter_out_type_args = (fun _66_982 -> (FStar_List.filter (fun a -> (match (a) with
| (FStar_Util.Inl (_64_162), _64_165) -> begin
false
end
| (FStar_Util.Inr (_64_168), _64_171) -> begin
true
end))))

let extract_binder = (fun b -> (match (b) with
| (FStar_Util.Inl (_64_175), _64_178) -> begin
(Prims.raise (NYI ("Extract binder cannot extract type arguments")))
end
| (FStar_Util.Inr (bvar), _64_183) -> begin
bvar.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ppname.FStar_Absyn_Syntax.idText
end))

let extract_const = (fun c -> (match (c) with
| FStar_Absyn_Syntax.Const_unit -> begin
"C_unit"
end
| FStar_Absyn_Syntax.Const_bool (b) -> begin
(Prims.strcat "C_opaque " (match (b) with
| true -> begin
"true"
end
| false -> begin
"false"
end))
end
| FStar_Absyn_Syntax.Const_int32 (n) -> begin
(Prims.strcat "C_opaque " (FStar_Util.string_of_int32 n))
end
| FStar_Absyn_Syntax.Const_int (x) -> begin
(Prims.strcat "C_opaque " x)
end
| _64_194 -> begin
(Prims.raise (NYI ("Extract constant cannot extract the constant")))
end))

let typ_of_exp = (fun e -> (let t' = (let _130_101 = (let _130_100 = (FStar_Absyn_Util.compress_exp e)
in _130_100.FStar_Absyn_Syntax.tk)
in (FStar_ST.read _130_101))
in (match (t') with
| Some (t) -> begin
t
end
| _64_200 -> begin
(Prims.raise (NYI ("Type of FFI call not set!")))
end)))

let is_ffi = (fun e -> (match ((let _130_104 = (FStar_Absyn_Util.compress_exp e)
in _130_104.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_fvar (fvv, _64_204) -> begin
(match (((FStar_Util.starts_with fvv.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.str "FFI.") || (FStar_Util.starts_with fvv.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.str "Prims."))) with
| true -> begin
(true, fvv.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.str)
end
| false -> begin
(false, "")
end)
end
| _64_208 -> begin
(false, "")
end))

let check_pats_for_bool = (fun l -> (let c_unit = (FStar_Absyn_Syntax.mk_Exp_constant FStar_Absyn_Syntax.Const_unit None FStar_Absyn_Syntax.dummyRange)
in (let def = (false, c_unit, c_unit)
in (match (((FStar_List.length l) <> 2)) with
| true -> begin
def
end
| false -> begin
(let _64_216 = (FStar_List.hd l)
in (match (_64_216) with
| (p1, _64_214, e1) -> begin
(let _64_221 = (let _130_107 = (FStar_List.tl l)
in (FStar_List.hd _130_107))
in (match (_64_221) with
| (p2, _64_219, e2) -> begin
(match ((p1.FStar_Absyn_Syntax.v, p2.FStar_Absyn_Syntax.v)) with
| (FStar_Absyn_Syntax.Pat_constant (FStar_Absyn_Syntax.Const_bool (_64_223)), FStar_Absyn_Syntax.Pat_constant (FStar_Absyn_Syntax.Const_bool (_64_227))) -> begin
(true, e1, e2)
end
| _64_232 -> begin
def
end)
end))
end))
end))))

let rec extract_exp = (fun e en -> (match ((let _130_119 = (FStar_Absyn_Util.compress_exp e)
in _130_119.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_bvar (bvar) -> begin
bvar.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ppname.FStar_Absyn_Syntax.idText
end
| FStar_Absyn_Syntax.Exp_fvar (fvar, _64_239) -> begin
fvar.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ident.FStar_Absyn_Syntax.idText
end
| FStar_Absyn_Syntax.Exp_constant (c) -> begin
(extract_const c)
end
| FStar_Absyn_Syntax.Exp_abs (bs, e) -> begin
(let body_str = (extract_exp e en)
in (let bs = ((filter_out_type_binders ()) bs)
in (FStar_List.fold_left (fun s b -> (let _130_125 = (let _130_124 = (let _130_123 = (let _130_122 = (extract_binder b)
in (Prims.strcat "E_abs " _130_122))
in (Prims.strcat _130_123 " ("))
in (Prims.strcat _130_124 s))
in (Prims.strcat _130_125 ")"))) body_str (FStar_List.rev bs))))
end
| FStar_Absyn_Syntax.Exp_app (e', args) -> begin
(let args = ((filter_out_type_args ()) args)
in (let _64_259 = (is_ffi e')
in (match (_64_259) with
| (b, ffi) -> begin
(match (b) with
| true -> begin
(let t = (let _130_126 = (typ_of_exp e)
in (FStar_Tc_Normalize.normalize en _130_126))
in (let inj = (get_injection t)
in (let args_str = (FStar_List.fold_left (fun s a -> (let _130_130 = (let _130_129 = (extract_arg a en)
in (Prims.strcat (Prims.strcat s " (") _130_129))
in (Prims.strcat _130_130 ")"))) "" args)
in (let _130_138 = (let _130_137 = (let _130_136 = (let _130_135 = (let _130_134 = (let _130_133 = (let _130_132 = (let _130_131 = (FStar_Util.string_of_int (FStar_List.length args))
in (Prims.strcat "E_ffi" _130_131))
in (Prims.strcat _130_132 " (F "))
in (Prims.strcat _130_133 ffi))
in (Prims.strcat _130_134 ") "))
in (Prims.strcat _130_135 args_str))
in (Prims.strcat _130_136 " (I ("))
in (Prims.strcat _130_137 inj))
in (Prims.strcat _130_138 ")")))))
end
| false -> begin
(let s = (extract_exp e' en)
in (let _64_268 = (extract_wysteria_specific_ast s args en)
in (match (_64_268) with
| (b, s') -> begin
(match (b) with
| true -> begin
s'
end
| false -> begin
(match ((s = "_assert")) with
| true -> begin
"C_unit"
end
| false -> begin
(FStar_List.fold_left (fun s a -> (let _130_142 = (let _130_141 = (extract_arg a en)
in (Prims.strcat (Prims.strcat s " (") _130_141))
in (Prims.strcat _130_142 ")"))) s args)
end)
end)
end)))
end)
end)))
end
| FStar_Absyn_Syntax.Exp_match (e, pats) -> begin
(let _64_278 = (check_pats_for_bool pats)
in (match (_64_278) with
| (b, e1, e2) -> begin
(match (b) with
| true -> begin
(let _130_150 = (let _130_149 = (let _130_147 = (let _130_146 = (let _130_144 = (let _130_143 = (extract_exp e en)
in (Prims.strcat "E_cond (" _130_143))
in (Prims.strcat _130_144 ") ("))
in (let _130_145 = (extract_exp e1 en)
in (Prims.strcat _130_146 _130_145)))
in (Prims.strcat _130_147 ") ("))
in (let _130_148 = (extract_exp e2 en)
in (Prims.strcat _130_149 _130_148)))
in (Prims.strcat _130_150 ")"))
end
| false -> begin
(Prims.raise (NYI ("Only boolean patterns are supported")))
end)
end))
end
| FStar_Absyn_Syntax.Exp_ascribed (e, _64_281, _64_283) -> begin
(extract_exp e en)
end
| FStar_Absyn_Syntax.Exp_let (lbs, e) -> begin
(match ((Prims.fst lbs)) with
| true -> begin
(Prims.raise (NYI ("Recursive let not expected (only top level)")))
end
| false -> begin
(let lb = (FStar_List.hd (Prims.snd lbs))
in (let _130_158 = (let _130_157 = (let _130_155 = (let _130_154 = (let _130_152 = (let _130_151 = (FStar_Absyn_Print.lbname_to_string lb.FStar_Absyn_Syntax.lbname)
in (Prims.strcat "E_let " _130_151))
in (Prims.strcat _130_152 " ("))
in (let _130_153 = (extract_exp lb.FStar_Absyn_Syntax.lbdef en)
in (Prims.strcat _130_154 _130_153)))
in (Prims.strcat _130_155 ") ("))
in (let _130_156 = (extract_exp e en)
in (Prims.strcat _130_157 _130_156)))
in (Prims.strcat _130_158 ")")))
end)
end
| _64_292 -> begin
(let _64_293 = (let _130_160 = (let _130_159 = (FStar_Absyn_Print.tag_of_exp e)
in (Prims.strcat "Expression not expected " _130_159))
in (FStar_Util.print_string _130_160))
in (Prims.raise (NYI (""))))
end))
and extract_wysteria_specific_ast = (fun s args en -> (match ((s = "main")) with
| true -> begin
(let f = (let _130_164 = (FStar_List.tl args)
in (FStar_List.hd _130_164))
in (let s = (match (f) with
| (FStar_Util.Inl (_64_300), _64_303) -> begin
(Prims.raise (NYI ("Main 2nd argument not expected to be a type argument")))
end
| (FStar_Util.Inr (f), _64_308) -> begin
(let _130_169 = (let _130_168 = (let _130_167 = (let _130_166 = (let _130_165 = (FStar_Absyn_Syntax.mk_Exp_constant FStar_Absyn_Syntax.Const_unit None FStar_Absyn_Syntax.dummyRange)
in (FStar_Absyn_Syntax.varg _130_165))
in (_130_166)::[])
in (f, _130_167))
in (FStar_Absyn_Syntax.mk_Exp_app _130_168 None FStar_Absyn_Syntax.dummyRange))
in (extract_exp _130_169 en))
end)
in (true, s)))
end
| false -> begin
(match (s) with
| "as_par" -> begin
(let a1 = (FStar_List.hd args)
in (let a2 = (let _130_170 = (FStar_List.tl args)
in (FStar_List.hd _130_170))
in (let _130_176 = (let _130_175 = (let _130_174 = (let _130_172 = (let _130_171 = (extract_arg a1 en)
in (Prims.strcat "E_aspar (" _130_171))
in (Prims.strcat _130_172 ") ("))
in (let _130_173 = (extract_arg a2 en)
in (Prims.strcat _130_174 _130_173)))
in (Prims.strcat _130_175 ")"))
in (true, _130_176))))
end
| "as_sec" -> begin
(let a1 = (FStar_List.hd args)
in (let a2 = (let _130_177 = (FStar_List.tl args)
in (FStar_List.hd _130_177))
in (let _130_183 = (let _130_182 = (let _130_181 = (let _130_179 = (let _130_178 = (extract_arg a1 en)
in (Prims.strcat "E_assec (" _130_178))
in (Prims.strcat _130_179 ") ("))
in (let _130_180 = (extract_arg a2 en)
in (Prims.strcat _130_181 _130_180)))
in (Prims.strcat _130_182 ")"))
in (true, _130_183))))
end
| "box" -> begin
(let a1 = (FStar_List.hd args)
in (let a2 = (let _130_184 = (FStar_List.tl args)
in (FStar_List.hd _130_184))
in (let _130_190 = (let _130_189 = (let _130_188 = (let _130_186 = (let _130_185 = (extract_arg a1 en)
in (Prims.strcat "E_box (" _130_185))
in (Prims.strcat _130_186 ") ("))
in (let _130_187 = (extract_arg a2 en)
in (Prims.strcat _130_188 _130_187)))
in (Prims.strcat _130_189 ")"))
in (true, _130_190))))
end
| ("unbox_p") | ("unbox_s") -> begin
(let a = (let _130_191 = (FStar_List.tl args)
in (FStar_List.hd _130_191))
in (let _130_194 = (let _130_193 = (let _130_192 = (extract_arg a en)
in (Prims.strcat "E_unbox (" _130_192))
in (Prims.strcat _130_193 ")"))
in (true, _130_194)))
end
| "mkwire_s" -> begin
(let a1 = (FStar_List.hd args)
in (let a2 = (let _130_195 = (FStar_List.tl args)
in (FStar_List.hd _130_195))
in (let _130_201 = (let _130_200 = (let _130_199 = (let _130_197 = (let _130_196 = (extract_arg a1 en)
in (Prims.strcat "E_mkwire (" _130_196))
in (Prims.strcat _130_197 ") ("))
in (let _130_198 = (extract_arg a2 en)
in (Prims.strcat _130_199 _130_198)))
in (Prims.strcat _130_200 ")"))
in (true, _130_201))))
end
| "mkwire_p" -> begin
(let a1 = (let _130_202 = (FStar_List.tl args)
in (FStar_List.hd _130_202))
in (let a2 = (let _130_204 = (let _130_203 = (FStar_List.tl args)
in (FStar_List.tl _130_203))
in (FStar_List.hd _130_204))
in (let _130_210 = (let _130_209 = (let _130_208 = (let _130_206 = (let _130_205 = (extract_arg a1 en)
in (Prims.strcat "E_mkwire (" _130_205))
in (Prims.strcat _130_206 ") ("))
in (let _130_207 = (extract_arg a2 en)
in (Prims.strcat _130_208 _130_207)))
in (Prims.strcat _130_209 ")"))
in (true, _130_210))))
end
| ("projwire_p") | ("projwire_s") -> begin
(let a1 = (let _130_211 = (FStar_List.tl args)
in (FStar_List.hd _130_211))
in (let a2 = (let _130_213 = (let _130_212 = (FStar_List.tl args)
in (FStar_List.tl _130_212))
in (FStar_List.hd _130_213))
in (let _130_219 = (let _130_218 = (let _130_217 = (let _130_215 = (let _130_214 = (extract_arg a1 en)
in (Prims.strcat "E_projwire (" _130_214))
in (Prims.strcat _130_215 ") ("))
in (let _130_216 = (extract_arg a2 en)
in (Prims.strcat _130_217 _130_216)))
in (Prims.strcat _130_218 ")"))
in (true, _130_219))))
end
| "concat_wire" -> begin
(let a1 = (let _130_221 = (let _130_220 = (FStar_List.tl args)
in (FStar_List.tl _130_220))
in (FStar_List.hd _130_221))
in (let a2 = (let _130_224 = (let _130_223 = (let _130_222 = (FStar_List.tl args)
in (FStar_List.tl _130_222))
in (FStar_List.tl _130_223))
in (FStar_List.hd _130_224))
in (let _130_230 = (let _130_229 = (let _130_228 = (let _130_226 = (let _130_225 = (extract_arg a1 en)
in (Prims.strcat "E_mkwire (" _130_225))
in (Prims.strcat _130_226 ") ("))
in (let _130_227 = (extract_arg a2 en)
in (Prims.strcat _130_228 _130_227)))
in (Prims.strcat _130_229 ")"))
in (true, _130_230))))
end
| _64_337 -> begin
(false, "")
end)
end))
and extract_arg = (fun a en -> (match (a) with
| (FStar_Util.Inl (_64_341), _64_344) -> begin
(Prims.raise (NYI ("Extract argument cannot extract type arguments")))
end
| (FStar_Util.Inr (e), _64_349) -> begin
(extract_exp e en)
end))
and extract_sigelt = (fun s en -> (match (s) with
| FStar_Absyn_Syntax.Sig_let (lbs, _64_355, _64_357, _64_359) -> begin
(match ((Prims.fst lbs)) with
| true -> begin
(match (((FStar_List.length (Prims.snd lbs)) <> 1)) with
| true -> begin
(Prims.raise (NYI ("Mutually recursive lets not supported")))
end
| false -> begin
(let lb = (FStar_List.hd (Prims.snd lbs))
in (let lbname = (FStar_Absyn_Print.lbname_to_string lb.FStar_Absyn_Syntax.lbname)
in (let filter_ascription = (fun e -> (match ((let _130_237 = (FStar_Absyn_Util.compress_exp e)
in _130_237.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_ascribed (e, _64_368, _64_370) -> begin
e
end
| _64_374 -> begin
e
end))
in (let lb_body = (filter_ascription lb.FStar_Absyn_Syntax.lbdef)
in (match ((let _130_238 = (FStar_Absyn_Util.compress_exp lb_body)
in _130_238.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_abs (bs, e) -> begin
(let bs = (FStar_List.filter (fun a -> (match (a) with
| (FStar_Util.Inl (_64_382), _64_385) -> begin
false
end
| (FStar_Util.Inr (_64_388), _64_391) -> begin
true
end)) bs)
in (let first_b = (FStar_List.hd bs)
in (let rest_bs = (FStar_List.tl bs)
in (let body_str = (extract_exp e en)
in (let tl_abs_str = (FStar_List.fold_left (fun s b -> (let _130_245 = (let _130_244 = (let _130_243 = (let _130_242 = (extract_binder b)
in (Prims.strcat "E_abs " _130_242))
in (Prims.strcat _130_243 " ("))
in (Prims.strcat _130_244 s))
in (Prims.strcat _130_245 ")"))) body_str (FStar_List.rev rest_bs))
in (let fix_str = (let _130_249 = (let _130_248 = (let _130_247 = (let _130_246 = (extract_binder first_b)
in (Prims.strcat (Prims.strcat (Prims.strcat "E_fix " lbname) " ") _130_246))
in (Prims.strcat _130_247 " ("))
in (Prims.strcat _130_248 tl_abs_str))
in (Prims.strcat _130_249 ")"))
in (let let_str = (Prims.strcat (Prims.strcat (Prims.strcat (Prims.strcat "E_let " lbname) " (") fix_str) ")")
in let_str)))))))
end
| _64_403 -> begin
(Prims.raise (NYI ("Expected an abs with recursive let")))
end)))))
end)
end
| false -> begin
(let lb = (FStar_List.hd (Prims.snd lbs))
in (let _130_254 = (let _130_253 = (let _130_251 = (let _130_250 = (FStar_Absyn_Print.lbname_to_string lb.FStar_Absyn_Syntax.lbname)
in (Prims.strcat "E_let " _130_250))
in (Prims.strcat _130_251 " ("))
in (let _130_252 = (extract_exp lb.FStar_Absyn_Syntax.lbdef en)
in (Prims.strcat _130_253 _130_252)))
in (Prims.strcat _130_254 ")")))
end)
end
| FStar_Absyn_Syntax.Sig_main (e, _64_407) -> begin
(extract_exp e en)
end
| _64_411 -> begin
""
end))

let extract_main = (fun s en -> (match (s) with
| FStar_Absyn_Syntax.Sig_main (e, _64_416) -> begin
(extract_exp e en)
end
| _64_420 -> begin
(Prims.raise (NYI ("Extract main got some other sigelt!")))
end))

let extract_sigelts = (fun l en -> (let l = (FStar_List.rev l)
in (let main_str = (let _130_263 = (FStar_List.hd l)
in (extract_main _130_263 en))
in (let _130_266 = (FStar_List.tl l)
in (FStar_List.fold_left (fun acc s -> (let s_str = (extract_sigelt s en)
in (Prims.strcat (Prims.strcat (Prims.strcat s_str " (") acc) ")"))) main_str _130_266)))))

let extract = (fun l en -> (let _64_430 = (initialize ())
in (FStar_List.iter (fun m -> (match ((m.FStar_Absyn_Syntax.name.FStar_Absyn_Syntax.str = "SMC")) with
| true -> begin
(let s = (extract_sigelts m.FStar_Absyn_Syntax.declarations en)
in (let _64_434 = (FStar_Util.print_string s)
in (FStar_Util.print_string "\n")))
end
| false -> begin
()
end)) l)))




