
open Prims
type env =
{curmodule : FStar_Ident.lident Prims.option; modules : (FStar_Ident.lident * FStar_Syntax_Syntax.modul) Prims.list; open_namespaces : FStar_Ident.lident Prims.list; sigaccum : FStar_Syntax_Syntax.sigelts; localbindings : (FStar_Ident.ident * FStar_Syntax_Syntax.bv) Prims.list; recbindings : (FStar_Ident.ident * FStar_Ident.lident) Prims.list; sigmap : (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap Prims.list; default_result_effect : FStar_Ident.lident; iface : Prims.bool; admitted_iface : Prims.bool; expect_typ : Prims.bool}

let is_Mkenv = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv"))))

let open_modules = (fun e -> e.modules)

let current_module = (fun env -> (match (env.curmodule) with
| None -> begin
(FStar_All.failwith "Unset current module")
end
| Some (m) -> begin
m
end))

let qual = (fun lid id -> (let _152_43 = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns ((lid.FStar_Ident.ident)::(id)::[])))
in (FStar_Ident.set_lid_range _152_43 id.FStar_Ident.idRange)))

let qualify = (fun env id -> (let _152_48 = (current_module env)
in (qual _152_48 id)))

let qualify_lid = (fun env lid -> (let cur = (current_module env)
in (let _152_53 = (FStar_Ident.lid_of_ids (FStar_List.append (FStar_List.append (FStar_List.append cur.FStar_Ident.ns ((cur.FStar_Ident.ident)::[])) lid.FStar_Ident.ns) ((lid.FStar_Ident.ident)::[])))
in (FStar_Ident.set_lid_range _152_53 (FStar_Ident.range_of_lid lid)))))

let new_sigmap = (fun _61_36 -> (match (()) with
| () -> begin
(FStar_Util.smap_create 100)
end))

let empty_env = (fun _61_37 -> (match (()) with
| () -> begin
(let _152_58 = (let _152_57 = (new_sigmap ())
in (_152_57)::[])
in {curmodule = None; modules = []; open_namespaces = []; sigaccum = []; localbindings = []; recbindings = []; sigmap = _152_58; default_result_effect = FStar_Syntax_Const.effect_ML_lid; iface = false; admitted_iface = false; expect_typ = false})
end))

let sigmap = (fun env -> (FStar_List.hd env.sigmap))

let default_total = (fun env -> (let _61_40 = env
in {curmodule = _61_40.curmodule; modules = _61_40.modules; open_namespaces = _61_40.open_namespaces; sigaccum = _61_40.sigaccum; localbindings = _61_40.localbindings; recbindings = _61_40.recbindings; sigmap = _61_40.sigmap; default_result_effect = FStar_Syntax_Const.effect_Tot_lid; iface = _61_40.iface; admitted_iface = _61_40.admitted_iface; expect_typ = _61_40.expect_typ}))

let default_ml = (fun env -> (let _61_43 = env
in {curmodule = _61_43.curmodule; modules = _61_43.modules; open_namespaces = _61_43.open_namespaces; sigaccum = _61_43.sigaccum; localbindings = _61_43.localbindings; recbindings = _61_43.recbindings; sigmap = _61_43.sigmap; default_result_effect = FStar_Syntax_Const.effect_ML_lid; iface = _61_43.iface; admitted_iface = _61_43.admitted_iface; expect_typ = _61_43.expect_typ}))

let set_bv_range = (fun bv r -> (let id = (let _61_47 = bv.FStar_Syntax_Syntax.ppname
in {FStar_Ident.idText = _61_47.FStar_Ident.idText; FStar_Ident.idRange = r})
in (let _61_50 = bv
in {FStar_Syntax_Syntax.ppname = id; FStar_Syntax_Syntax.index = _61_50.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _61_50.FStar_Syntax_Syntax.sort})))

let bv_to_name = (fun bv r -> (FStar_Syntax_Syntax.bv_to_name (set_bv_range bv r)))

let unmangleMap = (("op_ColonColon", "Cons"))::(("not", "op_Negation"))::[]

let unmangleOpName = (fun id -> (FStar_Util.find_map unmangleMap (fun _61_57 -> (match (_61_57) with
| (x, y) -> begin
if (id.FStar_Ident.idText = x) then begin
(let _152_76 = (FStar_Ident.lid_of_path (("Prims")::(y)::[]) id.FStar_Ident.idRange)
in Some (_152_76))
end else begin
None
end
end))))

let try_lookup_id = (fun env id -> (match ((unmangleOpName id)) with
| Some (l) -> begin
(let _152_81 = (FStar_Syntax_Syntax.fvar None l id.FStar_Ident.idRange)
in Some (_152_81))
end
| _61_63 -> begin
(FStar_Util.find_map env.localbindings (fun _61_1 -> (match (_61_1) with
| (id', x) when (id'.FStar_Ident.idText = id.FStar_Ident.idText) -> begin
(let _152_83 = (bv_to_name x id.FStar_Ident.idRange)
in Some (_152_83))
end
| _61_69 -> begin
None
end)))
end))

let resolve_in_open_namespaces = (fun env lid finder -> (let aux = (fun namespaces -> (match ((finder lid)) with
| Some (r) -> begin
Some (r)
end
| _61_79 -> begin
(let ids = (FStar_Ident.ids_of_lid lid)
in (FStar_Util.find_map namespaces (fun ns -> (let full_name = (FStar_Ident.lid_of_ids (FStar_List.append (FStar_Ident.ids_of_lid ns) ids))
in (finder full_name)))))
end))
in (let _152_98 = (let _152_97 = (current_module env)
in (_152_97)::env.open_namespaces)
in (aux _152_98))))

type foundname =
| Term_name of FStar_Syntax_Syntax.typ
| Eff_name of (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident)

let is_Term_name = (fun _discr_ -> (match (_discr_) with
| Term_name (_) -> begin
true
end
| _ -> begin
false
end))

let is_Eff_name = (fun _discr_ -> (match (_discr_) with
| Eff_name (_) -> begin
true
end
| _ -> begin
false
end))

let ___Term_name____0 = (fun projectee -> (match (projectee) with
| Term_name (_61_85) -> begin
_61_85
end))

let ___Eff_name____0 = (fun projectee -> (match (projectee) with
| Eff_name (_61_88) -> begin
_61_88
end))

let fv_qual_of_se = (fun _61_3 -> (match (_61_3) with
| FStar_Syntax_Syntax.Sig_datacon (Prims.MkTuple8 (_61_91, _61_93, _61_95, l, _61_98, quals, _61_101, _61_103)) -> begin
(let qopt = (FStar_Util.find_map quals (fun _61_2 -> (match (_61_2) with
| FStar_Syntax_Syntax.RecordConstructor (fs) -> begin
Some (FStar_Syntax_Syntax.Record_ctor ((l, fs)))
end
| _61_110 -> begin
None
end)))
in (match (qopt) with
| None -> begin
Some (FStar_Syntax_Syntax.Data_ctor)
end
| x -> begin
x
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (_61_115, _61_117, _61_119, quals, _61_122) -> begin
None
end
| _61_126 -> begin
None
end))

let try_lookup_name = (fun any_val exclude_interf env lid -> (let find_in_sig = (fun lid -> (match ((let _152_140 = (sigmap env)
in (FStar_Util.smap_try_find _152_140 lid.FStar_Ident.str))) with
| Some (_61_134, true) when exclude_interf -> begin
None
end
| None -> begin
None
end
| Some (se, _61_141) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_61_145) -> begin
(let _152_142 = (let _152_141 = (FStar_Syntax_Syntax.fvar None lid (FStar_Ident.range_of_lid lid))
in Term_name (_152_141))
in Some (_152_142))
end
| FStar_Syntax_Syntax.Sig_datacon (_61_148) -> begin
(let _152_145 = (let _152_144 = (let _152_143 = (fv_qual_of_se se)
in (FStar_Syntax_Syntax.fvar _152_143 lid (FStar_Ident.range_of_lid lid)))
in Term_name (_152_144))
in Some (_152_145))
end
| FStar_Syntax_Syntax.Sig_let (_61_151) -> begin
(let _152_147 = (let _152_146 = (FStar_Syntax_Syntax.fvar None lid (FStar_Ident.range_of_lid lid))
in Term_name (_152_146))
in Some (_152_147))
end
| FStar_Syntax_Syntax.Sig_declare_typ (_61_154, _61_156, _61_158, quals, _61_161) -> begin
if (any_val || (FStar_All.pipe_right quals (FStar_Util.for_some (fun _61_4 -> (match (_61_4) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| _61_167 -> begin
false
end))))) then begin
(let _152_151 = (let _152_150 = (let _152_149 = (fv_qual_of_se se)
in (FStar_Syntax_Syntax.fvar _152_149 lid (FStar_Ident.range_of_lid lid)))
in Term_name (_152_150))
in Some (_152_151))
end else begin
None
end
end
| FStar_Syntax_Syntax.Sig_new_effect (ne, _61_170) -> begin
(let _152_154 = (let _152_153 = (let _152_152 = (FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname (FStar_Ident.range_of_lid lid))
in (se, _152_152))
in Eff_name (_152_153))
in Some (_152_154))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (_61_174) -> begin
Some (Eff_name ((se, lid)))
end
| _61_177 -> begin
None
end)
end))
in (let found_id = (match (lid.FStar_Ident.ns) with
| [] -> begin
(match ((try_lookup_id env lid.FStar_Ident.ident)) with
| Some (e) -> begin
Some (Term_name (e))
end
| None -> begin
(let recname = (qualify env lid.FStar_Ident.ident)
in (FStar_Util.find_map env.recbindings (fun _61_185 -> (match (_61_185) with
| (id, l) -> begin
if (id.FStar_Ident.idText = lid.FStar_Ident.ident.FStar_Ident.idText) then begin
(let _152_158 = (let _152_157 = (let _152_156 = (FStar_Ident.set_lid_range l (FStar_Ident.range_of_lid lid))
in (FStar_Syntax_Syntax.fvar None _152_156 (FStar_Ident.range_of_lid lid)))
in Term_name (_152_157))
in Some (_152_158))
end else begin
None
end
end))))
end)
end
| _61_187 -> begin
None
end)
in (match (found_id) with
| Some (_61_190) -> begin
found_id
end
| _61_193 -> begin
(resolve_in_open_namespaces env lid find_in_sig)
end))))

let try_lookup_effect_name' = (fun exclude_interf env lid -> (match ((try_lookup_name true exclude_interf env lid)) with
| Some (Eff_name (o, l)) -> begin
Some ((o, l))
end
| _61_203 -> begin
None
end))

let try_lookup_effect_name = (fun env l -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some (o, l) -> begin
Some (l)
end
| _61_211 -> begin
None
end))

let try_lookup_effect_defn = (fun env l -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some (FStar_Syntax_Syntax.Sig_new_effect (ne, _61_216), _61_220) -> begin
Some (ne)
end
| _61_224 -> begin
None
end))

let is_effect_name = (fun env lid -> (match ((try_lookup_effect_name env lid)) with
| None -> begin
false
end
| Some (_61_229) -> begin
true
end))

let lookup_letbinding_quals = (fun env lid -> (let find_in_sig = (fun lid -> (match ((let _152_183 = (sigmap env)
in (FStar_Util.smap_try_find _152_183 lid.FStar_Ident.str))) with
| Some (FStar_Syntax_Syntax.Sig_declare_typ (lid, _61_237, _61_239, quals, _61_242), _61_246) -> begin
Some (quals)
end
| _61_250 -> begin
None
end))
in (match ((resolve_in_open_namespaces env lid find_in_sig)) with
| Some (quals) -> begin
quals
end
| _61_254 -> begin
[]
end)))

let try_lookup_module = (fun env path -> (match ((FStar_List.tryFind (fun _61_259 -> (match (_61_259) with
| (mlid, modul) -> begin
((FStar_Ident.path_of_lid mlid) = path)
end)) env.modules)) with
| Some (_61_261, modul) -> begin
Some (modul)
end
| None -> begin
None
end))

let try_lookup_let = (fun env lid -> (let find_in_sig = (fun lid -> (match ((let _152_195 = (sigmap env)
in (FStar_Util.smap_try_find _152_195 lid.FStar_Ident.str))) with
| Some (FStar_Syntax_Syntax.Sig_let (_61_271), _61_274) -> begin
(let _152_196 = (FStar_Syntax_Syntax.fvar None lid (FStar_Ident.range_of_lid lid))
in Some (_152_196))
end
| _61_278 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))

let try_lookup_definition = (fun env lid -> (let find_in_sig = (fun lid -> (match ((let _152_203 = (sigmap env)
in (FStar_Util.smap_try_find _152_203 lid.FStar_Ident.str))) with
| Some (FStar_Syntax_Syntax.Sig_let (lbs, _61_285, _61_287, _61_289), _61_293) -> begin
(FStar_Util.find_map (Prims.snd lbs) (fun lb -> (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (lid') when (FStar_Ident.lid_equals lid lid') -> begin
Some (lb.FStar_Syntax_Syntax.lbdef)
end
| _61_300 -> begin
None
end)))
end
| _61_302 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))

let try_lookup_lid' = (fun any_val exclude_interf env lid -> (match ((try_lookup_name any_val exclude_interf env lid)) with
| Some (Term_name (e)) -> begin
Some (e)
end
| _61_311 -> begin
None
end))

let try_lookup_lid = (fun env l -> (try_lookup_lid' env.iface false env l))

let try_lookup_datacon = (fun env lid -> (let find_in_sig = (fun lid -> (match ((let _152_223 = (sigmap env)
in (FStar_Util.smap_try_find _152_223 lid.FStar_Ident.str))) with
| Some (FStar_Syntax_Syntax.Sig_declare_typ (_61_319, _61_321, _61_323, quals, _61_326), _61_330) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _61_5 -> (match (_61_5) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| _61_336 -> begin
false
end)))) then begin
(let _152_225 = (FStar_Syntax_Syntax.lid_as_fv lid None)
in Some (_152_225))
end else begin
None
end
end
| Some (FStar_Syntax_Syntax.Sig_datacon (_61_338), _61_341) -> begin
(let _152_226 = (FStar_Syntax_Syntax.lid_as_fv lid (Some (FStar_Syntax_Syntax.Data_ctor)))
in Some (_152_226))
end
| _61_345 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))

let find_all_datacons = (fun env lid -> (let find_in_sig = (fun lid -> (match ((let _152_233 = (sigmap env)
in (FStar_Util.smap_try_find _152_233 lid.FStar_Ident.str))) with
| Some (FStar_Syntax_Syntax.Sig_inductive_typ (Prims.MkTuple8 (_61_351, _61_353, _61_355, _61_357, _61_359, datas, _61_362, _61_364)), _61_368) -> begin
Some (datas)
end
| _61_372 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))

type record_or_dc =
{typename : FStar_Ident.lident; constrname : FStar_Ident.lident; parms : FStar_Syntax_Syntax.binders; fields : (FStar_Syntax_Syntax.fieldname * FStar_Syntax_Syntax.typ) Prims.list; is_record : Prims.bool}

let is_Mkrecord_or_dc = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkrecord_or_dc"))))

let record_cache_aux = (let record_cache = (FStar_Util.mk_ref (([])::[]))
in (let push = (fun _61_381 -> (match (()) with
| () -> begin
(let _152_263 = (let _152_262 = (let _152_260 = (FStar_ST.read record_cache)
in (FStar_List.hd _152_260))
in (let _152_261 = (FStar_ST.read record_cache)
in (_152_262)::_152_261))
in (FStar_ST.op_Colon_Equals record_cache _152_263))
end))
in (let pop = (fun _61_383 -> (match (()) with
| () -> begin
(let _152_267 = (let _152_266 = (FStar_ST.read record_cache)
in (FStar_List.tl _152_266))
in (FStar_ST.op_Colon_Equals record_cache _152_267))
end))
in (let peek = (fun _61_385 -> (match (()) with
| () -> begin
(let _152_270 = (FStar_ST.read record_cache)
in (FStar_List.hd _152_270))
end))
in (let insert = (fun r -> (let _152_277 = (let _152_276 = (let _152_273 = (peek ())
in (r)::_152_273)
in (let _152_275 = (let _152_274 = (FStar_ST.read record_cache)
in (FStar_List.tl _152_274))
in (_152_276)::_152_275))
in (FStar_ST.op_Colon_Equals record_cache _152_277)))
in (push, pop, peek, insert))))))

let push_record_cache = (let _61_395 = record_cache_aux
in (match (_61_395) with
| (push, _61_390, _61_392, _61_394) -> begin
push
end))

let pop_record_cache = (let _61_403 = record_cache_aux
in (match (_61_403) with
| (_61_397, pop, _61_400, _61_402) -> begin
pop
end))

let peek_record_cache = (let _61_411 = record_cache_aux
in (match (_61_411) with
| (_61_405, _61_407, peek, _61_410) -> begin
peek
end))

let insert_record_cache = (let _61_419 = record_cache_aux
in (match (_61_419) with
| (_61_413, _61_415, _61_417, insert) -> begin
insert
end))

let extract_record = (fun e _61_9 -> (match (_61_9) with
| FStar_Syntax_Syntax.Sig_bundle (sigs, _61_424, _61_426, _61_428) -> begin
(let is_rec = (FStar_Util.for_some (fun _61_6 -> (match (_61_6) with
| (FStar_Syntax_Syntax.RecordType (_)) | (FStar_Syntax_Syntax.RecordConstructor (_)) -> begin
true
end
| _61_439 -> begin
false
end)))
in (let find_dc = (fun dc -> (FStar_All.pipe_right sigs (FStar_Util.find_opt (fun _61_7 -> (match (_61_7) with
| FStar_Syntax_Syntax.Sig_datacon (Prims.MkTuple8 (lid, _61_446, _61_448, _61_450, _61_452, _61_454, _61_456, _61_458)) -> begin
(FStar_Ident.lid_equals dc lid)
end
| _61_462 -> begin
false
end)))))
in (FStar_All.pipe_right sigs (FStar_List.iter (fun _61_8 -> (match (_61_8) with
| FStar_Syntax_Syntax.Sig_inductive_typ (Prims.MkTuple8 (typename, univs, parms, _61_468, _61_470, dc::[], tags, _61_475)) -> begin
(match ((let _152_348 = (find_dc dc)
in (FStar_All.pipe_left FStar_Util.must _152_348))) with
| FStar_Syntax_Syntax.Sig_datacon (Prims.MkTuple8 (constrname, _61_480, t, _61_483, _61_485, _61_487, _61_489, _61_491)) -> begin
(let _61_497 = (FStar_Syntax_Util.arrow_formals t)
in (match (_61_497) with
| (formals, _61_496) -> begin
(let is_rec = (is_rec tags)
in (let fields = (FStar_All.pipe_right formals (FStar_List.collect (fun _61_501 -> (match (_61_501) with
| (x, q) -> begin
if ((FStar_Syntax_Syntax.is_null_bv x) || (is_rec && (q = Some (FStar_Syntax_Syntax.Implicit)))) then begin
[]
end else begin
(let _152_352 = (let _152_351 = (let _152_350 = if is_rec then begin
(FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname)
end else begin
x.FStar_Syntax_Syntax.ppname
end
in (qual constrname _152_350))
in (_152_351, x.FStar_Syntax_Syntax.sort))
in (_152_352)::[])
end
end))))
in (let record = {typename = typename; constrname = constrname; parms = parms; fields = fields; is_record = is_rec}
in (insert_record_cache record))))
end))
end
| _61_505 -> begin
()
end)
end
| _61_507 -> begin
()
end))))))
end
| _61_509 -> begin
()
end))

let try_lookup_record_or_dc_by_field_name = (fun env fieldname -> (let maybe_add_constrname = (fun ns c -> (let rec aux = (fun ns -> (match (ns) with
| [] -> begin
(c)::[]
end
| c'::[] -> begin
if (c'.FStar_Ident.idText = c.FStar_Ident.idText) then begin
(c)::[]
end else begin
(c')::(c)::[]
end
end
| hd::tl -> begin
(let _152_363 = (aux tl)
in (hd)::_152_363)
end))
in (aux ns)))
in (let find_in_cache = (fun fieldname -> (let _61_527 = (fieldname.FStar_Ident.ns, fieldname.FStar_Ident.ident)
in (match (_61_527) with
| (ns, fieldname) -> begin
(let _152_368 = (peek_record_cache ())
in (FStar_Util.find_map _152_368 (fun record -> (let constrname = record.constrname.FStar_Ident.ident
in (let ns = (maybe_add_constrname ns constrname)
in (let fname = (FStar_Ident.lid_of_ids (FStar_List.append ns ((fieldname)::[])))
in (FStar_Util.find_map record.fields (fun _61_535 -> (match (_61_535) with
| (f, _61_534) -> begin
if (FStar_Ident.lid_equals fname f) then begin
Some ((record, fname))
end else begin
None
end
end)))))))))
end)))
in (resolve_in_open_namespaces env fieldname find_in_cache))))

let try_lookup_record_by_field_name = (fun env fieldname -> (match ((try_lookup_record_or_dc_by_field_name env fieldname)) with
| Some (r, f) when r.is_record -> begin
Some ((r, f))
end
| _61_543 -> begin
None
end))

let try_lookup_projector_by_field_name = (fun env fieldname -> (match ((try_lookup_record_or_dc_by_field_name env fieldname)) with
| Some (r, f) -> begin
Some ((f, r.is_record))
end
| _61_551 -> begin
None
end))

let qualify_field_to_record = (fun env recd f -> (let qualify = (fun fieldname -> (let _61_559 = (fieldname.FStar_Ident.ns, fieldname.FStar_Ident.ident)
in (match (_61_559) with
| (ns, fieldname) -> begin
(let constrname = recd.constrname.FStar_Ident.ident
in (let fname = (FStar_Ident.lid_of_ids (FStar_List.append (FStar_List.append ns ((constrname)::[])) ((fieldname)::[])))
in (FStar_Util.find_map recd.fields (fun _61_565 -> (match (_61_565) with
| (f, _61_564) -> begin
if (FStar_Ident.lid_equals fname f) then begin
Some (fname)
end else begin
None
end
end)))))
end)))
in (resolve_in_open_namespaces env f qualify)))

let unique = (fun any_val exclude_if env lid -> (let this_env = (let _61_570 = env
in {curmodule = _61_570.curmodule; modules = _61_570.modules; open_namespaces = []; sigaccum = _61_570.sigaccum; localbindings = _61_570.localbindings; recbindings = _61_570.recbindings; sigmap = _61_570.sigmap; default_result_effect = _61_570.default_result_effect; iface = _61_570.iface; admitted_iface = _61_570.admitted_iface; expect_typ = _61_570.expect_typ})
in (match ((try_lookup_lid' any_val exclude_if env lid)) with
| None -> begin
true
end
| Some (_61_575) -> begin
false
end)))

let push_bv = (fun env x -> (let bv = (FStar_Syntax_Syntax.gen_bv x.FStar_Ident.idText (Some (x.FStar_Ident.idRange)) FStar_Syntax_Syntax.tun)
in ((let _61_580 = env
in {curmodule = _61_580.curmodule; modules = _61_580.modules; open_namespaces = _61_580.open_namespaces; sigaccum = _61_580.sigaccum; localbindings = ((x, bv))::env.localbindings; recbindings = _61_580.recbindings; sigmap = _61_580.sigmap; default_result_effect = _61_580.default_result_effect; iface = _61_580.iface; admitted_iface = _61_580.admitted_iface; expect_typ = _61_580.expect_typ}), bv)))

let push_top_level_rec_binding = (fun env x -> (let l = (qualify env x)
in if (unique false true env l) then begin
(let _61_585 = env
in {curmodule = _61_585.curmodule; modules = _61_585.modules; open_namespaces = _61_585.open_namespaces; sigaccum = _61_585.sigaccum; localbindings = _61_585.localbindings; recbindings = ((x, l))::env.recbindings; sigmap = _61_585.sigmap; default_result_effect = _61_585.default_result_effect; iface = _61_585.iface; admitted_iface = _61_585.admitted_iface; expect_typ = _61_585.expect_typ})
end else begin
(Prims.raise (FStar_Syntax_Syntax.Error (((Prims.strcat "Duplicate top-level names " l.FStar_Ident.str), (FStar_Ident.range_of_lid l)))))
end))

let push_sigelt = (fun env s -> (let err = (fun l -> (let sopt = (let _152_408 = (sigmap env)
in (FStar_Util.smap_try_find _152_408 l.FStar_Ident.str))
in (let r = (match (sopt) with
| Some (se, _61_594) -> begin
(match ((let _152_409 = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_Util.find_opt (FStar_Ident.lid_equals l) _152_409))) with
| Some (l) -> begin
(FStar_All.pipe_left FStar_Range.string_of_range (FStar_Ident.range_of_lid l))
end
| None -> begin
"<unknown>"
end)
end
| None -> begin
"<unknown>"
end)
in (let _152_412 = (let _152_411 = (let _152_410 = (FStar_Util.format2 "Duplicate top-level names [%s]; previously declared at %s" (FStar_Ident.text_of_lid l) r)
in (_152_410, (FStar_Ident.range_of_lid l)))
in FStar_Syntax_Syntax.Error (_152_411))
in (Prims.raise _152_412)))))
in (let env = (let _61_612 = (match (s) with
| FStar_Syntax_Syntax.Sig_let (_61_603) -> begin
(false, true)
end
| FStar_Syntax_Syntax.Sig_bundle (_61_606) -> begin
(true, true)
end
| _61_609 -> begin
(false, false)
end)
in (match (_61_612) with
| (any_val, exclude_if) -> begin
(let lids = (FStar_Syntax_Util.lids_of_sigelt s)
in (match ((FStar_Util.find_map lids (fun l -> if (not ((unique any_val exclude_if env l))) then begin
Some (l)
end else begin
None
end))) with
| None -> begin
(let _61_616 = (extract_record env s)
in (let _61_618 = env
in {curmodule = _61_618.curmodule; modules = _61_618.modules; open_namespaces = _61_618.open_namespaces; sigaccum = (s)::env.sigaccum; localbindings = _61_618.localbindings; recbindings = _61_618.recbindings; sigmap = _61_618.sigmap; default_result_effect = _61_618.default_result_effect; iface = _61_618.iface; admitted_iface = _61_618.admitted_iface; expect_typ = _61_618.expect_typ}))
end
| Some (l) -> begin
(err l)
end))
end))
in (let _61_637 = (match (s) with
| FStar_Syntax_Syntax.Sig_bundle (ses, _61_625, _61_627, _61_629) -> begin
(let _152_416 = (FStar_List.map (fun se -> (let _152_415 = (FStar_Syntax_Util.lids_of_sigelt se)
in (_152_415, se))) ses)
in (env, _152_416))
end
| _61_634 -> begin
(let _152_419 = (let _152_418 = (let _152_417 = (FStar_Syntax_Util.lids_of_sigelt s)
in (_152_417, s))
in (_152_418)::[])
in (env, _152_419))
end)
in (match (_61_637) with
| (env, lss) -> begin
(let _61_642 = (FStar_All.pipe_right lss (FStar_List.iter (fun _61_640 -> (match (_61_640) with
| (lids, se) -> begin
(FStar_All.pipe_right lids (FStar_List.iter (fun lid -> (let _152_422 = (sigmap env)
in (FStar_Util.smap_add _152_422 lid.FStar_Ident.str (se, (env.iface && (not (env.admitted_iface)))))))))
end))))
in env)
end)))))

let push_namespace = (fun env lid -> (let _61_646 = env
in {curmodule = _61_646.curmodule; modules = _61_646.modules; open_namespaces = (lid)::env.open_namespaces; sigaccum = _61_646.sigaccum; localbindings = _61_646.localbindings; recbindings = _61_646.recbindings; sigmap = _61_646.sigmap; default_result_effect = _61_646.default_result_effect; iface = _61_646.iface; admitted_iface = _61_646.admitted_iface; expect_typ = _61_646.expect_typ}))

let check_admits = (fun nm env -> (let warn = (not ((let _152_432 = (FStar_ST.read FStar_Options.admit_fsi)
in (FStar_All.pipe_right _152_432 (FStar_Util.for_some (fun l -> (nm.FStar_Ident.str = l)))))))
in (FStar_All.pipe_right env.sigaccum (FStar_List.iter (fun se -> (match (se) with
| FStar_Syntax_Syntax.Sig_declare_typ (l, u, t, quals, r) -> begin
(match ((try_lookup_lid env l)) with
| None -> begin
(let _61_661 = if warn then begin
(let _152_436 = (let _152_435 = (FStar_Range.string_of_range (FStar_Ident.range_of_lid l))
in (let _152_434 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format2 "%s: Warning: Admitting %s without a definition\n" _152_435 _152_434)))
in (FStar_Util.print_string _152_436))
end else begin
()
end
in (let _152_437 = (sigmap env)
in (FStar_Util.smap_add _152_437 l.FStar_Ident.str (FStar_Syntax_Syntax.Sig_declare_typ ((l, u, t, (FStar_Syntax_Syntax.Assumption)::quals, r)), false))))
end
| Some (_61_664) -> begin
()
end)
end
| _61_667 -> begin
()
end))))))

let finish = (fun env modul -> (let _61_711 = (FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations (FStar_List.iter (fun _61_11 -> (match (_61_11) with
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _61_674, _61_676) -> begin
if (FStar_List.contains FStar_Syntax_Syntax.Private quals) then begin
(FStar_All.pipe_right ses (FStar_List.iter (fun _61_10 -> (match (_61_10) with
| FStar_Syntax_Syntax.Sig_datacon (Prims.MkTuple8 (lid, _61_682, _61_684, _61_686, _61_688, _61_690, _61_692, _61_694)) -> begin
(let _152_444 = (sigmap env)
in (FStar_Util.smap_remove _152_444 lid.FStar_Ident.str))
end
| _61_698 -> begin
()
end))))
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _61_701, _61_703, quals, _61_706) -> begin
if (FStar_List.contains FStar_Syntax_Syntax.Private quals) then begin
(let _152_445 = (sigmap env)
in (FStar_Util.smap_remove _152_445 lid.FStar_Ident.str))
end else begin
()
end
end
| _61_710 -> begin
()
end))))
in (let _61_713 = env
in {curmodule = None; modules = ((modul.FStar_Syntax_Syntax.name, modul))::env.modules; open_namespaces = []; sigaccum = []; localbindings = []; recbindings = []; sigmap = _61_713.sigmap; default_result_effect = _61_713.default_result_effect; iface = _61_713.iface; admitted_iface = _61_713.admitted_iface; expect_typ = _61_713.expect_typ})))

let push = (fun env -> (let _61_716 = (push_record_cache ())
in (let _61_718 = env
in (let _152_450 = (let _152_449 = (let _152_448 = (sigmap env)
in (FStar_Util.smap_copy _152_448))
in (_152_449)::env.sigmap)
in {curmodule = _61_718.curmodule; modules = _61_718.modules; open_namespaces = _61_718.open_namespaces; sigaccum = _61_718.sigaccum; localbindings = _61_718.localbindings; recbindings = _61_718.recbindings; sigmap = _152_450; default_result_effect = _61_718.default_result_effect; iface = _61_718.iface; admitted_iface = _61_718.admitted_iface; expect_typ = _61_718.expect_typ}))))

let mark = (fun env -> (push env))

let reset_mark = (fun env -> (let _61_722 = env
in (let _152_455 = (FStar_List.tl env.sigmap)
in {curmodule = _61_722.curmodule; modules = _61_722.modules; open_namespaces = _61_722.open_namespaces; sigaccum = _61_722.sigaccum; localbindings = _61_722.localbindings; recbindings = _61_722.recbindings; sigmap = _152_455; default_result_effect = _61_722.default_result_effect; iface = _61_722.iface; admitted_iface = _61_722.admitted_iface; expect_typ = _61_722.expect_typ})))

let commit_mark = (fun env -> (match (env.sigmap) with
| hd::_61_727::tl -> begin
(let _61_731 = env
in {curmodule = _61_731.curmodule; modules = _61_731.modules; open_namespaces = _61_731.open_namespaces; sigaccum = _61_731.sigaccum; localbindings = _61_731.localbindings; recbindings = _61_731.recbindings; sigmap = (hd)::tl; default_result_effect = _61_731.default_result_effect; iface = _61_731.iface; admitted_iface = _61_731.admitted_iface; expect_typ = _61_731.expect_typ})
end
| _61_734 -> begin
(FStar_All.failwith "Impossible")
end))

let pop = (fun env -> (match (env.sigmap) with
| _61_738::maps -> begin
(let _61_740 = (pop_record_cache ())
in (let _61_742 = env
in {curmodule = _61_742.curmodule; modules = _61_742.modules; open_namespaces = _61_742.open_namespaces; sigaccum = _61_742.sigaccum; localbindings = _61_742.localbindings; recbindings = _61_742.recbindings; sigmap = maps; default_result_effect = _61_742.default_result_effect; iface = _61_742.iface; admitted_iface = _61_742.admitted_iface; expect_typ = _61_742.expect_typ}))
end
| _61_745 -> begin
(FStar_All.failwith "No more modules to pop")
end))

let export_interface = (fun m env -> (let sigelt_in_m = (fun se -> (match ((FStar_Syntax_Util.lids_of_sigelt se)) with
| l::_61_751 -> begin
(l.FStar_Ident.nsstr = m.FStar_Ident.str)
end
| _61_755 -> begin
false
end))
in (let sm = (sigmap env)
in (let env = (pop env)
in (let keys = (FStar_Util.smap_keys sm)
in (let sm' = (sigmap env)
in (let _61_779 = (FStar_All.pipe_right keys (FStar_List.iter (fun k -> (match ((FStar_Util.smap_try_find sm' k)) with
| Some (se, true) when (sigelt_in_m se) -> begin
(let _61_765 = (FStar_Util.smap_remove sm' k)
in (let se = (match (se) with
| FStar_Syntax_Syntax.Sig_declare_typ (l, u, t, q, r) -> begin
FStar_Syntax_Syntax.Sig_declare_typ ((l, u, t, (FStar_Syntax_Syntax.Assumption)::q, r))
end
| _61_775 -> begin
se
end)
in (FStar_Util.smap_add sm' k (se, false))))
end
| _61_778 -> begin
()
end))))
in env)))))))

let finish_module_or_interface = (fun env modul -> (let _61_783 = if (not (modul.FStar_Syntax_Syntax.is_interface)) then begin
(check_admits modul.FStar_Syntax_Syntax.name env)
end else begin
()
end
in (finish env modul)))

let prepare_module_or_interface = (fun intf admitted env mname -> (let prep = (fun env -> (let open_ns = if (FStar_Ident.lid_equals mname FStar_Syntax_Const.prims_lid) then begin
[]
end else begin
if (FStar_Ident.lid_equals mname FStar_Syntax_Const.st_lid) then begin
(FStar_Syntax_Const.prims_lid)::[]
end else begin
if (FStar_Ident.lid_equals mname FStar_Syntax_Const.all_lid) then begin
(FStar_Syntax_Const.prims_lid)::(FStar_Syntax_Const.st_lid)::[]
end else begin
(FStar_Syntax_Const.prims_lid)::(FStar_Syntax_Const.st_lid)::(FStar_Syntax_Const.all_lid)::(FStar_Syntax_Const.fstar_ns_lid)::[]
end
end
end
in (let _61_792 = env
in {curmodule = Some (mname); modules = _61_792.modules; open_namespaces = open_ns; sigaccum = _61_792.sigaccum; localbindings = _61_792.localbindings; recbindings = _61_792.recbindings; sigmap = env.sigmap; default_result_effect = _61_792.default_result_effect; iface = intf; admitted_iface = admitted; expect_typ = _61_792.expect_typ})))
in (match ((FStar_All.pipe_right env.modules (FStar_Util.find_opt (fun _61_797 -> (match (_61_797) with
| (l, _61_796) -> begin
(FStar_Ident.lid_equals l mname)
end))))) with
| None -> begin
((prep env), false)
end
| Some (_61_800, m) -> begin
(let _61_804 = if ((not (m.FStar_Syntax_Syntax.is_interface)) || intf) then begin
(let _152_484 = (let _152_483 = (let _152_482 = (FStar_Util.format1 "Duplicate module or interface name: %s" mname.FStar_Ident.str)
in (_152_482, (FStar_Ident.range_of_lid mname)))
in FStar_Syntax_Syntax.Error (_152_483))
in (Prims.raise _152_484))
end else begin
()
end
in (let _152_486 = (let _152_485 = (push env)
in (prep _152_485))
in (_152_486, true)))
end)))

let enter_monad_scope = (fun env mname -> (let curmod = (current_module env)
in (let mscope = (FStar_Ident.lid_of_ids (FStar_List.append curmod.FStar_Ident.ns ((curmod.FStar_Ident.ident)::(mname)::[])))
in (let _61_810 = env
in {curmodule = Some (mscope); modules = _61_810.modules; open_namespaces = (curmod)::env.open_namespaces; sigaccum = _61_810.sigaccum; localbindings = _61_810.localbindings; recbindings = _61_810.recbindings; sigmap = _61_810.sigmap; default_result_effect = _61_810.default_result_effect; iface = _61_810.iface; admitted_iface = _61_810.admitted_iface; expect_typ = _61_810.expect_typ}))))

let exit_monad_scope = (fun env0 env -> (let _61_814 = env
in {curmodule = env0.curmodule; modules = _61_814.modules; open_namespaces = env0.open_namespaces; sigaccum = _61_814.sigaccum; localbindings = _61_814.localbindings; recbindings = _61_814.recbindings; sigmap = _61_814.sigmap; default_result_effect = _61_814.default_result_effect; iface = _61_814.iface; admitted_iface = _61_814.admitted_iface; expect_typ = _61_814.expect_typ}))

let fail_or = (fun lookup lid -> (match ((lookup lid)) with
| None -> begin
(let _152_502 = (let _152_501 = (let _152_500 = (FStar_Util.format1 "Identifier not found: [%s]" (FStar_Ident.text_of_lid lid))
in (_152_500, (FStar_Ident.range_of_lid lid)))
in FStar_Syntax_Syntax.Error (_152_501))
in (Prims.raise _152_502))
end
| Some (r) -> begin
r
end))

let fail_or2 = (fun lookup id -> (match ((lookup id)) with
| None -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (((Prims.strcat (Prims.strcat "Identifier not found [" id.FStar_Ident.idText) "]"), id.FStar_Ident.idRange))))
end
| Some (r) -> begin
r
end))




