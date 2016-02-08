
open Prims
type env =
{curmodule : FStar_Ident.lident Prims.option; modules : (FStar_Ident.lident * FStar_Syntax_Syntax.modul) Prims.list; open_namespaces : FStar_Ident.lident Prims.list; sigaccum : FStar_Syntax_Syntax.sigelts; localbindings : (FStar_Ident.ident * FStar_Syntax_Syntax.bv) Prims.list; recbindings : (FStar_Ident.ident * FStar_Ident.lident) Prims.list; sigmap : (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap Prims.list; default_result_effect : FStar_Ident.lident; iface : Prims.bool; admitted_iface : Prims.bool; expect_typ : Prims.bool}

let is_Mkenv : env  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv"))))

let open_modules : env  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.modul) Prims.list = (fun e -> e.modules)

let current_module : env  ->  FStar_Ident.lident = (fun env -> (match (env.curmodule) with
| None -> begin
(FStar_All.failwith "Unset current module")
end
| Some (m) -> begin
m
end))

let qual : FStar_Ident.lident  ->  FStar_Ident.ident  ->  FStar_Ident.lident = (fun lid id -> (let _167_43 = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns ((lid.FStar_Ident.ident)::(id)::[])))
in (FStar_Ident.set_lid_range _167_43 id.FStar_Ident.idRange)))

let qualify : env  ->  FStar_Ident.ident  ->  FStar_Ident.lident = (fun env id -> (let _167_48 = (current_module env)
in (qual _167_48 id)))

let qualify_lid : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (let cur = (current_module env)
in (let _167_53 = (FStar_Ident.lid_of_ids (FStar_List.append (FStar_List.append (FStar_List.append cur.FStar_Ident.ns ((cur.FStar_Ident.ident)::[])) lid.FStar_Ident.ns) ((lid.FStar_Ident.ident)::[])))
in (FStar_Ident.set_lid_range _167_53 (FStar_Ident.range_of_lid lid)))))

let new_sigmap = (fun _65_36 -> (match (()) with
| () -> begin
(FStar_Util.smap_create 100)
end))

let empty_env : Prims.unit  ->  env = (fun _65_37 -> (match (()) with
| () -> begin
(let _167_58 = (let _167_57 = (new_sigmap ())
in (_167_57)::[])
in {curmodule = None; modules = []; open_namespaces = []; sigaccum = []; localbindings = []; recbindings = []; sigmap = _167_58; default_result_effect = FStar_Syntax_Const.effect_ML_lid; iface = false; admitted_iface = false; expect_typ = false})
end))

let sigmap : env  ->  (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap = (fun env -> (FStar_List.hd env.sigmap))

let default_total : env  ->  env = (fun env -> (let _65_40 = env
in {curmodule = _65_40.curmodule; modules = _65_40.modules; open_namespaces = _65_40.open_namespaces; sigaccum = _65_40.sigaccum; localbindings = _65_40.localbindings; recbindings = _65_40.recbindings; sigmap = _65_40.sigmap; default_result_effect = FStar_Syntax_Const.effect_Tot_lid; iface = _65_40.iface; admitted_iface = _65_40.admitted_iface; expect_typ = _65_40.expect_typ}))

let default_ml : env  ->  env = (fun env -> (let _65_43 = env
in {curmodule = _65_43.curmodule; modules = _65_43.modules; open_namespaces = _65_43.open_namespaces; sigaccum = _65_43.sigaccum; localbindings = _65_43.localbindings; recbindings = _65_43.recbindings; sigmap = _65_43.sigmap; default_result_effect = FStar_Syntax_Const.effect_ML_lid; iface = _65_43.iface; admitted_iface = _65_43.admitted_iface; expect_typ = _65_43.expect_typ}))

let set_bv_range : FStar_Syntax_Syntax.bv  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.bv = (fun bv r -> (let id = (let _65_47 = bv.FStar_Syntax_Syntax.ppname
in {FStar_Ident.idText = _65_47.FStar_Ident.idText; FStar_Ident.idRange = r})
in (let _65_50 = bv
in {FStar_Syntax_Syntax.ppname = id; FStar_Syntax_Syntax.index = _65_50.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _65_50.FStar_Syntax_Syntax.sort})))

let bv_to_name : FStar_Syntax_Syntax.bv  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.term = (fun bv r -> (FStar_Syntax_Syntax.bv_to_name (set_bv_range bv r)))

let unmangleMap : (Prims.string * Prims.string) Prims.list = (("op_ColonColon", "Cons"))::(("not", "op_Negation"))::[]

let unmangleOpName : FStar_Ident.ident  ->  FStar_Ident.lident Prims.option = (fun id -> (FStar_Util.find_map unmangleMap (fun _65_57 -> (match (_65_57) with
| (x, y) -> begin
if (id.FStar_Ident.idText = x) then begin
(let _167_76 = (FStar_Ident.lid_of_path (("Prims")::(y)::[]) id.FStar_Ident.idRange)
in Some (_167_76))
end else begin
None
end
end))))

let try_lookup_id : env  ->  FStar_Ident.ident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env id -> (match ((unmangleOpName id)) with
| Some (l) -> begin
(let _167_81 = (FStar_Syntax_Syntax.fvar None l id.FStar_Ident.idRange)
in Some (_167_81))
end
| _65_63 -> begin
(FStar_Util.find_map env.localbindings (fun _65_1 -> (match (_65_1) with
| (id', x) when (id'.FStar_Ident.idText = id.FStar_Ident.idText) -> begin
(let _167_83 = (bv_to_name x id.FStar_Ident.idRange)
in Some (_167_83))
end
| _65_69 -> begin
None
end)))
end))

let resolve_in_open_namespaces = (fun env lid finder -> (let aux = (fun namespaces -> (match ((finder lid)) with
| Some (r) -> begin
Some (r)
end
| _65_79 -> begin
(let ids = (FStar_Ident.ids_of_lid lid)
in (FStar_Util.find_map namespaces (fun ns -> (let full_name = (FStar_Ident.lid_of_ids (FStar_List.append (FStar_Ident.ids_of_lid ns) ids))
in (finder full_name)))))
end))
in (let _167_98 = (let _167_97 = (current_module env)
in (_167_97)::env.open_namespaces)
in (aux _167_98))))

type foundname =
| Term_name of FStar_Syntax_Syntax.typ
| Eff_name of (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident)

let is_Term_name : foundname  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Term_name (_) -> begin
true
end
| _ -> begin
false
end))

let is_Eff_name : foundname  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Eff_name (_) -> begin
true
end
| _ -> begin
false
end))

let ___Term_name____0 : foundname  ->  FStar_Syntax_Syntax.typ = (fun projectee -> (match (projectee) with
| Term_name (_65_85) -> begin
_65_85
end))

let ___Eff_name____0 : foundname  ->  (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident) = (fun projectee -> (match (projectee) with
| Eff_name (_65_88) -> begin
_65_88
end))

let fv_qual_of_se : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.fv_qual Prims.option = (fun _65_3 -> (match (_65_3) with
| FStar_Syntax_Syntax.Sig_datacon (_65_91, _65_93, _65_95, l, _65_98, quals, _65_101, _65_103) -> begin
(let qopt = (FStar_Util.find_map quals (fun _65_2 -> (match (_65_2) with
| FStar_Syntax_Syntax.RecordConstructor (fs) -> begin
Some (FStar_Syntax_Syntax.Record_ctor ((l, fs)))
end
| _65_110 -> begin
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
| FStar_Syntax_Syntax.Sig_declare_typ (_65_115, _65_117, _65_119, quals, _65_122) -> begin
None
end
| _65_126 -> begin
None
end))

let try_lookup_name : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  foundname Prims.option = (fun any_val exclude_interf env lid -> (let find_in_sig = (fun lid -> (match ((let _167_140 = (sigmap env)
in (FStar_Util.smap_try_find _167_140 lid.FStar_Ident.str))) with
| Some (_65_134, true) when exclude_interf -> begin
None
end
| None -> begin
None
end
| Some (se, _65_141) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_65_145) -> begin
(let _167_142 = (let _167_141 = (FStar_Syntax_Syntax.fvar None lid (FStar_Ident.range_of_lid lid))
in Term_name (_167_141))
in Some (_167_142))
end
| FStar_Syntax_Syntax.Sig_datacon (_65_148) -> begin
(let _167_145 = (let _167_144 = (let _167_143 = (fv_qual_of_se se)
in (FStar_Syntax_Syntax.fvar _167_143 lid (FStar_Ident.range_of_lid lid)))
in Term_name (_167_144))
in Some (_167_145))
end
| FStar_Syntax_Syntax.Sig_let (_65_151) -> begin
(let _167_147 = (let _167_146 = (FStar_Syntax_Syntax.fvar None lid (FStar_Ident.range_of_lid lid))
in Term_name (_167_146))
in Some (_167_147))
end
| FStar_Syntax_Syntax.Sig_declare_typ (_65_154, _65_156, _65_158, quals, _65_161) -> begin
if (any_val || (FStar_All.pipe_right quals (FStar_Util.for_some (fun _65_4 -> (match (_65_4) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| _65_167 -> begin
false
end))))) then begin
(let _167_151 = (let _167_150 = (let _167_149 = (fv_qual_of_se se)
in (FStar_Syntax_Syntax.fvar _167_149 lid (FStar_Ident.range_of_lid lid)))
in Term_name (_167_150))
in Some (_167_151))
end else begin
None
end
end
| FStar_Syntax_Syntax.Sig_new_effect (ne, _65_170) -> begin
(let _167_154 = (let _167_153 = (let _167_152 = (FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname (FStar_Ident.range_of_lid lid))
in (se, _167_152))
in Eff_name (_167_153))
in Some (_167_154))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (_65_174) -> begin
Some (Eff_name ((se, lid)))
end
| _65_177 -> begin
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
in (FStar_Util.find_map env.recbindings (fun _65_185 -> (match (_65_185) with
| (id, l) -> begin
if (id.FStar_Ident.idText = lid.FStar_Ident.ident.FStar_Ident.idText) then begin
(let _167_158 = (let _167_157 = (let _167_156 = (FStar_Ident.set_lid_range l (FStar_Ident.range_of_lid lid))
in (FStar_Syntax_Syntax.fvar None _167_156 (FStar_Ident.range_of_lid lid)))
in Term_name (_167_157))
in Some (_167_158))
end else begin
None
end
end))))
end)
end
| _65_187 -> begin
None
end)
in (match (found_id) with
| Some (_65_190) -> begin
found_id
end
| _65_193 -> begin
(resolve_in_open_namespaces env lid find_in_sig)
end))))

let try_lookup_effect_name' : Prims.bool  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident) Prims.option = (fun exclude_interf env lid -> (match ((try_lookup_name true exclude_interf env lid)) with
| Some (Eff_name (o, l)) -> begin
Some ((o, l))
end
| _65_203 -> begin
None
end))

let try_lookup_effect_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env l -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some (o, l) -> begin
Some (l)
end
| _65_211 -> begin
None
end))

let try_lookup_effect_defn : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl Prims.option = (fun env l -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some (FStar_Syntax_Syntax.Sig_new_effect (ne, _65_216), _65_220) -> begin
Some (ne)
end
| _65_224 -> begin
None
end))

let is_effect_name : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((try_lookup_effect_name env lid)) with
| None -> begin
false
end
| Some (_65_229) -> begin
true
end))

let lookup_letbinding_quals : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.qualifier Prims.list = (fun env lid -> (let find_in_sig = (fun lid -> (match ((let _167_183 = (sigmap env)
in (FStar_Util.smap_try_find _167_183 lid.FStar_Ident.str))) with
| Some (FStar_Syntax_Syntax.Sig_declare_typ (lid, _65_237, _65_239, quals, _65_242), _65_246) -> begin
Some (quals)
end
| _65_250 -> begin
None
end))
in (match ((resolve_in_open_namespaces env lid find_in_sig)) with
| Some (quals) -> begin
quals
end
| _65_254 -> begin
[]
end)))

let try_lookup_module : env  ->  Prims.string Prims.list  ->  FStar_Syntax_Syntax.modul Prims.option = (fun env path -> (match ((FStar_List.tryFind (fun _65_259 -> (match (_65_259) with
| (mlid, modul) -> begin
((FStar_Ident.path_of_lid mlid) = path)
end)) env.modules)) with
| Some (_65_261, modul) -> begin
Some (modul)
end
| None -> begin
None
end))

let try_lookup_let : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env lid -> (let find_in_sig = (fun lid -> (match ((let _167_195 = (sigmap env)
in (FStar_Util.smap_try_find _167_195 lid.FStar_Ident.str))) with
| Some (FStar_Syntax_Syntax.Sig_let (_65_271), _65_274) -> begin
(let _167_196 = (FStar_Syntax_Syntax.fvar None lid (FStar_Ident.range_of_lid lid))
in Some (_167_196))
end
| _65_278 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))

let try_lookup_definition : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env lid -> (let find_in_sig = (fun lid -> (match ((let _167_203 = (sigmap env)
in (FStar_Util.smap_try_find _167_203 lid.FStar_Ident.str))) with
| Some (FStar_Syntax_Syntax.Sig_let (lbs, _65_285, _65_287, _65_289), _65_293) -> begin
(FStar_Util.find_map (Prims.snd lbs) (fun lb -> (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (lid') when (FStar_Ident.lid_equals lid lid') -> begin
Some (lb.FStar_Syntax_Syntax.lbdef)
end
| _65_300 -> begin
None
end)))
end
| _65_302 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))

let try_lookup_lid' : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun any_val exclude_interf env lid -> (match ((try_lookup_name any_val exclude_interf env lid)) with
| Some (Term_name (e)) -> begin
Some (e)
end
| _65_311 -> begin
None
end))

let try_lookup_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env l -> (try_lookup_lid' env.iface false env l))

let try_lookup_datacon : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.fv Prims.option = (fun env lid -> (let find_in_sig = (fun lid -> (match ((let _167_223 = (sigmap env)
in (FStar_Util.smap_try_find _167_223 lid.FStar_Ident.str))) with
| Some (FStar_Syntax_Syntax.Sig_declare_typ (_65_319, _65_321, _65_323, quals, _65_326), _65_330) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _65_5 -> (match (_65_5) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| _65_336 -> begin
false
end)))) then begin
(let _167_225 = (FStar_Syntax_Syntax.lid_as_fv lid None)
in Some (_167_225))
end else begin
None
end
end
| Some (FStar_Syntax_Syntax.Sig_datacon (_65_338), _65_341) -> begin
(let _167_226 = (FStar_Syntax_Syntax.lid_as_fv lid (Some (FStar_Syntax_Syntax.Data_ctor)))
in Some (_167_226))
end
| _65_345 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))

let find_all_datacons : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.list Prims.option = (fun env lid -> (let find_in_sig = (fun lid -> (match ((let _167_233 = (sigmap env)
in (FStar_Util.smap_try_find _167_233 lid.FStar_Ident.str))) with
| Some (FStar_Syntax_Syntax.Sig_inductive_typ (_65_351, _65_353, _65_355, _65_357, _65_359, datas, _65_362, _65_364), _65_368) -> begin
Some (datas)
end
| _65_372 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))

type record_or_dc =
{typename : FStar_Ident.lident; constrname : FStar_Ident.lident; parms : FStar_Syntax_Syntax.binders; fields : (FStar_Syntax_Syntax.fieldname * FStar_Syntax_Syntax.typ) Prims.list; is_record : Prims.bool}

let is_Mkrecord_or_dc : record_or_dc  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkrecord_or_dc"))))

let record_cache_aux : ((Prims.unit  ->  Prims.unit) * (Prims.unit  ->  Prims.unit) * (Prims.unit  ->  record_or_dc Prims.list) * (record_or_dc  ->  Prims.unit)) = (let record_cache = (FStar_Util.mk_ref (([])::[]))
in (let push = (fun _65_381 -> (match (()) with
| () -> begin
(let _167_263 = (let _167_262 = (let _167_260 = (FStar_ST.read record_cache)
in (FStar_List.hd _167_260))
in (let _167_261 = (FStar_ST.read record_cache)
in (_167_262)::_167_261))
in (FStar_ST.op_Colon_Equals record_cache _167_263))
end))
in (let pop = (fun _65_383 -> (match (()) with
| () -> begin
(let _167_267 = (let _167_266 = (FStar_ST.read record_cache)
in (FStar_List.tl _167_266))
in (FStar_ST.op_Colon_Equals record_cache _167_267))
end))
in (let peek = (fun _65_385 -> (match (()) with
| () -> begin
(let _167_270 = (FStar_ST.read record_cache)
in (FStar_List.hd _167_270))
end))
in (let insert = (fun r -> (let _167_277 = (let _167_276 = (let _167_273 = (peek ())
in (r)::_167_273)
in (let _167_275 = (let _167_274 = (FStar_ST.read record_cache)
in (FStar_List.tl _167_274))
in (_167_276)::_167_275))
in (FStar_ST.op_Colon_Equals record_cache _167_277)))
in (push, pop, peek, insert))))))

let push_record_cache : Prims.unit  ->  Prims.unit = (let _65_395 = record_cache_aux
in (match (_65_395) with
| (push, _65_390, _65_392, _65_394) -> begin
push
end))

let pop_record_cache : Prims.unit  ->  Prims.unit = (let _65_403 = record_cache_aux
in (match (_65_403) with
| (_65_397, pop, _65_400, _65_402) -> begin
pop
end))

let peek_record_cache : Prims.unit  ->  record_or_dc Prims.list = (let _65_411 = record_cache_aux
in (match (_65_411) with
| (_65_405, _65_407, peek, _65_410) -> begin
peek
end))

let insert_record_cache : record_or_dc  ->  Prims.unit = (let _65_419 = record_cache_aux
in (match (_65_419) with
| (_65_413, _65_415, _65_417, insert) -> begin
insert
end))

let extract_record : env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun e _65_9 -> (match (_65_9) with
| FStar_Syntax_Syntax.Sig_bundle (sigs, _65_424, _65_426, _65_428) -> begin
(let is_rec = (FStar_Util.for_some (fun _65_6 -> (match (_65_6) with
| (FStar_Syntax_Syntax.RecordType (_)) | (FStar_Syntax_Syntax.RecordConstructor (_)) -> begin
true
end
| _65_439 -> begin
false
end)))
in (let find_dc = (fun dc -> (FStar_All.pipe_right sigs (FStar_Util.find_opt (fun _65_7 -> (match (_65_7) with
| FStar_Syntax_Syntax.Sig_datacon (lid, _65_446, _65_448, _65_450, _65_452, _65_454, _65_456, _65_458) -> begin
(FStar_Ident.lid_equals dc lid)
end
| _65_462 -> begin
false
end)))))
in (FStar_All.pipe_right sigs (FStar_List.iter (fun _65_8 -> (match (_65_8) with
| FStar_Syntax_Syntax.Sig_inductive_typ (typename, univs, parms, _65_468, _65_470, dc::[], tags, _65_475) -> begin
(match ((let _167_348 = (find_dc dc)
in (FStar_All.pipe_left FStar_Util.must _167_348))) with
| FStar_Syntax_Syntax.Sig_datacon (constrname, _65_480, t, _65_483, _65_485, _65_487, _65_489, _65_491) -> begin
(let _65_497 = (FStar_Syntax_Util.arrow_formals t)
in (match (_65_497) with
| (formals, _65_496) -> begin
(let is_rec = (is_rec tags)
in (let fields = (FStar_All.pipe_right formals (FStar_List.collect (fun _65_501 -> (match (_65_501) with
| (x, q) -> begin
if ((FStar_Syntax_Syntax.is_null_bv x) || (is_rec && (q = Some (FStar_Syntax_Syntax.Implicit)))) then begin
[]
end else begin
(let _167_352 = (let _167_351 = (let _167_350 = if is_rec then begin
(FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname)
end else begin
x.FStar_Syntax_Syntax.ppname
end
in (qual constrname _167_350))
in (_167_351, x.FStar_Syntax_Syntax.sort))
in (_167_352)::[])
end
end))))
in (let record = {typename = typename; constrname = constrname; parms = parms; fields = fields; is_record = is_rec}
in (insert_record_cache record))))
end))
end
| _65_505 -> begin
()
end)
end
| _65_507 -> begin
()
end))))))
end
| _65_509 -> begin
()
end))

let try_lookup_record_or_dc_by_field_name : env  ->  FStar_Ident.lident  ->  (record_or_dc * FStar_Ident.lident) Prims.option = (fun env fieldname -> (let maybe_add_constrname = (fun ns c -> (let rec aux = (fun ns -> (match (ns) with
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
(let _167_363 = (aux tl)
in (hd)::_167_363)
end))
in (aux ns)))
in (let find_in_cache = (fun fieldname -> (let _65_527 = (fieldname.FStar_Ident.ns, fieldname.FStar_Ident.ident)
in (match (_65_527) with
| (ns, fieldname) -> begin
(let _167_368 = (peek_record_cache ())
in (FStar_Util.find_map _167_368 (fun record -> (let constrname = record.constrname.FStar_Ident.ident
in (let ns = (maybe_add_constrname ns constrname)
in (let fname = (FStar_Ident.lid_of_ids (FStar_List.append ns ((fieldname)::[])))
in (FStar_Util.find_map record.fields (fun _65_535 -> (match (_65_535) with
| (f, _65_534) -> begin
if (FStar_Ident.lid_equals fname f) then begin
Some ((record, fname))
end else begin
None
end
end)))))))))
end)))
in (resolve_in_open_namespaces env fieldname find_in_cache))))

let try_lookup_record_by_field_name : env  ->  FStar_Ident.lident  ->  (record_or_dc * FStar_Ident.lident) Prims.option = (fun env fieldname -> (match ((try_lookup_record_or_dc_by_field_name env fieldname)) with
| Some (r, f) when r.is_record -> begin
Some ((r, f))
end
| _65_543 -> begin
None
end))

let try_lookup_projector_by_field_name : env  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * Prims.bool) Prims.option = (fun env fieldname -> (match ((try_lookup_record_or_dc_by_field_name env fieldname)) with
| Some (r, f) -> begin
Some ((f, r.is_record))
end
| _65_551 -> begin
None
end))

let qualify_field_to_record : env  ->  record_or_dc  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env recd f -> (let qualify = (fun fieldname -> (let _65_559 = (fieldname.FStar_Ident.ns, fieldname.FStar_Ident.ident)
in (match (_65_559) with
| (ns, fieldname) -> begin
(let constrname = recd.constrname.FStar_Ident.ident
in (let fname = (FStar_Ident.lid_of_ids (FStar_List.append (FStar_List.append ns ((constrname)::[])) ((fieldname)::[])))
in (FStar_Util.find_map recd.fields (fun _65_565 -> (match (_65_565) with
| (f, _65_564) -> begin
if (FStar_Ident.lid_equals fname f) then begin
Some (fname)
end else begin
None
end
end)))))
end)))
in (resolve_in_open_namespaces env f qualify)))

let unique : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  Prims.bool = (fun any_val exclude_if env lid -> (let this_env = (let _65_570 = env
in {curmodule = _65_570.curmodule; modules = _65_570.modules; open_namespaces = []; sigaccum = _65_570.sigaccum; localbindings = _65_570.localbindings; recbindings = _65_570.recbindings; sigmap = _65_570.sigmap; default_result_effect = _65_570.default_result_effect; iface = _65_570.iface; admitted_iface = _65_570.admitted_iface; expect_typ = _65_570.expect_typ})
in (match ((try_lookup_lid' any_val exclude_if env lid)) with
| None -> begin
true
end
| Some (_65_575) -> begin
false
end)))

let push_bv : env  ->  FStar_Ident.ident  ->  (env * FStar_Syntax_Syntax.bv) = (fun env x -> (let bv = (FStar_Syntax_Syntax.gen_bv x.FStar_Ident.idText (Some (x.FStar_Ident.idRange)) FStar_Syntax_Syntax.tun)
in ((let _65_580 = env
in {curmodule = _65_580.curmodule; modules = _65_580.modules; open_namespaces = _65_580.open_namespaces; sigaccum = _65_580.sigaccum; localbindings = ((x, bv))::env.localbindings; recbindings = _65_580.recbindings; sigmap = _65_580.sigmap; default_result_effect = _65_580.default_result_effect; iface = _65_580.iface; admitted_iface = _65_580.admitted_iface; expect_typ = _65_580.expect_typ}), bv)))

let push_top_level_rec_binding : env  ->  FStar_Ident.ident  ->  env = (fun env x -> (let l = (qualify env x)
in if (unique false true env l) then begin
(let _65_585 = env
in {curmodule = _65_585.curmodule; modules = _65_585.modules; open_namespaces = _65_585.open_namespaces; sigaccum = _65_585.sigaccum; localbindings = _65_585.localbindings; recbindings = ((x, l))::env.recbindings; sigmap = _65_585.sigmap; default_result_effect = _65_585.default_result_effect; iface = _65_585.iface; admitted_iface = _65_585.admitted_iface; expect_typ = _65_585.expect_typ})
end else begin
(Prims.raise (FStar_Syntax_Syntax.Error (((Prims.strcat "Duplicate top-level names " l.FStar_Ident.str), (FStar_Ident.range_of_lid l)))))
end))

let push_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env s -> (let err = (fun l -> (let sopt = (let _167_408 = (sigmap env)
in (FStar_Util.smap_try_find _167_408 l.FStar_Ident.str))
in (let r = (match (sopt) with
| Some (se, _65_594) -> begin
(match ((let _167_409 = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_Util.find_opt (FStar_Ident.lid_equals l) _167_409))) with
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
in (let _167_412 = (let _167_411 = (let _167_410 = (FStar_Util.format2 "Duplicate top-level names [%s]; previously declared at %s" (FStar_Ident.text_of_lid l) r)
in (_167_410, (FStar_Ident.range_of_lid l)))
in FStar_Syntax_Syntax.Error (_167_411))
in (Prims.raise _167_412)))))
in (let env = (let _65_612 = (match (s) with
| FStar_Syntax_Syntax.Sig_let (_65_603) -> begin
(false, true)
end
| FStar_Syntax_Syntax.Sig_bundle (_65_606) -> begin
(true, true)
end
| _65_609 -> begin
(false, false)
end)
in (match (_65_612) with
| (any_val, exclude_if) -> begin
(let lids = (FStar_Syntax_Util.lids_of_sigelt s)
in (match ((FStar_Util.find_map lids (fun l -> if (not ((unique any_val exclude_if env l))) then begin
Some (l)
end else begin
None
end))) with
| None -> begin
(let _65_616 = (extract_record env s)
in (let _65_618 = env
in {curmodule = _65_618.curmodule; modules = _65_618.modules; open_namespaces = _65_618.open_namespaces; sigaccum = (s)::env.sigaccum; localbindings = _65_618.localbindings; recbindings = _65_618.recbindings; sigmap = _65_618.sigmap; default_result_effect = _65_618.default_result_effect; iface = _65_618.iface; admitted_iface = _65_618.admitted_iface; expect_typ = _65_618.expect_typ}))
end
| Some (l) -> begin
(err l)
end))
end))
in (let _65_637 = (match (s) with
| FStar_Syntax_Syntax.Sig_bundle (ses, _65_625, _65_627, _65_629) -> begin
(let _167_416 = (FStar_List.map (fun se -> (let _167_415 = (FStar_Syntax_Util.lids_of_sigelt se)
in (_167_415, se))) ses)
in (env, _167_416))
end
| _65_634 -> begin
(let _167_419 = (let _167_418 = (let _167_417 = (FStar_Syntax_Util.lids_of_sigelt s)
in (_167_417, s))
in (_167_418)::[])
in (env, _167_419))
end)
in (match (_65_637) with
| (env, lss) -> begin
(let _65_642 = (FStar_All.pipe_right lss (FStar_List.iter (fun _65_640 -> (match (_65_640) with
| (lids, se) -> begin
(FStar_All.pipe_right lids (FStar_List.iter (fun lid -> (let _167_422 = (sigmap env)
in (FStar_Util.smap_add _167_422 lid.FStar_Ident.str (se, (env.iface && (not (env.admitted_iface)))))))))
end))))
in env)
end)))))

let push_namespace : env  ->  FStar_Ident.lident  ->  env = (fun env lid -> (let _65_646 = env
in {curmodule = _65_646.curmodule; modules = _65_646.modules; open_namespaces = (lid)::env.open_namespaces; sigaccum = _65_646.sigaccum; localbindings = _65_646.localbindings; recbindings = _65_646.recbindings; sigmap = _65_646.sigmap; default_result_effect = _65_646.default_result_effect; iface = _65_646.iface; admitted_iface = _65_646.admitted_iface; expect_typ = _65_646.expect_typ}))

let check_admits : FStar_Ident.lident  ->  env  ->  Prims.unit = (fun nm env -> (let warn = (not ((let _167_432 = (FStar_ST.read FStar_Options.admit_fsi)
in (FStar_All.pipe_right _167_432 (FStar_Util.for_some (fun l -> (nm.FStar_Ident.str = l)))))))
in (FStar_All.pipe_right env.sigaccum (FStar_List.iter (fun se -> (match (se) with
| FStar_Syntax_Syntax.Sig_declare_typ (l, u, t, quals, r) -> begin
(match ((try_lookup_lid env l)) with
| None -> begin
(let _65_661 = if warn then begin
(let _167_436 = (let _167_435 = (FStar_Range.string_of_range (FStar_Ident.range_of_lid l))
in (let _167_434 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format2 "%s: Warning: Admitting %s without a definition\n" _167_435 _167_434)))
in (FStar_Util.print_string _167_436))
end else begin
()
end
in (let _167_437 = (sigmap env)
in (FStar_Util.smap_add _167_437 l.FStar_Ident.str (FStar_Syntax_Syntax.Sig_declare_typ ((l, u, t, (FStar_Syntax_Syntax.Assumption)::quals, r)), false))))
end
| Some (_65_664) -> begin
()
end)
end
| _65_667 -> begin
()
end))))))

let finish : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env modul -> (let _65_711 = (FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations (FStar_List.iter (fun _65_11 -> (match (_65_11) with
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _65_674, _65_676) -> begin
if (FStar_List.contains FStar_Syntax_Syntax.Private quals) then begin
(FStar_All.pipe_right ses (FStar_List.iter (fun _65_10 -> (match (_65_10) with
| FStar_Syntax_Syntax.Sig_datacon (lid, _65_682, _65_684, _65_686, _65_688, _65_690, _65_692, _65_694) -> begin
(let _167_444 = (sigmap env)
in (FStar_Util.smap_remove _167_444 lid.FStar_Ident.str))
end
| _65_698 -> begin
()
end))))
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _65_701, _65_703, quals, _65_706) -> begin
if (FStar_List.contains FStar_Syntax_Syntax.Private quals) then begin
(let _167_445 = (sigmap env)
in (FStar_Util.smap_remove _167_445 lid.FStar_Ident.str))
end else begin
()
end
end
| _65_710 -> begin
()
end))))
in (let _65_713 = env
in {curmodule = None; modules = ((modul.FStar_Syntax_Syntax.name, modul))::env.modules; open_namespaces = []; sigaccum = []; localbindings = []; recbindings = []; sigmap = _65_713.sigmap; default_result_effect = _65_713.default_result_effect; iface = _65_713.iface; admitted_iface = _65_713.admitted_iface; expect_typ = _65_713.expect_typ})))

let push : env  ->  env = (fun env -> (let _65_716 = (push_record_cache ())
in (let _65_718 = env
in (let _167_450 = (let _167_449 = (let _167_448 = (sigmap env)
in (FStar_Util.smap_copy _167_448))
in (_167_449)::env.sigmap)
in {curmodule = _65_718.curmodule; modules = _65_718.modules; open_namespaces = _65_718.open_namespaces; sigaccum = _65_718.sigaccum; localbindings = _65_718.localbindings; recbindings = _65_718.recbindings; sigmap = _167_450; default_result_effect = _65_718.default_result_effect; iface = _65_718.iface; admitted_iface = _65_718.admitted_iface; expect_typ = _65_718.expect_typ}))))

let mark : env  ->  env = (fun env -> (push env))

let reset_mark : env  ->  env = (fun env -> (let _65_722 = env
in (let _167_455 = (FStar_List.tl env.sigmap)
in {curmodule = _65_722.curmodule; modules = _65_722.modules; open_namespaces = _65_722.open_namespaces; sigaccum = _65_722.sigaccum; localbindings = _65_722.localbindings; recbindings = _65_722.recbindings; sigmap = _167_455; default_result_effect = _65_722.default_result_effect; iface = _65_722.iface; admitted_iface = _65_722.admitted_iface; expect_typ = _65_722.expect_typ})))

let commit_mark : env  ->  env = (fun env -> (match (env.sigmap) with
| hd::_65_727::tl -> begin
(let _65_731 = env
in {curmodule = _65_731.curmodule; modules = _65_731.modules; open_namespaces = _65_731.open_namespaces; sigaccum = _65_731.sigaccum; localbindings = _65_731.localbindings; recbindings = _65_731.recbindings; sigmap = (hd)::tl; default_result_effect = _65_731.default_result_effect; iface = _65_731.iface; admitted_iface = _65_731.admitted_iface; expect_typ = _65_731.expect_typ})
end
| _65_734 -> begin
(FStar_All.failwith "Impossible")
end))

let pop : env  ->  env = (fun env -> (match (env.sigmap) with
| _65_738::maps -> begin
(let _65_740 = (pop_record_cache ())
in (let _65_742 = env
in {curmodule = _65_742.curmodule; modules = _65_742.modules; open_namespaces = _65_742.open_namespaces; sigaccum = _65_742.sigaccum; localbindings = _65_742.localbindings; recbindings = _65_742.recbindings; sigmap = maps; default_result_effect = _65_742.default_result_effect; iface = _65_742.iface; admitted_iface = _65_742.admitted_iface; expect_typ = _65_742.expect_typ}))
end
| _65_745 -> begin
(FStar_All.failwith "No more modules to pop")
end))

let export_interface : FStar_Ident.lident  ->  env  ->  env = (fun m env -> (let sigelt_in_m = (fun se -> (match ((FStar_Syntax_Util.lids_of_sigelt se)) with
| l::_65_751 -> begin
(l.FStar_Ident.nsstr = m.FStar_Ident.str)
end
| _65_755 -> begin
false
end))
in (let sm = (sigmap env)
in (let env = (pop env)
in (let keys = (FStar_Util.smap_keys sm)
in (let sm' = (sigmap env)
in (let _65_779 = (FStar_All.pipe_right keys (FStar_List.iter (fun k -> (match ((FStar_Util.smap_try_find sm' k)) with
| Some (se, true) when (sigelt_in_m se) -> begin
(let _65_765 = (FStar_Util.smap_remove sm' k)
in (let se = (match (se) with
| FStar_Syntax_Syntax.Sig_declare_typ (l, u, t, q, r) -> begin
FStar_Syntax_Syntax.Sig_declare_typ ((l, u, t, (FStar_Syntax_Syntax.Assumption)::q, r))
end
| _65_775 -> begin
se
end)
in (FStar_Util.smap_add sm' k (se, false))))
end
| _65_778 -> begin
()
end))))
in env)))))))

let finish_module_or_interface : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env modul -> (let _65_783 = if (not (modul.FStar_Syntax_Syntax.is_interface)) then begin
(check_admits modul.FStar_Syntax_Syntax.name env)
end else begin
()
end
in (finish env modul)))

let prepare_module_or_interface : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  (env * Prims.bool) = (fun intf admitted env mname -> (let prep = (fun env -> (let open_ns = if (FStar_Ident.lid_equals mname FStar_Syntax_Const.prims_lid) then begin
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
in (let _65_792 = env
in {curmodule = Some (mname); modules = _65_792.modules; open_namespaces = open_ns; sigaccum = _65_792.sigaccum; localbindings = _65_792.localbindings; recbindings = _65_792.recbindings; sigmap = env.sigmap; default_result_effect = _65_792.default_result_effect; iface = intf; admitted_iface = admitted; expect_typ = _65_792.expect_typ})))
in (match ((FStar_All.pipe_right env.modules (FStar_Util.find_opt (fun _65_797 -> (match (_65_797) with
| (l, _65_796) -> begin
(FStar_Ident.lid_equals l mname)
end))))) with
| None -> begin
((prep env), false)
end
| Some (_65_800, m) -> begin
(let _65_804 = if ((not (m.FStar_Syntax_Syntax.is_interface)) || intf) then begin
(let _167_484 = (let _167_483 = (let _167_482 = (FStar_Util.format1 "Duplicate module or interface name: %s" mname.FStar_Ident.str)
in (_167_482, (FStar_Ident.range_of_lid mname)))
in FStar_Syntax_Syntax.Error (_167_483))
in (Prims.raise _167_484))
end else begin
()
end
in (let _167_486 = (let _167_485 = (push env)
in (prep _167_485))
in (_167_486, true)))
end)))

let enter_monad_scope : env  ->  FStar_Ident.ident  ->  env = (fun env mname -> (let curmod = (current_module env)
in (let mscope = (FStar_Ident.lid_of_ids (FStar_List.append curmod.FStar_Ident.ns ((curmod.FStar_Ident.ident)::(mname)::[])))
in (let _65_810 = env
in {curmodule = Some (mscope); modules = _65_810.modules; open_namespaces = (curmod)::env.open_namespaces; sigaccum = _65_810.sigaccum; localbindings = _65_810.localbindings; recbindings = _65_810.recbindings; sigmap = _65_810.sigmap; default_result_effect = _65_810.default_result_effect; iface = _65_810.iface; admitted_iface = _65_810.admitted_iface; expect_typ = _65_810.expect_typ}))))

let exit_monad_scope : env  ->  env  ->  env = (fun env0 env -> (let _65_814 = env
in {curmodule = env0.curmodule; modules = _65_814.modules; open_namespaces = env0.open_namespaces; sigaccum = _65_814.sigaccum; localbindings = _65_814.localbindings; recbindings = _65_814.recbindings; sigmap = _65_814.sigmap; default_result_effect = _65_814.default_result_effect; iface = _65_814.iface; admitted_iface = _65_814.admitted_iface; expect_typ = _65_814.expect_typ}))

let fail_or = (fun lookup lid -> (match ((lookup lid)) with
| None -> begin
(let _167_502 = (let _167_501 = (let _167_500 = (FStar_Util.format1 "Identifier not found: [%s]" (FStar_Ident.text_of_lid lid))
in (_167_500, (FStar_Ident.range_of_lid lid)))
in FStar_Syntax_Syntax.Error (_167_501))
in (Prims.raise _167_502))
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




