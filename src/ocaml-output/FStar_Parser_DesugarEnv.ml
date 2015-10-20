
open Prims
type binding =
| Binding_typ_var of FStar_Absyn_Syntax.ident
| Binding_var of FStar_Absyn_Syntax.ident
| Binding_let of FStar_Absyn_Syntax.lident
| Binding_tycon of FStar_Absyn_Syntax.lident

let is_Binding_typ_var = (fun _discr_ -> (match (_discr_) with
| Binding_typ_var (_) -> begin
true
end
| _ -> begin
false
end))

let is_Binding_var = (fun _discr_ -> (match (_discr_) with
| Binding_var (_) -> begin
true
end
| _ -> begin
false
end))

let is_Binding_let = (fun _discr_ -> (match (_discr_) with
| Binding_let (_) -> begin
true
end
| _ -> begin
false
end))

let is_Binding_tycon = (fun _discr_ -> (match (_discr_) with
| Binding_tycon (_) -> begin
true
end
| _ -> begin
false
end))

let ___Binding_typ_var____0 = (fun projectee -> (match (projectee) with
| Binding_typ_var (_42_18) -> begin
_42_18
end))

let ___Binding_var____0 = (fun projectee -> (match (projectee) with
| Binding_var (_42_21) -> begin
_42_21
end))

let ___Binding_let____0 = (fun projectee -> (match (projectee) with
| Binding_let (_42_24) -> begin
_42_24
end))

let ___Binding_tycon____0 = (fun projectee -> (match (projectee) with
| Binding_tycon (_42_27) -> begin
_42_27
end))

type kind_abbrev =
(FStar_Absyn_Syntax.lident * (FStar_Absyn_Syntax.btvdef, FStar_Absyn_Syntax.bvvdef) FStar_Util.either Prims.list * FStar_Absyn_Syntax.knd)

type env =
{curmodule : FStar_Absyn_Syntax.lident Prims.option; modules : (FStar_Absyn_Syntax.lident * FStar_Absyn_Syntax.modul) Prims.list; open_namespaces : FStar_Absyn_Syntax.lident Prims.list; sigaccum : FStar_Absyn_Syntax.sigelts; localbindings : ((FStar_Absyn_Syntax.btvdef, FStar_Absyn_Syntax.bvvdef) FStar_Util.either * binding) Prims.list; recbindings : binding Prims.list; phase : FStar_Parser_AST.level; sigmap : (FStar_Absyn_Syntax.sigelt * Prims.bool) FStar_Util.smap Prims.list; default_result_effect : FStar_Absyn_Syntax.typ  ->  FStar_Range.range  ->  FStar_Absyn_Syntax.comp; iface : Prims.bool; admitted_iface : Prims.bool}

let is_Mkenv = (Obj.magic (fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv")))

let open_modules = (fun e -> e.modules)

let current_module = (fun env -> (match (env.curmodule) with
| None -> begin
(FStar_All.failwith "Unset current module")
end
| Some (m) -> begin
m
end))

let qual = (fun lid id -> (let _107_111 = (FStar_Absyn_Syntax.lid_of_ids (FStar_List.append lid.FStar_Absyn_Syntax.ns ((lid.FStar_Absyn_Syntax.ident)::(id)::[])))
in (FStar_Absyn_Util.set_lid_range _107_111 id.FStar_Absyn_Syntax.idRange)))

let qualify = (fun env id -> (let _107_116 = (current_module env)
in (qual _107_116 id)))

let qualify_lid = (fun env lid -> (let cur = (current_module env)
in (let _107_122 = (FStar_Absyn_Syntax.lid_of_ids (FStar_List.append (FStar_List.append (FStar_List.append cur.FStar_Absyn_Syntax.ns ((cur.FStar_Absyn_Syntax.ident)::[])) lid.FStar_Absyn_Syntax.ns) ((lid.FStar_Absyn_Syntax.ident)::[])))
in (let _107_121 = (FStar_Absyn_Syntax.range_of_lid lid)
in (FStar_Absyn_Util.set_lid_range _107_122 _107_121)))))

let new_sigmap = (fun _42_52 -> (match (()) with
| () -> begin
(FStar_Util.smap_create 100)
end))

let empty_env = (fun _42_53 -> (match (()) with
| () -> begin
(let _107_127 = (let _107_126 = (new_sigmap ())
in (_107_126)::[])
in {curmodule = None; modules = []; open_namespaces = []; sigaccum = []; localbindings = []; recbindings = []; phase = FStar_Parser_AST.Un; sigmap = _107_127; default_result_effect = FStar_Absyn_Util.ml_comp; iface = false; admitted_iface = false})
end))

let sigmap = (fun env -> (FStar_List.hd env.sigmap))

let default_total = (fun env -> (let _42_56 = env
in {curmodule = _42_56.curmodule; modules = _42_56.modules; open_namespaces = _42_56.open_namespaces; sigaccum = _42_56.sigaccum; localbindings = _42_56.localbindings; recbindings = _42_56.recbindings; phase = _42_56.phase; sigmap = _42_56.sigmap; default_result_effect = (fun t _42_59 -> (FStar_Absyn_Syntax.mk_Total t)); iface = _42_56.iface; admitted_iface = _42_56.admitted_iface}))

let default_ml = (fun env -> (let _42_62 = env
in {curmodule = _42_62.curmodule; modules = _42_62.modules; open_namespaces = _42_62.open_namespaces; sigaccum = _42_62.sigaccum; localbindings = _42_62.localbindings; recbindings = _42_62.recbindings; phase = _42_62.phase; sigmap = _42_62.sigmap; default_result_effect = FStar_Absyn_Util.ml_comp; iface = _42_62.iface; admitted_iface = _42_62.admitted_iface}))

let range_of_binding = (fun _42_1 -> (match (_42_1) with
| (Binding_typ_var (id)) | (Binding_var (id)) -> begin
id.FStar_Absyn_Syntax.idRange
end
| (Binding_let (lid)) | (Binding_tycon (lid)) -> begin
(FStar_Absyn_Syntax.range_of_lid lid)
end))

let try_lookup_typ_var = (fun env id -> (let fopt = (FStar_List.tryFind (fun _42_76 -> (match (_42_76) with
| (_42_74, b) -> begin
(match (b) with
| (Binding_typ_var (id')) | (Binding_var (id')) -> begin
(id.FStar_Absyn_Syntax.idText = id'.FStar_Absyn_Syntax.idText)
end
| _42_81 -> begin
false
end)
end)) env.localbindings)
in (match (fopt) with
| Some (FStar_Util.Inl (bvd), Binding_typ_var (_42_86)) -> begin
(let _107_144 = (let _107_143 = (FStar_Absyn_Util.set_bvd_range bvd id.FStar_Absyn_Syntax.idRange)
in (FStar_Absyn_Util.bvd_to_typ _107_143 FStar_Absyn_Syntax.kun))
in Some (_107_144))
end
| _42_91 -> begin
None
end)))

let resolve_in_open_namespaces = (fun env lid finder -> (let aux = (fun namespaces -> (match ((finder lid)) with
| Some (r) -> begin
Some (r)
end
| _42_101 -> begin
(let ids = (FStar_Absyn_Syntax.ids_of_lid lid)
in (FStar_Util.find_map namespaces (fun ns -> (let full_name = (let _107_159 = (let _107_158 = (FStar_Absyn_Syntax.ids_of_lid ns)
in (FStar_List.append _107_158 ids))
in (FStar_Absyn_Syntax.lid_of_ids _107_159))
in (finder full_name)))))
end))
in (let _107_161 = (let _107_160 = (current_module env)
in (_107_160)::env.open_namespaces)
in (aux _107_161))))

let unmangleMap = (("op_ColonColon", "Cons"))::(("not", "op_Negation"))::[]

let unmangleOpName = (fun id -> (FStar_Util.find_map unmangleMap (fun _42_108 -> (match (_42_108) with
| (x, y) -> begin
(match ((id.FStar_Absyn_Syntax.idText = x)) with
| true -> begin
(let _107_165 = (FStar_Absyn_Syntax.lid_of_path (("Prims")::(y)::[]) id.FStar_Absyn_Syntax.idRange)
in Some (_107_165))
end
| false -> begin
None
end)
end))))

let try_lookup_id' = (fun env id -> (match ((unmangleOpName id)) with
| Some (l) -> begin
(let _107_173 = (let _107_172 = (let _107_171 = (let _107_170 = (FStar_Absyn_Util.fv l)
in (_107_170, None))
in (FStar_Absyn_Syntax.mk_Exp_fvar _107_171 None id.FStar_Absyn_Syntax.idRange))
in (l, _107_172))
in Some (_107_173))
end
| _42_114 -> begin
(let found = (FStar_Util.find_map env.localbindings (fun _42_2 -> (match (_42_2) with
| (FStar_Util.Inl (_42_117), Binding_typ_var (id')) when (id'.FStar_Absyn_Syntax.idText = id.FStar_Absyn_Syntax.idText) -> begin
Some (FStar_Util.Inl (()))
end
| (FStar_Util.Inr (bvd), Binding_var (id')) when (id'.FStar_Absyn_Syntax.idText = id.FStar_Absyn_Syntax.idText) -> begin
(let _107_179 = (let _107_178 = (let _107_177 = (FStar_Absyn_Syntax.lid_of_ids ((id')::[]))
in (let _107_176 = (let _107_175 = (FStar_Absyn_Util.set_bvd_range bvd id.FStar_Absyn_Syntax.idRange)
in (FStar_Absyn_Util.bvd_to_exp _107_175 FStar_Absyn_Syntax.tun))
in (_107_177, _107_176)))
in FStar_Util.Inr (_107_178))
in Some (_107_179))
end
| _42_128 -> begin
None
end)))
in (match (found) with
| Some (FStar_Util.Inr (x)) -> begin
Some (x)
end
| _42_134 -> begin
None
end))
end))

let try_lookup_id = (fun env id -> (match ((try_lookup_id' env id)) with
| Some (_42_138, e) -> begin
Some (e)
end
| None -> begin
None
end))

type occurrence =
| OSig of FStar_Absyn_Syntax.sigelt
| OLet of FStar_Absyn_Syntax.lident
| ORec of FStar_Absyn_Syntax.lident

let is_OSig = (fun _discr_ -> (match (_discr_) with
| OSig (_) -> begin
true
end
| _ -> begin
false
end))

let is_OLet = (fun _discr_ -> (match (_discr_) with
| OLet (_) -> begin
true
end
| _ -> begin
false
end))

let is_ORec = (fun _discr_ -> (match (_discr_) with
| ORec (_) -> begin
true
end
| _ -> begin
false
end))

let ___OSig____0 = (fun projectee -> (match (projectee) with
| OSig (_42_145) -> begin
_42_145
end))

let ___OLet____0 = (fun projectee -> (match (projectee) with
| OLet (_42_148) -> begin
_42_148
end))

let ___ORec____0 = (fun projectee -> (match (projectee) with
| ORec (_42_151) -> begin
_42_151
end))

let range_of_occurrence = (fun _42_3 -> (match (_42_3) with
| (OLet (l)) | (ORec (l)) -> begin
(FStar_Absyn_Syntax.range_of_lid l)
end
| OSig (se) -> begin
(FStar_Absyn_Util.range_of_sigelt se)
end))

type foundname =
| Exp_name of (occurrence * FStar_Absyn_Syntax.exp)
| Typ_name of (occurrence * FStar_Absyn_Syntax.typ)
| Eff_name of (occurrence * FStar_Absyn_Syntax.lident)
| Knd_name of (occurrence * FStar_Absyn_Syntax.lident)

let is_Exp_name = (fun _discr_ -> (match (_discr_) with
| Exp_name (_) -> begin
true
end
| _ -> begin
false
end))

let is_Typ_name = (fun _discr_ -> (match (_discr_) with
| Typ_name (_) -> begin
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

let is_Knd_name = (fun _discr_ -> (match (_discr_) with
| Knd_name (_) -> begin
true
end
| _ -> begin
false
end))

let ___Exp_name____0 = (fun projectee -> (match (projectee) with
| Exp_name (_42_160) -> begin
_42_160
end))

let ___Typ_name____0 = (fun projectee -> (match (projectee) with
| Typ_name (_42_163) -> begin
_42_163
end))

let ___Eff_name____0 = (fun projectee -> (match (projectee) with
| Eff_name (_42_166) -> begin
_42_166
end))

let ___Knd_name____0 = (fun projectee -> (match (projectee) with
| Knd_name (_42_169) -> begin
_42_169
end))

let fv_qual_of_se = (fun _42_5 -> (match (_42_5) with
| FStar_Absyn_Syntax.Sig_datacon (_42_172, _42_174, (l, _42_177, _42_179), quals, _42_183, _42_185) -> begin
(let qopt = (FStar_Util.find_map quals (fun _42_4 -> (match (_42_4) with
| FStar_Absyn_Syntax.RecordConstructor (fs) -> begin
Some (FStar_Absyn_Syntax.Record_ctor ((l, fs)))
end
| _42_192 -> begin
None
end)))
in (match (qopt) with
| None -> begin
Some (FStar_Absyn_Syntax.Data_ctor)
end
| x -> begin
x
end))
end
| FStar_Absyn_Syntax.Sig_val_decl (_42_197, _42_199, quals, _42_202) -> begin
None
end
| _42_206 -> begin
None
end))

let try_lookup_name = (fun any_val exclude_interf env lid -> (let find_in_sig = (fun lid -> (match ((let _107_297 = (sigmap env)
in (FStar_Util.smap_try_find _107_297 lid.FStar_Absyn_Syntax.str))) with
| Some (_42_214, true) when exclude_interf -> begin
None
end
| None -> begin
None
end
| Some (se, _42_221) -> begin
(match (se) with
| (FStar_Absyn_Syntax.Sig_typ_abbrev (_)) | (FStar_Absyn_Syntax.Sig_tycon (_)) -> begin
(let _107_300 = (let _107_299 = (let _107_298 = (FStar_Absyn_Util.ftv lid FStar_Absyn_Syntax.kun)
in (OSig (se), _107_298))
in Typ_name (_107_299))
in Some (_107_300))
end
| FStar_Absyn_Syntax.Sig_kind_abbrev (_42_231) -> begin
Some (Knd_name ((OSig (se), lid)))
end
| FStar_Absyn_Syntax.Sig_new_effect (ne, _42_235) -> begin
(let _107_304 = (let _107_303 = (let _107_302 = (let _107_301 = (FStar_Absyn_Syntax.range_of_lid lid)
in (FStar_Absyn_Util.set_lid_range ne.FStar_Absyn_Syntax.mname _107_301))
in (OSig (se), _107_302))
in Eff_name (_107_303))
in Some (_107_304))
end
| FStar_Absyn_Syntax.Sig_effect_abbrev (_42_239) -> begin
Some (Eff_name ((OSig (se), lid)))
end
| FStar_Absyn_Syntax.Sig_datacon (_42_242) -> begin
(let _107_309 = (let _107_308 = (let _107_307 = (let _107_306 = (fv_qual_of_se se)
in (let _107_305 = (FStar_Absyn_Syntax.range_of_lid lid)
in (FStar_Absyn_Util.fvar _107_306 lid _107_305)))
in (OSig (se), _107_307))
in Exp_name (_107_308))
in Some (_107_309))
end
| FStar_Absyn_Syntax.Sig_let (_42_245) -> begin
(let _107_313 = (let _107_312 = (let _107_311 = (let _107_310 = (FStar_Absyn_Syntax.range_of_lid lid)
in (FStar_Absyn_Util.fvar None lid _107_310))
in (OSig (se), _107_311))
in Exp_name (_107_312))
in Some (_107_313))
end
| FStar_Absyn_Syntax.Sig_val_decl (_42_248, _42_250, quals, _42_253) -> begin
(match ((any_val || (FStar_All.pipe_right quals (FStar_Util.for_some (fun _42_6 -> (match (_42_6) with
| FStar_Absyn_Syntax.Assumption -> begin
true
end
| _42_259 -> begin
false
end)))))) with
| true -> begin
(let _107_319 = (let _107_318 = (let _107_317 = (let _107_316 = (fv_qual_of_se se)
in (let _107_315 = (FStar_Absyn_Syntax.range_of_lid lid)
in (FStar_Absyn_Util.fvar _107_316 lid _107_315)))
in (OSig (se), _107_317))
in Exp_name (_107_318))
in Some (_107_319))
end
| false -> begin
None
end)
end
| _42_261 -> begin
None
end)
end))
in (let found_id = (match (lid.FStar_Absyn_Syntax.ns) with
| [] -> begin
(match ((try_lookup_id' env lid.FStar_Absyn_Syntax.ident)) with
| Some (lid, e) -> begin
Some (Exp_name ((OLet (lid), e)))
end
| None -> begin
(let recname = (qualify env lid.FStar_Absyn_Syntax.ident)
in (FStar_Util.find_map env.recbindings (fun _42_7 -> (match (_42_7) with
| Binding_let (l) when (FStar_Absyn_Syntax.lid_equals l recname) -> begin
(let _107_324 = (let _107_323 = (let _107_322 = (let _107_321 = (FStar_Absyn_Syntax.range_of_lid recname)
in (FStar_Absyn_Util.fvar None recname _107_321))
in (ORec (l), _107_322))
in Exp_name (_107_323))
in Some (_107_324))
end
| Binding_tycon (l) when (FStar_Absyn_Syntax.lid_equals l recname) -> begin
(let _107_327 = (let _107_326 = (let _107_325 = (FStar_Absyn_Util.ftv recname FStar_Absyn_Syntax.kun)
in (ORec (l), _107_325))
in Typ_name (_107_326))
in Some (_107_327))
end
| _42_275 -> begin
None
end))))
end)
end
| _42_277 -> begin
None
end)
in (match (found_id) with
| Some (_42_280) -> begin
found_id
end
| _42_283 -> begin
(resolve_in_open_namespaces env lid find_in_sig)
end))))

let try_lookup_typ_name' = (fun exclude_interf env lid -> (match ((try_lookup_name true exclude_interf env lid)) with
| Some (Typ_name (_42_288, t)) -> begin
Some (t)
end
| Some (Eff_name (_42_294, l)) -> begin
(let _107_334 = (FStar_Absyn_Util.ftv l FStar_Absyn_Syntax.mk_Kind_unknown)
in Some (_107_334))
end
| _42_300 -> begin
None
end))

let try_lookup_typ_name = (fun env l -> (try_lookup_typ_name' (not (env.iface)) env l))

let try_lookup_effect_name' = (fun exclude_interf env lid -> (match ((try_lookup_name true exclude_interf env lid)) with
| Some (Eff_name (o, l)) -> begin
Some ((o, l))
end
| _42_312 -> begin
None
end))

let try_lookup_effect_name = (fun env l -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some (o, l) -> begin
Some (l)
end
| _42_320 -> begin
None
end))

let try_lookup_effect_defn = (fun env l -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some (OSig (FStar_Absyn_Syntax.Sig_new_effect (ne, _42_325)), _42_330) -> begin
Some (ne)
end
| _42_334 -> begin
None
end))

let is_effect_name = (fun env lid -> (match ((try_lookup_effect_name env lid)) with
| None -> begin
false
end
| Some (_42_339) -> begin
true
end))

let try_resolve_typ_abbrev = (fun env lid -> (let find_in_sig = (fun lid -> (match ((let _107_363 = (sigmap env)
in (FStar_Util.smap_try_find _107_363 lid.FStar_Absyn_Syntax.str))) with
| Some (FStar_Absyn_Syntax.Sig_typ_abbrev (lid, tps, k, def, _42_350, _42_352), _42_356) -> begin
(let t = (let _107_366 = (let _107_365 = (let _107_364 = (FStar_Absyn_Util.close_with_lam tps def)
in (_107_364, lid))
in FStar_Absyn_Syntax.Meta_named (_107_365))
in (FStar_Absyn_Syntax.mk_Typ_meta _107_366))
in Some (t))
end
| _42_361 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))

let lookup_letbinding_quals = (fun env lid -> (let find_in_sig = (fun lid -> (match ((let _107_373 = (sigmap env)
in (FStar_Util.smap_try_find _107_373 lid.FStar_Absyn_Syntax.str))) with
| Some (FStar_Absyn_Syntax.Sig_val_decl (lid, _42_368, quals, _42_371), _42_375) -> begin
Some (quals)
end
| _42_379 -> begin
None
end))
in (match ((resolve_in_open_namespaces env lid find_in_sig)) with
| Some (quals) -> begin
quals
end
| _42_383 -> begin
[]
end)))

let try_lookup_module = (fun env path -> (match ((FStar_List.tryFind (fun _42_388 -> (match (_42_388) with
| (mlid, modul) -> begin
((FStar_Absyn_Syntax.path_of_lid mlid) = path)
end)) env.modules)) with
| Some (_42_390, modul) -> begin
Some (modul)
end
| None -> begin
None
end))

let try_lookup_let = (fun env lid -> (let find_in_sig = (fun lid -> (match ((let _107_385 = (sigmap env)
in (FStar_Util.smap_try_find _107_385 lid.FStar_Absyn_Syntax.str))) with
| Some (FStar_Absyn_Syntax.Sig_let (_42_400), _42_403) -> begin
(let _107_387 = (let _107_386 = (FStar_Absyn_Syntax.range_of_lid lid)
in (FStar_Absyn_Util.fvar None lid _107_386))
in Some (_107_387))
end
| _42_407 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))

let try_lookup_lid' = (fun any_val exclude_interf env lid -> (match ((try_lookup_name any_val exclude_interf env lid)) with
| Some (Exp_name (_42_413, e)) -> begin
Some (e)
end
| _42_419 -> begin
None
end))

let try_lookup_lid = (fun env l -> (try_lookup_lid' env.iface false env l))

let try_lookup_datacon = (fun env lid -> (let find_in_sig = (fun lid -> (match ((let _107_406 = (sigmap env)
in (FStar_Util.smap_try_find _107_406 lid.FStar_Absyn_Syntax.str))) with
| Some (FStar_Absyn_Syntax.Sig_val_decl (_42_427, _42_429, quals, _42_432), _42_436) -> begin
(match ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _42_8 -> (match (_42_8) with
| FStar_Absyn_Syntax.Assumption -> begin
true
end
| _42_442 -> begin
false
end))))) with
| true -> begin
(let _107_408 = (FStar_Absyn_Util.fv lid)
in Some (_107_408))
end
| false -> begin
None
end)
end
| Some (FStar_Absyn_Syntax.Sig_datacon (_42_444), _42_447) -> begin
(let _107_409 = (FStar_Absyn_Util.fv lid)
in Some (_107_409))
end
| _42_451 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))

let find_all_datacons = (fun env lid -> (let find_in_sig = (fun lid -> (match ((let _107_416 = (sigmap env)
in (FStar_Util.smap_try_find _107_416 lid.FStar_Absyn_Syntax.str))) with
| Some (FStar_Absyn_Syntax.Sig_tycon (_42_457, _42_459, _42_461, _42_463, datas, _42_466, _42_468), _42_472) -> begin
Some (datas)
end
| _42_476 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))

type record_or_dc =
{typename : FStar_Absyn_Syntax.lident; constrname : FStar_Absyn_Syntax.lident; parms : FStar_Absyn_Syntax.binders; fields : (FStar_Absyn_Syntax.fieldname * FStar_Absyn_Syntax.typ) Prims.list; is_record : Prims.bool}

let is_Mkrecord_or_dc = (Obj.magic (fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkrecord_or_dc")))

let record_cache = (FStar_Util.mk_ref [])

let extract_record = (fun e _42_12 -> (match (_42_12) with
| FStar_Absyn_Syntax.Sig_bundle (sigs, _42_487, _42_489, _42_491) -> begin
(let is_rec = (FStar_Util.for_some (fun _42_9 -> (match (_42_9) with
| (FStar_Absyn_Syntax.RecordType (_)) | (FStar_Absyn_Syntax.RecordConstructor (_)) -> begin
true
end
| _42_502 -> begin
false
end)))
in (let find_dc = (fun dc -> (FStar_All.pipe_right sigs (FStar_Util.find_opt (fun _42_10 -> (match (_42_10) with
| FStar_Absyn_Syntax.Sig_datacon (lid, _42_509, _42_511, _42_513, _42_515, _42_517) -> begin
(FStar_Absyn_Syntax.lid_equals dc lid)
end
| _42_521 -> begin
false
end)))))
in (FStar_All.pipe_right sigs (FStar_List.iter (fun _42_11 -> (match (_42_11) with
| FStar_Absyn_Syntax.Sig_tycon (typename, parms, _42_526, _42_528, dc::[], tags, _42_533) -> begin
(match ((let _107_443 = (find_dc dc)
in (FStar_All.pipe_left FStar_Util.must _107_443))) with
| FStar_Absyn_Syntax.Sig_datacon (constrname, t, _42_539, _42_541, _42_543, _42_545) -> begin
(let formals = (match ((FStar_Absyn_Util.function_formals t)) with
| Some (x, _42_550) -> begin
x
end
| _42_554 -> begin
[]
end)
in (let fields = (FStar_All.pipe_right formals (FStar_List.collect (fun b -> (match (b) with
| (FStar_Util.Inr (x), q) -> begin
(match (((FStar_Absyn_Syntax.is_null_binder b) || (q = Some (FStar_Absyn_Syntax.Implicit)))) with
| true -> begin
[]
end
| false -> begin
(let _107_447 = (let _107_446 = (let _107_445 = (match ((is_rec tags)) with
| true -> begin
(FStar_Absyn_Util.unmangle_field_name x.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ppname)
end
| false -> begin
x.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ppname
end)
in (qual constrname _107_445))
in (_107_446, x.FStar_Absyn_Syntax.sort))
in (_107_447)::[])
end)
end
| _42_562 -> begin
[]
end))))
in (let record = (let _107_448 = (is_rec tags)
in {typename = typename; constrname = constrname; parms = parms; fields = fields; is_record = _107_448})
in (let _107_450 = (let _107_449 = (FStar_ST.read record_cache)
in (record)::_107_449)
in (FStar_ST.op_Colon_Equals record_cache _107_450)))))
end
| _42_566 -> begin
()
end)
end
| _42_568 -> begin
()
end))))))
end
| _42_570 -> begin
()
end))

let try_lookup_record_or_dc_by_field_name = (fun env fieldname -> (let maybe_add_constrname = (fun ns c -> (let rec aux = (fun ns -> (match (ns) with
| [] -> begin
(c)::[]
end
| c'::[] -> begin
(match ((c'.FStar_Absyn_Syntax.idText = c.FStar_Absyn_Syntax.idText)) with
| true -> begin
(c)::[]
end
| false -> begin
(c')::(c)::[]
end)
end
| hd::tl -> begin
(let _107_461 = (aux tl)
in (hd)::_107_461)
end))
in (aux ns)))
in (let find_in_cache = (fun fieldname -> (let _42_588 = (fieldname.FStar_Absyn_Syntax.ns, fieldname.FStar_Absyn_Syntax.ident)
in (match (_42_588) with
| (ns, fieldname) -> begin
(let _107_466 = (FStar_ST.read record_cache)
in (FStar_Util.find_map _107_466 (fun record -> (let constrname = record.constrname.FStar_Absyn_Syntax.ident
in (let ns = (maybe_add_constrname ns constrname)
in (let fname = (FStar_Absyn_Syntax.lid_of_ids (FStar_List.append ns ((fieldname)::[])))
in (FStar_Util.find_map record.fields (fun _42_596 -> (match (_42_596) with
| (f, _42_595) -> begin
(match ((FStar_Absyn_Syntax.lid_equals fname f)) with
| true -> begin
Some ((record, fname))
end
| false -> begin
None
end)
end)))))))))
end)))
in (resolve_in_open_namespaces env fieldname find_in_cache))))

let try_lookup_record_by_field_name = (fun env fieldname -> (match ((try_lookup_record_or_dc_by_field_name env fieldname)) with
| Some (r, f) when r.is_record -> begin
Some ((r, f))
end
| _42_604 -> begin
None
end))

let try_lookup_projector_by_field_name = (fun env fieldname -> (match ((try_lookup_record_or_dc_by_field_name env fieldname)) with
| Some (r, f) -> begin
Some ((f, r.is_record))
end
| _42_612 -> begin
None
end))

let qualify_field_to_record = (fun env recd f -> (let qualify = (fun fieldname -> (let _42_620 = (fieldname.FStar_Absyn_Syntax.ns, fieldname.FStar_Absyn_Syntax.ident)
in (match (_42_620) with
| (ns, fieldname) -> begin
(let constrname = recd.constrname.FStar_Absyn_Syntax.ident
in (let fname = (FStar_Absyn_Syntax.lid_of_ids (FStar_List.append (FStar_List.append ns ((constrname)::[])) ((fieldname)::[])))
in (FStar_Util.find_map recd.fields (fun _42_626 -> (match (_42_626) with
| (f, _42_625) -> begin
(match ((FStar_Absyn_Syntax.lid_equals fname f)) with
| true -> begin
Some (fname)
end
| false -> begin
None
end)
end)))))
end)))
in (resolve_in_open_namespaces env f qualify)))

let find_kind_abbrev = (fun env l -> (match ((try_lookup_name true (not (env.iface)) env l)) with
| Some (Knd_name (_42_630, l)) -> begin
Some (l)
end
| _42_636 -> begin
None
end))

let is_kind_abbrev = (fun env l -> (match ((find_kind_abbrev env l)) with
| None -> begin
false
end
| Some (_42_641) -> begin
true
end))

let unique_name = (fun any_val exclude_if env lid -> (match ((try_lookup_lid' any_val exclude_if env lid)) with
| None -> begin
(match ((find_kind_abbrev env lid)) with
| None -> begin
true
end
| Some (_42_650) -> begin
false
end)
end
| Some (_42_653) -> begin
false
end))

let unique_typ_name = (fun env lid -> (match ((try_lookup_typ_name' true env lid)) with
| None -> begin
true
end
| Some (a) -> begin
false
end))

let unique = (fun any_val exclude_if env lid -> (let this_env = (let _42_664 = env
in {curmodule = _42_664.curmodule; modules = _42_664.modules; open_namespaces = []; sigaccum = _42_664.sigaccum; localbindings = _42_664.localbindings; recbindings = _42_664.recbindings; phase = _42_664.phase; sigmap = _42_664.sigmap; default_result_effect = _42_664.default_result_effect; iface = _42_664.iface; admitted_iface = _42_664.admitted_iface})
in ((unique_name any_val exclude_if this_env lid) && (unique_typ_name this_env lid))))

let gen_bvd = (fun _42_13 -> (match (_42_13) with
| Binding_typ_var (id) -> begin
(let _107_515 = (let _107_514 = (let _107_513 = (FStar_Absyn_Util.genident (Some (id.FStar_Absyn_Syntax.idRange)))
in (id, _107_513))
in (FStar_Absyn_Util.mkbvd _107_514))
in FStar_Util.Inl (_107_515))
end
| Binding_var (id) -> begin
(let _107_518 = (let _107_517 = (let _107_516 = (FStar_Absyn_Util.genident (Some (id.FStar_Absyn_Syntax.idRange)))
in (id, _107_516))
in (FStar_Absyn_Util.mkbvd _107_517))
in FStar_Util.Inr (_107_518))
end
| _42_673 -> begin
(FStar_All.failwith "Tried to generate a bound variable for a type constructor")
end))

let push_bvvdef = (fun env x -> (let b = Binding_var (x.FStar_Absyn_Syntax.ppname)
in (let _42_677 = env
in {curmodule = _42_677.curmodule; modules = _42_677.modules; open_namespaces = _42_677.open_namespaces; sigaccum = _42_677.sigaccum; localbindings = ((FStar_Util.Inr (x), b))::env.localbindings; recbindings = _42_677.recbindings; phase = _42_677.phase; sigmap = _42_677.sigmap; default_result_effect = _42_677.default_result_effect; iface = _42_677.iface; admitted_iface = _42_677.admitted_iface})))

let push_btvdef = (fun env x -> (let b = Binding_typ_var (x.FStar_Absyn_Syntax.ppname)
in (let _42_682 = env
in {curmodule = _42_682.curmodule; modules = _42_682.modules; open_namespaces = _42_682.open_namespaces; sigaccum = _42_682.sigaccum; localbindings = ((FStar_Util.Inl (x), b))::env.localbindings; recbindings = _42_682.recbindings; phase = _42_682.phase; sigmap = _42_682.sigmap; default_result_effect = _42_682.default_result_effect; iface = _42_682.iface; admitted_iface = _42_682.admitted_iface})))

let push_local_binding = (fun env b -> (let bvd = (gen_bvd b)
in ((let _42_687 = env
in {curmodule = _42_687.curmodule; modules = _42_687.modules; open_namespaces = _42_687.open_namespaces; sigaccum = _42_687.sigaccum; localbindings = ((bvd, b))::env.localbindings; recbindings = _42_687.recbindings; phase = _42_687.phase; sigmap = _42_687.sigmap; default_result_effect = _42_687.default_result_effect; iface = _42_687.iface; admitted_iface = _42_687.admitted_iface}), bvd)))

let push_local_tbinding = (fun env a -> (match ((push_local_binding env (Binding_typ_var (a)))) with
| (env, FStar_Util.Inl (x)) -> begin
(env, x)
end
| _42_696 -> begin
(FStar_All.failwith "impossible")
end))

let push_local_vbinding = (fun env b -> (match ((push_local_binding env (Binding_var (b)))) with
| (env, FStar_Util.Inr (x)) -> begin
(env, x)
end
| _42_704 -> begin
(FStar_All.failwith "impossible")
end))

let push_rec_binding = (fun env b -> (match (b) with
| (Binding_let (lid)) | (Binding_tycon (lid)) -> begin
(match ((unique false true env lid)) with
| true -> begin
(let _42_710 = env
in {curmodule = _42_710.curmodule; modules = _42_710.modules; open_namespaces = _42_710.open_namespaces; sigaccum = _42_710.sigaccum; localbindings = _42_710.localbindings; recbindings = (b)::env.recbindings; phase = _42_710.phase; sigmap = _42_710.sigmap; default_result_effect = _42_710.default_result_effect; iface = _42_710.iface; admitted_iface = _42_710.admitted_iface})
end
| false -> begin
(let _107_545 = (let _107_544 = (let _107_543 = (FStar_Absyn_Syntax.range_of_lid lid)
in ((Prims.strcat "Duplicate top-level names " lid.FStar_Absyn_Syntax.str), _107_543))
in FStar_Absyn_Syntax.Error (_107_544))
in (Prims.raise _107_545))
end)
end
| _42_713 -> begin
(FStar_All.failwith "Unexpected rec_binding")
end))

let push_sigelt = (fun env s -> (let err = (fun l -> (let sopt = (let _107_552 = (sigmap env)
in (FStar_Util.smap_try_find _107_552 l.FStar_Absyn_Syntax.str))
in (let r = (match (sopt) with
| Some (se, _42_721) -> begin
(match ((let _107_553 = (FStar_Absyn_Util.lids_of_sigelt se)
in (FStar_Util.find_opt (FStar_Absyn_Syntax.lid_equals l) _107_553))) with
| Some (l) -> begin
(let _107_554 = (FStar_Absyn_Syntax.range_of_lid l)
in (FStar_All.pipe_left FStar_Range.string_of_range _107_554))
end
| None -> begin
"<unknown>"
end)
end
| None -> begin
"<unknown>"
end)
in (let _107_559 = (let _107_558 = (let _107_557 = (let _107_555 = (FStar_Absyn_Syntax.text_of_lid l)
in (FStar_Util.format2 "Duplicate top-level names [%s]; previously declared at %s" _107_555 r))
in (let _107_556 = (FStar_Absyn_Syntax.range_of_lid l)
in (_107_557, _107_556)))
in FStar_Absyn_Syntax.Error (_107_558))
in (Prims.raise _107_559)))))
in (let env = (let _42_739 = (match (s) with
| FStar_Absyn_Syntax.Sig_let (_42_730) -> begin
(false, true)
end
| FStar_Absyn_Syntax.Sig_bundle (_42_733) -> begin
(true, true)
end
| _42_736 -> begin
(false, false)
end)
in (match (_42_739) with
| (any_val, exclude_if) -> begin
(let lids = (FStar_Absyn_Util.lids_of_sigelt s)
in (match ((FStar_Util.find_map lids (fun l -> (match ((not ((unique any_val exclude_if env l)))) with
| true -> begin
Some (l)
end
| false -> begin
None
end)))) with
| None -> begin
(let _42_743 = (extract_record env s)
in (let _42_745 = env
in {curmodule = _42_745.curmodule; modules = _42_745.modules; open_namespaces = _42_745.open_namespaces; sigaccum = (s)::env.sigaccum; localbindings = _42_745.localbindings; recbindings = _42_745.recbindings; phase = _42_745.phase; sigmap = _42_745.sigmap; default_result_effect = _42_745.default_result_effect; iface = _42_745.iface; admitted_iface = _42_745.admitted_iface}))
end
| Some (l) -> begin
(err l)
end))
end))
in (let _42_764 = (match (s) with
| FStar_Absyn_Syntax.Sig_bundle (ses, _42_752, _42_754, _42_756) -> begin
(let _107_563 = (FStar_List.map (fun se -> (let _107_562 = (FStar_Absyn_Util.lids_of_sigelt se)
in (_107_562, se))) ses)
in (env, _107_563))
end
| _42_761 -> begin
(let _107_566 = (let _107_565 = (let _107_564 = (FStar_Absyn_Util.lids_of_sigelt s)
in (_107_564, s))
in (_107_565)::[])
in (env, _107_566))
end)
in (match (_42_764) with
| (env, lss) -> begin
(let _42_769 = (FStar_All.pipe_right lss (FStar_List.iter (fun _42_767 -> (match (_42_767) with
| (lids, se) -> begin
(FStar_All.pipe_right lids (FStar_List.iter (fun lid -> (let _107_569 = (sigmap env)
in (FStar_Util.smap_add _107_569 lid.FStar_Absyn_Syntax.str (se, (env.iface && (not (env.admitted_iface)))))))))
end))))
in env)
end)))))

let push_namespace = (fun env lid -> (let _42_773 = env
in {curmodule = _42_773.curmodule; modules = _42_773.modules; open_namespaces = (lid)::env.open_namespaces; sigaccum = _42_773.sigaccum; localbindings = _42_773.localbindings; recbindings = _42_773.recbindings; phase = _42_773.phase; sigmap = _42_773.sigmap; default_result_effect = _42_773.default_result_effect; iface = _42_773.iface; admitted_iface = _42_773.admitted_iface}))

let is_type_lid = (fun env lid -> (let aux = (fun _42_778 -> (match (()) with
| () -> begin
(match ((try_lookup_typ_name' false env lid)) with
| Some (_42_780) -> begin
true
end
| _42_783 -> begin
false
end)
end))
in (match ((lid.FStar_Absyn_Syntax.ns = [])) with
| true -> begin
(match ((try_lookup_id env lid.FStar_Absyn_Syntax.ident)) with
| Some (_42_785) -> begin
false
end
| _42_788 -> begin
(aux ())
end)
end
| false -> begin
(aux ())
end)))

let check_admits = (fun nm env -> (let warn = (not ((let _107_585 = (FStar_ST.read FStar_Options.admit_fsi)
in (FStar_All.pipe_right _107_585 (FStar_Util.for_some (fun l -> (nm.FStar_Absyn_Syntax.str = l)))))))
in (FStar_All.pipe_right env.sigaccum (FStar_List.iter (fun se -> (match (se) with
| FStar_Absyn_Syntax.Sig_val_decl (l, t, quals, r) -> begin
(match ((try_lookup_lid env l)) with
| None -> begin
(let _42_801 = (match (warn) with
| true -> begin
(let _107_590 = (let _107_589 = (let _107_587 = (FStar_Absyn_Syntax.range_of_lid l)
in (FStar_Range.string_of_range _107_587))
in (let _107_588 = (FStar_Absyn_Print.sli l)
in (FStar_Util.format2 "%s: Warning: Admitting %s without a definition\n" _107_589 _107_588)))
in (FStar_Util.print_string _107_590))
end
| false -> begin
()
end)
in (let _107_591 = (sigmap env)
in (FStar_Util.smap_add _107_591 l.FStar_Absyn_Syntax.str (FStar_Absyn_Syntax.Sig_val_decl ((l, t, (FStar_Absyn_Syntax.Assumption)::quals, r)), false))))
end
| Some (_42_804) -> begin
()
end)
end
| _42_807 -> begin
()
end))))))

let finish = (fun env modul -> (let _42_845 = (FStar_All.pipe_right modul.FStar_Absyn_Syntax.declarations (FStar_List.iter (fun _42_15 -> (match (_42_15) with
| FStar_Absyn_Syntax.Sig_bundle (ses, quals, _42_814, _42_816) -> begin
(match ((FStar_List.contains FStar_Absyn_Syntax.Private quals)) with
| true -> begin
(FStar_All.pipe_right ses (FStar_List.iter (fun _42_14 -> (match (_42_14) with
| FStar_Absyn_Syntax.Sig_datacon (lid, _42_822, _42_824, _42_826, _42_828, _42_830) -> begin
(let _107_598 = (sigmap env)
in (FStar_Util.smap_remove _107_598 lid.FStar_Absyn_Syntax.str))
end
| _42_834 -> begin
()
end))))
end
| false -> begin
()
end)
end
| FStar_Absyn_Syntax.Sig_val_decl (lid, _42_837, quals, _42_840) -> begin
(match ((FStar_List.contains FStar_Absyn_Syntax.Private quals)) with
| true -> begin
(let _107_599 = (sigmap env)
in (FStar_Util.smap_remove _107_599 lid.FStar_Absyn_Syntax.str))
end
| false -> begin
()
end)
end
| _42_844 -> begin
()
end))))
in (let _42_847 = env
in {curmodule = None; modules = ((modul.FStar_Absyn_Syntax.name, modul))::env.modules; open_namespaces = []; sigaccum = []; localbindings = []; recbindings = []; phase = FStar_Parser_AST.Un; sigmap = _42_847.sigmap; default_result_effect = _42_847.default_result_effect; iface = _42_847.iface; admitted_iface = _42_847.admitted_iface})))

let push = (fun env -> (let _42_850 = env
in (let _107_604 = (let _107_603 = (let _107_602 = (sigmap env)
in (FStar_Util.smap_copy _107_602))
in (_107_603)::env.sigmap)
in {curmodule = _42_850.curmodule; modules = _42_850.modules; open_namespaces = _42_850.open_namespaces; sigaccum = _42_850.sigaccum; localbindings = _42_850.localbindings; recbindings = _42_850.recbindings; phase = _42_850.phase; sigmap = _107_604; default_result_effect = _42_850.default_result_effect; iface = _42_850.iface; admitted_iface = _42_850.admitted_iface})))

let mark = (fun env -> (push env))

let reset_mark = (fun env -> (let _42_854 = env
in (let _107_609 = (FStar_List.tl env.sigmap)
in {curmodule = _42_854.curmodule; modules = _42_854.modules; open_namespaces = _42_854.open_namespaces; sigaccum = _42_854.sigaccum; localbindings = _42_854.localbindings; recbindings = _42_854.recbindings; phase = _42_854.phase; sigmap = _107_609; default_result_effect = _42_854.default_result_effect; iface = _42_854.iface; admitted_iface = _42_854.admitted_iface})))

let commit_mark = (fun env -> (match (env.sigmap) with
| hd::_42_859::tl -> begin
(let _42_863 = env
in {curmodule = _42_863.curmodule; modules = _42_863.modules; open_namespaces = _42_863.open_namespaces; sigaccum = _42_863.sigaccum; localbindings = _42_863.localbindings; recbindings = _42_863.recbindings; phase = _42_863.phase; sigmap = (hd)::tl; default_result_effect = _42_863.default_result_effect; iface = _42_863.iface; admitted_iface = _42_863.admitted_iface})
end
| _42_866 -> begin
(FStar_All.failwith "Impossible")
end))

let pop = (fun env -> (match (env.sigmap) with
| _42_870::maps -> begin
(let _42_872 = env
in {curmodule = _42_872.curmodule; modules = _42_872.modules; open_namespaces = _42_872.open_namespaces; sigaccum = _42_872.sigaccum; localbindings = _42_872.localbindings; recbindings = _42_872.recbindings; phase = _42_872.phase; sigmap = maps; default_result_effect = _42_872.default_result_effect; iface = _42_872.iface; admitted_iface = _42_872.admitted_iface})
end
| _42_875 -> begin
(FStar_All.failwith "No more modules to pop")
end))

let export_interface = (fun m env -> (let sigelt_in_m = (fun se -> (match ((FStar_Absyn_Util.lids_of_sigelt se)) with
| l::_42_881 -> begin
(l.FStar_Absyn_Syntax.nsstr = m.FStar_Absyn_Syntax.str)
end
| _42_885 -> begin
false
end))
in (let sm = (sigmap env)
in (let env = (pop env)
in (let keys = (FStar_Util.smap_keys sm)
in (let sm' = (sigmap env)
in (let _42_908 = (FStar_All.pipe_right keys (FStar_List.iter (fun k -> (match ((FStar_Util.smap_try_find sm' k)) with
| Some (se, true) when (sigelt_in_m se) -> begin
(let _42_895 = (FStar_Util.smap_remove sm' k)
in (let se = (match (se) with
| FStar_Absyn_Syntax.Sig_val_decl (l, t, q, r) -> begin
FStar_Absyn_Syntax.Sig_val_decl ((l, t, (FStar_Absyn_Syntax.Assumption)::q, r))
end
| _42_904 -> begin
se
end)
in (FStar_Util.smap_add sm' k (se, false))))
end
| _42_907 -> begin
()
end))))
in env)))))))

let finish_module_or_interface = (fun env modul -> (let _42_912 = (match ((not (modul.FStar_Absyn_Syntax.is_interface))) with
| true -> begin
(check_admits modul.FStar_Absyn_Syntax.name env)
end
| false -> begin
()
end)
in (finish env modul)))

let prepare_module_or_interface = (fun intf admitted env mname -> (let prep = (fun env -> (let open_ns = (match ((FStar_Absyn_Syntax.lid_equals mname FStar_Absyn_Const.prims_lid)) with
| true -> begin
[]
end
| false -> begin
(match ((FStar_Absyn_Syntax.lid_equals mname FStar_Absyn_Const.st_lid)) with
| true -> begin
(FStar_Absyn_Const.prims_lid)::[]
end
| false -> begin
(match ((FStar_Absyn_Syntax.lid_equals mname FStar_Absyn_Const.all_lid)) with
| true -> begin
(FStar_Absyn_Const.prims_lid)::(FStar_Absyn_Const.st_lid)::[]
end
| false -> begin
(FStar_Absyn_Const.prims_lid)::(FStar_Absyn_Const.st_lid)::(FStar_Absyn_Const.all_lid)::(FStar_Absyn_Const.fstar_ns_lid)::[]
end)
end)
end)
in (let _42_921 = env
in {curmodule = Some (mname); modules = _42_921.modules; open_namespaces = open_ns; sigaccum = _42_921.sigaccum; localbindings = _42_921.localbindings; recbindings = _42_921.recbindings; phase = _42_921.phase; sigmap = env.sigmap; default_result_effect = _42_921.default_result_effect; iface = intf; admitted_iface = admitted})))
in (match ((FStar_All.pipe_right env.modules (FStar_Util.find_opt (fun _42_926 -> (match (_42_926) with
| (l, _42_925) -> begin
(FStar_Absyn_Syntax.lid_equals l mname)
end))))) with
| None -> begin
((prep env), false)
end
| Some (_42_929, m) -> begin
(let _42_933 = (match (((not (m.FStar_Absyn_Syntax.is_interface)) || intf)) with
| true -> begin
(let _107_639 = (let _107_638 = (let _107_637 = (FStar_Util.format1 "Duplicate module or interface name: %s" mname.FStar_Absyn_Syntax.str)
in (let _107_636 = (FStar_Absyn_Syntax.range_of_lid mname)
in (_107_637, _107_636)))
in FStar_Absyn_Syntax.Error (_107_638))
in (Prims.raise _107_639))
end
| false -> begin
()
end)
in (let _107_641 = (let _107_640 = (push env)
in (prep _107_640))
in (_107_641, true)))
end)))

let enter_monad_scope = (fun env mname -> (let curmod = (current_module env)
in (let mscope = (FStar_Absyn_Syntax.lid_of_ids (FStar_List.append curmod.FStar_Absyn_Syntax.ns ((curmod.FStar_Absyn_Syntax.ident)::(mname)::[])))
in (let _42_939 = env
in {curmodule = Some (mscope); modules = _42_939.modules; open_namespaces = (curmod)::env.open_namespaces; sigaccum = _42_939.sigaccum; localbindings = _42_939.localbindings; recbindings = _42_939.recbindings; phase = _42_939.phase; sigmap = _42_939.sigmap; default_result_effect = _42_939.default_result_effect; iface = _42_939.iface; admitted_iface = _42_939.admitted_iface}))))

let exit_monad_scope = (fun env0 env -> (let _42_943 = env
in {curmodule = env0.curmodule; modules = _42_943.modules; open_namespaces = env0.open_namespaces; sigaccum = _42_943.sigaccum; localbindings = _42_943.localbindings; recbindings = _42_943.recbindings; phase = _42_943.phase; sigmap = _42_943.sigmap; default_result_effect = _42_943.default_result_effect; iface = _42_943.iface; admitted_iface = _42_943.admitted_iface}))

let fail_or = (fun env lookup lid -> (match ((lookup lid)) with
| None -> begin
(let r = (match ((try_lookup_name true false env lid)) with
| None -> begin
None
end
| (Some (Knd_name (o, _))) | (Some (Eff_name (o, _))) | (Some (Typ_name (o, _))) | (Some (Exp_name (o, _))) -> begin
(let _107_656 = (range_of_occurrence o)
in Some (_107_656))
end)
in (let msg = (match (r) with
| None -> begin
""
end
| Some (r) -> begin
(let _107_657 = (FStar_Range.string_of_range r)
in (FStar_Util.format1 "(Possible clash with related name at %s)" _107_657))
end)
in (let _107_662 = (let _107_661 = (let _107_660 = (let _107_658 = (FStar_Absyn_Syntax.text_of_lid lid)
in (FStar_Util.format2 "Identifier not found: [%s] %s" _107_658 msg))
in (let _107_659 = (FStar_Absyn_Syntax.range_of_lid lid)
in (_107_660, _107_659)))
in FStar_Absyn_Syntax.Error (_107_661))
in (Prims.raise _107_662))))
end
| Some (r) -> begin
r
end))

let fail_or2 = (fun lookup id -> (match ((lookup id)) with
| None -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (((Prims.strcat (Prims.strcat "Identifier not found [" id.FStar_Absyn_Syntax.idText) "]"), id.FStar_Absyn_Syntax.idRange))))
end
| Some (r) -> begin
r
end))




