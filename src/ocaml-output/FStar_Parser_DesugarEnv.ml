
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

let is_Mkenv = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv"))))

let open_modules = (fun e -> e.modules)

let current_module = (fun env -> (match (env.curmodule) with
| None -> begin
(FStar_All.failwith "Unset current module")
end
| Some (m) -> begin
m
end))

let qual = (fun lid id -> (let _108_111 = (FStar_Absyn_Syntax.lid_of_ids (FStar_List.append lid.FStar_Absyn_Syntax.ns ((lid.FStar_Absyn_Syntax.ident)::(id)::[])))
in (FStar_Absyn_Util.set_lid_range _108_111 id.FStar_Absyn_Syntax.idRange)))

let qualify = (fun env id -> (let _108_116 = (current_module env)
in (qual _108_116 id)))

let qualify_lid = (fun env lid -> (let cur = (current_module env)
in (let _108_122 = (FStar_Absyn_Syntax.lid_of_ids (FStar_List.append (FStar_List.append (FStar_List.append cur.FStar_Absyn_Syntax.ns ((cur.FStar_Absyn_Syntax.ident)::[])) lid.FStar_Absyn_Syntax.ns) ((lid.FStar_Absyn_Syntax.ident)::[])))
in (let _108_121 = (FStar_Absyn_Syntax.range_of_lid lid)
in (FStar_Absyn_Util.set_lid_range _108_122 _108_121)))))

let new_sigmap = (fun _42_52 -> (match (()) with
| () -> begin
(FStar_Util.smap_create 100)
end))

let empty_env = (fun _42_53 -> (match (()) with
| () -> begin
(let _108_127 = (let _108_126 = (new_sigmap ())
in (_108_126)::[])
in {curmodule = None; modules = []; open_namespaces = []; sigaccum = []; localbindings = []; recbindings = []; phase = FStar_Parser_AST.Un; sigmap = _108_127; default_result_effect = FStar_Absyn_Util.ml_comp; iface = false; admitted_iface = false})
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
(let _108_144 = (let _108_143 = (FStar_Absyn_Util.set_bvd_range bvd id.FStar_Absyn_Syntax.idRange)
in (FStar_Absyn_Util.bvd_to_typ _108_143 FStar_Absyn_Syntax.kun))
in Some (_108_144))
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
in (FStar_Util.find_map namespaces (fun ns -> (let full_name = (let _108_159 = (let _108_158 = (FStar_Absyn_Syntax.ids_of_lid ns)
in (FStar_List.append _108_158 ids))
in (FStar_Absyn_Syntax.lid_of_ids _108_159))
in (finder full_name)))))
end))
in (let _108_161 = (let _108_160 = (current_module env)
in (_108_160)::env.open_namespaces)
in (aux _108_161))))

let unmangleMap = (("op_ColonColon", "Cons"))::(("not", "op_Negation"))::[]

let unmangleOpName = (fun id -> (FStar_Util.find_map unmangleMap (fun _42_108 -> (match (_42_108) with
| (x, y) -> begin
if (id.FStar_Absyn_Syntax.idText = x) then begin
(let _108_165 = (FStar_Absyn_Syntax.lid_of_path (("Prims")::(y)::[]) id.FStar_Absyn_Syntax.idRange)
in Some (_108_165))
end else begin
None
end
end))))

let try_lookup_id' = (fun env id -> (match ((unmangleOpName id)) with
| Some (l) -> begin
(let _108_173 = (let _108_172 = (let _108_171 = (let _108_170 = (FStar_Absyn_Util.fv l)
in (_108_170, None))
in (FStar_Absyn_Syntax.mk_Exp_fvar _108_171 None id.FStar_Absyn_Syntax.idRange))
in (l, _108_172))
in Some (_108_173))
end
| _42_114 -> begin
(let found = (FStar_Util.find_map env.localbindings (fun _42_2 -> (match (_42_2) with
| (FStar_Util.Inl (_42_117), Binding_typ_var (id')) when (id'.FStar_Absyn_Syntax.idText = id.FStar_Absyn_Syntax.idText) -> begin
Some (FStar_Util.Inl (()))
end
| (FStar_Util.Inr (bvd), Binding_var (id')) when (id'.FStar_Absyn_Syntax.idText = id.FStar_Absyn_Syntax.idText) -> begin
(let _108_179 = (let _108_178 = (let _108_177 = (FStar_Absyn_Syntax.lid_of_ids ((id')::[]))
in (let _108_176 = (let _108_175 = (FStar_Absyn_Util.set_bvd_range bvd id.FStar_Absyn_Syntax.idRange)
in (FStar_Absyn_Util.bvd_to_exp _108_175 FStar_Absyn_Syntax.tun))
in (_108_177, _108_176)))
in FStar_Util.Inr (_108_178))
in Some (_108_179))
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

let try_lookup_name = (fun any_val exclude_interf env lid -> (let find_in_sig = (fun lid -> (match ((let _108_297 = (sigmap env)
in (FStar_Util.smap_try_find _108_297 lid.FStar_Absyn_Syntax.str))) with
| Some (_42_214, true) when exclude_interf -> begin
None
end
| None -> begin
None
end
| Some (se, _42_221) -> begin
(match (se) with
| (FStar_Absyn_Syntax.Sig_typ_abbrev (_)) | (FStar_Absyn_Syntax.Sig_tycon (_)) -> begin
(let _108_300 = (let _108_299 = (let _108_298 = (FStar_Absyn_Util.ftv lid FStar_Absyn_Syntax.kun)
in (OSig (se), _108_298))
in Typ_name (_108_299))
in Some (_108_300))
end
| FStar_Absyn_Syntax.Sig_kind_abbrev (_42_231) -> begin
Some (Knd_name ((OSig (se), lid)))
end
| FStar_Absyn_Syntax.Sig_new_effect (ne, _42_235) -> begin
(let _108_304 = (let _108_303 = (let _108_302 = (let _108_301 = (FStar_Absyn_Syntax.range_of_lid lid)
in (FStar_Absyn_Util.set_lid_range ne.FStar_Absyn_Syntax.mname _108_301))
in (OSig (se), _108_302))
in Eff_name (_108_303))
in Some (_108_304))
end
| FStar_Absyn_Syntax.Sig_effect_abbrev (_42_239) -> begin
Some (Eff_name ((OSig (se), lid)))
end
| FStar_Absyn_Syntax.Sig_datacon (_42_242) -> begin
(let _108_309 = (let _108_308 = (let _108_307 = (let _108_306 = (fv_qual_of_se se)
in (let _108_305 = (FStar_Absyn_Syntax.range_of_lid lid)
in (FStar_Absyn_Util.fvar _108_306 lid _108_305)))
in (OSig (se), _108_307))
in Exp_name (_108_308))
in Some (_108_309))
end
| FStar_Absyn_Syntax.Sig_let (_42_245) -> begin
(let _108_313 = (let _108_312 = (let _108_311 = (let _108_310 = (FStar_Absyn_Syntax.range_of_lid lid)
in (FStar_Absyn_Util.fvar None lid _108_310))
in (OSig (se), _108_311))
in Exp_name (_108_312))
in Some (_108_313))
end
| FStar_Absyn_Syntax.Sig_val_decl (_42_248, _42_250, quals, _42_253) -> begin
if (any_val || (FStar_All.pipe_right quals (FStar_Util.for_some (fun _42_6 -> (match (_42_6) with
| FStar_Absyn_Syntax.Assumption -> begin
true
end
| _42_259 -> begin
false
end))))) then begin
(let _108_319 = (let _108_318 = (let _108_317 = (let _108_316 = (fv_qual_of_se se)
in (let _108_315 = (FStar_Absyn_Syntax.range_of_lid lid)
in (FStar_Absyn_Util.fvar _108_316 lid _108_315)))
in (OSig (se), _108_317))
in Exp_name (_108_318))
in Some (_108_319))
end else begin
None
end
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
(let _108_324 = (let _108_323 = (let _108_322 = (let _108_321 = (FStar_Absyn_Syntax.range_of_lid recname)
in (FStar_Absyn_Util.fvar None recname _108_321))
in (ORec (l), _108_322))
in Exp_name (_108_323))
in Some (_108_324))
end
| Binding_tycon (l) when (FStar_Absyn_Syntax.lid_equals l recname) -> begin
(let _108_327 = (let _108_326 = (let _108_325 = (FStar_Absyn_Util.ftv recname FStar_Absyn_Syntax.kun)
in (ORec (l), _108_325))
in Typ_name (_108_326))
in Some (_108_327))
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
(let _108_334 = (FStar_Absyn_Util.ftv l FStar_Absyn_Syntax.mk_Kind_unknown)
in Some (_108_334))
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

let try_resolve_typ_abbrev = (fun env lid -> (let find_in_sig = (fun lid -> (match ((let _108_363 = (sigmap env)
in (FStar_Util.smap_try_find _108_363 lid.FStar_Absyn_Syntax.str))) with
| Some (FStar_Absyn_Syntax.Sig_typ_abbrev (lid, tps, k, def, _42_350, _42_352), _42_356) -> begin
(let t = (let _108_366 = (let _108_365 = (let _108_364 = (FStar_Absyn_Util.close_with_lam tps def)
in (_108_364, lid))
in FStar_Absyn_Syntax.Meta_named (_108_365))
in (FStar_Absyn_Syntax.mk_Typ_meta _108_366))
in Some (t))
end
| _42_361 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))

let lookup_letbinding_quals = (fun env lid -> (let find_in_sig = (fun lid -> (match ((let _108_373 = (sigmap env)
in (FStar_Util.smap_try_find _108_373 lid.FStar_Absyn_Syntax.str))) with
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

let try_lookup_let = (fun env lid -> (let find_in_sig = (fun lid -> (match ((let _108_385 = (sigmap env)
in (FStar_Util.smap_try_find _108_385 lid.FStar_Absyn_Syntax.str))) with
| Some (FStar_Absyn_Syntax.Sig_let (_42_400), _42_403) -> begin
(let _108_387 = (let _108_386 = (FStar_Absyn_Syntax.range_of_lid lid)
in (FStar_Absyn_Util.fvar None lid _108_386))
in Some (_108_387))
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

let try_lookup_datacon = (fun env lid -> (let find_in_sig = (fun lid -> (match ((let _108_406 = (sigmap env)
in (FStar_Util.smap_try_find _108_406 lid.FStar_Absyn_Syntax.str))) with
| Some (FStar_Absyn_Syntax.Sig_val_decl (_42_427, _42_429, quals, _42_432), _42_436) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _42_8 -> (match (_42_8) with
| FStar_Absyn_Syntax.Assumption -> begin
true
end
| _42_442 -> begin
false
end)))) then begin
(let _108_408 = (FStar_Absyn_Util.fv lid)
in Some (_108_408))
end else begin
None
end
end
| Some (FStar_Absyn_Syntax.Sig_datacon (_42_444), _42_447) -> begin
(let _108_409 = (FStar_Absyn_Util.fv lid)
in Some (_108_409))
end
| _42_451 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))

let find_all_datacons = (fun env lid -> (let find_in_sig = (fun lid -> (match ((let _108_416 = (sigmap env)
in (FStar_Util.smap_try_find _108_416 lid.FStar_Absyn_Syntax.str))) with
| Some (FStar_Absyn_Syntax.Sig_tycon (_42_457, _42_459, _42_461, _42_463, datas, _42_466, _42_468), _42_472) -> begin
Some (datas)
end
| _42_476 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))

type record_or_dc =
{typename : FStar_Absyn_Syntax.lident; constrname : FStar_Absyn_Syntax.lident; parms : FStar_Absyn_Syntax.binders; fields : (FStar_Absyn_Syntax.fieldname * FStar_Absyn_Syntax.typ) Prims.list; is_record : Prims.bool}

let is_Mkrecord_or_dc = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkrecord_or_dc"))))

let record_cache_aux = (let record_cache = (FStar_Util.mk_ref (([])::[]))
in (let push = (fun _42_485 -> (match (()) with
| () -> begin
(let _108_446 = (let _108_445 = (let _108_443 = (FStar_ST.read record_cache)
in (FStar_List.hd _108_443))
in (let _108_444 = (FStar_ST.read record_cache)
in (_108_445)::_108_444))
in (FStar_ST.op_Colon_Equals record_cache _108_446))
end))
in (let pop = (fun _42_487 -> (match (()) with
| () -> begin
(let _108_450 = (let _108_449 = (FStar_ST.read record_cache)
in (FStar_List.tl _108_449))
in (FStar_ST.op_Colon_Equals record_cache _108_450))
end))
in (let peek = (fun _42_489 -> (match (()) with
| () -> begin
(let _108_453 = (FStar_ST.read record_cache)
in (FStar_List.hd _108_453))
end))
in (let insert = (fun r -> (let _108_460 = (let _108_459 = (let _108_456 = (peek ())
in (r)::_108_456)
in (let _108_458 = (let _108_457 = (FStar_ST.read record_cache)
in (FStar_List.tl _108_457))
in (_108_459)::_108_458))
in (FStar_ST.op_Colon_Equals record_cache _108_460)))
in (push, pop, peek, insert))))))

let push_record_cache = (let _42_499 = record_cache_aux
in (match (_42_499) with
| (push, _42_494, _42_496, _42_498) -> begin
push
end))

let pop_record_cache = (let _42_507 = record_cache_aux
in (match (_42_507) with
| (_42_501, pop, _42_504, _42_506) -> begin
pop
end))

let peek_record_cache = (let _42_515 = record_cache_aux
in (match (_42_515) with
| (_42_509, _42_511, peek, _42_514) -> begin
peek
end))

let insert_record_cache = (let _42_523 = record_cache_aux
in (match (_42_523) with
| (_42_517, _42_519, _42_521, insert) -> begin
insert
end))

let extract_record = (fun e _42_12 -> (match (_42_12) with
| FStar_Absyn_Syntax.Sig_bundle (sigs, _42_528, _42_530, _42_532) -> begin
(let is_rec = (FStar_Util.for_some (fun _42_9 -> (match (_42_9) with
| (FStar_Absyn_Syntax.RecordType (_)) | (FStar_Absyn_Syntax.RecordConstructor (_)) -> begin
true
end
| _42_543 -> begin
false
end)))
in (let find_dc = (fun dc -> (FStar_All.pipe_right sigs (FStar_Util.find_opt (fun _42_10 -> (match (_42_10) with
| FStar_Absyn_Syntax.Sig_datacon (lid, _42_550, _42_552, _42_554, _42_556, _42_558) -> begin
(FStar_Absyn_Syntax.lid_equals dc lid)
end
| _42_562 -> begin
false
end)))))
in (FStar_All.pipe_right sigs (FStar_List.iter (fun _42_11 -> (match (_42_11) with
| FStar_Absyn_Syntax.Sig_tycon (typename, parms, _42_567, _42_569, dc::[], tags, _42_574) -> begin
(match ((let _108_531 = (find_dc dc)
in (FStar_All.pipe_left FStar_Util.must _108_531))) with
| FStar_Absyn_Syntax.Sig_datacon (constrname, t, _42_580, _42_582, _42_584, _42_586) -> begin
(let formals = (match ((FStar_Absyn_Util.function_formals t)) with
| Some (x, _42_591) -> begin
x
end
| _42_595 -> begin
[]
end)
in (let is_rec = (is_rec tags)
in (let fields = (FStar_All.pipe_right formals (FStar_List.collect (fun b -> (match (b) with
| (FStar_Util.Inr (x), q) -> begin
if ((FStar_Absyn_Syntax.is_null_binder b) || (is_rec && (q = Some (FStar_Absyn_Syntax.Implicit)))) then begin
[]
end else begin
(let _108_535 = (let _108_534 = (let _108_533 = if is_rec then begin
(FStar_Absyn_Util.unmangle_field_name x.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ppname)
end else begin
x.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ppname
end
in (qual constrname _108_533))
in (_108_534, x.FStar_Absyn_Syntax.sort))
in (_108_535)::[])
end
end
| _42_604 -> begin
[]
end))))
in (let record = {typename = typename; constrname = constrname; parms = parms; fields = fields; is_record = is_rec}
in (insert_record_cache record)))))
end
| _42_608 -> begin
()
end)
end
| _42_610 -> begin
()
end))))))
end
| _42_612 -> begin
()
end))

let try_lookup_record_or_dc_by_field_name = (fun env fieldname -> (let maybe_add_constrname = (fun ns c -> (let rec aux = (fun ns -> (match (ns) with
| [] -> begin
(c)::[]
end
| c'::[] -> begin
if (c'.FStar_Absyn_Syntax.idText = c.FStar_Absyn_Syntax.idText) then begin
(c)::[]
end else begin
(c')::(c)::[]
end
end
| hd::tl -> begin
(let _108_546 = (aux tl)
in (hd)::_108_546)
end))
in (aux ns)))
in (let find_in_cache = (fun fieldname -> (let _42_630 = (fieldname.FStar_Absyn_Syntax.ns, fieldname.FStar_Absyn_Syntax.ident)
in (match (_42_630) with
| (ns, fieldname) -> begin
(let _108_551 = (peek_record_cache ())
in (FStar_Util.find_map _108_551 (fun record -> (let constrname = record.constrname.FStar_Absyn_Syntax.ident
in (let ns = (maybe_add_constrname ns constrname)
in (let fname = (FStar_Absyn_Syntax.lid_of_ids (FStar_List.append ns ((fieldname)::[])))
in (FStar_Util.find_map record.fields (fun _42_638 -> (match (_42_638) with
| (f, _42_637) -> begin
if (FStar_Absyn_Syntax.lid_equals fname f) then begin
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
| _42_646 -> begin
None
end))

let try_lookup_projector_by_field_name = (fun env fieldname -> (match ((try_lookup_record_or_dc_by_field_name env fieldname)) with
| Some (r, f) -> begin
Some ((f, r.is_record))
end
| _42_654 -> begin
None
end))

let qualify_field_to_record = (fun env recd f -> (let qualify = (fun fieldname -> (let _42_662 = (fieldname.FStar_Absyn_Syntax.ns, fieldname.FStar_Absyn_Syntax.ident)
in (match (_42_662) with
| (ns, fieldname) -> begin
(let constrname = recd.constrname.FStar_Absyn_Syntax.ident
in (let fname = (FStar_Absyn_Syntax.lid_of_ids (FStar_List.append (FStar_List.append ns ((constrname)::[])) ((fieldname)::[])))
in (FStar_Util.find_map recd.fields (fun _42_668 -> (match (_42_668) with
| (f, _42_667) -> begin
if (FStar_Absyn_Syntax.lid_equals fname f) then begin
Some (fname)
end else begin
None
end
end)))))
end)))
in (resolve_in_open_namespaces env f qualify)))

let find_kind_abbrev = (fun env l -> (match ((try_lookup_name true (not (env.iface)) env l)) with
| Some (Knd_name (_42_672, l)) -> begin
Some (l)
end
| _42_678 -> begin
None
end))

let is_kind_abbrev = (fun env l -> (match ((find_kind_abbrev env l)) with
| None -> begin
false
end
| Some (_42_683) -> begin
true
end))

let unique_name = (fun any_val exclude_if env lid -> (match ((try_lookup_lid' any_val exclude_if env lid)) with
| None -> begin
(match ((find_kind_abbrev env lid)) with
| None -> begin
true
end
| Some (_42_692) -> begin
false
end)
end
| Some (_42_695) -> begin
false
end))

let unique_typ_name = (fun env lid -> (match ((try_lookup_typ_name' true env lid)) with
| None -> begin
true
end
| Some (a) -> begin
false
end))

let unique = (fun any_val exclude_if env lid -> (let this_env = (let _42_706 = env
in {curmodule = _42_706.curmodule; modules = _42_706.modules; open_namespaces = []; sigaccum = _42_706.sigaccum; localbindings = _42_706.localbindings; recbindings = _42_706.recbindings; phase = _42_706.phase; sigmap = _42_706.sigmap; default_result_effect = _42_706.default_result_effect; iface = _42_706.iface; admitted_iface = _42_706.admitted_iface})
in ((unique_name any_val exclude_if this_env lid) && (unique_typ_name this_env lid))))

let gen_bvd = (fun _42_13 -> (match (_42_13) with
| Binding_typ_var (id) -> begin
(let _108_600 = (let _108_599 = (let _108_598 = (FStar_Absyn_Util.genident (Some (id.FStar_Absyn_Syntax.idRange)))
in (id, _108_598))
in (FStar_Absyn_Util.mkbvd _108_599))
in FStar_Util.Inl (_108_600))
end
| Binding_var (id) -> begin
(let _108_603 = (let _108_602 = (let _108_601 = (FStar_Absyn_Util.genident (Some (id.FStar_Absyn_Syntax.idRange)))
in (id, _108_601))
in (FStar_Absyn_Util.mkbvd _108_602))
in FStar_Util.Inr (_108_603))
end
| _42_715 -> begin
(FStar_All.failwith "Tried to generate a bound variable for a type constructor")
end))

let push_bvvdef = (fun env x -> (let b = Binding_var (x.FStar_Absyn_Syntax.ppname)
in (let _42_719 = env
in {curmodule = _42_719.curmodule; modules = _42_719.modules; open_namespaces = _42_719.open_namespaces; sigaccum = _42_719.sigaccum; localbindings = ((FStar_Util.Inr (x), b))::env.localbindings; recbindings = _42_719.recbindings; phase = _42_719.phase; sigmap = _42_719.sigmap; default_result_effect = _42_719.default_result_effect; iface = _42_719.iface; admitted_iface = _42_719.admitted_iface})))

let push_btvdef = (fun env x -> (let b = Binding_typ_var (x.FStar_Absyn_Syntax.ppname)
in (let _42_724 = env
in {curmodule = _42_724.curmodule; modules = _42_724.modules; open_namespaces = _42_724.open_namespaces; sigaccum = _42_724.sigaccum; localbindings = ((FStar_Util.Inl (x), b))::env.localbindings; recbindings = _42_724.recbindings; phase = _42_724.phase; sigmap = _42_724.sigmap; default_result_effect = _42_724.default_result_effect; iface = _42_724.iface; admitted_iface = _42_724.admitted_iface})))

let push_local_binding = (fun env b -> (let bvd = (gen_bvd b)
in ((let _42_729 = env
in {curmodule = _42_729.curmodule; modules = _42_729.modules; open_namespaces = _42_729.open_namespaces; sigaccum = _42_729.sigaccum; localbindings = ((bvd, b))::env.localbindings; recbindings = _42_729.recbindings; phase = _42_729.phase; sigmap = _42_729.sigmap; default_result_effect = _42_729.default_result_effect; iface = _42_729.iface; admitted_iface = _42_729.admitted_iface}), bvd)))

let push_local_tbinding = (fun env a -> (match ((push_local_binding env (Binding_typ_var (a)))) with
| (env, FStar_Util.Inl (x)) -> begin
(env, x)
end
| _42_738 -> begin
(FStar_All.failwith "impossible")
end))

let push_local_vbinding = (fun env b -> (match ((push_local_binding env (Binding_var (b)))) with
| (env, FStar_Util.Inr (x)) -> begin
(env, x)
end
| _42_746 -> begin
(FStar_All.failwith "impossible")
end))

let push_rec_binding = (fun env b -> (match (b) with
| (Binding_let (lid)) | (Binding_tycon (lid)) -> begin
if (unique false true env lid) then begin
(let _42_752 = env
in {curmodule = _42_752.curmodule; modules = _42_752.modules; open_namespaces = _42_752.open_namespaces; sigaccum = _42_752.sigaccum; localbindings = _42_752.localbindings; recbindings = (b)::env.recbindings; phase = _42_752.phase; sigmap = _42_752.sigmap; default_result_effect = _42_752.default_result_effect; iface = _42_752.iface; admitted_iface = _42_752.admitted_iface})
end else begin
(let _108_630 = (let _108_629 = (let _108_628 = (FStar_Absyn_Syntax.range_of_lid lid)
in ((Prims.strcat "Duplicate top-level names " lid.FStar_Absyn_Syntax.str), _108_628))
in FStar_Absyn_Syntax.Error (_108_629))
in (Prims.raise _108_630))
end
end
| _42_755 -> begin
(FStar_All.failwith "Unexpected rec_binding")
end))

let push_sigelt = (fun env s -> (let err = (fun l -> (let sopt = (let _108_637 = (sigmap env)
in (FStar_Util.smap_try_find _108_637 l.FStar_Absyn_Syntax.str))
in (let r = (match (sopt) with
| Some (se, _42_763) -> begin
(match ((let _108_638 = (FStar_Absyn_Util.lids_of_sigelt se)
in (FStar_Util.find_opt (FStar_Absyn_Syntax.lid_equals l) _108_638))) with
| Some (l) -> begin
(let _108_639 = (FStar_Absyn_Syntax.range_of_lid l)
in (FStar_All.pipe_left FStar_Range.string_of_range _108_639))
end
| None -> begin
"<unknown>"
end)
end
| None -> begin
"<unknown>"
end)
in (let _108_644 = (let _108_643 = (let _108_642 = (let _108_640 = (FStar_Absyn_Syntax.text_of_lid l)
in (FStar_Util.format2 "Duplicate top-level names [%s]; previously declared at %s" _108_640 r))
in (let _108_641 = (FStar_Absyn_Syntax.range_of_lid l)
in (_108_642, _108_641)))
in FStar_Absyn_Syntax.Error (_108_643))
in (Prims.raise _108_644)))))
in (let env = (let _42_781 = (match (s) with
| FStar_Absyn_Syntax.Sig_let (_42_772) -> begin
(false, true)
end
| FStar_Absyn_Syntax.Sig_bundle (_42_775) -> begin
(true, true)
end
| _42_778 -> begin
(false, false)
end)
in (match (_42_781) with
| (any_val, exclude_if) -> begin
(let lids = (FStar_Absyn_Util.lids_of_sigelt s)
in (match ((FStar_Util.find_map lids (fun l -> if (not ((unique any_val exclude_if env l))) then begin
Some (l)
end else begin
None
end))) with
| None -> begin
(let _42_785 = (extract_record env s)
in (let _42_787 = env
in {curmodule = _42_787.curmodule; modules = _42_787.modules; open_namespaces = _42_787.open_namespaces; sigaccum = (s)::env.sigaccum; localbindings = _42_787.localbindings; recbindings = _42_787.recbindings; phase = _42_787.phase; sigmap = _42_787.sigmap; default_result_effect = _42_787.default_result_effect; iface = _42_787.iface; admitted_iface = _42_787.admitted_iface}))
end
| Some (l) -> begin
(err l)
end))
end))
in (let _42_806 = (match (s) with
| FStar_Absyn_Syntax.Sig_bundle (ses, _42_794, _42_796, _42_798) -> begin
(let _108_648 = (FStar_List.map (fun se -> (let _108_647 = (FStar_Absyn_Util.lids_of_sigelt se)
in (_108_647, se))) ses)
in (env, _108_648))
end
| _42_803 -> begin
(let _108_651 = (let _108_650 = (let _108_649 = (FStar_Absyn_Util.lids_of_sigelt s)
in (_108_649, s))
in (_108_650)::[])
in (env, _108_651))
end)
in (match (_42_806) with
| (env, lss) -> begin
(let _42_811 = (FStar_All.pipe_right lss (FStar_List.iter (fun _42_809 -> (match (_42_809) with
| (lids, se) -> begin
(FStar_All.pipe_right lids (FStar_List.iter (fun lid -> (let _108_654 = (sigmap env)
in (FStar_Util.smap_add _108_654 lid.FStar_Absyn_Syntax.str (se, (env.iface && (not (env.admitted_iface)))))))))
end))))
in env)
end)))))

let push_namespace = (fun env lid -> (let _42_815 = env
in {curmodule = _42_815.curmodule; modules = _42_815.modules; open_namespaces = (lid)::env.open_namespaces; sigaccum = _42_815.sigaccum; localbindings = _42_815.localbindings; recbindings = _42_815.recbindings; phase = _42_815.phase; sigmap = _42_815.sigmap; default_result_effect = _42_815.default_result_effect; iface = _42_815.iface; admitted_iface = _42_815.admitted_iface}))

let is_type_lid = (fun env lid -> (let aux = (fun _42_820 -> (match (()) with
| () -> begin
(match ((try_lookup_typ_name' false env lid)) with
| Some (_42_822) -> begin
true
end
| _42_825 -> begin
false
end)
end))
in if (lid.FStar_Absyn_Syntax.ns = []) then begin
(match ((try_lookup_id env lid.FStar_Absyn_Syntax.ident)) with
| Some (_42_827) -> begin
false
end
| _42_830 -> begin
(aux ())
end)
end else begin
(aux ())
end))

let check_admits = (fun nm env -> (let warn = (not ((let _108_670 = (FStar_ST.read FStar_Options.admit_fsi)
in (FStar_All.pipe_right _108_670 (FStar_Util.for_some (fun l -> (nm.FStar_Absyn_Syntax.str = l)))))))
in (FStar_All.pipe_right env.sigaccum (FStar_List.iter (fun se -> (match (se) with
| FStar_Absyn_Syntax.Sig_val_decl (l, t, quals, r) -> begin
(match ((try_lookup_lid env l)) with
| None -> begin
(let _42_843 = if warn then begin
(let _108_675 = (let _108_674 = (let _108_672 = (FStar_Absyn_Syntax.range_of_lid l)
in (FStar_Range.string_of_range _108_672))
in (let _108_673 = (FStar_Absyn_Print.sli l)
in (FStar_Util.format2 "%s: Warning: Admitting %s without a definition\n" _108_674 _108_673)))
in (FStar_Util.print_string _108_675))
end else begin
()
end
in (let _108_676 = (sigmap env)
in (FStar_Util.smap_add _108_676 l.FStar_Absyn_Syntax.str (FStar_Absyn_Syntax.Sig_val_decl ((l, t, (FStar_Absyn_Syntax.Assumption)::quals, r)), false))))
end
| Some (_42_846) -> begin
()
end)
end
| _42_849 -> begin
()
end))))))

let finish = (fun env modul -> (let _42_887 = (FStar_All.pipe_right modul.FStar_Absyn_Syntax.declarations (FStar_List.iter (fun _42_15 -> (match (_42_15) with
| FStar_Absyn_Syntax.Sig_bundle (ses, quals, _42_856, _42_858) -> begin
if (FStar_List.contains FStar_Absyn_Syntax.Private quals) then begin
(FStar_All.pipe_right ses (FStar_List.iter (fun _42_14 -> (match (_42_14) with
| FStar_Absyn_Syntax.Sig_datacon (lid, _42_864, _42_866, _42_868, _42_870, _42_872) -> begin
(let _108_683 = (sigmap env)
in (FStar_Util.smap_remove _108_683 lid.FStar_Absyn_Syntax.str))
end
| _42_876 -> begin
()
end))))
end else begin
()
end
end
| FStar_Absyn_Syntax.Sig_val_decl (lid, _42_879, quals, _42_882) -> begin
if (FStar_List.contains FStar_Absyn_Syntax.Private quals) then begin
(let _108_684 = (sigmap env)
in (FStar_Util.smap_remove _108_684 lid.FStar_Absyn_Syntax.str))
end else begin
()
end
end
| _42_886 -> begin
()
end))))
in (let _42_889 = env
in {curmodule = None; modules = ((modul.FStar_Absyn_Syntax.name, modul))::env.modules; open_namespaces = []; sigaccum = []; localbindings = []; recbindings = []; phase = FStar_Parser_AST.Un; sigmap = _42_889.sigmap; default_result_effect = _42_889.default_result_effect; iface = _42_889.iface; admitted_iface = _42_889.admitted_iface})))

let push = (fun env -> (let _42_892 = (push_record_cache ())
in (let _42_894 = env
in (let _108_689 = (let _108_688 = (let _108_687 = (sigmap env)
in (FStar_Util.smap_copy _108_687))
in (_108_688)::env.sigmap)
in {curmodule = _42_894.curmodule; modules = _42_894.modules; open_namespaces = _42_894.open_namespaces; sigaccum = _42_894.sigaccum; localbindings = _42_894.localbindings; recbindings = _42_894.recbindings; phase = _42_894.phase; sigmap = _108_689; default_result_effect = _42_894.default_result_effect; iface = _42_894.iface; admitted_iface = _42_894.admitted_iface}))))

let mark = (fun env -> (push env))

let reset_mark = (fun env -> (let _42_898 = env
in (let _108_694 = (FStar_List.tl env.sigmap)
in {curmodule = _42_898.curmodule; modules = _42_898.modules; open_namespaces = _42_898.open_namespaces; sigaccum = _42_898.sigaccum; localbindings = _42_898.localbindings; recbindings = _42_898.recbindings; phase = _42_898.phase; sigmap = _108_694; default_result_effect = _42_898.default_result_effect; iface = _42_898.iface; admitted_iface = _42_898.admitted_iface})))

let commit_mark = (fun env -> (match (env.sigmap) with
| hd::_42_903::tl -> begin
(let _42_907 = env
in {curmodule = _42_907.curmodule; modules = _42_907.modules; open_namespaces = _42_907.open_namespaces; sigaccum = _42_907.sigaccum; localbindings = _42_907.localbindings; recbindings = _42_907.recbindings; phase = _42_907.phase; sigmap = (hd)::tl; default_result_effect = _42_907.default_result_effect; iface = _42_907.iface; admitted_iface = _42_907.admitted_iface})
end
| _42_910 -> begin
(FStar_All.failwith "Impossible")
end))

let pop = (fun env -> (match (env.sigmap) with
| _42_914::maps -> begin
(let _42_916 = (pop_record_cache ())
in (let _42_918 = env
in {curmodule = _42_918.curmodule; modules = _42_918.modules; open_namespaces = _42_918.open_namespaces; sigaccum = _42_918.sigaccum; localbindings = _42_918.localbindings; recbindings = _42_918.recbindings; phase = _42_918.phase; sigmap = maps; default_result_effect = _42_918.default_result_effect; iface = _42_918.iface; admitted_iface = _42_918.admitted_iface}))
end
| _42_921 -> begin
(FStar_All.failwith "No more modules to pop")
end))

let export_interface = (fun m env -> (let sigelt_in_m = (fun se -> (match ((FStar_Absyn_Util.lids_of_sigelt se)) with
| l::_42_927 -> begin
(l.FStar_Absyn_Syntax.nsstr = m.FStar_Absyn_Syntax.str)
end
| _42_931 -> begin
false
end))
in (let sm = (sigmap env)
in (let env = (pop env)
in (let keys = (FStar_Util.smap_keys sm)
in (let sm' = (sigmap env)
in (let _42_954 = (FStar_All.pipe_right keys (FStar_List.iter (fun k -> (match ((FStar_Util.smap_try_find sm' k)) with
| Some (se, true) when (sigelt_in_m se) -> begin
(let _42_941 = (FStar_Util.smap_remove sm' k)
in (let se = (match (se) with
| FStar_Absyn_Syntax.Sig_val_decl (l, t, q, r) -> begin
FStar_Absyn_Syntax.Sig_val_decl ((l, t, (FStar_Absyn_Syntax.Assumption)::q, r))
end
| _42_950 -> begin
se
end)
in (FStar_Util.smap_add sm' k (se, false))))
end
| _42_953 -> begin
()
end))))
in env)))))))

let finish_module_or_interface = (fun env modul -> (let _42_958 = if (not (modul.FStar_Absyn_Syntax.is_interface)) then begin
(check_admits modul.FStar_Absyn_Syntax.name env)
end else begin
()
end
in (finish env modul)))

let prepare_module_or_interface = (fun intf admitted env mname -> (let prep = (fun env -> (let open_ns = if (FStar_Absyn_Syntax.lid_equals mname FStar_Absyn_Const.prims_lid) then begin
[]
end else begin
if (FStar_Absyn_Syntax.lid_equals mname FStar_Absyn_Const.st_lid) then begin
(FStar_Absyn_Const.prims_lid)::[]
end else begin
if (FStar_Absyn_Syntax.lid_equals mname FStar_Absyn_Const.all_lid) then begin
(FStar_Absyn_Const.prims_lid)::(FStar_Absyn_Const.st_lid)::[]
end else begin
(FStar_Absyn_Const.prims_lid)::(FStar_Absyn_Const.st_lid)::(FStar_Absyn_Const.all_lid)::(FStar_Absyn_Const.fstar_ns_lid)::[]
end
end
end
in (let _42_967 = env
in {curmodule = Some (mname); modules = _42_967.modules; open_namespaces = open_ns; sigaccum = _42_967.sigaccum; localbindings = _42_967.localbindings; recbindings = _42_967.recbindings; phase = _42_967.phase; sigmap = env.sigmap; default_result_effect = _42_967.default_result_effect; iface = intf; admitted_iface = admitted})))
in (match ((FStar_All.pipe_right env.modules (FStar_Util.find_opt (fun _42_972 -> (match (_42_972) with
| (l, _42_971) -> begin
(FStar_Absyn_Syntax.lid_equals l mname)
end))))) with
| None -> begin
((prep env), false)
end
| Some (_42_975, m) -> begin
(let _42_979 = if ((not (m.FStar_Absyn_Syntax.is_interface)) || intf) then begin
(let _108_724 = (let _108_723 = (let _108_722 = (FStar_Util.format1 "Duplicate module or interface name: %s" mname.FStar_Absyn_Syntax.str)
in (let _108_721 = (FStar_Absyn_Syntax.range_of_lid mname)
in (_108_722, _108_721)))
in FStar_Absyn_Syntax.Error (_108_723))
in (Prims.raise _108_724))
end else begin
()
end
in (let _108_726 = (let _108_725 = (push env)
in (prep _108_725))
in (_108_726, true)))
end)))

let enter_monad_scope = (fun env mname -> (let curmod = (current_module env)
in (let mscope = (FStar_Absyn_Syntax.lid_of_ids (FStar_List.append curmod.FStar_Absyn_Syntax.ns ((curmod.FStar_Absyn_Syntax.ident)::(mname)::[])))
in (let _42_985 = env
in {curmodule = Some (mscope); modules = _42_985.modules; open_namespaces = (curmod)::env.open_namespaces; sigaccum = _42_985.sigaccum; localbindings = _42_985.localbindings; recbindings = _42_985.recbindings; phase = _42_985.phase; sigmap = _42_985.sigmap; default_result_effect = _42_985.default_result_effect; iface = _42_985.iface; admitted_iface = _42_985.admitted_iface}))))

let exit_monad_scope = (fun env0 env -> (let _42_989 = env
in {curmodule = env0.curmodule; modules = _42_989.modules; open_namespaces = env0.open_namespaces; sigaccum = _42_989.sigaccum; localbindings = _42_989.localbindings; recbindings = _42_989.recbindings; phase = _42_989.phase; sigmap = _42_989.sigmap; default_result_effect = _42_989.default_result_effect; iface = _42_989.iface; admitted_iface = _42_989.admitted_iface}))

let fail_or = (fun env lookup lid -> (match ((lookup lid)) with
| None -> begin
(let r = (match ((try_lookup_name true false env lid)) with
| None -> begin
None
end
| (Some (Knd_name (o, _))) | (Some (Eff_name (o, _))) | (Some (Typ_name (o, _))) | (Some (Exp_name (o, _))) -> begin
(let _108_741 = (range_of_occurrence o)
in Some (_108_741))
end)
in (let msg = (match (r) with
| None -> begin
""
end
| Some (r) -> begin
(let _108_742 = (FStar_Range.string_of_range r)
in (FStar_Util.format1 "(Possible clash with related name at %s)" _108_742))
end)
in (let _108_747 = (let _108_746 = (let _108_745 = (let _108_743 = (FStar_Absyn_Syntax.text_of_lid lid)
in (FStar_Util.format2 "Identifier not found: [%s] %s" _108_743 msg))
in (let _108_744 = (FStar_Absyn_Syntax.range_of_lid lid)
in (_108_745, _108_744)))
in FStar_Absyn_Syntax.Error (_108_746))
in (Prims.raise _108_747))))
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




