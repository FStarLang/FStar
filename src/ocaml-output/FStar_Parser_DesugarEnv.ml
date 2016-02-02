
open Prims
type binding =
| Binding_typ_var of FStar_Ident.ident
| Binding_var of FStar_Ident.ident
| Binding_let of FStar_Ident.lident
| Binding_tycon of FStar_Ident.lident

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
| Binding_typ_var (_57_18) -> begin
_57_18
end))

let ___Binding_var____0 = (fun projectee -> (match (projectee) with
| Binding_var (_57_21) -> begin
_57_21
end))

let ___Binding_let____0 = (fun projectee -> (match (projectee) with
| Binding_let (_57_24) -> begin
_57_24
end))

let ___Binding_tycon____0 = (fun projectee -> (match (projectee) with
| Binding_tycon (_57_27) -> begin
_57_27
end))

type kind_abbrev =
(FStar_Ident.lident * (FStar_Absyn_Syntax.btvdef, FStar_Absyn_Syntax.bvvdef) FStar_Util.either Prims.list * FStar_Absyn_Syntax.knd)

type env =
{curmodule : FStar_Ident.lident Prims.option; modules : (FStar_Ident.lident * FStar_Absyn_Syntax.modul) Prims.list; open_namespaces : FStar_Ident.lident Prims.list; modul_abbrevs : (FStar_Ident.ident * FStar_Ident.lident) Prims.list; sigaccum : FStar_Absyn_Syntax.sigelts; localbindings : ((FStar_Absyn_Syntax.btvdef, FStar_Absyn_Syntax.bvvdef) FStar_Util.either * binding) Prims.list; recbindings : binding Prims.list; phase : FStar_Parser_AST.level; sigmap : (FStar_Absyn_Syntax.sigelt * Prims.bool) FStar_Util.smap Prims.list; default_result_effect : FStar_Absyn_Syntax.typ  ->  FStar_Range.range  ->  FStar_Absyn_Syntax.comp; iface : Prims.bool; admitted_iface : Prims.bool}

let is_Mkenv = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv"))))

let open_modules = (fun e -> e.modules)

let current_module = (fun env -> (match (env.curmodule) with
| None -> begin
(FStar_All.failwith "Unset current module")
end
| Some (m) -> begin
m
end))

let qual = (fun lid id -> (let _134_114 = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns ((lid.FStar_Ident.ident)::(id)::[])))
in (FStar_Ident.set_lid_range _134_114 id.FStar_Ident.idRange)))

let qualify = (fun env id -> (let _134_119 = (current_module env)
in (qual _134_119 id)))

let qualify_lid = (fun env lid -> (let cur = (current_module env)
in (let _134_124 = (FStar_Ident.lid_of_ids (FStar_List.append (FStar_List.append (FStar_List.append cur.FStar_Ident.ns ((cur.FStar_Ident.ident)::[])) lid.FStar_Ident.ns) ((lid.FStar_Ident.ident)::[])))
in (FStar_Ident.set_lid_range _134_124 (FStar_Ident.range_of_lid lid)))))

let new_sigmap = (fun _57_53 -> (match (()) with
| () -> begin
(FStar_Util.smap_create 100)
end))

let empty_env = (fun _57_54 -> (match (()) with
| () -> begin
(let _134_129 = (let _134_128 = (new_sigmap ())
in (_134_128)::[])
in {curmodule = None; modules = []; open_namespaces = []; modul_abbrevs = []; sigaccum = []; localbindings = []; recbindings = []; phase = FStar_Parser_AST.Un; sigmap = _134_129; default_result_effect = FStar_Absyn_Util.ml_comp; iface = false; admitted_iface = false})
end))

let sigmap = (fun env -> (FStar_List.hd env.sigmap))

let default_total = (fun env -> (let _57_57 = env
in {curmodule = _57_57.curmodule; modules = _57_57.modules; open_namespaces = _57_57.open_namespaces; modul_abbrevs = _57_57.modul_abbrevs; sigaccum = _57_57.sigaccum; localbindings = _57_57.localbindings; recbindings = _57_57.recbindings; phase = _57_57.phase; sigmap = _57_57.sigmap; default_result_effect = (fun t _57_60 -> (FStar_Absyn_Syntax.mk_Total t)); iface = _57_57.iface; admitted_iface = _57_57.admitted_iface}))

let default_ml = (fun env -> (let _57_63 = env
in {curmodule = _57_63.curmodule; modules = _57_63.modules; open_namespaces = _57_63.open_namespaces; modul_abbrevs = _57_63.modul_abbrevs; sigaccum = _57_63.sigaccum; localbindings = _57_63.localbindings; recbindings = _57_63.recbindings; phase = _57_63.phase; sigmap = _57_63.sigmap; default_result_effect = FStar_Absyn_Util.ml_comp; iface = _57_63.iface; admitted_iface = _57_63.admitted_iface}))

let range_of_binding = (fun _57_1 -> (match (_57_1) with
| (Binding_typ_var (id)) | (Binding_var (id)) -> begin
id.FStar_Ident.idRange
end
| (Binding_let (lid)) | (Binding_tycon (lid)) -> begin
(FStar_Ident.range_of_lid lid)
end))

let try_lookup_typ_var = (fun env id -> (let fopt = (FStar_List.tryFind (fun _57_77 -> (match (_57_77) with
| (_57_75, b) -> begin
(match (b) with
| (Binding_typ_var (id')) | (Binding_var (id')) -> begin
(id.FStar_Ident.idText = id'.FStar_Ident.idText)
end
| _57_82 -> begin
false
end)
end)) env.localbindings)
in (match (fopt) with
| Some (FStar_Util.Inl (bvd), Binding_typ_var (_57_87)) -> begin
(let _134_145 = (FStar_Absyn_Util.bvd_to_typ (FStar_Absyn_Util.set_bvd_range bvd id.FStar_Ident.idRange) FStar_Absyn_Syntax.kun)
in Some (_134_145))
end
| _57_92 -> begin
None
end)))

let resolve_in_open_namespaces' = (fun env lid finder -> (let aux = (fun namespaces -> (match ((finder lid)) with
| Some (r) -> begin
Some (r)
end
| _57_102 -> begin
(let ids = (FStar_Ident.ids_of_lid lid)
in (FStar_Util.find_map namespaces (fun ns -> (let full_name = (FStar_Ident.lid_of_ids (FStar_List.append (FStar_Ident.ids_of_lid ns) ids))
in (finder full_name)))))
end))
in (let _134_156 = (let _134_155 = (current_module env)
in (_134_155)::env.open_namespaces)
in (aux _134_156))))

let expand_module_abbrevs = (fun env lid -> (match (lid.FStar_Ident.ns) with
| id::[] -> begin
(match ((FStar_All.pipe_right env.modul_abbrevs (FStar_List.tryFind (fun _57_113 -> (match (_57_113) with
| (id', _57_112) -> begin
(id.FStar_Ident.idText = id'.FStar_Ident.idText)
end))))) with
| None -> begin
lid
end
| Some (_57_116, lid') -> begin
(FStar_Ident.lid_of_ids (FStar_List.append (FStar_Ident.ids_of_lid lid') ((lid.FStar_Ident.ident)::[])))
end)
end
| _57_121 -> begin
lid
end))

let resolve_in_open_namespaces = (fun env lid finder -> (let _134_172 = (expand_module_abbrevs env lid)
in (resolve_in_open_namespaces' env _134_172 finder)))

let unmangleMap = (("op_ColonColon", "Cons"))::(("not", "op_Negation"))::[]

let unmangleOpName = (fun id -> (FStar_Util.find_map unmangleMap (fun _57_129 -> (match (_57_129) with
| (x, y) -> begin
if (id.FStar_Ident.idText = x) then begin
(let _134_176 = (FStar_Ident.lid_of_path (("Prims")::(y)::[]) id.FStar_Ident.idRange)
in Some (_134_176))
end else begin
None
end
end))))

let try_lookup_id' = (fun env id -> (match ((unmangleOpName id)) with
| Some (l) -> begin
(let _134_182 = (let _134_181 = (FStar_Absyn_Syntax.mk_Exp_fvar ((FStar_Absyn_Util.fv l), None) None id.FStar_Ident.idRange)
in (l, _134_181))
in Some (_134_182))
end
| _57_135 -> begin
(let found = (FStar_Util.find_map env.localbindings (fun _57_2 -> (match (_57_2) with
| (FStar_Util.Inl (_57_138), Binding_typ_var (id')) when (id'.FStar_Ident.idText = id.FStar_Ident.idText) -> begin
Some (FStar_Util.Inl (()))
end
| (FStar_Util.Inr (bvd), Binding_var (id')) when (id'.FStar_Ident.idText = id.FStar_Ident.idText) -> begin
(let _134_187 = (let _134_186 = (let _134_185 = (FStar_Ident.lid_of_ids ((id')::[]))
in (let _134_184 = (FStar_Absyn_Util.bvd_to_exp (FStar_Absyn_Util.set_bvd_range bvd id.FStar_Ident.idRange) FStar_Absyn_Syntax.tun)
in (_134_185, _134_184)))
in FStar_Util.Inr (_134_186))
in Some (_134_187))
end
| _57_149 -> begin
None
end)))
in (match (found) with
| Some (FStar_Util.Inr (x)) -> begin
Some (x)
end
| _57_155 -> begin
None
end))
end))

let try_lookup_id = (fun env id -> (match ((try_lookup_id' env id)) with
| Some (_57_159, e) -> begin
Some (e)
end
| None -> begin
None
end))

type occurrence =
| OSig of FStar_Absyn_Syntax.sigelt
| OLet of FStar_Ident.lident
| ORec of FStar_Ident.lident

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
| OSig (_57_166) -> begin
_57_166
end))

let ___OLet____0 = (fun projectee -> (match (projectee) with
| OLet (_57_169) -> begin
_57_169
end))

let ___ORec____0 = (fun projectee -> (match (projectee) with
| ORec (_57_172) -> begin
_57_172
end))

let range_of_occurrence = (fun _57_3 -> (match (_57_3) with
| (OLet (l)) | (ORec (l)) -> begin
(FStar_Ident.range_of_lid l)
end
| OSig (se) -> begin
(FStar_Absyn_Util.range_of_sigelt se)
end))

type foundname =
| Exp_name of (occurrence * FStar_Absyn_Syntax.exp)
| Typ_name of (occurrence * FStar_Absyn_Syntax.typ)
| Eff_name of (occurrence * FStar_Ident.lident)
| Knd_name of (occurrence * FStar_Ident.lident)

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
| Exp_name (_57_181) -> begin
_57_181
end))

let ___Typ_name____0 = (fun projectee -> (match (projectee) with
| Typ_name (_57_184) -> begin
_57_184
end))

let ___Eff_name____0 = (fun projectee -> (match (projectee) with
| Eff_name (_57_187) -> begin
_57_187
end))

let ___Knd_name____0 = (fun projectee -> (match (projectee) with
| Knd_name (_57_190) -> begin
_57_190
end))

let fv_qual_of_se = (fun _57_5 -> (match (_57_5) with
| FStar_Absyn_Syntax.Sig_datacon (_57_193, _57_195, (l, _57_198, _57_200), quals, _57_204, _57_206) -> begin
(let qopt = (FStar_Util.find_map quals (fun _57_4 -> (match (_57_4) with
| FStar_Absyn_Syntax.RecordConstructor (fs) -> begin
Some (FStar_Absyn_Syntax.Record_ctor ((l, fs)))
end
| _57_213 -> begin
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
| FStar_Absyn_Syntax.Sig_val_decl (_57_218, _57_220, quals, _57_223) -> begin
None
end
| _57_227 -> begin
None
end))

let try_lookup_name = (fun any_val exclude_interf env lid -> (let find_in_sig = (fun lid -> (match ((let _134_305 = (sigmap env)
in (FStar_Util.smap_try_find _134_305 lid.FStar_Ident.str))) with
| Some (_57_235, true) when exclude_interf -> begin
None
end
| None -> begin
None
end
| Some (se, _57_242) -> begin
(match (se) with
| (FStar_Absyn_Syntax.Sig_typ_abbrev (_)) | (FStar_Absyn_Syntax.Sig_tycon (_)) -> begin
(let _134_308 = (let _134_307 = (let _134_306 = (FStar_Absyn_Util.ftv lid FStar_Absyn_Syntax.kun)
in (OSig (se), _134_306))
in Typ_name (_134_307))
in Some (_134_308))
end
| FStar_Absyn_Syntax.Sig_kind_abbrev (_57_252) -> begin
Some (Knd_name ((OSig (se), lid)))
end
| FStar_Absyn_Syntax.Sig_new_effect (ne, _57_256) -> begin
(let _134_311 = (let _134_310 = (let _134_309 = (FStar_Ident.set_lid_range ne.FStar_Absyn_Syntax.mname (FStar_Ident.range_of_lid lid))
in (OSig (se), _134_309))
in Eff_name (_134_310))
in Some (_134_311))
end
| FStar_Absyn_Syntax.Sig_effect_abbrev (_57_260) -> begin
Some (Eff_name ((OSig (se), lid)))
end
| FStar_Absyn_Syntax.Sig_datacon (_57_263) -> begin
(let _134_315 = (let _134_314 = (let _134_313 = (let _134_312 = (fv_qual_of_se se)
in (FStar_Absyn_Util.fvar _134_312 lid (FStar_Ident.range_of_lid lid)))
in (OSig (se), _134_313))
in Exp_name (_134_314))
in Some (_134_315))
end
| FStar_Absyn_Syntax.Sig_let (_57_266) -> begin
(let _134_318 = (let _134_317 = (let _134_316 = (FStar_Absyn_Util.fvar None lid (FStar_Ident.range_of_lid lid))
in (OSig (se), _134_316))
in Exp_name (_134_317))
in Some (_134_318))
end
| FStar_Absyn_Syntax.Sig_val_decl (_57_269, _57_271, quals, _57_274) -> begin
if (any_val || (FStar_All.pipe_right quals (FStar_Util.for_some (fun _57_6 -> (match (_57_6) with
| FStar_Absyn_Syntax.Assumption -> begin
true
end
| _57_280 -> begin
false
end))))) then begin
(let _134_323 = (let _134_322 = (let _134_321 = (let _134_320 = (fv_qual_of_se se)
in (FStar_Absyn_Util.fvar _134_320 lid (FStar_Ident.range_of_lid lid)))
in (OSig (se), _134_321))
in Exp_name (_134_322))
in Some (_134_323))
end else begin
None
end
end
| _57_282 -> begin
None
end)
end))
in (let found_id = (match (lid.FStar_Ident.ns) with
| [] -> begin
(match ((try_lookup_id' env lid.FStar_Ident.ident)) with
| Some (lid, e) -> begin
Some (Exp_name ((OLet (lid), e)))
end
| None -> begin
(let recname = (qualify env lid.FStar_Ident.ident)
in (FStar_Util.find_map env.recbindings (fun _57_7 -> (match (_57_7) with
| Binding_let (l) when (FStar_Ident.lid_equals l recname) -> begin
(let _134_327 = (let _134_326 = (let _134_325 = (FStar_Absyn_Util.fvar None recname (FStar_Ident.range_of_lid recname))
in (ORec (l), _134_325))
in Exp_name (_134_326))
in Some (_134_327))
end
| Binding_tycon (l) when (FStar_Ident.lid_equals l recname) -> begin
(let _134_330 = (let _134_329 = (let _134_328 = (FStar_Absyn_Util.ftv recname FStar_Absyn_Syntax.kun)
in (ORec (l), _134_328))
in Typ_name (_134_329))
in Some (_134_330))
end
| _57_296 -> begin
None
end))))
end)
end
| _57_298 -> begin
None
end)
in (match (found_id) with
| Some (_57_301) -> begin
found_id
end
| _57_304 -> begin
(resolve_in_open_namespaces env lid find_in_sig)
end))))

let try_lookup_typ_name' = (fun exclude_interf env lid -> (match ((try_lookup_name true exclude_interf env lid)) with
| Some (Typ_name (_57_309, t)) -> begin
Some (t)
end
| Some (Eff_name (_57_315, l)) -> begin
(let _134_337 = (FStar_Absyn_Util.ftv l FStar_Absyn_Syntax.mk_Kind_unknown)
in Some (_134_337))
end
| _57_321 -> begin
None
end))

let try_lookup_typ_name = (fun env l -> (try_lookup_typ_name' (not (env.iface)) env l))

let try_lookup_effect_name' = (fun exclude_interf env lid -> (match ((try_lookup_name true exclude_interf env lid)) with
| Some (Eff_name (o, l)) -> begin
Some ((o, l))
end
| _57_333 -> begin
None
end))

let try_lookup_effect_name = (fun env l -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some (o, l) -> begin
Some (l)
end
| _57_341 -> begin
None
end))

let try_lookup_effect_defn = (fun env l -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some (OSig (FStar_Absyn_Syntax.Sig_new_effect (ne, _57_346)), _57_351) -> begin
Some (ne)
end
| _57_355 -> begin
None
end))

let is_effect_name = (fun env lid -> (match ((try_lookup_effect_name env lid)) with
| None -> begin
false
end
| Some (_57_360) -> begin
true
end))

let try_resolve_typ_abbrev = (fun env lid -> (let find_in_sig = (fun lid -> (match ((let _134_366 = (sigmap env)
in (FStar_Util.smap_try_find _134_366 lid.FStar_Ident.str))) with
| Some (FStar_Absyn_Syntax.Sig_typ_abbrev (lid, tps, k, def, _57_371, _57_373), _57_377) -> begin
(let t = (let _134_369 = (let _134_368 = (let _134_367 = (FStar_Absyn_Util.close_with_lam tps def)
in (_134_367, lid))
in FStar_Absyn_Syntax.Meta_named (_134_368))
in (FStar_Absyn_Syntax.mk_Typ_meta _134_369))
in Some (t))
end
| _57_382 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))

let lookup_letbinding_quals = (fun env lid -> (let find_in_sig = (fun lid -> (match ((let _134_376 = (sigmap env)
in (FStar_Util.smap_try_find _134_376 lid.FStar_Ident.str))) with
| Some (FStar_Absyn_Syntax.Sig_val_decl (lid, _57_389, quals, _57_392), _57_396) -> begin
Some (quals)
end
| _57_400 -> begin
None
end))
in (match ((resolve_in_open_namespaces env lid find_in_sig)) with
| Some (quals) -> begin
quals
end
| _57_404 -> begin
[]
end)))

let try_lookup_module = (fun env path -> (match ((FStar_List.tryFind (fun _57_409 -> (match (_57_409) with
| (mlid, modul) -> begin
((FStar_Ident.path_of_lid mlid) = path)
end)) env.modules)) with
| Some (_57_411, modul) -> begin
Some (modul)
end
| None -> begin
None
end))

let try_lookup_let = (fun env lid -> (let find_in_sig = (fun lid -> (match ((let _134_388 = (sigmap env)
in (FStar_Util.smap_try_find _134_388 lid.FStar_Ident.str))) with
| Some (FStar_Absyn_Syntax.Sig_let (_57_421), _57_424) -> begin
(let _134_389 = (FStar_Absyn_Util.fvar None lid (FStar_Ident.range_of_lid lid))
in Some (_134_389))
end
| _57_428 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))

let try_lookup_lid' = (fun any_val exclude_interf env lid -> (match ((try_lookup_name any_val exclude_interf env lid)) with
| Some (Exp_name (_57_434, e)) -> begin
Some (e)
end
| _57_440 -> begin
None
end))

let try_lookup_lid = (fun env l -> (try_lookup_lid' env.iface false env l))

let try_lookup_datacon = (fun env lid -> (let find_in_sig = (fun lid -> (match ((let _134_408 = (sigmap env)
in (FStar_Util.smap_try_find _134_408 lid.FStar_Ident.str))) with
| Some (FStar_Absyn_Syntax.Sig_val_decl (_57_448, _57_450, quals, _57_453), _57_457) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _57_8 -> (match (_57_8) with
| FStar_Absyn_Syntax.Assumption -> begin
true
end
| _57_463 -> begin
false
end)))) then begin
Some ((FStar_Absyn_Util.fv lid))
end else begin
None
end
end
| Some (FStar_Absyn_Syntax.Sig_datacon (_57_465), _57_468) -> begin
Some ((FStar_Absyn_Util.fv lid))
end
| _57_472 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))

let find_all_datacons = (fun env lid -> (let find_in_sig = (fun lid -> (match ((let _134_416 = (sigmap env)
in (FStar_Util.smap_try_find _134_416 lid.FStar_Ident.str))) with
| Some (FStar_Absyn_Syntax.Sig_tycon (_57_478, _57_480, _57_482, _57_484, datas, _57_487, _57_489), _57_493) -> begin
Some (datas)
end
| _57_497 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))

type record_or_dc =
{typename : FStar_Ident.lident; constrname : FStar_Ident.lident; parms : FStar_Absyn_Syntax.binders; fields : (FStar_Absyn_Syntax.fieldname * FStar_Absyn_Syntax.typ) Prims.list; is_record : Prims.bool}

let is_Mkrecord_or_dc = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkrecord_or_dc"))))

let record_cache_aux = (let record_cache = (FStar_Util.mk_ref (([])::[]))
in (let push = (fun _57_506 -> (match (()) with
| () -> begin
(let _134_446 = (let _134_445 = (let _134_443 = (FStar_ST.read record_cache)
in (FStar_List.hd _134_443))
in (let _134_444 = (FStar_ST.read record_cache)
in (_134_445)::_134_444))
in (FStar_ST.op_Colon_Equals record_cache _134_446))
end))
in (let pop = (fun _57_508 -> (match (()) with
| () -> begin
(let _134_450 = (let _134_449 = (FStar_ST.read record_cache)
in (FStar_List.tl _134_449))
in (FStar_ST.op_Colon_Equals record_cache _134_450))
end))
in (let peek = (fun _57_510 -> (match (()) with
| () -> begin
(let _134_453 = (FStar_ST.read record_cache)
in (FStar_List.hd _134_453))
end))
in (let insert = (fun r -> (let _134_460 = (let _134_459 = (let _134_456 = (peek ())
in (r)::_134_456)
in (let _134_458 = (let _134_457 = (FStar_ST.read record_cache)
in (FStar_List.tl _134_457))
in (_134_459)::_134_458))
in (FStar_ST.op_Colon_Equals record_cache _134_460)))
in (push, pop, peek, insert))))))

let push_record_cache = (let _57_520 = record_cache_aux
in (match (_57_520) with
| (push, _57_515, _57_517, _57_519) -> begin
push
end))

let pop_record_cache = (let _57_528 = record_cache_aux
in (match (_57_528) with
| (_57_522, pop, _57_525, _57_527) -> begin
pop
end))

let peek_record_cache = (let _57_536 = record_cache_aux
in (match (_57_536) with
| (_57_530, _57_532, peek, _57_535) -> begin
peek
end))

let insert_record_cache = (let _57_544 = record_cache_aux
in (match (_57_544) with
| (_57_538, _57_540, _57_542, insert) -> begin
insert
end))

let extract_record = (fun e _57_12 -> (match (_57_12) with
| FStar_Absyn_Syntax.Sig_bundle (sigs, _57_549, _57_551, _57_553) -> begin
(let is_rec = (FStar_Util.for_some (fun _57_9 -> (match (_57_9) with
| (FStar_Absyn_Syntax.RecordType (_)) | (FStar_Absyn_Syntax.RecordConstructor (_)) -> begin
true
end
| _57_564 -> begin
false
end)))
in (let find_dc = (fun dc -> (FStar_All.pipe_right sigs (FStar_Util.find_opt (fun _57_10 -> (match (_57_10) with
| FStar_Absyn_Syntax.Sig_datacon (lid, _57_571, _57_573, _57_575, _57_577, _57_579) -> begin
(FStar_Ident.lid_equals dc lid)
end
| _57_583 -> begin
false
end)))))
in (FStar_All.pipe_right sigs (FStar_List.iter (fun _57_11 -> (match (_57_11) with
| FStar_Absyn_Syntax.Sig_tycon (typename, parms, _57_588, _57_590, dc::[], tags, _57_595) -> begin
(match ((let _134_531 = (find_dc dc)
in (FStar_All.pipe_left FStar_Util.must _134_531))) with
| FStar_Absyn_Syntax.Sig_datacon (constrname, t, _57_601, _57_603, _57_605, _57_607) -> begin
(let formals = (match ((FStar_Absyn_Util.function_formals t)) with
| Some (x, _57_612) -> begin
x
end
| _57_616 -> begin
[]
end)
in (let is_rec = (is_rec tags)
in (let fields = (FStar_All.pipe_right formals (FStar_List.collect (fun b -> (match (b) with
| (FStar_Util.Inr (x), q) -> begin
if ((FStar_Absyn_Syntax.is_null_binder b) || (is_rec && (q = Some (FStar_Absyn_Syntax.Implicit)))) then begin
[]
end else begin
(let _134_535 = (let _134_534 = (let _134_533 = if is_rec then begin
(FStar_Absyn_Util.unmangle_field_name x.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ppname)
end else begin
x.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ppname
end
in (qual constrname _134_533))
in (_134_534, x.FStar_Absyn_Syntax.sort))
in (_134_535)::[])
end
end
| _57_625 -> begin
[]
end))))
in (let record = {typename = typename; constrname = constrname; parms = parms; fields = fields; is_record = is_rec}
in (insert_record_cache record)))))
end
| _57_629 -> begin
()
end)
end
| _57_631 -> begin
()
end))))))
end
| _57_633 -> begin
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
(let _134_546 = (aux tl)
in (hd)::_134_546)
end))
in (aux ns)))
in (let find_in_cache = (fun fieldname -> (let _57_651 = (fieldname.FStar_Ident.ns, fieldname.FStar_Ident.ident)
in (match (_57_651) with
| (ns, fieldname) -> begin
(let _134_551 = (peek_record_cache ())
in (FStar_Util.find_map _134_551 (fun record -> (let constrname = record.constrname.FStar_Ident.ident
in (let ns = (maybe_add_constrname ns constrname)
in (let fname = (FStar_Ident.lid_of_ids (FStar_List.append ns ((fieldname)::[])))
in (FStar_Util.find_map record.fields (fun _57_659 -> (match (_57_659) with
| (f, _57_658) -> begin
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
| _57_667 -> begin
None
end))

let try_lookup_projector_by_field_name = (fun env fieldname -> (match ((try_lookup_record_or_dc_by_field_name env fieldname)) with
| Some (r, f) -> begin
Some ((f, r.is_record))
end
| _57_675 -> begin
None
end))

let qualify_field_to_record = (fun env recd f -> (let qualify = (fun fieldname -> (let _57_683 = (fieldname.FStar_Ident.ns, fieldname.FStar_Ident.ident)
in (match (_57_683) with
| (ns, fieldname) -> begin
(let constrname = recd.constrname.FStar_Ident.ident
in (let fname = (FStar_Ident.lid_of_ids (FStar_List.append (FStar_List.append ns ((constrname)::[])) ((fieldname)::[])))
in (FStar_Util.find_map recd.fields (fun _57_689 -> (match (_57_689) with
| (f, _57_688) -> begin
if (FStar_Ident.lid_equals fname f) then begin
Some (fname)
end else begin
None
end
end)))))
end)))
in (resolve_in_open_namespaces env f qualify)))

let find_kind_abbrev = (fun env l -> (match ((try_lookup_name true (not (env.iface)) env l)) with
| Some (Knd_name (_57_693, l)) -> begin
Some (l)
end
| _57_699 -> begin
None
end))

let is_kind_abbrev = (fun env l -> (match ((find_kind_abbrev env l)) with
| None -> begin
false
end
| Some (_57_704) -> begin
true
end))

let unique_name = (fun any_val exclude_if env lid -> (match ((try_lookup_lid' any_val exclude_if env lid)) with
| None -> begin
(match ((find_kind_abbrev env lid)) with
| None -> begin
true
end
| Some (_57_713) -> begin
false
end)
end
| Some (_57_716) -> begin
false
end))

let unique_typ_name = (fun env lid -> (match ((try_lookup_typ_name' true env lid)) with
| None -> begin
true
end
| Some (a) -> begin
false
end))

let unique = (fun any_val exclude_if env lid -> (let this_env = (let _57_727 = env
in {curmodule = _57_727.curmodule; modules = _57_727.modules; open_namespaces = []; modul_abbrevs = _57_727.modul_abbrevs; sigaccum = _57_727.sigaccum; localbindings = _57_727.localbindings; recbindings = _57_727.recbindings; phase = _57_727.phase; sigmap = _57_727.sigmap; default_result_effect = _57_727.default_result_effect; iface = _57_727.iface; admitted_iface = _57_727.admitted_iface})
in ((unique_name any_val exclude_if this_env lid) && (unique_typ_name this_env lid))))

let gen_bvd = (fun _57_13 -> (match (_57_13) with
| Binding_typ_var (id) -> begin
(let _134_600 = (let _134_599 = (let _134_598 = (FStar_Absyn_Util.genident (Some (id.FStar_Ident.idRange)))
in (id, _134_598))
in (FStar_Absyn_Util.mkbvd _134_599))
in FStar_Util.Inl (_134_600))
end
| Binding_var (id) -> begin
(let _134_603 = (let _134_602 = (let _134_601 = (FStar_Absyn_Util.genident (Some (id.FStar_Ident.idRange)))
in (id, _134_601))
in (FStar_Absyn_Util.mkbvd _134_602))
in FStar_Util.Inr (_134_603))
end
| _57_736 -> begin
(FStar_All.failwith "Tried to generate a bound variable for a type constructor")
end))

let push_bvvdef = (fun env x -> (let b = Binding_var (x.FStar_Absyn_Syntax.ppname)
in (let _57_740 = env
in {curmodule = _57_740.curmodule; modules = _57_740.modules; open_namespaces = _57_740.open_namespaces; modul_abbrevs = _57_740.modul_abbrevs; sigaccum = _57_740.sigaccum; localbindings = ((FStar_Util.Inr (x), b))::env.localbindings; recbindings = _57_740.recbindings; phase = _57_740.phase; sigmap = _57_740.sigmap; default_result_effect = _57_740.default_result_effect; iface = _57_740.iface; admitted_iface = _57_740.admitted_iface})))

let push_btvdef = (fun env x -> (let b = Binding_typ_var (x.FStar_Absyn_Syntax.ppname)
in (let _57_745 = env
in {curmodule = _57_745.curmodule; modules = _57_745.modules; open_namespaces = _57_745.open_namespaces; modul_abbrevs = _57_745.modul_abbrevs; sigaccum = _57_745.sigaccum; localbindings = ((FStar_Util.Inl (x), b))::env.localbindings; recbindings = _57_745.recbindings; phase = _57_745.phase; sigmap = _57_745.sigmap; default_result_effect = _57_745.default_result_effect; iface = _57_745.iface; admitted_iface = _57_745.admitted_iface})))

let push_local_binding = (fun env b -> (let bvd = (gen_bvd b)
in ((let _57_750 = env
in {curmodule = _57_750.curmodule; modules = _57_750.modules; open_namespaces = _57_750.open_namespaces; modul_abbrevs = _57_750.modul_abbrevs; sigaccum = _57_750.sigaccum; localbindings = ((bvd, b))::env.localbindings; recbindings = _57_750.recbindings; phase = _57_750.phase; sigmap = _57_750.sigmap; default_result_effect = _57_750.default_result_effect; iface = _57_750.iface; admitted_iface = _57_750.admitted_iface}), bvd)))

let push_local_tbinding = (fun env a -> (match ((push_local_binding env (Binding_typ_var (a)))) with
| (env, FStar_Util.Inl (x)) -> begin
(env, x)
end
| _57_759 -> begin
(FStar_All.failwith "impossible")
end))

let push_local_vbinding = (fun env b -> (match ((push_local_binding env (Binding_var (b)))) with
| (env, FStar_Util.Inr (x)) -> begin
(env, x)
end
| _57_767 -> begin
(FStar_All.failwith "impossible")
end))

let push_rec_binding = (fun env b -> (match (b) with
| (Binding_let (lid)) | (Binding_tycon (lid)) -> begin
if (unique false true env lid) then begin
(let _57_773 = env
in {curmodule = _57_773.curmodule; modules = _57_773.modules; open_namespaces = _57_773.open_namespaces; modul_abbrevs = _57_773.modul_abbrevs; sigaccum = _57_773.sigaccum; localbindings = _57_773.localbindings; recbindings = (b)::env.recbindings; phase = _57_773.phase; sigmap = _57_773.sigmap; default_result_effect = _57_773.default_result_effect; iface = _57_773.iface; admitted_iface = _57_773.admitted_iface})
end else begin
(Prims.raise (FStar_Absyn_Syntax.Error (((Prims.strcat "Duplicate top-level names " lid.FStar_Ident.str), (FStar_Ident.range_of_lid lid)))))
end
end
| _57_776 -> begin
(FStar_All.failwith "Unexpected rec_binding")
end))

let push_sigelt = (fun env s -> (let err = (fun l -> (let sopt = (let _134_634 = (sigmap env)
in (FStar_Util.smap_try_find _134_634 l.FStar_Ident.str))
in (let r = (match (sopt) with
| Some (se, _57_784) -> begin
(match ((let _134_635 = (FStar_Absyn_Util.lids_of_sigelt se)
in (FStar_Util.find_opt (FStar_Ident.lid_equals l) _134_635))) with
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
in (let _134_638 = (let _134_637 = (let _134_636 = (FStar_Util.format2 "Duplicate top-level names [%s]; previously declared at %s" (FStar_Ident.text_of_lid l) r)
in (_134_636, (FStar_Ident.range_of_lid l)))
in FStar_Absyn_Syntax.Error (_134_637))
in (Prims.raise _134_638)))))
in (let env = (let _57_802 = (match (s) with
| FStar_Absyn_Syntax.Sig_let (_57_793) -> begin
(false, true)
end
| FStar_Absyn_Syntax.Sig_bundle (_57_796) -> begin
(true, true)
end
| _57_799 -> begin
(false, false)
end)
in (match (_57_802) with
| (any_val, exclude_if) -> begin
(let lids = (FStar_Absyn_Util.lids_of_sigelt s)
in (match ((FStar_Util.find_map lids (fun l -> if (not ((unique any_val exclude_if env l))) then begin
Some (l)
end else begin
None
end))) with
| None -> begin
(let _57_806 = (extract_record env s)
in (let _57_808 = env
in {curmodule = _57_808.curmodule; modules = _57_808.modules; open_namespaces = _57_808.open_namespaces; modul_abbrevs = _57_808.modul_abbrevs; sigaccum = (s)::env.sigaccum; localbindings = _57_808.localbindings; recbindings = _57_808.recbindings; phase = _57_808.phase; sigmap = _57_808.sigmap; default_result_effect = _57_808.default_result_effect; iface = _57_808.iface; admitted_iface = _57_808.admitted_iface}))
end
| Some (l) -> begin
(err l)
end))
end))
in (let _57_827 = (match (s) with
| FStar_Absyn_Syntax.Sig_bundle (ses, _57_815, _57_817, _57_819) -> begin
(let _134_642 = (FStar_List.map (fun se -> (let _134_641 = (FStar_Absyn_Util.lids_of_sigelt se)
in (_134_641, se))) ses)
in (env, _134_642))
end
| _57_824 -> begin
(let _134_645 = (let _134_644 = (let _134_643 = (FStar_Absyn_Util.lids_of_sigelt s)
in (_134_643, s))
in (_134_644)::[])
in (env, _134_645))
end)
in (match (_57_827) with
| (env, lss) -> begin
(let _57_832 = (FStar_All.pipe_right lss (FStar_List.iter (fun _57_830 -> (match (_57_830) with
| (lids, se) -> begin
(FStar_All.pipe_right lids (FStar_List.iter (fun lid -> (let _134_648 = (sigmap env)
in (FStar_Util.smap_add _134_648 lid.FStar_Ident.str (se, (env.iface && (not (env.admitted_iface)))))))))
end))))
in env)
end)))))

let push_namespace = (fun env lid -> (let _57_836 = env
in {curmodule = _57_836.curmodule; modules = _57_836.modules; open_namespaces = (lid)::env.open_namespaces; modul_abbrevs = _57_836.modul_abbrevs; sigaccum = _57_836.sigaccum; localbindings = _57_836.localbindings; recbindings = _57_836.recbindings; phase = _57_836.phase; sigmap = _57_836.sigmap; default_result_effect = _57_836.default_result_effect; iface = _57_836.iface; admitted_iface = _57_836.admitted_iface}))

let push_module_abbrev = (fun env x l -> if (FStar_All.pipe_right env.modul_abbrevs (FStar_Util.for_some (fun _57_844 -> (match (_57_844) with
| (y, _57_843) -> begin
(x.FStar_Ident.idText = y.FStar_Ident.idText)
end)))) then begin
(let _134_662 = (let _134_661 = (let _134_660 = (FStar_Util.format1 "Module %s is already defined" x.FStar_Ident.idText)
in (_134_660, x.FStar_Ident.idRange))
in FStar_Absyn_Syntax.Error (_134_661))
in (Prims.raise _134_662))
end else begin
(let _57_845 = env
in {curmodule = _57_845.curmodule; modules = _57_845.modules; open_namespaces = _57_845.open_namespaces; modul_abbrevs = ((x, l))::env.modul_abbrevs; sigaccum = _57_845.sigaccum; localbindings = _57_845.localbindings; recbindings = _57_845.recbindings; phase = _57_845.phase; sigmap = _57_845.sigmap; default_result_effect = _57_845.default_result_effect; iface = _57_845.iface; admitted_iface = _57_845.admitted_iface})
end)

let is_type_lid = (fun env lid -> (let aux = (fun _57_850 -> (match (()) with
| () -> begin
(match ((try_lookup_typ_name' false env lid)) with
| Some (_57_852) -> begin
true
end
| _57_855 -> begin
false
end)
end))
in if (lid.FStar_Ident.ns = []) then begin
(match ((try_lookup_id env lid.FStar_Ident.ident)) with
| Some (_57_857) -> begin
false
end
| _57_860 -> begin
(aux ())
end)
end else begin
(aux ())
end))

let check_admits = (fun nm env -> (let warn = (not ((let _134_674 = (FStar_ST.read FStar_Options.admit_fsi)
in (FStar_All.pipe_right _134_674 (FStar_Util.for_some (fun l -> (nm.FStar_Ident.str = l)))))))
in (FStar_All.pipe_right env.sigaccum (FStar_List.iter (fun se -> (match (se) with
| FStar_Absyn_Syntax.Sig_val_decl (l, t, quals, r) -> begin
(match ((try_lookup_lid env l)) with
| None -> begin
(let _57_873 = if warn then begin
(let _134_678 = (let _134_677 = (FStar_Range.string_of_range (FStar_Ident.range_of_lid l))
in (let _134_676 = (FStar_Absyn_Print.sli l)
in (FStar_Util.format2 "%s: Warning: Admitting %s without a definition\n" _134_677 _134_676)))
in (FStar_Util.print_string _134_678))
end else begin
()
end
in (let _134_679 = (sigmap env)
in (FStar_Util.smap_add _134_679 l.FStar_Ident.str (FStar_Absyn_Syntax.Sig_val_decl ((l, t, (FStar_Absyn_Syntax.Assumption)::quals, r)), false))))
end
| Some (_57_876) -> begin
()
end)
end
| _57_879 -> begin
()
end))))))

let finish = (fun env modul -> (let _57_917 = (FStar_All.pipe_right modul.FStar_Absyn_Syntax.declarations (FStar_List.iter (fun _57_15 -> (match (_57_15) with
| FStar_Absyn_Syntax.Sig_bundle (ses, quals, _57_886, _57_888) -> begin
if (FStar_List.contains FStar_Absyn_Syntax.Private quals) then begin
(FStar_All.pipe_right ses (FStar_List.iter (fun _57_14 -> (match (_57_14) with
| FStar_Absyn_Syntax.Sig_datacon (lid, _57_894, _57_896, _57_898, _57_900, _57_902) -> begin
(let _134_686 = (sigmap env)
in (FStar_Util.smap_remove _134_686 lid.FStar_Ident.str))
end
| _57_906 -> begin
()
end))))
end else begin
()
end
end
| FStar_Absyn_Syntax.Sig_val_decl (lid, _57_909, quals, _57_912) -> begin
if (FStar_List.contains FStar_Absyn_Syntax.Private quals) then begin
(let _134_687 = (sigmap env)
in (FStar_Util.smap_remove _134_687 lid.FStar_Ident.str))
end else begin
()
end
end
| _57_916 -> begin
()
end))))
in (let _57_919 = env
in {curmodule = None; modules = ((modul.FStar_Absyn_Syntax.name, modul))::env.modules; open_namespaces = []; modul_abbrevs = []; sigaccum = []; localbindings = []; recbindings = []; phase = FStar_Parser_AST.Un; sigmap = _57_919.sigmap; default_result_effect = _57_919.default_result_effect; iface = _57_919.iface; admitted_iface = _57_919.admitted_iface})))

let push = (fun env -> (let _57_922 = (push_record_cache ())
in (let _57_924 = env
in (let _134_692 = (let _134_691 = (let _134_690 = (sigmap env)
in (FStar_Util.smap_copy _134_690))
in (_134_691)::env.sigmap)
in {curmodule = _57_924.curmodule; modules = _57_924.modules; open_namespaces = _57_924.open_namespaces; modul_abbrevs = _57_924.modul_abbrevs; sigaccum = _57_924.sigaccum; localbindings = _57_924.localbindings; recbindings = _57_924.recbindings; phase = _57_924.phase; sigmap = _134_692; default_result_effect = _57_924.default_result_effect; iface = _57_924.iface; admitted_iface = _57_924.admitted_iface}))))

let mark = (fun env -> (push env))

let reset_mark = (fun env -> (let _57_928 = env
in (let _134_697 = (FStar_List.tl env.sigmap)
in {curmodule = _57_928.curmodule; modules = _57_928.modules; open_namespaces = _57_928.open_namespaces; modul_abbrevs = _57_928.modul_abbrevs; sigaccum = _57_928.sigaccum; localbindings = _57_928.localbindings; recbindings = _57_928.recbindings; phase = _57_928.phase; sigmap = _134_697; default_result_effect = _57_928.default_result_effect; iface = _57_928.iface; admitted_iface = _57_928.admitted_iface})))

let commit_mark = (fun env -> (match (env.sigmap) with
| hd::_57_933::tl -> begin
(let _57_937 = env
in {curmodule = _57_937.curmodule; modules = _57_937.modules; open_namespaces = _57_937.open_namespaces; modul_abbrevs = _57_937.modul_abbrevs; sigaccum = _57_937.sigaccum; localbindings = _57_937.localbindings; recbindings = _57_937.recbindings; phase = _57_937.phase; sigmap = (hd)::tl; default_result_effect = _57_937.default_result_effect; iface = _57_937.iface; admitted_iface = _57_937.admitted_iface})
end
| _57_940 -> begin
(FStar_All.failwith "Impossible")
end))

let pop = (fun env -> (match (env.sigmap) with
| _57_944::maps -> begin
(let _57_946 = (pop_record_cache ())
in (let _57_948 = env
in {curmodule = _57_948.curmodule; modules = _57_948.modules; open_namespaces = _57_948.open_namespaces; modul_abbrevs = _57_948.modul_abbrevs; sigaccum = _57_948.sigaccum; localbindings = _57_948.localbindings; recbindings = _57_948.recbindings; phase = _57_948.phase; sigmap = maps; default_result_effect = _57_948.default_result_effect; iface = _57_948.iface; admitted_iface = _57_948.admitted_iface}))
end
| _57_951 -> begin
(FStar_All.failwith "No more modules to pop")
end))

let export_interface = (fun m env -> (let sigelt_in_m = (fun se -> (match ((FStar_Absyn_Util.lids_of_sigelt se)) with
| l::_57_957 -> begin
(l.FStar_Ident.nsstr = m.FStar_Ident.str)
end
| _57_961 -> begin
false
end))
in (let sm = (sigmap env)
in (let env = (pop env)
in (let keys = (FStar_Util.smap_keys sm)
in (let sm' = (sigmap env)
in (let _57_984 = (FStar_All.pipe_right keys (FStar_List.iter (fun k -> (match ((FStar_Util.smap_try_find sm' k)) with
| Some (se, true) when (sigelt_in_m se) -> begin
(let _57_971 = (FStar_Util.smap_remove sm' k)
in (let se = (match (se) with
| FStar_Absyn_Syntax.Sig_val_decl (l, t, q, r) -> begin
FStar_Absyn_Syntax.Sig_val_decl ((l, t, (FStar_Absyn_Syntax.Assumption)::q, r))
end
| _57_980 -> begin
se
end)
in (FStar_Util.smap_add sm' k (se, false))))
end
| _57_983 -> begin
()
end))))
in env)))))))

let finish_module_or_interface = (fun env modul -> (let _57_988 = if (not (modul.FStar_Absyn_Syntax.is_interface)) then begin
(check_admits modul.FStar_Absyn_Syntax.name env)
end else begin
()
end
in (finish env modul)))

let prepare_module_or_interface = (fun intf admitted env mname -> (let prep = (fun env -> (let open_ns = if (FStar_Ident.lid_equals mname FStar_Absyn_Const.prims_lid) then begin
[]
end else begin
if (FStar_Ident.lid_equals mname FStar_Absyn_Const.st_lid) then begin
(FStar_Absyn_Const.prims_lid)::[]
end else begin
if (FStar_Ident.lid_equals mname FStar_Absyn_Const.all_lid) then begin
(FStar_Absyn_Const.prims_lid)::(FStar_Absyn_Const.st_lid)::[]
end else begin
(FStar_Absyn_Const.prims_lid)::(FStar_Absyn_Const.st_lid)::(FStar_Absyn_Const.all_lid)::(FStar_Absyn_Const.fstar_ns_lid)::[]
end
end
end
in (let _57_997 = env
in {curmodule = Some (mname); modules = _57_997.modules; open_namespaces = open_ns; modul_abbrevs = _57_997.modul_abbrevs; sigaccum = _57_997.sigaccum; localbindings = _57_997.localbindings; recbindings = _57_997.recbindings; phase = _57_997.phase; sigmap = env.sigmap; default_result_effect = _57_997.default_result_effect; iface = intf; admitted_iface = admitted})))
in (match ((FStar_All.pipe_right env.modules (FStar_Util.find_opt (fun _57_1002 -> (match (_57_1002) with
| (l, _57_1001) -> begin
(FStar_Ident.lid_equals l mname)
end))))) with
| None -> begin
((prep env), false)
end
| Some (_57_1005, m) -> begin
(let _57_1009 = if ((not (m.FStar_Absyn_Syntax.is_interface)) || intf) then begin
(let _134_726 = (let _134_725 = (let _134_724 = (FStar_Util.format1 "Duplicate module or interface name: %s" mname.FStar_Ident.str)
in (_134_724, (FStar_Ident.range_of_lid mname)))
in FStar_Absyn_Syntax.Error (_134_725))
in (Prims.raise _134_726))
end else begin
()
end
in (let _134_728 = (let _134_727 = (push env)
in (prep _134_727))
in (_134_728, true)))
end)))

let enter_monad_scope = (fun env mname -> (let curmod = (current_module env)
in (let mscope = (FStar_Ident.lid_of_ids (FStar_List.append curmod.FStar_Ident.ns ((curmod.FStar_Ident.ident)::(mname)::[])))
in (let _57_1015 = env
in {curmodule = Some (mscope); modules = _57_1015.modules; open_namespaces = (curmod)::env.open_namespaces; modul_abbrevs = _57_1015.modul_abbrevs; sigaccum = _57_1015.sigaccum; localbindings = _57_1015.localbindings; recbindings = _57_1015.recbindings; phase = _57_1015.phase; sigmap = _57_1015.sigmap; default_result_effect = _57_1015.default_result_effect; iface = _57_1015.iface; admitted_iface = _57_1015.admitted_iface}))))

let exit_monad_scope = (fun env0 env -> (let _57_1019 = env
in {curmodule = env0.curmodule; modules = _57_1019.modules; open_namespaces = env0.open_namespaces; modul_abbrevs = _57_1019.modul_abbrevs; sigaccum = _57_1019.sigaccum; localbindings = _57_1019.localbindings; recbindings = _57_1019.recbindings; phase = _57_1019.phase; sigmap = _57_1019.sigmap; default_result_effect = _57_1019.default_result_effect; iface = _57_1019.iface; admitted_iface = _57_1019.admitted_iface}))

let fail_or = (fun env lookup lid -> (match ((lookup lid)) with
| None -> begin
(let r = (match ((try_lookup_name true false env lid)) with
| None -> begin
None
end
| (Some (Knd_name (o, _))) | (Some (Eff_name (o, _))) | (Some (Typ_name (o, _))) | (Some (Exp_name (o, _))) -> begin
Some ((range_of_occurrence o))
end)
in (let msg = (match (r) with
| None -> begin
""
end
| Some (r) -> begin
(let _134_743 = (FStar_Range.string_of_range r)
in (FStar_Util.format1 "(Possible clash with related name at %s)" _134_743))
end)
in (let _134_746 = (let _134_745 = (let _134_744 = (FStar_Util.format2 "Identifier not found: [%s] %s" (FStar_Ident.text_of_lid lid) msg)
in (_134_744, (FStar_Ident.range_of_lid lid)))
in FStar_Absyn_Syntax.Error (_134_745))
in (Prims.raise _134_746))))
end
| Some (r) -> begin
r
end))

let fail_or2 = (fun lookup id -> (match ((lookup id)) with
| None -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (((Prims.strcat (Prims.strcat "Identifier not found [" id.FStar_Ident.idText) "]"), id.FStar_Ident.idRange))))
end
| Some (r) -> begin
r
end))




