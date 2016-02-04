
open Prims
type binding =
| Binding_typ_var of FStar_Ident.ident
| Binding_var of FStar_Ident.ident
| Binding_let of FStar_Ident.lident
| Binding_tycon of FStar_Ident.lident

let is_Binding_typ_var : binding  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Binding_typ_var (_) -> begin
true
end
| _ -> begin
false
end))

let is_Binding_var : binding  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Binding_var (_) -> begin
true
end
| _ -> begin
false
end))

let is_Binding_let : binding  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Binding_let (_) -> begin
true
end
| _ -> begin
false
end))

let is_Binding_tycon : binding  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Binding_tycon (_) -> begin
true
end
| _ -> begin
false
end))

let ___Binding_typ_var____0 : binding  ->  FStar_Ident.ident = (fun projectee -> (match (projectee) with
| Binding_typ_var (_62_18) -> begin
_62_18
end))

let ___Binding_var____0 : binding  ->  FStar_Ident.ident = (fun projectee -> (match (projectee) with
| Binding_var (_62_21) -> begin
_62_21
end))

let ___Binding_let____0 : binding  ->  FStar_Ident.lident = (fun projectee -> (match (projectee) with
| Binding_let (_62_24) -> begin
_62_24
end))

let ___Binding_tycon____0 : binding  ->  FStar_Ident.lident = (fun projectee -> (match (projectee) with
| Binding_tycon (_62_27) -> begin
_62_27
end))

type kind_abbrev =
(FStar_Ident.lident * (FStar_Absyn_Syntax.btvdef, FStar_Absyn_Syntax.bvvdef) FStar_Util.either Prims.list * FStar_Absyn_Syntax.knd)

type env =
{curmodule : FStar_Ident.lident Prims.option; modules : (FStar_Ident.lident * FStar_Absyn_Syntax.modul) Prims.list; open_namespaces : FStar_Ident.lident Prims.list; modul_abbrevs : (FStar_Ident.ident * FStar_Ident.lident) Prims.list; sigaccum : FStar_Absyn_Syntax.sigelts; localbindings : ((FStar_Absyn_Syntax.btvdef, FStar_Absyn_Syntax.bvvdef) FStar_Util.either * binding) Prims.list; recbindings : binding Prims.list; phase : FStar_Parser_AST.level; sigmap : (FStar_Absyn_Syntax.sigelt * Prims.bool) FStar_Util.smap Prims.list; default_result_effect : FStar_Absyn_Syntax.typ  ->  FStar_Range.range  ->  FStar_Absyn_Syntax.comp; iface : Prims.bool; admitted_iface : Prims.bool}

let is_Mkenv : env  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv"))))

let open_modules : env  ->  (FStar_Ident.lident * FStar_Absyn_Syntax.modul) Prims.list = (fun e -> e.modules)

let current_module : env  ->  FStar_Absyn_Syntax.lident = (fun env -> (match (env.curmodule) with
| None -> begin
(FStar_All.failwith "Unset current module")
end
| Some (m) -> begin
m
end))

let qual : FStar_Ident.lident  ->  FStar_Ident.ident  ->  FStar_Ident.lident = (fun lid id -> (let _165_114 = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns ((lid.FStar_Ident.ident)::(id)::[])))
in (FStar_Ident.set_lid_range _165_114 id.FStar_Ident.idRange)))

let qualify : env  ->  FStar_Absyn_Syntax.ident  ->  FStar_Absyn_Syntax.lident = (fun env id -> (let _165_119 = (current_module env)
in (qual _165_119 id)))

let qualify_lid : env  ->  FStar_Absyn_Syntax.lident  ->  FStar_Absyn_Syntax.lident = (fun env lid -> (let cur = (current_module env)
in (let _165_124 = (FStar_Ident.lid_of_ids (FStar_List.append (FStar_List.append (FStar_List.append cur.FStar_Ident.ns ((cur.FStar_Ident.ident)::[])) lid.FStar_Ident.ns) ((lid.FStar_Ident.ident)::[])))
in (FStar_Ident.set_lid_range _165_124 (FStar_Ident.range_of_lid lid)))))

let new_sigmap = (fun _62_53 -> (match (()) with
| () -> begin
(FStar_Util.smap_create 100)
end))

let empty_env : Prims.unit  ->  env = (fun _62_54 -> (match (()) with
| () -> begin
(let _165_129 = (let _165_128 = (new_sigmap ())
in (_165_128)::[])
in {curmodule = None; modules = []; open_namespaces = []; modul_abbrevs = []; sigaccum = []; localbindings = []; recbindings = []; phase = FStar_Parser_AST.Un; sigmap = _165_129; default_result_effect = FStar_Absyn_Util.ml_comp; iface = false; admitted_iface = false})
end))

let sigmap : env  ->  (FStar_Absyn_Syntax.sigelt * Prims.bool) FStar_Util.smap = (fun env -> (FStar_List.hd env.sigmap))

let default_total : env  ->  env = (fun env -> (let _62_57 = env
in {curmodule = _62_57.curmodule; modules = _62_57.modules; open_namespaces = _62_57.open_namespaces; modul_abbrevs = _62_57.modul_abbrevs; sigaccum = _62_57.sigaccum; localbindings = _62_57.localbindings; recbindings = _62_57.recbindings; phase = _62_57.phase; sigmap = _62_57.sigmap; default_result_effect = (fun t _62_60 -> (FStar_Absyn_Syntax.mk_Total t)); iface = _62_57.iface; admitted_iface = _62_57.admitted_iface}))

let default_ml : env  ->  env = (fun env -> (let _62_63 = env
in {curmodule = _62_63.curmodule; modules = _62_63.modules; open_namespaces = _62_63.open_namespaces; modul_abbrevs = _62_63.modul_abbrevs; sigaccum = _62_63.sigaccum; localbindings = _62_63.localbindings; recbindings = _62_63.recbindings; phase = _62_63.phase; sigmap = _62_63.sigmap; default_result_effect = FStar_Absyn_Util.ml_comp; iface = _62_63.iface; admitted_iface = _62_63.admitted_iface}))

let range_of_binding : binding  ->  FStar_Range.range = (fun _62_1 -> (match (_62_1) with
| (Binding_typ_var (id)) | (Binding_var (id)) -> begin
id.FStar_Ident.idRange
end
| (Binding_let (lid)) | (Binding_tycon (lid)) -> begin
(FStar_Ident.range_of_lid lid)
end))

let try_lookup_typ_var : env  ->  FStar_Absyn_Syntax.ident  ->  FStar_Absyn_Syntax.typ Prims.option = (fun env id -> (let fopt = (FStar_List.tryFind (fun _62_77 -> (match (_62_77) with
| (_62_75, b) -> begin
(match (b) with
| (Binding_typ_var (id')) | (Binding_var (id')) -> begin
(id.FStar_Ident.idText = id'.FStar_Ident.idText)
end
| _62_82 -> begin
false
end)
end)) env.localbindings)
in (match (fopt) with
| Some (FStar_Util.Inl (bvd), Binding_typ_var (_62_87)) -> begin
(let _165_145 = (FStar_Absyn_Util.bvd_to_typ (FStar_Absyn_Util.set_bvd_range bvd id.FStar_Ident.idRange) FStar_Absyn_Syntax.kun)
in Some (_165_145))
end
| _62_92 -> begin
None
end)))

let resolve_in_open_namespaces' = (fun env lid finder -> (let aux = (fun namespaces -> (match ((finder lid)) with
| Some (r) -> begin
Some (r)
end
| _62_102 -> begin
(let ids = (FStar_Ident.ids_of_lid lid)
in (FStar_Util.find_map namespaces (fun ns -> (let full_name = (FStar_Ident.lid_of_ids (FStar_List.append (FStar_Ident.ids_of_lid ns) ids))
in (finder full_name)))))
end))
in (let _165_156 = (let _165_155 = (current_module env)
in (_165_155)::env.open_namespaces)
in (aux _165_156))))

let expand_module_abbrevs : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (match (lid.FStar_Ident.ns) with
| id::[] -> begin
(match ((FStar_All.pipe_right env.modul_abbrevs (FStar_List.tryFind (fun _62_113 -> (match (_62_113) with
| (id', _62_112) -> begin
(id.FStar_Ident.idText = id'.FStar_Ident.idText)
end))))) with
| None -> begin
lid
end
| Some (_62_116, lid') -> begin
(FStar_Ident.lid_of_ids (FStar_List.append (FStar_Ident.ids_of_lid lid') ((lid.FStar_Ident.ident)::[])))
end)
end
| _62_121 -> begin
lid
end))

let resolve_in_open_namespaces = (fun env lid finder -> (let _165_172 = (expand_module_abbrevs env lid)
in (resolve_in_open_namespaces' env _165_172 finder)))

let unmangleMap : (Prims.string * Prims.string) Prims.list = (("op_ColonColon", "Cons"))::(("not", "op_Negation"))::[]

let unmangleOpName : FStar_Absyn_Syntax.ident  ->  FStar_Absyn_Syntax.lident Prims.option = (fun id -> (FStar_Util.find_map unmangleMap (fun _62_129 -> (match (_62_129) with
| (x, y) -> begin
if (id.FStar_Ident.idText = x) then begin
(let _165_176 = (FStar_Ident.lid_of_path (("Prims")::(y)::[]) id.FStar_Ident.idRange)
in Some (_165_176))
end else begin
None
end
end))))

let try_lookup_id' : env  ->  FStar_Ident.ident  ->  (FStar_Absyn_Syntax.lident * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) Prims.option = (fun env id -> (match ((unmangleOpName id)) with
| Some (l) -> begin
(let _165_182 = (let _165_181 = (FStar_Absyn_Syntax.mk_Exp_fvar ((FStar_Absyn_Util.fv l), None) None id.FStar_Ident.idRange)
in (l, _165_181))
in Some (_165_182))
end
| _62_135 -> begin
(let found = (FStar_Util.find_map env.localbindings (fun _62_2 -> (match (_62_2) with
| (FStar_Util.Inl (_62_138), Binding_typ_var (id')) when (id'.FStar_Ident.idText = id.FStar_Ident.idText) -> begin
Some (FStar_Util.Inl (()))
end
| (FStar_Util.Inr (bvd), Binding_var (id')) when (id'.FStar_Ident.idText = id.FStar_Ident.idText) -> begin
(let _165_187 = (let _165_186 = (let _165_185 = (FStar_Ident.lid_of_ids ((id')::[]))
in (let _165_184 = (FStar_Absyn_Util.bvd_to_exp (FStar_Absyn_Util.set_bvd_range bvd id.FStar_Ident.idRange) FStar_Absyn_Syntax.tun)
in (_165_185, _165_184)))
in FStar_Util.Inr (_165_186))
in Some (_165_187))
end
| _62_149 -> begin
None
end)))
in (match (found) with
| Some (FStar_Util.Inr (x)) -> begin
Some (x)
end
| _62_155 -> begin
None
end))
end))

let try_lookup_id : env  ->  FStar_Absyn_Syntax.ident  ->  FStar_Absyn_Syntax.exp Prims.option = (fun env id -> (match ((try_lookup_id' env id)) with
| Some (_62_159, e) -> begin
Some (e)
end
| None -> begin
None
end))

type occurrence =
| OSig of FStar_Absyn_Syntax.sigelt
| OLet of FStar_Ident.lident
| ORec of FStar_Ident.lident

let is_OSig : occurrence  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| OSig (_) -> begin
true
end
| _ -> begin
false
end))

let is_OLet : occurrence  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| OLet (_) -> begin
true
end
| _ -> begin
false
end))

let is_ORec : occurrence  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| ORec (_) -> begin
true
end
| _ -> begin
false
end))

let ___OSig____0 : occurrence  ->  FStar_Absyn_Syntax.sigelt = (fun projectee -> (match (projectee) with
| OSig (_62_166) -> begin
_62_166
end))

let ___OLet____0 : occurrence  ->  FStar_Ident.lident = (fun projectee -> (match (projectee) with
| OLet (_62_169) -> begin
_62_169
end))

let ___ORec____0 : occurrence  ->  FStar_Ident.lident = (fun projectee -> (match (projectee) with
| ORec (_62_172) -> begin
_62_172
end))

let range_of_occurrence : occurrence  ->  FStar_Range.range = (fun _62_3 -> (match (_62_3) with
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

let is_Exp_name : foundname  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Exp_name (_) -> begin
true
end
| _ -> begin
false
end))

let is_Typ_name : foundname  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Typ_name (_) -> begin
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

let is_Knd_name : foundname  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Knd_name (_) -> begin
true
end
| _ -> begin
false
end))

let ___Exp_name____0 : foundname  ->  (occurrence * FStar_Absyn_Syntax.exp) = (fun projectee -> (match (projectee) with
| Exp_name (_62_181) -> begin
_62_181
end))

let ___Typ_name____0 : foundname  ->  (occurrence * FStar_Absyn_Syntax.typ) = (fun projectee -> (match (projectee) with
| Typ_name (_62_184) -> begin
_62_184
end))

let ___Eff_name____0 : foundname  ->  (occurrence * FStar_Ident.lident) = (fun projectee -> (match (projectee) with
| Eff_name (_62_187) -> begin
_62_187
end))

let ___Knd_name____0 : foundname  ->  (occurrence * FStar_Ident.lident) = (fun projectee -> (match (projectee) with
| Knd_name (_62_190) -> begin
_62_190
end))

let fv_qual_of_se : FStar_Absyn_Syntax.sigelt  ->  FStar_Absyn_Syntax.fv_qual Prims.option = (fun _62_5 -> (match (_62_5) with
| FStar_Absyn_Syntax.Sig_datacon (_62_193, _62_195, (l, _62_198, _62_200), quals, _62_204, _62_206) -> begin
(let qopt = (FStar_Util.find_map quals (fun _62_4 -> (match (_62_4) with
| FStar_Absyn_Syntax.RecordConstructor (fs) -> begin
Some (FStar_Absyn_Syntax.Record_ctor ((l, fs)))
end
| _62_213 -> begin
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
| FStar_Absyn_Syntax.Sig_val_decl (_62_218, _62_220, quals, _62_223) -> begin
None
end
| _62_227 -> begin
None
end))

let try_lookup_name : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Absyn_Syntax.lident  ->  foundname Prims.option = (fun any_val exclude_interf env lid -> (let find_in_sig = (fun lid -> (match ((let _165_305 = (sigmap env)
in (FStar_Util.smap_try_find _165_305 lid.FStar_Ident.str))) with
| Some (_62_235, true) when exclude_interf -> begin
None
end
| None -> begin
None
end
| Some (se, _62_242) -> begin
(match (se) with
| (FStar_Absyn_Syntax.Sig_typ_abbrev (_)) | (FStar_Absyn_Syntax.Sig_tycon (_)) -> begin
(let _165_308 = (let _165_307 = (let _165_306 = (FStar_Absyn_Util.ftv lid FStar_Absyn_Syntax.kun)
in (OSig (se), _165_306))
in Typ_name (_165_307))
in Some (_165_308))
end
| FStar_Absyn_Syntax.Sig_kind_abbrev (_62_252) -> begin
Some (Knd_name ((OSig (se), lid)))
end
| FStar_Absyn_Syntax.Sig_new_effect (ne, _62_256) -> begin
(let _165_311 = (let _165_310 = (let _165_309 = (FStar_Ident.set_lid_range ne.FStar_Absyn_Syntax.mname (FStar_Ident.range_of_lid lid))
in (OSig (se), _165_309))
in Eff_name (_165_310))
in Some (_165_311))
end
| FStar_Absyn_Syntax.Sig_effect_abbrev (_62_260) -> begin
Some (Eff_name ((OSig (se), lid)))
end
| FStar_Absyn_Syntax.Sig_datacon (_62_263) -> begin
(let _165_315 = (let _165_314 = (let _165_313 = (let _165_312 = (fv_qual_of_se se)
in (FStar_Absyn_Util.fvar _165_312 lid (FStar_Ident.range_of_lid lid)))
in (OSig (se), _165_313))
in Exp_name (_165_314))
in Some (_165_315))
end
| FStar_Absyn_Syntax.Sig_let (_62_266) -> begin
(let _165_318 = (let _165_317 = (let _165_316 = (FStar_Absyn_Util.fvar None lid (FStar_Ident.range_of_lid lid))
in (OSig (se), _165_316))
in Exp_name (_165_317))
in Some (_165_318))
end
| FStar_Absyn_Syntax.Sig_val_decl (_62_269, _62_271, quals, _62_274) -> begin
if (any_val || (FStar_All.pipe_right quals (FStar_Util.for_some (fun _62_6 -> (match (_62_6) with
| FStar_Absyn_Syntax.Assumption -> begin
true
end
| _62_280 -> begin
false
end))))) then begin
(let _165_323 = (let _165_322 = (let _165_321 = (let _165_320 = (fv_qual_of_se se)
in (FStar_Absyn_Util.fvar _165_320 lid (FStar_Ident.range_of_lid lid)))
in (OSig (se), _165_321))
in Exp_name (_165_322))
in Some (_165_323))
end else begin
None
end
end
| _62_282 -> begin
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
in (FStar_Util.find_map env.recbindings (fun _62_7 -> (match (_62_7) with
| Binding_let (l) when (FStar_Ident.lid_equals l recname) -> begin
(let _165_327 = (let _165_326 = (let _165_325 = (FStar_Absyn_Util.fvar None recname (FStar_Ident.range_of_lid recname))
in (ORec (l), _165_325))
in Exp_name (_165_326))
in Some (_165_327))
end
| Binding_tycon (l) when (FStar_Ident.lid_equals l recname) -> begin
(let _165_330 = (let _165_329 = (let _165_328 = (FStar_Absyn_Util.ftv recname FStar_Absyn_Syntax.kun)
in (ORec (l), _165_328))
in Typ_name (_165_329))
in Some (_165_330))
end
| _62_296 -> begin
None
end))))
end)
end
| _62_298 -> begin
None
end)
in (match (found_id) with
| Some (_62_301) -> begin
found_id
end
| _62_304 -> begin
(resolve_in_open_namespaces env lid find_in_sig)
end))))

let try_lookup_typ_name' : Prims.bool  ->  env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.typ Prims.option = (fun exclude_interf env lid -> (match ((try_lookup_name true exclude_interf env lid)) with
| Some (Typ_name (_62_309, t)) -> begin
Some (t)
end
| Some (Eff_name (_62_315, l)) -> begin
(let _165_337 = (FStar_Absyn_Util.ftv l FStar_Absyn_Syntax.mk_Kind_unknown)
in Some (_165_337))
end
| _62_321 -> begin
None
end))

let try_lookup_typ_name : env  ->  FStar_Absyn_Syntax.lident  ->  FStar_Absyn_Syntax.typ Prims.option = (fun env l -> (try_lookup_typ_name' (not (env.iface)) env l))

let try_lookup_effect_name' : Prims.bool  ->  env  ->  FStar_Ident.lident  ->  (occurrence * FStar_Ident.lident) Prims.option = (fun exclude_interf env lid -> (match ((try_lookup_name true exclude_interf env lid)) with
| Some (Eff_name (o, l)) -> begin
Some ((o, l))
end
| _62_333 -> begin
None
end))

let try_lookup_effect_name : env  ->  FStar_Absyn_Syntax.lident  ->  FStar_Absyn_Syntax.lident Prims.option = (fun env l -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some (o, l) -> begin
Some (l)
end
| _62_341 -> begin
None
end))

let try_lookup_effect_defn : env  ->  FStar_Absyn_Syntax.lident  ->  FStar_Absyn_Syntax.eff_decl Prims.option = (fun env l -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some (OSig (FStar_Absyn_Syntax.Sig_new_effect (ne, _62_346)), _62_351) -> begin
Some (ne)
end
| _62_355 -> begin
None
end))

let is_effect_name : env  ->  FStar_Absyn_Syntax.lident  ->  Prims.bool = (fun env lid -> (match ((try_lookup_effect_name env lid)) with
| None -> begin
false
end
| Some (_62_360) -> begin
true
end))

let try_resolve_typ_abbrev : env  ->  FStar_Absyn_Syntax.lident  ->  FStar_Absyn_Syntax.typ Prims.option = (fun env lid -> (let find_in_sig = (fun lid -> (match ((let _165_366 = (sigmap env)
in (FStar_Util.smap_try_find _165_366 lid.FStar_Ident.str))) with
| Some (FStar_Absyn_Syntax.Sig_typ_abbrev (lid, tps, k, def, _62_371, _62_373), _62_377) -> begin
(let t = (let _165_369 = (let _165_368 = (let _165_367 = (FStar_Absyn_Util.close_with_lam tps def)
in (_165_367, lid))
in FStar_Absyn_Syntax.Meta_named (_165_368))
in (FStar_Absyn_Syntax.mk_Typ_meta _165_369))
in Some (t))
end
| _62_382 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))

let lookup_letbinding_quals : env  ->  FStar_Absyn_Syntax.lident  ->  FStar_Absyn_Syntax.qualifier Prims.list = (fun env lid -> (let find_in_sig = (fun lid -> (match ((let _165_376 = (sigmap env)
in (FStar_Util.smap_try_find _165_376 lid.FStar_Ident.str))) with
| Some (FStar_Absyn_Syntax.Sig_val_decl (lid, _62_389, quals, _62_392), _62_396) -> begin
Some (quals)
end
| _62_400 -> begin
None
end))
in (match ((resolve_in_open_namespaces env lid find_in_sig)) with
| Some (quals) -> begin
quals
end
| _62_404 -> begin
[]
end)))

let try_lookup_module : env  ->  Prims.string Prims.list  ->  FStar_Absyn_Syntax.modul Prims.option = (fun env path -> (match ((FStar_List.tryFind (fun _62_409 -> (match (_62_409) with
| (mlid, modul) -> begin
((FStar_Ident.path_of_lid mlid) = path)
end)) env.modules)) with
| Some (_62_411, modul) -> begin
Some (modul)
end
| None -> begin
None
end))

let try_lookup_let : env  ->  FStar_Ident.lident  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax Prims.option = (fun env lid -> (let find_in_sig = (fun lid -> (match ((let _165_388 = (sigmap env)
in (FStar_Util.smap_try_find _165_388 lid.FStar_Ident.str))) with
| Some (FStar_Absyn_Syntax.Sig_let (_62_421), _62_424) -> begin
(let _165_389 = (FStar_Absyn_Util.fvar None lid (FStar_Ident.range_of_lid lid))
in Some (_165_389))
end
| _62_428 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))

let try_lookup_lid' : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Absyn_Syntax.lident  ->  FStar_Absyn_Syntax.exp Prims.option = (fun any_val exclude_interf env lid -> (match ((try_lookup_name any_val exclude_interf env lid)) with
| Some (Exp_name (_62_434, e)) -> begin
Some (e)
end
| _62_440 -> begin
None
end))

let try_lookup_lid : env  ->  FStar_Absyn_Syntax.lident  ->  FStar_Absyn_Syntax.exp Prims.option = (fun env l -> (try_lookup_lid' env.iface false env l))

let try_lookup_datacon : env  ->  FStar_Absyn_Syntax.lident  ->  FStar_Absyn_Syntax.typ FStar_Absyn_Syntax.var Prims.option = (fun env lid -> (let find_in_sig = (fun lid -> (match ((let _165_408 = (sigmap env)
in (FStar_Util.smap_try_find _165_408 lid.FStar_Ident.str))) with
| Some (FStar_Absyn_Syntax.Sig_val_decl (_62_448, _62_450, quals, _62_453), _62_457) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _62_8 -> (match (_62_8) with
| FStar_Absyn_Syntax.Assumption -> begin
true
end
| _62_463 -> begin
false
end)))) then begin
Some ((FStar_Absyn_Util.fv lid))
end else begin
None
end
end
| Some (FStar_Absyn_Syntax.Sig_datacon (_62_465), _62_468) -> begin
Some ((FStar_Absyn_Util.fv lid))
end
| _62_472 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))

let find_all_datacons : env  ->  FStar_Absyn_Syntax.lident  ->  FStar_Absyn_Syntax.lident Prims.list Prims.option = (fun env lid -> (let find_in_sig = (fun lid -> (match ((let _165_416 = (sigmap env)
in (FStar_Util.smap_try_find _165_416 lid.FStar_Ident.str))) with
| Some (FStar_Absyn_Syntax.Sig_tycon (_62_478, _62_480, _62_482, _62_484, datas, _62_487, _62_489), _62_493) -> begin
Some (datas)
end
| _62_497 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))

type record_or_dc =
{typename : FStar_Ident.lident; constrname : FStar_Ident.lident; parms : FStar_Absyn_Syntax.binders; fields : (FStar_Absyn_Syntax.fieldname * FStar_Absyn_Syntax.typ) Prims.list; is_record : Prims.bool}

let is_Mkrecord_or_dc : record_or_dc  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkrecord_or_dc"))))

let record_cache_aux : ((Prims.unit  ->  Prims.unit) * (Prims.unit  ->  Prims.unit) * (Prims.unit  ->  record_or_dc Prims.list) * (record_or_dc  ->  Prims.unit)) = (let record_cache = (FStar_Util.mk_ref (([])::[]))
in (let push = (fun _62_506 -> (match (()) with
| () -> begin
(let _165_446 = (let _165_445 = (let _165_443 = (FStar_ST.read record_cache)
in (FStar_List.hd _165_443))
in (let _165_444 = (FStar_ST.read record_cache)
in (_165_445)::_165_444))
in (FStar_ST.op_Colon_Equals record_cache _165_446))
end))
in (let pop = (fun _62_508 -> (match (()) with
| () -> begin
(let _165_450 = (let _165_449 = (FStar_ST.read record_cache)
in (FStar_List.tl _165_449))
in (FStar_ST.op_Colon_Equals record_cache _165_450))
end))
in (let peek = (fun _62_510 -> (match (()) with
| () -> begin
(let _165_453 = (FStar_ST.read record_cache)
in (FStar_List.hd _165_453))
end))
in (let insert = (fun r -> (let _165_460 = (let _165_459 = (let _165_456 = (peek ())
in (r)::_165_456)
in (let _165_458 = (let _165_457 = (FStar_ST.read record_cache)
in (FStar_List.tl _165_457))
in (_165_459)::_165_458))
in (FStar_ST.op_Colon_Equals record_cache _165_460)))
in (push, pop, peek, insert))))))

let push_record_cache : Prims.unit  ->  Prims.unit = (let _62_520 = record_cache_aux
in (match (_62_520) with
| (push, _62_515, _62_517, _62_519) -> begin
push
end))

let pop_record_cache : Prims.unit  ->  Prims.unit = (let _62_528 = record_cache_aux
in (match (_62_528) with
| (_62_522, pop, _62_525, _62_527) -> begin
pop
end))

let peek_record_cache : Prims.unit  ->  record_or_dc Prims.list = (let _62_536 = record_cache_aux
in (match (_62_536) with
| (_62_530, _62_532, peek, _62_535) -> begin
peek
end))

let insert_record_cache : record_or_dc  ->  Prims.unit = (let _62_544 = record_cache_aux
in (match (_62_544) with
| (_62_538, _62_540, _62_542, insert) -> begin
insert
end))

let extract_record : env  ->  FStar_Absyn_Syntax.sigelt  ->  Prims.unit = (fun e _62_12 -> (match (_62_12) with
| FStar_Absyn_Syntax.Sig_bundle (sigs, _62_549, _62_551, _62_553) -> begin
(let is_rec = (FStar_Util.for_some (fun _62_9 -> (match (_62_9) with
| (FStar_Absyn_Syntax.RecordType (_)) | (FStar_Absyn_Syntax.RecordConstructor (_)) -> begin
true
end
| _62_564 -> begin
false
end)))
in (let find_dc = (fun dc -> (FStar_All.pipe_right sigs (FStar_Util.find_opt (fun _62_10 -> (match (_62_10) with
| FStar_Absyn_Syntax.Sig_datacon (lid, _62_571, _62_573, _62_575, _62_577, _62_579) -> begin
(FStar_Ident.lid_equals dc lid)
end
| _62_583 -> begin
false
end)))))
in (FStar_All.pipe_right sigs (FStar_List.iter (fun _62_11 -> (match (_62_11) with
| FStar_Absyn_Syntax.Sig_tycon (typename, parms, _62_588, _62_590, dc::[], tags, _62_595) -> begin
(match ((let _165_531 = (find_dc dc)
in (FStar_All.pipe_left FStar_Util.must _165_531))) with
| FStar_Absyn_Syntax.Sig_datacon (constrname, t, _62_601, _62_603, _62_605, _62_607) -> begin
(let formals = (match ((FStar_Absyn_Util.function_formals t)) with
| Some (x, _62_612) -> begin
x
end
| _62_616 -> begin
[]
end)
in (let is_rec = (is_rec tags)
in (let fields = (FStar_All.pipe_right formals (FStar_List.collect (fun b -> (match (b) with
| (FStar_Util.Inr (x), q) -> begin
if ((FStar_Absyn_Syntax.is_null_binder b) || (is_rec && (q = Some (FStar_Absyn_Syntax.Implicit)))) then begin
[]
end else begin
(let _165_535 = (let _165_534 = (let _165_533 = if is_rec then begin
(FStar_Absyn_Util.unmangle_field_name x.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ppname)
end else begin
x.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ppname
end
in (qual constrname _165_533))
in (_165_534, x.FStar_Absyn_Syntax.sort))
in (_165_535)::[])
end
end
| _62_625 -> begin
[]
end))))
in (let record = {typename = typename; constrname = constrname; parms = parms; fields = fields; is_record = is_rec}
in (insert_record_cache record)))))
end
| _62_629 -> begin
()
end)
end
| _62_631 -> begin
()
end))))))
end
| _62_633 -> begin
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
(let _165_546 = (aux tl)
in (hd)::_165_546)
end))
in (aux ns)))
in (let find_in_cache = (fun fieldname -> (let _62_651 = (fieldname.FStar_Ident.ns, fieldname.FStar_Ident.ident)
in (match (_62_651) with
| (ns, fieldname) -> begin
(let _165_551 = (peek_record_cache ())
in (FStar_Util.find_map _165_551 (fun record -> (let constrname = record.constrname.FStar_Ident.ident
in (let ns = (maybe_add_constrname ns constrname)
in (let fname = (FStar_Ident.lid_of_ids (FStar_List.append ns ((fieldname)::[])))
in (FStar_Util.find_map record.fields (fun _62_659 -> (match (_62_659) with
| (f, _62_658) -> begin
if (FStar_Ident.lid_equals fname f) then begin
Some ((record, fname))
end else begin
None
end
end)))))))))
end)))
in (resolve_in_open_namespaces env fieldname find_in_cache))))

let try_lookup_record_by_field_name : env  ->  FStar_Absyn_Syntax.lident  ->  (record_or_dc * FStar_Absyn_Syntax.lident) Prims.option = (fun env fieldname -> (match ((try_lookup_record_or_dc_by_field_name env fieldname)) with
| Some (r, f) when r.is_record -> begin
Some ((r, f))
end
| _62_667 -> begin
None
end))

let try_lookup_projector_by_field_name : env  ->  FStar_Absyn_Syntax.lident  ->  (FStar_Absyn_Syntax.lident * Prims.bool) Prims.option = (fun env fieldname -> (match ((try_lookup_record_or_dc_by_field_name env fieldname)) with
| Some (r, f) -> begin
Some ((f, r.is_record))
end
| _62_675 -> begin
None
end))

let qualify_field_to_record : env  ->  record_or_dc  ->  FStar_Absyn_Syntax.lident  ->  FStar_Absyn_Syntax.lident Prims.option = (fun env recd f -> (let qualify = (fun fieldname -> (let _62_683 = (fieldname.FStar_Ident.ns, fieldname.FStar_Ident.ident)
in (match (_62_683) with
| (ns, fieldname) -> begin
(let constrname = recd.constrname.FStar_Ident.ident
in (let fname = (FStar_Ident.lid_of_ids (FStar_List.append (FStar_List.append ns ((constrname)::[])) ((fieldname)::[])))
in (FStar_Util.find_map recd.fields (fun _62_689 -> (match (_62_689) with
| (f, _62_688) -> begin
if (FStar_Ident.lid_equals fname f) then begin
Some (fname)
end else begin
None
end
end)))))
end)))
in (resolve_in_open_namespaces env f qualify)))

let find_kind_abbrev : env  ->  FStar_Absyn_Syntax.lident  ->  FStar_Absyn_Syntax.lident Prims.option = (fun env l -> (match ((try_lookup_name true (not (env.iface)) env l)) with
| Some (Knd_name (_62_693, l)) -> begin
Some (l)
end
| _62_699 -> begin
None
end))

let is_kind_abbrev : env  ->  FStar_Absyn_Syntax.lident  ->  Prims.bool = (fun env l -> (match ((find_kind_abbrev env l)) with
| None -> begin
false
end
| Some (_62_704) -> begin
true
end))

let unique_name : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Absyn_Syntax.lident  ->  Prims.bool = (fun any_val exclude_if env lid -> (match ((try_lookup_lid' any_val exclude_if env lid)) with
| None -> begin
(match ((find_kind_abbrev env lid)) with
| None -> begin
true
end
| Some (_62_713) -> begin
false
end)
end
| Some (_62_716) -> begin
false
end))

let unique_typ_name : env  ->  FStar_Absyn_Syntax.lident  ->  Prims.bool = (fun env lid -> (match ((try_lookup_typ_name' true env lid)) with
| None -> begin
true
end
| Some (a) -> begin
false
end))

let unique : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Absyn_Syntax.lident  ->  Prims.bool = (fun any_val exclude_if env lid -> (let this_env = (let _62_727 = env
in {curmodule = _62_727.curmodule; modules = _62_727.modules; open_namespaces = []; modul_abbrevs = _62_727.modul_abbrevs; sigaccum = _62_727.sigaccum; localbindings = _62_727.localbindings; recbindings = _62_727.recbindings; phase = _62_727.phase; sigmap = _62_727.sigmap; default_result_effect = _62_727.default_result_effect; iface = _62_727.iface; admitted_iface = _62_727.admitted_iface})
in ((unique_name any_val exclude_if this_env lid) && (unique_typ_name this_env lid))))

let gen_bvd = (fun _62_13 -> (match (_62_13) with
| Binding_typ_var (id) -> begin
(let _165_600 = (let _165_599 = (let _165_598 = (FStar_Absyn_Util.genident (Some (id.FStar_Ident.idRange)))
in (id, _165_598))
in (FStar_Absyn_Util.mkbvd _165_599))
in FStar_Util.Inl (_165_600))
end
| Binding_var (id) -> begin
(let _165_603 = (let _165_602 = (let _165_601 = (FStar_Absyn_Util.genident (Some (id.FStar_Ident.idRange)))
in (id, _165_601))
in (FStar_Absyn_Util.mkbvd _165_602))
in FStar_Util.Inr (_165_603))
end
| _62_736 -> begin
(FStar_All.failwith "Tried to generate a bound variable for a type constructor")
end))

let push_bvvdef : env  ->  FStar_Absyn_Syntax.bvvdef  ->  env = (fun env x -> (let b = Binding_var (x.FStar_Absyn_Syntax.ppname)
in (let _62_740 = env
in {curmodule = _62_740.curmodule; modules = _62_740.modules; open_namespaces = _62_740.open_namespaces; modul_abbrevs = _62_740.modul_abbrevs; sigaccum = _62_740.sigaccum; localbindings = ((FStar_Util.Inr (x), b))::env.localbindings; recbindings = _62_740.recbindings; phase = _62_740.phase; sigmap = _62_740.sigmap; default_result_effect = _62_740.default_result_effect; iface = _62_740.iface; admitted_iface = _62_740.admitted_iface})))

let push_btvdef : env  ->  FStar_Absyn_Syntax.btvdef  ->  env = (fun env x -> (let b = Binding_typ_var (x.FStar_Absyn_Syntax.ppname)
in (let _62_745 = env
in {curmodule = _62_745.curmodule; modules = _62_745.modules; open_namespaces = _62_745.open_namespaces; modul_abbrevs = _62_745.modul_abbrevs; sigaccum = _62_745.sigaccum; localbindings = ((FStar_Util.Inl (x), b))::env.localbindings; recbindings = _62_745.recbindings; phase = _62_745.phase; sigmap = _62_745.sigmap; default_result_effect = _62_745.default_result_effect; iface = _62_745.iface; admitted_iface = _62_745.admitted_iface})))

let push_local_binding : env  ->  binding  ->  (env * (FStar_Absyn_Syntax.btvdef, FStar_Absyn_Syntax.bvvdef) FStar_Util.either) = (fun env b -> (let bvd = (gen_bvd b)
in ((let _62_750 = env
in {curmodule = _62_750.curmodule; modules = _62_750.modules; open_namespaces = _62_750.open_namespaces; modul_abbrevs = _62_750.modul_abbrevs; sigaccum = _62_750.sigaccum; localbindings = ((bvd, b))::env.localbindings; recbindings = _62_750.recbindings; phase = _62_750.phase; sigmap = _62_750.sigmap; default_result_effect = _62_750.default_result_effect; iface = _62_750.iface; admitted_iface = _62_750.admitted_iface}), bvd)))

let push_local_tbinding : env  ->  FStar_Absyn_Syntax.ident  ->  (env * FStar_Absyn_Syntax.btvdef) = (fun env a -> (match ((push_local_binding env (Binding_typ_var (a)))) with
| (env, FStar_Util.Inl (x)) -> begin
(env, x)
end
| _62_759 -> begin
(FStar_All.failwith "impossible")
end))

let push_local_vbinding : env  ->  FStar_Absyn_Syntax.ident  ->  (env * FStar_Absyn_Syntax.bvvdef) = (fun env b -> (match ((push_local_binding env (Binding_var (b)))) with
| (env, FStar_Util.Inr (x)) -> begin
(env, x)
end
| _62_767 -> begin
(FStar_All.failwith "impossible")
end))

let push_rec_binding : env  ->  binding  ->  env = (fun env b -> (match (b) with
| (Binding_let (lid)) | (Binding_tycon (lid)) -> begin
if (unique false true env lid) then begin
(let _62_773 = env
in {curmodule = _62_773.curmodule; modules = _62_773.modules; open_namespaces = _62_773.open_namespaces; modul_abbrevs = _62_773.modul_abbrevs; sigaccum = _62_773.sigaccum; localbindings = _62_773.localbindings; recbindings = (b)::env.recbindings; phase = _62_773.phase; sigmap = _62_773.sigmap; default_result_effect = _62_773.default_result_effect; iface = _62_773.iface; admitted_iface = _62_773.admitted_iface})
end else begin
(Prims.raise (FStar_Absyn_Syntax.Error (((Prims.strcat "Duplicate top-level names " lid.FStar_Ident.str), (FStar_Ident.range_of_lid lid)))))
end
end
| _62_776 -> begin
(FStar_All.failwith "Unexpected rec_binding")
end))

let push_sigelt : env  ->  FStar_Absyn_Syntax.sigelt  ->  env = (fun env s -> (let err = (fun l -> (let sopt = (let _165_634 = (sigmap env)
in (FStar_Util.smap_try_find _165_634 l.FStar_Ident.str))
in (let r = (match (sopt) with
| Some (se, _62_784) -> begin
(match ((let _165_635 = (FStar_Absyn_Util.lids_of_sigelt se)
in (FStar_Util.find_opt (FStar_Ident.lid_equals l) _165_635))) with
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
in (let _165_638 = (let _165_637 = (let _165_636 = (FStar_Util.format2 "Duplicate top-level names [%s]; previously declared at %s" (FStar_Ident.text_of_lid l) r)
in (_165_636, (FStar_Ident.range_of_lid l)))
in FStar_Absyn_Syntax.Error (_165_637))
in (Prims.raise _165_638)))))
in (let env = (let _62_802 = (match (s) with
| FStar_Absyn_Syntax.Sig_let (_62_793) -> begin
(false, true)
end
| FStar_Absyn_Syntax.Sig_bundle (_62_796) -> begin
(true, true)
end
| _62_799 -> begin
(false, false)
end)
in (match (_62_802) with
| (any_val, exclude_if) -> begin
(let lids = (FStar_Absyn_Util.lids_of_sigelt s)
in (match ((FStar_Util.find_map lids (fun l -> if (not ((unique any_val exclude_if env l))) then begin
Some (l)
end else begin
None
end))) with
| None -> begin
(let _62_806 = (extract_record env s)
in (let _62_808 = env
in {curmodule = _62_808.curmodule; modules = _62_808.modules; open_namespaces = _62_808.open_namespaces; modul_abbrevs = _62_808.modul_abbrevs; sigaccum = (s)::env.sigaccum; localbindings = _62_808.localbindings; recbindings = _62_808.recbindings; phase = _62_808.phase; sigmap = _62_808.sigmap; default_result_effect = _62_808.default_result_effect; iface = _62_808.iface; admitted_iface = _62_808.admitted_iface}))
end
| Some (l) -> begin
(err l)
end))
end))
in (let _62_827 = (match (s) with
| FStar_Absyn_Syntax.Sig_bundle (ses, _62_815, _62_817, _62_819) -> begin
(let _165_642 = (FStar_List.map (fun se -> (let _165_641 = (FStar_Absyn_Util.lids_of_sigelt se)
in (_165_641, se))) ses)
in (env, _165_642))
end
| _62_824 -> begin
(let _165_645 = (let _165_644 = (let _165_643 = (FStar_Absyn_Util.lids_of_sigelt s)
in (_165_643, s))
in (_165_644)::[])
in (env, _165_645))
end)
in (match (_62_827) with
| (env, lss) -> begin
(let _62_832 = (FStar_All.pipe_right lss (FStar_List.iter (fun _62_830 -> (match (_62_830) with
| (lids, se) -> begin
(FStar_All.pipe_right lids (FStar_List.iter (fun lid -> (let _165_648 = (sigmap env)
in (FStar_Util.smap_add _165_648 lid.FStar_Ident.str (se, (env.iface && (not (env.admitted_iface)))))))))
end))))
in env)
end)))))

let push_namespace : env  ->  FStar_Absyn_Syntax.lident  ->  env = (fun env lid -> (let _62_836 = env
in {curmodule = _62_836.curmodule; modules = _62_836.modules; open_namespaces = (lid)::env.open_namespaces; modul_abbrevs = _62_836.modul_abbrevs; sigaccum = _62_836.sigaccum; localbindings = _62_836.localbindings; recbindings = _62_836.recbindings; phase = _62_836.phase; sigmap = _62_836.sigmap; default_result_effect = _62_836.default_result_effect; iface = _62_836.iface; admitted_iface = _62_836.admitted_iface}))

let push_module_abbrev : env  ->  FStar_Absyn_Syntax.ident  ->  FStar_Absyn_Syntax.lident  ->  env = (fun env x l -> if (FStar_All.pipe_right env.modul_abbrevs (FStar_Util.for_some (fun _62_844 -> (match (_62_844) with
| (y, _62_843) -> begin
(x.FStar_Ident.idText = y.FStar_Ident.idText)
end)))) then begin
(let _165_662 = (let _165_661 = (let _165_660 = (FStar_Util.format1 "Module %s is already defined" x.FStar_Ident.idText)
in (_165_660, x.FStar_Ident.idRange))
in FStar_Absyn_Syntax.Error (_165_661))
in (Prims.raise _165_662))
end else begin
(let _62_845 = env
in {curmodule = _62_845.curmodule; modules = _62_845.modules; open_namespaces = _62_845.open_namespaces; modul_abbrevs = ((x, l))::env.modul_abbrevs; sigaccum = _62_845.sigaccum; localbindings = _62_845.localbindings; recbindings = _62_845.recbindings; phase = _62_845.phase; sigmap = _62_845.sigmap; default_result_effect = _62_845.default_result_effect; iface = _62_845.iface; admitted_iface = _62_845.admitted_iface})
end)

let is_type_lid : env  ->  FStar_Absyn_Syntax.lident  ->  Prims.bool = (fun env lid -> (let aux = (fun _62_850 -> (match (()) with
| () -> begin
(match ((try_lookup_typ_name' false env lid)) with
| Some (_62_852) -> begin
true
end
| _62_855 -> begin
false
end)
end))
in if (lid.FStar_Ident.ns = []) then begin
(match ((try_lookup_id env lid.FStar_Ident.ident)) with
| Some (_62_857) -> begin
false
end
| _62_860 -> begin
(aux ())
end)
end else begin
(aux ())
end))

let check_admits : FStar_Absyn_Syntax.lident  ->  env  ->  Prims.unit = (fun nm env -> (let warn = (not ((let _165_674 = (FStar_ST.read FStar_Options.admit_fsi)
in (FStar_All.pipe_right _165_674 (FStar_Util.for_some (fun l -> (nm.FStar_Ident.str = l)))))))
in (FStar_All.pipe_right env.sigaccum (FStar_List.iter (fun se -> (match (se) with
| FStar_Absyn_Syntax.Sig_val_decl (l, t, quals, r) -> begin
(match ((try_lookup_lid env l)) with
| None -> begin
(let _62_873 = if warn then begin
(let _165_678 = (let _165_677 = (FStar_Range.string_of_range (FStar_Ident.range_of_lid l))
in (let _165_676 = (FStar_Absyn_Print.sli l)
in (FStar_Util.format2 "%s: Warning: Admitting %s without a definition\n" _165_677 _165_676)))
in (FStar_Util.print_string _165_678))
end else begin
()
end
in (let _165_679 = (sigmap env)
in (FStar_Util.smap_add _165_679 l.FStar_Ident.str (FStar_Absyn_Syntax.Sig_val_decl ((l, t, (FStar_Absyn_Syntax.Assumption)::quals, r)), false))))
end
| Some (_62_876) -> begin
()
end)
end
| _62_879 -> begin
()
end))))))

let finish : env  ->  FStar_Absyn_Syntax.modul  ->  env = (fun env modul -> (let _62_917 = (FStar_All.pipe_right modul.FStar_Absyn_Syntax.declarations (FStar_List.iter (fun _62_15 -> (match (_62_15) with
| FStar_Absyn_Syntax.Sig_bundle (ses, quals, _62_886, _62_888) -> begin
if (FStar_List.contains FStar_Absyn_Syntax.Private quals) then begin
(FStar_All.pipe_right ses (FStar_List.iter (fun _62_14 -> (match (_62_14) with
| FStar_Absyn_Syntax.Sig_datacon (lid, _62_894, _62_896, _62_898, _62_900, _62_902) -> begin
(let _165_686 = (sigmap env)
in (FStar_Util.smap_remove _165_686 lid.FStar_Ident.str))
end
| _62_906 -> begin
()
end))))
end else begin
()
end
end
| FStar_Absyn_Syntax.Sig_val_decl (lid, _62_909, quals, _62_912) -> begin
if (FStar_List.contains FStar_Absyn_Syntax.Private quals) then begin
(let _165_687 = (sigmap env)
in (FStar_Util.smap_remove _165_687 lid.FStar_Ident.str))
end else begin
()
end
end
| _62_916 -> begin
()
end))))
in (let _62_919 = env
in {curmodule = None; modules = ((modul.FStar_Absyn_Syntax.name, modul))::env.modules; open_namespaces = []; modul_abbrevs = []; sigaccum = []; localbindings = []; recbindings = []; phase = FStar_Parser_AST.Un; sigmap = _62_919.sigmap; default_result_effect = _62_919.default_result_effect; iface = _62_919.iface; admitted_iface = _62_919.admitted_iface})))

let push : env  ->  env = (fun env -> (let _62_922 = (push_record_cache ())
in (let _62_924 = env
in (let _165_692 = (let _165_691 = (let _165_690 = (sigmap env)
in (FStar_Util.smap_copy _165_690))
in (_165_691)::env.sigmap)
in {curmodule = _62_924.curmodule; modules = _62_924.modules; open_namespaces = _62_924.open_namespaces; modul_abbrevs = _62_924.modul_abbrevs; sigaccum = _62_924.sigaccum; localbindings = _62_924.localbindings; recbindings = _62_924.recbindings; phase = _62_924.phase; sigmap = _165_692; default_result_effect = _62_924.default_result_effect; iface = _62_924.iface; admitted_iface = _62_924.admitted_iface}))))

let mark : env  ->  env = (fun env -> (push env))

let reset_mark : env  ->  env = (fun env -> (let _62_928 = env
in (let _165_697 = (FStar_List.tl env.sigmap)
in {curmodule = _62_928.curmodule; modules = _62_928.modules; open_namespaces = _62_928.open_namespaces; modul_abbrevs = _62_928.modul_abbrevs; sigaccum = _62_928.sigaccum; localbindings = _62_928.localbindings; recbindings = _62_928.recbindings; phase = _62_928.phase; sigmap = _165_697; default_result_effect = _62_928.default_result_effect; iface = _62_928.iface; admitted_iface = _62_928.admitted_iface})))

let commit_mark : env  ->  env = (fun env -> (match (env.sigmap) with
| hd::_62_933::tl -> begin
(let _62_937 = env
in {curmodule = _62_937.curmodule; modules = _62_937.modules; open_namespaces = _62_937.open_namespaces; modul_abbrevs = _62_937.modul_abbrevs; sigaccum = _62_937.sigaccum; localbindings = _62_937.localbindings; recbindings = _62_937.recbindings; phase = _62_937.phase; sigmap = (hd)::tl; default_result_effect = _62_937.default_result_effect; iface = _62_937.iface; admitted_iface = _62_937.admitted_iface})
end
| _62_940 -> begin
(FStar_All.failwith "Impossible")
end))

let pop : env  ->  env = (fun env -> (match (env.sigmap) with
| _62_944::maps -> begin
(let _62_946 = (pop_record_cache ())
in (let _62_948 = env
in {curmodule = _62_948.curmodule; modules = _62_948.modules; open_namespaces = _62_948.open_namespaces; modul_abbrevs = _62_948.modul_abbrevs; sigaccum = _62_948.sigaccum; localbindings = _62_948.localbindings; recbindings = _62_948.recbindings; phase = _62_948.phase; sigmap = maps; default_result_effect = _62_948.default_result_effect; iface = _62_948.iface; admitted_iface = _62_948.admitted_iface}))
end
| _62_951 -> begin
(FStar_All.failwith "No more modules to pop")
end))

let export_interface : FStar_Absyn_Syntax.lident  ->  env  ->  env = (fun m env -> (let sigelt_in_m = (fun se -> (match ((FStar_Absyn_Util.lids_of_sigelt se)) with
| l::_62_957 -> begin
(l.FStar_Ident.nsstr = m.FStar_Ident.str)
end
| _62_961 -> begin
false
end))
in (let sm = (sigmap env)
in (let env = (pop env)
in (let keys = (FStar_Util.smap_keys sm)
in (let sm' = (sigmap env)
in (let _62_984 = (FStar_All.pipe_right keys (FStar_List.iter (fun k -> (match ((FStar_Util.smap_try_find sm' k)) with
| Some (se, true) when (sigelt_in_m se) -> begin
(let _62_971 = (FStar_Util.smap_remove sm' k)
in (let se = (match (se) with
| FStar_Absyn_Syntax.Sig_val_decl (l, t, q, r) -> begin
FStar_Absyn_Syntax.Sig_val_decl ((l, t, (FStar_Absyn_Syntax.Assumption)::q, r))
end
| _62_980 -> begin
se
end)
in (FStar_Util.smap_add sm' k (se, false))))
end
| _62_983 -> begin
()
end))))
in env)))))))

let finish_module_or_interface : env  ->  FStar_Absyn_Syntax.modul  ->  env = (fun env modul -> (let _62_988 = if (not (modul.FStar_Absyn_Syntax.is_interface)) then begin
(check_admits modul.FStar_Absyn_Syntax.name env)
end else begin
()
end
in (finish env modul)))

let prepare_module_or_interface : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Absyn_Syntax.lident  ->  (env * Prims.bool) = (fun intf admitted env mname -> (let prep = (fun env -> (let open_ns = if (FStar_Ident.lid_equals mname FStar_Absyn_Const.prims_lid) then begin
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
in (let _62_997 = env
in {curmodule = Some (mname); modules = _62_997.modules; open_namespaces = open_ns; modul_abbrevs = _62_997.modul_abbrevs; sigaccum = _62_997.sigaccum; localbindings = _62_997.localbindings; recbindings = _62_997.recbindings; phase = _62_997.phase; sigmap = env.sigmap; default_result_effect = _62_997.default_result_effect; iface = intf; admitted_iface = admitted})))
in (match ((FStar_All.pipe_right env.modules (FStar_Util.find_opt (fun _62_1002 -> (match (_62_1002) with
| (l, _62_1001) -> begin
(FStar_Ident.lid_equals l mname)
end))))) with
| None -> begin
((prep env), false)
end
| Some (_62_1005, m) -> begin
(let _62_1009 = if ((not (m.FStar_Absyn_Syntax.is_interface)) || intf) then begin
(let _165_726 = (let _165_725 = (let _165_724 = (FStar_Util.format1 "Duplicate module or interface name: %s" mname.FStar_Ident.str)
in (_165_724, (FStar_Ident.range_of_lid mname)))
in FStar_Absyn_Syntax.Error (_165_725))
in (Prims.raise _165_726))
end else begin
()
end
in (let _165_728 = (let _165_727 = (push env)
in (prep _165_727))
in (_165_728, true)))
end)))

let enter_monad_scope : env  ->  FStar_Absyn_Syntax.ident  ->  env = (fun env mname -> (let curmod = (current_module env)
in (let mscope = (FStar_Ident.lid_of_ids (FStar_List.append curmod.FStar_Ident.ns ((curmod.FStar_Ident.ident)::(mname)::[])))
in (let _62_1015 = env
in {curmodule = Some (mscope); modules = _62_1015.modules; open_namespaces = (curmod)::env.open_namespaces; modul_abbrevs = _62_1015.modul_abbrevs; sigaccum = _62_1015.sigaccum; localbindings = _62_1015.localbindings; recbindings = _62_1015.recbindings; phase = _62_1015.phase; sigmap = _62_1015.sigmap; default_result_effect = _62_1015.default_result_effect; iface = _62_1015.iface; admitted_iface = _62_1015.admitted_iface}))))

let exit_monad_scope : env  ->  env  ->  env = (fun env0 env -> (let _62_1019 = env
in {curmodule = env0.curmodule; modules = _62_1019.modules; open_namespaces = env0.open_namespaces; modul_abbrevs = _62_1019.modul_abbrevs; sigaccum = _62_1019.sigaccum; localbindings = _62_1019.localbindings; recbindings = _62_1019.recbindings; phase = _62_1019.phase; sigmap = _62_1019.sigmap; default_result_effect = _62_1019.default_result_effect; iface = _62_1019.iface; admitted_iface = _62_1019.admitted_iface}))

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
(let _165_743 = (FStar_Range.string_of_range r)
in (FStar_Util.format1 "(Possible clash with related name at %s)" _165_743))
end)
in (let _165_746 = (let _165_745 = (let _165_744 = (FStar_Util.format2 "Identifier not found: [%s] %s" (FStar_Ident.text_of_lid lid) msg)
in (_165_744, (FStar_Ident.range_of_lid lid)))
in FStar_Absyn_Syntax.Error (_165_745))
in (Prims.raise _165_746))))
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




