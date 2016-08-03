
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
| Binding_typ_var (_60_18) -> begin
_60_18
end))


let ___Binding_var____0 = (fun projectee -> (match (projectee) with
| Binding_var (_60_21) -> begin
_60_21
end))


let ___Binding_let____0 = (fun projectee -> (match (projectee) with
| Binding_let (_60_24) -> begin
_60_24
end))


let ___Binding_tycon____0 = (fun projectee -> (match (projectee) with
| Binding_tycon (_60_27) -> begin
_60_27
end))


type kind_abbrev =
(FStar_Ident.lident * (FStar_Absyn_Syntax.btvdef, FStar_Absyn_Syntax.bvvdef) FStar_Util.either Prims.list * FStar_Absyn_Syntax.knd)


type env =
{curmodule : FStar_Ident.lident Prims.option; modules : (FStar_Ident.lident * FStar_Absyn_Syntax.modul) Prims.list; open_namespaces : FStar_Ident.lident Prims.list; modul_abbrevs : (FStar_Ident.ident * FStar_Ident.lident) Prims.list; sigaccum : FStar_Absyn_Syntax.sigelts; localbindings : ((FStar_Absyn_Syntax.btvdef, FStar_Absyn_Syntax.bvvdef) FStar_Util.either * binding) Prims.list; recbindings : binding Prims.list; phase : FStar_Parser_AST.level; sigmap : (FStar_Absyn_Syntax.sigelt * Prims.bool) FStar_Util.smap Prims.list; default_result_effect : FStar_Absyn_Syntax.typ  ->  FStar_Range.range  ->  FStar_Absyn_Syntax.comp; iface : Prims.bool; admitted_iface : Prims.bool}


let is_Mkenv : env  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv"))))


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
| OSig (_60_43) -> begin
_60_43
end))


let ___OLet____0 = (fun projectee -> (match (projectee) with
| OLet (_60_46) -> begin
_60_46
end))


let ___ORec____0 = (fun projectee -> (match (projectee) with
| ORec (_60_49) -> begin
_60_49
end))


let range_of_occurrence : occurrence  ->  FStar_Range.range = (fun _60_1 -> (match (_60_1) with
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
| Exp_name (_60_58) -> begin
_60_58
end))


let ___Typ_name____0 = (fun projectee -> (match (projectee) with
| Typ_name (_60_61) -> begin
_60_61
end))


let ___Eff_name____0 = (fun projectee -> (match (projectee) with
| Eff_name (_60_64) -> begin
_60_64
end))


let ___Knd_name____0 = (fun projectee -> (match (projectee) with
| Knd_name (_60_67) -> begin
_60_67
end))


type record_or_dc =
{typename : FStar_Ident.lident; constrname : FStar_Ident.lident; parms : FStar_Absyn_Syntax.binders; fields : (FStar_Absyn_Syntax.fieldname * FStar_Absyn_Syntax.typ) Prims.list; is_record : Prims.bool}


let is_Mkrecord_or_dc : record_or_dc  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkrecord_or_dc"))))


let open_modules : env  ->  (FStar_Ident.lident * FStar_Absyn_Syntax.modul) Prims.list = (fun e -> e.modules)


let current_module : env  ->  FStar_Ident.lident = (fun env -> (match (env.curmodule) with
| None -> begin
(FStar_All.failwith "Unset current module")
end
| Some (m) -> begin
m
end))


let qual : FStar_Ident.lident  ->  FStar_Ident.ident  ->  FStar_Ident.lident = (fun lid id -> (let _152_230 = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns ((lid.FStar_Ident.ident)::(id)::[])))
in (FStar_Ident.set_lid_range _152_230 id.FStar_Ident.idRange)))


let qualify : env  ->  FStar_Ident.ident  ->  FStar_Ident.lident = (fun env id -> (let _152_235 = (current_module env)
in (qual _152_235 id)))


let qualify_lid : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (

let cur = (current_module env)
in (let _152_240 = (FStar_Ident.lid_of_ids (FStar_List.append cur.FStar_Ident.ns (FStar_List.append ((cur.FStar_Ident.ident)::[]) (FStar_List.append lid.FStar_Ident.ns ((lid.FStar_Ident.ident)::[])))))
in (FStar_Ident.set_lid_range _152_240 (FStar_Ident.range_of_lid lid)))))


let new_sigmap = (fun _60_89 -> (match (()) with
| () -> begin
(FStar_Util.smap_create 100)
end))


let empty_env : Prims.unit  ->  env = (fun _60_90 -> (match (()) with
| () -> begin
(let _152_245 = (let _152_244 = (new_sigmap ())
in (_152_244)::[])
in {curmodule = None; modules = []; open_namespaces = []; modul_abbrevs = []; sigaccum = []; localbindings = []; recbindings = []; phase = FStar_Parser_AST.Un; sigmap = _152_245; default_result_effect = FStar_Absyn_Util.ml_comp; iface = false; admitted_iface = false})
end))


let sigmap : env  ->  (FStar_Absyn_Syntax.sigelt * Prims.bool) FStar_Util.smap = (fun env -> (FStar_List.hd env.sigmap))


let default_total : env  ->  env = (fun env -> (

let _60_93 = env
in {curmodule = _60_93.curmodule; modules = _60_93.modules; open_namespaces = _60_93.open_namespaces; modul_abbrevs = _60_93.modul_abbrevs; sigaccum = _60_93.sigaccum; localbindings = _60_93.localbindings; recbindings = _60_93.recbindings; phase = _60_93.phase; sigmap = _60_93.sigmap; default_result_effect = (fun t _60_96 -> (FStar_Absyn_Syntax.mk_Total t)); iface = _60_93.iface; admitted_iface = _60_93.admitted_iface}))


let default_ml : env  ->  env = (fun env -> (

let _60_99 = env
in {curmodule = _60_99.curmodule; modules = _60_99.modules; open_namespaces = _60_99.open_namespaces; modul_abbrevs = _60_99.modul_abbrevs; sigaccum = _60_99.sigaccum; localbindings = _60_99.localbindings; recbindings = _60_99.recbindings; phase = _60_99.phase; sigmap = _60_99.sigmap; default_result_effect = FStar_Absyn_Util.ml_comp; iface = _60_99.iface; admitted_iface = _60_99.admitted_iface}))


let range_of_binding : binding  ->  FStar_Range.range = (fun _60_2 -> (match (_60_2) with
| (Binding_typ_var (id)) | (Binding_var (id)) -> begin
id.FStar_Ident.idRange
end
| (Binding_let (lid)) | (Binding_tycon (lid)) -> begin
(FStar_Ident.range_of_lid lid)
end))


let try_lookup_typ_var : env  ->  FStar_Ident.ident  ->  FStar_Absyn_Syntax.typ Prims.option = (fun env id -> (

let fopt = (FStar_List.tryFind (fun _60_113 -> (match (_60_113) with
| (_60_111, b) -> begin
(match (b) with
| (Binding_typ_var (id')) | (Binding_var (id')) -> begin
(id.FStar_Ident.idText = id'.FStar_Ident.idText)
end
| _60_118 -> begin
false
end)
end)) env.localbindings)
in (match (fopt) with
| Some (FStar_Util.Inl (bvd), Binding_typ_var (_60_123)) -> begin
(let _152_261 = (FStar_Absyn_Util.bvd_to_typ (FStar_Absyn_Util.set_bvd_range bvd id.FStar_Ident.idRange) FStar_Absyn_Syntax.kun)
in Some (_152_261))
end
| _60_128 -> begin
None
end)))


let resolve_in_open_namespaces' = (fun env lid finder -> (

let aux = (fun namespaces -> (match ((finder lid)) with
| Some (r) -> begin
Some (r)
end
| _60_138 -> begin
(

let ids = (FStar_Ident.ids_of_lid lid)
in (FStar_Util.find_map namespaces (fun ns -> (

let full_name = (FStar_Ident.lid_of_ids (FStar_List.append (FStar_Ident.ids_of_lid ns) ids))
in (finder full_name)))))
end))
in (let _152_272 = (let _152_271 = (current_module env)
in (_152_271)::env.open_namespaces)
in (aux _152_272))))


let expand_module_abbrevs : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (match (lid.FStar_Ident.ns) with
| (id)::[] -> begin
(match ((FStar_All.pipe_right env.modul_abbrevs (FStar_List.tryFind (fun _60_149 -> (match (_60_149) with
| (id', _60_148) -> begin
(id.FStar_Ident.idText = id'.FStar_Ident.idText)
end))))) with
| None -> begin
lid
end
| Some (_60_152, lid') -> begin
(FStar_Ident.lid_of_ids (FStar_List.append (FStar_Ident.ids_of_lid lid') ((lid.FStar_Ident.ident)::[])))
end)
end
| _60_157 -> begin
lid
end))


let resolve_in_open_namespaces = (fun env lid finder -> (let _152_288 = (expand_module_abbrevs env lid)
in (resolve_in_open_namespaces' env _152_288 finder)))


let unmangleMap : (Prims.string * Prims.string) Prims.list = ((("op_ColonColon"), ("Cons")))::((("not"), ("op_Negation")))::[]


let unmangleOpName : FStar_Ident.ident  ->  FStar_Ident.lident Prims.option = (fun id -> (FStar_Util.find_map unmangleMap (fun _60_165 -> (match (_60_165) with
| (x, y) -> begin
if (id.FStar_Ident.idText = x) then begin
(let _152_292 = (FStar_Ident.lid_of_path (("Prims")::(y)::[]) id.FStar_Ident.idRange)
in Some (_152_292))
end else begin
None
end
end))))


let try_lookup_id' : env  ->  FStar_Ident.ident  ->  (FStar_Ident.lident * FStar_Absyn_Syntax.exp) Prims.option = (fun env id -> (match ((unmangleOpName id)) with
| Some (l) -> begin
(let _152_298 = (let _152_297 = (FStar_Absyn_Syntax.mk_Exp_fvar (((FStar_Absyn_Util.fv l)), (None)) None id.FStar_Ident.idRange)
in ((l), (_152_297)))
in Some (_152_298))
end
| _60_171 -> begin
(

let found = (FStar_Util.find_map env.localbindings (fun _60_3 -> (match (_60_3) with
| (FStar_Util.Inl (_60_174), Binding_typ_var (id')) when (id'.FStar_Ident.idText = id.FStar_Ident.idText) -> begin
Some (FStar_Util.Inl (()))
end
| (FStar_Util.Inr (bvd), Binding_var (id')) when (id'.FStar_Ident.idText = id.FStar_Ident.idText) -> begin
(let _152_303 = (let _152_302 = (let _152_301 = (FStar_Ident.lid_of_ids ((id')::[]))
in (let _152_300 = (FStar_Absyn_Util.bvd_to_exp (FStar_Absyn_Util.set_bvd_range bvd id.FStar_Ident.idRange) FStar_Absyn_Syntax.tun)
in ((_152_301), (_152_300))))
in FStar_Util.Inr (_152_302))
in Some (_152_303))
end
| _60_185 -> begin
None
end)))
in (match (found) with
| Some (FStar_Util.Inr (x)) -> begin
Some (x)
end
| _60_191 -> begin
None
end))
end))


let try_lookup_id : env  ->  FStar_Ident.ident  ->  FStar_Absyn_Syntax.exp Prims.option = (fun env id -> (match ((try_lookup_id' env id)) with
| Some (_60_195, e) -> begin
Some (e)
end
| None -> begin
None
end))


let fv_qual_of_se : FStar_Absyn_Syntax.sigelt  ->  FStar_Absyn_Syntax.fv_qual Prims.option = (fun _60_5 -> (match (_60_5) with
| FStar_Absyn_Syntax.Sig_datacon (_60_202, _60_204, (l, _60_207, _60_209), quals, _60_213, _60_215) -> begin
(

let qopt = (FStar_Util.find_map quals (fun _60_4 -> (match (_60_4) with
| FStar_Absyn_Syntax.RecordConstructor (fs) -> begin
Some (FStar_Absyn_Syntax.Record_ctor (((l), (fs))))
end
| _60_222 -> begin
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
| FStar_Absyn_Syntax.Sig_val_decl (_60_227, _60_229, quals, _60_232) -> begin
None
end
| _60_236 -> begin
None
end))


let try_lookup_name : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  foundname Prims.option = (fun any_val exclude_interf env lid -> (

let find_in_sig = (fun lid -> (match ((let _152_321 = (sigmap env)
in (FStar_Util.smap_try_find _152_321 lid.FStar_Ident.str))) with
| Some (_60_244, true) when exclude_interf -> begin
None
end
| None -> begin
None
end
| Some (se, _60_251) -> begin
(match (se) with
| (FStar_Absyn_Syntax.Sig_typ_abbrev (_)) | (FStar_Absyn_Syntax.Sig_tycon (_)) -> begin
(let _152_324 = (let _152_323 = (let _152_322 = (FStar_Absyn_Util.ftv lid FStar_Absyn_Syntax.kun)
in ((OSig (se)), (_152_322)))
in Typ_name (_152_323))
in Some (_152_324))
end
| FStar_Absyn_Syntax.Sig_kind_abbrev (_60_261) -> begin
Some (Knd_name (((OSig (se)), (lid))))
end
| FStar_Absyn_Syntax.Sig_new_effect (ne, _60_265) -> begin
(let _152_327 = (let _152_326 = (let _152_325 = (FStar_Ident.set_lid_range ne.FStar_Absyn_Syntax.mname (FStar_Ident.range_of_lid lid))
in ((OSig (se)), (_152_325)))
in Eff_name (_152_326))
in Some (_152_327))
end
| FStar_Absyn_Syntax.Sig_effect_abbrev (_60_269) -> begin
Some (Eff_name (((OSig (se)), (lid))))
end
| FStar_Absyn_Syntax.Sig_datacon (_60_272) -> begin
(let _152_331 = (let _152_330 = (let _152_329 = (let _152_328 = (fv_qual_of_se se)
in (FStar_Absyn_Util.fvar _152_328 lid (FStar_Ident.range_of_lid lid)))
in ((OSig (se)), (_152_329)))
in Exp_name (_152_330))
in Some (_152_331))
end
| FStar_Absyn_Syntax.Sig_let (_60_275) -> begin
(let _152_334 = (let _152_333 = (let _152_332 = (FStar_Absyn_Util.fvar None lid (FStar_Ident.range_of_lid lid))
in ((OSig (se)), (_152_332)))
in Exp_name (_152_333))
in Some (_152_334))
end
| FStar_Absyn_Syntax.Sig_val_decl (_60_278, _60_280, quals, _60_283) -> begin
if (any_val || (FStar_All.pipe_right quals (FStar_Util.for_some (fun _60_6 -> (match (_60_6) with
| FStar_Absyn_Syntax.Assumption -> begin
true
end
| _60_289 -> begin
false
end))))) then begin
(let _152_339 = (let _152_338 = (let _152_337 = (let _152_336 = (fv_qual_of_se se)
in (FStar_Absyn_Util.fvar _152_336 lid (FStar_Ident.range_of_lid lid)))
in ((OSig (se)), (_152_337)))
in Exp_name (_152_338))
in Some (_152_339))
end else begin
None
end
end
| _60_291 -> begin
None
end)
end))
in (

let found_id = (match (lid.FStar_Ident.ns) with
| [] -> begin
(match ((try_lookup_id' env lid.FStar_Ident.ident)) with
| Some (lid, e) -> begin
Some (Exp_name (((OLet (lid)), (e))))
end
| None -> begin
(

let recname = (qualify env lid.FStar_Ident.ident)
in (FStar_Util.find_map env.recbindings (fun _60_7 -> (match (_60_7) with
| Binding_let (l) when (FStar_Ident.lid_equals l recname) -> begin
(let _152_343 = (let _152_342 = (let _152_341 = (FStar_Absyn_Util.fvar None recname (FStar_Ident.range_of_lid recname))
in ((ORec (l)), (_152_341)))
in Exp_name (_152_342))
in Some (_152_343))
end
| Binding_tycon (l) when (FStar_Ident.lid_equals l recname) -> begin
(let _152_346 = (let _152_345 = (let _152_344 = (FStar_Absyn_Util.ftv recname FStar_Absyn_Syntax.kun)
in ((ORec (l)), (_152_344)))
in Typ_name (_152_345))
in Some (_152_346))
end
| _60_305 -> begin
None
end))))
end)
end
| _60_307 -> begin
None
end)
in (match (found_id) with
| Some (_60_310) -> begin
found_id
end
| _60_313 -> begin
(resolve_in_open_namespaces env lid find_in_sig)
end))))


let try_lookup_typ_name' : Prims.bool  ->  env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.typ Prims.option = (fun exclude_interf env lid -> (match ((try_lookup_name true exclude_interf env lid)) with
| Some (Typ_name (_60_318, t)) -> begin
Some (t)
end
| Some (Eff_name (_60_324, l)) -> begin
(let _152_353 = (FStar_Absyn_Util.ftv l FStar_Absyn_Syntax.mk_Kind_unknown)
in Some (_152_353))
end
| _60_330 -> begin
None
end))


let try_lookup_typ_name : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.typ Prims.option = (fun env l -> (try_lookup_typ_name' (not (env.iface)) env l))


let try_lookup_effect_name' : Prims.bool  ->  env  ->  FStar_Ident.lident  ->  (occurrence * FStar_Ident.lident) Prims.option = (fun exclude_interf env lid -> (match ((try_lookup_name true exclude_interf env lid)) with
| Some (Eff_name (o, l)) -> begin
Some (((o), (l)))
end
| _60_342 -> begin
None
end))


let try_lookup_effect_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env l -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some (o, l) -> begin
Some (l)
end
| _60_350 -> begin
None
end))


let try_lookup_effect_defn : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.eff_decl Prims.option = (fun env l -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some (OSig (FStar_Absyn_Syntax.Sig_new_effect (ne, _60_355)), _60_360) -> begin
Some (ne)
end
| _60_364 -> begin
None
end))


let is_effect_name : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((try_lookup_effect_name env lid)) with
| None -> begin
false
end
| Some (_60_369) -> begin
true
end))


let try_resolve_typ_abbrev : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.typ Prims.option = (fun env lid -> (

let find_in_sig = (fun lid -> (match ((let _152_382 = (sigmap env)
in (FStar_Util.smap_try_find _152_382 lid.FStar_Ident.str))) with
| Some (FStar_Absyn_Syntax.Sig_typ_abbrev (lid, tps, k, def, _60_380, _60_382), _60_386) -> begin
(

let t = (let _152_385 = (let _152_384 = (let _152_383 = (FStar_Absyn_Util.close_with_lam tps def)
in ((_152_383), (lid)))
in FStar_Absyn_Syntax.Meta_named (_152_384))
in (FStar_Absyn_Syntax.mk_Typ_meta _152_385))
in Some (t))
end
| _60_391 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))


let lookup_letbinding_quals : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.qualifier Prims.list = (fun env lid -> (

let find_in_sig = (fun lid -> (match ((let _152_392 = (sigmap env)
in (FStar_Util.smap_try_find _152_392 lid.FStar_Ident.str))) with
| Some (FStar_Absyn_Syntax.Sig_val_decl (lid, _60_398, quals, _60_401), _60_405) -> begin
Some (quals)
end
| _60_409 -> begin
None
end))
in (match ((resolve_in_open_namespaces env lid find_in_sig)) with
| Some (quals) -> begin
quals
end
| _60_413 -> begin
[]
end)))


let try_lookup_module : env  ->  Prims.string Prims.list  ->  FStar_Absyn_Syntax.modul Prims.option = (fun env path -> (match ((FStar_List.tryFind (fun _60_418 -> (match (_60_418) with
| (mlid, modul) -> begin
((FStar_Ident.path_of_lid mlid) = path)
end)) env.modules)) with
| Some (_60_420, modul) -> begin
Some (modul)
end
| None -> begin
None
end))


let try_lookup_let : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.exp Prims.option = (fun env lid -> (

let find_in_sig = (fun lid -> (match ((let _152_404 = (sigmap env)
in (FStar_Util.smap_try_find _152_404 lid.FStar_Ident.str))) with
| Some (FStar_Absyn_Syntax.Sig_let (_60_430), _60_433) -> begin
(let _152_405 = (FStar_Absyn_Util.fvar None lid (FStar_Ident.range_of_lid lid))
in Some (_152_405))
end
| _60_437 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))


let try_lookup_lid' : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.exp Prims.option = (fun any_val exclude_interf env lid -> (match ((try_lookup_name any_val exclude_interf env lid)) with
| Some (Exp_name (_60_443, e)) -> begin
Some (e)
end
| _60_449 -> begin
None
end))


let try_lookup_lid : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.exp Prims.option = (fun env l -> (try_lookup_lid' env.iface false env l))


let try_lookup_datacon : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.typ FStar_Absyn_Syntax.var Prims.option = (fun env lid -> (

let find_in_sig = (fun lid -> (match ((let _152_424 = (sigmap env)
in (FStar_Util.smap_try_find _152_424 lid.FStar_Ident.str))) with
| Some (FStar_Absyn_Syntax.Sig_val_decl (_60_457, _60_459, quals, _60_462), _60_466) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _60_8 -> (match (_60_8) with
| FStar_Absyn_Syntax.Assumption -> begin
true
end
| _60_472 -> begin
false
end)))) then begin
Some ((FStar_Absyn_Util.fv lid))
end else begin
None
end
end
| Some (FStar_Absyn_Syntax.Sig_datacon (_60_474), _60_477) -> begin
Some ((FStar_Absyn_Util.fv lid))
end
| _60_481 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))


let find_all_datacons : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.list Prims.option = (fun env lid -> (

let find_in_sig = (fun lid -> (match ((let _152_432 = (sigmap env)
in (FStar_Util.smap_try_find _152_432 lid.FStar_Ident.str))) with
| Some (FStar_Absyn_Syntax.Sig_tycon (_60_487, _60_489, _60_491, _60_493, datas, _60_496, _60_498), _60_502) -> begin
Some (datas)
end
| _60_506 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))


let record_cache_aux : ((Prims.unit  ->  Prims.unit) * (Prims.unit  ->  Prims.unit) * (Prims.unit  ->  record_or_dc Prims.list) * (record_or_dc  ->  Prims.unit)) = (

let record_cache = (FStar_Util.mk_ref (([])::[]))
in (

let push = (fun _60_509 -> (match (()) with
| () -> begin
(let _152_446 = (let _152_445 = (let _152_443 = (FStar_ST.read record_cache)
in (FStar_List.hd _152_443))
in (let _152_444 = (FStar_ST.read record_cache)
in (_152_445)::_152_444))
in (FStar_ST.op_Colon_Equals record_cache _152_446))
end))
in (

let pop = (fun _60_511 -> (match (()) with
| () -> begin
(let _152_450 = (let _152_449 = (FStar_ST.read record_cache)
in (FStar_List.tl _152_449))
in (FStar_ST.op_Colon_Equals record_cache _152_450))
end))
in (

let peek = (fun _60_513 -> (match (()) with
| () -> begin
(let _152_453 = (FStar_ST.read record_cache)
in (FStar_List.hd _152_453))
end))
in (

let insert = (fun r -> (let _152_460 = (let _152_459 = (let _152_456 = (peek ())
in (r)::_152_456)
in (let _152_458 = (let _152_457 = (FStar_ST.read record_cache)
in (FStar_List.tl _152_457))
in (_152_459)::_152_458))
in (FStar_ST.op_Colon_Equals record_cache _152_460)))
in ((push), (pop), (peek), (insert)))))))


let push_record_cache : Prims.unit  ->  Prims.unit = (

let _60_523 = record_cache_aux
in (match (_60_523) with
| (push, _60_518, _60_520, _60_522) -> begin
push
end))


let pop_record_cache : Prims.unit  ->  Prims.unit = (

let _60_531 = record_cache_aux
in (match (_60_531) with
| (_60_525, pop, _60_528, _60_530) -> begin
pop
end))


let peek_record_cache : Prims.unit  ->  record_or_dc Prims.list = (

let _60_539 = record_cache_aux
in (match (_60_539) with
| (_60_533, _60_535, peek, _60_538) -> begin
peek
end))


let insert_record_cache : record_or_dc  ->  Prims.unit = (

let _60_547 = record_cache_aux
in (match (_60_547) with
| (_60_541, _60_543, _60_545, insert) -> begin
insert
end))


let extract_record : env  ->  FStar_Absyn_Syntax.sigelt  ->  Prims.unit = (fun e _60_12 -> (match (_60_12) with
| FStar_Absyn_Syntax.Sig_bundle (sigs, _60_552, _60_554, _60_556) -> begin
(

let is_rec = (FStar_Util.for_some (fun _60_9 -> (match (_60_9) with
| (FStar_Absyn_Syntax.RecordType (_)) | (FStar_Absyn_Syntax.RecordConstructor (_)) -> begin
true
end
| _60_567 -> begin
false
end)))
in (

let find_dc = (fun dc -> (FStar_All.pipe_right sigs (FStar_Util.find_opt (fun _60_10 -> (match (_60_10) with
| FStar_Absyn_Syntax.Sig_datacon (lid, _60_574, _60_576, _60_578, _60_580, _60_582) -> begin
(FStar_Ident.lid_equals dc lid)
end
| _60_586 -> begin
false
end)))))
in (FStar_All.pipe_right sigs (FStar_List.iter (fun _60_11 -> (match (_60_11) with
| FStar_Absyn_Syntax.Sig_tycon (typename, parms, _60_591, _60_593, (dc)::[], tags, _60_598) -> begin
(match ((let _152_531 = (find_dc dc)
in (FStar_All.pipe_left FStar_Util.must _152_531))) with
| FStar_Absyn_Syntax.Sig_datacon (constrname, t, _60_604, _60_606, _60_608, _60_610) -> begin
(

let formals = (match ((FStar_Absyn_Util.function_formals t)) with
| Some (x, _60_615) -> begin
x
end
| _60_619 -> begin
[]
end)
in (

let is_rec = (is_rec tags)
in (

let fields = (FStar_All.pipe_right formals (FStar_List.collect (fun b -> (match (b) with
| (FStar_Util.Inr (x), q) -> begin
if ((FStar_Absyn_Syntax.is_null_binder b) || (is_rec && (match (q) with
| Some (FStar_Absyn_Syntax.Implicit (_60_628)) -> begin
true
end
| _60_632 -> begin
false
end))) then begin
[]
end else begin
(let _152_535 = (let _152_534 = (let _152_533 = if is_rec then begin
(FStar_Absyn_Util.unmangle_field_name x.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ppname)
end else begin
x.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ppname
end
in (qual constrname _152_533))
in ((_152_534), (x.FStar_Absyn_Syntax.sort)))
in (_152_535)::[])
end
end
| _60_634 -> begin
[]
end))))
in (

let record = {typename = typename; constrname = constrname; parms = parms; fields = fields; is_record = is_rec}
in (insert_record_cache record)))))
end
| _60_638 -> begin
()
end)
end
| _60_640 -> begin
()
end))))))
end
| _60_642 -> begin
()
end))


let try_lookup_record_or_dc_by_field_name : env  ->  FStar_Ident.lident  ->  (record_or_dc * FStar_Ident.lident) Prims.option = (fun env fieldname -> (

let maybe_add_constrname = (fun ns c -> (

let rec aux = (fun ns -> (match (ns) with
| [] -> begin
(c)::[]
end
| (c')::[] -> begin
if (c'.FStar_Ident.idText = c.FStar_Ident.idText) then begin
(c)::[]
end else begin
(c')::(c)::[]
end
end
| (hd)::tl -> begin
(let _152_546 = (aux tl)
in (hd)::_152_546)
end))
in (aux ns)))
in (

let find_in_cache = (fun fieldname -> (

let _60_660 = ((fieldname.FStar_Ident.ns), (fieldname.FStar_Ident.ident))
in (match (_60_660) with
| (ns, fieldname) -> begin
(let _152_551 = (peek_record_cache ())
in (FStar_Util.find_map _152_551 (fun record -> (

let constrname = record.constrname.FStar_Ident.ident
in (

let ns = (maybe_add_constrname ns constrname)
in (

let fname = (FStar_Ident.lid_of_ids (FStar_List.append ns ((fieldname)::[])))
in (FStar_Util.find_map record.fields (fun _60_668 -> (match (_60_668) with
| (f, _60_667) -> begin
if (FStar_Ident.lid_equals fname f) then begin
Some (((record), (fname)))
end else begin
None
end
end)))))))))
end)))
in (resolve_in_open_namespaces env fieldname find_in_cache))))


let try_lookup_record_by_field_name : env  ->  FStar_Ident.lident  ->  (record_or_dc * FStar_Ident.lident) Prims.option = (fun env fieldname -> (match ((try_lookup_record_or_dc_by_field_name env fieldname)) with
| Some (r, f) when r.is_record -> begin
Some (((r), (f)))
end
| _60_676 -> begin
None
end))


let try_lookup_projector_by_field_name : env  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * Prims.bool) Prims.option = (fun env fieldname -> (match ((try_lookup_record_or_dc_by_field_name env fieldname)) with
| Some (r, f) -> begin
Some (((f), (r.is_record)))
end
| _60_684 -> begin
None
end))


let qualify_field_to_record : env  ->  record_or_dc  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env recd f -> (

let qualify = (fun fieldname -> (

let _60_692 = ((fieldname.FStar_Ident.ns), (fieldname.FStar_Ident.ident))
in (match (_60_692) with
| (ns, fieldname) -> begin
(

let constrname = recd.constrname.FStar_Ident.ident
in (

let fname = (FStar_Ident.lid_of_ids (FStar_List.append ns (FStar_List.append ((constrname)::[]) ((fieldname)::[]))))
in (FStar_Util.find_map recd.fields (fun _60_698 -> (match (_60_698) with
| (f, _60_697) -> begin
if (FStar_Ident.lid_equals fname f) then begin
Some (fname)
end else begin
None
end
end)))))
end)))
in (resolve_in_open_namespaces env f qualify)))


let find_kind_abbrev : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env l -> (match ((try_lookup_name true (not (env.iface)) env l)) with
| Some (Knd_name (_60_702, l)) -> begin
Some (l)
end
| _60_708 -> begin
None
end))


let is_kind_abbrev : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (match ((find_kind_abbrev env l)) with
| None -> begin
false
end
| Some (_60_713) -> begin
true
end))


let unique_name : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  Prims.bool = (fun any_val exclude_if env lid -> (match ((try_lookup_lid' any_val exclude_if env lid)) with
| None -> begin
(match ((find_kind_abbrev env lid)) with
| None -> begin
true
end
| Some (_60_722) -> begin
false
end)
end
| Some (_60_725) -> begin
false
end))


let unique_typ_name : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((try_lookup_typ_name' true env lid)) with
| None -> begin
true
end
| Some (a) -> begin
false
end))


let unique : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  Prims.bool = (fun any_val exclude_if env lid -> (

let this_env = (

let _60_736 = env
in {curmodule = _60_736.curmodule; modules = _60_736.modules; open_namespaces = []; modul_abbrevs = _60_736.modul_abbrevs; sigaccum = _60_736.sigaccum; localbindings = _60_736.localbindings; recbindings = _60_736.recbindings; phase = _60_736.phase; sigmap = _60_736.sigmap; default_result_effect = _60_736.default_result_effect; iface = _60_736.iface; admitted_iface = _60_736.admitted_iface})
in ((unique_name any_val exclude_if this_env lid) && (unique_typ_name this_env lid))))


let gen_bvd = (fun _60_13 -> (match (_60_13) with
| Binding_typ_var (id) -> begin
(let _152_600 = (let _152_599 = (let _152_598 = (FStar_Absyn_Util.genident (Some (id.FStar_Ident.idRange)))
in ((id), (_152_598)))
in (FStar_Absyn_Util.mkbvd _152_599))
in FStar_Util.Inl (_152_600))
end
| Binding_var (id) -> begin
(let _152_603 = (let _152_602 = (let _152_601 = (FStar_Absyn_Util.genident (Some (id.FStar_Ident.idRange)))
in ((id), (_152_601)))
in (FStar_Absyn_Util.mkbvd _152_602))
in FStar_Util.Inr (_152_603))
end
| _60_745 -> begin
(FStar_All.failwith "Tried to generate a bound variable for a type constructor")
end))


let push_bvvdef : env  ->  FStar_Absyn_Syntax.bvvdef  ->  env = (fun env x -> (

let b = Binding_var (x.FStar_Absyn_Syntax.ppname)
in (

let _60_749 = env
in {curmodule = _60_749.curmodule; modules = _60_749.modules; open_namespaces = _60_749.open_namespaces; modul_abbrevs = _60_749.modul_abbrevs; sigaccum = _60_749.sigaccum; localbindings = (((FStar_Util.Inr (x)), (b)))::env.localbindings; recbindings = _60_749.recbindings; phase = _60_749.phase; sigmap = _60_749.sigmap; default_result_effect = _60_749.default_result_effect; iface = _60_749.iface; admitted_iface = _60_749.admitted_iface})))


let push_btvdef : env  ->  FStar_Absyn_Syntax.btvdef  ->  env = (fun env x -> (

let b = Binding_typ_var (x.FStar_Absyn_Syntax.ppname)
in (

let _60_754 = env
in {curmodule = _60_754.curmodule; modules = _60_754.modules; open_namespaces = _60_754.open_namespaces; modul_abbrevs = _60_754.modul_abbrevs; sigaccum = _60_754.sigaccum; localbindings = (((FStar_Util.Inl (x)), (b)))::env.localbindings; recbindings = _60_754.recbindings; phase = _60_754.phase; sigmap = _60_754.sigmap; default_result_effect = _60_754.default_result_effect; iface = _60_754.iface; admitted_iface = _60_754.admitted_iface})))


let push_local_binding : env  ->  binding  ->  (env * (FStar_Absyn_Syntax.btvdef, FStar_Absyn_Syntax.bvvdef) FStar_Util.either) = (fun env b -> (

let bvd = (gen_bvd b)
in (((

let _60_759 = env
in {curmodule = _60_759.curmodule; modules = _60_759.modules; open_namespaces = _60_759.open_namespaces; modul_abbrevs = _60_759.modul_abbrevs; sigaccum = _60_759.sigaccum; localbindings = (((bvd), (b)))::env.localbindings; recbindings = _60_759.recbindings; phase = _60_759.phase; sigmap = _60_759.sigmap; default_result_effect = _60_759.default_result_effect; iface = _60_759.iface; admitted_iface = _60_759.admitted_iface})), (bvd))))


let push_local_tbinding : env  ->  FStar_Ident.ident  ->  (env * FStar_Absyn_Syntax.btvdef) = (fun env a -> (match ((push_local_binding env (Binding_typ_var (a)))) with
| (env, FStar_Util.Inl (x)) -> begin
((env), (x))
end
| _60_768 -> begin
(FStar_All.failwith "impossible")
end))


let push_local_vbinding : env  ->  FStar_Ident.ident  ->  (env * FStar_Absyn_Syntax.bvvdef) = (fun env b -> (match ((push_local_binding env (Binding_var (b)))) with
| (env, FStar_Util.Inr (x)) -> begin
((env), (x))
end
| _60_776 -> begin
(FStar_All.failwith "impossible")
end))


let push_rec_binding : env  ->  binding  ->  env = (fun env b -> (match (b) with
| (Binding_let (lid)) | (Binding_tycon (lid)) -> begin
if (unique false true env lid) then begin
(

let _60_782 = env
in {curmodule = _60_782.curmodule; modules = _60_782.modules; open_namespaces = _60_782.open_namespaces; modul_abbrevs = _60_782.modul_abbrevs; sigaccum = _60_782.sigaccum; localbindings = _60_782.localbindings; recbindings = (b)::env.recbindings; phase = _60_782.phase; sigmap = _60_782.sigmap; default_result_effect = _60_782.default_result_effect; iface = _60_782.iface; admitted_iface = _60_782.admitted_iface})
end else begin
(Prims.raise (FStar_Absyn_Syntax.Error ((((Prims.strcat "Duplicate top-level names " lid.FStar_Ident.str)), ((FStar_Ident.range_of_lid lid))))))
end
end
| _60_785 -> begin
(FStar_All.failwith "Unexpected rec_binding")
end))


let push_sigelt : env  ->  FStar_Absyn_Syntax.sigelt  ->  env = (fun env s -> (

let err = (fun l -> (

let sopt = (let _152_634 = (sigmap env)
in (FStar_Util.smap_try_find _152_634 l.FStar_Ident.str))
in (

let r = (match (sopt) with
| Some (se, _60_793) -> begin
(match ((let _152_635 = (FStar_Absyn_Util.lids_of_sigelt se)
in (FStar_Util.find_opt (FStar_Ident.lid_equals l) _152_635))) with
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
in (let _152_638 = (let _152_637 = (let _152_636 = (FStar_Util.format2 "Duplicate top-level names [%s]; previously declared at %s" (FStar_Ident.text_of_lid l) r)
in ((_152_636), ((FStar_Ident.range_of_lid l))))
in FStar_Absyn_Syntax.Error (_152_637))
in (Prims.raise _152_638)))))
in (

let env = (

let _60_811 = (match (s) with
| FStar_Absyn_Syntax.Sig_let (_60_802) -> begin
((false), (true))
end
| FStar_Absyn_Syntax.Sig_bundle (_60_805) -> begin
((true), (true))
end
| _60_808 -> begin
((false), (false))
end)
in (match (_60_811) with
| (any_val, exclude_if) -> begin
(

let lids = (FStar_Absyn_Util.lids_of_sigelt s)
in (match ((FStar_Util.find_map lids (fun l -> if (not ((unique any_val exclude_if env l))) then begin
Some (l)
end else begin
None
end))) with
| None -> begin
(

let _60_815 = (extract_record env s)
in (

let _60_817 = env
in {curmodule = _60_817.curmodule; modules = _60_817.modules; open_namespaces = _60_817.open_namespaces; modul_abbrevs = _60_817.modul_abbrevs; sigaccum = (s)::env.sigaccum; localbindings = _60_817.localbindings; recbindings = _60_817.recbindings; phase = _60_817.phase; sigmap = _60_817.sigmap; default_result_effect = _60_817.default_result_effect; iface = _60_817.iface; admitted_iface = _60_817.admitted_iface}))
end
| Some (l) -> begin
(err l)
end))
end))
in (

let _60_836 = (match (s) with
| FStar_Absyn_Syntax.Sig_bundle (ses, _60_824, _60_826, _60_828) -> begin
(let _152_642 = (FStar_List.map (fun se -> (let _152_641 = (FStar_Absyn_Util.lids_of_sigelt se)
in ((_152_641), (se)))) ses)
in ((env), (_152_642)))
end
| _60_833 -> begin
(let _152_645 = (let _152_644 = (let _152_643 = (FStar_Absyn_Util.lids_of_sigelt s)
in ((_152_643), (s)))
in (_152_644)::[])
in ((env), (_152_645)))
end)
in (match (_60_836) with
| (env, lss) -> begin
(

let _60_841 = (FStar_All.pipe_right lss (FStar_List.iter (fun _60_839 -> (match (_60_839) with
| (lids, se) -> begin
(FStar_All.pipe_right lids (FStar_List.iter (fun lid -> (let _152_648 = (sigmap env)
in (FStar_Util.smap_add _152_648 lid.FStar_Ident.str ((se), ((env.iface && (not (env.admitted_iface))))))))))
end))))
in env)
end)))))


let push_namespace : env  ->  FStar_Ident.lident  ->  env = (fun env lid -> (

let _60_845 = env
in {curmodule = _60_845.curmodule; modules = _60_845.modules; open_namespaces = (lid)::env.open_namespaces; modul_abbrevs = _60_845.modul_abbrevs; sigaccum = _60_845.sigaccum; localbindings = _60_845.localbindings; recbindings = _60_845.recbindings; phase = _60_845.phase; sigmap = _60_845.sigmap; default_result_effect = _60_845.default_result_effect; iface = _60_845.iface; admitted_iface = _60_845.admitted_iface}))


let push_module_abbrev : env  ->  FStar_Ident.ident  ->  FStar_Ident.lident  ->  env = (fun env x l -> if (FStar_All.pipe_right env.modul_abbrevs (FStar_Util.for_some (fun _60_853 -> (match (_60_853) with
| (y, _60_852) -> begin
(x.FStar_Ident.idText = y.FStar_Ident.idText)
end)))) then begin
(let _152_662 = (let _152_661 = (let _152_660 = (FStar_Util.format1 "Module %s is already defined" x.FStar_Ident.idText)
in ((_152_660), (x.FStar_Ident.idRange)))
in FStar_Absyn_Syntax.Error (_152_661))
in (Prims.raise _152_662))
end else begin
(

let _60_854 = env
in {curmodule = _60_854.curmodule; modules = _60_854.modules; open_namespaces = _60_854.open_namespaces; modul_abbrevs = (((x), (l)))::env.modul_abbrevs; sigaccum = _60_854.sigaccum; localbindings = _60_854.localbindings; recbindings = _60_854.recbindings; phase = _60_854.phase; sigmap = _60_854.sigmap; default_result_effect = _60_854.default_result_effect; iface = _60_854.iface; admitted_iface = _60_854.admitted_iface})
end)


let is_type_lid : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let aux = (fun _60_859 -> (match (()) with
| () -> begin
(match ((try_lookup_typ_name' false env lid)) with
| Some (_60_861) -> begin
true
end
| _60_864 -> begin
false
end)
end))
in if (lid.FStar_Ident.ns = []) then begin
(match ((try_lookup_id env lid.FStar_Ident.ident)) with
| Some (_60_866) -> begin
false
end
| _60_869 -> begin
(aux ())
end)
end else begin
(aux ())
end))


let check_admits : FStar_Ident.lident  ->  env  ->  Prims.unit = (fun nm env -> (FStar_All.pipe_right env.sigaccum (FStar_List.iter (fun se -> (match (se) with
| FStar_Absyn_Syntax.Sig_val_decl (l, t, quals, r) -> begin
(match ((try_lookup_lid env l)) with
| None -> begin
(

let _60_880 = (let _152_676 = (let _152_675 = (FStar_Range.string_of_range (FStar_Ident.range_of_lid l))
in (let _152_674 = (FStar_Absyn_Print.sli l)
in (FStar_Util.format2 "%s: Warning: Admitting %s without a definition\n" _152_675 _152_674)))
in (FStar_Util.print_string _152_676))
in (let _152_677 = (sigmap env)
in (FStar_Util.smap_add _152_677 l.FStar_Ident.str ((FStar_Absyn_Syntax.Sig_val_decl (((l), (t), ((FStar_Absyn_Syntax.Assumption)::quals), (r)))), (false)))))
end
| Some (_60_883) -> begin
()
end)
end
| _60_886 -> begin
()
end)))))


let finish : env  ->  FStar_Absyn_Syntax.modul  ->  env = (fun env modul -> (

let _60_924 = (FStar_All.pipe_right modul.FStar_Absyn_Syntax.declarations (FStar_List.iter (fun _60_15 -> (match (_60_15) with
| FStar_Absyn_Syntax.Sig_bundle (ses, quals, _60_893, _60_895) -> begin
if (FStar_List.contains FStar_Absyn_Syntax.Private quals) then begin
(FStar_All.pipe_right ses (FStar_List.iter (fun _60_14 -> (match (_60_14) with
| FStar_Absyn_Syntax.Sig_datacon (lid, _60_901, _60_903, _60_905, _60_907, _60_909) -> begin
(let _152_684 = (sigmap env)
in (FStar_Util.smap_remove _152_684 lid.FStar_Ident.str))
end
| _60_913 -> begin
()
end))))
end else begin
()
end
end
| FStar_Absyn_Syntax.Sig_val_decl (lid, _60_916, quals, _60_919) -> begin
if (FStar_List.contains FStar_Absyn_Syntax.Private quals) then begin
(let _152_685 = (sigmap env)
in (FStar_Util.smap_remove _152_685 lid.FStar_Ident.str))
end else begin
()
end
end
| _60_923 -> begin
()
end))))
in (

let _60_926 = env
in {curmodule = None; modules = (((modul.FStar_Absyn_Syntax.name), (modul)))::env.modules; open_namespaces = []; modul_abbrevs = []; sigaccum = []; localbindings = []; recbindings = []; phase = FStar_Parser_AST.Un; sigmap = _60_926.sigmap; default_result_effect = _60_926.default_result_effect; iface = _60_926.iface; admitted_iface = _60_926.admitted_iface})))


let push : env  ->  env = (fun env -> (

let _60_929 = (push_record_cache ())
in (

let _60_931 = env
in (let _152_690 = (let _152_689 = (let _152_688 = (sigmap env)
in (FStar_Util.smap_copy _152_688))
in (_152_689)::env.sigmap)
in {curmodule = _60_931.curmodule; modules = _60_931.modules; open_namespaces = _60_931.open_namespaces; modul_abbrevs = _60_931.modul_abbrevs; sigaccum = _60_931.sigaccum; localbindings = _60_931.localbindings; recbindings = _60_931.recbindings; phase = _60_931.phase; sigmap = _152_690; default_result_effect = _60_931.default_result_effect; iface = _60_931.iface; admitted_iface = _60_931.admitted_iface}))))


let mark : env  ->  env = (fun env -> (push env))


let reset_mark : env  ->  env = (fun env -> (

let _60_935 = env
in (let _152_695 = (FStar_List.tl env.sigmap)
in {curmodule = _60_935.curmodule; modules = _60_935.modules; open_namespaces = _60_935.open_namespaces; modul_abbrevs = _60_935.modul_abbrevs; sigaccum = _60_935.sigaccum; localbindings = _60_935.localbindings; recbindings = _60_935.recbindings; phase = _60_935.phase; sigmap = _152_695; default_result_effect = _60_935.default_result_effect; iface = _60_935.iface; admitted_iface = _60_935.admitted_iface})))


let commit_mark : env  ->  env = (fun env -> (match (env.sigmap) with
| (hd)::(_60_940)::tl -> begin
(

let _60_944 = env
in {curmodule = _60_944.curmodule; modules = _60_944.modules; open_namespaces = _60_944.open_namespaces; modul_abbrevs = _60_944.modul_abbrevs; sigaccum = _60_944.sigaccum; localbindings = _60_944.localbindings; recbindings = _60_944.recbindings; phase = _60_944.phase; sigmap = (hd)::tl; default_result_effect = _60_944.default_result_effect; iface = _60_944.iface; admitted_iface = _60_944.admitted_iface})
end
| _60_947 -> begin
(FStar_All.failwith "Impossible")
end))


let pop : env  ->  env = (fun env -> (match (env.sigmap) with
| (_60_951)::maps -> begin
(

let _60_953 = (pop_record_cache ())
in (

let _60_955 = env
in {curmodule = _60_955.curmodule; modules = _60_955.modules; open_namespaces = _60_955.open_namespaces; modul_abbrevs = _60_955.modul_abbrevs; sigaccum = _60_955.sigaccum; localbindings = _60_955.localbindings; recbindings = _60_955.recbindings; phase = _60_955.phase; sigmap = maps; default_result_effect = _60_955.default_result_effect; iface = _60_955.iface; admitted_iface = _60_955.admitted_iface}))
end
| _60_958 -> begin
(FStar_All.failwith "No more modules to pop")
end))


let export_interface : FStar_Ident.lident  ->  env  ->  env = (fun m env -> (

let sigelt_in_m = (fun se -> (match ((FStar_Absyn_Util.lids_of_sigelt se)) with
| (l)::_60_964 -> begin
(l.FStar_Ident.nsstr = m.FStar_Ident.str)
end
| _60_968 -> begin
false
end))
in (

let sm = (sigmap env)
in (

let env = (pop env)
in (

let keys = (FStar_Util.smap_keys sm)
in (

let sm' = (sigmap env)
in (

let _60_991 = (FStar_All.pipe_right keys (FStar_List.iter (fun k -> (match ((FStar_Util.smap_try_find sm' k)) with
| Some (se, true) when (sigelt_in_m se) -> begin
(

let _60_978 = (FStar_Util.smap_remove sm' k)
in (

let se = (match (se) with
| FStar_Absyn_Syntax.Sig_val_decl (l, t, q, r) -> begin
FStar_Absyn_Syntax.Sig_val_decl (((l), (t), ((FStar_Absyn_Syntax.Assumption)::q), (r)))
end
| _60_987 -> begin
se
end)
in (FStar_Util.smap_add sm' k ((se), (false)))))
end
| _60_990 -> begin
()
end))))
in env)))))))


let finish_module_or_interface : env  ->  FStar_Absyn_Syntax.modul  ->  env = (fun env modul -> (

let _60_995 = if (not (modul.FStar_Absyn_Syntax.is_interface)) then begin
(check_admits modul.FStar_Absyn_Syntax.name env)
end else begin
()
end
in (finish env modul)))


let prepare_module_or_interface : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  (env * Prims.bool) = (fun intf admitted env mname -> (

let prep = (fun env -> (

let open_ns = if (FStar_Ident.lid_equals mname FStar_Absyn_Const.prims_lid) then begin
[]
end else begin
if (FStar_Util.starts_with "FStar." (FStar_Ident.text_of_lid mname)) then begin
(FStar_Absyn_Const.prims_lid)::(FStar_Absyn_Const.fstar_ns_lid)::[]
end else begin
(FStar_Absyn_Const.prims_lid)::(FStar_Absyn_Const.st_lid)::(FStar_Absyn_Const.all_lid)::(FStar_Absyn_Const.fstar_ns_lid)::[]
end
end
in (

let _60_1004 = env
in {curmodule = Some (mname); modules = _60_1004.modules; open_namespaces = open_ns; modul_abbrevs = _60_1004.modul_abbrevs; sigaccum = _60_1004.sigaccum; localbindings = _60_1004.localbindings; recbindings = _60_1004.recbindings; phase = _60_1004.phase; sigmap = env.sigmap; default_result_effect = _60_1004.default_result_effect; iface = intf; admitted_iface = admitted})))
in (match ((FStar_All.pipe_right env.modules (FStar_Util.find_opt (fun _60_1009 -> (match (_60_1009) with
| (l, _60_1008) -> begin
(FStar_Ident.lid_equals l mname)
end))))) with
| None -> begin
(((prep env)), (false))
end
| Some (_60_1012, m) -> begin
(let _152_724 = (let _152_723 = (let _152_722 = (FStar_Util.format1 "Duplicate module or interface name: %s" mname.FStar_Ident.str)
in ((_152_722), ((FStar_Ident.range_of_lid mname))))
in FStar_Absyn_Syntax.Error (_152_723))
in (Prims.raise _152_724))
end)))


let enter_monad_scope : env  ->  FStar_Ident.ident  ->  env = (fun env mname -> (

let curmod = (current_module env)
in (

let mscope = (FStar_Ident.lid_of_ids (FStar_List.append curmod.FStar_Ident.ns ((curmod.FStar_Ident.ident)::(mname)::[])))
in (

let _60_1020 = env
in {curmodule = Some (mscope); modules = _60_1020.modules; open_namespaces = (curmod)::env.open_namespaces; modul_abbrevs = _60_1020.modul_abbrevs; sigaccum = _60_1020.sigaccum; localbindings = _60_1020.localbindings; recbindings = _60_1020.recbindings; phase = _60_1020.phase; sigmap = _60_1020.sigmap; default_result_effect = _60_1020.default_result_effect; iface = _60_1020.iface; admitted_iface = _60_1020.admitted_iface}))))


let exit_monad_scope : env  ->  env  ->  env = (fun env0 env -> (

let _60_1024 = env
in {curmodule = env0.curmodule; modules = _60_1024.modules; open_namespaces = env0.open_namespaces; modul_abbrevs = _60_1024.modul_abbrevs; sigaccum = _60_1024.sigaccum; localbindings = _60_1024.localbindings; recbindings = _60_1024.recbindings; phase = _60_1024.phase; sigmap = _60_1024.sigmap; default_result_effect = _60_1024.default_result_effect; iface = _60_1024.iface; admitted_iface = _60_1024.admitted_iface}))


let fail_or = (fun env lookup lid -> (match ((lookup lid)) with
| None -> begin
(

let r = (match ((try_lookup_name true false env lid)) with
| None -> begin
None
end
| (Some (Knd_name (o, _))) | (Some (Eff_name (o, _))) | (Some (Typ_name (o, _))) | (Some (Exp_name (o, _))) -> begin
Some ((range_of_occurrence o))
end)
in (

let msg = (match (r) with
| None -> begin
""
end
| Some (r) -> begin
(let _152_739 = (FStar_Range.string_of_range r)
in (FStar_Util.format1 "(Possible clash with related name at %s)" _152_739))
end)
in (let _152_742 = (let _152_741 = (let _152_740 = (FStar_Util.format2 "Identifier not found: [%s] %s" (FStar_Ident.text_of_lid lid) msg)
in ((_152_740), ((FStar_Ident.range_of_lid lid))))
in FStar_Absyn_Syntax.Error (_152_741))
in (Prims.raise _152_742))))
end
| Some (r) -> begin
r
end))


let fail_or2 = (fun lookup id -> (match ((lookup id)) with
| None -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((((Prims.strcat "Identifier not found [" (Prims.strcat id.FStar_Ident.idText "]"))), (id.FStar_Ident.idRange)))))
end
| Some (r) -> begin
r
end))




