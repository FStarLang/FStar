
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
| Binding_typ_var (_52_18) -> begin
_52_18
end))


let ___Binding_var____0 = (fun projectee -> (match (projectee) with
| Binding_var (_52_21) -> begin
_52_21
end))


let ___Binding_let____0 = (fun projectee -> (match (projectee) with
| Binding_let (_52_24) -> begin
_52_24
end))


let ___Binding_tycon____0 = (fun projectee -> (match (projectee) with
| Binding_tycon (_52_27) -> begin
_52_27
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
| OSig (_52_43) -> begin
_52_43
end))


let ___OLet____0 = (fun projectee -> (match (projectee) with
| OLet (_52_46) -> begin
_52_46
end))


let ___ORec____0 = (fun projectee -> (match (projectee) with
| ORec (_52_49) -> begin
_52_49
end))


let range_of_occurrence : occurrence  ->  FStar_Range.range = (fun _52_1 -> (match (_52_1) with
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
| Exp_name (_52_58) -> begin
_52_58
end))


let ___Typ_name____0 = (fun projectee -> (match (projectee) with
| Typ_name (_52_61) -> begin
_52_61
end))


let ___Eff_name____0 = (fun projectee -> (match (projectee) with
| Eff_name (_52_64) -> begin
_52_64
end))


let ___Knd_name____0 = (fun projectee -> (match (projectee) with
| Knd_name (_52_67) -> begin
_52_67
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


let qual : FStar_Ident.lident  ->  FStar_Ident.ident  ->  FStar_Ident.lident = (fun lid id -> (let _141_230 = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns ((lid.FStar_Ident.ident)::(id)::[])))
in (FStar_Ident.set_lid_range _141_230 id.FStar_Ident.idRange)))


let qualify : env  ->  FStar_Ident.ident  ->  FStar_Ident.lident = (fun env id -> (let _141_235 = (current_module env)
in (qual _141_235 id)))


let qualify_lid : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (

let cur = (current_module env)
in (let _141_240 = (FStar_Ident.lid_of_ids (FStar_List.append (FStar_List.append (FStar_List.append cur.FStar_Ident.ns ((cur.FStar_Ident.ident)::[])) lid.FStar_Ident.ns) ((lid.FStar_Ident.ident)::[])))
in (FStar_Ident.set_lid_range _141_240 (FStar_Ident.range_of_lid lid)))))


let new_sigmap = (fun _52_89 -> (match (()) with
| () -> begin
(FStar_Util.smap_create 100)
end))


let empty_env : Prims.unit  ->  env = (fun _52_90 -> (match (()) with
| () -> begin
(let _141_245 = (let _141_244 = (new_sigmap ())
in (_141_244)::[])
in {curmodule = None; modules = []; open_namespaces = []; modul_abbrevs = []; sigaccum = []; localbindings = []; recbindings = []; phase = FStar_Parser_AST.Un; sigmap = _141_245; default_result_effect = FStar_Absyn_Util.ml_comp; iface = false; admitted_iface = false})
end))


let sigmap : env  ->  (FStar_Absyn_Syntax.sigelt * Prims.bool) FStar_Util.smap = (fun env -> (FStar_List.hd env.sigmap))


let default_total : env  ->  env = (fun env -> (

let _52_93 = env
in {curmodule = _52_93.curmodule; modules = _52_93.modules; open_namespaces = _52_93.open_namespaces; modul_abbrevs = _52_93.modul_abbrevs; sigaccum = _52_93.sigaccum; localbindings = _52_93.localbindings; recbindings = _52_93.recbindings; phase = _52_93.phase; sigmap = _52_93.sigmap; default_result_effect = (fun t _52_96 -> (FStar_Absyn_Syntax.mk_Total t)); iface = _52_93.iface; admitted_iface = _52_93.admitted_iface}))


let default_ml : env  ->  env = (fun env -> (

let _52_99 = env
in {curmodule = _52_99.curmodule; modules = _52_99.modules; open_namespaces = _52_99.open_namespaces; modul_abbrevs = _52_99.modul_abbrevs; sigaccum = _52_99.sigaccum; localbindings = _52_99.localbindings; recbindings = _52_99.recbindings; phase = _52_99.phase; sigmap = _52_99.sigmap; default_result_effect = FStar_Absyn_Util.ml_comp; iface = _52_99.iface; admitted_iface = _52_99.admitted_iface}))


let range_of_binding : binding  ->  FStar_Range.range = (fun _52_2 -> (match (_52_2) with
| (Binding_typ_var (id)) | (Binding_var (id)) -> begin
id.FStar_Ident.idRange
end
| (Binding_let (lid)) | (Binding_tycon (lid)) -> begin
(FStar_Ident.range_of_lid lid)
end))


let try_lookup_typ_var : env  ->  FStar_Ident.ident  ->  FStar_Absyn_Syntax.typ Prims.option = (fun env id -> (

let fopt = (FStar_List.tryFind (fun _52_113 -> (match (_52_113) with
| (_52_111, b) -> begin
(match (b) with
| (Binding_typ_var (id')) | (Binding_var (id')) -> begin
(id.FStar_Ident.idText = id'.FStar_Ident.idText)
end
| _52_118 -> begin
false
end)
end)) env.localbindings)
in (match (fopt) with
| Some (FStar_Util.Inl (bvd), Binding_typ_var (_52_123)) -> begin
(let _141_261 = (FStar_Absyn_Util.bvd_to_typ (FStar_Absyn_Util.set_bvd_range bvd id.FStar_Ident.idRange) FStar_Absyn_Syntax.kun)
in Some (_141_261))
end
| _52_128 -> begin
None
end)))


let resolve_in_open_namespaces' = (fun env lid finder -> (

let aux = (fun namespaces -> (match ((finder lid)) with
| Some (r) -> begin
Some (r)
end
| _52_138 -> begin
(

let ids = (FStar_Ident.ids_of_lid lid)
in (FStar_Util.find_map namespaces (fun ns -> (

let full_name = (FStar_Ident.lid_of_ids (FStar_List.append (FStar_Ident.ids_of_lid ns) ids))
in (finder full_name)))))
end))
in (let _141_272 = (let _141_271 = (current_module env)
in (_141_271)::env.open_namespaces)
in (aux _141_272))))


let expand_module_abbrevs : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (match (lid.FStar_Ident.ns) with
| id::[] -> begin
(match ((FStar_All.pipe_right env.modul_abbrevs (FStar_List.tryFind (fun _52_149 -> (match (_52_149) with
| (id', _52_148) -> begin
(id.FStar_Ident.idText = id'.FStar_Ident.idText)
end))))) with
| None -> begin
lid
end
| Some (_52_152, lid') -> begin
(FStar_Ident.lid_of_ids (FStar_List.append (FStar_Ident.ids_of_lid lid') ((lid.FStar_Ident.ident)::[])))
end)
end
| _52_157 -> begin
lid
end))


let resolve_in_open_namespaces = (fun env lid finder -> (let _141_288 = (expand_module_abbrevs env lid)
in (resolve_in_open_namespaces' env _141_288 finder)))


let unmangleMap : (Prims.string * Prims.string) Prims.list = (("op_ColonColon", "Cons"))::(("not", "op_Negation"))::[]


let unmangleOpName : FStar_Ident.ident  ->  FStar_Ident.lident Prims.option = (fun id -> (FStar_Util.find_map unmangleMap (fun _52_165 -> (match (_52_165) with
| (x, y) -> begin
if (id.FStar_Ident.idText = x) then begin
(let _141_292 = (FStar_Ident.lid_of_path (("Prims")::(y)::[]) id.FStar_Ident.idRange)
in Some (_141_292))
end else begin
None
end
end))))


let try_lookup_id' : env  ->  FStar_Ident.ident  ->  (FStar_Ident.lident * FStar_Absyn_Syntax.exp) Prims.option = (fun env id -> (match ((unmangleOpName id)) with
| Some (l) -> begin
(let _141_298 = (let _141_297 = (FStar_Absyn_Syntax.mk_Exp_fvar ((FStar_Absyn_Util.fv l), None) None id.FStar_Ident.idRange)
in (l, _141_297))
in Some (_141_298))
end
| _52_171 -> begin
(

let found = (FStar_Util.find_map env.localbindings (fun _52_3 -> (match (_52_3) with
| (FStar_Util.Inl (_52_174), Binding_typ_var (id')) when (id'.FStar_Ident.idText = id.FStar_Ident.idText) -> begin
Some (FStar_Util.Inl (()))
end
| (FStar_Util.Inr (bvd), Binding_var (id')) when (id'.FStar_Ident.idText = id.FStar_Ident.idText) -> begin
(let _141_303 = (let _141_302 = (let _141_301 = (FStar_Ident.lid_of_ids ((id')::[]))
in (let _141_300 = (FStar_Absyn_Util.bvd_to_exp (FStar_Absyn_Util.set_bvd_range bvd id.FStar_Ident.idRange) FStar_Absyn_Syntax.tun)
in (_141_301, _141_300)))
in FStar_Util.Inr (_141_302))
in Some (_141_303))
end
| _52_185 -> begin
None
end)))
in (match (found) with
| Some (FStar_Util.Inr (x)) -> begin
Some (x)
end
| _52_191 -> begin
None
end))
end))


let try_lookup_id : env  ->  FStar_Ident.ident  ->  FStar_Absyn_Syntax.exp Prims.option = (fun env id -> (match ((try_lookup_id' env id)) with
| Some (_52_195, e) -> begin
Some (e)
end
| None -> begin
None
end))


let fv_qual_of_se : FStar_Absyn_Syntax.sigelt  ->  FStar_Absyn_Syntax.fv_qual Prims.option = (fun _52_5 -> (match (_52_5) with
| FStar_Absyn_Syntax.Sig_datacon (_52_202, _52_204, (l, _52_207, _52_209), quals, _52_213, _52_215) -> begin
(

let qopt = (FStar_Util.find_map quals (fun _52_4 -> (match (_52_4) with
| FStar_Absyn_Syntax.RecordConstructor (fs) -> begin
Some (FStar_Absyn_Syntax.Record_ctor ((l, fs)))
end
| _52_222 -> begin
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
| FStar_Absyn_Syntax.Sig_val_decl (_52_227, _52_229, quals, _52_232) -> begin
None
end
| _52_236 -> begin
None
end))


let try_lookup_name : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  foundname Prims.option = (fun any_val exclude_interf env lid -> (

let find_in_sig = (fun lid -> (match ((let _141_321 = (sigmap env)
in (FStar_Util.smap_try_find _141_321 lid.FStar_Ident.str))) with
| Some (_52_244, true) when exclude_interf -> begin
None
end
| None -> begin
None
end
| Some (se, _52_251) -> begin
(match (se) with
| (FStar_Absyn_Syntax.Sig_typ_abbrev (_)) | (FStar_Absyn_Syntax.Sig_tycon (_)) -> begin
(let _141_324 = (let _141_323 = (let _141_322 = (FStar_Absyn_Util.ftv lid FStar_Absyn_Syntax.kun)
in (OSig (se), _141_322))
in Typ_name (_141_323))
in Some (_141_324))
end
| FStar_Absyn_Syntax.Sig_kind_abbrev (_52_261) -> begin
Some (Knd_name ((OSig (se), lid)))
end
| FStar_Absyn_Syntax.Sig_new_effect (ne, _52_265) -> begin
(let _141_327 = (let _141_326 = (let _141_325 = (FStar_Ident.set_lid_range ne.FStar_Absyn_Syntax.mname (FStar_Ident.range_of_lid lid))
in (OSig (se), _141_325))
in Eff_name (_141_326))
in Some (_141_327))
end
| FStar_Absyn_Syntax.Sig_effect_abbrev (_52_269) -> begin
Some (Eff_name ((OSig (se), lid)))
end
| FStar_Absyn_Syntax.Sig_datacon (_52_272) -> begin
(let _141_331 = (let _141_330 = (let _141_329 = (let _141_328 = (fv_qual_of_se se)
in (FStar_Absyn_Util.fvar _141_328 lid (FStar_Ident.range_of_lid lid)))
in (OSig (se), _141_329))
in Exp_name (_141_330))
in Some (_141_331))
end
| FStar_Absyn_Syntax.Sig_let (_52_275) -> begin
(let _141_334 = (let _141_333 = (let _141_332 = (FStar_Absyn_Util.fvar None lid (FStar_Ident.range_of_lid lid))
in (OSig (se), _141_332))
in Exp_name (_141_333))
in Some (_141_334))
end
| FStar_Absyn_Syntax.Sig_val_decl (_52_278, _52_280, quals, _52_283) -> begin
if (any_val || (FStar_All.pipe_right quals (FStar_Util.for_some (fun _52_6 -> (match (_52_6) with
| FStar_Absyn_Syntax.Assumption -> begin
true
end
| _52_289 -> begin
false
end))))) then begin
(let _141_339 = (let _141_338 = (let _141_337 = (let _141_336 = (fv_qual_of_se se)
in (FStar_Absyn_Util.fvar _141_336 lid (FStar_Ident.range_of_lid lid)))
in (OSig (se), _141_337))
in Exp_name (_141_338))
in Some (_141_339))
end else begin
None
end
end
| _52_291 -> begin
None
end)
end))
in (

let found_id = (match (lid.FStar_Ident.ns) with
| [] -> begin
(match ((try_lookup_id' env lid.FStar_Ident.ident)) with
| Some (lid, e) -> begin
Some (Exp_name ((OLet (lid), e)))
end
| None -> begin
(

let recname = (qualify env lid.FStar_Ident.ident)
in (FStar_Util.find_map env.recbindings (fun _52_7 -> (match (_52_7) with
| Binding_let (l) when (FStar_Ident.lid_equals l recname) -> begin
(let _141_343 = (let _141_342 = (let _141_341 = (FStar_Absyn_Util.fvar None recname (FStar_Ident.range_of_lid recname))
in (ORec (l), _141_341))
in Exp_name (_141_342))
in Some (_141_343))
end
| Binding_tycon (l) when (FStar_Ident.lid_equals l recname) -> begin
(let _141_346 = (let _141_345 = (let _141_344 = (FStar_Absyn_Util.ftv recname FStar_Absyn_Syntax.kun)
in (ORec (l), _141_344))
in Typ_name (_141_345))
in Some (_141_346))
end
| _52_305 -> begin
None
end))))
end)
end
| _52_307 -> begin
None
end)
in (match (found_id) with
| Some (_52_310) -> begin
found_id
end
| _52_313 -> begin
(resolve_in_open_namespaces env lid find_in_sig)
end))))


let try_lookup_typ_name' : Prims.bool  ->  env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.typ Prims.option = (fun exclude_interf env lid -> (match ((try_lookup_name true exclude_interf env lid)) with
| Some (Typ_name (_52_318, t)) -> begin
Some (t)
end
| Some (Eff_name (_52_324, l)) -> begin
(let _141_353 = (FStar_Absyn_Util.ftv l FStar_Absyn_Syntax.mk_Kind_unknown)
in Some (_141_353))
end
| _52_330 -> begin
None
end))


let try_lookup_typ_name : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.typ Prims.option = (fun env l -> (try_lookup_typ_name' (not (env.iface)) env l))


let try_lookup_effect_name' : Prims.bool  ->  env  ->  FStar_Ident.lident  ->  (occurrence * FStar_Ident.lident) Prims.option = (fun exclude_interf env lid -> (match ((try_lookup_name true exclude_interf env lid)) with
| Some (Eff_name (o, l)) -> begin
Some ((o, l))
end
| _52_342 -> begin
None
end))


let try_lookup_effect_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env l -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some (o, l) -> begin
Some (l)
end
| _52_350 -> begin
None
end))


let try_lookup_effect_defn : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.eff_decl Prims.option = (fun env l -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some (OSig (FStar_Absyn_Syntax.Sig_new_effect (ne, _52_355)), _52_360) -> begin
Some (ne)
end
| _52_364 -> begin
None
end))


let is_effect_name : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((try_lookup_effect_name env lid)) with
| None -> begin
false
end
| Some (_52_369) -> begin
true
end))


let try_resolve_typ_abbrev : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.typ Prims.option = (fun env lid -> (

let find_in_sig = (fun lid -> (match ((let _141_382 = (sigmap env)
in (FStar_Util.smap_try_find _141_382 lid.FStar_Ident.str))) with
| Some (FStar_Absyn_Syntax.Sig_typ_abbrev (lid, tps, k, def, _52_380, _52_382), _52_386) -> begin
(

let t = (let _141_385 = (let _141_384 = (let _141_383 = (FStar_Absyn_Util.close_with_lam tps def)
in (_141_383, lid))
in FStar_Absyn_Syntax.Meta_named (_141_384))
in (FStar_Absyn_Syntax.mk_Typ_meta _141_385))
in Some (t))
end
| _52_391 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))


let lookup_letbinding_quals : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.qualifier Prims.list = (fun env lid -> (

let find_in_sig = (fun lid -> (match ((let _141_392 = (sigmap env)
in (FStar_Util.smap_try_find _141_392 lid.FStar_Ident.str))) with
| Some (FStar_Absyn_Syntax.Sig_val_decl (lid, _52_398, quals, _52_401), _52_405) -> begin
Some (quals)
end
| _52_409 -> begin
None
end))
in (match ((resolve_in_open_namespaces env lid find_in_sig)) with
| Some (quals) -> begin
quals
end
| _52_413 -> begin
[]
end)))


let try_lookup_module : env  ->  Prims.string Prims.list  ->  FStar_Absyn_Syntax.modul Prims.option = (fun env path -> (match ((FStar_List.tryFind (fun _52_418 -> (match (_52_418) with
| (mlid, modul) -> begin
((FStar_Ident.path_of_lid mlid) = path)
end)) env.modules)) with
| Some (_52_420, modul) -> begin
Some (modul)
end
| None -> begin
None
end))


let try_lookup_let : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.exp Prims.option = (fun env lid -> (

let find_in_sig = (fun lid -> (match ((let _141_404 = (sigmap env)
in (FStar_Util.smap_try_find _141_404 lid.FStar_Ident.str))) with
| Some (FStar_Absyn_Syntax.Sig_let (_52_430), _52_433) -> begin
(let _141_405 = (FStar_Absyn_Util.fvar None lid (FStar_Ident.range_of_lid lid))
in Some (_141_405))
end
| _52_437 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))


let try_lookup_lid' : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.exp Prims.option = (fun any_val exclude_interf env lid -> (match ((try_lookup_name any_val exclude_interf env lid)) with
| Some (Exp_name (_52_443, e)) -> begin
Some (e)
end
| _52_449 -> begin
None
end))


let try_lookup_lid : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.exp Prims.option = (fun env l -> (try_lookup_lid' env.iface false env l))


let try_lookup_datacon : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.typ FStar_Absyn_Syntax.var Prims.option = (fun env lid -> (

let find_in_sig = (fun lid -> (match ((let _141_424 = (sigmap env)
in (FStar_Util.smap_try_find _141_424 lid.FStar_Ident.str))) with
| Some (FStar_Absyn_Syntax.Sig_val_decl (_52_457, _52_459, quals, _52_462), _52_466) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _52_8 -> (match (_52_8) with
| FStar_Absyn_Syntax.Assumption -> begin
true
end
| _52_472 -> begin
false
end)))) then begin
Some ((FStar_Absyn_Util.fv lid))
end else begin
None
end
end
| Some (FStar_Absyn_Syntax.Sig_datacon (_52_474), _52_477) -> begin
Some ((FStar_Absyn_Util.fv lid))
end
| _52_481 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))


let find_all_datacons : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.list Prims.option = (fun env lid -> (

let find_in_sig = (fun lid -> (match ((let _141_432 = (sigmap env)
in (FStar_Util.smap_try_find _141_432 lid.FStar_Ident.str))) with
| Some (FStar_Absyn_Syntax.Sig_tycon (_52_487, _52_489, _52_491, _52_493, datas, _52_496, _52_498), _52_502) -> begin
Some (datas)
end
| _52_506 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))


let record_cache_aux : ((Prims.unit  ->  Prims.unit) * (Prims.unit  ->  Prims.unit) * (Prims.unit  ->  record_or_dc Prims.list) * (record_or_dc  ->  Prims.unit)) = (

let record_cache = (FStar_Util.mk_ref (([])::[]))
in (

let push = (fun _52_509 -> (match (()) with
| () -> begin
(let _141_446 = (let _141_445 = (let _141_443 = (FStar_ST.read record_cache)
in (FStar_List.hd _141_443))
in (let _141_444 = (FStar_ST.read record_cache)
in (_141_445)::_141_444))
in (FStar_ST.op_Colon_Equals record_cache _141_446))
end))
in (

let pop = (fun _52_511 -> (match (()) with
| () -> begin
(let _141_450 = (let _141_449 = (FStar_ST.read record_cache)
in (FStar_List.tl _141_449))
in (FStar_ST.op_Colon_Equals record_cache _141_450))
end))
in (

let peek = (fun _52_513 -> (match (()) with
| () -> begin
(let _141_453 = (FStar_ST.read record_cache)
in (FStar_List.hd _141_453))
end))
in (

let insert = (fun r -> (let _141_460 = (let _141_459 = (let _141_456 = (peek ())
in (r)::_141_456)
in (let _141_458 = (let _141_457 = (FStar_ST.read record_cache)
in (FStar_List.tl _141_457))
in (_141_459)::_141_458))
in (FStar_ST.op_Colon_Equals record_cache _141_460)))
in (push, pop, peek, insert))))))


let push_record_cache : Prims.unit  ->  Prims.unit = (

let _52_523 = record_cache_aux
in (match (_52_523) with
| (push, _52_518, _52_520, _52_522) -> begin
push
end))


let pop_record_cache : Prims.unit  ->  Prims.unit = (

let _52_531 = record_cache_aux
in (match (_52_531) with
| (_52_525, pop, _52_528, _52_530) -> begin
pop
end))


let peek_record_cache : Prims.unit  ->  record_or_dc Prims.list = (

let _52_539 = record_cache_aux
in (match (_52_539) with
| (_52_533, _52_535, peek, _52_538) -> begin
peek
end))


let insert_record_cache : record_or_dc  ->  Prims.unit = (

let _52_547 = record_cache_aux
in (match (_52_547) with
| (_52_541, _52_543, _52_545, insert) -> begin
insert
end))


let extract_record : env  ->  FStar_Absyn_Syntax.sigelt  ->  Prims.unit = (fun e _52_12 -> (match (_52_12) with
| FStar_Absyn_Syntax.Sig_bundle (sigs, _52_552, _52_554, _52_556) -> begin
(

let is_rec = (FStar_Util.for_some (fun _52_9 -> (match (_52_9) with
| (FStar_Absyn_Syntax.RecordType (_)) | (FStar_Absyn_Syntax.RecordConstructor (_)) -> begin
true
end
| _52_567 -> begin
false
end)))
in (

let find_dc = (fun dc -> (FStar_All.pipe_right sigs (FStar_Util.find_opt (fun _52_10 -> (match (_52_10) with
| FStar_Absyn_Syntax.Sig_datacon (lid, _52_574, _52_576, _52_578, _52_580, _52_582) -> begin
(FStar_Ident.lid_equals dc lid)
end
| _52_586 -> begin
false
end)))))
in (FStar_All.pipe_right sigs (FStar_List.iter (fun _52_11 -> (match (_52_11) with
| FStar_Absyn_Syntax.Sig_tycon (typename, parms, _52_591, _52_593, dc::[], tags, _52_598) -> begin
(match ((let _141_531 = (find_dc dc)
in (FStar_All.pipe_left FStar_Util.must _141_531))) with
| FStar_Absyn_Syntax.Sig_datacon (constrname, t, _52_604, _52_606, _52_608, _52_610) -> begin
(

let formals = (match ((FStar_Absyn_Util.function_formals t)) with
| Some (x, _52_615) -> begin
x
end
| _52_619 -> begin
[]
end)
in (

let is_rec = (is_rec tags)
in (

let fields = (FStar_All.pipe_right formals (FStar_List.collect (fun b -> (match (b) with
| (FStar_Util.Inr (x), q) -> begin
if ((FStar_Absyn_Syntax.is_null_binder b) || (is_rec && (match (q) with
| Some (FStar_Absyn_Syntax.Implicit (_52_628)) -> begin
true
end
| _52_632 -> begin
false
end))) then begin
[]
end else begin
(let _141_535 = (let _141_534 = (let _141_533 = if is_rec then begin
(FStar_Absyn_Util.unmangle_field_name x.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ppname)
end else begin
x.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ppname
end
in (qual constrname _141_533))
in (_141_534, x.FStar_Absyn_Syntax.sort))
in (_141_535)::[])
end
end
| _52_634 -> begin
[]
end))))
in (

let record = {typename = typename; constrname = constrname; parms = parms; fields = fields; is_record = is_rec}
in (insert_record_cache record)))))
end
| _52_638 -> begin
()
end)
end
| _52_640 -> begin
()
end))))))
end
| _52_642 -> begin
()
end))


let try_lookup_record_or_dc_by_field_name : env  ->  FStar_Ident.lident  ->  (record_or_dc * FStar_Ident.lident) Prims.option = (fun env fieldname -> (

let maybe_add_constrname = (fun ns c -> (

let rec aux = (fun ns -> (match (ns) with
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
(let _141_546 = (aux tl)
in (hd)::_141_546)
end))
in (aux ns)))
in (

let find_in_cache = (fun fieldname -> (

let _52_660 = (fieldname.FStar_Ident.ns, fieldname.FStar_Ident.ident)
in (match (_52_660) with
| (ns, fieldname) -> begin
(let _141_551 = (peek_record_cache ())
in (FStar_Util.find_map _141_551 (fun record -> (

let constrname = record.constrname.FStar_Ident.ident
in (

let ns = (maybe_add_constrname ns constrname)
in (

let fname = (FStar_Ident.lid_of_ids (FStar_List.append ns ((fieldname)::[])))
in (FStar_Util.find_map record.fields (fun _52_668 -> (match (_52_668) with
| (f, _52_667) -> begin
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
| _52_676 -> begin
None
end))


let try_lookup_projector_by_field_name : env  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * Prims.bool) Prims.option = (fun env fieldname -> (match ((try_lookup_record_or_dc_by_field_name env fieldname)) with
| Some (r, f) -> begin
Some ((f, r.is_record))
end
| _52_684 -> begin
None
end))


let qualify_field_to_record : env  ->  record_or_dc  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env recd f -> (

let qualify = (fun fieldname -> (

let _52_692 = (fieldname.FStar_Ident.ns, fieldname.FStar_Ident.ident)
in (match (_52_692) with
| (ns, fieldname) -> begin
(

let constrname = recd.constrname.FStar_Ident.ident
in (

let fname = (FStar_Ident.lid_of_ids (FStar_List.append (FStar_List.append ns ((constrname)::[])) ((fieldname)::[])))
in (FStar_Util.find_map recd.fields (fun _52_698 -> (match (_52_698) with
| (f, _52_697) -> begin
if (FStar_Ident.lid_equals fname f) then begin
Some (fname)
end else begin
None
end
end)))))
end)))
in (resolve_in_open_namespaces env f qualify)))


let find_kind_abbrev : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env l -> (match ((try_lookup_name true (not (env.iface)) env l)) with
| Some (Knd_name (_52_702, l)) -> begin
Some (l)
end
| _52_708 -> begin
None
end))


let is_kind_abbrev : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (match ((find_kind_abbrev env l)) with
| None -> begin
false
end
| Some (_52_713) -> begin
true
end))


let unique_name : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  Prims.bool = (fun any_val exclude_if env lid -> (match ((try_lookup_lid' any_val exclude_if env lid)) with
| None -> begin
(match ((find_kind_abbrev env lid)) with
| None -> begin
true
end
| Some (_52_722) -> begin
false
end)
end
| Some (_52_725) -> begin
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

let _52_736 = env
in {curmodule = _52_736.curmodule; modules = _52_736.modules; open_namespaces = []; modul_abbrevs = _52_736.modul_abbrevs; sigaccum = _52_736.sigaccum; localbindings = _52_736.localbindings; recbindings = _52_736.recbindings; phase = _52_736.phase; sigmap = _52_736.sigmap; default_result_effect = _52_736.default_result_effect; iface = _52_736.iface; admitted_iface = _52_736.admitted_iface})
in ((unique_name any_val exclude_if this_env lid) && (unique_typ_name this_env lid))))


let gen_bvd = (fun _52_13 -> (match (_52_13) with
| Binding_typ_var (id) -> begin
(let _141_600 = (let _141_599 = (let _141_598 = (FStar_Absyn_Util.genident (Some (id.FStar_Ident.idRange)))
in (id, _141_598))
in (FStar_Absyn_Util.mkbvd _141_599))
in FStar_Util.Inl (_141_600))
end
| Binding_var (id) -> begin
(let _141_603 = (let _141_602 = (let _141_601 = (FStar_Absyn_Util.genident (Some (id.FStar_Ident.idRange)))
in (id, _141_601))
in (FStar_Absyn_Util.mkbvd _141_602))
in FStar_Util.Inr (_141_603))
end
| _52_745 -> begin
(FStar_All.failwith "Tried to generate a bound variable for a type constructor")
end))


let push_bvvdef : env  ->  FStar_Absyn_Syntax.bvvdef  ->  env = (fun env x -> (

let b = Binding_var (x.FStar_Absyn_Syntax.ppname)
in (

let _52_749 = env
in {curmodule = _52_749.curmodule; modules = _52_749.modules; open_namespaces = _52_749.open_namespaces; modul_abbrevs = _52_749.modul_abbrevs; sigaccum = _52_749.sigaccum; localbindings = ((FStar_Util.Inr (x), b))::env.localbindings; recbindings = _52_749.recbindings; phase = _52_749.phase; sigmap = _52_749.sigmap; default_result_effect = _52_749.default_result_effect; iface = _52_749.iface; admitted_iface = _52_749.admitted_iface})))


let push_btvdef : env  ->  FStar_Absyn_Syntax.btvdef  ->  env = (fun env x -> (

let b = Binding_typ_var (x.FStar_Absyn_Syntax.ppname)
in (

let _52_754 = env
in {curmodule = _52_754.curmodule; modules = _52_754.modules; open_namespaces = _52_754.open_namespaces; modul_abbrevs = _52_754.modul_abbrevs; sigaccum = _52_754.sigaccum; localbindings = ((FStar_Util.Inl (x), b))::env.localbindings; recbindings = _52_754.recbindings; phase = _52_754.phase; sigmap = _52_754.sigmap; default_result_effect = _52_754.default_result_effect; iface = _52_754.iface; admitted_iface = _52_754.admitted_iface})))


let push_local_binding : env  ->  binding  ->  (env * (FStar_Absyn_Syntax.btvdef, FStar_Absyn_Syntax.bvvdef) FStar_Util.either) = (fun env b -> (

let bvd = (gen_bvd b)
in ((

let _52_759 = env
in {curmodule = _52_759.curmodule; modules = _52_759.modules; open_namespaces = _52_759.open_namespaces; modul_abbrevs = _52_759.modul_abbrevs; sigaccum = _52_759.sigaccum; localbindings = ((bvd, b))::env.localbindings; recbindings = _52_759.recbindings; phase = _52_759.phase; sigmap = _52_759.sigmap; default_result_effect = _52_759.default_result_effect; iface = _52_759.iface; admitted_iface = _52_759.admitted_iface}), bvd)))


let push_local_tbinding : env  ->  FStar_Ident.ident  ->  (env * FStar_Absyn_Syntax.btvdef) = (fun env a -> (match ((push_local_binding env (Binding_typ_var (a)))) with
| (env, FStar_Util.Inl (x)) -> begin
(env, x)
end
| _52_768 -> begin
(FStar_All.failwith "impossible")
end))


let push_local_vbinding : env  ->  FStar_Ident.ident  ->  (env * FStar_Absyn_Syntax.bvvdef) = (fun env b -> (match ((push_local_binding env (Binding_var (b)))) with
| (env, FStar_Util.Inr (x)) -> begin
(env, x)
end
| _52_776 -> begin
(FStar_All.failwith "impossible")
end))


let push_rec_binding : env  ->  binding  ->  env = (fun env b -> (match (b) with
| (Binding_let (lid)) | (Binding_tycon (lid)) -> begin
if (unique false true env lid) then begin
(

let _52_782 = env
in {curmodule = _52_782.curmodule; modules = _52_782.modules; open_namespaces = _52_782.open_namespaces; modul_abbrevs = _52_782.modul_abbrevs; sigaccum = _52_782.sigaccum; localbindings = _52_782.localbindings; recbindings = (b)::env.recbindings; phase = _52_782.phase; sigmap = _52_782.sigmap; default_result_effect = _52_782.default_result_effect; iface = _52_782.iface; admitted_iface = _52_782.admitted_iface})
end else begin
(Prims.raise (FStar_Absyn_Syntax.Error (((Prims.strcat "Duplicate top-level names " lid.FStar_Ident.str), (FStar_Ident.range_of_lid lid)))))
end
end
| _52_785 -> begin
(FStar_All.failwith "Unexpected rec_binding")
end))


let push_sigelt : env  ->  FStar_Absyn_Syntax.sigelt  ->  env = (fun env s -> (

let err = (fun l -> (

let sopt = (let _141_634 = (sigmap env)
in (FStar_Util.smap_try_find _141_634 l.FStar_Ident.str))
in (

let r = (match (sopt) with
| Some (se, _52_793) -> begin
(match ((let _141_635 = (FStar_Absyn_Util.lids_of_sigelt se)
in (FStar_Util.find_opt (FStar_Ident.lid_equals l) _141_635))) with
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
in (let _141_638 = (let _141_637 = (let _141_636 = (FStar_Util.format2 "Duplicate top-level names [%s]; previously declared at %s" (FStar_Ident.text_of_lid l) r)
in (_141_636, (FStar_Ident.range_of_lid l)))
in FStar_Absyn_Syntax.Error (_141_637))
in (Prims.raise _141_638)))))
in (

let env = (

let _52_811 = (match (s) with
| FStar_Absyn_Syntax.Sig_let (_52_802) -> begin
(false, true)
end
| FStar_Absyn_Syntax.Sig_bundle (_52_805) -> begin
(true, true)
end
| _52_808 -> begin
(false, false)
end)
in (match (_52_811) with
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

let _52_815 = (extract_record env s)
in (

let _52_817 = env
in {curmodule = _52_817.curmodule; modules = _52_817.modules; open_namespaces = _52_817.open_namespaces; modul_abbrevs = _52_817.modul_abbrevs; sigaccum = (s)::env.sigaccum; localbindings = _52_817.localbindings; recbindings = _52_817.recbindings; phase = _52_817.phase; sigmap = _52_817.sigmap; default_result_effect = _52_817.default_result_effect; iface = _52_817.iface; admitted_iface = _52_817.admitted_iface}))
end
| Some (l) -> begin
(err l)
end))
end))
in (

let _52_836 = (match (s) with
| FStar_Absyn_Syntax.Sig_bundle (ses, _52_824, _52_826, _52_828) -> begin
(let _141_642 = (FStar_List.map (fun se -> (let _141_641 = (FStar_Absyn_Util.lids_of_sigelt se)
in (_141_641, se))) ses)
in (env, _141_642))
end
| _52_833 -> begin
(let _141_645 = (let _141_644 = (let _141_643 = (FStar_Absyn_Util.lids_of_sigelt s)
in (_141_643, s))
in (_141_644)::[])
in (env, _141_645))
end)
in (match (_52_836) with
| (env, lss) -> begin
(

let _52_841 = (FStar_All.pipe_right lss (FStar_List.iter (fun _52_839 -> (match (_52_839) with
| (lids, se) -> begin
(FStar_All.pipe_right lids (FStar_List.iter (fun lid -> (let _141_648 = (sigmap env)
in (FStar_Util.smap_add _141_648 lid.FStar_Ident.str (se, (env.iface && (not (env.admitted_iface)))))))))
end))))
in env)
end)))))


let push_namespace : env  ->  FStar_Ident.lident  ->  env = (fun env lid -> (

let _52_845 = env
in {curmodule = _52_845.curmodule; modules = _52_845.modules; open_namespaces = (lid)::env.open_namespaces; modul_abbrevs = _52_845.modul_abbrevs; sigaccum = _52_845.sigaccum; localbindings = _52_845.localbindings; recbindings = _52_845.recbindings; phase = _52_845.phase; sigmap = _52_845.sigmap; default_result_effect = _52_845.default_result_effect; iface = _52_845.iface; admitted_iface = _52_845.admitted_iface}))


let push_module_abbrev : env  ->  FStar_Ident.ident  ->  FStar_Ident.lident  ->  env = (fun env x l -> if (FStar_All.pipe_right env.modul_abbrevs (FStar_Util.for_some (fun _52_853 -> (match (_52_853) with
| (y, _52_852) -> begin
(x.FStar_Ident.idText = y.FStar_Ident.idText)
end)))) then begin
(let _141_662 = (let _141_661 = (let _141_660 = (FStar_Util.format1 "Module %s is already defined" x.FStar_Ident.idText)
in (_141_660, x.FStar_Ident.idRange))
in FStar_Absyn_Syntax.Error (_141_661))
in (Prims.raise _141_662))
end else begin
(

let _52_854 = env
in {curmodule = _52_854.curmodule; modules = _52_854.modules; open_namespaces = _52_854.open_namespaces; modul_abbrevs = ((x, l))::env.modul_abbrevs; sigaccum = _52_854.sigaccum; localbindings = _52_854.localbindings; recbindings = _52_854.recbindings; phase = _52_854.phase; sigmap = _52_854.sigmap; default_result_effect = _52_854.default_result_effect; iface = _52_854.iface; admitted_iface = _52_854.admitted_iface})
end)


let is_type_lid : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let aux = (fun _52_859 -> (match (()) with
| () -> begin
(match ((try_lookup_typ_name' false env lid)) with
| Some (_52_861) -> begin
true
end
| _52_864 -> begin
false
end)
end))
in if (lid.FStar_Ident.ns = []) then begin
(match ((try_lookup_id env lid.FStar_Ident.ident)) with
| Some (_52_866) -> begin
false
end
| _52_869 -> begin
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

let _52_880 = (let _141_676 = (let _141_675 = (FStar_Range.string_of_range (FStar_Ident.range_of_lid l))
in (let _141_674 = (FStar_Absyn_Print.sli l)
in (FStar_Util.format2 "%s: Warning: Admitting %s without a definition\n" _141_675 _141_674)))
in (FStar_Util.print_string _141_676))
in (let _141_677 = (sigmap env)
in (FStar_Util.smap_add _141_677 l.FStar_Ident.str (FStar_Absyn_Syntax.Sig_val_decl ((l, t, (FStar_Absyn_Syntax.Assumption)::quals, r)), false))))
end
| Some (_52_883) -> begin
()
end)
end
| _52_886 -> begin
()
end)))))


let finish : env  ->  FStar_Absyn_Syntax.modul  ->  env = (fun env modul -> (

let _52_924 = (FStar_All.pipe_right modul.FStar_Absyn_Syntax.declarations (FStar_List.iter (fun _52_15 -> (match (_52_15) with
| FStar_Absyn_Syntax.Sig_bundle (ses, quals, _52_893, _52_895) -> begin
if (FStar_List.contains FStar_Absyn_Syntax.Private quals) then begin
(FStar_All.pipe_right ses (FStar_List.iter (fun _52_14 -> (match (_52_14) with
| FStar_Absyn_Syntax.Sig_datacon (lid, _52_901, _52_903, _52_905, _52_907, _52_909) -> begin
(let _141_684 = (sigmap env)
in (FStar_Util.smap_remove _141_684 lid.FStar_Ident.str))
end
| _52_913 -> begin
()
end))))
end else begin
()
end
end
| FStar_Absyn_Syntax.Sig_val_decl (lid, _52_916, quals, _52_919) -> begin
if (FStar_List.contains FStar_Absyn_Syntax.Private quals) then begin
(let _141_685 = (sigmap env)
in (FStar_Util.smap_remove _141_685 lid.FStar_Ident.str))
end else begin
()
end
end
| _52_923 -> begin
()
end))))
in (

let _52_926 = env
in {curmodule = None; modules = ((modul.FStar_Absyn_Syntax.name, modul))::env.modules; open_namespaces = []; modul_abbrevs = []; sigaccum = []; localbindings = []; recbindings = []; phase = FStar_Parser_AST.Un; sigmap = _52_926.sigmap; default_result_effect = _52_926.default_result_effect; iface = _52_926.iface; admitted_iface = _52_926.admitted_iface})))


let push : env  ->  env = (fun env -> (

let _52_929 = (push_record_cache ())
in (

let _52_931 = env
in (let _141_690 = (let _141_689 = (let _141_688 = (sigmap env)
in (FStar_Util.smap_copy _141_688))
in (_141_689)::env.sigmap)
in {curmodule = _52_931.curmodule; modules = _52_931.modules; open_namespaces = _52_931.open_namespaces; modul_abbrevs = _52_931.modul_abbrevs; sigaccum = _52_931.sigaccum; localbindings = _52_931.localbindings; recbindings = _52_931.recbindings; phase = _52_931.phase; sigmap = _141_690; default_result_effect = _52_931.default_result_effect; iface = _52_931.iface; admitted_iface = _52_931.admitted_iface}))))


let mark : env  ->  env = (fun env -> (push env))


let reset_mark : env  ->  env = (fun env -> (

let _52_935 = env
in (let _141_695 = (FStar_List.tl env.sigmap)
in {curmodule = _52_935.curmodule; modules = _52_935.modules; open_namespaces = _52_935.open_namespaces; modul_abbrevs = _52_935.modul_abbrevs; sigaccum = _52_935.sigaccum; localbindings = _52_935.localbindings; recbindings = _52_935.recbindings; phase = _52_935.phase; sigmap = _141_695; default_result_effect = _52_935.default_result_effect; iface = _52_935.iface; admitted_iface = _52_935.admitted_iface})))


let commit_mark : env  ->  env = (fun env -> (match (env.sigmap) with
| hd::_52_940::tl -> begin
(

let _52_944 = env
in {curmodule = _52_944.curmodule; modules = _52_944.modules; open_namespaces = _52_944.open_namespaces; modul_abbrevs = _52_944.modul_abbrevs; sigaccum = _52_944.sigaccum; localbindings = _52_944.localbindings; recbindings = _52_944.recbindings; phase = _52_944.phase; sigmap = (hd)::tl; default_result_effect = _52_944.default_result_effect; iface = _52_944.iface; admitted_iface = _52_944.admitted_iface})
end
| _52_947 -> begin
(FStar_All.failwith "Impossible")
end))


let pop : env  ->  env = (fun env -> (match (env.sigmap) with
| _52_951::maps -> begin
(

let _52_953 = (pop_record_cache ())
in (

let _52_955 = env
in {curmodule = _52_955.curmodule; modules = _52_955.modules; open_namespaces = _52_955.open_namespaces; modul_abbrevs = _52_955.modul_abbrevs; sigaccum = _52_955.sigaccum; localbindings = _52_955.localbindings; recbindings = _52_955.recbindings; phase = _52_955.phase; sigmap = maps; default_result_effect = _52_955.default_result_effect; iface = _52_955.iface; admitted_iface = _52_955.admitted_iface}))
end
| _52_958 -> begin
(FStar_All.failwith "No more modules to pop")
end))


let export_interface : FStar_Ident.lident  ->  env  ->  env = (fun m env -> (

let sigelt_in_m = (fun se -> (match ((FStar_Absyn_Util.lids_of_sigelt se)) with
| l::_52_964 -> begin
(l.FStar_Ident.nsstr = m.FStar_Ident.str)
end
| _52_968 -> begin
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

let _52_991 = (FStar_All.pipe_right keys (FStar_List.iter (fun k -> (match ((FStar_Util.smap_try_find sm' k)) with
| Some (se, true) when (sigelt_in_m se) -> begin
(

let _52_978 = (FStar_Util.smap_remove sm' k)
in (

let se = (match (se) with
| FStar_Absyn_Syntax.Sig_val_decl (l, t, q, r) -> begin
FStar_Absyn_Syntax.Sig_val_decl ((l, t, (FStar_Absyn_Syntax.Assumption)::q, r))
end
| _52_987 -> begin
se
end)
in (FStar_Util.smap_add sm' k (se, false))))
end
| _52_990 -> begin
()
end))))
in env)))))))


let finish_module_or_interface : env  ->  FStar_Absyn_Syntax.modul  ->  env = (fun env modul -> (

let _52_995 = if (not (modul.FStar_Absyn_Syntax.is_interface)) then begin
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
in (

let _52_1004 = env
in {curmodule = Some (mname); modules = _52_1004.modules; open_namespaces = open_ns; modul_abbrevs = _52_1004.modul_abbrevs; sigaccum = _52_1004.sigaccum; localbindings = _52_1004.localbindings; recbindings = _52_1004.recbindings; phase = _52_1004.phase; sigmap = env.sigmap; default_result_effect = _52_1004.default_result_effect; iface = intf; admitted_iface = admitted})))
in (match ((FStar_All.pipe_right env.modules (FStar_Util.find_opt (fun _52_1009 -> (match (_52_1009) with
| (l, _52_1008) -> begin
(FStar_Ident.lid_equals l mname)
end))))) with
| None -> begin
((prep env), false)
end
| Some (_52_1012, m) -> begin
(let _141_724 = (let _141_723 = (let _141_722 = (FStar_Util.format1 "Duplicate module or interface name: %s" mname.FStar_Ident.str)
in (_141_722, (FStar_Ident.range_of_lid mname)))
in FStar_Absyn_Syntax.Error (_141_723))
in (Prims.raise _141_724))
end)))


let enter_monad_scope : env  ->  FStar_Ident.ident  ->  env = (fun env mname -> (

let curmod = (current_module env)
in (

let mscope = (FStar_Ident.lid_of_ids (FStar_List.append curmod.FStar_Ident.ns ((curmod.FStar_Ident.ident)::(mname)::[])))
in (

let _52_1020 = env
in {curmodule = Some (mscope); modules = _52_1020.modules; open_namespaces = (curmod)::env.open_namespaces; modul_abbrevs = _52_1020.modul_abbrevs; sigaccum = _52_1020.sigaccum; localbindings = _52_1020.localbindings; recbindings = _52_1020.recbindings; phase = _52_1020.phase; sigmap = _52_1020.sigmap; default_result_effect = _52_1020.default_result_effect; iface = _52_1020.iface; admitted_iface = _52_1020.admitted_iface}))))


let exit_monad_scope : env  ->  env  ->  env = (fun env0 env -> (

let _52_1024 = env
in {curmodule = env0.curmodule; modules = _52_1024.modules; open_namespaces = env0.open_namespaces; modul_abbrevs = _52_1024.modul_abbrevs; sigaccum = _52_1024.sigaccum; localbindings = _52_1024.localbindings; recbindings = _52_1024.recbindings; phase = _52_1024.phase; sigmap = _52_1024.sigmap; default_result_effect = _52_1024.default_result_effect; iface = _52_1024.iface; admitted_iface = _52_1024.admitted_iface}))


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
(let _141_739 = (FStar_Range.string_of_range r)
in (FStar_Util.format1 "(Possible clash with related name at %s)" _141_739))
end)
in (let _141_742 = (let _141_741 = (let _141_740 = (FStar_Util.format2 "Identifier not found: [%s] %s" (FStar_Ident.text_of_lid lid) msg)
in (_141_740, (FStar_Ident.range_of_lid lid)))
in FStar_Absyn_Syntax.Error (_141_741))
in (Prims.raise _141_742))))
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




