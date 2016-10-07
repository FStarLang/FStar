
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
| Binding_typ_var (_61_18) -> begin
_61_18
end))


let ___Binding_var____0 = (fun projectee -> (match (projectee) with
| Binding_var (_61_21) -> begin
_61_21
end))


let ___Binding_let____0 = (fun projectee -> (match (projectee) with
| Binding_let (_61_24) -> begin
_61_24
end))


let ___Binding_tycon____0 = (fun projectee -> (match (projectee) with
| Binding_tycon (_61_27) -> begin
_61_27
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
| OSig (_61_43) -> begin
_61_43
end))


let ___OLet____0 = (fun projectee -> (match (projectee) with
| OLet (_61_46) -> begin
_61_46
end))


let ___ORec____0 = (fun projectee -> (match (projectee) with
| ORec (_61_49) -> begin
_61_49
end))


let range_of_occurrence : occurrence  ->  FStar_Range.range = (fun _61_1 -> (match (_61_1) with
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
| Exp_name (_61_58) -> begin
_61_58
end))


let ___Typ_name____0 = (fun projectee -> (match (projectee) with
| Typ_name (_61_61) -> begin
_61_61
end))


let ___Eff_name____0 = (fun projectee -> (match (projectee) with
| Eff_name (_61_64) -> begin
_61_64
end))


let ___Knd_name____0 = (fun projectee -> (match (projectee) with
| Knd_name (_61_67) -> begin
_61_67
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


let qual : FStar_Ident.lident  ->  FStar_Ident.ident  ->  FStar_Ident.lident = (fun lid id -> (let _155_230 = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns ((lid.FStar_Ident.ident)::(id)::[])))
in (FStar_Ident.set_lid_range _155_230 id.FStar_Ident.idRange)))


let qualify : env  ->  FStar_Ident.ident  ->  FStar_Ident.lident = (fun env id -> (let _155_235 = (current_module env)
in (qual _155_235 id)))


let qualify_lid : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (

let cur = (current_module env)
in (let _155_240 = (FStar_Ident.lid_of_ids (FStar_List.append cur.FStar_Ident.ns (FStar_List.append ((cur.FStar_Ident.ident)::[]) (FStar_List.append lid.FStar_Ident.ns ((lid.FStar_Ident.ident)::[])))))
in (FStar_Ident.set_lid_range _155_240 (FStar_Ident.range_of_lid lid)))))


let new_sigmap = (fun _61_89 -> (match (()) with
| () -> begin
(FStar_Util.smap_create (Prims.parse_int "100"))
end))


let empty_env : Prims.unit  ->  env = (fun _61_90 -> (match (()) with
| () -> begin
(let _155_245 = (let _155_244 = (new_sigmap ())
in (_155_244)::[])
in {curmodule = None; modules = []; open_namespaces = []; modul_abbrevs = []; sigaccum = []; localbindings = []; recbindings = []; phase = FStar_Parser_AST.Un; sigmap = _155_245; default_result_effect = FStar_Absyn_Util.ml_comp; iface = false; admitted_iface = false})
end))


let sigmap : env  ->  (FStar_Absyn_Syntax.sigelt * Prims.bool) FStar_Util.smap = (fun env -> (FStar_List.hd env.sigmap))


let default_total : env  ->  env = (fun env -> (

let _61_93 = env
in {curmodule = _61_93.curmodule; modules = _61_93.modules; open_namespaces = _61_93.open_namespaces; modul_abbrevs = _61_93.modul_abbrevs; sigaccum = _61_93.sigaccum; localbindings = _61_93.localbindings; recbindings = _61_93.recbindings; phase = _61_93.phase; sigmap = _61_93.sigmap; default_result_effect = (fun t _61_96 -> (FStar_Absyn_Syntax.mk_Total t)); iface = _61_93.iface; admitted_iface = _61_93.admitted_iface}))


let default_ml : env  ->  env = (fun env -> (

let _61_99 = env
in {curmodule = _61_99.curmodule; modules = _61_99.modules; open_namespaces = _61_99.open_namespaces; modul_abbrevs = _61_99.modul_abbrevs; sigaccum = _61_99.sigaccum; localbindings = _61_99.localbindings; recbindings = _61_99.recbindings; phase = _61_99.phase; sigmap = _61_99.sigmap; default_result_effect = FStar_Absyn_Util.ml_comp; iface = _61_99.iface; admitted_iface = _61_99.admitted_iface}))


let range_of_binding : binding  ->  FStar_Range.range = (fun _61_2 -> (match (_61_2) with
| (Binding_typ_var (id)) | (Binding_var (id)) -> begin
id.FStar_Ident.idRange
end
| (Binding_let (lid)) | (Binding_tycon (lid)) -> begin
(FStar_Ident.range_of_lid lid)
end))


let try_lookup_typ_var : env  ->  FStar_Ident.ident  ->  FStar_Absyn_Syntax.typ Prims.option = (fun env id -> (

let fopt = (FStar_List.tryFind (fun _61_113 -> (match (_61_113) with
| (_61_111, b) -> begin
(match (b) with
| (Binding_typ_var (id')) | (Binding_var (id')) -> begin
(id.FStar_Ident.idText = id'.FStar_Ident.idText)
end
| _61_118 -> begin
false
end)
end)) env.localbindings)
in (match (fopt) with
| Some (FStar_Util.Inl (bvd), Binding_typ_var (_61_123)) -> begin
(let _155_261 = (FStar_Absyn_Util.bvd_to_typ (FStar_Absyn_Util.set_bvd_range bvd id.FStar_Ident.idRange) FStar_Absyn_Syntax.kun)
in Some (_155_261))
end
| _61_128 -> begin
None
end)))


let resolve_in_open_namespaces' = (fun env lid finder -> (

let aux = (fun namespaces -> (match ((finder lid)) with
| Some (r) -> begin
Some (r)
end
| _61_138 -> begin
(

let ids = (FStar_Ident.ids_of_lid lid)
in (FStar_Util.find_map namespaces (fun ns -> (

let full_name = (FStar_Ident.lid_of_ids (FStar_List.append (FStar_Ident.ids_of_lid ns) ids))
in (finder full_name)))))
end))
in (let _155_272 = (let _155_271 = (current_module env)
in (_155_271)::env.open_namespaces)
in (aux _155_272))))


let expand_module_abbrevs : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (match (lid.FStar_Ident.ns) with
| (id)::[] -> begin
(match ((FStar_All.pipe_right env.modul_abbrevs (FStar_List.tryFind (fun _61_149 -> (match (_61_149) with
| (id', _61_148) -> begin
(id.FStar_Ident.idText = id'.FStar_Ident.idText)
end))))) with
| None -> begin
lid
end
| Some (_61_152, lid') -> begin
(FStar_Ident.lid_of_ids (FStar_List.append (FStar_Ident.ids_of_lid lid') ((lid.FStar_Ident.ident)::[])))
end)
end
| _61_157 -> begin
lid
end))


let resolve_in_open_namespaces = (fun env lid finder -> (let _155_288 = (expand_module_abbrevs env lid)
in (resolve_in_open_namespaces' env _155_288 finder)))


let unmangleMap : (Prims.string * Prims.string) Prims.list = ((("op_ColonColon"), ("Cons")))::((("not"), ("op_Negation")))::[]


let unmangleOpName : FStar_Ident.ident  ->  FStar_Ident.lident Prims.option = (fun id -> (FStar_Util.find_map unmangleMap (fun _61_165 -> (match (_61_165) with
| (x, y) -> begin
if (id.FStar_Ident.idText = x) then begin
(let _155_292 = (FStar_Ident.lid_of_path (("Prims")::(y)::[]) id.FStar_Ident.idRange)
in Some (_155_292))
end else begin
None
end
end))))


let try_lookup_id' : env  ->  FStar_Ident.ident  ->  (FStar_Ident.lident * FStar_Absyn_Syntax.exp) Prims.option = (fun env id -> (match ((unmangleOpName id)) with
| Some (l) -> begin
(let _155_298 = (let _155_297 = (FStar_Absyn_Syntax.mk_Exp_fvar (((FStar_Absyn_Util.fv l)), (None)) None id.FStar_Ident.idRange)
in ((l), (_155_297)))
in Some (_155_298))
end
| _61_171 -> begin
(

let found = (FStar_Util.find_map env.localbindings (fun _61_3 -> (match (_61_3) with
| (FStar_Util.Inl (_61_174), Binding_typ_var (id')) when (id'.FStar_Ident.idText = id.FStar_Ident.idText) -> begin
Some (FStar_Util.Inl (()))
end
| (FStar_Util.Inr (bvd), Binding_var (id')) when (id'.FStar_Ident.idText = id.FStar_Ident.idText) -> begin
(let _155_303 = (let _155_302 = (let _155_301 = (FStar_Ident.lid_of_ids ((id')::[]))
in (let _155_300 = (FStar_Absyn_Util.bvd_to_exp (FStar_Absyn_Util.set_bvd_range bvd id.FStar_Ident.idRange) FStar_Absyn_Syntax.tun)
in ((_155_301), (_155_300))))
in FStar_Util.Inr (_155_302))
in Some (_155_303))
end
| _61_185 -> begin
None
end)))
in (match (found) with
| Some (FStar_Util.Inr (x)) -> begin
Some (x)
end
| _61_191 -> begin
None
end))
end))


let try_lookup_id : env  ->  FStar_Ident.ident  ->  FStar_Absyn_Syntax.exp Prims.option = (fun env id -> (match ((try_lookup_id' env id)) with
| Some (_61_195, e) -> begin
Some (e)
end
| None -> begin
None
end))


let fv_qual_of_se : FStar_Absyn_Syntax.sigelt  ->  FStar_Absyn_Syntax.fv_qual Prims.option = (fun _61_5 -> (match (_61_5) with
| FStar_Absyn_Syntax.Sig_datacon (_61_202, _61_204, (l, _61_207, _61_209), quals, _61_213, _61_215) -> begin
(

let qopt = (FStar_Util.find_map quals (fun _61_4 -> (match (_61_4) with
| FStar_Absyn_Syntax.RecordConstructor (fs) -> begin
Some (FStar_Absyn_Syntax.Record_ctor (((l), (fs))))
end
| _61_222 -> begin
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
| FStar_Absyn_Syntax.Sig_val_decl (_61_227, _61_229, quals, _61_232) -> begin
None
end
| _61_236 -> begin
None
end))


let try_lookup_name : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  foundname Prims.option = (fun any_val exclude_interf env lid -> (

let find_in_sig = (fun lid -> (match ((let _155_321 = (sigmap env)
in (FStar_Util.smap_try_find _155_321 lid.FStar_Ident.str))) with
| Some (_61_244, true) when exclude_interf -> begin
None
end
| None -> begin
None
end
| Some (se, _61_251) -> begin
(match (se) with
| (FStar_Absyn_Syntax.Sig_typ_abbrev (_)) | (FStar_Absyn_Syntax.Sig_tycon (_)) -> begin
(let _155_324 = (let _155_323 = (let _155_322 = (FStar_Absyn_Util.ftv lid FStar_Absyn_Syntax.kun)
in ((OSig (se)), (_155_322)))
in Typ_name (_155_323))
in Some (_155_324))
end
| FStar_Absyn_Syntax.Sig_kind_abbrev (_61_261) -> begin
Some (Knd_name (((OSig (se)), (lid))))
end
| FStar_Absyn_Syntax.Sig_new_effect (ne, _61_265) -> begin
Some (Eff_name (((OSig (se)), ((FStar_Ident.set_lid_range ne.FStar_Absyn_Syntax.mname (FStar_Ident.range_of_lid lid))))))
end
| FStar_Absyn_Syntax.Sig_effect_abbrev (_61_269) -> begin
Some (Eff_name (((OSig (se)), (lid))))
end
| FStar_Absyn_Syntax.Sig_datacon (_61_272) -> begin
(let _155_328 = (let _155_327 = (let _155_326 = (let _155_325 = (fv_qual_of_se se)
in (FStar_Absyn_Util.fvar _155_325 lid (FStar_Ident.range_of_lid lid)))
in ((OSig (se)), (_155_326)))
in Exp_name (_155_327))
in Some (_155_328))
end
| FStar_Absyn_Syntax.Sig_let (_61_275) -> begin
(let _155_331 = (let _155_330 = (let _155_329 = (FStar_Absyn_Util.fvar None lid (FStar_Ident.range_of_lid lid))
in ((OSig (se)), (_155_329)))
in Exp_name (_155_330))
in Some (_155_331))
end
| FStar_Absyn_Syntax.Sig_val_decl (_61_278, _61_280, quals, _61_283) -> begin
if (any_val || (FStar_All.pipe_right quals (FStar_Util.for_some (fun _61_6 -> (match (_61_6) with
| FStar_Absyn_Syntax.Assumption -> begin
true
end
| _61_289 -> begin
false
end))))) then begin
(let _155_336 = (let _155_335 = (let _155_334 = (let _155_333 = (fv_qual_of_se se)
in (FStar_Absyn_Util.fvar _155_333 lid (FStar_Ident.range_of_lid lid)))
in ((OSig (se)), (_155_334)))
in Exp_name (_155_335))
in Some (_155_336))
end else begin
None
end
end
| _61_291 -> begin
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
in (FStar_Util.find_map env.recbindings (fun _61_7 -> (match (_61_7) with
| Binding_let (l) when (FStar_Ident.lid_equals l recname) -> begin
(let _155_340 = (let _155_339 = (let _155_338 = (FStar_Absyn_Util.fvar None recname (FStar_Ident.range_of_lid recname))
in ((ORec (l)), (_155_338)))
in Exp_name (_155_339))
in Some (_155_340))
end
| Binding_tycon (l) when (FStar_Ident.lid_equals l recname) -> begin
(let _155_343 = (let _155_342 = (let _155_341 = (FStar_Absyn_Util.ftv recname FStar_Absyn_Syntax.kun)
in ((ORec (l)), (_155_341)))
in Typ_name (_155_342))
in Some (_155_343))
end
| _61_305 -> begin
None
end))))
end)
end
| _61_307 -> begin
None
end)
in (match (found_id) with
| Some (_61_310) -> begin
found_id
end
| _61_313 -> begin
(resolve_in_open_namespaces env lid find_in_sig)
end))))


let try_lookup_typ_name' : Prims.bool  ->  env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.typ Prims.option = (fun exclude_interf env lid -> (match ((try_lookup_name true exclude_interf env lid)) with
| Some (Typ_name (_61_318, t)) -> begin
Some (t)
end
| Some (Eff_name (_61_324, l)) -> begin
(let _155_350 = (FStar_Absyn_Util.ftv l FStar_Absyn_Syntax.mk_Kind_unknown)
in Some (_155_350))
end
| _61_330 -> begin
None
end))


let try_lookup_typ_name : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.typ Prims.option = (fun env l -> (try_lookup_typ_name' (not (env.iface)) env l))


let try_lookup_effect_name' : Prims.bool  ->  env  ->  FStar_Ident.lident  ->  (occurrence * FStar_Ident.lident) Prims.option = (fun exclude_interf env lid -> (match ((try_lookup_name true exclude_interf env lid)) with
| Some (Eff_name (o, l)) -> begin
Some (((o), (l)))
end
| _61_342 -> begin
None
end))


let try_lookup_effect_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env l -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some (o, l) -> begin
Some (l)
end
| _61_350 -> begin
None
end))


let try_lookup_effect_defn : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.eff_decl Prims.option = (fun env l -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some (OSig (FStar_Absyn_Syntax.Sig_new_effect (ne, _61_355)), _61_360) -> begin
Some (ne)
end
| _61_364 -> begin
None
end))


let is_effect_name : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((try_lookup_effect_name env lid)) with
| None -> begin
false
end
| Some (_61_369) -> begin
true
end))


let try_resolve_typ_abbrev : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.typ Prims.option = (fun env lid -> (

let find_in_sig = (fun lid -> (match ((let _155_379 = (sigmap env)
in (FStar_Util.smap_try_find _155_379 lid.FStar_Ident.str))) with
| Some (FStar_Absyn_Syntax.Sig_typ_abbrev (lid, tps, k, def, _61_380, _61_382), _61_386) -> begin
(

let t = (let _155_382 = (let _155_381 = (let _155_380 = (FStar_Absyn_Util.close_with_lam tps def)
in ((_155_380), (lid)))
in FStar_Absyn_Syntax.Meta_named (_155_381))
in (FStar_Absyn_Syntax.mk_Typ_meta _155_382))
in Some (t))
end
| _61_391 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))


let lookup_letbinding_quals : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.qualifier Prims.list = (fun env lid -> (

let find_in_sig = (fun lid -> (match ((let _155_389 = (sigmap env)
in (FStar_Util.smap_try_find _155_389 lid.FStar_Ident.str))) with
| Some (FStar_Absyn_Syntax.Sig_val_decl (lid, _61_398, quals, _61_401), _61_405) -> begin
Some (quals)
end
| _61_409 -> begin
None
end))
in (match ((resolve_in_open_namespaces env lid find_in_sig)) with
| Some (quals) -> begin
quals
end
| _61_413 -> begin
[]
end)))


let try_lookup_module : env  ->  Prims.string Prims.list  ->  FStar_Absyn_Syntax.modul Prims.option = (fun env path -> (match ((FStar_List.tryFind (fun _61_418 -> (match (_61_418) with
| (mlid, modul) -> begin
((FStar_Ident.path_of_lid mlid) = path)
end)) env.modules)) with
| Some (_61_420, modul) -> begin
Some (modul)
end
| None -> begin
None
end))


let try_lookup_let : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.exp Prims.option = (fun env lid -> (

let find_in_sig = (fun lid -> (match ((let _155_401 = (sigmap env)
in (FStar_Util.smap_try_find _155_401 lid.FStar_Ident.str))) with
| Some (FStar_Absyn_Syntax.Sig_let (_61_430), _61_433) -> begin
(let _155_402 = (FStar_Absyn_Util.fvar None lid (FStar_Ident.range_of_lid lid))
in Some (_155_402))
end
| _61_437 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))


let try_lookup_lid' : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.exp Prims.option = (fun any_val exclude_interf env lid -> (match ((try_lookup_name any_val exclude_interf env lid)) with
| Some (Exp_name (_61_443, e)) -> begin
Some (e)
end
| _61_449 -> begin
None
end))


let try_lookup_lid : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.exp Prims.option = (fun env l -> (try_lookup_lid' env.iface false env l))


let try_lookup_datacon : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.typ FStar_Absyn_Syntax.var Prims.option = (fun env lid -> (

let find_in_sig = (fun lid -> (match ((let _155_421 = (sigmap env)
in (FStar_Util.smap_try_find _155_421 lid.FStar_Ident.str))) with
| Some (FStar_Absyn_Syntax.Sig_val_decl (_61_457, _61_459, quals, _61_462), _61_466) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _61_8 -> (match (_61_8) with
| FStar_Absyn_Syntax.Assumption -> begin
true
end
| _61_472 -> begin
false
end)))) then begin
Some ((FStar_Absyn_Util.fv lid))
end else begin
None
end
end
| Some (FStar_Absyn_Syntax.Sig_datacon (_61_474), _61_477) -> begin
Some ((FStar_Absyn_Util.fv lid))
end
| _61_481 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))


let find_all_datacons : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.list Prims.option = (fun env lid -> (

let find_in_sig = (fun lid -> (match ((let _155_429 = (sigmap env)
in (FStar_Util.smap_try_find _155_429 lid.FStar_Ident.str))) with
| Some (FStar_Absyn_Syntax.Sig_tycon (_61_487, _61_489, _61_491, _61_493, datas, _61_496, _61_498), _61_502) -> begin
Some (datas)
end
| _61_506 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))


let record_cache_aux : ((Prims.unit  ->  Prims.unit) * (Prims.unit  ->  Prims.unit) * (Prims.unit  ->  record_or_dc Prims.list) * (record_or_dc  ->  Prims.unit)) = (

let record_cache = (FStar_Util.mk_ref (([])::[]))
in (

let push = (fun _61_509 -> (match (()) with
| () -> begin
(let _155_443 = (let _155_442 = (let _155_440 = (FStar_ST.read record_cache)
in (FStar_List.hd _155_440))
in (let _155_441 = (FStar_ST.read record_cache)
in (_155_442)::_155_441))
in (FStar_ST.op_Colon_Equals record_cache _155_443))
end))
in (

let pop = (fun _61_511 -> (match (()) with
| () -> begin
(let _155_447 = (let _155_446 = (FStar_ST.read record_cache)
in (FStar_List.tl _155_446))
in (FStar_ST.op_Colon_Equals record_cache _155_447))
end))
in (

let peek = (fun _61_513 -> (match (()) with
| () -> begin
(let _155_450 = (FStar_ST.read record_cache)
in (FStar_List.hd _155_450))
end))
in (

let insert = (fun r -> (let _155_457 = (let _155_456 = (let _155_453 = (peek ())
in (r)::_155_453)
in (let _155_455 = (let _155_454 = (FStar_ST.read record_cache)
in (FStar_List.tl _155_454))
in (_155_456)::_155_455))
in (FStar_ST.op_Colon_Equals record_cache _155_457)))
in ((push), (pop), (peek), (insert)))))))


let push_record_cache : Prims.unit  ->  Prims.unit = (

let _61_523 = record_cache_aux
in (match (_61_523) with
| (push, _61_518, _61_520, _61_522) -> begin
push
end))


let pop_record_cache : Prims.unit  ->  Prims.unit = (

let _61_531 = record_cache_aux
in (match (_61_531) with
| (_61_525, pop, _61_528, _61_530) -> begin
pop
end))


let peek_record_cache : Prims.unit  ->  record_or_dc Prims.list = (

let _61_539 = record_cache_aux
in (match (_61_539) with
| (_61_533, _61_535, peek, _61_538) -> begin
peek
end))


let insert_record_cache : record_or_dc  ->  Prims.unit = (

let _61_547 = record_cache_aux
in (match (_61_547) with
| (_61_541, _61_543, _61_545, insert) -> begin
insert
end))


let extract_record : env  ->  FStar_Absyn_Syntax.sigelt  ->  Prims.unit = (fun e _61_12 -> (match (_61_12) with
| FStar_Absyn_Syntax.Sig_bundle (sigs, _61_552, _61_554, _61_556) -> begin
(

let is_rec = (FStar_Util.for_some (fun _61_9 -> (match (_61_9) with
| (FStar_Absyn_Syntax.RecordType (_)) | (FStar_Absyn_Syntax.RecordConstructor (_)) -> begin
true
end
| _61_567 -> begin
false
end)))
in (

let find_dc = (fun dc -> (FStar_All.pipe_right sigs (FStar_Util.find_opt (fun _61_10 -> (match (_61_10) with
| FStar_Absyn_Syntax.Sig_datacon (lid, _61_574, _61_576, _61_578, _61_580, _61_582) -> begin
(FStar_Ident.lid_equals dc lid)
end
| _61_586 -> begin
false
end)))))
in (FStar_All.pipe_right sigs (FStar_List.iter (fun _61_11 -> (match (_61_11) with
| FStar_Absyn_Syntax.Sig_tycon (typename, parms, _61_591, _61_593, (dc)::[], tags, _61_598) -> begin
(match ((let _155_528 = (find_dc dc)
in (FStar_All.pipe_left FStar_Util.must _155_528))) with
| FStar_Absyn_Syntax.Sig_datacon (constrname, t, _61_604, _61_606, _61_608, _61_610) -> begin
(

let formals = (match ((FStar_Absyn_Util.function_formals t)) with
| Some (x, _61_615) -> begin
x
end
| _61_619 -> begin
[]
end)
in (

let is_rec = (is_rec tags)
in (

let fields = (FStar_All.pipe_right formals (FStar_List.collect (fun b -> (match (b) with
| (FStar_Util.Inr (x), q) -> begin
if ((FStar_Absyn_Syntax.is_null_binder b) || (is_rec && (match (q) with
| Some (FStar_Absyn_Syntax.Implicit (_61_628)) -> begin
true
end
| _61_632 -> begin
false
end))) then begin
[]
end else begin
(let _155_532 = (let _155_531 = (let _155_530 = if is_rec then begin
(FStar_Absyn_Util.unmangle_field_name x.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ppname)
end else begin
x.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ppname
end
in (qual constrname _155_530))
in ((_155_531), (x.FStar_Absyn_Syntax.sort)))
in (_155_532)::[])
end
end
| _61_634 -> begin
[]
end))))
in (

let record = {typename = typename; constrname = constrname; parms = parms; fields = fields; is_record = is_rec}
in (insert_record_cache record)))))
end
| _61_638 -> begin
()
end)
end
| _61_640 -> begin
()
end))))))
end
| _61_642 -> begin
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
(let _155_543 = (aux tl)
in (hd)::_155_543)
end))
in (aux ns)))
in (

let find_in_cache = (fun fieldname -> (

let _61_660 = ((fieldname.FStar_Ident.ns), (fieldname.FStar_Ident.ident))
in (match (_61_660) with
| (ns, fieldname) -> begin
(let _155_548 = (peek_record_cache ())
in (FStar_Util.find_map _155_548 (fun record -> (

let constrname = record.constrname.FStar_Ident.ident
in (

let ns = (maybe_add_constrname ns constrname)
in (

let fname = (FStar_Ident.lid_of_ids (FStar_List.append ns ((fieldname)::[])))
in (FStar_Util.find_map record.fields (fun _61_668 -> (match (_61_668) with
| (f, _61_667) -> begin
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
| _61_676 -> begin
None
end))


let try_lookup_projector_by_field_name : env  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * Prims.bool) Prims.option = (fun env fieldname -> (match ((try_lookup_record_or_dc_by_field_name env fieldname)) with
| Some (r, f) -> begin
Some (((f), (r.is_record)))
end
| _61_684 -> begin
None
end))


let qualify_field_to_record : env  ->  record_or_dc  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env recd f -> (

let qualify = (fun fieldname -> (

let _61_692 = ((fieldname.FStar_Ident.ns), (fieldname.FStar_Ident.ident))
in (match (_61_692) with
| (ns, fieldname) -> begin
(

let constrname = recd.constrname.FStar_Ident.ident
in (

let fname = (FStar_Ident.lid_of_ids (FStar_List.append ns (FStar_List.append ((constrname)::[]) ((fieldname)::[]))))
in (FStar_Util.find_map recd.fields (fun _61_698 -> (match (_61_698) with
| (f, _61_697) -> begin
if (FStar_Ident.lid_equals fname f) then begin
Some (fname)
end else begin
None
end
end)))))
end)))
in (resolve_in_open_namespaces env f qualify)))


let find_kind_abbrev : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env l -> (match ((try_lookup_name true (not (env.iface)) env l)) with
| Some (Knd_name (_61_702, l)) -> begin
Some (l)
end
| _61_708 -> begin
None
end))


let is_kind_abbrev : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (match ((find_kind_abbrev env l)) with
| None -> begin
false
end
| Some (_61_713) -> begin
true
end))


let unique_name : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  Prims.bool = (fun any_val exclude_if env lid -> (match ((try_lookup_lid' any_val exclude_if env lid)) with
| None -> begin
(match ((find_kind_abbrev env lid)) with
| None -> begin
true
end
| Some (_61_722) -> begin
false
end)
end
| Some (_61_725) -> begin
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

let _61_736 = env
in {curmodule = _61_736.curmodule; modules = _61_736.modules; open_namespaces = []; modul_abbrevs = _61_736.modul_abbrevs; sigaccum = _61_736.sigaccum; localbindings = _61_736.localbindings; recbindings = _61_736.recbindings; phase = _61_736.phase; sigmap = _61_736.sigmap; default_result_effect = _61_736.default_result_effect; iface = _61_736.iface; admitted_iface = _61_736.admitted_iface})
in ((unique_name any_val exclude_if this_env lid) && (unique_typ_name this_env lid))))


let gen_bvd = (fun _61_13 -> (match (_61_13) with
| Binding_typ_var (id) -> begin
(let _155_597 = (let _155_596 = (let _155_595 = (FStar_Absyn_Util.genident (Some (id.FStar_Ident.idRange)))
in ((id), (_155_595)))
in (FStar_Absyn_Util.mkbvd _155_596))
in FStar_Util.Inl (_155_597))
end
| Binding_var (id) -> begin
(let _155_600 = (let _155_599 = (let _155_598 = (FStar_Absyn_Util.genident (Some (id.FStar_Ident.idRange)))
in ((id), (_155_598)))
in (FStar_Absyn_Util.mkbvd _155_599))
in FStar_Util.Inr (_155_600))
end
| _61_745 -> begin
(FStar_All.failwith "Tried to generate a bound variable for a type constructor")
end))


let push_bvvdef : env  ->  FStar_Absyn_Syntax.bvvdef  ->  env = (fun env x -> (

let b = Binding_var (x.FStar_Absyn_Syntax.ppname)
in (

let _61_749 = env
in {curmodule = _61_749.curmodule; modules = _61_749.modules; open_namespaces = _61_749.open_namespaces; modul_abbrevs = _61_749.modul_abbrevs; sigaccum = _61_749.sigaccum; localbindings = (((FStar_Util.Inr (x)), (b)))::env.localbindings; recbindings = _61_749.recbindings; phase = _61_749.phase; sigmap = _61_749.sigmap; default_result_effect = _61_749.default_result_effect; iface = _61_749.iface; admitted_iface = _61_749.admitted_iface})))


let push_btvdef : env  ->  FStar_Absyn_Syntax.btvdef  ->  env = (fun env x -> (

let b = Binding_typ_var (x.FStar_Absyn_Syntax.ppname)
in (

let _61_754 = env
in {curmodule = _61_754.curmodule; modules = _61_754.modules; open_namespaces = _61_754.open_namespaces; modul_abbrevs = _61_754.modul_abbrevs; sigaccum = _61_754.sigaccum; localbindings = (((FStar_Util.Inl (x)), (b)))::env.localbindings; recbindings = _61_754.recbindings; phase = _61_754.phase; sigmap = _61_754.sigmap; default_result_effect = _61_754.default_result_effect; iface = _61_754.iface; admitted_iface = _61_754.admitted_iface})))


let push_local_binding : env  ->  binding  ->  (env * (FStar_Absyn_Syntax.btvdef, FStar_Absyn_Syntax.bvvdef) FStar_Util.either) = (fun env b -> (

let bvd = (gen_bvd b)
in (((

let _61_759 = env
in {curmodule = _61_759.curmodule; modules = _61_759.modules; open_namespaces = _61_759.open_namespaces; modul_abbrevs = _61_759.modul_abbrevs; sigaccum = _61_759.sigaccum; localbindings = (((bvd), (b)))::env.localbindings; recbindings = _61_759.recbindings; phase = _61_759.phase; sigmap = _61_759.sigmap; default_result_effect = _61_759.default_result_effect; iface = _61_759.iface; admitted_iface = _61_759.admitted_iface})), (bvd))))


let push_local_tbinding : env  ->  FStar_Ident.ident  ->  (env * FStar_Absyn_Syntax.btvdef) = (fun env a -> (match ((push_local_binding env (Binding_typ_var (a)))) with
| (env, FStar_Util.Inl (x)) -> begin
((env), (x))
end
| _61_768 -> begin
(FStar_All.failwith "impossible")
end))


let push_local_vbinding : env  ->  FStar_Ident.ident  ->  (env * FStar_Absyn_Syntax.bvvdef) = (fun env b -> (match ((push_local_binding env (Binding_var (b)))) with
| (env, FStar_Util.Inr (x)) -> begin
((env), (x))
end
| _61_776 -> begin
(FStar_All.failwith "impossible")
end))


let push_rec_binding : env  ->  binding  ->  env = (fun env b -> (match (b) with
| (Binding_let (lid)) | (Binding_tycon (lid)) -> begin
if (unique false true env lid) then begin
(

let _61_782 = env
in {curmodule = _61_782.curmodule; modules = _61_782.modules; open_namespaces = _61_782.open_namespaces; modul_abbrevs = _61_782.modul_abbrevs; sigaccum = _61_782.sigaccum; localbindings = _61_782.localbindings; recbindings = (b)::env.recbindings; phase = _61_782.phase; sigmap = _61_782.sigmap; default_result_effect = _61_782.default_result_effect; iface = _61_782.iface; admitted_iface = _61_782.admitted_iface})
end else begin
(Prims.raise (FStar_Absyn_Syntax.Error ((((Prims.strcat "Duplicate top-level names " lid.FStar_Ident.str)), ((FStar_Ident.range_of_lid lid))))))
end
end
| _61_785 -> begin
(FStar_All.failwith "Unexpected rec_binding")
end))


let push_sigelt : env  ->  FStar_Absyn_Syntax.sigelt  ->  env = (fun env s -> (

let err = (fun l -> (

let sopt = (let _155_631 = (sigmap env)
in (FStar_Util.smap_try_find _155_631 l.FStar_Ident.str))
in (

let r = (match (sopt) with
| Some (se, _61_793) -> begin
(match ((let _155_632 = (FStar_Absyn_Util.lids_of_sigelt se)
in (FStar_Util.find_opt (FStar_Ident.lid_equals l) _155_632))) with
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
in (let _155_635 = (let _155_634 = (let _155_633 = (FStar_Util.format2 "Duplicate top-level names [%s]; previously declared at %s" (FStar_Ident.text_of_lid l) r)
in ((_155_633), ((FStar_Ident.range_of_lid l))))
in FStar_Absyn_Syntax.Error (_155_634))
in (Prims.raise _155_635)))))
in (

let env = (

let _61_811 = (match (s) with
| FStar_Absyn_Syntax.Sig_let (_61_802) -> begin
((false), (true))
end
| FStar_Absyn_Syntax.Sig_bundle (_61_805) -> begin
((true), (true))
end
| _61_808 -> begin
((false), (false))
end)
in (match (_61_811) with
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

let _61_815 = (extract_record env s)
in (

let _61_817 = env
in {curmodule = _61_817.curmodule; modules = _61_817.modules; open_namespaces = _61_817.open_namespaces; modul_abbrevs = _61_817.modul_abbrevs; sigaccum = (s)::env.sigaccum; localbindings = _61_817.localbindings; recbindings = _61_817.recbindings; phase = _61_817.phase; sigmap = _61_817.sigmap; default_result_effect = _61_817.default_result_effect; iface = _61_817.iface; admitted_iface = _61_817.admitted_iface}))
end
| Some (l) -> begin
(err l)
end))
end))
in (

let _61_836 = (match (s) with
| FStar_Absyn_Syntax.Sig_bundle (ses, _61_824, _61_826, _61_828) -> begin
(let _155_639 = (FStar_List.map (fun se -> (let _155_638 = (FStar_Absyn_Util.lids_of_sigelt se)
in ((_155_638), (se)))) ses)
in ((env), (_155_639)))
end
| _61_833 -> begin
(let _155_642 = (let _155_641 = (let _155_640 = (FStar_Absyn_Util.lids_of_sigelt s)
in ((_155_640), (s)))
in (_155_641)::[])
in ((env), (_155_642)))
end)
in (match (_61_836) with
| (env, lss) -> begin
(

let _61_841 = (FStar_All.pipe_right lss (FStar_List.iter (fun _61_839 -> (match (_61_839) with
| (lids, se) -> begin
(FStar_All.pipe_right lids (FStar_List.iter (fun lid -> (let _155_645 = (sigmap env)
in (FStar_Util.smap_add _155_645 lid.FStar_Ident.str ((se), ((env.iface && (not (env.admitted_iface))))))))))
end))))
in env)
end)))))


let push_namespace : env  ->  FStar_Ident.lident  ->  env = (fun env lid -> (

let _61_845 = env
in {curmodule = _61_845.curmodule; modules = _61_845.modules; open_namespaces = (lid)::env.open_namespaces; modul_abbrevs = _61_845.modul_abbrevs; sigaccum = _61_845.sigaccum; localbindings = _61_845.localbindings; recbindings = _61_845.recbindings; phase = _61_845.phase; sigmap = _61_845.sigmap; default_result_effect = _61_845.default_result_effect; iface = _61_845.iface; admitted_iface = _61_845.admitted_iface}))


let push_module_abbrev : env  ->  FStar_Ident.ident  ->  FStar_Ident.lident  ->  env = (fun env x l -> if (FStar_All.pipe_right env.modul_abbrevs (FStar_Util.for_some (fun _61_853 -> (match (_61_853) with
| (y, _61_852) -> begin
(x.FStar_Ident.idText = y.FStar_Ident.idText)
end)))) then begin
(let _155_659 = (let _155_658 = (let _155_657 = (FStar_Util.format1 "Module %s is already defined" x.FStar_Ident.idText)
in ((_155_657), (x.FStar_Ident.idRange)))
in FStar_Absyn_Syntax.Error (_155_658))
in (Prims.raise _155_659))
end else begin
(

let _61_854 = env
in {curmodule = _61_854.curmodule; modules = _61_854.modules; open_namespaces = _61_854.open_namespaces; modul_abbrevs = (((x), (l)))::env.modul_abbrevs; sigaccum = _61_854.sigaccum; localbindings = _61_854.localbindings; recbindings = _61_854.recbindings; phase = _61_854.phase; sigmap = _61_854.sigmap; default_result_effect = _61_854.default_result_effect; iface = _61_854.iface; admitted_iface = _61_854.admitted_iface})
end)


let is_type_lid : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let aux = (fun _61_859 -> (match (()) with
| () -> begin
(match ((try_lookup_typ_name' false env lid)) with
| Some (_61_861) -> begin
true
end
| _61_864 -> begin
false
end)
end))
in if (lid.FStar_Ident.ns = []) then begin
(match ((try_lookup_id env lid.FStar_Ident.ident)) with
| Some (_61_866) -> begin
false
end
| _61_869 -> begin
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

let _61_880 = (let _155_673 = (let _155_672 = (FStar_Range.string_of_range (FStar_Ident.range_of_lid l))
in (let _155_671 = (FStar_Absyn_Print.sli l)
in (FStar_Util.format2 "%s: Warning: Admitting %s without a definition\n" _155_672 _155_671)))
in (FStar_Util.print_string _155_673))
in (let _155_674 = (sigmap env)
in (FStar_Util.smap_add _155_674 l.FStar_Ident.str ((FStar_Absyn_Syntax.Sig_val_decl (((l), (t), ((FStar_Absyn_Syntax.Assumption)::quals), (r)))), (false)))))
end
| Some (_61_883) -> begin
()
end)
end
| _61_886 -> begin
()
end)))))


let finish : env  ->  FStar_Absyn_Syntax.modul  ->  env = (fun env modul -> (

let _61_924 = (FStar_All.pipe_right modul.FStar_Absyn_Syntax.declarations (FStar_List.iter (fun _61_15 -> (match (_61_15) with
| FStar_Absyn_Syntax.Sig_bundle (ses, quals, _61_893, _61_895) -> begin
if (FStar_List.contains FStar_Absyn_Syntax.Private quals) then begin
(FStar_All.pipe_right ses (FStar_List.iter (fun _61_14 -> (match (_61_14) with
| FStar_Absyn_Syntax.Sig_datacon (lid, _61_901, _61_903, _61_905, _61_907, _61_909) -> begin
(let _155_681 = (sigmap env)
in (FStar_Util.smap_remove _155_681 lid.FStar_Ident.str))
end
| _61_913 -> begin
()
end))))
end else begin
()
end
end
| FStar_Absyn_Syntax.Sig_val_decl (lid, _61_916, quals, _61_919) -> begin
if (FStar_List.contains FStar_Absyn_Syntax.Private quals) then begin
(let _155_682 = (sigmap env)
in (FStar_Util.smap_remove _155_682 lid.FStar_Ident.str))
end else begin
()
end
end
| _61_923 -> begin
()
end))))
in (

let _61_926 = env
in {curmodule = None; modules = (((modul.FStar_Absyn_Syntax.name), (modul)))::env.modules; open_namespaces = []; modul_abbrevs = []; sigaccum = []; localbindings = []; recbindings = []; phase = FStar_Parser_AST.Un; sigmap = _61_926.sigmap; default_result_effect = _61_926.default_result_effect; iface = _61_926.iface; admitted_iface = _61_926.admitted_iface})))


let push : env  ->  env = (fun env -> (

let _61_929 = (push_record_cache ())
in (

let _61_931 = env
in (let _155_687 = (let _155_686 = (let _155_685 = (sigmap env)
in (FStar_Util.smap_copy _155_685))
in (_155_686)::env.sigmap)
in {curmodule = _61_931.curmodule; modules = _61_931.modules; open_namespaces = _61_931.open_namespaces; modul_abbrevs = _61_931.modul_abbrevs; sigaccum = _61_931.sigaccum; localbindings = _61_931.localbindings; recbindings = _61_931.recbindings; phase = _61_931.phase; sigmap = _155_687; default_result_effect = _61_931.default_result_effect; iface = _61_931.iface; admitted_iface = _61_931.admitted_iface}))))


let mark : env  ->  env = (fun env -> (push env))


let reset_mark : env  ->  env = (fun env -> (

let _61_935 = env
in (let _155_692 = (FStar_List.tl env.sigmap)
in {curmodule = _61_935.curmodule; modules = _61_935.modules; open_namespaces = _61_935.open_namespaces; modul_abbrevs = _61_935.modul_abbrevs; sigaccum = _61_935.sigaccum; localbindings = _61_935.localbindings; recbindings = _61_935.recbindings; phase = _61_935.phase; sigmap = _155_692; default_result_effect = _61_935.default_result_effect; iface = _61_935.iface; admitted_iface = _61_935.admitted_iface})))


let commit_mark : env  ->  env = (fun env -> (match (env.sigmap) with
| (hd)::(_61_940)::tl -> begin
(

let _61_944 = env
in {curmodule = _61_944.curmodule; modules = _61_944.modules; open_namespaces = _61_944.open_namespaces; modul_abbrevs = _61_944.modul_abbrevs; sigaccum = _61_944.sigaccum; localbindings = _61_944.localbindings; recbindings = _61_944.recbindings; phase = _61_944.phase; sigmap = (hd)::tl; default_result_effect = _61_944.default_result_effect; iface = _61_944.iface; admitted_iface = _61_944.admitted_iface})
end
| _61_947 -> begin
(FStar_All.failwith "Impossible")
end))


let pop : env  ->  env = (fun env -> (match (env.sigmap) with
| (_61_951)::maps -> begin
(

let _61_953 = (pop_record_cache ())
in (

let _61_955 = env
in {curmodule = _61_955.curmodule; modules = _61_955.modules; open_namespaces = _61_955.open_namespaces; modul_abbrevs = _61_955.modul_abbrevs; sigaccum = _61_955.sigaccum; localbindings = _61_955.localbindings; recbindings = _61_955.recbindings; phase = _61_955.phase; sigmap = maps; default_result_effect = _61_955.default_result_effect; iface = _61_955.iface; admitted_iface = _61_955.admitted_iface}))
end
| _61_958 -> begin
(FStar_All.failwith "No more modules to pop")
end))


let export_interface : FStar_Ident.lident  ->  env  ->  env = (fun m env -> (

let sigelt_in_m = (fun se -> (match ((FStar_Absyn_Util.lids_of_sigelt se)) with
| (l)::_61_964 -> begin
(l.FStar_Ident.nsstr = m.FStar_Ident.str)
end
| _61_968 -> begin
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

let _61_991 = (FStar_All.pipe_right keys (FStar_List.iter (fun k -> (match ((FStar_Util.smap_try_find sm' k)) with
| Some (se, true) when (sigelt_in_m se) -> begin
(

let _61_978 = (FStar_Util.smap_remove sm' k)
in (

let se = (match (se) with
| FStar_Absyn_Syntax.Sig_val_decl (l, t, q, r) -> begin
FStar_Absyn_Syntax.Sig_val_decl (((l), (t), ((FStar_Absyn_Syntax.Assumption)::q), (r)))
end
| _61_987 -> begin
se
end)
in (FStar_Util.smap_add sm' k ((se), (false)))))
end
| _61_990 -> begin
()
end))))
in env)))))))


let finish_module_or_interface : env  ->  FStar_Absyn_Syntax.modul  ->  env = (fun env modul -> (

let _61_995 = if (not (modul.FStar_Absyn_Syntax.is_interface)) then begin
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

let _61_1004 = env
in {curmodule = Some (mname); modules = _61_1004.modules; open_namespaces = open_ns; modul_abbrevs = _61_1004.modul_abbrevs; sigaccum = _61_1004.sigaccum; localbindings = _61_1004.localbindings; recbindings = _61_1004.recbindings; phase = _61_1004.phase; sigmap = env.sigmap; default_result_effect = _61_1004.default_result_effect; iface = intf; admitted_iface = admitted})))
in (match ((FStar_All.pipe_right env.modules (FStar_Util.find_opt (fun _61_1009 -> (match (_61_1009) with
| (l, _61_1008) -> begin
(FStar_Ident.lid_equals l mname)
end))))) with
| None -> begin
(((prep env)), (false))
end
| Some (_61_1012, m) -> begin
(let _155_721 = (let _155_720 = (let _155_719 = (FStar_Util.format1 "Duplicate module or interface name: %s" mname.FStar_Ident.str)
in ((_155_719), ((FStar_Ident.range_of_lid mname))))
in FStar_Absyn_Syntax.Error (_155_720))
in (Prims.raise _155_721))
end)))


let enter_monad_scope : env  ->  FStar_Ident.ident  ->  env = (fun env mname -> (

let curmod = (current_module env)
in (

let mscope = (FStar_Ident.lid_of_ids (FStar_List.append curmod.FStar_Ident.ns ((curmod.FStar_Ident.ident)::(mname)::[])))
in (

let _61_1020 = env
in {curmodule = Some (mscope); modules = _61_1020.modules; open_namespaces = (curmod)::env.open_namespaces; modul_abbrevs = _61_1020.modul_abbrevs; sigaccum = _61_1020.sigaccum; localbindings = _61_1020.localbindings; recbindings = _61_1020.recbindings; phase = _61_1020.phase; sigmap = _61_1020.sigmap; default_result_effect = _61_1020.default_result_effect; iface = _61_1020.iface; admitted_iface = _61_1020.admitted_iface}))))


let exit_monad_scope : env  ->  env  ->  env = (fun env0 env -> (

let _61_1024 = env
in {curmodule = env0.curmodule; modules = _61_1024.modules; open_namespaces = env0.open_namespaces; modul_abbrevs = _61_1024.modul_abbrevs; sigaccum = _61_1024.sigaccum; localbindings = _61_1024.localbindings; recbindings = _61_1024.recbindings; phase = _61_1024.phase; sigmap = _61_1024.sigmap; default_result_effect = _61_1024.default_result_effect; iface = _61_1024.iface; admitted_iface = _61_1024.admitted_iface}))


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
(let _155_736 = (FStar_Range.string_of_range r)
in (FStar_Util.format1 "(Possible clash with related name at %s)" _155_736))
end)
in (let _155_739 = (let _155_738 = (let _155_737 = (FStar_Util.format2 "Identifier not found: [%s] %s" (FStar_Ident.text_of_lid lid) msg)
in ((_155_737), ((FStar_Ident.range_of_lid lid))))
in FStar_Absyn_Syntax.Error (_155_738))
in (Prims.raise _155_739))))
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




