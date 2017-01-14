
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
| Binding_typ_var (_71_3) -> begin
_71_3
end))


let ___Binding_var____0 = (fun projectee -> (match (projectee) with
| Binding_var (_71_6) -> begin
_71_6
end))


let ___Binding_let____0 = (fun projectee -> (match (projectee) with
| Binding_let (_71_9) -> begin
_71_9
end))


let ___Binding_tycon____0 = (fun projectee -> (match (projectee) with
| Binding_tycon (_71_12) -> begin
_71_12
end))


type kind_abbrev =
(FStar_Ident.lident * (FStar_Absyn_Syntax.btvdef, FStar_Absyn_Syntax.bvvdef) FStar_Util.either Prims.list * FStar_Absyn_Syntax.knd)


type env =
{curmodule : FStar_Ident.lident Prims.option; modules : (FStar_Ident.lident * FStar_Absyn_Syntax.modul) Prims.list; open_namespaces : FStar_Ident.lident Prims.list; modul_abbrevs : (FStar_Ident.ident * FStar_Ident.lident) Prims.list; sigaccum : FStar_Absyn_Syntax.sigelts; localbindings : ((FStar_Absyn_Syntax.btvdef, FStar_Absyn_Syntax.bvvdef) FStar_Util.either * binding) Prims.list; recbindings : binding Prims.list; phase : FStar_Parser_AST.level; sigmap : (FStar_Absyn_Syntax.sigelt * Prims.bool) FStar_Util.smap Prims.list; default_result_effect : FStar_Absyn_Syntax.typ  ->  FStar_Range.range  ->  FStar_Absyn_Syntax.comp; iface : Prims.bool; admitted_iface : Prims.bool}


let is_Mkenv : env  ->  Prims.bool = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mkenv"))))


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
| OSig (_71_28) -> begin
_71_28
end))


let ___OLet____0 = (fun projectee -> (match (projectee) with
| OLet (_71_31) -> begin
_71_31
end))


let ___ORec____0 = (fun projectee -> (match (projectee) with
| ORec (_71_34) -> begin
_71_34
end))


let range_of_occurrence : occurrence  ->  FStar_Range.range = (fun uu___393 -> (match (uu___393) with
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
| Exp_name (_71_43) -> begin
_71_43
end))


let ___Typ_name____0 = (fun projectee -> (match (projectee) with
| Typ_name (_71_46) -> begin
_71_46
end))


let ___Eff_name____0 = (fun projectee -> (match (projectee) with
| Eff_name (_71_49) -> begin
_71_49
end))


let ___Knd_name____0 = (fun projectee -> (match (projectee) with
| Knd_name (_71_52) -> begin
_71_52
end))


type record_or_dc =
{typename : FStar_Ident.lident; constrname : FStar_Ident.lident; parms : FStar_Absyn_Syntax.binders; fields : (FStar_Absyn_Syntax.fieldname * FStar_Absyn_Syntax.typ) Prims.list; is_record : Prims.bool}


let is_Mkrecord_or_dc : record_or_dc  ->  Prims.bool = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mkrecord_or_dc"))))


let open_modules : env  ->  (FStar_Ident.lident * FStar_Absyn_Syntax.modul) Prims.list = (fun e -> e.modules)


let current_module : env  ->  FStar_Ident.lident = (fun env -> (match (env.curmodule) with
| None -> begin
(failwith "Unset current module")
end
| Some (m) -> begin
m
end))


let qual : FStar_Ident.lident  ->  FStar_Ident.ident  ->  FStar_Ident.lident = (fun lid id -> (let _172_230 = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns ((lid.FStar_Ident.ident)::(id)::[])))
in (FStar_Ident.set_lid_range _172_230 id.FStar_Ident.idRange)))


let qualify : env  ->  FStar_Ident.ident  ->  FStar_Ident.lident = (fun env id -> (let _172_235 = (current_module env)
in (qual _172_235 id)))


let qualify_lid : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (

let cur = (current_module env)
in (let _172_240 = (FStar_Ident.lid_of_ids (FStar_List.append cur.FStar_Ident.ns (FStar_List.append ((cur.FStar_Ident.ident)::[]) (FStar_List.append lid.FStar_Ident.ns ((lid.FStar_Ident.ident)::[])))))
in (FStar_Ident.set_lid_range _172_240 (FStar_Ident.range_of_lid lid)))))


let new_sigmap = (fun _71_74 -> (match (()) with
| () -> begin
(FStar_Util.smap_create (Prims.parse_int "100"))
end))


let empty_env : Prims.unit  ->  env = (fun _71_75 -> (match (()) with
| () -> begin
(let _172_245 = (let _172_244 = (new_sigmap ())
in (_172_244)::[])
in {curmodule = None; modules = []; open_namespaces = []; modul_abbrevs = []; sigaccum = []; localbindings = []; recbindings = []; phase = FStar_Parser_AST.Un; sigmap = _172_245; default_result_effect = FStar_Absyn_Util.ml_comp; iface = false; admitted_iface = false})
end))


let sigmap : env  ->  (FStar_Absyn_Syntax.sigelt * Prims.bool) FStar_Util.smap = (fun env -> (FStar_List.hd env.sigmap))


let default_total : env  ->  env = (fun env -> (

let _71_78 = env
in {curmodule = _71_78.curmodule; modules = _71_78.modules; open_namespaces = _71_78.open_namespaces; modul_abbrevs = _71_78.modul_abbrevs; sigaccum = _71_78.sigaccum; localbindings = _71_78.localbindings; recbindings = _71_78.recbindings; phase = _71_78.phase; sigmap = _71_78.sigmap; default_result_effect = (fun t _71_81 -> (FStar_Absyn_Syntax.mk_Total t)); iface = _71_78.iface; admitted_iface = _71_78.admitted_iface}))


let default_ml : env  ->  env = (fun env -> (

let _71_84 = env
in {curmodule = _71_84.curmodule; modules = _71_84.modules; open_namespaces = _71_84.open_namespaces; modul_abbrevs = _71_84.modul_abbrevs; sigaccum = _71_84.sigaccum; localbindings = _71_84.localbindings; recbindings = _71_84.recbindings; phase = _71_84.phase; sigmap = _71_84.sigmap; default_result_effect = FStar_Absyn_Util.ml_comp; iface = _71_84.iface; admitted_iface = _71_84.admitted_iface}))


let range_of_binding : binding  ->  FStar_Range.range = (fun uu___394 -> (match (uu___394) with
| (Binding_typ_var (id)) | (Binding_var (id)) -> begin
id.FStar_Ident.idRange
end
| (Binding_let (lid)) | (Binding_tycon (lid)) -> begin
(FStar_Ident.range_of_lid lid)
end))


let try_lookup_typ_var : env  ->  FStar_Ident.ident  ->  FStar_Absyn_Syntax.typ Prims.option = (fun env id -> (

let fopt = (FStar_List.tryFind (fun _71_98 -> (match (_71_98) with
| (_71_96, b) -> begin
(match (b) with
| (Binding_typ_var (id')) | (Binding_var (id')) -> begin
(id.FStar_Ident.idText = id'.FStar_Ident.idText)
end
| _71_103 -> begin
false
end)
end)) env.localbindings)
in (match (fopt) with
| Some (FStar_Util.Inl (bvd), Binding_typ_var (_71_108)) -> begin
(let _172_261 = (FStar_Absyn_Util.bvd_to_typ (FStar_Absyn_Util.set_bvd_range bvd id.FStar_Ident.idRange) FStar_Absyn_Syntax.kun)
in Some (_172_261))
end
| _71_113 -> begin
None
end)))


let resolve_in_open_namespaces' = (fun env lid finder -> (

let aux = (fun namespaces -> (match ((finder lid)) with
| Some (r) -> begin
Some (r)
end
| _71_123 -> begin
(

let ids = (FStar_Ident.ids_of_lid lid)
in (FStar_Util.find_map namespaces (fun ns -> (

let full_name = (FStar_Ident.lid_of_ids (FStar_List.append (FStar_Ident.ids_of_lid ns) ids))
in (finder full_name)))))
end))
in (let _172_272 = (let _172_271 = (current_module env)
in (_172_271)::env.open_namespaces)
in (aux _172_272))))


let expand_module_abbrevs : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (match (lid.FStar_Ident.ns) with
| (id)::[] -> begin
(match ((FStar_All.pipe_right env.modul_abbrevs (FStar_List.tryFind (fun _71_134 -> (match (_71_134) with
| (id', _71_133) -> begin
(id.FStar_Ident.idText = id'.FStar_Ident.idText)
end))))) with
| None -> begin
lid
end
| Some (_71_137, lid') -> begin
(FStar_Ident.lid_of_ids (FStar_List.append (FStar_Ident.ids_of_lid lid') ((lid.FStar_Ident.ident)::[])))
end)
end
| _71_142 -> begin
lid
end))


let resolve_in_open_namespaces = (fun env lid finder -> (let _172_288 = (expand_module_abbrevs env lid)
in (resolve_in_open_namespaces' env _172_288 finder)))


let unmangleMap : (Prims.string * Prims.string) Prims.list = ((("op_ColonColon"), ("Cons")))::((("not"), ("op_Negation")))::[]


let unmangleOpName : FStar_Ident.ident  ->  FStar_Ident.lident Prims.option = (fun id -> (FStar_Util.find_map unmangleMap (fun _71_150 -> (match (_71_150) with
| (x, y) -> begin
if (id.FStar_Ident.idText = x) then begin
(let _172_292 = (FStar_Ident.lid_of_path (("Prims")::(y)::[]) id.FStar_Ident.idRange)
in Some (_172_292))
end else begin
None
end
end))))


let try_lookup_id' : env  ->  FStar_Ident.ident  ->  (FStar_Ident.lident * FStar_Absyn_Syntax.exp) Prims.option = (fun env id -> (match ((unmangleOpName id)) with
| Some (l) -> begin
(let _172_298 = (let _172_297 = (FStar_Absyn_Syntax.mk_Exp_fvar (((FStar_Absyn_Util.fv l)), (None)) None id.FStar_Ident.idRange)
in ((l), (_172_297)))
in Some (_172_298))
end
| _71_156 -> begin
(

let found = (FStar_Util.find_map env.localbindings (fun uu___395 -> (match (uu___395) with
| (FStar_Util.Inl (_71_159), Binding_typ_var (id')) when (id'.FStar_Ident.idText = id.FStar_Ident.idText) -> begin
Some (FStar_Util.Inl (()))
end
| (FStar_Util.Inr (bvd), Binding_var (id')) when (id'.FStar_Ident.idText = id.FStar_Ident.idText) -> begin
(let _172_303 = (let _172_302 = (let _172_301 = (FStar_Ident.lid_of_ids ((id')::[]))
in (let _172_300 = (FStar_Absyn_Util.bvd_to_exp (FStar_Absyn_Util.set_bvd_range bvd id.FStar_Ident.idRange) FStar_Absyn_Syntax.tun)
in ((_172_301), (_172_300))))
in FStar_Util.Inr (_172_302))
in Some (_172_303))
end
| _71_170 -> begin
None
end)))
in (match (found) with
| Some (FStar_Util.Inr (x)) -> begin
Some (x)
end
| _71_176 -> begin
None
end))
end))


let try_lookup_id : env  ->  FStar_Ident.ident  ->  FStar_Absyn_Syntax.exp Prims.option = (fun env id -> (match ((try_lookup_id' env id)) with
| Some (_71_180, e) -> begin
Some (e)
end
| None -> begin
None
end))


let fv_qual_of_se : FStar_Absyn_Syntax.sigelt  ->  FStar_Absyn_Syntax.fv_qual Prims.option = (fun uu___397 -> (match (uu___397) with
| FStar_Absyn_Syntax.Sig_datacon (_71_187, _71_189, (l, _71_192, _71_194), quals, _71_198, _71_200) -> begin
(

let qopt = (FStar_Util.find_map quals (fun uu___396 -> (match (uu___396) with
| FStar_Absyn_Syntax.RecordConstructor (fs) -> begin
Some (FStar_Absyn_Syntax.Record_ctor (((l), (fs))))
end
| _71_207 -> begin
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
| FStar_Absyn_Syntax.Sig_val_decl (_71_212, _71_214, quals, _71_217) -> begin
None
end
| _71_221 -> begin
None
end))


let try_lookup_name : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  foundname Prims.option = (fun any_val exclude_interf env lid -> (

let find_in_sig = (fun lid -> (match ((let _172_321 = (sigmap env)
in (FStar_Util.smap_try_find _172_321 lid.FStar_Ident.str))) with
| Some (_71_229, true) when exclude_interf -> begin
None
end
| None -> begin
None
end
| Some (se, _71_236) -> begin
(match (se) with
| (FStar_Absyn_Syntax.Sig_typ_abbrev (_)) | (FStar_Absyn_Syntax.Sig_tycon (_)) -> begin
(let _172_324 = (let _172_323 = (let _172_322 = (FStar_Absyn_Util.ftv lid FStar_Absyn_Syntax.kun)
in ((OSig (se)), (_172_322)))
in Typ_name (_172_323))
in Some (_172_324))
end
| FStar_Absyn_Syntax.Sig_kind_abbrev (_71_246) -> begin
Some (Knd_name (((OSig (se)), (lid))))
end
| FStar_Absyn_Syntax.Sig_new_effect (ne, _71_250) -> begin
Some (Eff_name (((OSig (se)), ((FStar_Ident.set_lid_range ne.FStar_Absyn_Syntax.mname (FStar_Ident.range_of_lid lid))))))
end
| FStar_Absyn_Syntax.Sig_effect_abbrev (_71_254) -> begin
Some (Eff_name (((OSig (se)), (lid))))
end
| FStar_Absyn_Syntax.Sig_datacon (_71_257) -> begin
(let _172_328 = (let _172_327 = (let _172_326 = (let _172_325 = (fv_qual_of_se se)
in (FStar_Absyn_Util.fvar _172_325 lid (FStar_Ident.range_of_lid lid)))
in ((OSig (se)), (_172_326)))
in Exp_name (_172_327))
in Some (_172_328))
end
| FStar_Absyn_Syntax.Sig_let (_71_260) -> begin
(let _172_331 = (let _172_330 = (let _172_329 = (FStar_Absyn_Util.fvar None lid (FStar_Ident.range_of_lid lid))
in ((OSig (se)), (_172_329)))
in Exp_name (_172_330))
in Some (_172_331))
end
| FStar_Absyn_Syntax.Sig_val_decl (_71_263, _71_265, quals, _71_268) -> begin
if (any_val || (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___398 -> (match (uu___398) with
| FStar_Absyn_Syntax.Assumption -> begin
true
end
| _71_274 -> begin
false
end))))) then begin
(let _172_336 = (let _172_335 = (let _172_334 = (let _172_333 = (fv_qual_of_se se)
in (FStar_Absyn_Util.fvar _172_333 lid (FStar_Ident.range_of_lid lid)))
in ((OSig (se)), (_172_334)))
in Exp_name (_172_335))
in Some (_172_336))
end else begin
None
end
end
| _71_276 -> begin
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
in (FStar_Util.find_map env.recbindings (fun uu___399 -> (match (uu___399) with
| Binding_let (l) when (FStar_Ident.lid_equals l recname) -> begin
(let _172_340 = (let _172_339 = (let _172_338 = (FStar_Absyn_Util.fvar None recname (FStar_Ident.range_of_lid recname))
in ((ORec (l)), (_172_338)))
in Exp_name (_172_339))
in Some (_172_340))
end
| Binding_tycon (l) when (FStar_Ident.lid_equals l recname) -> begin
(let _172_343 = (let _172_342 = (let _172_341 = (FStar_Absyn_Util.ftv recname FStar_Absyn_Syntax.kun)
in ((ORec (l)), (_172_341)))
in Typ_name (_172_342))
in Some (_172_343))
end
| _71_290 -> begin
None
end))))
end)
end
| _71_292 -> begin
None
end)
in (match (found_id) with
| Some (_71_295) -> begin
found_id
end
| _71_298 -> begin
(resolve_in_open_namespaces env lid find_in_sig)
end))))


let try_lookup_typ_name' : Prims.bool  ->  env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.typ Prims.option = (fun exclude_interf env lid -> (match ((try_lookup_name true exclude_interf env lid)) with
| Some (Typ_name (_71_303, t)) -> begin
Some (t)
end
| Some (Eff_name (_71_309, l)) -> begin
(let _172_350 = (FStar_Absyn_Util.ftv l FStar_Absyn_Syntax.mk_Kind_unknown)
in Some (_172_350))
end
| _71_315 -> begin
None
end))


let try_lookup_typ_name : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.typ Prims.option = (fun env l -> (try_lookup_typ_name' (not (env.iface)) env l))


let try_lookup_effect_name' : Prims.bool  ->  env  ->  FStar_Ident.lident  ->  (occurrence * FStar_Ident.lident) Prims.option = (fun exclude_interf env lid -> (match ((try_lookup_name true exclude_interf env lid)) with
| Some (Eff_name (o, l)) -> begin
Some (((o), (l)))
end
| _71_327 -> begin
None
end))


let try_lookup_effect_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env l -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some (o, l) -> begin
Some (l)
end
| _71_335 -> begin
None
end))


let try_lookup_effect_defn : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.eff_decl Prims.option = (fun env l -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some (OSig (FStar_Absyn_Syntax.Sig_new_effect (ne, _71_340)), _71_345) -> begin
Some (ne)
end
| _71_349 -> begin
None
end))


let is_effect_name : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((try_lookup_effect_name env lid)) with
| None -> begin
false
end
| Some (_71_354) -> begin
true
end))


let try_resolve_typ_abbrev : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.typ Prims.option = (fun env lid -> (

let find_in_sig = (fun lid -> (match ((let _172_379 = (sigmap env)
in (FStar_Util.smap_try_find _172_379 lid.FStar_Ident.str))) with
| Some (FStar_Absyn_Syntax.Sig_typ_abbrev (lid, tps, k, def, _71_365, _71_367), _71_371) -> begin
(

let t = (let _172_382 = (let _172_381 = (let _172_380 = (FStar_Absyn_Util.close_with_lam tps def)
in ((_172_380), (lid)))
in FStar_Absyn_Syntax.Meta_named (_172_381))
in (FStar_Absyn_Syntax.mk_Typ_meta _172_382))
in Some (t))
end
| _71_376 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))


let lookup_letbinding_quals : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.qualifier Prims.list = (fun env lid -> (

let find_in_sig = (fun lid -> (match ((let _172_389 = (sigmap env)
in (FStar_Util.smap_try_find _172_389 lid.FStar_Ident.str))) with
| Some (FStar_Absyn_Syntax.Sig_val_decl (lid, _71_383, quals, _71_386), _71_390) -> begin
Some (quals)
end
| _71_394 -> begin
None
end))
in (match ((resolve_in_open_namespaces env lid find_in_sig)) with
| Some (quals) -> begin
quals
end
| _71_398 -> begin
[]
end)))


let try_lookup_module : env  ->  Prims.string Prims.list  ->  FStar_Absyn_Syntax.modul Prims.option = (fun env path -> (match ((FStar_List.tryFind (fun _71_403 -> (match (_71_403) with
| (mlid, modul) -> begin
((FStar_Ident.path_of_lid mlid) = path)
end)) env.modules)) with
| Some (_71_405, modul) -> begin
Some (modul)
end
| None -> begin
None
end))


let try_lookup_let : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.exp Prims.option = (fun env lid -> (

let find_in_sig = (fun lid -> (match ((let _172_401 = (sigmap env)
in (FStar_Util.smap_try_find _172_401 lid.FStar_Ident.str))) with
| Some (FStar_Absyn_Syntax.Sig_let (_71_415), _71_418) -> begin
(let _172_402 = (FStar_Absyn_Util.fvar None lid (FStar_Ident.range_of_lid lid))
in Some (_172_402))
end
| _71_422 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))


let try_lookup_lid' : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.exp Prims.option = (fun any_val exclude_interf env lid -> (match ((try_lookup_name any_val exclude_interf env lid)) with
| Some (Exp_name (_71_428, e)) -> begin
Some (e)
end
| _71_434 -> begin
None
end))


let try_lookup_lid : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.exp Prims.option = (fun env l -> (try_lookup_lid' env.iface false env l))


let try_lookup_datacon : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.typ FStar_Absyn_Syntax.var Prims.option = (fun env lid -> (

let find_in_sig = (fun lid -> (match ((let _172_421 = (sigmap env)
in (FStar_Util.smap_try_find _172_421 lid.FStar_Ident.str))) with
| Some (FStar_Absyn_Syntax.Sig_val_decl (_71_442, _71_444, quals, _71_447), _71_451) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___400 -> (match (uu___400) with
| FStar_Absyn_Syntax.Assumption -> begin
true
end
| _71_457 -> begin
false
end)))) then begin
Some ((FStar_Absyn_Util.fv lid))
end else begin
None
end
end
| Some (FStar_Absyn_Syntax.Sig_datacon (_71_459), _71_462) -> begin
Some ((FStar_Absyn_Util.fv lid))
end
| _71_466 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))


let find_all_datacons : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.list Prims.option = (fun env lid -> (

let find_in_sig = (fun lid -> (match ((let _172_429 = (sigmap env)
in (FStar_Util.smap_try_find _172_429 lid.FStar_Ident.str))) with
| Some (FStar_Absyn_Syntax.Sig_tycon (_71_472, _71_474, _71_476, _71_478, datas, _71_481, _71_483), _71_487) -> begin
Some (datas)
end
| _71_491 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))


let record_cache_aux : ((Prims.unit  ->  Prims.unit) * (Prims.unit  ->  Prims.unit) * (Prims.unit  ->  record_or_dc Prims.list) * (record_or_dc  ->  Prims.unit)) = (

let record_cache = (FStar_Util.mk_ref (([])::[]))
in (

let push = (fun _71_494 -> (match (()) with
| () -> begin
(let _172_443 = (let _172_442 = (let _172_440 = (FStar_ST.read record_cache)
in (FStar_List.hd _172_440))
in (let _172_441 = (FStar_ST.read record_cache)
in (_172_442)::_172_441))
in (FStar_ST.op_Colon_Equals record_cache _172_443))
end))
in (

let pop = (fun _71_496 -> (match (()) with
| () -> begin
(let _172_447 = (let _172_446 = (FStar_ST.read record_cache)
in (FStar_List.tl _172_446))
in (FStar_ST.op_Colon_Equals record_cache _172_447))
end))
in (

let peek = (fun _71_498 -> (match (()) with
| () -> begin
(let _172_450 = (FStar_ST.read record_cache)
in (FStar_List.hd _172_450))
end))
in (

let insert = (fun r -> (let _172_457 = (let _172_456 = (let _172_453 = (peek ())
in (r)::_172_453)
in (let _172_455 = (let _172_454 = (FStar_ST.read record_cache)
in (FStar_List.tl _172_454))
in (_172_456)::_172_455))
in (FStar_ST.op_Colon_Equals record_cache _172_457)))
in ((push), (pop), (peek), (insert)))))))


let push_record_cache : Prims.unit  ->  Prims.unit = (

let _71_508 = record_cache_aux
in (match (_71_508) with
| (push, _71_503, _71_505, _71_507) -> begin
push
end))


let pop_record_cache : Prims.unit  ->  Prims.unit = (

let _71_516 = record_cache_aux
in (match (_71_516) with
| (_71_510, pop, _71_513, _71_515) -> begin
pop
end))


let peek_record_cache : Prims.unit  ->  record_or_dc Prims.list = (

let _71_524 = record_cache_aux
in (match (_71_524) with
| (_71_518, _71_520, peek, _71_523) -> begin
peek
end))


let insert_record_cache : record_or_dc  ->  Prims.unit = (

let _71_532 = record_cache_aux
in (match (_71_532) with
| (_71_526, _71_528, _71_530, insert) -> begin
insert
end))


let extract_record : env  ->  FStar_Absyn_Syntax.sigelt  ->  Prims.unit = (fun e uu___404 -> (match (uu___404) with
| FStar_Absyn_Syntax.Sig_bundle (sigs, _71_537, _71_539, _71_541) -> begin
(

let is_rec = (FStar_Util.for_some (fun uu___401 -> (match (uu___401) with
| (FStar_Absyn_Syntax.RecordType (_)) | (FStar_Absyn_Syntax.RecordConstructor (_)) -> begin
true
end
| _71_552 -> begin
false
end)))
in (

let find_dc = (fun dc -> (FStar_All.pipe_right sigs (FStar_Util.find_opt (fun uu___402 -> (match (uu___402) with
| FStar_Absyn_Syntax.Sig_datacon (lid, _71_559, _71_561, _71_563, _71_565, _71_567) -> begin
(FStar_Ident.lid_equals dc lid)
end
| _71_571 -> begin
false
end)))))
in (FStar_All.pipe_right sigs (FStar_List.iter (fun uu___403 -> (match (uu___403) with
| FStar_Absyn_Syntax.Sig_tycon (typename, parms, _71_576, _71_578, (dc)::[], tags, _71_583) -> begin
(match ((let _172_528 = (find_dc dc)
in (FStar_All.pipe_left FStar_Util.must _172_528))) with
| FStar_Absyn_Syntax.Sig_datacon (constrname, t, _71_589, _71_591, _71_593, _71_595) -> begin
(

let formals = (match ((FStar_Absyn_Util.function_formals t)) with
| Some (x, _71_600) -> begin
x
end
| _71_604 -> begin
[]
end)
in (

let is_rec = (is_rec tags)
in (

let fields = (FStar_All.pipe_right formals (FStar_List.collect (fun b -> (match (b) with
| (FStar_Util.Inr (x), q) -> begin
if ((FStar_Absyn_Syntax.is_null_binder b) || (is_rec && (match (q) with
| Some (FStar_Absyn_Syntax.Implicit (_71_613)) -> begin
true
end
| _71_617 -> begin
false
end))) then begin
[]
end else begin
(let _172_532 = (let _172_531 = (let _172_530 = if is_rec then begin
(FStar_Absyn_Util.unmangle_field_name x.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ppname)
end else begin
x.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ppname
end
in (qual constrname _172_530))
in ((_172_531), (x.FStar_Absyn_Syntax.sort)))
in (_172_532)::[])
end
end
| _71_619 -> begin
[]
end))))
in (

let record = {typename = typename; constrname = constrname; parms = parms; fields = fields; is_record = is_rec}
in (insert_record_cache record)))))
end
| _71_623 -> begin
()
end)
end
| _71_625 -> begin
()
end))))))
end
| _71_627 -> begin
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
(let _172_543 = (aux tl)
in (hd)::_172_543)
end))
in (aux ns)))
in (

let find_in_cache = (fun fieldname -> (

let _71_645 = ((fieldname.FStar_Ident.ns), (fieldname.FStar_Ident.ident))
in (match (_71_645) with
| (ns, fieldname) -> begin
(let _172_548 = (peek_record_cache ())
in (FStar_Util.find_map _172_548 (fun record -> (

let constrname = record.constrname.FStar_Ident.ident
in (

let ns = (maybe_add_constrname ns constrname)
in (

let fname = (FStar_Ident.lid_of_ids (FStar_List.append ns ((fieldname)::[])))
in (FStar_Util.find_map record.fields (fun _71_653 -> (match (_71_653) with
| (f, _71_652) -> begin
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
| _71_661 -> begin
None
end))


let try_lookup_projector_by_field_name : env  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * Prims.bool) Prims.option = (fun env fieldname -> (match ((try_lookup_record_or_dc_by_field_name env fieldname)) with
| Some (r, f) -> begin
Some (((f), (r.is_record)))
end
| _71_669 -> begin
None
end))


let qualify_field_to_record : env  ->  record_or_dc  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env recd f -> (

let qualify = (fun fieldname -> (

let _71_677 = ((fieldname.FStar_Ident.ns), (fieldname.FStar_Ident.ident))
in (match (_71_677) with
| (ns, fieldname) -> begin
(

let constrname = recd.constrname.FStar_Ident.ident
in (

let fname = (FStar_Ident.lid_of_ids (FStar_List.append ns (FStar_List.append ((constrname)::[]) ((fieldname)::[]))))
in (FStar_Util.find_map recd.fields (fun _71_683 -> (match (_71_683) with
| (f, _71_682) -> begin
if (FStar_Ident.lid_equals fname f) then begin
Some (fname)
end else begin
None
end
end)))))
end)))
in (resolve_in_open_namespaces env f qualify)))


let find_kind_abbrev : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env l -> (match ((try_lookup_name true (not (env.iface)) env l)) with
| Some (Knd_name (_71_687, l)) -> begin
Some (l)
end
| _71_693 -> begin
None
end))


let is_kind_abbrev : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (match ((find_kind_abbrev env l)) with
| None -> begin
false
end
| Some (_71_698) -> begin
true
end))


let unique_name : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  Prims.bool = (fun any_val exclude_if env lid -> (match ((try_lookup_lid' any_val exclude_if env lid)) with
| None -> begin
(match ((find_kind_abbrev env lid)) with
| None -> begin
true
end
| Some (_71_707) -> begin
false
end)
end
| Some (_71_710) -> begin
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

let _71_721 = env
in {curmodule = _71_721.curmodule; modules = _71_721.modules; open_namespaces = []; modul_abbrevs = _71_721.modul_abbrevs; sigaccum = _71_721.sigaccum; localbindings = _71_721.localbindings; recbindings = _71_721.recbindings; phase = _71_721.phase; sigmap = _71_721.sigmap; default_result_effect = _71_721.default_result_effect; iface = _71_721.iface; admitted_iface = _71_721.admitted_iface})
in ((unique_name any_val exclude_if this_env lid) && (unique_typ_name this_env lid))))


let gen_bvd = (fun uu___405 -> (match (uu___405) with
| Binding_typ_var (id) -> begin
(let _172_597 = (let _172_596 = (let _172_595 = (FStar_Absyn_Util.genident (Some (id.FStar_Ident.idRange)))
in ((id), (_172_595)))
in (FStar_Absyn_Util.mkbvd _172_596))
in FStar_Util.Inl (_172_597))
end
| Binding_var (id) -> begin
(let _172_600 = (let _172_599 = (let _172_598 = (FStar_Absyn_Util.genident (Some (id.FStar_Ident.idRange)))
in ((id), (_172_598)))
in (FStar_Absyn_Util.mkbvd _172_599))
in FStar_Util.Inr (_172_600))
end
| _71_730 -> begin
(failwith "Tried to generate a bound variable for a type constructor")
end))


let push_bvvdef : env  ->  FStar_Absyn_Syntax.bvvdef  ->  env = (fun env x -> (

let b = Binding_var (x.FStar_Absyn_Syntax.ppname)
in (

let _71_734 = env
in {curmodule = _71_734.curmodule; modules = _71_734.modules; open_namespaces = _71_734.open_namespaces; modul_abbrevs = _71_734.modul_abbrevs; sigaccum = _71_734.sigaccum; localbindings = (((FStar_Util.Inr (x)), (b)))::env.localbindings; recbindings = _71_734.recbindings; phase = _71_734.phase; sigmap = _71_734.sigmap; default_result_effect = _71_734.default_result_effect; iface = _71_734.iface; admitted_iface = _71_734.admitted_iface})))


let push_btvdef : env  ->  FStar_Absyn_Syntax.btvdef  ->  env = (fun env x -> (

let b = Binding_typ_var (x.FStar_Absyn_Syntax.ppname)
in (

let _71_739 = env
in {curmodule = _71_739.curmodule; modules = _71_739.modules; open_namespaces = _71_739.open_namespaces; modul_abbrevs = _71_739.modul_abbrevs; sigaccum = _71_739.sigaccum; localbindings = (((FStar_Util.Inl (x)), (b)))::env.localbindings; recbindings = _71_739.recbindings; phase = _71_739.phase; sigmap = _71_739.sigmap; default_result_effect = _71_739.default_result_effect; iface = _71_739.iface; admitted_iface = _71_739.admitted_iface})))


let push_local_binding : env  ->  binding  ->  (env * (FStar_Absyn_Syntax.btvdef, FStar_Absyn_Syntax.bvvdef) FStar_Util.either) = (fun env b -> (

let bvd = (gen_bvd b)
in (((

let _71_744 = env
in {curmodule = _71_744.curmodule; modules = _71_744.modules; open_namespaces = _71_744.open_namespaces; modul_abbrevs = _71_744.modul_abbrevs; sigaccum = _71_744.sigaccum; localbindings = (((bvd), (b)))::env.localbindings; recbindings = _71_744.recbindings; phase = _71_744.phase; sigmap = _71_744.sigmap; default_result_effect = _71_744.default_result_effect; iface = _71_744.iface; admitted_iface = _71_744.admitted_iface})), (bvd))))


let push_local_tbinding : env  ->  FStar_Ident.ident  ->  (env * FStar_Absyn_Syntax.btvdef) = (fun env a -> (match ((push_local_binding env (Binding_typ_var (a)))) with
| (env, FStar_Util.Inl (x)) -> begin
((env), (x))
end
| _71_753 -> begin
(failwith "impossible")
end))


let push_local_vbinding : env  ->  FStar_Ident.ident  ->  (env * FStar_Absyn_Syntax.bvvdef) = (fun env b -> (match ((push_local_binding env (Binding_var (b)))) with
| (env, FStar_Util.Inr (x)) -> begin
((env), (x))
end
| _71_761 -> begin
(failwith "impossible")
end))


let push_rec_binding : env  ->  binding  ->  env = (fun env b -> (match (b) with
| (Binding_let (lid)) | (Binding_tycon (lid)) -> begin
if (unique false true env lid) then begin
(

let _71_767 = env
in {curmodule = _71_767.curmodule; modules = _71_767.modules; open_namespaces = _71_767.open_namespaces; modul_abbrevs = _71_767.modul_abbrevs; sigaccum = _71_767.sigaccum; localbindings = _71_767.localbindings; recbindings = (b)::env.recbindings; phase = _71_767.phase; sigmap = _71_767.sigmap; default_result_effect = _71_767.default_result_effect; iface = _71_767.iface; admitted_iface = _71_767.admitted_iface})
end else begin
(Prims.raise (FStar_Errors.Error ((((Prims.strcat "Duplicate top-level names " lid.FStar_Ident.str)), ((FStar_Ident.range_of_lid lid))))))
end
end
| _71_770 -> begin
(failwith "Unexpected rec_binding")
end))


let push_sigelt : env  ->  FStar_Absyn_Syntax.sigelt  ->  env = (fun env s -> (

let err = (fun l -> (

let sopt = (let _172_631 = (sigmap env)
in (FStar_Util.smap_try_find _172_631 l.FStar_Ident.str))
in (

let r = (match (sopt) with
| Some (se, _71_778) -> begin
(match ((let _172_632 = (FStar_Absyn_Util.lids_of_sigelt se)
in (FStar_Util.find_opt (FStar_Ident.lid_equals l) _172_632))) with
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
in (let _172_635 = (let _172_634 = (let _172_633 = (FStar_Util.format2 "Duplicate top-level names [%s]; previously declared at %s" (FStar_Ident.text_of_lid l) r)
in ((_172_633), ((FStar_Ident.range_of_lid l))))
in FStar_Errors.Error (_172_634))
in (Prims.raise _172_635)))))
in (

let env = (

let _71_796 = (match (s) with
| FStar_Absyn_Syntax.Sig_let (_71_787) -> begin
((false), (true))
end
| FStar_Absyn_Syntax.Sig_bundle (_71_790) -> begin
((true), (true))
end
| _71_793 -> begin
((false), (false))
end)
in (match (_71_796) with
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

let _71_800 = (extract_record env s)
in (

let _71_802 = env
in {curmodule = _71_802.curmodule; modules = _71_802.modules; open_namespaces = _71_802.open_namespaces; modul_abbrevs = _71_802.modul_abbrevs; sigaccum = (s)::env.sigaccum; localbindings = _71_802.localbindings; recbindings = _71_802.recbindings; phase = _71_802.phase; sigmap = _71_802.sigmap; default_result_effect = _71_802.default_result_effect; iface = _71_802.iface; admitted_iface = _71_802.admitted_iface}))
end
| Some (l) -> begin
(err l)
end))
end))
in (

let _71_821 = (match (s) with
| FStar_Absyn_Syntax.Sig_bundle (ses, _71_809, _71_811, _71_813) -> begin
(let _172_639 = (FStar_List.map (fun se -> (let _172_638 = (FStar_Absyn_Util.lids_of_sigelt se)
in ((_172_638), (se)))) ses)
in ((env), (_172_639)))
end
| _71_818 -> begin
(let _172_642 = (let _172_641 = (let _172_640 = (FStar_Absyn_Util.lids_of_sigelt s)
in ((_172_640), (s)))
in (_172_641)::[])
in ((env), (_172_642)))
end)
in (match (_71_821) with
| (env, lss) -> begin
(

let _71_826 = (FStar_All.pipe_right lss (FStar_List.iter (fun _71_824 -> (match (_71_824) with
| (lids, se) -> begin
(FStar_All.pipe_right lids (FStar_List.iter (fun lid -> (let _172_645 = (sigmap env)
in (FStar_Util.smap_add _172_645 lid.FStar_Ident.str ((se), ((env.iface && (not (env.admitted_iface))))))))))
end))))
in env)
end)))))


let push_namespace : env  ->  FStar_Ident.lident  ->  env = (fun env lid -> (

let _71_830 = env
in {curmodule = _71_830.curmodule; modules = _71_830.modules; open_namespaces = (lid)::env.open_namespaces; modul_abbrevs = _71_830.modul_abbrevs; sigaccum = _71_830.sigaccum; localbindings = _71_830.localbindings; recbindings = _71_830.recbindings; phase = _71_830.phase; sigmap = _71_830.sigmap; default_result_effect = _71_830.default_result_effect; iface = _71_830.iface; admitted_iface = _71_830.admitted_iface}))


let push_module_abbrev : env  ->  FStar_Ident.ident  ->  FStar_Ident.lident  ->  env = (fun env x l -> if (FStar_All.pipe_right env.modul_abbrevs (FStar_Util.for_some (fun _71_838 -> (match (_71_838) with
| (y, _71_837) -> begin
(x.FStar_Ident.idText = y.FStar_Ident.idText)
end)))) then begin
(let _172_659 = (let _172_658 = (let _172_657 = (FStar_Util.format1 "Module %s is already defined" x.FStar_Ident.idText)
in ((_172_657), (x.FStar_Ident.idRange)))
in FStar_Errors.Error (_172_658))
in (Prims.raise _172_659))
end else begin
(

let _71_839 = env
in {curmodule = _71_839.curmodule; modules = _71_839.modules; open_namespaces = _71_839.open_namespaces; modul_abbrevs = (((x), (l)))::env.modul_abbrevs; sigaccum = _71_839.sigaccum; localbindings = _71_839.localbindings; recbindings = _71_839.recbindings; phase = _71_839.phase; sigmap = _71_839.sigmap; default_result_effect = _71_839.default_result_effect; iface = _71_839.iface; admitted_iface = _71_839.admitted_iface})
end)


let is_type_lid : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let aux = (fun _71_844 -> (match (()) with
| () -> begin
(match ((try_lookup_typ_name' false env lid)) with
| Some (_71_846) -> begin
true
end
| _71_849 -> begin
false
end)
end))
in if (lid.FStar_Ident.ns = []) then begin
(match ((try_lookup_id env lid.FStar_Ident.ident)) with
| Some (_71_851) -> begin
false
end
| _71_854 -> begin
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

let _71_865 = (let _172_673 = (let _172_672 = (FStar_Range.string_of_range (FStar_Ident.range_of_lid l))
in (let _172_671 = (FStar_Absyn_Print.sli l)
in (FStar_Util.format2 "%s: Warning: Admitting %s without a definition\n" _172_672 _172_671)))
in (FStar_Util.print_string _172_673))
in (let _172_674 = (sigmap env)
in (FStar_Util.smap_add _172_674 l.FStar_Ident.str ((FStar_Absyn_Syntax.Sig_val_decl (((l), (t), ((FStar_Absyn_Syntax.Assumption)::quals), (r)))), (false)))))
end
| Some (_71_868) -> begin
()
end)
end
| _71_871 -> begin
()
end)))))


let finish : env  ->  FStar_Absyn_Syntax.modul  ->  env = (fun env modul -> (

let _71_909 = (FStar_All.pipe_right modul.FStar_Absyn_Syntax.declarations (FStar_List.iter (fun uu___407 -> (match (uu___407) with
| FStar_Absyn_Syntax.Sig_bundle (ses, quals, _71_878, _71_880) -> begin
if (FStar_List.contains FStar_Absyn_Syntax.Private quals) then begin
(FStar_All.pipe_right ses (FStar_List.iter (fun uu___406 -> (match (uu___406) with
| FStar_Absyn_Syntax.Sig_datacon (lid, _71_886, _71_888, _71_890, _71_892, _71_894) -> begin
(let _172_681 = (sigmap env)
in (FStar_Util.smap_remove _172_681 lid.FStar_Ident.str))
end
| _71_898 -> begin
()
end))))
end else begin
()
end
end
| FStar_Absyn_Syntax.Sig_val_decl (lid, _71_901, quals, _71_904) -> begin
if (FStar_List.contains FStar_Absyn_Syntax.Private quals) then begin
(let _172_682 = (sigmap env)
in (FStar_Util.smap_remove _172_682 lid.FStar_Ident.str))
end else begin
()
end
end
| _71_908 -> begin
()
end))))
in (

let _71_911 = env
in {curmodule = None; modules = (((modul.FStar_Absyn_Syntax.name), (modul)))::env.modules; open_namespaces = []; modul_abbrevs = []; sigaccum = []; localbindings = []; recbindings = []; phase = FStar_Parser_AST.Un; sigmap = _71_911.sigmap; default_result_effect = _71_911.default_result_effect; iface = _71_911.iface; admitted_iface = _71_911.admitted_iface})))


let push : env  ->  env = (fun env -> (

let _71_914 = (push_record_cache ())
in (

let _71_916 = env
in (let _172_687 = (let _172_686 = (let _172_685 = (sigmap env)
in (FStar_Util.smap_copy _172_685))
in (_172_686)::env.sigmap)
in {curmodule = _71_916.curmodule; modules = _71_916.modules; open_namespaces = _71_916.open_namespaces; modul_abbrevs = _71_916.modul_abbrevs; sigaccum = _71_916.sigaccum; localbindings = _71_916.localbindings; recbindings = _71_916.recbindings; phase = _71_916.phase; sigmap = _172_687; default_result_effect = _71_916.default_result_effect; iface = _71_916.iface; admitted_iface = _71_916.admitted_iface}))))


let mark : env  ->  env = (fun env -> (push env))


let reset_mark : env  ->  env = (fun env -> (

let _71_920 = env
in (let _172_692 = (FStar_List.tl env.sigmap)
in {curmodule = _71_920.curmodule; modules = _71_920.modules; open_namespaces = _71_920.open_namespaces; modul_abbrevs = _71_920.modul_abbrevs; sigaccum = _71_920.sigaccum; localbindings = _71_920.localbindings; recbindings = _71_920.recbindings; phase = _71_920.phase; sigmap = _172_692; default_result_effect = _71_920.default_result_effect; iface = _71_920.iface; admitted_iface = _71_920.admitted_iface})))


let commit_mark : env  ->  env = (fun env -> (match (env.sigmap) with
| (hd)::(_71_925)::tl -> begin
(

let _71_929 = env
in {curmodule = _71_929.curmodule; modules = _71_929.modules; open_namespaces = _71_929.open_namespaces; modul_abbrevs = _71_929.modul_abbrevs; sigaccum = _71_929.sigaccum; localbindings = _71_929.localbindings; recbindings = _71_929.recbindings; phase = _71_929.phase; sigmap = (hd)::tl; default_result_effect = _71_929.default_result_effect; iface = _71_929.iface; admitted_iface = _71_929.admitted_iface})
end
| _71_932 -> begin
(failwith "Impossible")
end))


let pop : env  ->  env = (fun env -> (match (env.sigmap) with
| (_71_936)::maps -> begin
(

let _71_938 = (pop_record_cache ())
in (

let _71_940 = env
in {curmodule = _71_940.curmodule; modules = _71_940.modules; open_namespaces = _71_940.open_namespaces; modul_abbrevs = _71_940.modul_abbrevs; sigaccum = _71_940.sigaccum; localbindings = _71_940.localbindings; recbindings = _71_940.recbindings; phase = _71_940.phase; sigmap = maps; default_result_effect = _71_940.default_result_effect; iface = _71_940.iface; admitted_iface = _71_940.admitted_iface}))
end
| _71_943 -> begin
(failwith "No more modules to pop")
end))


let export_interface : FStar_Ident.lident  ->  env  ->  env = (fun m env -> (

let sigelt_in_m = (fun se -> (match ((FStar_Absyn_Util.lids_of_sigelt se)) with
| (l)::_71_949 -> begin
(l.FStar_Ident.nsstr = m.FStar_Ident.str)
end
| _71_953 -> begin
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

let _71_976 = (FStar_All.pipe_right keys (FStar_List.iter (fun k -> (match ((FStar_Util.smap_try_find sm' k)) with
| Some (se, true) when (sigelt_in_m se) -> begin
(

let _71_963 = (FStar_Util.smap_remove sm' k)
in (

let se = (match (se) with
| FStar_Absyn_Syntax.Sig_val_decl (l, t, q, r) -> begin
FStar_Absyn_Syntax.Sig_val_decl (((l), (t), ((FStar_Absyn_Syntax.Assumption)::q), (r)))
end
| _71_972 -> begin
se
end)
in (FStar_Util.smap_add sm' k ((se), (false)))))
end
| _71_975 -> begin
()
end))))
in env)))))))


let finish_module_or_interface : env  ->  FStar_Absyn_Syntax.modul  ->  env = (fun env modul -> (

let _71_980 = if (not (modul.FStar_Absyn_Syntax.is_interface)) then begin
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

let _71_989 = env
in {curmodule = Some (mname); modules = _71_989.modules; open_namespaces = open_ns; modul_abbrevs = _71_989.modul_abbrevs; sigaccum = _71_989.sigaccum; localbindings = _71_989.localbindings; recbindings = _71_989.recbindings; phase = _71_989.phase; sigmap = env.sigmap; default_result_effect = _71_989.default_result_effect; iface = intf; admitted_iface = admitted})))
in (match ((FStar_All.pipe_right env.modules (FStar_Util.find_opt (fun _71_994 -> (match (_71_994) with
| (l, _71_993) -> begin
(FStar_Ident.lid_equals l mname)
end))))) with
| None -> begin
(((prep env)), (false))
end
| Some (_71_997, m) -> begin
(let _172_721 = (let _172_720 = (let _172_719 = (FStar_Util.format1 "Duplicate module or interface name: %s" mname.FStar_Ident.str)
in ((_172_719), ((FStar_Ident.range_of_lid mname))))
in FStar_Errors.Error (_172_720))
in (Prims.raise _172_721))
end)))


let enter_monad_scope : env  ->  FStar_Ident.ident  ->  env = (fun env mname -> (

let curmod = (current_module env)
in (

let mscope = (FStar_Ident.lid_of_ids (FStar_List.append curmod.FStar_Ident.ns ((curmod.FStar_Ident.ident)::(mname)::[])))
in (

let _71_1005 = env
in {curmodule = Some (mscope); modules = _71_1005.modules; open_namespaces = (curmod)::env.open_namespaces; modul_abbrevs = _71_1005.modul_abbrevs; sigaccum = _71_1005.sigaccum; localbindings = _71_1005.localbindings; recbindings = _71_1005.recbindings; phase = _71_1005.phase; sigmap = _71_1005.sigmap; default_result_effect = _71_1005.default_result_effect; iface = _71_1005.iface; admitted_iface = _71_1005.admitted_iface}))))


let exit_monad_scope : env  ->  env  ->  env = (fun env0 env -> (

let _71_1009 = env
in {curmodule = env0.curmodule; modules = _71_1009.modules; open_namespaces = env0.open_namespaces; modul_abbrevs = _71_1009.modul_abbrevs; sigaccum = _71_1009.sigaccum; localbindings = _71_1009.localbindings; recbindings = _71_1009.recbindings; phase = _71_1009.phase; sigmap = _71_1009.sigmap; default_result_effect = _71_1009.default_result_effect; iface = _71_1009.iface; admitted_iface = _71_1009.admitted_iface}))


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
(let _172_736 = (FStar_Range.string_of_range r)
in (FStar_Util.format1 "(Possible clash with related name at %s)" _172_736))
end)
in (let _172_739 = (let _172_738 = (let _172_737 = (FStar_Util.format2 "Identifier not found: [%s] %s" (FStar_Ident.text_of_lid lid) msg)
in ((_172_737), ((FStar_Ident.range_of_lid lid))))
in FStar_Errors.Error (_172_738))
in (Prims.raise _172_739))))
end
| Some (r) -> begin
r
end))


let fail_or2 = (fun lookup id -> (match ((lookup id)) with
| None -> begin
(Prims.raise (FStar_Errors.Error ((((Prims.strcat "Identifier not found [" (Prims.strcat id.FStar_Ident.idText "]"))), (id.FStar_Ident.idRange)))))
end
| Some (r) -> begin
r
end))




