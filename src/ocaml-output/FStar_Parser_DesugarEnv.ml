
open Prims
# 29 "FStar.Parser.DesugarEnv.fst"
type binding =
| Binding_typ_var of FStar_Ident.ident
| Binding_var of FStar_Ident.ident
| Binding_let of FStar_Ident.lident
| Binding_tycon of FStar_Ident.lident

# 32 "FStar.Parser.DesugarEnv.fst"
let is_Binding_typ_var = (fun _discr_ -> (match (_discr_) with
| Binding_typ_var (_) -> begin
true
end
| _ -> begin
false
end))

# 33 "FStar.Parser.DesugarEnv.fst"
let is_Binding_var = (fun _discr_ -> (match (_discr_) with
| Binding_var (_) -> begin
true
end
| _ -> begin
false
end))

# 34 "FStar.Parser.DesugarEnv.fst"
let is_Binding_let = (fun _discr_ -> (match (_discr_) with
| Binding_let (_) -> begin
true
end
| _ -> begin
false
end))

# 35 "FStar.Parser.DesugarEnv.fst"
let is_Binding_tycon = (fun _discr_ -> (match (_discr_) with
| Binding_tycon (_) -> begin
true
end
| _ -> begin
false
end))

# 32 "FStar.Parser.DesugarEnv.fst"
let ___Binding_typ_var____0 = (fun projectee -> (match (projectee) with
| Binding_typ_var (_60_18) -> begin
_60_18
end))

# 33 "FStar.Parser.DesugarEnv.fst"
let ___Binding_var____0 = (fun projectee -> (match (projectee) with
| Binding_var (_60_21) -> begin
_60_21
end))

# 34 "FStar.Parser.DesugarEnv.fst"
let ___Binding_let____0 = (fun projectee -> (match (projectee) with
| Binding_let (_60_24) -> begin
_60_24
end))

# 35 "FStar.Parser.DesugarEnv.fst"
let ___Binding_tycon____0 = (fun projectee -> (match (projectee) with
| Binding_tycon (_60_27) -> begin
_60_27
end))

# 35 "FStar.Parser.DesugarEnv.fst"
type kind_abbrev =
(FStar_Ident.lident * (FStar_Absyn_Syntax.btvdef, FStar_Absyn_Syntax.bvvdef) FStar_Util.either Prims.list * FStar_Absyn_Syntax.knd)

# 37 "FStar.Parser.DesugarEnv.fst"
type env =
{curmodule : FStar_Ident.lident Prims.option; modules : (FStar_Ident.lident * FStar_Absyn_Syntax.modul) Prims.list; open_namespaces : FStar_Ident.lident Prims.list; modul_abbrevs : (FStar_Ident.ident * FStar_Ident.lident) Prims.list; sigaccum : FStar_Absyn_Syntax.sigelts; localbindings : ((FStar_Absyn_Syntax.btvdef, FStar_Absyn_Syntax.bvvdef) FStar_Util.either * binding) Prims.list; recbindings : binding Prims.list; phase : FStar_Parser_AST.level; sigmap : (FStar_Absyn_Syntax.sigelt * Prims.bool) FStar_Util.smap Prims.list; default_result_effect : FStar_Absyn_Syntax.typ  ->  FStar_Range.range  ->  FStar_Absyn_Syntax.comp; iface : Prims.bool; admitted_iface : Prims.bool}

# 38 "FStar.Parser.DesugarEnv.fst"
let is_Mkenv : env  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv"))))

# 51 "FStar.Parser.DesugarEnv.fst"
type occurrence =
| OSig of FStar_Absyn_Syntax.sigelt
| OLet of FStar_Ident.lident
| ORec of FStar_Ident.lident

# 54 "FStar.Parser.DesugarEnv.fst"
let is_OSig = (fun _discr_ -> (match (_discr_) with
| OSig (_) -> begin
true
end
| _ -> begin
false
end))

# 55 "FStar.Parser.DesugarEnv.fst"
let is_OLet = (fun _discr_ -> (match (_discr_) with
| OLet (_) -> begin
true
end
| _ -> begin
false
end))

# 56 "FStar.Parser.DesugarEnv.fst"
let is_ORec = (fun _discr_ -> (match (_discr_) with
| ORec (_) -> begin
true
end
| _ -> begin
false
end))

# 54 "FStar.Parser.DesugarEnv.fst"
let ___OSig____0 = (fun projectee -> (match (projectee) with
| OSig (_60_43) -> begin
_60_43
end))

# 55 "FStar.Parser.DesugarEnv.fst"
let ___OLet____0 = (fun projectee -> (match (projectee) with
| OLet (_60_46) -> begin
_60_46
end))

# 56 "FStar.Parser.DesugarEnv.fst"
let ___ORec____0 = (fun projectee -> (match (projectee) with
| ORec (_60_49) -> begin
_60_49
end))

# 56 "FStar.Parser.DesugarEnv.fst"
let range_of_occurrence : occurrence  ->  FStar_Range.range = (fun _60_1 -> (match (_60_1) with
| (OLet (l)) | (ORec (l)) -> begin
(FStar_Ident.range_of_lid l)
end
| OSig (se) -> begin
(FStar_Absyn_Util.range_of_sigelt se)
end))

# 60 "FStar.Parser.DesugarEnv.fst"
type foundname =
| Exp_name of (occurrence * FStar_Absyn_Syntax.exp)
| Typ_name of (occurrence * FStar_Absyn_Syntax.typ)
| Eff_name of (occurrence * FStar_Ident.lident)
| Knd_name of (occurrence * FStar_Ident.lident)

# 63 "FStar.Parser.DesugarEnv.fst"
let is_Exp_name = (fun _discr_ -> (match (_discr_) with
| Exp_name (_) -> begin
true
end
| _ -> begin
false
end))

# 64 "FStar.Parser.DesugarEnv.fst"
let is_Typ_name = (fun _discr_ -> (match (_discr_) with
| Typ_name (_) -> begin
true
end
| _ -> begin
false
end))

# 65 "FStar.Parser.DesugarEnv.fst"
let is_Eff_name = (fun _discr_ -> (match (_discr_) with
| Eff_name (_) -> begin
true
end
| _ -> begin
false
end))

# 66 "FStar.Parser.DesugarEnv.fst"
let is_Knd_name = (fun _discr_ -> (match (_discr_) with
| Knd_name (_) -> begin
true
end
| _ -> begin
false
end))

# 63 "FStar.Parser.DesugarEnv.fst"
let ___Exp_name____0 = (fun projectee -> (match (projectee) with
| Exp_name (_60_58) -> begin
_60_58
end))

# 64 "FStar.Parser.DesugarEnv.fst"
let ___Typ_name____0 = (fun projectee -> (match (projectee) with
| Typ_name (_60_61) -> begin
_60_61
end))

# 65 "FStar.Parser.DesugarEnv.fst"
let ___Eff_name____0 = (fun projectee -> (match (projectee) with
| Eff_name (_60_64) -> begin
_60_64
end))

# 66 "FStar.Parser.DesugarEnv.fst"
let ___Knd_name____0 = (fun projectee -> (match (projectee) with
| Knd_name (_60_67) -> begin
_60_67
end))

# 66 "FStar.Parser.DesugarEnv.fst"
type record_or_dc =
{typename : FStar_Ident.lident; constrname : FStar_Ident.lident; parms : FStar_Absyn_Syntax.binders; fields : (FStar_Absyn_Syntax.fieldname * FStar_Absyn_Syntax.typ) Prims.list; is_record : Prims.bool}

# 68 "FStar.Parser.DesugarEnv.fst"
let is_Mkrecord_or_dc : record_or_dc  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkrecord_or_dc"))))

# 121 "FStar.Parser.DesugarEnv.fst"
let open_modules : env  ->  (FStar_Ident.lident * FStar_Absyn_Syntax.modul) Prims.list = (fun e -> e.modules)

# 123 "FStar.Parser.DesugarEnv.fst"
let current_module : env  ->  FStar_Ident.lident = (fun env -> (match (env.curmodule) with
| None -> begin
(FStar_All.failwith "Unset current module")
end
| Some (m) -> begin
m
end))

# 126 "FStar.Parser.DesugarEnv.fst"
let qual : FStar_Ident.lident  ->  FStar_Ident.ident  ->  FStar_Ident.lident = (fun lid id -> (let _153_230 = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns ((lid.FStar_Ident.ident)::(id)::[])))
in (FStar_Ident.set_lid_range _153_230 id.FStar_Ident.idRange)))

# 127 "FStar.Parser.DesugarEnv.fst"
let qualify : env  ->  FStar_Ident.ident  ->  FStar_Ident.lident = (fun env id -> (let _153_235 = (current_module env)
in (qual _153_235 id)))

# 128 "FStar.Parser.DesugarEnv.fst"
let qualify_lid : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (
# 130 "FStar.Parser.DesugarEnv.fst"
let cur = (current_module env)
in (let _153_240 = (FStar_Ident.lid_of_ids (FStar_List.append cur.FStar_Ident.ns (FStar_List.append ((cur.FStar_Ident.ident)::[]) (FStar_List.append lid.FStar_Ident.ns ((lid.FStar_Ident.ident)::[])))))
in (FStar_Ident.set_lid_range _153_240 (FStar_Ident.range_of_lid lid)))))

# 131 "FStar.Parser.DesugarEnv.fst"
let new_sigmap = (fun _60_89 -> (match (()) with
| () -> begin
(FStar_Util.smap_create 100)
end))

# 132 "FStar.Parser.DesugarEnv.fst"
let empty_env : Prims.unit  ->  env = (fun _60_90 -> (match (()) with
| () -> begin
(let _153_245 = (let _153_244 = (new_sigmap ())
in (_153_244)::[])
in {curmodule = None; modules = []; open_namespaces = []; modul_abbrevs = []; sigaccum = []; localbindings = []; recbindings = []; phase = FStar_Parser_AST.Un; sigmap = _153_245; default_result_effect = FStar_Absyn_Util.ml_comp; iface = false; admitted_iface = false})
end))

# 144 "FStar.Parser.DesugarEnv.fst"
let sigmap : env  ->  (FStar_Absyn_Syntax.sigelt * Prims.bool) FStar_Util.smap = (fun env -> (FStar_List.hd env.sigmap))

# 145 "FStar.Parser.DesugarEnv.fst"
let default_total : env  ->  env = (fun env -> (
# 146 "FStar.Parser.DesugarEnv.fst"
let _60_93 = env
in {curmodule = _60_93.curmodule; modules = _60_93.modules; open_namespaces = _60_93.open_namespaces; modul_abbrevs = _60_93.modul_abbrevs; sigaccum = _60_93.sigaccum; localbindings = _60_93.localbindings; recbindings = _60_93.recbindings; phase = _60_93.phase; sigmap = _60_93.sigmap; default_result_effect = (fun t _60_96 -> (FStar_Absyn_Syntax.mk_Total t)); iface = _60_93.iface; admitted_iface = _60_93.admitted_iface}))

# 146 "FStar.Parser.DesugarEnv.fst"
let default_ml : env  ->  env = (fun env -> (
# 147 "FStar.Parser.DesugarEnv.fst"
let _60_99 = env
in {curmodule = _60_99.curmodule; modules = _60_99.modules; open_namespaces = _60_99.open_namespaces; modul_abbrevs = _60_99.modul_abbrevs; sigaccum = _60_99.sigaccum; localbindings = _60_99.localbindings; recbindings = _60_99.recbindings; phase = _60_99.phase; sigmap = _60_99.sigmap; default_result_effect = FStar_Absyn_Util.ml_comp; iface = _60_99.iface; admitted_iface = _60_99.admitted_iface}))

# 147 "FStar.Parser.DesugarEnv.fst"
let range_of_binding : binding  ->  FStar_Range.range = (fun _60_2 -> (match (_60_2) with
| (Binding_typ_var (id)) | (Binding_var (id)) -> begin
id.FStar_Ident.idRange
end
| (Binding_let (lid)) | (Binding_tycon (lid)) -> begin
(FStar_Ident.range_of_lid lid)
end))

# 153 "FStar.Parser.DesugarEnv.fst"
let try_lookup_typ_var : env  ->  FStar_Ident.ident  ->  FStar_Absyn_Syntax.typ Prims.option = (fun env id -> (
# 156 "FStar.Parser.DesugarEnv.fst"
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
(let _153_261 = (FStar_Absyn_Util.bvd_to_typ (FStar_Absyn_Util.set_bvd_range bvd id.FStar_Ident.idRange) FStar_Absyn_Syntax.kun)
in Some (_153_261))
end
| _60_128 -> begin
None
end)))

# 163 "FStar.Parser.DesugarEnv.fst"
let resolve_in_open_namespaces' = (fun env lid finder -> (
# 166 "FStar.Parser.DesugarEnv.fst"
let aux = (fun namespaces -> (match ((finder lid)) with
| Some (r) -> begin
Some (r)
end
| _60_138 -> begin
(
# 170 "FStar.Parser.DesugarEnv.fst"
let ids = (FStar_Ident.ids_of_lid lid)
in (FStar_Util.find_map namespaces (fun ns -> (
# 172 "FStar.Parser.DesugarEnv.fst"
let full_name = (FStar_Ident.lid_of_ids (FStar_List.append (FStar_Ident.ids_of_lid ns) ids))
in (finder full_name)))))
end))
in (let _153_272 = (let _153_271 = (current_module env)
in (_153_271)::env.open_namespaces)
in (aux _153_272))))

# 174 "FStar.Parser.DesugarEnv.fst"
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

# 184 "FStar.Parser.DesugarEnv.fst"
let resolve_in_open_namespaces = (fun env lid finder -> (let _153_288 = (expand_module_abbrevs env lid)
in (resolve_in_open_namespaces' env _153_288 finder)))

# 187 "FStar.Parser.DesugarEnv.fst"
let unmangleMap : (Prims.string * Prims.string) Prims.list = ((("op_ColonColon"), ("Cons")))::((("not"), ("op_Negation")))::[]

# 190 "FStar.Parser.DesugarEnv.fst"
let unmangleOpName : FStar_Ident.ident  ->  FStar_Ident.lident Prims.option = (fun id -> (FStar_Util.find_map unmangleMap (fun _60_165 -> (match (_60_165) with
| (x, y) -> begin
if (id.FStar_Ident.idText = x) then begin
(let _153_292 = (FStar_Ident.lid_of_path (("Prims")::(y)::[]) id.FStar_Ident.idRange)
in Some (_153_292))
end else begin
None
end
end))))

# 195 "FStar.Parser.DesugarEnv.fst"
let try_lookup_id' : env  ->  FStar_Ident.ident  ->  (FStar_Ident.lident * FStar_Absyn_Syntax.exp) Prims.option = (fun env id -> (match ((unmangleOpName id)) with
| Some (l) -> begin
(let _153_298 = (let _153_297 = (FStar_Absyn_Syntax.mk_Exp_fvar (((FStar_Absyn_Util.fv l)), (None)) None id.FStar_Ident.idRange)
in ((l), (_153_297)))
in Some (_153_298))
end
| _60_171 -> begin
(
# 201 "FStar.Parser.DesugarEnv.fst"
let found = (FStar_Util.find_map env.localbindings (fun _60_3 -> (match (_60_3) with
| (FStar_Util.Inl (_60_174), Binding_typ_var (id')) when (id'.FStar_Ident.idText = id.FStar_Ident.idText) -> begin
Some (FStar_Util.Inl (()))
end
| (FStar_Util.Inr (bvd), Binding_var (id')) when (id'.FStar_Ident.idText = id.FStar_Ident.idText) -> begin
(let _153_303 = (let _153_302 = (let _153_301 = (FStar_Ident.lid_of_ids ((id')::[]))
in (let _153_300 = (FStar_Absyn_Util.bvd_to_exp (FStar_Absyn_Util.set_bvd_range bvd id.FStar_Ident.idRange) FStar_Absyn_Syntax.tun)
in ((_153_301), (_153_300))))
in FStar_Util.Inr (_153_302))
in Some (_153_303))
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

# 207 "FStar.Parser.DesugarEnv.fst"
let try_lookup_id : env  ->  FStar_Ident.ident  ->  FStar_Absyn_Syntax.exp Prims.option = (fun env id -> (match ((try_lookup_id' env id)) with
| Some (_60_195, e) -> begin
Some (e)
end
| None -> begin
None
end))

# 212 "FStar.Parser.DesugarEnv.fst"
let fv_qual_of_se : FStar_Absyn_Syntax.sigelt  ->  FStar_Absyn_Syntax.fv_qual Prims.option = (fun _60_5 -> (match (_60_5) with
| FStar_Absyn_Syntax.Sig_datacon (_60_202, _60_204, (l, _60_207, _60_209), quals, _60_213, _60_215) -> begin
(
# 217 "FStar.Parser.DesugarEnv.fst"
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

# 226 "FStar.Parser.DesugarEnv.fst"
let try_lookup_name : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  foundname Prims.option = (fun any_val exclude_interf env lid -> (
# 236 "FStar.Parser.DesugarEnv.fst"
let find_in_sig = (fun lid -> (match ((let _153_321 = (sigmap env)
in (FStar_Util.smap_try_find _153_321 lid.FStar_Ident.str))) with
| Some (_60_244, true) when exclude_interf -> begin
None
end
| None -> begin
None
end
| Some (se, _60_251) -> begin
(match (se) with
| (FStar_Absyn_Syntax.Sig_typ_abbrev (_)) | (FStar_Absyn_Syntax.Sig_tycon (_)) -> begin
(let _153_324 = (let _153_323 = (let _153_322 = (FStar_Absyn_Util.ftv lid FStar_Absyn_Syntax.kun)
in ((OSig (se)), (_153_322)))
in Typ_name (_153_323))
in Some (_153_324))
end
| FStar_Absyn_Syntax.Sig_kind_abbrev (_60_261) -> begin
Some (Knd_name (((OSig (se)), (lid))))
end
| FStar_Absyn_Syntax.Sig_new_effect (ne, _60_265) -> begin
(let _153_327 = (let _153_326 = (let _153_325 = (FStar_Ident.set_lid_range ne.FStar_Absyn_Syntax.mname (FStar_Ident.range_of_lid lid))
in ((OSig (se)), (_153_325)))
in Eff_name (_153_326))
in Some (_153_327))
end
| FStar_Absyn_Syntax.Sig_effect_abbrev (_60_269) -> begin
Some (Eff_name (((OSig (se)), (lid))))
end
| FStar_Absyn_Syntax.Sig_datacon (_60_272) -> begin
(let _153_331 = (let _153_330 = (let _153_329 = (let _153_328 = (fv_qual_of_se se)
in (FStar_Absyn_Util.fvar _153_328 lid (FStar_Ident.range_of_lid lid)))
in ((OSig (se)), (_153_329)))
in Exp_name (_153_330))
in Some (_153_331))
end
| FStar_Absyn_Syntax.Sig_let (_60_275) -> begin
(let _153_334 = (let _153_333 = (let _153_332 = (FStar_Absyn_Util.fvar None lid (FStar_Ident.range_of_lid lid))
in ((OSig (se)), (_153_332)))
in Exp_name (_153_333))
in Some (_153_334))
end
| FStar_Absyn_Syntax.Sig_val_decl (_60_278, _60_280, quals, _60_283) -> begin
if (any_val || (FStar_All.pipe_right quals (FStar_Util.for_some (fun _60_6 -> (match (_60_6) with
| FStar_Absyn_Syntax.Assumption -> begin
true
end
| _60_289 -> begin
false
end))))) then begin
(let _153_339 = (let _153_338 = (let _153_337 = (let _153_336 = (fv_qual_of_se se)
in (FStar_Absyn_Util.fvar _153_336 lid (FStar_Ident.range_of_lid lid)))
in ((OSig (se)), (_153_337)))
in Exp_name (_153_338))
in Some (_153_339))
end else begin
None
end
end
| _60_291 -> begin
None
end)
end))
in (
# 256 "FStar.Parser.DesugarEnv.fst"
let found_id = (match (lid.FStar_Ident.ns) with
| [] -> begin
(match ((try_lookup_id' env lid.FStar_Ident.ident)) with
| Some (lid, e) -> begin
Some (Exp_name (((OLet (lid)), (e))))
end
| None -> begin
(
# 261 "FStar.Parser.DesugarEnv.fst"
let recname = (qualify env lid.FStar_Ident.ident)
in (FStar_Util.find_map env.recbindings (fun _60_7 -> (match (_60_7) with
| Binding_let (l) when (FStar_Ident.lid_equals l recname) -> begin
(let _153_343 = (let _153_342 = (let _153_341 = (FStar_Absyn_Util.fvar None recname (FStar_Ident.range_of_lid recname))
in ((ORec (l)), (_153_341)))
in Exp_name (_153_342))
in Some (_153_343))
end
| Binding_tycon (l) when (FStar_Ident.lid_equals l recname) -> begin
(let _153_346 = (let _153_345 = (let _153_344 = (FStar_Absyn_Util.ftv recname FStar_Absyn_Syntax.kun)
in ((ORec (l)), (_153_344)))
in Typ_name (_153_345))
in Some (_153_346))
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

# 272 "FStar.Parser.DesugarEnv.fst"
let try_lookup_typ_name' : Prims.bool  ->  env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.typ Prims.option = (fun exclude_interf env lid -> (match ((try_lookup_name true exclude_interf env lid)) with
| Some (Typ_name (_60_318, t)) -> begin
Some (t)
end
| Some (Eff_name (_60_324, l)) -> begin
(let _153_353 = (FStar_Absyn_Util.ftv l FStar_Absyn_Syntax.mk_Kind_unknown)
in Some (_153_353))
end
| _60_330 -> begin
None
end))

# 278 "FStar.Parser.DesugarEnv.fst"
let try_lookup_typ_name : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.typ Prims.option = (fun env l -> (try_lookup_typ_name' (not (env.iface)) env l))

# 279 "FStar.Parser.DesugarEnv.fst"
let try_lookup_effect_name' : Prims.bool  ->  env  ->  FStar_Ident.lident  ->  (occurrence * FStar_Ident.lident) Prims.option = (fun exclude_interf env lid -> (match ((try_lookup_name true exclude_interf env lid)) with
| Some (Eff_name (o, l)) -> begin
Some (((o), (l)))
end
| _60_342 -> begin
None
end))

# 284 "FStar.Parser.DesugarEnv.fst"
let try_lookup_effect_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env l -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some (o, l) -> begin
Some (l)
end
| _60_350 -> begin
None
end))

# 288 "FStar.Parser.DesugarEnv.fst"
let try_lookup_effect_defn : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.eff_decl Prims.option = (fun env l -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some (OSig (FStar_Absyn_Syntax.Sig_new_effect (ne, _60_355)), _60_360) -> begin
Some (ne)
end
| _60_364 -> begin
None
end))

# 292 "FStar.Parser.DesugarEnv.fst"
let is_effect_name : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((try_lookup_effect_name env lid)) with
| None -> begin
false
end
| Some (_60_369) -> begin
true
end))

# 296 "FStar.Parser.DesugarEnv.fst"
let try_resolve_typ_abbrev : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.typ Prims.option = (fun env lid -> (
# 299 "FStar.Parser.DesugarEnv.fst"
let find_in_sig = (fun lid -> (match ((let _153_382 = (sigmap env)
in (FStar_Util.smap_try_find _153_382 lid.FStar_Ident.str))) with
| Some (FStar_Absyn_Syntax.Sig_typ_abbrev (lid, tps, k, def, _60_380, _60_382), _60_386) -> begin
(
# 302 "FStar.Parser.DesugarEnv.fst"
let t = (let _153_385 = (let _153_384 = (let _153_383 = (FStar_Absyn_Util.close_with_lam tps def)
in ((_153_383), (lid)))
in FStar_Absyn_Syntax.Meta_named (_153_384))
in (FStar_Absyn_Syntax.mk_Typ_meta _153_385))
in Some (t))
end
| _60_391 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))

# 305 "FStar.Parser.DesugarEnv.fst"
let lookup_letbinding_quals : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.qualifier Prims.list = (fun env lid -> (
# 308 "FStar.Parser.DesugarEnv.fst"
let find_in_sig = (fun lid -> (match ((let _153_392 = (sigmap env)
in (FStar_Util.smap_try_find _153_392 lid.FStar_Ident.str))) with
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

# 314 "FStar.Parser.DesugarEnv.fst"
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

# 319 "FStar.Parser.DesugarEnv.fst"
let try_lookup_let : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.exp Prims.option = (fun env lid -> (
# 322 "FStar.Parser.DesugarEnv.fst"
let find_in_sig = (fun lid -> (match ((let _153_404 = (sigmap env)
in (FStar_Util.smap_try_find _153_404 lid.FStar_Ident.str))) with
| Some (FStar_Absyn_Syntax.Sig_let (_60_430), _60_433) -> begin
(let _153_405 = (FStar_Absyn_Util.fvar None lid (FStar_Ident.range_of_lid lid))
in Some (_153_405))
end
| _60_437 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))

# 326 "FStar.Parser.DesugarEnv.fst"
let try_lookup_lid' : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.exp Prims.option = (fun any_val exclude_interf env lid -> (match ((try_lookup_name any_val exclude_interf env lid)) with
| Some (Exp_name (_60_443, e)) -> begin
Some (e)
end
| _60_449 -> begin
None
end))

# 331 "FStar.Parser.DesugarEnv.fst"
let try_lookup_lid : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.exp Prims.option = (fun env l -> (try_lookup_lid' env.iface false env l))

# 332 "FStar.Parser.DesugarEnv.fst"
let try_lookup_datacon : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.typ FStar_Absyn_Syntax.var Prims.option = (fun env lid -> (
# 335 "FStar.Parser.DesugarEnv.fst"
let find_in_sig = (fun lid -> (match ((let _153_424 = (sigmap env)
in (FStar_Util.smap_try_find _153_424 lid.FStar_Ident.str))) with
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

# 343 "FStar.Parser.DesugarEnv.fst"
let find_all_datacons : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.list Prims.option = (fun env lid -> (
# 346 "FStar.Parser.DesugarEnv.fst"
let find_in_sig = (fun lid -> (match ((let _153_432 = (sigmap env)
in (FStar_Util.smap_try_find _153_432 lid.FStar_Ident.str))) with
| Some (FStar_Absyn_Syntax.Sig_tycon (_60_487, _60_489, _60_491, _60_493, datas, _60_496, _60_498), _60_502) -> begin
Some (datas)
end
| _60_506 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))

# 350 "FStar.Parser.DesugarEnv.fst"
let record_cache_aux : ((Prims.unit  ->  Prims.unit) * (Prims.unit  ->  Prims.unit) * (Prims.unit  ->  record_or_dc Prims.list) * (record_or_dc  ->  Prims.unit)) = (
# 354 "FStar.Parser.DesugarEnv.fst"
let record_cache = (FStar_Util.mk_ref (([])::[]))
in (
# 355 "FStar.Parser.DesugarEnv.fst"
let push = (fun _60_509 -> (match (()) with
| () -> begin
(let _153_446 = (let _153_445 = (let _153_443 = (FStar_ST.read record_cache)
in (FStar_List.hd _153_443))
in (let _153_444 = (FStar_ST.read record_cache)
in (_153_445)::_153_444))
in (FStar_ST.op_Colon_Equals record_cache _153_446))
end))
in (
# 357 "FStar.Parser.DesugarEnv.fst"
let pop = (fun _60_511 -> (match (()) with
| () -> begin
(let _153_450 = (let _153_449 = (FStar_ST.read record_cache)
in (FStar_List.tl _153_449))
in (FStar_ST.op_Colon_Equals record_cache _153_450))
end))
in (
# 359 "FStar.Parser.DesugarEnv.fst"
let peek = (fun _60_513 -> (match (()) with
| () -> begin
(let _153_453 = (FStar_ST.read record_cache)
in (FStar_List.hd _153_453))
end))
in (
# 360 "FStar.Parser.DesugarEnv.fst"
let insert = (fun r -> (let _153_460 = (let _153_459 = (let _153_456 = (peek ())
in (r)::_153_456)
in (let _153_458 = (let _153_457 = (FStar_ST.read record_cache)
in (FStar_List.tl _153_457))
in (_153_459)::_153_458))
in (FStar_ST.op_Colon_Equals record_cache _153_460)))
in ((push), (pop), (peek), (insert)))))))

# 361 "FStar.Parser.DesugarEnv.fst"
let push_record_cache : Prims.unit  ->  Prims.unit = (
# 364 "FStar.Parser.DesugarEnv.fst"
let _60_523 = record_cache_aux
in (match (_60_523) with
| (push, _60_518, _60_520, _60_522) -> begin
push
end))

# 365 "FStar.Parser.DesugarEnv.fst"
let pop_record_cache : Prims.unit  ->  Prims.unit = (
# 368 "FStar.Parser.DesugarEnv.fst"
let _60_531 = record_cache_aux
in (match (_60_531) with
| (_60_525, pop, _60_528, _60_530) -> begin
pop
end))

# 369 "FStar.Parser.DesugarEnv.fst"
let peek_record_cache : Prims.unit  ->  record_or_dc Prims.list = (
# 372 "FStar.Parser.DesugarEnv.fst"
let _60_539 = record_cache_aux
in (match (_60_539) with
| (_60_533, _60_535, peek, _60_538) -> begin
peek
end))

# 373 "FStar.Parser.DesugarEnv.fst"
let insert_record_cache : record_or_dc  ->  Prims.unit = (
# 376 "FStar.Parser.DesugarEnv.fst"
let _60_547 = record_cache_aux
in (match (_60_547) with
| (_60_541, _60_543, _60_545, insert) -> begin
insert
end))

# 377 "FStar.Parser.DesugarEnv.fst"
let extract_record : env  ->  FStar_Absyn_Syntax.sigelt  ->  Prims.unit = (fun e _60_12 -> (match (_60_12) with
| FStar_Absyn_Syntax.Sig_bundle (sigs, _60_552, _60_554, _60_556) -> begin
(
# 381 "FStar.Parser.DesugarEnv.fst"
let is_rec = (FStar_Util.for_some (fun _60_9 -> (match (_60_9) with
| (FStar_Absyn_Syntax.RecordType (_)) | (FStar_Absyn_Syntax.RecordConstructor (_)) -> begin
true
end
| _60_567 -> begin
false
end)))
in (
# 386 "FStar.Parser.DesugarEnv.fst"
let find_dc = (fun dc -> (FStar_All.pipe_right sigs (FStar_Util.find_opt (fun _60_10 -> (match (_60_10) with
| FStar_Absyn_Syntax.Sig_datacon (lid, _60_574, _60_576, _60_578, _60_580, _60_582) -> begin
(FStar_Ident.lid_equals dc lid)
end
| _60_586 -> begin
false
end)))))
in (FStar_All.pipe_right sigs (FStar_List.iter (fun _60_11 -> (match (_60_11) with
| FStar_Absyn_Syntax.Sig_tycon (typename, parms, _60_591, _60_593, (dc)::[], tags, _60_598) -> begin
(match ((let _153_531 = (find_dc dc)
in (FStar_All.pipe_left FStar_Util.must _153_531))) with
| FStar_Absyn_Syntax.Sig_datacon (constrname, t, _60_604, _60_606, _60_608, _60_610) -> begin
(
# 395 "FStar.Parser.DesugarEnv.fst"
let formals = (match ((FStar_Absyn_Util.function_formals t)) with
| Some (x, _60_615) -> begin
x
end
| _60_619 -> begin
[]
end)
in (
# 398 "FStar.Parser.DesugarEnv.fst"
let is_rec = (is_rec tags)
in (
# 399 "FStar.Parser.DesugarEnv.fst"
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
(let _153_535 = (let _153_534 = (let _153_533 = if is_rec then begin
(FStar_Absyn_Util.unmangle_field_name x.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ppname)
end else begin
x.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ppname
end
in (qual constrname _153_533))
in ((_153_534), (x.FStar_Absyn_Syntax.sort)))
in (_153_535)::[])
end
end
| _60_634 -> begin
[]
end))))
in (
# 406 "FStar.Parser.DesugarEnv.fst"
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

# 416 "FStar.Parser.DesugarEnv.fst"
let try_lookup_record_or_dc_by_field_name : env  ->  FStar_Ident.lident  ->  (record_or_dc * FStar_Ident.lident) Prims.option = (fun env fieldname -> (
# 419 "FStar.Parser.DesugarEnv.fst"
let maybe_add_constrname = (fun ns c -> (
# 420 "FStar.Parser.DesugarEnv.fst"
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
(let _153_546 = (aux tl)
in (hd)::_153_546)
end))
in (aux ns)))
in (
# 425 "FStar.Parser.DesugarEnv.fst"
let find_in_cache = (fun fieldname -> (
# 427 "FStar.Parser.DesugarEnv.fst"
let _60_660 = ((fieldname.FStar_Ident.ns), (fieldname.FStar_Ident.ident))
in (match (_60_660) with
| (ns, fieldname) -> begin
(let _153_551 = (peek_record_cache ())
in (FStar_Util.find_map _153_551 (fun record -> (
# 429 "FStar.Parser.DesugarEnv.fst"
let constrname = record.constrname.FStar_Ident.ident
in (
# 430 "FStar.Parser.DesugarEnv.fst"
let ns = (maybe_add_constrname ns constrname)
in (
# 431 "FStar.Parser.DesugarEnv.fst"
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

# 436 "FStar.Parser.DesugarEnv.fst"
let try_lookup_record_by_field_name : env  ->  FStar_Ident.lident  ->  (record_or_dc * FStar_Ident.lident) Prims.option = (fun env fieldname -> (match ((try_lookup_record_or_dc_by_field_name env fieldname)) with
| Some (r, f) when r.is_record -> begin
Some (((r), (f)))
end
| _60_676 -> begin
None
end))

# 441 "FStar.Parser.DesugarEnv.fst"
let try_lookup_projector_by_field_name : env  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * Prims.bool) Prims.option = (fun env fieldname -> (match ((try_lookup_record_or_dc_by_field_name env fieldname)) with
| Some (r, f) -> begin
Some (((f), (r.is_record)))
end
| _60_684 -> begin
None
end))

# 446 "FStar.Parser.DesugarEnv.fst"
let qualify_field_to_record : env  ->  record_or_dc  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env recd f -> (
# 449 "FStar.Parser.DesugarEnv.fst"
let qualify = (fun fieldname -> (
# 450 "FStar.Parser.DesugarEnv.fst"
let _60_692 = ((fieldname.FStar_Ident.ns), (fieldname.FStar_Ident.ident))
in (match (_60_692) with
| (ns, fieldname) -> begin
(
# 451 "FStar.Parser.DesugarEnv.fst"
let constrname = recd.constrname.FStar_Ident.ident
in (
# 452 "FStar.Parser.DesugarEnv.fst"
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

# 457 "FStar.Parser.DesugarEnv.fst"
let find_kind_abbrev : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env l -> (match ((try_lookup_name true (not (env.iface)) env l)) with
| Some (Knd_name (_60_702, l)) -> begin
Some (l)
end
| _60_708 -> begin
None
end))

# 462 "FStar.Parser.DesugarEnv.fst"
let is_kind_abbrev : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (match ((find_kind_abbrev env l)) with
| None -> begin
false
end
| Some (_60_713) -> begin
true
end))

# 467 "FStar.Parser.DesugarEnv.fst"
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

# 476 "FStar.Parser.DesugarEnv.fst"
let unique_typ_name : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((try_lookup_typ_name' true env lid)) with
| None -> begin
true
end
| Some (a) -> begin
false
end))

# 481 "FStar.Parser.DesugarEnv.fst"
let unique : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  Prims.bool = (fun any_val exclude_if env lid -> (
# 484 "FStar.Parser.DesugarEnv.fst"
let this_env = (
# 484 "FStar.Parser.DesugarEnv.fst"
let _60_736 = env
in {curmodule = _60_736.curmodule; modules = _60_736.modules; open_namespaces = []; modul_abbrevs = _60_736.modul_abbrevs; sigaccum = _60_736.sigaccum; localbindings = _60_736.localbindings; recbindings = _60_736.recbindings; phase = _60_736.phase; sigmap = _60_736.sigmap; default_result_effect = _60_736.default_result_effect; iface = _60_736.iface; admitted_iface = _60_736.admitted_iface})
in ((unique_name any_val exclude_if this_env lid) && (unique_typ_name this_env lid))))

# 485 "FStar.Parser.DesugarEnv.fst"
let gen_bvd = (fun _60_13 -> (match (_60_13) with
| Binding_typ_var (id) -> begin
(let _153_600 = (let _153_599 = (let _153_598 = (FStar_Absyn_Util.genident (Some (id.FStar_Ident.idRange)))
in ((id), (_153_598)))
in (FStar_Absyn_Util.mkbvd _153_599))
in FStar_Util.Inl (_153_600))
end
| Binding_var (id) -> begin
(let _153_603 = (let _153_602 = (let _153_601 = (FStar_Absyn_Util.genident (Some (id.FStar_Ident.idRange)))
in ((id), (_153_601)))
in (FStar_Absyn_Util.mkbvd _153_602))
in FStar_Util.Inr (_153_603))
end
| _60_745 -> begin
(FStar_All.failwith "Tried to generate a bound variable for a type constructor")
end))

# 490 "FStar.Parser.DesugarEnv.fst"
let push_bvvdef : env  ->  FStar_Absyn_Syntax.bvvdef  ->  env = (fun env x -> (
# 493 "FStar.Parser.DesugarEnv.fst"
let b = Binding_var (x.FStar_Absyn_Syntax.ppname)
in (
# 494 "FStar.Parser.DesugarEnv.fst"
let _60_749 = env
in {curmodule = _60_749.curmodule; modules = _60_749.modules; open_namespaces = _60_749.open_namespaces; modul_abbrevs = _60_749.modul_abbrevs; sigaccum = _60_749.sigaccum; localbindings = (((FStar_Util.Inr (x)), (b)))::env.localbindings; recbindings = _60_749.recbindings; phase = _60_749.phase; sigmap = _60_749.sigmap; default_result_effect = _60_749.default_result_effect; iface = _60_749.iface; admitted_iface = _60_749.admitted_iface})))

# 494 "FStar.Parser.DesugarEnv.fst"
let push_btvdef : env  ->  FStar_Absyn_Syntax.btvdef  ->  env = (fun env x -> (
# 497 "FStar.Parser.DesugarEnv.fst"
let b = Binding_typ_var (x.FStar_Absyn_Syntax.ppname)
in (
# 498 "FStar.Parser.DesugarEnv.fst"
let _60_754 = env
in {curmodule = _60_754.curmodule; modules = _60_754.modules; open_namespaces = _60_754.open_namespaces; modul_abbrevs = _60_754.modul_abbrevs; sigaccum = _60_754.sigaccum; localbindings = (((FStar_Util.Inl (x)), (b)))::env.localbindings; recbindings = _60_754.recbindings; phase = _60_754.phase; sigmap = _60_754.sigmap; default_result_effect = _60_754.default_result_effect; iface = _60_754.iface; admitted_iface = _60_754.admitted_iface})))

# 498 "FStar.Parser.DesugarEnv.fst"
let push_local_binding : env  ->  binding  ->  (env * (FStar_Absyn_Syntax.btvdef, FStar_Absyn_Syntax.bvvdef) FStar_Util.either) = (fun env b -> (
# 501 "FStar.Parser.DesugarEnv.fst"
let bvd = (gen_bvd b)
in (((
# 502 "FStar.Parser.DesugarEnv.fst"
let _60_759 = env
in {curmodule = _60_759.curmodule; modules = _60_759.modules; open_namespaces = _60_759.open_namespaces; modul_abbrevs = _60_759.modul_abbrevs; sigaccum = _60_759.sigaccum; localbindings = (((bvd), (b)))::env.localbindings; recbindings = _60_759.recbindings; phase = _60_759.phase; sigmap = _60_759.sigmap; default_result_effect = _60_759.default_result_effect; iface = _60_759.iface; admitted_iface = _60_759.admitted_iface})), (bvd))))

# 502 "FStar.Parser.DesugarEnv.fst"
let push_local_tbinding : env  ->  FStar_Ident.ident  ->  (env * FStar_Absyn_Syntax.btvdef) = (fun env a -> (match ((push_local_binding env (Binding_typ_var (a)))) with
| (env, FStar_Util.Inl (x)) -> begin
((env), (x))
end
| _60_768 -> begin
(FStar_All.failwith "impossible")
end))

# 507 "FStar.Parser.DesugarEnv.fst"
let push_local_vbinding : env  ->  FStar_Ident.ident  ->  (env * FStar_Absyn_Syntax.bvvdef) = (fun env b -> (match ((push_local_binding env (Binding_var (b)))) with
| (env, FStar_Util.Inr (x)) -> begin
((env), (x))
end
| _60_776 -> begin
(FStar_All.failwith "impossible")
end))

# 513 "FStar.Parser.DesugarEnv.fst"
let push_rec_binding : env  ->  binding  ->  env = (fun env b -> (match (b) with
| (Binding_let (lid)) | (Binding_tycon (lid)) -> begin
if (unique false true env lid) then begin
(
# 519 "FStar.Parser.DesugarEnv.fst"
let _60_782 = env
in {curmodule = _60_782.curmodule; modules = _60_782.modules; open_namespaces = _60_782.open_namespaces; modul_abbrevs = _60_782.modul_abbrevs; sigaccum = _60_782.sigaccum; localbindings = _60_782.localbindings; recbindings = (b)::env.recbindings; phase = _60_782.phase; sigmap = _60_782.sigmap; default_result_effect = _60_782.default_result_effect; iface = _60_782.iface; admitted_iface = _60_782.admitted_iface})
end else begin
(Prims.raise (FStar_Absyn_Syntax.Error ((((Prims.strcat "Duplicate top-level names " lid.FStar_Ident.str)), ((FStar_Ident.range_of_lid lid))))))
end
end
| _60_785 -> begin
(FStar_All.failwith "Unexpected rec_binding")
end))

# 521 "FStar.Parser.DesugarEnv.fst"
let push_sigelt : env  ->  FStar_Absyn_Syntax.sigelt  ->  env = (fun env s -> (
# 524 "FStar.Parser.DesugarEnv.fst"
let err = (fun l -> (
# 525 "FStar.Parser.DesugarEnv.fst"
let sopt = (let _153_634 = (sigmap env)
in (FStar_Util.smap_try_find _153_634 l.FStar_Ident.str))
in (
# 526 "FStar.Parser.DesugarEnv.fst"
let r = (match (sopt) with
| Some (se, _60_793) -> begin
(match ((let _153_635 = (FStar_Absyn_Util.lids_of_sigelt se)
in (FStar_Util.find_opt (FStar_Ident.lid_equals l) _153_635))) with
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
in (let _153_638 = (let _153_637 = (let _153_636 = (FStar_Util.format2 "Duplicate top-level names [%s]; previously declared at %s" (FStar_Ident.text_of_lid l) r)
in ((_153_636), ((FStar_Ident.range_of_lid l))))
in FStar_Absyn_Syntax.Error (_153_637))
in (Prims.raise _153_638)))))
in (
# 534 "FStar.Parser.DesugarEnv.fst"
let env = (
# 535 "FStar.Parser.DesugarEnv.fst"
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
# 539 "FStar.Parser.DesugarEnv.fst"
let lids = (FStar_Absyn_Util.lids_of_sigelt s)
in (match ((FStar_Util.find_map lids (fun l -> if (not ((unique any_val exclude_if env l))) then begin
Some (l)
end else begin
None
end))) with
| None -> begin
(
# 541 "FStar.Parser.DesugarEnv.fst"
let _60_815 = (extract_record env s)
in (
# 541 "FStar.Parser.DesugarEnv.fst"
let _60_817 = env
in {curmodule = _60_817.curmodule; modules = _60_817.modules; open_namespaces = _60_817.open_namespaces; modul_abbrevs = _60_817.modul_abbrevs; sigaccum = (s)::env.sigaccum; localbindings = _60_817.localbindings; recbindings = _60_817.recbindings; phase = _60_817.phase; sigmap = _60_817.sigmap; default_result_effect = _60_817.default_result_effect; iface = _60_817.iface; admitted_iface = _60_817.admitted_iface}))
end
| Some (l) -> begin
(err l)
end))
end))
in (
# 544 "FStar.Parser.DesugarEnv.fst"
let _60_836 = (match (s) with
| FStar_Absyn_Syntax.Sig_bundle (ses, _60_824, _60_826, _60_828) -> begin
(let _153_642 = (FStar_List.map (fun se -> (let _153_641 = (FStar_Absyn_Util.lids_of_sigelt se)
in ((_153_641), (se)))) ses)
in ((env), (_153_642)))
end
| _60_833 -> begin
(let _153_645 = (let _153_644 = (let _153_643 = (FStar_Absyn_Util.lids_of_sigelt s)
in ((_153_643), (s)))
in (_153_644)::[])
in ((env), (_153_645)))
end)
in (match (_60_836) with
| (env, lss) -> begin
(
# 547 "FStar.Parser.DesugarEnv.fst"
let _60_841 = (FStar_All.pipe_right lss (FStar_List.iter (fun _60_839 -> (match (_60_839) with
| (lids, se) -> begin
(FStar_All.pipe_right lids (FStar_List.iter (fun lid -> (let _153_648 = (sigmap env)
in (FStar_Util.smap_add _153_648 lid.FStar_Ident.str ((se), ((env.iface && (not (env.admitted_iface))))))))))
end))))
in env)
end)))))

# 550 "FStar.Parser.DesugarEnv.fst"
let push_namespace : env  ->  FStar_Ident.lident  ->  env = (fun env lid -> (
# 553 "FStar.Parser.DesugarEnv.fst"
let _60_845 = env
in {curmodule = _60_845.curmodule; modules = _60_845.modules; open_namespaces = (lid)::env.open_namespaces; modul_abbrevs = _60_845.modul_abbrevs; sigaccum = _60_845.sigaccum; localbindings = _60_845.localbindings; recbindings = _60_845.recbindings; phase = _60_845.phase; sigmap = _60_845.sigmap; default_result_effect = _60_845.default_result_effect; iface = _60_845.iface; admitted_iface = _60_845.admitted_iface}))

# 553 "FStar.Parser.DesugarEnv.fst"
let push_module_abbrev : env  ->  FStar_Ident.ident  ->  FStar_Ident.lident  ->  env = (fun env x l -> if (FStar_All.pipe_right env.modul_abbrevs (FStar_Util.for_some (fun _60_853 -> (match (_60_853) with
| (y, _60_852) -> begin
(x.FStar_Ident.idText = y.FStar_Ident.idText)
end)))) then begin
(let _153_662 = (let _153_661 = (let _153_660 = (FStar_Util.format1 "Module %s is already defined" x.FStar_Ident.idText)
in ((_153_660), (x.FStar_Ident.idRange)))
in FStar_Absyn_Syntax.Error (_153_661))
in (Prims.raise _153_662))
end else begin
(
# 558 "FStar.Parser.DesugarEnv.fst"
let _60_854 = env
in {curmodule = _60_854.curmodule; modules = _60_854.modules; open_namespaces = _60_854.open_namespaces; modul_abbrevs = (((x), (l)))::env.modul_abbrevs; sigaccum = _60_854.sigaccum; localbindings = _60_854.localbindings; recbindings = _60_854.recbindings; phase = _60_854.phase; sigmap = _60_854.sigmap; default_result_effect = _60_854.default_result_effect; iface = _60_854.iface; admitted_iface = _60_854.admitted_iface})
end)

# 558 "FStar.Parser.DesugarEnv.fst"
let is_type_lid : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (
# 561 "FStar.Parser.DesugarEnv.fst"
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

# 568 "FStar.Parser.DesugarEnv.fst"
let check_admits : FStar_Ident.lident  ->  env  ->  Prims.unit = (fun nm env -> (FStar_All.pipe_right env.sigaccum (FStar_List.iter (fun se -> (match (se) with
| FStar_Absyn_Syntax.Sig_val_decl (l, t, quals, r) -> begin
(match ((try_lookup_lid env l)) with
| None -> begin
(
# 576 "FStar.Parser.DesugarEnv.fst"
let _60_880 = (let _153_676 = (let _153_675 = (FStar_Range.string_of_range (FStar_Ident.range_of_lid l))
in (let _153_674 = (FStar_Absyn_Print.sli l)
in (FStar_Util.format2 "%s: Warning: Admitting %s without a definition\n" _153_675 _153_674)))
in (FStar_Util.print_string _153_676))
in (let _153_677 = (sigmap env)
in (FStar_Util.smap_add _153_677 l.FStar_Ident.str ((FStar_Absyn_Syntax.Sig_val_decl (((l), (t), ((FStar_Absyn_Syntax.Assumption)::quals), (r)))), (false)))))
end
| Some (_60_883) -> begin
()
end)
end
| _60_886 -> begin
()
end)))))

# 580 "FStar.Parser.DesugarEnv.fst"
let finish : env  ->  FStar_Absyn_Syntax.modul  ->  env = (fun env modul -> (
# 583 "FStar.Parser.DesugarEnv.fst"
let _60_924 = (FStar_All.pipe_right modul.FStar_Absyn_Syntax.declarations (FStar_List.iter (fun _60_15 -> (match (_60_15) with
| FStar_Absyn_Syntax.Sig_bundle (ses, quals, _60_893, _60_895) -> begin
if (FStar_List.contains FStar_Absyn_Syntax.Private quals) then begin
(FStar_All.pipe_right ses (FStar_List.iter (fun _60_14 -> (match (_60_14) with
| FStar_Absyn_Syntax.Sig_datacon (lid, _60_901, _60_903, _60_905, _60_907, _60_909) -> begin
(let _153_684 = (sigmap env)
in (FStar_Util.smap_remove _153_684 lid.FStar_Ident.str))
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
(let _153_685 = (sigmap env)
in (FStar_Util.smap_remove _153_685 lid.FStar_Ident.str))
end else begin
()
end
end
| _60_923 -> begin
()
end))))
in (
# 593 "FStar.Parser.DesugarEnv.fst"
let _60_926 = env
in {curmodule = None; modules = (((modul.FStar_Absyn_Syntax.name), (modul)))::env.modules; open_namespaces = []; modul_abbrevs = []; sigaccum = []; localbindings = []; recbindings = []; phase = FStar_Parser_AST.Un; sigmap = _60_926.sigmap; default_result_effect = _60_926.default_result_effect; iface = _60_926.iface; admitted_iface = _60_926.admitted_iface})))

# 601 "FStar.Parser.DesugarEnv.fst"
let push : env  ->  env = (fun env -> (
# 604 "FStar.Parser.DesugarEnv.fst"
let _60_929 = (push_record_cache ())
in (
# 605 "FStar.Parser.DesugarEnv.fst"
let _60_931 = env
in (let _153_690 = (let _153_689 = (let _153_688 = (sigmap env)
in (FStar_Util.smap_copy _153_688))
in (_153_689)::env.sigmap)
in {curmodule = _60_931.curmodule; modules = _60_931.modules; open_namespaces = _60_931.open_namespaces; modul_abbrevs = _60_931.modul_abbrevs; sigaccum = _60_931.sigaccum; localbindings = _60_931.localbindings; recbindings = _60_931.recbindings; phase = _60_931.phase; sigmap = _153_690; default_result_effect = _60_931.default_result_effect; iface = _60_931.iface; admitted_iface = _60_931.admitted_iface}))))

# 606 "FStar.Parser.DesugarEnv.fst"
let mark : env  ->  env = (fun env -> (push env))

# 608 "FStar.Parser.DesugarEnv.fst"
let reset_mark : env  ->  env = (fun env -> (
# 609 "FStar.Parser.DesugarEnv.fst"
let _60_935 = env
in (let _153_695 = (FStar_List.tl env.sigmap)
in {curmodule = _60_935.curmodule; modules = _60_935.modules; open_namespaces = _60_935.open_namespaces; modul_abbrevs = _60_935.modul_abbrevs; sigaccum = _60_935.sigaccum; localbindings = _60_935.localbindings; recbindings = _60_935.recbindings; phase = _60_935.phase; sigmap = _153_695; default_result_effect = _60_935.default_result_effect; iface = _60_935.iface; admitted_iface = _60_935.admitted_iface})))

# 609 "FStar.Parser.DesugarEnv.fst"
let commit_mark : env  ->  env = (fun env -> (match (env.sigmap) with
| (hd)::(_60_940)::tl -> begin
(
# 611 "FStar.Parser.DesugarEnv.fst"
let _60_944 = env
in {curmodule = _60_944.curmodule; modules = _60_944.modules; open_namespaces = _60_944.open_namespaces; modul_abbrevs = _60_944.modul_abbrevs; sigaccum = _60_944.sigaccum; localbindings = _60_944.localbindings; recbindings = _60_944.recbindings; phase = _60_944.phase; sigmap = (hd)::tl; default_result_effect = _60_944.default_result_effect; iface = _60_944.iface; admitted_iface = _60_944.admitted_iface})
end
| _60_947 -> begin
(FStar_All.failwith "Impossible")
end))

# 612 "FStar.Parser.DesugarEnv.fst"
let pop : env  ->  env = (fun env -> (match (env.sigmap) with
| (_60_951)::maps -> begin
(
# 615 "FStar.Parser.DesugarEnv.fst"
let _60_953 = (pop_record_cache ())
in (
# 616 "FStar.Parser.DesugarEnv.fst"
let _60_955 = env
in {curmodule = _60_955.curmodule; modules = _60_955.modules; open_namespaces = _60_955.open_namespaces; modul_abbrevs = _60_955.modul_abbrevs; sigaccum = _60_955.sigaccum; localbindings = _60_955.localbindings; recbindings = _60_955.recbindings; phase = _60_955.phase; sigmap = maps; default_result_effect = _60_955.default_result_effect; iface = _60_955.iface; admitted_iface = _60_955.admitted_iface}))
end
| _60_958 -> begin
(FStar_All.failwith "No more modules to pop")
end))

# 618 "FStar.Parser.DesugarEnv.fst"
let export_interface : FStar_Ident.lident  ->  env  ->  env = (fun m env -> (
# 622 "FStar.Parser.DesugarEnv.fst"
let sigelt_in_m = (fun se -> (match ((FStar_Absyn_Util.lids_of_sigelt se)) with
| (l)::_60_964 -> begin
(l.FStar_Ident.nsstr = m.FStar_Ident.str)
end
| _60_968 -> begin
false
end))
in (
# 626 "FStar.Parser.DesugarEnv.fst"
let sm = (sigmap env)
in (
# 627 "FStar.Parser.DesugarEnv.fst"
let env = (pop env)
in (
# 628 "FStar.Parser.DesugarEnv.fst"
let keys = (FStar_Util.smap_keys sm)
in (
# 629 "FStar.Parser.DesugarEnv.fst"
let sm' = (sigmap env)
in (
# 630 "FStar.Parser.DesugarEnv.fst"
let _60_991 = (FStar_All.pipe_right keys (FStar_List.iter (fun k -> (match ((FStar_Util.smap_try_find sm' k)) with
| Some (se, true) when (sigelt_in_m se) -> begin
(
# 633 "FStar.Parser.DesugarEnv.fst"
let _60_978 = (FStar_Util.smap_remove sm' k)
in (
# 635 "FStar.Parser.DesugarEnv.fst"
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

# 640 "FStar.Parser.DesugarEnv.fst"
let finish_module_or_interface : env  ->  FStar_Absyn_Syntax.modul  ->  env = (fun env modul -> (
# 643 "FStar.Parser.DesugarEnv.fst"
let _60_995 = if (not (modul.FStar_Absyn_Syntax.is_interface)) then begin
(check_admits modul.FStar_Absyn_Syntax.name env)
end else begin
()
end
in (finish env modul)))

# 645 "FStar.Parser.DesugarEnv.fst"
let prepare_module_or_interface : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  (env * Prims.bool) = (fun intf admitted env mname -> (
# 648 "FStar.Parser.DesugarEnv.fst"
let prep = (fun env -> (
# 650 "FStar.Parser.DesugarEnv.fst"
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
# 658 "FStar.Parser.DesugarEnv.fst"
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
(let _153_724 = (let _153_723 = (let _153_722 = (FStar_Util.format1 "Duplicate module or interface name: %s" mname.FStar_Ident.str)
in ((_153_722), ((FStar_Ident.range_of_lid mname))))
in FStar_Absyn_Syntax.Error (_153_723))
in (Prims.raise _153_724))
end)))

# 662 "FStar.Parser.DesugarEnv.fst"
let enter_monad_scope : env  ->  FStar_Ident.ident  ->  env = (fun env mname -> (
# 665 "FStar.Parser.DesugarEnv.fst"
let curmod = (current_module env)
in (
# 666 "FStar.Parser.DesugarEnv.fst"
let mscope = (FStar_Ident.lid_of_ids (FStar_List.append curmod.FStar_Ident.ns ((curmod.FStar_Ident.ident)::(mname)::[])))
in (
# 667 "FStar.Parser.DesugarEnv.fst"
let _60_1020 = env
in {curmodule = Some (mscope); modules = _60_1020.modules; open_namespaces = (curmod)::env.open_namespaces; modul_abbrevs = _60_1020.modul_abbrevs; sigaccum = _60_1020.sigaccum; localbindings = _60_1020.localbindings; recbindings = _60_1020.recbindings; phase = _60_1020.phase; sigmap = _60_1020.sigmap; default_result_effect = _60_1020.default_result_effect; iface = _60_1020.iface; admitted_iface = _60_1020.admitted_iface}))))

# 669 "FStar.Parser.DesugarEnv.fst"
let exit_monad_scope : env  ->  env  ->  env = (fun env0 env -> (
# 672 "FStar.Parser.DesugarEnv.fst"
let _60_1024 = env
in {curmodule = env0.curmodule; modules = _60_1024.modules; open_namespaces = env0.open_namespaces; modul_abbrevs = _60_1024.modul_abbrevs; sigaccum = _60_1024.sigaccum; localbindings = _60_1024.localbindings; recbindings = _60_1024.recbindings; phase = _60_1024.phase; sigmap = _60_1024.sigmap; default_result_effect = _60_1024.default_result_effect; iface = _60_1024.iface; admitted_iface = _60_1024.admitted_iface}))

# 674 "FStar.Parser.DesugarEnv.fst"
let fail_or = (fun env lookup lid -> (match ((lookup lid)) with
| None -> begin
(
# 678 "FStar.Parser.DesugarEnv.fst"
let r = (match ((try_lookup_name true false env lid)) with
| None -> begin
None
end
| (Some (Knd_name (o, _))) | (Some (Eff_name (o, _))) | (Some (Typ_name (o, _))) | (Some (Exp_name (o, _))) -> begin
Some ((range_of_occurrence o))
end)
in (
# 684 "FStar.Parser.DesugarEnv.fst"
let msg = (match (r) with
| None -> begin
""
end
| Some (r) -> begin
(let _153_739 = (FStar_Range.string_of_range r)
in (FStar_Util.format1 "(Possible clash with related name at %s)" _153_739))
end)
in (let _153_742 = (let _153_741 = (let _153_740 = (FStar_Util.format2 "Identifier not found: [%s] %s" (FStar_Ident.text_of_lid lid) msg)
in ((_153_740), ((FStar_Ident.range_of_lid lid))))
in FStar_Absyn_Syntax.Error (_153_741))
in (Prims.raise _153_742))))
end
| Some (r) -> begin
r
end))

# 688 "FStar.Parser.DesugarEnv.fst"
let fail_or2 = (fun lookup id -> (match ((lookup id)) with
| None -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((((Prims.strcat "Identifier not found [" (Prims.strcat id.FStar_Ident.idText "]"))), (id.FStar_Ident.idRange)))))
end
| Some (r) -> begin
r
end))




