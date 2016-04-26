
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
| Binding_typ_var (_59_18) -> begin
_59_18
end))

# 33 "FStar.Parser.DesugarEnv.fst"
let ___Binding_var____0 = (fun projectee -> (match (projectee) with
| Binding_var (_59_21) -> begin
_59_21
end))

# 34 "FStar.Parser.DesugarEnv.fst"
let ___Binding_let____0 = (fun projectee -> (match (projectee) with
| Binding_let (_59_24) -> begin
_59_24
end))

# 35 "FStar.Parser.DesugarEnv.fst"
let ___Binding_tycon____0 = (fun projectee -> (match (projectee) with
| Binding_tycon (_59_27) -> begin
_59_27
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
| OSig (_59_43) -> begin
_59_43
end))

# 55 "FStar.Parser.DesugarEnv.fst"
let ___OLet____0 = (fun projectee -> (match (projectee) with
| OLet (_59_46) -> begin
_59_46
end))

# 56 "FStar.Parser.DesugarEnv.fst"
let ___ORec____0 = (fun projectee -> (match (projectee) with
| ORec (_59_49) -> begin
_59_49
end))

# 56 "FStar.Parser.DesugarEnv.fst"
let range_of_occurrence : occurrence  ->  FStar_Range.range = (fun _59_1 -> (match (_59_1) with
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
| Exp_name (_59_58) -> begin
_59_58
end))

# 64 "FStar.Parser.DesugarEnv.fst"
let ___Typ_name____0 = (fun projectee -> (match (projectee) with
| Typ_name (_59_61) -> begin
_59_61
end))

# 65 "FStar.Parser.DesugarEnv.fst"
let ___Eff_name____0 = (fun projectee -> (match (projectee) with
| Eff_name (_59_64) -> begin
_59_64
end))

# 66 "FStar.Parser.DesugarEnv.fst"
let ___Knd_name____0 = (fun projectee -> (match (projectee) with
| Knd_name (_59_67) -> begin
_59_67
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
let qual : FStar_Ident.lident  ->  FStar_Ident.ident  ->  FStar_Ident.lident = (fun lid id -> (let _148_230 = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns ((lid.FStar_Ident.ident)::(id)::[])))
in (FStar_Ident.set_lid_range _148_230 id.FStar_Ident.idRange)))

# 127 "FStar.Parser.DesugarEnv.fst"
let qualify : env  ->  FStar_Ident.ident  ->  FStar_Ident.lident = (fun env id -> (let _148_235 = (current_module env)
in (qual _148_235 id)))

# 128 "FStar.Parser.DesugarEnv.fst"
let qualify_lid : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (
# 130 "FStar.Parser.DesugarEnv.fst"
let cur = (current_module env)
in (let _148_240 = (FStar_Ident.lid_of_ids (FStar_List.append (FStar_List.append (FStar_List.append cur.FStar_Ident.ns ((cur.FStar_Ident.ident)::[])) lid.FStar_Ident.ns) ((lid.FStar_Ident.ident)::[])))
in (FStar_Ident.set_lid_range _148_240 (FStar_Ident.range_of_lid lid)))))

# 131 "FStar.Parser.DesugarEnv.fst"
let new_sigmap = (fun _59_89 -> (match (()) with
| () -> begin
(FStar_Util.smap_create 100)
end))

# 132 "FStar.Parser.DesugarEnv.fst"
let empty_env : Prims.unit  ->  env = (fun _59_90 -> (match (()) with
| () -> begin
(let _148_245 = (let _148_244 = (new_sigmap ())
in (_148_244)::[])
in {curmodule = None; modules = []; open_namespaces = []; modul_abbrevs = []; sigaccum = []; localbindings = []; recbindings = []; phase = FStar_Parser_AST.Un; sigmap = _148_245; default_result_effect = FStar_Absyn_Util.ml_comp; iface = false; admitted_iface = false})
end))

# 144 "FStar.Parser.DesugarEnv.fst"
let sigmap : env  ->  (FStar_Absyn_Syntax.sigelt * Prims.bool) FStar_Util.smap = (fun env -> (FStar_List.hd env.sigmap))

# 145 "FStar.Parser.DesugarEnv.fst"
let default_total : env  ->  env = (fun env -> (
# 146 "FStar.Parser.DesugarEnv.fst"
let _59_93 = env
in {curmodule = _59_93.curmodule; modules = _59_93.modules; open_namespaces = _59_93.open_namespaces; modul_abbrevs = _59_93.modul_abbrevs; sigaccum = _59_93.sigaccum; localbindings = _59_93.localbindings; recbindings = _59_93.recbindings; phase = _59_93.phase; sigmap = _59_93.sigmap; default_result_effect = (fun t _59_96 -> (FStar_Absyn_Syntax.mk_Total t)); iface = _59_93.iface; admitted_iface = _59_93.admitted_iface}))

# 146 "FStar.Parser.DesugarEnv.fst"
let default_ml : env  ->  env = (fun env -> (
# 147 "FStar.Parser.DesugarEnv.fst"
let _59_99 = env
in {curmodule = _59_99.curmodule; modules = _59_99.modules; open_namespaces = _59_99.open_namespaces; modul_abbrevs = _59_99.modul_abbrevs; sigaccum = _59_99.sigaccum; localbindings = _59_99.localbindings; recbindings = _59_99.recbindings; phase = _59_99.phase; sigmap = _59_99.sigmap; default_result_effect = FStar_Absyn_Util.ml_comp; iface = _59_99.iface; admitted_iface = _59_99.admitted_iface}))

# 147 "FStar.Parser.DesugarEnv.fst"
let range_of_binding : binding  ->  FStar_Range.range = (fun _59_2 -> (match (_59_2) with
| (Binding_typ_var (id)) | (Binding_var (id)) -> begin
id.FStar_Ident.idRange
end
| (Binding_let (lid)) | (Binding_tycon (lid)) -> begin
(FStar_Ident.range_of_lid lid)
end))

# 153 "FStar.Parser.DesugarEnv.fst"
let try_lookup_typ_var : env  ->  FStar_Ident.ident  ->  FStar_Absyn_Syntax.typ Prims.option = (fun env id -> (
# 156 "FStar.Parser.DesugarEnv.fst"
let fopt = (FStar_List.tryFind (fun _59_113 -> (match (_59_113) with
| (_59_111, b) -> begin
(match (b) with
| (Binding_typ_var (id')) | (Binding_var (id')) -> begin
(id.FStar_Ident.idText = id'.FStar_Ident.idText)
end
| _59_118 -> begin
false
end)
end)) env.localbindings)
in (match (fopt) with
| Some (FStar_Util.Inl (bvd), Binding_typ_var (_59_123)) -> begin
(let _148_261 = (FStar_Absyn_Util.bvd_to_typ (FStar_Absyn_Util.set_bvd_range bvd id.FStar_Ident.idRange) FStar_Absyn_Syntax.kun)
in Some (_148_261))
end
| _59_128 -> begin
None
end)))

# 163 "FStar.Parser.DesugarEnv.fst"
let resolve_in_open_namespaces' = (fun env lid finder -> (
# 166 "FStar.Parser.DesugarEnv.fst"
let aux = (fun namespaces -> (match ((finder lid)) with
| Some (r) -> begin
Some (r)
end
| _59_138 -> begin
(
# 170 "FStar.Parser.DesugarEnv.fst"
let ids = (FStar_Ident.ids_of_lid lid)
in (FStar_Util.find_map namespaces (fun ns -> (
# 172 "FStar.Parser.DesugarEnv.fst"
let full_name = (FStar_Ident.lid_of_ids (FStar_List.append (FStar_Ident.ids_of_lid ns) ids))
in (finder full_name)))))
end))
in (let _148_272 = (let _148_271 = (current_module env)
in (_148_271)::env.open_namespaces)
in (aux _148_272))))

# 174 "FStar.Parser.DesugarEnv.fst"
let expand_module_abbrevs : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (match (lid.FStar_Ident.ns) with
| id::[] -> begin
(match ((FStar_All.pipe_right env.modul_abbrevs (FStar_List.tryFind (fun _59_149 -> (match (_59_149) with
| (id', _59_148) -> begin
(id.FStar_Ident.idText = id'.FStar_Ident.idText)
end))))) with
| None -> begin
lid
end
| Some (_59_152, lid') -> begin
(FStar_Ident.lid_of_ids (FStar_List.append (FStar_Ident.ids_of_lid lid') ((lid.FStar_Ident.ident)::[])))
end)
end
| _59_157 -> begin
lid
end))

# 184 "FStar.Parser.DesugarEnv.fst"
let resolve_in_open_namespaces = (fun env lid finder -> (let _148_288 = (expand_module_abbrevs env lid)
in (resolve_in_open_namespaces' env _148_288 finder)))

# 187 "FStar.Parser.DesugarEnv.fst"
let unmangleMap : (Prims.string * Prims.string) Prims.list = (("op_ColonColon", "Cons"))::(("not", "op_Negation"))::[]

# 190 "FStar.Parser.DesugarEnv.fst"
let unmangleOpName : FStar_Ident.ident  ->  FStar_Ident.lident Prims.option = (fun id -> (FStar_Util.find_map unmangleMap (fun _59_165 -> (match (_59_165) with
| (x, y) -> begin
if (id.FStar_Ident.idText = x) then begin
(let _148_292 = (FStar_Ident.lid_of_path (("Prims")::(y)::[]) id.FStar_Ident.idRange)
in Some (_148_292))
end else begin
None
end
end))))

# 195 "FStar.Parser.DesugarEnv.fst"
let try_lookup_id' : env  ->  FStar_Ident.ident  ->  (FStar_Ident.lident * FStar_Absyn_Syntax.exp) Prims.option = (fun env id -> (match ((unmangleOpName id)) with
| Some (l) -> begin
(let _148_298 = (let _148_297 = (FStar_Absyn_Syntax.mk_Exp_fvar ((FStar_Absyn_Util.fv l), None) None id.FStar_Ident.idRange)
in (l, _148_297))
in Some (_148_298))
end
| _59_171 -> begin
(
# 201 "FStar.Parser.DesugarEnv.fst"
let found = (FStar_Util.find_map env.localbindings (fun _59_3 -> (match (_59_3) with
| (FStar_Util.Inl (_59_174), Binding_typ_var (id')) when (id'.FStar_Ident.idText = id.FStar_Ident.idText) -> begin
Some (FStar_Util.Inl (()))
end
| (FStar_Util.Inr (bvd), Binding_var (id')) when (id'.FStar_Ident.idText = id.FStar_Ident.idText) -> begin
(let _148_303 = (let _148_302 = (let _148_301 = (FStar_Ident.lid_of_ids ((id')::[]))
in (let _148_300 = (FStar_Absyn_Util.bvd_to_exp (FStar_Absyn_Util.set_bvd_range bvd id.FStar_Ident.idRange) FStar_Absyn_Syntax.tun)
in (_148_301, _148_300)))
in FStar_Util.Inr (_148_302))
in Some (_148_303))
end
| _59_185 -> begin
None
end)))
in (match (found) with
| Some (FStar_Util.Inr (x)) -> begin
Some (x)
end
| _59_191 -> begin
None
end))
end))

# 207 "FStar.Parser.DesugarEnv.fst"
let try_lookup_id : env  ->  FStar_Ident.ident  ->  FStar_Absyn_Syntax.exp Prims.option = (fun env id -> (match ((try_lookup_id' env id)) with
| Some (_59_195, e) -> begin
Some (e)
end
| None -> begin
None
end))

# 212 "FStar.Parser.DesugarEnv.fst"
let fv_qual_of_se : FStar_Absyn_Syntax.sigelt  ->  FStar_Absyn_Syntax.fv_qual Prims.option = (fun _59_5 -> (match (_59_5) with
| FStar_Absyn_Syntax.Sig_datacon (_59_202, _59_204, (l, _59_207, _59_209), quals, _59_213, _59_215) -> begin
(
# 217 "FStar.Parser.DesugarEnv.fst"
let qopt = (FStar_Util.find_map quals (fun _59_4 -> (match (_59_4) with
| FStar_Absyn_Syntax.RecordConstructor (fs) -> begin
Some (FStar_Absyn_Syntax.Record_ctor ((l, fs)))
end
| _59_222 -> begin
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
| FStar_Absyn_Syntax.Sig_val_decl (_59_227, _59_229, quals, _59_232) -> begin
None
end
| _59_236 -> begin
None
end))

# 226 "FStar.Parser.DesugarEnv.fst"
let try_lookup_name : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  foundname Prims.option = (fun any_val exclude_interf env lid -> (
# 236 "FStar.Parser.DesugarEnv.fst"
let find_in_sig = (fun lid -> (match ((let _148_321 = (sigmap env)
in (FStar_Util.smap_try_find _148_321 lid.FStar_Ident.str))) with
| Some (_59_244, true) when exclude_interf -> begin
None
end
| None -> begin
None
end
| Some (se, _59_251) -> begin
(match (se) with
| (FStar_Absyn_Syntax.Sig_typ_abbrev (_)) | (FStar_Absyn_Syntax.Sig_tycon (_)) -> begin
(let _148_324 = (let _148_323 = (let _148_322 = (FStar_Absyn_Util.ftv lid FStar_Absyn_Syntax.kun)
in (OSig (se), _148_322))
in Typ_name (_148_323))
in Some (_148_324))
end
| FStar_Absyn_Syntax.Sig_kind_abbrev (_59_261) -> begin
Some (Knd_name ((OSig (se), lid)))
end
| FStar_Absyn_Syntax.Sig_new_effect (ne, _59_265) -> begin
(let _148_327 = (let _148_326 = (let _148_325 = (FStar_Ident.set_lid_range ne.FStar_Absyn_Syntax.mname (FStar_Ident.range_of_lid lid))
in (OSig (se), _148_325))
in Eff_name (_148_326))
in Some (_148_327))
end
| FStar_Absyn_Syntax.Sig_effect_abbrev (_59_269) -> begin
Some (Eff_name ((OSig (se), lid)))
end
| FStar_Absyn_Syntax.Sig_datacon (_59_272) -> begin
(let _148_331 = (let _148_330 = (let _148_329 = (let _148_328 = (fv_qual_of_se se)
in (FStar_Absyn_Util.fvar _148_328 lid (FStar_Ident.range_of_lid lid)))
in (OSig (se), _148_329))
in Exp_name (_148_330))
in Some (_148_331))
end
| FStar_Absyn_Syntax.Sig_let (_59_275) -> begin
(let _148_334 = (let _148_333 = (let _148_332 = (FStar_Absyn_Util.fvar None lid (FStar_Ident.range_of_lid lid))
in (OSig (se), _148_332))
in Exp_name (_148_333))
in Some (_148_334))
end
| FStar_Absyn_Syntax.Sig_val_decl (_59_278, _59_280, quals, _59_283) -> begin
if (any_val || (FStar_All.pipe_right quals (FStar_Util.for_some (fun _59_6 -> (match (_59_6) with
| FStar_Absyn_Syntax.Assumption -> begin
true
end
| _59_289 -> begin
false
end))))) then begin
(let _148_339 = (let _148_338 = (let _148_337 = (let _148_336 = (fv_qual_of_se se)
in (FStar_Absyn_Util.fvar _148_336 lid (FStar_Ident.range_of_lid lid)))
in (OSig (se), _148_337))
in Exp_name (_148_338))
in Some (_148_339))
end else begin
None
end
end
| _59_291 -> begin
None
end)
end))
in (
# 256 "FStar.Parser.DesugarEnv.fst"
let found_id = (match (lid.FStar_Ident.ns) with
| [] -> begin
(match ((try_lookup_id' env lid.FStar_Ident.ident)) with
| Some (lid, e) -> begin
Some (Exp_name ((OLet (lid), e)))
end
| None -> begin
(
# 261 "FStar.Parser.DesugarEnv.fst"
let recname = (qualify env lid.FStar_Ident.ident)
in (FStar_Util.find_map env.recbindings (fun _59_7 -> (match (_59_7) with
| Binding_let (l) when (FStar_Ident.lid_equals l recname) -> begin
(let _148_343 = (let _148_342 = (let _148_341 = (FStar_Absyn_Util.fvar None recname (FStar_Ident.range_of_lid recname))
in (ORec (l), _148_341))
in Exp_name (_148_342))
in Some (_148_343))
end
| Binding_tycon (l) when (FStar_Ident.lid_equals l recname) -> begin
(let _148_346 = (let _148_345 = (let _148_344 = (FStar_Absyn_Util.ftv recname FStar_Absyn_Syntax.kun)
in (ORec (l), _148_344))
in Typ_name (_148_345))
in Some (_148_346))
end
| _59_305 -> begin
None
end))))
end)
end
| _59_307 -> begin
None
end)
in (match (found_id) with
| Some (_59_310) -> begin
found_id
end
| _59_313 -> begin
(resolve_in_open_namespaces env lid find_in_sig)
end))))

# 272 "FStar.Parser.DesugarEnv.fst"
let try_lookup_typ_name' : Prims.bool  ->  env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.typ Prims.option = (fun exclude_interf env lid -> (match ((try_lookup_name true exclude_interf env lid)) with
| Some (Typ_name (_59_318, t)) -> begin
Some (t)
end
| Some (Eff_name (_59_324, l)) -> begin
(let _148_353 = (FStar_Absyn_Util.ftv l FStar_Absyn_Syntax.mk_Kind_unknown)
in Some (_148_353))
end
| _59_330 -> begin
None
end))

# 278 "FStar.Parser.DesugarEnv.fst"
let try_lookup_typ_name : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.typ Prims.option = (fun env l -> (try_lookup_typ_name' (not (env.iface)) env l))

# 279 "FStar.Parser.DesugarEnv.fst"
let try_lookup_effect_name' : Prims.bool  ->  env  ->  FStar_Ident.lident  ->  (occurrence * FStar_Ident.lident) Prims.option = (fun exclude_interf env lid -> (match ((try_lookup_name true exclude_interf env lid)) with
| Some (Eff_name (o, l)) -> begin
Some ((o, l))
end
| _59_342 -> begin
None
end))

# 284 "FStar.Parser.DesugarEnv.fst"
let try_lookup_effect_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env l -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some (o, l) -> begin
Some (l)
end
| _59_350 -> begin
None
end))

# 288 "FStar.Parser.DesugarEnv.fst"
let try_lookup_effect_defn : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.eff_decl Prims.option = (fun env l -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some (OSig (FStar_Absyn_Syntax.Sig_new_effect (ne, _59_355)), _59_360) -> begin
Some (ne)
end
| _59_364 -> begin
None
end))

# 292 "FStar.Parser.DesugarEnv.fst"
let is_effect_name : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((try_lookup_effect_name env lid)) with
| None -> begin
false
end
| Some (_59_369) -> begin
true
end))

# 296 "FStar.Parser.DesugarEnv.fst"
let try_resolve_typ_abbrev : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.typ Prims.option = (fun env lid -> (
# 299 "FStar.Parser.DesugarEnv.fst"
let find_in_sig = (fun lid -> (match ((let _148_382 = (sigmap env)
in (FStar_Util.smap_try_find _148_382 lid.FStar_Ident.str))) with
| Some (FStar_Absyn_Syntax.Sig_typ_abbrev (lid, tps, k, def, _59_380, _59_382), _59_386) -> begin
(
# 302 "FStar.Parser.DesugarEnv.fst"
let t = (let _148_385 = (let _148_384 = (let _148_383 = (FStar_Absyn_Util.close_with_lam tps def)
in (_148_383, lid))
in FStar_Absyn_Syntax.Meta_named (_148_384))
in (FStar_Absyn_Syntax.mk_Typ_meta _148_385))
in Some (t))
end
| _59_391 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))

# 305 "FStar.Parser.DesugarEnv.fst"
let lookup_letbinding_quals : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.qualifier Prims.list = (fun env lid -> (
# 308 "FStar.Parser.DesugarEnv.fst"
let find_in_sig = (fun lid -> (match ((let _148_392 = (sigmap env)
in (FStar_Util.smap_try_find _148_392 lid.FStar_Ident.str))) with
| Some (FStar_Absyn_Syntax.Sig_val_decl (lid, _59_398, quals, _59_401), _59_405) -> begin
Some (quals)
end
| _59_409 -> begin
None
end))
in (match ((resolve_in_open_namespaces env lid find_in_sig)) with
| Some (quals) -> begin
quals
end
| _59_413 -> begin
[]
end)))

# 314 "FStar.Parser.DesugarEnv.fst"
let try_lookup_module : env  ->  Prims.string Prims.list  ->  FStar_Absyn_Syntax.modul Prims.option = (fun env path -> (match ((FStar_List.tryFind (fun _59_418 -> (match (_59_418) with
| (mlid, modul) -> begin
((FStar_Ident.path_of_lid mlid) = path)
end)) env.modules)) with
| Some (_59_420, modul) -> begin
Some (modul)
end
| None -> begin
None
end))

# 319 "FStar.Parser.DesugarEnv.fst"
let try_lookup_let : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.exp Prims.option = (fun env lid -> (
# 322 "FStar.Parser.DesugarEnv.fst"
let find_in_sig = (fun lid -> (match ((let _148_404 = (sigmap env)
in (FStar_Util.smap_try_find _148_404 lid.FStar_Ident.str))) with
| Some (FStar_Absyn_Syntax.Sig_let (_59_430), _59_433) -> begin
(let _148_405 = (FStar_Absyn_Util.fvar None lid (FStar_Ident.range_of_lid lid))
in Some (_148_405))
end
| _59_437 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))

# 326 "FStar.Parser.DesugarEnv.fst"
let try_lookup_lid' : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.exp Prims.option = (fun any_val exclude_interf env lid -> (match ((try_lookup_name any_val exclude_interf env lid)) with
| Some (Exp_name (_59_443, e)) -> begin
Some (e)
end
| _59_449 -> begin
None
end))

# 331 "FStar.Parser.DesugarEnv.fst"
let try_lookup_lid : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.exp Prims.option = (fun env l -> (try_lookup_lid' env.iface false env l))

# 332 "FStar.Parser.DesugarEnv.fst"
let try_lookup_datacon : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.typ FStar_Absyn_Syntax.var Prims.option = (fun env lid -> (
# 335 "FStar.Parser.DesugarEnv.fst"
let find_in_sig = (fun lid -> (match ((let _148_424 = (sigmap env)
in (FStar_Util.smap_try_find _148_424 lid.FStar_Ident.str))) with
| Some (FStar_Absyn_Syntax.Sig_val_decl (_59_457, _59_459, quals, _59_462), _59_466) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _59_8 -> (match (_59_8) with
| FStar_Absyn_Syntax.Assumption -> begin
true
end
| _59_472 -> begin
false
end)))) then begin
Some ((FStar_Absyn_Util.fv lid))
end else begin
None
end
end
| Some (FStar_Absyn_Syntax.Sig_datacon (_59_474), _59_477) -> begin
Some ((FStar_Absyn_Util.fv lid))
end
| _59_481 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))

# 343 "FStar.Parser.DesugarEnv.fst"
let find_all_datacons : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.list Prims.option = (fun env lid -> (
# 346 "FStar.Parser.DesugarEnv.fst"
let find_in_sig = (fun lid -> (match ((let _148_432 = (sigmap env)
in (FStar_Util.smap_try_find _148_432 lid.FStar_Ident.str))) with
| Some (FStar_Absyn_Syntax.Sig_tycon (_59_487, _59_489, _59_491, _59_493, datas, _59_496, _59_498), _59_502) -> begin
Some (datas)
end
| _59_506 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))

# 350 "FStar.Parser.DesugarEnv.fst"
let record_cache_aux : ((Prims.unit  ->  Prims.unit) * (Prims.unit  ->  Prims.unit) * (Prims.unit  ->  record_or_dc Prims.list) * (record_or_dc  ->  Prims.unit)) = (
# 354 "FStar.Parser.DesugarEnv.fst"
let record_cache = (FStar_Util.mk_ref (([])::[]))
in (
# 355 "FStar.Parser.DesugarEnv.fst"
let push = (fun _59_509 -> (match (()) with
| () -> begin
(let _148_446 = (let _148_445 = (let _148_443 = (FStar_ST.read record_cache)
in (FStar_List.hd _148_443))
in (let _148_444 = (FStar_ST.read record_cache)
in (_148_445)::_148_444))
in (FStar_ST.op_Colon_Equals record_cache _148_446))
end))
in (
# 357 "FStar.Parser.DesugarEnv.fst"
let pop = (fun _59_511 -> (match (()) with
| () -> begin
(let _148_450 = (let _148_449 = (FStar_ST.read record_cache)
in (FStar_List.tl _148_449))
in (FStar_ST.op_Colon_Equals record_cache _148_450))
end))
in (
# 359 "FStar.Parser.DesugarEnv.fst"
let peek = (fun _59_513 -> (match (()) with
| () -> begin
(let _148_453 = (FStar_ST.read record_cache)
in (FStar_List.hd _148_453))
end))
in (
# 360 "FStar.Parser.DesugarEnv.fst"
let insert = (fun r -> (let _148_460 = (let _148_459 = (let _148_456 = (peek ())
in (r)::_148_456)
in (let _148_458 = (let _148_457 = (FStar_ST.read record_cache)
in (FStar_List.tl _148_457))
in (_148_459)::_148_458))
in (FStar_ST.op_Colon_Equals record_cache _148_460)))
in (push, pop, peek, insert))))))

# 361 "FStar.Parser.DesugarEnv.fst"
let push_record_cache : Prims.unit  ->  Prims.unit = (
# 364 "FStar.Parser.DesugarEnv.fst"
let _59_523 = record_cache_aux
in (match (_59_523) with
| (push, _59_518, _59_520, _59_522) -> begin
push
end))

# 365 "FStar.Parser.DesugarEnv.fst"
let pop_record_cache : Prims.unit  ->  Prims.unit = (
# 368 "FStar.Parser.DesugarEnv.fst"
let _59_531 = record_cache_aux
in (match (_59_531) with
| (_59_525, pop, _59_528, _59_530) -> begin
pop
end))

# 369 "FStar.Parser.DesugarEnv.fst"
let peek_record_cache : Prims.unit  ->  record_or_dc Prims.list = (
# 372 "FStar.Parser.DesugarEnv.fst"
let _59_539 = record_cache_aux
in (match (_59_539) with
| (_59_533, _59_535, peek, _59_538) -> begin
peek
end))

# 373 "FStar.Parser.DesugarEnv.fst"
let insert_record_cache : record_or_dc  ->  Prims.unit = (
# 376 "FStar.Parser.DesugarEnv.fst"
let _59_547 = record_cache_aux
in (match (_59_547) with
| (_59_541, _59_543, _59_545, insert) -> begin
insert
end))

# 377 "FStar.Parser.DesugarEnv.fst"
let extract_record : env  ->  FStar_Absyn_Syntax.sigelt  ->  Prims.unit = (fun e _59_12 -> (match (_59_12) with
| FStar_Absyn_Syntax.Sig_bundle (sigs, _59_552, _59_554, _59_556) -> begin
(
# 381 "FStar.Parser.DesugarEnv.fst"
let is_rec = (FStar_Util.for_some (fun _59_9 -> (match (_59_9) with
| (FStar_Absyn_Syntax.RecordType (_)) | (FStar_Absyn_Syntax.RecordConstructor (_)) -> begin
true
end
| _59_567 -> begin
false
end)))
in (
# 386 "FStar.Parser.DesugarEnv.fst"
let find_dc = (fun dc -> (FStar_All.pipe_right sigs (FStar_Util.find_opt (fun _59_10 -> (match (_59_10) with
| FStar_Absyn_Syntax.Sig_datacon (lid, _59_574, _59_576, _59_578, _59_580, _59_582) -> begin
(FStar_Ident.lid_equals dc lid)
end
| _59_586 -> begin
false
end)))))
in (FStar_All.pipe_right sigs (FStar_List.iter (fun _59_11 -> (match (_59_11) with
| FStar_Absyn_Syntax.Sig_tycon (typename, parms, _59_591, _59_593, dc::[], tags, _59_598) -> begin
(match ((let _148_531 = (find_dc dc)
in (FStar_All.pipe_left FStar_Util.must _148_531))) with
| FStar_Absyn_Syntax.Sig_datacon (constrname, t, _59_604, _59_606, _59_608, _59_610) -> begin
(
# 395 "FStar.Parser.DesugarEnv.fst"
let formals = (match ((FStar_Absyn_Util.function_formals t)) with
| Some (x, _59_615) -> begin
x
end
| _59_619 -> begin
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
| Some (FStar_Absyn_Syntax.Implicit (_59_628)) -> begin
true
end
| _59_632 -> begin
false
end))) then begin
[]
end else begin
(let _148_535 = (let _148_534 = (let _148_533 = if is_rec then begin
(FStar_Absyn_Util.unmangle_field_name x.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ppname)
end else begin
x.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ppname
end
in (qual constrname _148_533))
in (_148_534, x.FStar_Absyn_Syntax.sort))
in (_148_535)::[])
end
end
| _59_634 -> begin
[]
end))))
in (
# 406 "FStar.Parser.DesugarEnv.fst"
let record = {typename = typename; constrname = constrname; parms = parms; fields = fields; is_record = is_rec}
in (insert_record_cache record)))))
end
| _59_638 -> begin
()
end)
end
| _59_640 -> begin
()
end))))))
end
| _59_642 -> begin
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
| c'::[] -> begin
if (c'.FStar_Ident.idText = c.FStar_Ident.idText) then begin
(c)::[]
end else begin
(c')::(c)::[]
end
end
| hd::tl -> begin
(let _148_546 = (aux tl)
in (hd)::_148_546)
end))
in (aux ns)))
in (
# 425 "FStar.Parser.DesugarEnv.fst"
let find_in_cache = (fun fieldname -> (
# 427 "FStar.Parser.DesugarEnv.fst"
let _59_660 = (fieldname.FStar_Ident.ns, fieldname.FStar_Ident.ident)
in (match (_59_660) with
| (ns, fieldname) -> begin
(let _148_551 = (peek_record_cache ())
in (FStar_Util.find_map _148_551 (fun record -> (
# 429 "FStar.Parser.DesugarEnv.fst"
let constrname = record.constrname.FStar_Ident.ident
in (
# 430 "FStar.Parser.DesugarEnv.fst"
let ns = (maybe_add_constrname ns constrname)
in (
# 431 "FStar.Parser.DesugarEnv.fst"
let fname = (FStar_Ident.lid_of_ids (FStar_List.append ns ((fieldname)::[])))
in (FStar_Util.find_map record.fields (fun _59_668 -> (match (_59_668) with
| (f, _59_667) -> begin
if (FStar_Ident.lid_equals fname f) then begin
Some ((record, fname))
end else begin
None
end
end)))))))))
end)))
in (resolve_in_open_namespaces env fieldname find_in_cache))))

# 436 "FStar.Parser.DesugarEnv.fst"
let try_lookup_record_by_field_name : env  ->  FStar_Ident.lident  ->  (record_or_dc * FStar_Ident.lident) Prims.option = (fun env fieldname -> (match ((try_lookup_record_or_dc_by_field_name env fieldname)) with
| Some (r, f) when r.is_record -> begin
Some ((r, f))
end
| _59_676 -> begin
None
end))

# 441 "FStar.Parser.DesugarEnv.fst"
let try_lookup_projector_by_field_name : env  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * Prims.bool) Prims.option = (fun env fieldname -> (match ((try_lookup_record_or_dc_by_field_name env fieldname)) with
| Some (r, f) -> begin
Some ((f, r.is_record))
end
| _59_684 -> begin
None
end))

# 446 "FStar.Parser.DesugarEnv.fst"
let qualify_field_to_record : env  ->  record_or_dc  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env recd f -> (
# 449 "FStar.Parser.DesugarEnv.fst"
let qualify = (fun fieldname -> (
# 450 "FStar.Parser.DesugarEnv.fst"
let _59_692 = (fieldname.FStar_Ident.ns, fieldname.FStar_Ident.ident)
in (match (_59_692) with
| (ns, fieldname) -> begin
(
# 451 "FStar.Parser.DesugarEnv.fst"
let constrname = recd.constrname.FStar_Ident.ident
in (
# 452 "FStar.Parser.DesugarEnv.fst"
let fname = (FStar_Ident.lid_of_ids (FStar_List.append (FStar_List.append ns ((constrname)::[])) ((fieldname)::[])))
in (FStar_Util.find_map recd.fields (fun _59_698 -> (match (_59_698) with
| (f, _59_697) -> begin
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
| Some (Knd_name (_59_702, l)) -> begin
Some (l)
end
| _59_708 -> begin
None
end))

# 462 "FStar.Parser.DesugarEnv.fst"
let is_kind_abbrev : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (match ((find_kind_abbrev env l)) with
| None -> begin
false
end
| Some (_59_713) -> begin
true
end))

# 467 "FStar.Parser.DesugarEnv.fst"
let unique_name : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  Prims.bool = (fun any_val exclude_if env lid -> (match ((try_lookup_lid' any_val exclude_if env lid)) with
| None -> begin
(match ((find_kind_abbrev env lid)) with
| None -> begin
true
end
| Some (_59_722) -> begin
false
end)
end
| Some (_59_725) -> begin
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
let _59_736 = env
in {curmodule = _59_736.curmodule; modules = _59_736.modules; open_namespaces = []; modul_abbrevs = _59_736.modul_abbrevs; sigaccum = _59_736.sigaccum; localbindings = _59_736.localbindings; recbindings = _59_736.recbindings; phase = _59_736.phase; sigmap = _59_736.sigmap; default_result_effect = _59_736.default_result_effect; iface = _59_736.iface; admitted_iface = _59_736.admitted_iface})
in ((unique_name any_val exclude_if this_env lid) && (unique_typ_name this_env lid))))

# 485 "FStar.Parser.DesugarEnv.fst"
let gen_bvd = (fun _59_13 -> (match (_59_13) with
| Binding_typ_var (id) -> begin
(let _148_600 = (let _148_599 = (let _148_598 = (FStar_Absyn_Util.genident (Some (id.FStar_Ident.idRange)))
in (id, _148_598))
in (FStar_Absyn_Util.mkbvd _148_599))
in FStar_Util.Inl (_148_600))
end
| Binding_var (id) -> begin
(let _148_603 = (let _148_602 = (let _148_601 = (FStar_Absyn_Util.genident (Some (id.FStar_Ident.idRange)))
in (id, _148_601))
in (FStar_Absyn_Util.mkbvd _148_602))
in FStar_Util.Inr (_148_603))
end
| _59_745 -> begin
(FStar_All.failwith "Tried to generate a bound variable for a type constructor")
end))

# 490 "FStar.Parser.DesugarEnv.fst"
let push_bvvdef : env  ->  FStar_Absyn_Syntax.bvvdef  ->  env = (fun env x -> (
# 493 "FStar.Parser.DesugarEnv.fst"
let b = Binding_var (x.FStar_Absyn_Syntax.ppname)
in (
# 494 "FStar.Parser.DesugarEnv.fst"
let _59_749 = env
in {curmodule = _59_749.curmodule; modules = _59_749.modules; open_namespaces = _59_749.open_namespaces; modul_abbrevs = _59_749.modul_abbrevs; sigaccum = _59_749.sigaccum; localbindings = ((FStar_Util.Inr (x), b))::env.localbindings; recbindings = _59_749.recbindings; phase = _59_749.phase; sigmap = _59_749.sigmap; default_result_effect = _59_749.default_result_effect; iface = _59_749.iface; admitted_iface = _59_749.admitted_iface})))

# 494 "FStar.Parser.DesugarEnv.fst"
let push_btvdef : env  ->  FStar_Absyn_Syntax.btvdef  ->  env = (fun env x -> (
# 497 "FStar.Parser.DesugarEnv.fst"
let b = Binding_typ_var (x.FStar_Absyn_Syntax.ppname)
in (
# 498 "FStar.Parser.DesugarEnv.fst"
let _59_754 = env
in {curmodule = _59_754.curmodule; modules = _59_754.modules; open_namespaces = _59_754.open_namespaces; modul_abbrevs = _59_754.modul_abbrevs; sigaccum = _59_754.sigaccum; localbindings = ((FStar_Util.Inl (x), b))::env.localbindings; recbindings = _59_754.recbindings; phase = _59_754.phase; sigmap = _59_754.sigmap; default_result_effect = _59_754.default_result_effect; iface = _59_754.iface; admitted_iface = _59_754.admitted_iface})))

# 498 "FStar.Parser.DesugarEnv.fst"
let push_local_binding : env  ->  binding  ->  (env * (FStar_Absyn_Syntax.btvdef, FStar_Absyn_Syntax.bvvdef) FStar_Util.either) = (fun env b -> (
# 501 "FStar.Parser.DesugarEnv.fst"
let bvd = (gen_bvd b)
in ((
# 502 "FStar.Parser.DesugarEnv.fst"
let _59_759 = env
in {curmodule = _59_759.curmodule; modules = _59_759.modules; open_namespaces = _59_759.open_namespaces; modul_abbrevs = _59_759.modul_abbrevs; sigaccum = _59_759.sigaccum; localbindings = ((bvd, b))::env.localbindings; recbindings = _59_759.recbindings; phase = _59_759.phase; sigmap = _59_759.sigmap; default_result_effect = _59_759.default_result_effect; iface = _59_759.iface; admitted_iface = _59_759.admitted_iface}), bvd)))

# 502 "FStar.Parser.DesugarEnv.fst"
let push_local_tbinding : env  ->  FStar_Ident.ident  ->  (env * FStar_Absyn_Syntax.btvdef) = (fun env a -> (match ((push_local_binding env (Binding_typ_var (a)))) with
| (env, FStar_Util.Inl (x)) -> begin
(env, x)
end
| _59_768 -> begin
(FStar_All.failwith "impossible")
end))

# 507 "FStar.Parser.DesugarEnv.fst"
let push_local_vbinding : env  ->  FStar_Ident.ident  ->  (env * FStar_Absyn_Syntax.bvvdef) = (fun env b -> (match ((push_local_binding env (Binding_var (b)))) with
| (env, FStar_Util.Inr (x)) -> begin
(env, x)
end
| _59_776 -> begin
(FStar_All.failwith "impossible")
end))

# 513 "FStar.Parser.DesugarEnv.fst"
let push_rec_binding : env  ->  binding  ->  env = (fun env b -> (match (b) with
| (Binding_let (lid)) | (Binding_tycon (lid)) -> begin
if (unique false true env lid) then begin
(
# 519 "FStar.Parser.DesugarEnv.fst"
let _59_782 = env
in {curmodule = _59_782.curmodule; modules = _59_782.modules; open_namespaces = _59_782.open_namespaces; modul_abbrevs = _59_782.modul_abbrevs; sigaccum = _59_782.sigaccum; localbindings = _59_782.localbindings; recbindings = (b)::env.recbindings; phase = _59_782.phase; sigmap = _59_782.sigmap; default_result_effect = _59_782.default_result_effect; iface = _59_782.iface; admitted_iface = _59_782.admitted_iface})
end else begin
(Prims.raise (FStar_Absyn_Syntax.Error (((Prims.strcat "Duplicate top-level names " lid.FStar_Ident.str), (FStar_Ident.range_of_lid lid)))))
end
end
| _59_785 -> begin
(FStar_All.failwith "Unexpected rec_binding")
end))

# 521 "FStar.Parser.DesugarEnv.fst"
let push_sigelt : env  ->  FStar_Absyn_Syntax.sigelt  ->  env = (fun env s -> (
# 524 "FStar.Parser.DesugarEnv.fst"
let err = (fun l -> (
# 525 "FStar.Parser.DesugarEnv.fst"
let sopt = (let _148_634 = (sigmap env)
in (FStar_Util.smap_try_find _148_634 l.FStar_Ident.str))
in (
# 526 "FStar.Parser.DesugarEnv.fst"
let r = (match (sopt) with
| Some (se, _59_793) -> begin
(match ((let _148_635 = (FStar_Absyn_Util.lids_of_sigelt se)
in (FStar_Util.find_opt (FStar_Ident.lid_equals l) _148_635))) with
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
in (let _148_638 = (let _148_637 = (let _148_636 = (FStar_Util.format2 "Duplicate top-level names [%s]; previously declared at %s" (FStar_Ident.text_of_lid l) r)
in (_148_636, (FStar_Ident.range_of_lid l)))
in FStar_Absyn_Syntax.Error (_148_637))
in (Prims.raise _148_638)))))
in (
# 534 "FStar.Parser.DesugarEnv.fst"
let env = (
# 535 "FStar.Parser.DesugarEnv.fst"
let _59_811 = (match (s) with
| FStar_Absyn_Syntax.Sig_let (_59_802) -> begin
(false, true)
end
| FStar_Absyn_Syntax.Sig_bundle (_59_805) -> begin
(true, true)
end
| _59_808 -> begin
(false, false)
end)
in (match (_59_811) with
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
let _59_815 = (extract_record env s)
in (
# 541 "FStar.Parser.DesugarEnv.fst"
let _59_817 = env
in {curmodule = _59_817.curmodule; modules = _59_817.modules; open_namespaces = _59_817.open_namespaces; modul_abbrevs = _59_817.modul_abbrevs; sigaccum = (s)::env.sigaccum; localbindings = _59_817.localbindings; recbindings = _59_817.recbindings; phase = _59_817.phase; sigmap = _59_817.sigmap; default_result_effect = _59_817.default_result_effect; iface = _59_817.iface; admitted_iface = _59_817.admitted_iface}))
end
| Some (l) -> begin
(err l)
end))
end))
in (
# 544 "FStar.Parser.DesugarEnv.fst"
let _59_836 = (match (s) with
| FStar_Absyn_Syntax.Sig_bundle (ses, _59_824, _59_826, _59_828) -> begin
(let _148_642 = (FStar_List.map (fun se -> (let _148_641 = (FStar_Absyn_Util.lids_of_sigelt se)
in (_148_641, se))) ses)
in (env, _148_642))
end
| _59_833 -> begin
(let _148_645 = (let _148_644 = (let _148_643 = (FStar_Absyn_Util.lids_of_sigelt s)
in (_148_643, s))
in (_148_644)::[])
in (env, _148_645))
end)
in (match (_59_836) with
| (env, lss) -> begin
(
# 547 "FStar.Parser.DesugarEnv.fst"
let _59_841 = (FStar_All.pipe_right lss (FStar_List.iter (fun _59_839 -> (match (_59_839) with
| (lids, se) -> begin
(FStar_All.pipe_right lids (FStar_List.iter (fun lid -> (let _148_648 = (sigmap env)
in (FStar_Util.smap_add _148_648 lid.FStar_Ident.str (se, (env.iface && (not (env.admitted_iface)))))))))
end))))
in env)
end)))))

# 550 "FStar.Parser.DesugarEnv.fst"
let push_namespace : env  ->  FStar_Ident.lident  ->  env = (fun env lid -> (
# 553 "FStar.Parser.DesugarEnv.fst"
let _59_845 = env
in {curmodule = _59_845.curmodule; modules = _59_845.modules; open_namespaces = (lid)::env.open_namespaces; modul_abbrevs = _59_845.modul_abbrevs; sigaccum = _59_845.sigaccum; localbindings = _59_845.localbindings; recbindings = _59_845.recbindings; phase = _59_845.phase; sigmap = _59_845.sigmap; default_result_effect = _59_845.default_result_effect; iface = _59_845.iface; admitted_iface = _59_845.admitted_iface}))

# 553 "FStar.Parser.DesugarEnv.fst"
let push_module_abbrev : env  ->  FStar_Ident.ident  ->  FStar_Ident.lident  ->  env = (fun env x l -> if (FStar_All.pipe_right env.modul_abbrevs (FStar_Util.for_some (fun _59_853 -> (match (_59_853) with
| (y, _59_852) -> begin
(x.FStar_Ident.idText = y.FStar_Ident.idText)
end)))) then begin
(let _148_662 = (let _148_661 = (let _148_660 = (FStar_Util.format1 "Module %s is already defined" x.FStar_Ident.idText)
in (_148_660, x.FStar_Ident.idRange))
in FStar_Absyn_Syntax.Error (_148_661))
in (Prims.raise _148_662))
end else begin
(
# 558 "FStar.Parser.DesugarEnv.fst"
let _59_854 = env
in {curmodule = _59_854.curmodule; modules = _59_854.modules; open_namespaces = _59_854.open_namespaces; modul_abbrevs = ((x, l))::env.modul_abbrevs; sigaccum = _59_854.sigaccum; localbindings = _59_854.localbindings; recbindings = _59_854.recbindings; phase = _59_854.phase; sigmap = _59_854.sigmap; default_result_effect = _59_854.default_result_effect; iface = _59_854.iface; admitted_iface = _59_854.admitted_iface})
end)

# 558 "FStar.Parser.DesugarEnv.fst"
let is_type_lid : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (
# 561 "FStar.Parser.DesugarEnv.fst"
let aux = (fun _59_859 -> (match (()) with
| () -> begin
(match ((try_lookup_typ_name' false env lid)) with
| Some (_59_861) -> begin
true
end
| _59_864 -> begin
false
end)
end))
in if (lid.FStar_Ident.ns = []) then begin
(match ((try_lookup_id env lid.FStar_Ident.ident)) with
| Some (_59_866) -> begin
false
end
| _59_869 -> begin
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
let _59_880 = (let _148_676 = (let _148_675 = (FStar_Range.string_of_range (FStar_Ident.range_of_lid l))
in (let _148_674 = (FStar_Absyn_Print.sli l)
in (FStar_Util.format2 "%s: Warning: Admitting %s without a definition\n" _148_675 _148_674)))
in (FStar_Util.print_string _148_676))
in (let _148_677 = (sigmap env)
in (FStar_Util.smap_add _148_677 l.FStar_Ident.str (FStar_Absyn_Syntax.Sig_val_decl ((l, t, (FStar_Absyn_Syntax.Assumption)::quals, r)), false))))
end
| Some (_59_883) -> begin
()
end)
end
| _59_886 -> begin
()
end)))))

# 580 "FStar.Parser.DesugarEnv.fst"
let finish : env  ->  FStar_Absyn_Syntax.modul  ->  env = (fun env modul -> (
# 583 "FStar.Parser.DesugarEnv.fst"
let _59_924 = (FStar_All.pipe_right modul.FStar_Absyn_Syntax.declarations (FStar_List.iter (fun _59_15 -> (match (_59_15) with
| FStar_Absyn_Syntax.Sig_bundle (ses, quals, _59_893, _59_895) -> begin
if (FStar_List.contains FStar_Absyn_Syntax.Private quals) then begin
(FStar_All.pipe_right ses (FStar_List.iter (fun _59_14 -> (match (_59_14) with
| FStar_Absyn_Syntax.Sig_datacon (lid, _59_901, _59_903, _59_905, _59_907, _59_909) -> begin
(let _148_684 = (sigmap env)
in (FStar_Util.smap_remove _148_684 lid.FStar_Ident.str))
end
| _59_913 -> begin
()
end))))
end else begin
()
end
end
| FStar_Absyn_Syntax.Sig_val_decl (lid, _59_916, quals, _59_919) -> begin
if (FStar_List.contains FStar_Absyn_Syntax.Private quals) then begin
(let _148_685 = (sigmap env)
in (FStar_Util.smap_remove _148_685 lid.FStar_Ident.str))
end else begin
()
end
end
| _59_923 -> begin
()
end))))
in (
# 593 "FStar.Parser.DesugarEnv.fst"
let _59_926 = env
in {curmodule = None; modules = ((modul.FStar_Absyn_Syntax.name, modul))::env.modules; open_namespaces = []; modul_abbrevs = []; sigaccum = []; localbindings = []; recbindings = []; phase = FStar_Parser_AST.Un; sigmap = _59_926.sigmap; default_result_effect = _59_926.default_result_effect; iface = _59_926.iface; admitted_iface = _59_926.admitted_iface})))

# 601 "FStar.Parser.DesugarEnv.fst"
let push : env  ->  env = (fun env -> (
# 604 "FStar.Parser.DesugarEnv.fst"
let _59_929 = (push_record_cache ())
in (
# 605 "FStar.Parser.DesugarEnv.fst"
let _59_931 = env
in (let _148_690 = (let _148_689 = (let _148_688 = (sigmap env)
in (FStar_Util.smap_copy _148_688))
in (_148_689)::env.sigmap)
in {curmodule = _59_931.curmodule; modules = _59_931.modules; open_namespaces = _59_931.open_namespaces; modul_abbrevs = _59_931.modul_abbrevs; sigaccum = _59_931.sigaccum; localbindings = _59_931.localbindings; recbindings = _59_931.recbindings; phase = _59_931.phase; sigmap = _148_690; default_result_effect = _59_931.default_result_effect; iface = _59_931.iface; admitted_iface = _59_931.admitted_iface}))))

# 606 "FStar.Parser.DesugarEnv.fst"
let mark : env  ->  env = (fun env -> (push env))

# 608 "FStar.Parser.DesugarEnv.fst"
let reset_mark : env  ->  env = (fun env -> (
# 609 "FStar.Parser.DesugarEnv.fst"
let _59_935 = env
in (let _148_695 = (FStar_List.tl env.sigmap)
in {curmodule = _59_935.curmodule; modules = _59_935.modules; open_namespaces = _59_935.open_namespaces; modul_abbrevs = _59_935.modul_abbrevs; sigaccum = _59_935.sigaccum; localbindings = _59_935.localbindings; recbindings = _59_935.recbindings; phase = _59_935.phase; sigmap = _148_695; default_result_effect = _59_935.default_result_effect; iface = _59_935.iface; admitted_iface = _59_935.admitted_iface})))

# 609 "FStar.Parser.DesugarEnv.fst"
let commit_mark : env  ->  env = (fun env -> (match (env.sigmap) with
| hd::_59_940::tl -> begin
(
# 611 "FStar.Parser.DesugarEnv.fst"
let _59_944 = env
in {curmodule = _59_944.curmodule; modules = _59_944.modules; open_namespaces = _59_944.open_namespaces; modul_abbrevs = _59_944.modul_abbrevs; sigaccum = _59_944.sigaccum; localbindings = _59_944.localbindings; recbindings = _59_944.recbindings; phase = _59_944.phase; sigmap = (hd)::tl; default_result_effect = _59_944.default_result_effect; iface = _59_944.iface; admitted_iface = _59_944.admitted_iface})
end
| _59_947 -> begin
(FStar_All.failwith "Impossible")
end))

# 612 "FStar.Parser.DesugarEnv.fst"
let pop : env  ->  env = (fun env -> (match (env.sigmap) with
| _59_951::maps -> begin
(
# 615 "FStar.Parser.DesugarEnv.fst"
let _59_953 = (pop_record_cache ())
in (
# 616 "FStar.Parser.DesugarEnv.fst"
let _59_955 = env
in {curmodule = _59_955.curmodule; modules = _59_955.modules; open_namespaces = _59_955.open_namespaces; modul_abbrevs = _59_955.modul_abbrevs; sigaccum = _59_955.sigaccum; localbindings = _59_955.localbindings; recbindings = _59_955.recbindings; phase = _59_955.phase; sigmap = maps; default_result_effect = _59_955.default_result_effect; iface = _59_955.iface; admitted_iface = _59_955.admitted_iface}))
end
| _59_958 -> begin
(FStar_All.failwith "No more modules to pop")
end))

# 618 "FStar.Parser.DesugarEnv.fst"
let export_interface : FStar_Ident.lident  ->  env  ->  env = (fun m env -> (
# 622 "FStar.Parser.DesugarEnv.fst"
let sigelt_in_m = (fun se -> (match ((FStar_Absyn_Util.lids_of_sigelt se)) with
| l::_59_964 -> begin
(l.FStar_Ident.nsstr = m.FStar_Ident.str)
end
| _59_968 -> begin
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
let _59_991 = (FStar_All.pipe_right keys (FStar_List.iter (fun k -> (match ((FStar_Util.smap_try_find sm' k)) with
| Some (se, true) when (sigelt_in_m se) -> begin
(
# 633 "FStar.Parser.DesugarEnv.fst"
let _59_978 = (FStar_Util.smap_remove sm' k)
in (
# 635 "FStar.Parser.DesugarEnv.fst"
let se = (match (se) with
| FStar_Absyn_Syntax.Sig_val_decl (l, t, q, r) -> begin
FStar_Absyn_Syntax.Sig_val_decl ((l, t, (FStar_Absyn_Syntax.Assumption)::q, r))
end
| _59_987 -> begin
se
end)
in (FStar_Util.smap_add sm' k (se, false))))
end
| _59_990 -> begin
()
end))))
in env)))))))

# 640 "FStar.Parser.DesugarEnv.fst"
let finish_module_or_interface : env  ->  FStar_Absyn_Syntax.modul  ->  env = (fun env modul -> (
# 643 "FStar.Parser.DesugarEnv.fst"
let _59_995 = if (not (modul.FStar_Absyn_Syntax.is_interface)) then begin
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
# 654 "FStar.Parser.DesugarEnv.fst"
let _59_1004 = env
in {curmodule = Some (mname); modules = _59_1004.modules; open_namespaces = open_ns; modul_abbrevs = _59_1004.modul_abbrevs; sigaccum = _59_1004.sigaccum; localbindings = _59_1004.localbindings; recbindings = _59_1004.recbindings; phase = _59_1004.phase; sigmap = env.sigmap; default_result_effect = _59_1004.default_result_effect; iface = intf; admitted_iface = admitted})))
in (match ((FStar_All.pipe_right env.modules (FStar_Util.find_opt (fun _59_1009 -> (match (_59_1009) with
| (l, _59_1008) -> begin
(FStar_Ident.lid_equals l mname)
end))))) with
| None -> begin
((prep env), false)
end
| Some (_59_1012, m) -> begin
(let _148_724 = (let _148_723 = (let _148_722 = (FStar_Util.format1 "Duplicate module or interface name: %s" mname.FStar_Ident.str)
in (_148_722, (FStar_Ident.range_of_lid mname)))
in FStar_Absyn_Syntax.Error (_148_723))
in (Prims.raise _148_724))
end)))

# 658 "FStar.Parser.DesugarEnv.fst"
let enter_monad_scope : env  ->  FStar_Ident.ident  ->  env = (fun env mname -> (
# 661 "FStar.Parser.DesugarEnv.fst"
let curmod = (current_module env)
in (
# 662 "FStar.Parser.DesugarEnv.fst"
let mscope = (FStar_Ident.lid_of_ids (FStar_List.append curmod.FStar_Ident.ns ((curmod.FStar_Ident.ident)::(mname)::[])))
in (
# 663 "FStar.Parser.DesugarEnv.fst"
let _59_1020 = env
in {curmodule = Some (mscope); modules = _59_1020.modules; open_namespaces = (curmod)::env.open_namespaces; modul_abbrevs = _59_1020.modul_abbrevs; sigaccum = _59_1020.sigaccum; localbindings = _59_1020.localbindings; recbindings = _59_1020.recbindings; phase = _59_1020.phase; sigmap = _59_1020.sigmap; default_result_effect = _59_1020.default_result_effect; iface = _59_1020.iface; admitted_iface = _59_1020.admitted_iface}))))

# 665 "FStar.Parser.DesugarEnv.fst"
let exit_monad_scope : env  ->  env  ->  env = (fun env0 env -> (
# 668 "FStar.Parser.DesugarEnv.fst"
let _59_1024 = env
in {curmodule = env0.curmodule; modules = _59_1024.modules; open_namespaces = env0.open_namespaces; modul_abbrevs = _59_1024.modul_abbrevs; sigaccum = _59_1024.sigaccum; localbindings = _59_1024.localbindings; recbindings = _59_1024.recbindings; phase = _59_1024.phase; sigmap = _59_1024.sigmap; default_result_effect = _59_1024.default_result_effect; iface = _59_1024.iface; admitted_iface = _59_1024.admitted_iface}))

# 670 "FStar.Parser.DesugarEnv.fst"
let fail_or = (fun env lookup lid -> (match ((lookup lid)) with
| None -> begin
(
# 674 "FStar.Parser.DesugarEnv.fst"
let r = (match ((try_lookup_name true false env lid)) with
| None -> begin
None
end
| (Some (Knd_name (o, _))) | (Some (Eff_name (o, _))) | (Some (Typ_name (o, _))) | (Some (Exp_name (o, _))) -> begin
Some ((range_of_occurrence o))
end)
in (
# 680 "FStar.Parser.DesugarEnv.fst"
let msg = (match (r) with
| None -> begin
""
end
| Some (r) -> begin
(let _148_739 = (FStar_Range.string_of_range r)
in (FStar_Util.format1 "(Possible clash with related name at %s)" _148_739))
end)
in (let _148_742 = (let _148_741 = (let _148_740 = (FStar_Util.format2 "Identifier not found: [%s] %s" (FStar_Ident.text_of_lid lid) msg)
in (_148_740, (FStar_Ident.range_of_lid lid)))
in FStar_Absyn_Syntax.Error (_148_741))
in (Prims.raise _148_742))))
end
| Some (r) -> begin
r
end))

# 684 "FStar.Parser.DesugarEnv.fst"
let fail_or2 = (fun lookup id -> (match ((lookup id)) with
| None -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (((Prims.strcat (Prims.strcat "Identifier not found [" id.FStar_Ident.idText) "]"), id.FStar_Ident.idRange))))
end
| Some (r) -> begin
r
end))




