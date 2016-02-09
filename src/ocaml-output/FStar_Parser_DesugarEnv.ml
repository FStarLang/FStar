
open Prims
# 31 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

type binding =
| Binding_typ_var of FStar_Ident.ident
| Binding_var of FStar_Ident.ident
| Binding_let of FStar_Ident.lident
| Binding_tycon of FStar_Ident.lident

# 32 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let is_Binding_typ_var = (fun _discr_ -> (match (_discr_) with
| Binding_typ_var (_) -> begin
true
end
| _ -> begin
false
end))

# 33 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let is_Binding_var = (fun _discr_ -> (match (_discr_) with
| Binding_var (_) -> begin
true
end
| _ -> begin
false
end))

# 34 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let is_Binding_let = (fun _discr_ -> (match (_discr_) with
| Binding_let (_) -> begin
true
end
| _ -> begin
false
end))

# 35 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let is_Binding_tycon = (fun _discr_ -> (match (_discr_) with
| Binding_tycon (_) -> begin
true
end
| _ -> begin
false
end))

# 32 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let ___Binding_typ_var____0 : binding  ->  FStar_Ident.ident = (fun projectee -> (match (projectee) with
| Binding_typ_var (_61_18) -> begin
_61_18
end))

# 33 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let ___Binding_var____0 : binding  ->  FStar_Ident.ident = (fun projectee -> (match (projectee) with
| Binding_var (_61_21) -> begin
_61_21
end))

# 34 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let ___Binding_let____0 : binding  ->  FStar_Ident.lident = (fun projectee -> (match (projectee) with
| Binding_let (_61_24) -> begin
_61_24
end))

# 35 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let ___Binding_tycon____0 : binding  ->  FStar_Ident.lident = (fun projectee -> (match (projectee) with
| Binding_tycon (_61_27) -> begin
_61_27
end))

# 37 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

type kind_abbrev =
(FStar_Ident.lident * (FStar_Absyn_Syntax.btvdef, FStar_Absyn_Syntax.bvvdef) FStar_Util.either Prims.list * FStar_Absyn_Syntax.knd)

# 38 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

type env =
{curmodule : FStar_Ident.lident Prims.option; modules : (FStar_Ident.lident * FStar_Absyn_Syntax.modul) Prims.list; open_namespaces : FStar_Ident.lident Prims.list; modul_abbrevs : (FStar_Ident.ident * FStar_Ident.lident) Prims.list; sigaccum : FStar_Absyn_Syntax.sigelts; localbindings : ((FStar_Absyn_Syntax.btvdef, FStar_Absyn_Syntax.bvvdef) FStar_Util.either * binding) Prims.list; recbindings : binding Prims.list; phase : FStar_Parser_AST.level; sigmap : (FStar_Absyn_Syntax.sigelt * Prims.bool) FStar_Util.smap Prims.list; default_result_effect : FStar_Absyn_Syntax.typ  ->  FStar_Range.range  ->  FStar_Absyn_Syntax.comp; iface : Prims.bool; admitted_iface : Prims.bool}

# 38 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let is_Mkenv : env  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv"))))

# 53 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let open_modules : env  ->  (FStar_Ident.lident * FStar_Absyn_Syntax.modul) Prims.list = (fun e -> e.modules)

# 54 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let current_module : env  ->  FStar_Ident.lident = (fun env -> (match (env.curmodule) with
| None -> begin
(FStar_All.failwith "Unset current module")
end
| Some (m) -> begin
m
end))

# 57 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let qual : FStar_Ident.lident  ->  FStar_Ident.ident  ->  FStar_Ident.lident = (fun lid id -> (let _163_114 = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns ((lid.FStar_Ident.ident)::(id)::[])))
in (FStar_Ident.set_lid_range _163_114 id.FStar_Ident.idRange)))

# 58 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let qualify : env  ->  FStar_Ident.ident  ->  FStar_Ident.lident = (fun env id -> (let _163_119 = (current_module env)
in (qual _163_119 id)))

# 59 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let qualify_lid : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (let cur = (current_module env)
in (let _163_124 = (FStar_Ident.lid_of_ids (FStar_List.append (FStar_List.append (FStar_List.append cur.FStar_Ident.ns ((cur.FStar_Ident.ident)::[])) lid.FStar_Ident.ns) ((lid.FStar_Ident.ident)::[])))
in (FStar_Ident.set_lid_range _163_124 (FStar_Ident.range_of_lid lid)))))

# 62 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let new_sigmap = (fun _61_53 -> (match (()) with
| () -> begin
(FStar_Util.smap_create 100)
end))

# 63 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let empty_env : Prims.unit  ->  env = (fun _61_54 -> (match (()) with
| () -> begin
(let _163_129 = (let _163_128 = (new_sigmap ())
in (_163_128)::[])
in {curmodule = None; modules = []; open_namespaces = []; modul_abbrevs = []; sigaccum = []; localbindings = []; recbindings = []; phase = FStar_Parser_AST.Un; sigmap = _163_129; default_result_effect = FStar_Absyn_Util.ml_comp; iface = false; admitted_iface = false})
end))

# 75 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let sigmap : env  ->  (FStar_Absyn_Syntax.sigelt * Prims.bool) FStar_Util.smap = (fun env -> (FStar_List.hd env.sigmap))

# 76 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let default_total : env  ->  env = (fun env -> (let _61_57 = env
in {curmodule = _61_57.curmodule; modules = _61_57.modules; open_namespaces = _61_57.open_namespaces; modul_abbrevs = _61_57.modul_abbrevs; sigaccum = _61_57.sigaccum; localbindings = _61_57.localbindings; recbindings = _61_57.recbindings; phase = _61_57.phase; sigmap = _61_57.sigmap; default_result_effect = (fun t _61_60 -> (FStar_Absyn_Syntax.mk_Total t)); iface = _61_57.iface; admitted_iface = _61_57.admitted_iface}))

# 77 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let default_ml : env  ->  env = (fun env -> (let _61_63 = env
in {curmodule = _61_63.curmodule; modules = _61_63.modules; open_namespaces = _61_63.open_namespaces; modul_abbrevs = _61_63.modul_abbrevs; sigaccum = _61_63.sigaccum; localbindings = _61_63.localbindings; recbindings = _61_63.recbindings; phase = _61_63.phase; sigmap = _61_63.sigmap; default_result_effect = FStar_Absyn_Util.ml_comp; iface = _61_63.iface; admitted_iface = _61_63.admitted_iface}))

# 79 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let range_of_binding : binding  ->  FStar_Range.range = (fun _61_1 -> (match (_61_1) with
| (Binding_typ_var (id)) | (Binding_var (id)) -> begin
id.FStar_Ident.idRange
end
| (Binding_let (lid)) | (Binding_tycon (lid)) -> begin
(FStar_Ident.range_of_lid lid)
end))

# 85 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let try_lookup_typ_var : env  ->  FStar_Ident.ident  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax Prims.option = (fun env id -> (let fopt = (FStar_List.tryFind (fun _61_77 -> (match (_61_77) with
| (_61_75, b) -> begin
(match (b) with
| (Binding_typ_var (id')) | (Binding_var (id')) -> begin
(id.FStar_Ident.idText = id'.FStar_Ident.idText)
end
| _61_82 -> begin
false
end)
end)) env.localbindings)
in (match (fopt) with
| Some (FStar_Util.Inl (bvd), Binding_typ_var (_61_87)) -> begin
(let _163_145 = (FStar_Absyn_Util.bvd_to_typ (FStar_Absyn_Util.set_bvd_range bvd id.FStar_Ident.idRange) FStar_Absyn_Syntax.kun)
in Some (_163_145))
end
| _61_92 -> begin
None
end)))

# 95 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let resolve_in_open_namespaces' = (fun env lid finder -> (let aux = (fun namespaces -> (match ((finder lid)) with
| Some (r) -> begin
Some (r)
end
| _61_102 -> begin
(let ids = (FStar_Ident.ids_of_lid lid)
in (FStar_Util.find_map namespaces (fun ns -> (let full_name = (FStar_Ident.lid_of_ids (FStar_List.append (FStar_Ident.ids_of_lid ns) ids))
in (finder full_name)))))
end))
in (let _163_156 = (let _163_155 = (current_module env)
in (_163_155)::env.open_namespaces)
in (aux _163_156))))

# 106 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let expand_module_abbrevs : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (match (lid.FStar_Ident.ns) with
| id::[] -> begin
(match ((FStar_All.pipe_right env.modul_abbrevs (FStar_List.tryFind (fun _61_113 -> (match (_61_113) with
| (id', _61_112) -> begin
(id.FStar_Ident.idText = id'.FStar_Ident.idText)
end))))) with
| None -> begin
lid
end
| Some (_61_116, lid') -> begin
(FStar_Ident.lid_of_ids (FStar_List.append (FStar_Ident.ids_of_lid lid') ((lid.FStar_Ident.ident)::[])))
end)
end
| _61_121 -> begin
lid
end))

# 116 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let resolve_in_open_namespaces = (fun env lid finder -> (let _163_168 = (expand_module_abbrevs env lid)
in (resolve_in_open_namespaces' env _163_168 finder)))

# 119 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let unmangleMap : (Prims.string * Prims.string) Prims.list = (("op_ColonColon", "Cons"))::(("not", "op_Negation"))::[]

# 122 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let unmangleOpName : FStar_Ident.ident  ->  FStar_Ident.lident Prims.option = (fun id -> (FStar_Util.find_map unmangleMap (fun _61_129 -> (match (_61_129) with
| (x, y) -> begin
if (id.FStar_Ident.idText = x) then begin
(let _163_172 = (FStar_Ident.lid_of_path (("Prims")::(y)::[]) id.FStar_Ident.idRange)
in Some (_163_172))
end else begin
None
end
end))))

# 127 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let try_lookup_id' : env  ->  FStar_Ident.ident  ->  (FStar_Ident.lident * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) Prims.option = (fun env id -> (match ((unmangleOpName id)) with
| Some (l) -> begin
(let _163_178 = (let _163_177 = (FStar_Absyn_Syntax.mk_Exp_fvar ((FStar_Absyn_Util.fv l), None) None id.FStar_Ident.idRange)
in (l, _163_177))
in Some (_163_178))
end
| _61_135 -> begin
(let found = (FStar_Util.find_map env.localbindings (fun _61_2 -> (match (_61_2) with
| (FStar_Util.Inl (_61_138), Binding_typ_var (id')) when (id'.FStar_Ident.idText = id.FStar_Ident.idText) -> begin
Some (FStar_Util.Inl (()))
end
| (FStar_Util.Inr (bvd), Binding_var (id')) when (id'.FStar_Ident.idText = id.FStar_Ident.idText) -> begin
(let _163_183 = (let _163_182 = (let _163_181 = (FStar_Ident.lid_of_ids ((id')::[]))
in (let _163_180 = (FStar_Absyn_Util.bvd_to_exp (FStar_Absyn_Util.set_bvd_range bvd id.FStar_Ident.idRange) FStar_Absyn_Syntax.tun)
in (_163_181, _163_180)))
in FStar_Util.Inr (_163_182))
in Some (_163_183))
end
| _61_149 -> begin
None
end)))
in (match (found) with
| Some (FStar_Util.Inr (x)) -> begin
Some (x)
end
| _61_155 -> begin
None
end))
end))

# 139 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let try_lookup_id : env  ->  FStar_Ident.ident  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax Prims.option = (fun env id -> (match ((try_lookup_id' env id)) with
| Some (_61_159, e) -> begin
Some (e)
end
| None -> begin
None
end))

# 144 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

type occurrence =
| OSig of FStar_Absyn_Syntax.sigelt
| OLet of FStar_Ident.lident
| ORec of FStar_Ident.lident

# 145 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let is_OSig = (fun _discr_ -> (match (_discr_) with
| OSig (_) -> begin
true
end
| _ -> begin
false
end))

# 146 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let is_OLet = (fun _discr_ -> (match (_discr_) with
| OLet (_) -> begin
true
end
| _ -> begin
false
end))

# 147 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let is_ORec = (fun _discr_ -> (match (_discr_) with
| ORec (_) -> begin
true
end
| _ -> begin
false
end))

# 145 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let ___OSig____0 : occurrence  ->  FStar_Absyn_Syntax.sigelt = (fun projectee -> (match (projectee) with
| OSig (_61_166) -> begin
_61_166
end))

# 146 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let ___OLet____0 : occurrence  ->  FStar_Ident.lident = (fun projectee -> (match (projectee) with
| OLet (_61_169) -> begin
_61_169
end))

# 147 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let ___ORec____0 : occurrence  ->  FStar_Ident.lident = (fun projectee -> (match (projectee) with
| ORec (_61_172) -> begin
_61_172
end))

# 148 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let range_of_occurrence : occurrence  ->  FStar_Range.range = (fun _61_3 -> (match (_61_3) with
| (OLet (l)) | (ORec (l)) -> begin
(FStar_Ident.range_of_lid l)
end
| OSig (se) -> begin
(FStar_Absyn_Util.range_of_sigelt se)
end))

# 153 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

type foundname =
| Exp_name of (occurrence * FStar_Absyn_Syntax.exp)
| Typ_name of (occurrence * FStar_Absyn_Syntax.typ)
| Eff_name of (occurrence * FStar_Ident.lident)
| Knd_name of (occurrence * FStar_Ident.lident)

# 154 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let is_Exp_name = (fun _discr_ -> (match (_discr_) with
| Exp_name (_) -> begin
true
end
| _ -> begin
false
end))

# 155 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let is_Typ_name = (fun _discr_ -> (match (_discr_) with
| Typ_name (_) -> begin
true
end
| _ -> begin
false
end))

# 156 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let is_Eff_name = (fun _discr_ -> (match (_discr_) with
| Eff_name (_) -> begin
true
end
| _ -> begin
false
end))

# 157 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let is_Knd_name = (fun _discr_ -> (match (_discr_) with
| Knd_name (_) -> begin
true
end
| _ -> begin
false
end))

# 154 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let ___Exp_name____0 : foundname  ->  (occurrence * FStar_Absyn_Syntax.exp) = (fun projectee -> (match (projectee) with
| Exp_name (_61_181) -> begin
_61_181
end))

# 155 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let ___Typ_name____0 : foundname  ->  (occurrence * FStar_Absyn_Syntax.typ) = (fun projectee -> (match (projectee) with
| Typ_name (_61_184) -> begin
_61_184
end))

# 156 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let ___Eff_name____0 : foundname  ->  (occurrence * FStar_Ident.lident) = (fun projectee -> (match (projectee) with
| Eff_name (_61_187) -> begin
_61_187
end))

# 157 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let ___Knd_name____0 : foundname  ->  (occurrence * FStar_Ident.lident) = (fun projectee -> (match (projectee) with
| Knd_name (_61_190) -> begin
_61_190
end))

# 159 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let fv_qual_of_se : FStar_Absyn_Syntax.sigelt  ->  FStar_Absyn_Syntax.fv_qual Prims.option = (fun _61_5 -> (match (_61_5) with
| FStar_Absyn_Syntax.Sig_datacon (_61_193, _61_195, (l, _61_198, _61_200), quals, _61_204, _61_206) -> begin
(let qopt = (FStar_Util.find_map quals (fun _61_4 -> (match (_61_4) with
| FStar_Absyn_Syntax.RecordConstructor (fs) -> begin
Some (FStar_Absyn_Syntax.Record_ctor ((l, fs)))
end
| _61_213 -> begin
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
| FStar_Absyn_Syntax.Sig_val_decl (_61_218, _61_220, quals, _61_223) -> begin
None
end
| _61_227 -> begin
None
end))

# 172 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let try_lookup_name : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  foundname Prims.option = (fun any_val exclude_interf env lid -> (let find_in_sig = (fun lid -> (match ((let _163_301 = (sigmap env)
in (FStar_Util.smap_try_find _163_301 lid.FStar_Ident.str))) with
| Some (_61_235, true) when exclude_interf -> begin
None
end
| None -> begin
None
end
| Some (se, _61_242) -> begin
(match (se) with
| (FStar_Absyn_Syntax.Sig_typ_abbrev (_)) | (FStar_Absyn_Syntax.Sig_tycon (_)) -> begin
(let _163_304 = (let _163_303 = (let _163_302 = (FStar_Absyn_Util.ftv lid FStar_Absyn_Syntax.kun)
in (OSig (se), _163_302))
in Typ_name (_163_303))
in Some (_163_304))
end
| FStar_Absyn_Syntax.Sig_kind_abbrev (_61_252) -> begin
Some (Knd_name ((OSig (se), lid)))
end
| FStar_Absyn_Syntax.Sig_new_effect (ne, _61_256) -> begin
(let _163_307 = (let _163_306 = (let _163_305 = (FStar_Ident.set_lid_range ne.FStar_Absyn_Syntax.mname (FStar_Ident.range_of_lid lid))
in (OSig (se), _163_305))
in Eff_name (_163_306))
in Some (_163_307))
end
| FStar_Absyn_Syntax.Sig_effect_abbrev (_61_260) -> begin
Some (Eff_name ((OSig (se), lid)))
end
| FStar_Absyn_Syntax.Sig_datacon (_61_263) -> begin
(let _163_311 = (let _163_310 = (let _163_309 = (let _163_308 = (fv_qual_of_se se)
in (FStar_Absyn_Util.fvar _163_308 lid (FStar_Ident.range_of_lid lid)))
in (OSig (se), _163_309))
in Exp_name (_163_310))
in Some (_163_311))
end
| FStar_Absyn_Syntax.Sig_let (_61_266) -> begin
(let _163_314 = (let _163_313 = (let _163_312 = (FStar_Absyn_Util.fvar None lid (FStar_Ident.range_of_lid lid))
in (OSig (se), _163_312))
in Exp_name (_163_313))
in Some (_163_314))
end
| FStar_Absyn_Syntax.Sig_val_decl (_61_269, _61_271, quals, _61_274) -> begin
if (any_val || (FStar_All.pipe_right quals (FStar_Util.for_some (fun _61_6 -> (match (_61_6) with
| FStar_Absyn_Syntax.Assumption -> begin
true
end
| _61_280 -> begin
false
end))))) then begin
(let _163_319 = (let _163_318 = (let _163_317 = (let _163_316 = (fv_qual_of_se se)
in (FStar_Absyn_Util.fvar _163_316 lid (FStar_Ident.range_of_lid lid)))
in (OSig (se), _163_317))
in Exp_name (_163_318))
in Some (_163_319))
end else begin
None
end
end
| _61_282 -> begin
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
in (FStar_Util.find_map env.recbindings (fun _61_7 -> (match (_61_7) with
| Binding_let (l) when (FStar_Ident.lid_equals l recname) -> begin
(let _163_323 = (let _163_322 = (let _163_321 = (FStar_Absyn_Util.fvar None recname (FStar_Ident.range_of_lid recname))
in (ORec (l), _163_321))
in Exp_name (_163_322))
in Some (_163_323))
end
| Binding_tycon (l) when (FStar_Ident.lid_equals l recname) -> begin
(let _163_326 = (let _163_325 = (let _163_324 = (FStar_Absyn_Util.ftv recname FStar_Absyn_Syntax.kun)
in (ORec (l), _163_324))
in Typ_name (_163_325))
in Some (_163_326))
end
| _61_296 -> begin
None
end))))
end)
end
| _61_298 -> begin
None
end)
in (match (found_id) with
| Some (_61_301) -> begin
found_id
end
| _61_304 -> begin
(resolve_in_open_namespaces env lid find_in_sig)
end))))

# 218 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let try_lookup_typ_name' : Prims.bool  ->  env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.typ Prims.option = (fun exclude_interf env lid -> (match ((try_lookup_name true exclude_interf env lid)) with
| Some (Typ_name (_61_309, t)) -> begin
Some (t)
end
| Some (Eff_name (_61_315, l)) -> begin
(let _163_333 = (FStar_Absyn_Util.ftv l FStar_Absyn_Syntax.mk_Kind_unknown)
in Some (_163_333))
end
| _61_321 -> begin
None
end))

# 223 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let try_lookup_typ_name : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.typ Prims.option = (fun env l -> (try_lookup_typ_name' (not (env.iface)) env l))

# 225 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let try_lookup_effect_name' : Prims.bool  ->  env  ->  FStar_Ident.lident  ->  (occurrence * FStar_Ident.lident) Prims.option = (fun exclude_interf env lid -> (match ((try_lookup_name true exclude_interf env lid)) with
| Some (Eff_name (o, l)) -> begin
Some ((o, l))
end
| _61_333 -> begin
None
end))

# 229 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let try_lookup_effect_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env l -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some (o, l) -> begin
Some (l)
end
| _61_341 -> begin
None
end))

# 233 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let try_lookup_effect_defn : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.eff_decl Prims.option = (fun env l -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some (OSig (FStar_Absyn_Syntax.Sig_new_effect (ne, _61_346)), _61_351) -> begin
Some (ne)
end
| _61_355 -> begin
None
end))

# 237 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let is_effect_name : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((try_lookup_effect_name env lid)) with
| None -> begin
false
end
| Some (_61_360) -> begin
true
end))

# 242 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let try_resolve_typ_abbrev : env  ->  FStar_Ident.lident  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax Prims.option = (fun env lid -> (let find_in_sig = (fun lid -> (match ((let _163_362 = (sigmap env)
in (FStar_Util.smap_try_find _163_362 lid.FStar_Ident.str))) with
| Some (FStar_Absyn_Syntax.Sig_typ_abbrev (lid, tps, k, def, _61_371, _61_373), _61_377) -> begin
(let t = (let _163_365 = (let _163_364 = (let _163_363 = (FStar_Absyn_Util.close_with_lam tps def)
in (_163_363, lid))
in FStar_Absyn_Syntax.Meta_named (_163_364))
in (FStar_Absyn_Syntax.mk_Typ_meta _163_365))
in Some (t))
end
| _61_382 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))

# 251 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let lookup_letbinding_quals : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.qualifier Prims.list = (fun env lid -> (let find_in_sig = (fun lid -> (match ((let _163_372 = (sigmap env)
in (FStar_Util.smap_try_find _163_372 lid.FStar_Ident.str))) with
| Some (FStar_Absyn_Syntax.Sig_val_decl (lid, _61_389, quals, _61_392), _61_396) -> begin
Some (quals)
end
| _61_400 -> begin
None
end))
in (match ((resolve_in_open_namespaces env lid find_in_sig)) with
| Some (quals) -> begin
quals
end
| _61_404 -> begin
[]
end)))

# 260 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let try_lookup_module : env  ->  Prims.string Prims.list  ->  FStar_Absyn_Syntax.modul Prims.option = (fun env path -> (match ((FStar_List.tryFind (fun _61_409 -> (match (_61_409) with
| (mlid, modul) -> begin
((FStar_Ident.path_of_lid mlid) = path)
end)) env.modules)) with
| Some (_61_411, modul) -> begin
Some (modul)
end
| None -> begin
None
end))

# 265 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let try_lookup_let : env  ->  FStar_Ident.lident  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax Prims.option = (fun env lid -> (let find_in_sig = (fun lid -> (match ((let _163_384 = (sigmap env)
in (FStar_Util.smap_try_find _163_384 lid.FStar_Ident.str))) with
| Some (FStar_Absyn_Syntax.Sig_let (_61_421), _61_424) -> begin
(let _163_385 = (FStar_Absyn_Util.fvar None lid (FStar_Ident.range_of_lid lid))
in Some (_163_385))
end
| _61_428 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))

# 272 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let try_lookup_lid' : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.exp Prims.option = (fun any_val exclude_interf env lid -> (match ((try_lookup_name any_val exclude_interf env lid)) with
| Some (Exp_name (_61_434, e)) -> begin
Some (e)
end
| _61_440 -> begin
None
end))

# 276 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let try_lookup_lid : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.exp Prims.option = (fun env l -> (try_lookup_lid' env.iface false env l))

# 278 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let try_lookup_datacon : env  ->  FStar_Ident.lident  ->  (FStar_Ident.lid, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t Prims.option = (fun env lid -> (let find_in_sig = (fun lid -> (match ((let _163_404 = (sigmap env)
in (FStar_Util.smap_try_find _163_404 lid.FStar_Ident.str))) with
| Some (FStar_Absyn_Syntax.Sig_val_decl (_61_448, _61_450, quals, _61_453), _61_457) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _61_8 -> (match (_61_8) with
| FStar_Absyn_Syntax.Assumption -> begin
true
end
| _61_463 -> begin
false
end)))) then begin
Some ((FStar_Absyn_Util.fv lid))
end else begin
None
end
end
| Some (FStar_Absyn_Syntax.Sig_datacon (_61_465), _61_468) -> begin
Some ((FStar_Absyn_Util.fv lid))
end
| _61_472 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))

# 289 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let find_all_datacons : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.lident Prims.list Prims.option = (fun env lid -> (let find_in_sig = (fun lid -> (match ((let _163_412 = (sigmap env)
in (FStar_Util.smap_try_find _163_412 lid.FStar_Ident.str))) with
| Some (FStar_Absyn_Syntax.Sig_tycon (_61_478, _61_480, _61_482, _61_484, datas, _61_487, _61_489), _61_493) -> begin
Some (datas)
end
| _61_497 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))

# 296 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

type record_or_dc =
{typename : FStar_Ident.lident; constrname : FStar_Ident.lident; parms : FStar_Absyn_Syntax.binders; fields : (FStar_Absyn_Syntax.fieldname * FStar_Absyn_Syntax.typ) Prims.list; is_record : Prims.bool}

# 296 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let is_Mkrecord_or_dc : record_or_dc  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkrecord_or_dc"))))

# 305 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let record_cache_aux : ((Prims.unit  ->  Prims.unit) * (Prims.unit  ->  Prims.unit) * (Prims.unit  ->  record_or_dc Prims.list) * (record_or_dc  ->  Prims.unit)) = (let record_cache = (FStar_Util.mk_ref (([])::[]))
in (let push = (fun _61_506 -> (match (()) with
| () -> begin
(let _163_442 = (let _163_441 = (let _163_439 = (FStar_ST.read record_cache)
in (FStar_List.hd _163_439))
in (let _163_440 = (FStar_ST.read record_cache)
in (_163_441)::_163_440))
in (FStar_ST.op_Colon_Equals record_cache _163_442))
end))
in (let pop = (fun _61_508 -> (match (()) with
| () -> begin
(let _163_446 = (let _163_445 = (FStar_ST.read record_cache)
in (FStar_List.tl _163_445))
in (FStar_ST.op_Colon_Equals record_cache _163_446))
end))
in (let peek = (fun _61_510 -> (match (()) with
| () -> begin
(let _163_449 = (FStar_ST.read record_cache)
in (FStar_List.hd _163_449))
end))
in (let insert = (fun r -> (let _163_456 = (let _163_455 = (let _163_452 = (peek ())
in (r)::_163_452)
in (let _163_454 = (let _163_453 = (FStar_ST.read record_cache)
in (FStar_List.tl _163_453))
in (_163_455)::_163_454))
in (FStar_ST.op_Colon_Equals record_cache _163_456)))
in (push, pop, peek, insert))))))

# 315 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let push_record_cache : Prims.unit  ->  Prims.unit = (let _61_520 = record_cache_aux
in (match (_61_520) with
| (push, _61_515, _61_517, _61_519) -> begin
push
end))

# 319 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let pop_record_cache : Prims.unit  ->  Prims.unit = (let _61_528 = record_cache_aux
in (match (_61_528) with
| (_61_522, pop, _61_525, _61_527) -> begin
pop
end))

# 323 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let peek_record_cache : Prims.unit  ->  record_or_dc Prims.list = (let _61_536 = record_cache_aux
in (match (_61_536) with
| (_61_530, _61_532, peek, _61_535) -> begin
peek
end))

# 327 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let insert_record_cache : record_or_dc  ->  Prims.unit = (let _61_544 = record_cache_aux
in (match (_61_544) with
| (_61_538, _61_540, _61_542, insert) -> begin
insert
end))

# 331 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let extract_record : env  ->  FStar_Absyn_Syntax.sigelt  ->  Prims.unit = (fun e _61_12 -> (match (_61_12) with
| FStar_Absyn_Syntax.Sig_bundle (sigs, _61_549, _61_551, _61_553) -> begin
(let is_rec = (FStar_Util.for_some (fun _61_9 -> (match (_61_9) with
| (FStar_Absyn_Syntax.RecordType (_)) | (FStar_Absyn_Syntax.RecordConstructor (_)) -> begin
true
end
| _61_564 -> begin
false
end)))
in (let find_dc = (fun dc -> (FStar_All.pipe_right sigs (FStar_Util.find_opt (fun _61_10 -> (match (_61_10) with
| FStar_Absyn_Syntax.Sig_datacon (lid, _61_571, _61_573, _61_575, _61_577, _61_579) -> begin
(FStar_Ident.lid_equals dc lid)
end
| _61_583 -> begin
false
end)))))
in (FStar_All.pipe_right sigs (FStar_List.iter (fun _61_11 -> (match (_61_11) with
| FStar_Absyn_Syntax.Sig_tycon (typename, parms, _61_588, _61_590, dc::[], tags, _61_595) -> begin
(match ((let _163_527 = (find_dc dc)
in (FStar_All.pipe_left FStar_Util.must _163_527))) with
| FStar_Absyn_Syntax.Sig_datacon (constrname, t, _61_601, _61_603, _61_605, _61_607) -> begin
(let formals = (match ((FStar_Absyn_Util.function_formals t)) with
| Some (x, _61_612) -> begin
x
end
| _61_616 -> begin
[]
end)
in (let is_rec = (is_rec tags)
in (let fields = (FStar_All.pipe_right formals (FStar_List.collect (fun b -> (match (b) with
| (FStar_Util.Inr (x), q) -> begin
if ((FStar_Absyn_Syntax.is_null_binder b) || (is_rec && (match (q) with
| Some (FStar_Absyn_Syntax.Implicit (_61_625)) -> begin
true
end
| _61_629 -> begin
false
end))) then begin
[]
end else begin
(let _163_531 = (let _163_530 = (let _163_529 = if is_rec then begin
(FStar_Absyn_Util.unmangle_field_name x.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ppname)
end else begin
x.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ppname
end
in (qual constrname _163_529))
in (_163_530, x.FStar_Absyn_Syntax.sort))
in (_163_531)::[])
end
end
| _61_631 -> begin
[]
end))))
in (let record = {typename = typename; constrname = constrname; parms = parms; fields = fields; is_record = is_rec}
in (insert_record_cache record)))))
end
| _61_635 -> begin
()
end)
end
| _61_637 -> begin
()
end))))))
end
| _61_639 -> begin
()
end))

# 370 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

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
(let _163_542 = (aux tl)
in (hd)::_163_542)
end))
in (aux ns)))
in (let find_in_cache = (fun fieldname -> (let _61_657 = (fieldname.FStar_Ident.ns, fieldname.FStar_Ident.ident)
in (match (_61_657) with
| (ns, fieldname) -> begin
(let _163_547 = (peek_record_cache ())
in (FStar_Util.find_map _163_547 (fun record -> (let constrname = record.constrname.FStar_Ident.ident
in (let ns = (maybe_add_constrname ns constrname)
in (let fname = (FStar_Ident.lid_of_ids (FStar_List.append ns ((fieldname)::[])))
in (FStar_Util.find_map record.fields (fun _61_665 -> (match (_61_665) with
| (f, _61_664) -> begin
if (FStar_Ident.lid_equals fname f) then begin
Some ((record, fname))
end else begin
None
end
end)))))))))
end)))
in (resolve_in_open_namespaces env fieldname find_in_cache))))

# 390 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let try_lookup_record_by_field_name : env  ->  FStar_Ident.lident  ->  (record_or_dc * FStar_Ident.lident) Prims.option = (fun env fieldname -> (match ((try_lookup_record_or_dc_by_field_name env fieldname)) with
| Some (r, f) when r.is_record -> begin
Some ((r, f))
end
| _61_673 -> begin
None
end))

# 395 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let try_lookup_projector_by_field_name : env  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * Prims.bool) Prims.option = (fun env fieldname -> (match ((try_lookup_record_or_dc_by_field_name env fieldname)) with
| Some (r, f) -> begin
Some ((f, r.is_record))
end
| _61_681 -> begin
None
end))

# 400 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let qualify_field_to_record : env  ->  record_or_dc  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env recd f -> (let qualify = (fun fieldname -> (let _61_689 = (fieldname.FStar_Ident.ns, fieldname.FStar_Ident.ident)
in (match (_61_689) with
| (ns, fieldname) -> begin
(let constrname = recd.constrname.FStar_Ident.ident
in (let fname = (FStar_Ident.lid_of_ids (FStar_List.append (FStar_List.append ns ((constrname)::[])) ((fieldname)::[])))
in (FStar_Util.find_map recd.fields (fun _61_695 -> (match (_61_695) with
| (f, _61_694) -> begin
if (FStar_Ident.lid_equals fname f) then begin
Some (fname)
end else begin
None
end
end)))))
end)))
in (resolve_in_open_namespaces env f qualify)))

# 411 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let find_kind_abbrev : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env l -> (match ((try_lookup_name true (not (env.iface)) env l)) with
| Some (Knd_name (_61_699, l)) -> begin
Some (l)
end
| _61_705 -> begin
None
end))

# 416 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let is_kind_abbrev : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (match ((find_kind_abbrev env l)) with
| None -> begin
false
end
| Some (_61_710) -> begin
true
end))

# 421 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let unique_name : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  Prims.bool = (fun any_val exclude_if env lid -> (match ((try_lookup_lid' any_val exclude_if env lid)) with
| None -> begin
(match ((find_kind_abbrev env lid)) with
| None -> begin
true
end
| Some (_61_719) -> begin
false
end)
end
| Some (_61_722) -> begin
false
end))

# 430 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let unique_typ_name : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((try_lookup_typ_name' true env lid)) with
| None -> begin
true
end
| Some (a) -> begin
false
end))

# 435 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let unique : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  Prims.bool = (fun any_val exclude_if env lid -> (let this_env = (let _61_733 = env
in {curmodule = _61_733.curmodule; modules = _61_733.modules; open_namespaces = []; modul_abbrevs = _61_733.modul_abbrevs; sigaccum = _61_733.sigaccum; localbindings = _61_733.localbindings; recbindings = _61_733.recbindings; phase = _61_733.phase; sigmap = _61_733.sigmap; default_result_effect = _61_733.default_result_effect; iface = _61_733.iface; admitted_iface = _61_733.admitted_iface})
in ((unique_name any_val exclude_if this_env lid) && (unique_typ_name this_env lid))))

# 439 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let gen_bvd = (fun _61_13 -> (match (_61_13) with
| Binding_typ_var (id) -> begin
(let _163_596 = (let _163_595 = (let _163_594 = (FStar_Absyn_Util.genident (Some (id.FStar_Ident.idRange)))
in (id, _163_594))
in (FStar_Absyn_Util.mkbvd _163_595))
in FStar_Util.Inl (_163_596))
end
| Binding_var (id) -> begin
(let _163_599 = (let _163_598 = (let _163_597 = (FStar_Absyn_Util.genident (Some (id.FStar_Ident.idRange)))
in (id, _163_597))
in (FStar_Absyn_Util.mkbvd _163_598))
in FStar_Util.Inr (_163_599))
end
| _61_742 -> begin
(FStar_All.failwith "Tried to generate a bound variable for a type constructor")
end))

# 444 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let push_bvvdef : env  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef  ->  env = (fun env x -> (let b = Binding_var (x.FStar_Absyn_Syntax.ppname)
in (let _61_746 = env
in {curmodule = _61_746.curmodule; modules = _61_746.modules; open_namespaces = _61_746.open_namespaces; modul_abbrevs = _61_746.modul_abbrevs; sigaccum = _61_746.sigaccum; localbindings = ((FStar_Util.Inr (x), b))::env.localbindings; recbindings = _61_746.recbindings; phase = _61_746.phase; sigmap = _61_746.sigmap; default_result_effect = _61_746.default_result_effect; iface = _61_746.iface; admitted_iface = _61_746.admitted_iface})))

# 448 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let push_btvdef : env  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef  ->  env = (fun env x -> (let b = Binding_typ_var (x.FStar_Absyn_Syntax.ppname)
in (let _61_751 = env
in {curmodule = _61_751.curmodule; modules = _61_751.modules; open_namespaces = _61_751.open_namespaces; modul_abbrevs = _61_751.modul_abbrevs; sigaccum = _61_751.sigaccum; localbindings = ((FStar_Util.Inl (x), b))::env.localbindings; recbindings = _61_751.recbindings; phase = _61_751.phase; sigmap = _61_751.sigmap; default_result_effect = _61_751.default_result_effect; iface = _61_751.iface; admitted_iface = _61_751.admitted_iface})))

# 452 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let push_local_binding : env  ->  binding  ->  (env * ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef) FStar_Util.either) = (fun env b -> (let bvd = (gen_bvd b)
in ((let _61_756 = env
in {curmodule = _61_756.curmodule; modules = _61_756.modules; open_namespaces = _61_756.open_namespaces; modul_abbrevs = _61_756.modul_abbrevs; sigaccum = _61_756.sigaccum; localbindings = ((bvd, b))::env.localbindings; recbindings = _61_756.recbindings; phase = _61_756.phase; sigmap = _61_756.sigmap; default_result_effect = _61_756.default_result_effect; iface = _61_756.iface; admitted_iface = _61_756.admitted_iface}), bvd)))

# 456 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let push_local_tbinding : env  ->  FStar_Ident.ident  ->  (env * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef) = (fun env a -> (match ((push_local_binding env (Binding_typ_var (a)))) with
| (env, FStar_Util.Inl (x)) -> begin
(env, x)
end
| _61_765 -> begin
(FStar_All.failwith "impossible")
end))

# 461 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let push_local_vbinding : env  ->  FStar_Ident.ident  ->  (env * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef) = (fun env b -> (match ((push_local_binding env (Binding_var (b)))) with
| (env, FStar_Util.Inr (x)) -> begin
(env, x)
end
| _61_773 -> begin
(FStar_All.failwith "impossible")
end))

# 467 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let push_rec_binding : env  ->  binding  ->  env = (fun env b -> (match (b) with
| (Binding_let (lid)) | (Binding_tycon (lid)) -> begin
if (unique false true env lid) then begin
(let _61_779 = env
in {curmodule = _61_779.curmodule; modules = _61_779.modules; open_namespaces = _61_779.open_namespaces; modul_abbrevs = _61_779.modul_abbrevs; sigaccum = _61_779.sigaccum; localbindings = _61_779.localbindings; recbindings = (b)::env.recbindings; phase = _61_779.phase; sigmap = _61_779.sigmap; default_result_effect = _61_779.default_result_effect; iface = _61_779.iface; admitted_iface = _61_779.admitted_iface})
end else begin
(Prims.raise (FStar_Absyn_Syntax.Error (((Prims.strcat "Duplicate top-level names " lid.FStar_Ident.str), (FStar_Ident.range_of_lid lid)))))
end
end
| _61_782 -> begin
(FStar_All.failwith "Unexpected rec_binding")
end))

# 475 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let push_sigelt : env  ->  FStar_Absyn_Syntax.sigelt  ->  env = (fun env s -> (let err = (fun l -> (let sopt = (let _163_630 = (sigmap env)
in (FStar_Util.smap_try_find _163_630 l.FStar_Ident.str))
in (let r = (match (sopt) with
| Some (se, _61_790) -> begin
(match ((let _163_631 = (FStar_Absyn_Util.lids_of_sigelt se)
in (FStar_Util.find_opt (FStar_Ident.lid_equals l) _163_631))) with
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
in (let _163_634 = (let _163_633 = (let _163_632 = (FStar_Util.format2 "Duplicate top-level names [%s]; previously declared at %s" (FStar_Ident.text_of_lid l) r)
in (_163_632, (FStar_Ident.range_of_lid l)))
in FStar_Absyn_Syntax.Error (_163_633))
in (Prims.raise _163_634)))))
in (let env = (let _61_808 = (match (s) with
| FStar_Absyn_Syntax.Sig_let (_61_799) -> begin
(false, true)
end
| FStar_Absyn_Syntax.Sig_bundle (_61_802) -> begin
(true, true)
end
| _61_805 -> begin
(false, false)
end)
in (match (_61_808) with
| (any_val, exclude_if) -> begin
(let lids = (FStar_Absyn_Util.lids_of_sigelt s)
in (match ((FStar_Util.find_map lids (fun l -> if (not ((unique any_val exclude_if env l))) then begin
Some (l)
end else begin
None
end))) with
| None -> begin
(let _61_812 = (extract_record env s)
in (let _61_814 = env
in {curmodule = _61_814.curmodule; modules = _61_814.modules; open_namespaces = _61_814.open_namespaces; modul_abbrevs = _61_814.modul_abbrevs; sigaccum = (s)::env.sigaccum; localbindings = _61_814.localbindings; recbindings = _61_814.recbindings; phase = _61_814.phase; sigmap = _61_814.sigmap; default_result_effect = _61_814.default_result_effect; iface = _61_814.iface; admitted_iface = _61_814.admitted_iface}))
end
| Some (l) -> begin
(err l)
end))
end))
in (let _61_833 = (match (s) with
| FStar_Absyn_Syntax.Sig_bundle (ses, _61_821, _61_823, _61_825) -> begin
(let _163_638 = (FStar_List.map (fun se -> (let _163_637 = (FStar_Absyn_Util.lids_of_sigelt se)
in (_163_637, se))) ses)
in (env, _163_638))
end
| _61_830 -> begin
(let _163_641 = (let _163_640 = (let _163_639 = (FStar_Absyn_Util.lids_of_sigelt s)
in (_163_639, s))
in (_163_640)::[])
in (env, _163_641))
end)
in (match (_61_833) with
| (env, lss) -> begin
(let _61_838 = (FStar_All.pipe_right lss (FStar_List.iter (fun _61_836 -> (match (_61_836) with
| (lids, se) -> begin
(FStar_All.pipe_right lids (FStar_List.iter (fun lid -> (let _163_644 = (sigmap env)
in (FStar_Util.smap_add _163_644 lid.FStar_Ident.str (se, (env.iface && (not (env.admitted_iface)))))))))
end))))
in env)
end)))))

# 504 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let push_namespace : env  ->  FStar_Ident.lident  ->  env = (fun env lid -> (let _61_842 = env
in {curmodule = _61_842.curmodule; modules = _61_842.modules; open_namespaces = (lid)::env.open_namespaces; modul_abbrevs = _61_842.modul_abbrevs; sigaccum = _61_842.sigaccum; localbindings = _61_842.localbindings; recbindings = _61_842.recbindings; phase = _61_842.phase; sigmap = _61_842.sigmap; default_result_effect = _61_842.default_result_effect; iface = _61_842.iface; admitted_iface = _61_842.admitted_iface}))

# 507 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let push_module_abbrev : env  ->  FStar_Ident.ident  ->  FStar_Ident.lident  ->  env = (fun env x l -> if (FStar_All.pipe_right env.modul_abbrevs (FStar_Util.for_some (fun _61_850 -> (match (_61_850) with
| (y, _61_849) -> begin
(x.FStar_Ident.idText = y.FStar_Ident.idText)
end)))) then begin
(let _163_658 = (let _163_657 = (let _163_656 = (FStar_Util.format1 "Module %s is already defined" x.FStar_Ident.idText)
in (_163_656, x.FStar_Ident.idRange))
in FStar_Absyn_Syntax.Error (_163_657))
in (Prims.raise _163_658))
end else begin
(let _61_851 = env
in {curmodule = _61_851.curmodule; modules = _61_851.modules; open_namespaces = _61_851.open_namespaces; modul_abbrevs = ((x, l))::env.modul_abbrevs; sigaccum = _61_851.sigaccum; localbindings = _61_851.localbindings; recbindings = _61_851.recbindings; phase = _61_851.phase; sigmap = _61_851.sigmap; default_result_effect = _61_851.default_result_effect; iface = _61_851.iface; admitted_iface = _61_851.admitted_iface})
end)

# 512 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let is_type_lid : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (let aux = (fun _61_856 -> (match (()) with
| () -> begin
(match ((try_lookup_typ_name' false env lid)) with
| Some (_61_858) -> begin
true
end
| _61_861 -> begin
false
end)
end))
in if (lid.FStar_Ident.ns = []) then begin
(match ((try_lookup_id env lid.FStar_Ident.ident)) with
| Some (_61_863) -> begin
false
end
| _61_866 -> begin
(aux ())
end)
end else begin
(aux ())
end))

# 523 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let check_admits : FStar_Ident.lident  ->  env  ->  Prims.unit = (fun nm env -> (let warn = (not ((let _163_670 = (FStar_ST.read FStar_Options.admit_fsi)
in (FStar_All.pipe_right _163_670 (FStar_Util.for_some (fun l -> (nm.FStar_Ident.str = l)))))))
in (FStar_All.pipe_right env.sigaccum (FStar_List.iter (fun se -> (match (se) with
| FStar_Absyn_Syntax.Sig_val_decl (l, t, quals, r) -> begin
(match ((try_lookup_lid env l)) with
| None -> begin
(let _61_879 = if warn then begin
(let _163_674 = (let _163_673 = (FStar_Range.string_of_range (FStar_Ident.range_of_lid l))
in (let _163_672 = (FStar_Absyn_Print.sli l)
in (FStar_Util.format2 "%s: Warning: Admitting %s without a definition\n" _163_673 _163_672)))
in (FStar_Util.print_string _163_674))
end else begin
()
end
in (let _163_675 = (sigmap env)
in (FStar_Util.smap_add _163_675 l.FStar_Ident.str (FStar_Absyn_Syntax.Sig_val_decl ((l, t, (FStar_Absyn_Syntax.Assumption)::quals, r)), false))))
end
| Some (_61_882) -> begin
()
end)
end
| _61_885 -> begin
()
end))))))

# 535 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let finish : env  ->  FStar_Absyn_Syntax.modul  ->  env = (fun env modul -> (let _61_923 = (FStar_All.pipe_right modul.FStar_Absyn_Syntax.declarations (FStar_List.iter (fun _61_15 -> (match (_61_15) with
| FStar_Absyn_Syntax.Sig_bundle (ses, quals, _61_892, _61_894) -> begin
if (FStar_List.contains FStar_Absyn_Syntax.Private quals) then begin
(FStar_All.pipe_right ses (FStar_List.iter (fun _61_14 -> (match (_61_14) with
| FStar_Absyn_Syntax.Sig_datacon (lid, _61_900, _61_902, _61_904, _61_906, _61_908) -> begin
(let _163_682 = (sigmap env)
in (FStar_Util.smap_remove _163_682 lid.FStar_Ident.str))
end
| _61_912 -> begin
()
end))))
end else begin
()
end
end
| FStar_Absyn_Syntax.Sig_val_decl (lid, _61_915, quals, _61_918) -> begin
if (FStar_List.contains FStar_Absyn_Syntax.Private quals) then begin
(let _163_683 = (sigmap env)
in (FStar_Util.smap_remove _163_683 lid.FStar_Ident.str))
end else begin
()
end
end
| _61_922 -> begin
()
end))))
in (let _61_925 = env
in {curmodule = None; modules = ((modul.FStar_Absyn_Syntax.name, modul))::env.modules; open_namespaces = []; modul_abbrevs = []; sigaccum = []; localbindings = []; recbindings = []; phase = FStar_Parser_AST.Un; sigmap = _61_925.sigmap; default_result_effect = _61_925.default_result_effect; iface = _61_925.iface; admitted_iface = _61_925.admitted_iface})))

# 556 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let push : env  ->  env = (fun env -> (let _61_928 = (push_record_cache ())
in (let _61_930 = env
in (let _163_688 = (let _163_687 = (let _163_686 = (sigmap env)
in (FStar_Util.smap_copy _163_686))
in (_163_687)::env.sigmap)
in {curmodule = _61_930.curmodule; modules = _61_930.modules; open_namespaces = _61_930.open_namespaces; modul_abbrevs = _61_930.modul_abbrevs; sigaccum = _61_930.sigaccum; localbindings = _61_930.localbindings; recbindings = _61_930.recbindings; phase = _61_930.phase; sigmap = _163_688; default_result_effect = _61_930.default_result_effect; iface = _61_930.iface; admitted_iface = _61_930.admitted_iface}))))

# 561 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let mark : env  ->  env = (fun env -> (push env))

# 562 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let reset_mark : env  ->  env = (fun env -> (let _61_934 = env
in (let _163_693 = (FStar_List.tl env.sigmap)
in {curmodule = _61_934.curmodule; modules = _61_934.modules; open_namespaces = _61_934.open_namespaces; modul_abbrevs = _61_934.modul_abbrevs; sigaccum = _61_934.sigaccum; localbindings = _61_934.localbindings; recbindings = _61_934.recbindings; phase = _61_934.phase; sigmap = _163_693; default_result_effect = _61_934.default_result_effect; iface = _61_934.iface; admitted_iface = _61_934.admitted_iface})))

# 563 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let commit_mark : env  ->  env = (fun env -> (match (env.sigmap) with
| hd::_61_939::tl -> begin
(let _61_943 = env
in {curmodule = _61_943.curmodule; modules = _61_943.modules; open_namespaces = _61_943.open_namespaces; modul_abbrevs = _61_943.modul_abbrevs; sigaccum = _61_943.sigaccum; localbindings = _61_943.localbindings; recbindings = _61_943.recbindings; phase = _61_943.phase; sigmap = (hd)::tl; default_result_effect = _61_943.default_result_effect; iface = _61_943.iface; admitted_iface = _61_943.admitted_iface})
end
| _61_946 -> begin
(FStar_All.failwith "Impossible")
end))

# 566 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let pop : env  ->  env = (fun env -> (match (env.sigmap) with
| _61_950::maps -> begin
(let _61_952 = (pop_record_cache ())
in (let _61_954 = env
in {curmodule = _61_954.curmodule; modules = _61_954.modules; open_namespaces = _61_954.open_namespaces; modul_abbrevs = _61_954.modul_abbrevs; sigaccum = _61_954.sigaccum; localbindings = _61_954.localbindings; recbindings = _61_954.recbindings; phase = _61_954.phase; sigmap = maps; default_result_effect = _61_954.default_result_effect; iface = _61_954.iface; admitted_iface = _61_954.admitted_iface}))
end
| _61_957 -> begin
(FStar_All.failwith "No more modules to pop")
end))

# 573 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let export_interface : FStar_Ident.lident  ->  env  ->  env = (fun m env -> (let sigelt_in_m = (fun se -> (match ((FStar_Absyn_Util.lids_of_sigelt se)) with
| l::_61_963 -> begin
(l.FStar_Ident.nsstr = m.FStar_Ident.str)
end
| _61_967 -> begin
false
end))
in (let sm = (sigmap env)
in (let env = (pop env)
in (let keys = (FStar_Util.smap_keys sm)
in (let sm' = (sigmap env)
in (let _61_990 = (FStar_All.pipe_right keys (FStar_List.iter (fun k -> (match ((FStar_Util.smap_try_find sm' k)) with
| Some (se, true) when (sigelt_in_m se) -> begin
(let _61_977 = (FStar_Util.smap_remove sm' k)
in (let se = (match (se) with
| FStar_Absyn_Syntax.Sig_val_decl (l, t, q, r) -> begin
FStar_Absyn_Syntax.Sig_val_decl ((l, t, (FStar_Absyn_Syntax.Assumption)::q, r))
end
| _61_986 -> begin
se
end)
in (FStar_Util.smap_add sm' k (se, false))))
end
| _61_989 -> begin
()
end))))
in env)))))))

# 595 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let finish_module_or_interface : env  ->  FStar_Absyn_Syntax.modul  ->  env = (fun env modul -> (let _61_994 = if (not (modul.FStar_Absyn_Syntax.is_interface)) then begin
(check_admits modul.FStar_Absyn_Syntax.name env)
end else begin
()
end
in (finish env modul)))

# 600 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let prepare_module_or_interface : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  (env * Prims.bool) = (fun intf admitted env mname -> (let prep = (fun env -> (let open_ns = if (FStar_Ident.lid_equals mname FStar_Absyn_Const.prims_lid) then begin
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
in (let _61_1003 = env
in {curmodule = Some (mname); modules = _61_1003.modules; open_namespaces = open_ns; modul_abbrevs = _61_1003.modul_abbrevs; sigaccum = _61_1003.sigaccum; localbindings = _61_1003.localbindings; recbindings = _61_1003.recbindings; phase = _61_1003.phase; sigmap = env.sigmap; default_result_effect = _61_1003.default_result_effect; iface = intf; admitted_iface = admitted})))
in (match ((FStar_All.pipe_right env.modules (FStar_Util.find_opt (fun _61_1008 -> (match (_61_1008) with
| (l, _61_1007) -> begin
(FStar_Ident.lid_equals l mname)
end))))) with
| None -> begin
((prep env), false)
end
| Some (_61_1011, m) -> begin
(let _61_1015 = if ((not (m.FStar_Absyn_Syntax.is_interface)) || intf) then begin
(let _163_722 = (let _163_721 = (let _163_720 = (FStar_Util.format1 "Duplicate module or interface name: %s" mname.FStar_Ident.str)
in (_163_720, (FStar_Ident.range_of_lid mname)))
in FStar_Absyn_Syntax.Error (_163_721))
in (Prims.raise _163_722))
end else begin
()
end
in (let _163_724 = (let _163_723 = (push env)
in (prep _163_723))
in (_163_724, true)))
end)))

# 617 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let enter_monad_scope : env  ->  FStar_Ident.ident  ->  env = (fun env mname -> (let curmod = (current_module env)
in (let mscope = (FStar_Ident.lid_of_ids (FStar_List.append curmod.FStar_Ident.ns ((curmod.FStar_Ident.ident)::(mname)::[])))
in (let _61_1021 = env
in {curmodule = Some (mscope); modules = _61_1021.modules; open_namespaces = (curmod)::env.open_namespaces; modul_abbrevs = _61_1021.modul_abbrevs; sigaccum = _61_1021.sigaccum; localbindings = _61_1021.localbindings; recbindings = _61_1021.recbindings; phase = _61_1021.phase; sigmap = _61_1021.sigmap; default_result_effect = _61_1021.default_result_effect; iface = _61_1021.iface; admitted_iface = _61_1021.admitted_iface}))))

# 624 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let exit_monad_scope : env  ->  env  ->  env = (fun env0 env -> (let _61_1025 = env
in {curmodule = env0.curmodule; modules = _61_1025.modules; open_namespaces = env0.open_namespaces; modul_abbrevs = _61_1025.modul_abbrevs; sigaccum = _61_1025.sigaccum; localbindings = _61_1025.localbindings; recbindings = _61_1025.recbindings; phase = _61_1025.phase; sigmap = _61_1025.sigmap; default_result_effect = _61_1025.default_result_effect; iface = _61_1025.iface; admitted_iface = _61_1025.admitted_iface}))

# 629 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

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
(let _163_739 = (FStar_Range.string_of_range r)
in (FStar_Util.format1 "(Possible clash with related name at %s)" _163_739))
end)
in (let _163_742 = (let _163_741 = (let _163_740 = (FStar_Util.format2 "Identifier not found: [%s] %s" (FStar_Ident.text_of_lid lid) msg)
in (_163_740, (FStar_Ident.range_of_lid lid)))
in FStar_Absyn_Syntax.Error (_163_741))
in (Prims.raise _163_742))))
end
| Some (r) -> begin
r
end))

# 643 "D:\\workspace\\universes\\FStar\\src\\parser\\dsenv.fs"

let fail_or2 = (fun lookup id -> (match ((lookup id)) with
| None -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (((Prims.strcat (Prims.strcat "Identifier not found [" id.FStar_Ident.idText) "]"), id.FStar_Ident.idRange))))
end
| Some (r) -> begin
r
end))




