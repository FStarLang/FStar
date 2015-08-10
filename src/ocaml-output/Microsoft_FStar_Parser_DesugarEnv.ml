
type binding =
| Binding_typ_var of Microsoft_FStar_Absyn_Syntax.ident
| Binding_var of Microsoft_FStar_Absyn_Syntax.ident
| Binding_let of Microsoft_FStar_Absyn_Syntax.lident
| Binding_tycon of Microsoft_FStar_Absyn_Syntax.lident

let is_Binding_typ_var = (fun ( _discr_ ) -> (match (_discr_) with
| Binding_typ_var (_) -> begin
true
end
| _ -> begin
false
end))

let is_Binding_var = (fun ( _discr_ ) -> (match (_discr_) with
| Binding_var (_) -> begin
true
end
| _ -> begin
false
end))

let is_Binding_let = (fun ( _discr_ ) -> (match (_discr_) with
| Binding_let (_) -> begin
true
end
| _ -> begin
false
end))

let is_Binding_tycon = (fun ( _discr_ ) -> (match (_discr_) with
| Binding_tycon (_) -> begin
true
end
| _ -> begin
false
end))

let ___Binding_typ_var____0 = (fun ( projectee ) -> (match (projectee) with
| Binding_typ_var (_41_18) -> begin
_41_18
end))

let ___Binding_var____0 = (fun ( projectee ) -> (match (projectee) with
| Binding_var (_41_21) -> begin
_41_21
end))

let ___Binding_let____0 = (fun ( projectee ) -> (match (projectee) with
| Binding_let (_41_24) -> begin
_41_24
end))

let ___Binding_tycon____0 = (fun ( projectee ) -> (match (projectee) with
| Binding_tycon (_41_27) -> begin
_41_27
end))

type kind_abbrev =
(Microsoft_FStar_Absyn_Syntax.lident * (Microsoft_FStar_Absyn_Syntax.btvdef, Microsoft_FStar_Absyn_Syntax.bvvdef) Support.Microsoft.FStar.Util.either list * Microsoft_FStar_Absyn_Syntax.knd)

type env =
{curmodule : Microsoft_FStar_Absyn_Syntax.lident option; modules : (Microsoft_FStar_Absyn_Syntax.lident * Microsoft_FStar_Absyn_Syntax.modul) list; open_namespaces : Microsoft_FStar_Absyn_Syntax.lident list; sigaccum : Microsoft_FStar_Absyn_Syntax.sigelts; localbindings : ((Microsoft_FStar_Absyn_Syntax.btvdef, Microsoft_FStar_Absyn_Syntax.bvvdef) Support.Microsoft.FStar.Util.either * binding) list; recbindings : binding list; phase : Microsoft_FStar_Parser_AST.level; sigmap : (Microsoft_FStar_Absyn_Syntax.sigelt * bool) Support.Microsoft.FStar.Util.smap list; default_result_effect : Microsoft_FStar_Absyn_Syntax.typ  ->  Support.Microsoft.FStar.Range.range  ->  Microsoft_FStar_Absyn_Syntax.comp; iface : bool; admitted_iface : bool}

let is_Mkenv = (fun ( _ ) -> (Support.All.failwith "Not yet implemented:is_Mkenv"))

let open_modules = (fun ( e ) -> e.modules)

let current_module = (fun ( env ) -> (match (env.curmodule) with
| None -> begin
(Support.All.failwith "Unset current module")
end
| Some (m) -> begin
m
end))

let qual = (fun ( lid ) ( id ) -> (let _112_111 = (Microsoft_FStar_Absyn_Syntax.lid_of_ids (Support.List.append lid.Microsoft_FStar_Absyn_Syntax.ns ((lid.Microsoft_FStar_Absyn_Syntax.ident)::(id)::[])))
in (Microsoft_FStar_Absyn_Util.set_lid_range _112_111 id.Microsoft_FStar_Absyn_Syntax.idRange)))

let qualify = (fun ( env ) ( id ) -> (let _112_116 = (current_module env)
in (qual _112_116 id)))

let qualify_lid = (fun ( env ) ( lid ) -> (let cur = (current_module env)
in (let _112_122 = (Microsoft_FStar_Absyn_Syntax.lid_of_ids (Support.List.append (Support.List.append (Support.List.append cur.Microsoft_FStar_Absyn_Syntax.ns ((cur.Microsoft_FStar_Absyn_Syntax.ident)::[])) lid.Microsoft_FStar_Absyn_Syntax.ns) ((lid.Microsoft_FStar_Absyn_Syntax.ident)::[])))
in (let _112_121 = (Microsoft_FStar_Absyn_Syntax.range_of_lid lid)
in (Microsoft_FStar_Absyn_Util.set_lid_range _112_122 _112_121)))))

let new_sigmap = (fun ( _41_52 ) -> (match (()) with
| () -> begin
(Support.Microsoft.FStar.Util.smap_create 100)
end))

let empty_env = (fun ( _41_53 ) -> (match (()) with
| () -> begin
(let _112_127 = (let _112_126 = (new_sigmap ())
in (_112_126)::[])
in {curmodule = None; modules = []; open_namespaces = []; sigaccum = []; localbindings = []; recbindings = []; phase = Microsoft_FStar_Parser_AST.Un; sigmap = _112_127; default_result_effect = Microsoft_FStar_Absyn_Util.ml_comp; iface = false; admitted_iface = false})
end))

let sigmap = (fun ( env ) -> (Support.List.hd env.sigmap))

let default_total = (fun ( env ) -> (let _41_56 = env
in {curmodule = _41_56.curmodule; modules = _41_56.modules; open_namespaces = _41_56.open_namespaces; sigaccum = _41_56.sigaccum; localbindings = _41_56.localbindings; recbindings = _41_56.recbindings; phase = _41_56.phase; sigmap = _41_56.sigmap; default_result_effect = (fun ( t ) ( _41_59 ) -> (Microsoft_FStar_Absyn_Syntax.mk_Total t)); iface = _41_56.iface; admitted_iface = _41_56.admitted_iface}))

let default_ml = (fun ( env ) -> (let _41_62 = env
in {curmodule = _41_62.curmodule; modules = _41_62.modules; open_namespaces = _41_62.open_namespaces; sigaccum = _41_62.sigaccum; localbindings = _41_62.localbindings; recbindings = _41_62.recbindings; phase = _41_62.phase; sigmap = _41_62.sigmap; default_result_effect = Microsoft_FStar_Absyn_Util.ml_comp; iface = _41_62.iface; admitted_iface = _41_62.admitted_iface}))

let range_of_binding = (fun ( _41_1 ) -> (match (_41_1) with
| (Binding_typ_var (id)) | (Binding_var (id)) -> begin
id.Microsoft_FStar_Absyn_Syntax.idRange
end
| (Binding_let (lid)) | (Binding_tycon (lid)) -> begin
(Microsoft_FStar_Absyn_Syntax.range_of_lid lid)
end))

let try_lookup_typ_var = (fun ( env ) ( id ) -> (let fopt = (Support.List.tryFind (fun ( _41_76 ) -> (match (_41_76) with
| (_41_74, b) -> begin
(match (b) with
| (Binding_typ_var (id')) | (Binding_var (id')) -> begin
(id.Microsoft_FStar_Absyn_Syntax.idText = id'.Microsoft_FStar_Absyn_Syntax.idText)
end
| _41_81 -> begin
false
end)
end)) env.localbindings)
in (match (fopt) with
| Some ((Support.Microsoft.FStar.Util.Inl (bvd), Binding_typ_var (_41_86))) -> begin
(let _112_144 = (let _112_143 = (Microsoft_FStar_Absyn_Util.set_bvd_range bvd id.Microsoft_FStar_Absyn_Syntax.idRange)
in (Microsoft_FStar_Absyn_Util.bvd_to_typ _112_143 Microsoft_FStar_Absyn_Syntax.kun))
in Some (_112_144))
end
| _41_91 -> begin
None
end)))

let resolve_in_open_namespaces = (fun ( env ) ( lid ) ( finder ) -> (let aux = (fun ( namespaces ) -> (match ((finder lid)) with
| Some (r) -> begin
Some (r)
end
| _41_101 -> begin
(let ids = (Microsoft_FStar_Absyn_Syntax.ids_of_lid lid)
in (Support.Microsoft.FStar.Util.find_map namespaces (fun ( ns ) -> (let full_name = (let _112_159 = (let _112_158 = (Microsoft_FStar_Absyn_Syntax.ids_of_lid ns)
in (Support.List.append _112_158 ids))
in (Microsoft_FStar_Absyn_Syntax.lid_of_ids _112_159))
in (finder full_name)))))
end))
in (let _112_161 = (let _112_160 = (current_module env)
in (_112_160)::env.open_namespaces)
in (aux _112_161))))

let unmangleMap = (("op_ColonColon", "Cons"))::(("not", "op_Negation"))::[]

let unmangleOpName = (fun ( id ) -> (Support.Microsoft.FStar.Util.find_map unmangleMap (fun ( _41_108 ) -> (match (_41_108) with
| (x, y) -> begin
(match ((id.Microsoft_FStar_Absyn_Syntax.idText = x)) with
| true -> begin
(let _112_165 = (Microsoft_FStar_Absyn_Syntax.lid_of_path (("Prims")::(y)::[]) id.Microsoft_FStar_Absyn_Syntax.idRange)
in Some (_112_165))
end
| false -> begin
None
end)
end))))

let try_lookup_id' = (fun ( env ) ( id ) -> (match ((unmangleOpName id)) with
| Some (l) -> begin
(let _112_173 = (let _112_172 = (let _112_171 = (let _112_170 = (Microsoft_FStar_Absyn_Util.fv l)
in (_112_170, None))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_fvar _112_171 None id.Microsoft_FStar_Absyn_Syntax.idRange))
in (l, _112_172))
in Some (_112_173))
end
| _41_114 -> begin
(let found = (Support.Microsoft.FStar.Util.find_map env.localbindings (fun ( _41_2 ) -> (match (_41_2) with
| (Support.Microsoft.FStar.Util.Inl (_41_117), Binding_typ_var (id')) when (id'.Microsoft_FStar_Absyn_Syntax.idText = id.Microsoft_FStar_Absyn_Syntax.idText) -> begin
Some (Support.Microsoft.FStar.Util.Inl (()))
end
| (Support.Microsoft.FStar.Util.Inr (bvd), Binding_var (id')) when (id'.Microsoft_FStar_Absyn_Syntax.idText = id.Microsoft_FStar_Absyn_Syntax.idText) -> begin
(let _112_179 = (let _112_178 = (let _112_177 = (Microsoft_FStar_Absyn_Syntax.lid_of_ids ((id')::[]))
in (let _112_176 = (let _112_175 = (Microsoft_FStar_Absyn_Util.set_bvd_range bvd id.Microsoft_FStar_Absyn_Syntax.idRange)
in (Microsoft_FStar_Absyn_Util.bvd_to_exp _112_175 Microsoft_FStar_Absyn_Syntax.tun))
in (_112_177, _112_176)))
in Support.Microsoft.FStar.Util.Inr (_112_178))
in Some (_112_179))
end
| _41_128 -> begin
None
end)))
in (match (found) with
| Some (Support.Microsoft.FStar.Util.Inr (x)) -> begin
Some (x)
end
| _41_134 -> begin
None
end))
end))

let try_lookup_id = (fun ( env ) ( id ) -> (match ((try_lookup_id' env id)) with
| Some ((_41_138, e)) -> begin
Some (e)
end
| None -> begin
None
end))

type occurrence =
| OSig of Microsoft_FStar_Absyn_Syntax.sigelt
| OLet of Microsoft_FStar_Absyn_Syntax.lident
| ORec of Microsoft_FStar_Absyn_Syntax.lident

let is_OSig = (fun ( _discr_ ) -> (match (_discr_) with
| OSig (_) -> begin
true
end
| _ -> begin
false
end))

let is_OLet = (fun ( _discr_ ) -> (match (_discr_) with
| OLet (_) -> begin
true
end
| _ -> begin
false
end))

let is_ORec = (fun ( _discr_ ) -> (match (_discr_) with
| ORec (_) -> begin
true
end
| _ -> begin
false
end))

let ___OSig____0 = (fun ( projectee ) -> (match (projectee) with
| OSig (_41_145) -> begin
_41_145
end))

let ___OLet____0 = (fun ( projectee ) -> (match (projectee) with
| OLet (_41_148) -> begin
_41_148
end))

let ___ORec____0 = (fun ( projectee ) -> (match (projectee) with
| ORec (_41_151) -> begin
_41_151
end))

let range_of_occurrence = (fun ( _41_3 ) -> (match (_41_3) with
| (OLet (l)) | (ORec (l)) -> begin
(Microsoft_FStar_Absyn_Syntax.range_of_lid l)
end
| OSig (se) -> begin
(Microsoft_FStar_Absyn_Util.range_of_sigelt se)
end))

type foundname =
| Exp_name of (occurrence * Microsoft_FStar_Absyn_Syntax.exp)
| Typ_name of (occurrence * Microsoft_FStar_Absyn_Syntax.typ)
| Eff_name of (occurrence * Microsoft_FStar_Absyn_Syntax.lident)
| Knd_name of (occurrence * Microsoft_FStar_Absyn_Syntax.lident)

let is_Exp_name = (fun ( _discr_ ) -> (match (_discr_) with
| Exp_name (_) -> begin
true
end
| _ -> begin
false
end))

let is_Typ_name = (fun ( _discr_ ) -> (match (_discr_) with
| Typ_name (_) -> begin
true
end
| _ -> begin
false
end))

let is_Eff_name = (fun ( _discr_ ) -> (match (_discr_) with
| Eff_name (_) -> begin
true
end
| _ -> begin
false
end))

let is_Knd_name = (fun ( _discr_ ) -> (match (_discr_) with
| Knd_name (_) -> begin
true
end
| _ -> begin
false
end))

let ___Exp_name____0 = (fun ( projectee ) -> (match (projectee) with
| Exp_name (_41_160) -> begin
_41_160
end))

let ___Typ_name____0 = (fun ( projectee ) -> (match (projectee) with
| Typ_name (_41_163) -> begin
_41_163
end))

let ___Eff_name____0 = (fun ( projectee ) -> (match (projectee) with
| Eff_name (_41_166) -> begin
_41_166
end))

let ___Knd_name____0 = (fun ( projectee ) -> (match (projectee) with
| Knd_name (_41_169) -> begin
_41_169
end))

let fv_qual_of_se = (fun ( _41_5 ) -> (match (_41_5) with
| Microsoft_FStar_Absyn_Syntax.Sig_datacon ((_41_172, _41_174, (l, _41_177, _41_179), quals, _41_183, _41_185)) -> begin
(let qopt = (Support.Microsoft.FStar.Util.find_map quals (fun ( _41_4 ) -> (match (_41_4) with
| Microsoft_FStar_Absyn_Syntax.RecordConstructor (fs) -> begin
Some (Microsoft_FStar_Absyn_Syntax.Record_ctor ((l, fs)))
end
| _41_192 -> begin
None
end)))
in (match (qopt) with
| None -> begin
Some (Microsoft_FStar_Absyn_Syntax.Data_ctor)
end
| x -> begin
x
end))
end
| Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((_41_197, _41_199, quals, _41_202)) -> begin
None
end
| _41_206 -> begin
None
end))

let try_lookup_name = (fun ( any_val ) ( exclude_interf ) ( env ) ( lid ) -> (let find_in_sig = (fun ( lid ) -> (match ((let _112_297 = (sigmap env)
in (Support.Microsoft.FStar.Util.smap_try_find _112_297 lid.Microsoft_FStar_Absyn_Syntax.str))) with
| Some ((_41_214, true)) when exclude_interf -> begin
None
end
| None -> begin
None
end
| Some ((se, _41_221)) -> begin
(match (se) with
| (Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_tycon (_)) -> begin
(let _112_300 = (let _112_299 = (let _112_298 = (Microsoft_FStar_Absyn_Util.ftv lid Microsoft_FStar_Absyn_Syntax.kun)
in (OSig (se), _112_298))
in Typ_name (_112_299))
in Some (_112_300))
end
| Microsoft_FStar_Absyn_Syntax.Sig_kind_abbrev (_41_231) -> begin
Some (Knd_name ((OSig (se), lid)))
end
| Microsoft_FStar_Absyn_Syntax.Sig_new_effect ((ne, _41_235)) -> begin
(let _112_304 = (let _112_303 = (let _112_302 = (let _112_301 = (Microsoft_FStar_Absyn_Syntax.range_of_lid lid)
in (Microsoft_FStar_Absyn_Util.set_lid_range ne.Microsoft_FStar_Absyn_Syntax.mname _112_301))
in (OSig (se), _112_302))
in Eff_name (_112_303))
in Some (_112_304))
end
| Microsoft_FStar_Absyn_Syntax.Sig_effect_abbrev (_41_239) -> begin
Some (Eff_name ((OSig (se), lid)))
end
| Microsoft_FStar_Absyn_Syntax.Sig_datacon (_41_242) -> begin
(let _112_309 = (let _112_308 = (let _112_307 = (let _112_306 = (fv_qual_of_se se)
in (let _112_305 = (Microsoft_FStar_Absyn_Syntax.range_of_lid lid)
in (Microsoft_FStar_Absyn_Util.fvar _112_306 lid _112_305)))
in (OSig (se), _112_307))
in Exp_name (_112_308))
in Some (_112_309))
end
| Microsoft_FStar_Absyn_Syntax.Sig_let (_41_245) -> begin
(let _112_313 = (let _112_312 = (let _112_311 = (let _112_310 = (Microsoft_FStar_Absyn_Syntax.range_of_lid lid)
in (Microsoft_FStar_Absyn_Util.fvar None lid _112_310))
in (OSig (se), _112_311))
in Exp_name (_112_312))
in Some (_112_313))
end
| Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((_41_248, _41_250, quals, _41_253)) -> begin
(match ((any_val || (Support.All.pipe_right quals (Support.Microsoft.FStar.Util.for_some (fun ( _41_6 ) -> (match (_41_6) with
| Microsoft_FStar_Absyn_Syntax.Assumption -> begin
true
end
| _41_259 -> begin
false
end)))))) with
| true -> begin
(let _112_319 = (let _112_318 = (let _112_317 = (let _112_316 = (fv_qual_of_se se)
in (let _112_315 = (Microsoft_FStar_Absyn_Syntax.range_of_lid lid)
in (Microsoft_FStar_Absyn_Util.fvar _112_316 lid _112_315)))
in (OSig (se), _112_317))
in Exp_name (_112_318))
in Some (_112_319))
end
| false -> begin
None
end)
end
| _41_261 -> begin
None
end)
end))
in (let found_id = (match (lid.Microsoft_FStar_Absyn_Syntax.ns) with
| [] -> begin
(match ((try_lookup_id' env lid.Microsoft_FStar_Absyn_Syntax.ident)) with
| Some ((lid, e)) -> begin
Some (Exp_name ((OLet (lid), e)))
end
| None -> begin
(let recname = (qualify env lid.Microsoft_FStar_Absyn_Syntax.ident)
in (Support.Microsoft.FStar.Util.find_map env.recbindings (fun ( _41_7 ) -> (match (_41_7) with
| Binding_let (l) when (Microsoft_FStar_Absyn_Syntax.lid_equals l recname) -> begin
(let _112_324 = (let _112_323 = (let _112_322 = (let _112_321 = (Microsoft_FStar_Absyn_Syntax.range_of_lid recname)
in (Microsoft_FStar_Absyn_Util.fvar None recname _112_321))
in (ORec (l), _112_322))
in Exp_name (_112_323))
in Some (_112_324))
end
| Binding_tycon (l) when (Microsoft_FStar_Absyn_Syntax.lid_equals l recname) -> begin
(let _112_327 = (let _112_326 = (let _112_325 = (Microsoft_FStar_Absyn_Util.ftv recname Microsoft_FStar_Absyn_Syntax.kun)
in (ORec (l), _112_325))
in Typ_name (_112_326))
in Some (_112_327))
end
| _41_275 -> begin
None
end))))
end)
end
| _41_277 -> begin
None
end)
in (match (found_id) with
| Some (_41_280) -> begin
found_id
end
| _41_283 -> begin
(resolve_in_open_namespaces env lid find_in_sig)
end))))

let try_lookup_typ_name' = (fun ( exclude_interf ) ( env ) ( lid ) -> (match ((try_lookup_name true exclude_interf env lid)) with
| Some (Typ_name ((_41_288, t))) -> begin
Some (t)
end
| Some (Eff_name ((_41_294, l))) -> begin
(let _112_334 = (Microsoft_FStar_Absyn_Util.ftv l Microsoft_FStar_Absyn_Syntax.mk_Kind_unknown)
in Some (_112_334))
end
| _41_300 -> begin
None
end))

let try_lookup_typ_name = (fun ( env ) ( l ) -> (try_lookup_typ_name' (not (env.iface)) env l))

let try_lookup_effect_name' = (fun ( exclude_interf ) ( env ) ( lid ) -> (match ((try_lookup_name true exclude_interf env lid)) with
| Some (Eff_name ((o, l))) -> begin
Some ((o, l))
end
| _41_312 -> begin
None
end))

let try_lookup_effect_name = (fun ( env ) ( l ) -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some ((o, l)) -> begin
Some (l)
end
| _41_320 -> begin
None
end))

let try_lookup_effect_defn = (fun ( env ) ( l ) -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some ((OSig (Microsoft_FStar_Absyn_Syntax.Sig_new_effect ((ne, _41_325))), _41_330)) -> begin
Some (ne)
end
| _41_334 -> begin
None
end))

let is_effect_name = (fun ( env ) ( lid ) -> (match ((try_lookup_effect_name env lid)) with
| None -> begin
false
end
| Some (_41_339) -> begin
true
end))

let try_resolve_typ_abbrev = (fun ( env ) ( lid ) -> (let find_in_sig = (fun ( lid ) -> (match ((let _112_363 = (sigmap env)
in (Support.Microsoft.FStar.Util.smap_try_find _112_363 lid.Microsoft_FStar_Absyn_Syntax.str))) with
| Some ((Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev ((lid, tps, k, def, _41_350, _41_352)), _41_356)) -> begin
(let t = (let _112_366 = (let _112_365 = (let _112_364 = (Microsoft_FStar_Absyn_Util.close_with_lam tps def)
in (_112_364, lid))
in Microsoft_FStar_Absyn_Syntax.Meta_named (_112_365))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta _112_366))
in Some (t))
end
| _41_361 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))

let lookup_letbinding_quals = (fun ( env ) ( lid ) -> (let find_in_sig = (fun ( lid ) -> (match ((let _112_373 = (sigmap env)
in (Support.Microsoft.FStar.Util.smap_try_find _112_373 lid.Microsoft_FStar_Absyn_Syntax.str))) with
| Some ((Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((lid, _41_368, quals, _41_371)), _41_375)) -> begin
Some (quals)
end
| _41_379 -> begin
None
end))
in (match ((resolve_in_open_namespaces env lid find_in_sig)) with
| Some (quals) -> begin
quals
end
| _41_383 -> begin
[]
end)))

let try_lookup_module = (fun ( env ) ( path ) -> (match ((Support.List.tryFind (fun ( _41_388 ) -> (match (_41_388) with
| (mlid, modul) -> begin
((Microsoft_FStar_Absyn_Syntax.path_of_lid mlid) = path)
end)) env.modules)) with
| Some ((_41_390, modul)) -> begin
Some (modul)
end
| None -> begin
None
end))

let try_lookup_let = (fun ( env ) ( lid ) -> (let find_in_sig = (fun ( lid ) -> (match ((let _112_385 = (sigmap env)
in (Support.Microsoft.FStar.Util.smap_try_find _112_385 lid.Microsoft_FStar_Absyn_Syntax.str))) with
| Some ((Microsoft_FStar_Absyn_Syntax.Sig_let (_41_400), _41_403)) -> begin
(let _112_387 = (let _112_386 = (Microsoft_FStar_Absyn_Syntax.range_of_lid lid)
in (Microsoft_FStar_Absyn_Util.fvar None lid _112_386))
in Some (_112_387))
end
| _41_407 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))

let try_lookup_lid' = (fun ( any_val ) ( exclude_interf ) ( env ) ( lid ) -> (match ((try_lookup_name any_val exclude_interf env lid)) with
| Some (Exp_name ((_41_413, e))) -> begin
Some (e)
end
| _41_419 -> begin
None
end))

let try_lookup_lid = (fun ( env ) ( l ) -> (try_lookup_lid' env.iface false env l))

let try_lookup_datacon = (fun ( env ) ( lid ) -> (let find_in_sig = (fun ( lid ) -> (match ((let _112_406 = (sigmap env)
in (Support.Microsoft.FStar.Util.smap_try_find _112_406 lid.Microsoft_FStar_Absyn_Syntax.str))) with
| Some ((Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((_41_427, _41_429, quals, _41_432)), _41_436)) -> begin
(match ((Support.All.pipe_right quals (Support.Microsoft.FStar.Util.for_some (fun ( _41_8 ) -> (match (_41_8) with
| Microsoft_FStar_Absyn_Syntax.Assumption -> begin
true
end
| _41_442 -> begin
false
end))))) with
| true -> begin
(let _112_408 = (Microsoft_FStar_Absyn_Util.fv lid)
in Some (_112_408))
end
| false -> begin
None
end)
end
| Some ((Microsoft_FStar_Absyn_Syntax.Sig_datacon (_41_444), _41_447)) -> begin
(let _112_409 = (Microsoft_FStar_Absyn_Util.fv lid)
in Some (_112_409))
end
| _41_451 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))

let find_all_datacons = (fun ( env ) ( lid ) -> (let find_in_sig = (fun ( lid ) -> (match ((let _112_416 = (sigmap env)
in (Support.Microsoft.FStar.Util.smap_try_find _112_416 lid.Microsoft_FStar_Absyn_Syntax.str))) with
| Some ((Microsoft_FStar_Absyn_Syntax.Sig_tycon ((_41_457, _41_459, _41_461, _41_463, datas, _41_466, _41_468)), _41_472)) -> begin
Some (datas)
end
| _41_476 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))

type record =
{typename : Microsoft_FStar_Absyn_Syntax.lident; constrname : Microsoft_FStar_Absyn_Syntax.lident; parms : Microsoft_FStar_Absyn_Syntax.binders; fields : (Microsoft_FStar_Absyn_Syntax.fieldname * Microsoft_FStar_Absyn_Syntax.typ) list}

let is_Mkrecord = (fun ( _ ) -> (Support.All.failwith "Not yet implemented:is_Mkrecord"))

let record_cache = (Support.Microsoft.FStar.Util.mk_ref [])

let extract_record = (fun ( e ) ( _41_12 ) -> (match (_41_12) with
| Microsoft_FStar_Absyn_Syntax.Sig_bundle ((sigs, _41_486, _41_488, _41_490)) -> begin
(let is_rec = (Support.Microsoft.FStar.Util.for_some (fun ( _41_9 ) -> (match (_41_9) with
| (Microsoft_FStar_Absyn_Syntax.RecordType (_)) | (Microsoft_FStar_Absyn_Syntax.RecordConstructor (_)) -> begin
true
end
| _41_501 -> begin
false
end)))
in (let find_dc = (fun ( dc ) -> (Support.All.pipe_right sigs (Support.Microsoft.FStar.Util.find_opt (fun ( _41_10 ) -> (match (_41_10) with
| Microsoft_FStar_Absyn_Syntax.Sig_datacon ((lid, _41_508, _41_510, _41_512, _41_514, _41_516)) -> begin
(Microsoft_FStar_Absyn_Syntax.lid_equals dc lid)
end
| _41_520 -> begin
false
end)))))
in (Support.All.pipe_right sigs (Support.List.iter (fun ( _41_11 ) -> (match (_41_11) with
| Microsoft_FStar_Absyn_Syntax.Sig_tycon ((typename, parms, _41_525, _41_527, dc::[], tags, _41_532)) -> begin
(match ((is_rec tags)) with
| true -> begin
(match ((let _112_440 = (find_dc dc)
in (Support.All.pipe_left Support.Microsoft.FStar.Util.must _112_440))) with
| Microsoft_FStar_Absyn_Syntax.Sig_datacon ((constrname, t, _41_538, _41_540, _41_542, _41_544)) -> begin
(let formals = (match ((Microsoft_FStar_Absyn_Util.function_formals t)) with
| Some ((x, _41_549)) -> begin
x
end
| _41_553 -> begin
[]
end)
in (let fields = (Support.All.pipe_right formals (Support.List.collect (fun ( b ) -> (match (b) with
| (Support.Microsoft.FStar.Util.Inr (x), q) -> begin
(match (((Microsoft_FStar_Absyn_Syntax.is_null_binder b) || (q = Some (Microsoft_FStar_Absyn_Syntax.Implicit)))) with
| true -> begin
[]
end
| false -> begin
(let _112_444 = (let _112_443 = (let _112_442 = (Microsoft_FStar_Absyn_Util.unmangle_field_name x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ppname)
in (qual constrname _112_442))
in (_112_443, x.Microsoft_FStar_Absyn_Syntax.sort))
in (_112_444)::[])
end)
end
| _41_561 -> begin
[]
end))))
in (let record = {typename = typename; constrname = constrname; parms = parms; fields = fields}
in (let _112_446 = (let _112_445 = (Support.ST.read record_cache)
in (record)::_112_445)
in (Support.ST.op_Colon_Equals record_cache _112_446)))))
end
| _41_565 -> begin
()
end)
end
| false -> begin
()
end)
end
| _41_567 -> begin
()
end))))))
end
| _41_569 -> begin
()
end))

let try_lookup_record_by_field_name = (fun ( env ) ( fieldname ) -> (let maybe_add_constrname = (fun ( ns ) ( c ) -> (let rec aux = (fun ( ns ) -> (match (ns) with
| [] -> begin
(c)::[]
end
| c'::[] -> begin
(match ((c'.Microsoft_FStar_Absyn_Syntax.idText = c.Microsoft_FStar_Absyn_Syntax.idText)) with
| true -> begin
(c)::[]
end
| false -> begin
(c')::(c)::[]
end)
end
| hd::tl -> begin
(let _112_457 = (aux tl)
in (hd)::_112_457)
end))
in (aux ns)))
in (let find_in_cache = (fun ( fieldname ) -> (let _41_587 = (fieldname.Microsoft_FStar_Absyn_Syntax.ns, fieldname.Microsoft_FStar_Absyn_Syntax.ident)
in (match (_41_587) with
| (ns, fieldname) -> begin
(let _112_462 = (Support.ST.read record_cache)
in (Support.Microsoft.FStar.Util.find_map _112_462 (fun ( record ) -> (let constrname = record.constrname.Microsoft_FStar_Absyn_Syntax.ident
in (let ns = (maybe_add_constrname ns constrname)
in (let fname = (Microsoft_FStar_Absyn_Syntax.lid_of_ids (Support.List.append ns ((fieldname)::[])))
in (Support.Microsoft.FStar.Util.find_map record.fields (fun ( _41_595 ) -> (match (_41_595) with
| (f, _41_594) -> begin
(match ((Microsoft_FStar_Absyn_Syntax.lid_equals fname f)) with
| true -> begin
Some ((record, fname))
end
| false -> begin
None
end)
end)))))))))
end)))
in (resolve_in_open_namespaces env fieldname find_in_cache))))

let qualify_field_to_record = (fun ( env ) ( recd ) ( f ) -> (let qualify = (fun ( fieldname ) -> (let _41_603 = (fieldname.Microsoft_FStar_Absyn_Syntax.ns, fieldname.Microsoft_FStar_Absyn_Syntax.ident)
in (match (_41_603) with
| (ns, fieldname) -> begin
(let constrname = recd.constrname.Microsoft_FStar_Absyn_Syntax.ident
in (let fname = (Microsoft_FStar_Absyn_Syntax.lid_of_ids (Support.List.append (Support.List.append ns ((constrname)::[])) ((fieldname)::[])))
in (Support.Microsoft.FStar.Util.find_map recd.fields (fun ( _41_609 ) -> (match (_41_609) with
| (f, _41_608) -> begin
(match ((Microsoft_FStar_Absyn_Syntax.lid_equals fname f)) with
| true -> begin
Some (fname)
end
| false -> begin
None
end)
end)))))
end)))
in (resolve_in_open_namespaces env f qualify)))

let find_kind_abbrev = (fun ( env ) ( l ) -> (match ((try_lookup_name true (not (env.iface)) env l)) with
| Some (Knd_name ((_41_613, l))) -> begin
Some (l)
end
| _41_619 -> begin
None
end))

let is_kind_abbrev = (fun ( env ) ( l ) -> (match ((find_kind_abbrev env l)) with
| None -> begin
false
end
| Some (_41_624) -> begin
true
end))

let unique_name = (fun ( any_val ) ( exclude_if ) ( env ) ( lid ) -> (match ((try_lookup_lid' any_val exclude_if env lid)) with
| None -> begin
(match ((find_kind_abbrev env lid)) with
| None -> begin
true
end
| Some (_41_633) -> begin
false
end)
end
| Some (_41_636) -> begin
false
end))

let unique_typ_name = (fun ( env ) ( lid ) -> (match ((try_lookup_typ_name' true env lid)) with
| None -> begin
true
end
| Some (a) -> begin
false
end))

let unique = (fun ( any_val ) ( exclude_if ) ( env ) ( lid ) -> (let this_env = (let _41_647 = env
in {curmodule = _41_647.curmodule; modules = _41_647.modules; open_namespaces = []; sigaccum = _41_647.sigaccum; localbindings = _41_647.localbindings; recbindings = _41_647.recbindings; phase = _41_647.phase; sigmap = _41_647.sigmap; default_result_effect = _41_647.default_result_effect; iface = _41_647.iface; admitted_iface = _41_647.admitted_iface})
in ((unique_name any_val exclude_if this_env lid) && (unique_typ_name this_env lid))))

let gen_bvd = (fun ( _41_13 ) -> (match (_41_13) with
| Binding_typ_var (id) -> begin
(let _112_503 = (let _112_502 = (let _112_501 = (Microsoft_FStar_Absyn_Util.genident (Some (id.Microsoft_FStar_Absyn_Syntax.idRange)))
in (id, _112_501))
in (Microsoft_FStar_Absyn_Util.mkbvd _112_502))
in Support.Microsoft.FStar.Util.Inl (_112_503))
end
| Binding_var (id) -> begin
(let _112_506 = (let _112_505 = (let _112_504 = (Microsoft_FStar_Absyn_Util.genident (Some (id.Microsoft_FStar_Absyn_Syntax.idRange)))
in (id, _112_504))
in (Microsoft_FStar_Absyn_Util.mkbvd _112_505))
in Support.Microsoft.FStar.Util.Inr (_112_506))
end
| _41_656 -> begin
(Support.All.failwith "Tried to generate a bound variable for a type constructor")
end))

let push_bvvdef = (fun ( env ) ( x ) -> (let b = Binding_var (x.Microsoft_FStar_Absyn_Syntax.ppname)
in (let _41_660 = env
in {curmodule = _41_660.curmodule; modules = _41_660.modules; open_namespaces = _41_660.open_namespaces; sigaccum = _41_660.sigaccum; localbindings = ((Support.Microsoft.FStar.Util.Inr (x), b))::env.localbindings; recbindings = _41_660.recbindings; phase = _41_660.phase; sigmap = _41_660.sigmap; default_result_effect = _41_660.default_result_effect; iface = _41_660.iface; admitted_iface = _41_660.admitted_iface})))

let push_btvdef = (fun ( env ) ( x ) -> (let b = Binding_typ_var (x.Microsoft_FStar_Absyn_Syntax.ppname)
in (let _41_665 = env
in {curmodule = _41_665.curmodule; modules = _41_665.modules; open_namespaces = _41_665.open_namespaces; sigaccum = _41_665.sigaccum; localbindings = ((Support.Microsoft.FStar.Util.Inl (x), b))::env.localbindings; recbindings = _41_665.recbindings; phase = _41_665.phase; sigmap = _41_665.sigmap; default_result_effect = _41_665.default_result_effect; iface = _41_665.iface; admitted_iface = _41_665.admitted_iface})))

let push_local_binding = (fun ( env ) ( b ) -> (let bvd = (gen_bvd b)
in ((let _41_670 = env
in {curmodule = _41_670.curmodule; modules = _41_670.modules; open_namespaces = _41_670.open_namespaces; sigaccum = _41_670.sigaccum; localbindings = ((bvd, b))::env.localbindings; recbindings = _41_670.recbindings; phase = _41_670.phase; sigmap = _41_670.sigmap; default_result_effect = _41_670.default_result_effect; iface = _41_670.iface; admitted_iface = _41_670.admitted_iface}), bvd)))

let push_local_tbinding = (fun ( env ) ( a ) -> (match ((push_local_binding env (Binding_typ_var (a)))) with
| (env, Support.Microsoft.FStar.Util.Inl (x)) -> begin
(env, x)
end
| _41_679 -> begin
(Support.All.failwith "impossible")
end))

let push_local_vbinding = (fun ( env ) ( b ) -> (match ((push_local_binding env (Binding_var (b)))) with
| (env, Support.Microsoft.FStar.Util.Inr (x)) -> begin
(env, x)
end
| _41_687 -> begin
(Support.All.failwith "impossible")
end))

let push_rec_binding = (fun ( env ) ( b ) -> (match (b) with
| (Binding_let (lid)) | (Binding_tycon (lid)) -> begin
(match ((unique false true env lid)) with
| true -> begin
(let _41_693 = env
in {curmodule = _41_693.curmodule; modules = _41_693.modules; open_namespaces = _41_693.open_namespaces; sigaccum = _41_693.sigaccum; localbindings = _41_693.localbindings; recbindings = (b)::env.recbindings; phase = _41_693.phase; sigmap = _41_693.sigmap; default_result_effect = _41_693.default_result_effect; iface = _41_693.iface; admitted_iface = _41_693.admitted_iface})
end
| false -> begin
(let _112_533 = (let _112_532 = (let _112_531 = (Microsoft_FStar_Absyn_Syntax.range_of_lid lid)
in ((Support.String.strcat "Duplicate top-level names " lid.Microsoft_FStar_Absyn_Syntax.str), _112_531))
in Microsoft_FStar_Absyn_Syntax.Error (_112_532))
in (raise (_112_533)))
end)
end
| _41_696 -> begin
(Support.All.failwith "Unexpected rec_binding")
end))

let push_sigelt = (fun ( env ) ( s ) -> (let err = (fun ( l ) -> (let sopt = (let _112_540 = (sigmap env)
in (Support.Microsoft.FStar.Util.smap_try_find _112_540 l.Microsoft_FStar_Absyn_Syntax.str))
in (let r = (match (sopt) with
| Some ((se, _41_704)) -> begin
(match ((let _112_541 = (Microsoft_FStar_Absyn_Util.lids_of_sigelt se)
in (Support.Microsoft.FStar.Util.find_opt (Microsoft_FStar_Absyn_Syntax.lid_equals l) _112_541))) with
| Some (l) -> begin
(let _112_542 = (Microsoft_FStar_Absyn_Syntax.range_of_lid l)
in (Support.All.pipe_left Support.Microsoft.FStar.Range.string_of_range _112_542))
end
| None -> begin
"<unknown>"
end)
end
| None -> begin
"<unknown>"
end)
in (let _112_547 = (let _112_546 = (let _112_545 = (let _112_543 = (Microsoft_FStar_Absyn_Syntax.text_of_lid l)
in (Support.Microsoft.FStar.Util.format2 "Duplicate top-level names [%s]; previously declared at %s" _112_543 r))
in (let _112_544 = (Microsoft_FStar_Absyn_Syntax.range_of_lid l)
in (_112_545, _112_544)))
in Microsoft_FStar_Absyn_Syntax.Error (_112_546))
in (raise (_112_547))))))
in (let env = (let _41_722 = (match (s) with
| Microsoft_FStar_Absyn_Syntax.Sig_let (_41_713) -> begin
(false, true)
end
| Microsoft_FStar_Absyn_Syntax.Sig_bundle (_41_716) -> begin
(true, true)
end
| _41_719 -> begin
(false, false)
end)
in (match (_41_722) with
| (any_val, exclude_if) -> begin
(let lids = (Microsoft_FStar_Absyn_Util.lids_of_sigelt s)
in (match ((Support.Microsoft.FStar.Util.find_map lids (fun ( l ) -> (match ((not ((unique any_val exclude_if env l)))) with
| true -> begin
Some (l)
end
| false -> begin
None
end)))) with
| None -> begin
(let _41_726 = (extract_record env s)
in (let _41_728 = env
in {curmodule = _41_728.curmodule; modules = _41_728.modules; open_namespaces = _41_728.open_namespaces; sigaccum = (s)::env.sigaccum; localbindings = _41_728.localbindings; recbindings = _41_728.recbindings; phase = _41_728.phase; sigmap = _41_728.sigmap; default_result_effect = _41_728.default_result_effect; iface = _41_728.iface; admitted_iface = _41_728.admitted_iface}))
end
| Some (l) -> begin
(err l)
end))
end))
in (let _41_747 = (match (s) with
| Microsoft_FStar_Absyn_Syntax.Sig_bundle ((ses, _41_735, _41_737, _41_739)) -> begin
(let _112_551 = (Support.List.map (fun ( se ) -> (let _112_550 = (Microsoft_FStar_Absyn_Util.lids_of_sigelt se)
in (_112_550, se))) ses)
in (env, _112_551))
end
| _41_744 -> begin
(let _112_554 = (let _112_553 = (let _112_552 = (Microsoft_FStar_Absyn_Util.lids_of_sigelt s)
in (_112_552, s))
in (_112_553)::[])
in (env, _112_554))
end)
in (match (_41_747) with
| (env, lss) -> begin
(let _41_752 = (Support.All.pipe_right lss (Support.List.iter (fun ( _41_750 ) -> (match (_41_750) with
| (lids, se) -> begin
(Support.All.pipe_right lids (Support.List.iter (fun ( lid ) -> (let _112_557 = (sigmap env)
in (Support.Microsoft.FStar.Util.smap_add _112_557 lid.Microsoft_FStar_Absyn_Syntax.str (se, (env.iface && (not (env.admitted_iface)))))))))
end))))
in env)
end)))))

let push_namespace = (fun ( env ) ( lid ) -> (let _41_756 = env
in {curmodule = _41_756.curmodule; modules = _41_756.modules; open_namespaces = (lid)::env.open_namespaces; sigaccum = _41_756.sigaccum; localbindings = _41_756.localbindings; recbindings = _41_756.recbindings; phase = _41_756.phase; sigmap = _41_756.sigmap; default_result_effect = _41_756.default_result_effect; iface = _41_756.iface; admitted_iface = _41_756.admitted_iface}))

let is_type_lid = (fun ( env ) ( lid ) -> (let aux = (fun ( _41_761 ) -> (match (()) with
| () -> begin
(match ((try_lookup_typ_name' false env lid)) with
| Some (_41_763) -> begin
true
end
| _41_766 -> begin
false
end)
end))
in (match ((lid.Microsoft_FStar_Absyn_Syntax.ns = [])) with
| true -> begin
(match ((try_lookup_id env lid.Microsoft_FStar_Absyn_Syntax.ident)) with
| Some (_41_768) -> begin
false
end
| _41_771 -> begin
(aux ())
end)
end
| false -> begin
(aux ())
end)))

let check_admits = (fun ( nm ) ( env ) -> (let warn = (not ((let _112_573 = (Support.ST.read Microsoft_FStar_Options.admit_fsi)
in (Support.All.pipe_right _112_573 (Support.Microsoft.FStar.Util.for_some (fun ( l ) -> (nm.Microsoft_FStar_Absyn_Syntax.str = l)))))))
in (Support.All.pipe_right env.sigaccum (Support.List.iter (fun ( se ) -> (match (se) with
| Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((l, t, quals, r)) -> begin
(match ((try_lookup_lid env l)) with
| None -> begin
(let _41_784 = (match (warn) with
| true -> begin
(let _112_578 = (let _112_577 = (let _112_575 = (Microsoft_FStar_Absyn_Syntax.range_of_lid l)
in (Support.Microsoft.FStar.Range.string_of_range _112_575))
in (let _112_576 = (Microsoft_FStar_Absyn_Print.sli l)
in (Support.Microsoft.FStar.Util.format2 "%s: Warning: Admitting %s without a definition\n" _112_577 _112_576)))
in (Support.Microsoft.FStar.Util.print_string _112_578))
end
| false -> begin
()
end)
in (let _112_579 = (sigmap env)
in (Support.Microsoft.FStar.Util.smap_add _112_579 l.Microsoft_FStar_Absyn_Syntax.str (Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((l, t, (Microsoft_FStar_Absyn_Syntax.Assumption)::quals, r)), false))))
end
| Some (_41_787) -> begin
()
end)
end
| _41_790 -> begin
()
end))))))

let finish = (fun ( env ) ( modul ) -> (let _41_828 = (Support.All.pipe_right modul.Microsoft_FStar_Absyn_Syntax.declarations (Support.List.iter (fun ( _41_15 ) -> (match (_41_15) with
| Microsoft_FStar_Absyn_Syntax.Sig_bundle ((ses, quals, _41_797, _41_799)) -> begin
(match ((Support.List.contains Microsoft_FStar_Absyn_Syntax.Private quals)) with
| true -> begin
(Support.All.pipe_right ses (Support.List.iter (fun ( _41_14 ) -> (match (_41_14) with
| Microsoft_FStar_Absyn_Syntax.Sig_datacon ((lid, _41_805, _41_807, _41_809, _41_811, _41_813)) -> begin
(let _112_586 = (sigmap env)
in (Support.Microsoft.FStar.Util.smap_remove _112_586 lid.Microsoft_FStar_Absyn_Syntax.str))
end
| _41_817 -> begin
()
end))))
end
| false -> begin
()
end)
end
| Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((lid, _41_820, quals, _41_823)) -> begin
(match ((Support.List.contains Microsoft_FStar_Absyn_Syntax.Private quals)) with
| true -> begin
(let _112_587 = (sigmap env)
in (Support.Microsoft.FStar.Util.smap_remove _112_587 lid.Microsoft_FStar_Absyn_Syntax.str))
end
| false -> begin
()
end)
end
| _41_827 -> begin
()
end))))
in (let _41_830 = env
in {curmodule = None; modules = ((modul.Microsoft_FStar_Absyn_Syntax.name, modul))::env.modules; open_namespaces = []; sigaccum = []; localbindings = []; recbindings = []; phase = Microsoft_FStar_Parser_AST.Un; sigmap = _41_830.sigmap; default_result_effect = _41_830.default_result_effect; iface = _41_830.iface; admitted_iface = _41_830.admitted_iface})))

let push = (fun ( env ) -> (let _41_833 = env
in (let _112_592 = (let _112_591 = (let _112_590 = (sigmap env)
in (Support.Microsoft.FStar.Util.smap_copy _112_590))
in (_112_591)::env.sigmap)
in {curmodule = _41_833.curmodule; modules = _41_833.modules; open_namespaces = _41_833.open_namespaces; sigaccum = _41_833.sigaccum; localbindings = _41_833.localbindings; recbindings = _41_833.recbindings; phase = _41_833.phase; sigmap = _112_592; default_result_effect = _41_833.default_result_effect; iface = _41_833.iface; admitted_iface = _41_833.admitted_iface})))

let mark = (fun ( env ) -> (push env))

let reset_mark = (fun ( env ) -> (let _41_837 = env
in (let _112_597 = (Support.List.tl env.sigmap)
in {curmodule = _41_837.curmodule; modules = _41_837.modules; open_namespaces = _41_837.open_namespaces; sigaccum = _41_837.sigaccum; localbindings = _41_837.localbindings; recbindings = _41_837.recbindings; phase = _41_837.phase; sigmap = _112_597; default_result_effect = _41_837.default_result_effect; iface = _41_837.iface; admitted_iface = _41_837.admitted_iface})))

let commit_mark = (fun ( env ) -> (match (env.sigmap) with
| hd::_41_842::tl -> begin
(let _41_846 = env
in {curmodule = _41_846.curmodule; modules = _41_846.modules; open_namespaces = _41_846.open_namespaces; sigaccum = _41_846.sigaccum; localbindings = _41_846.localbindings; recbindings = _41_846.recbindings; phase = _41_846.phase; sigmap = (hd)::tl; default_result_effect = _41_846.default_result_effect; iface = _41_846.iface; admitted_iface = _41_846.admitted_iface})
end
| _41_849 -> begin
(Support.All.failwith "Impossible")
end))

let pop = (fun ( env ) -> (match (env.sigmap) with
| _41_853::maps -> begin
(let _41_855 = env
in {curmodule = _41_855.curmodule; modules = _41_855.modules; open_namespaces = _41_855.open_namespaces; sigaccum = _41_855.sigaccum; localbindings = _41_855.localbindings; recbindings = _41_855.recbindings; phase = _41_855.phase; sigmap = maps; default_result_effect = _41_855.default_result_effect; iface = _41_855.iface; admitted_iface = _41_855.admitted_iface})
end
| _41_858 -> begin
(Support.All.failwith "No more modules to pop")
end))

let finish_module_or_interface = (fun ( env ) ( modul ) -> (let _41_861 = (match ((not (modul.Microsoft_FStar_Absyn_Syntax.is_interface))) with
| true -> begin
(check_admits modul.Microsoft_FStar_Absyn_Syntax.name env)
end
| false -> begin
()
end)
in (finish env modul)))

let prepare_module_or_interface = (fun ( intf ) ( admitted ) ( env ) ( mname ) -> (let prep = (fun ( env ) -> (let open_ns = (match ((Microsoft_FStar_Absyn_Syntax.lid_equals mname Microsoft_FStar_Absyn_Const.prims_lid)) with
| true -> begin
[]
end
| false -> begin
(match ((Microsoft_FStar_Absyn_Syntax.lid_equals mname Microsoft_FStar_Absyn_Const.st_lid)) with
| true -> begin
(Microsoft_FStar_Absyn_Const.prims_lid)::[]
end
| false -> begin
(match ((Microsoft_FStar_Absyn_Syntax.lid_equals mname Microsoft_FStar_Absyn_Const.all_lid)) with
| true -> begin
(Microsoft_FStar_Absyn_Const.prims_lid)::(Microsoft_FStar_Absyn_Const.st_lid)::[]
end
| false -> begin
(Microsoft_FStar_Absyn_Const.prims_lid)::(Microsoft_FStar_Absyn_Const.st_lid)::(Microsoft_FStar_Absyn_Const.all_lid)::[]
end)
end)
end)
in (let _41_870 = env
in {curmodule = Some (mname); modules = _41_870.modules; open_namespaces = open_ns; sigaccum = _41_870.sigaccum; localbindings = _41_870.localbindings; recbindings = _41_870.recbindings; phase = _41_870.phase; sigmap = env.sigmap; default_result_effect = _41_870.default_result_effect; iface = intf; admitted_iface = admitted})))
in (match ((Support.All.pipe_right env.modules (Support.Microsoft.FStar.Util.find_opt (fun ( _41_875 ) -> (match (_41_875) with
| (l, _41_874) -> begin
(Microsoft_FStar_Absyn_Syntax.lid_equals l mname)
end))))) with
| None -> begin
(prep env)
end
| Some ((_41_878, m)) -> begin
(let _41_882 = (match (intf) with
| true -> begin
(let _112_620 = (let _112_619 = (let _112_618 = (Support.Microsoft.FStar.Util.format1 "Duplicate module or interface name: %s" mname.Microsoft_FStar_Absyn_Syntax.str)
in (let _112_617 = (Microsoft_FStar_Absyn_Syntax.range_of_lid mname)
in (_112_618, _112_617)))
in Microsoft_FStar_Absyn_Syntax.Error (_112_619))
in (raise (_112_620)))
end
| false -> begin
()
end)
in (prep env))
end)))

let enter_monad_scope = (fun ( env ) ( mname ) -> (let curmod = (current_module env)
in (let mscope = (Microsoft_FStar_Absyn_Syntax.lid_of_ids (Support.List.append curmod.Microsoft_FStar_Absyn_Syntax.ns ((curmod.Microsoft_FStar_Absyn_Syntax.ident)::(mname)::[])))
in (let _41_888 = env
in {curmodule = Some (mscope); modules = _41_888.modules; open_namespaces = (curmod)::env.open_namespaces; sigaccum = _41_888.sigaccum; localbindings = _41_888.localbindings; recbindings = _41_888.recbindings; phase = _41_888.phase; sigmap = _41_888.sigmap; default_result_effect = _41_888.default_result_effect; iface = _41_888.iface; admitted_iface = _41_888.admitted_iface}))))

let exit_monad_scope = (fun ( env0 ) ( env ) -> (let _41_892 = env
in {curmodule = env0.curmodule; modules = _41_892.modules; open_namespaces = env0.open_namespaces; sigaccum = _41_892.sigaccum; localbindings = _41_892.localbindings; recbindings = _41_892.recbindings; phase = _41_892.phase; sigmap = _41_892.sigmap; default_result_effect = _41_892.default_result_effect; iface = _41_892.iface; admitted_iface = _41_892.admitted_iface}))

let fail_or = (fun ( env ) ( lookup ) ( lid ) -> (match ((lookup lid)) with
| None -> begin
(let r = (match ((try_lookup_name true false env lid)) with
| None -> begin
None
end
| (Some (Knd_name ((o, _)))) | (Some (Eff_name ((o, _)))) | (Some (Typ_name ((o, _)))) | (Some (Exp_name ((o, _)))) -> begin
(let _112_635 = (range_of_occurrence o)
in Some (_112_635))
end)
in (let msg = (match (r) with
| None -> begin
""
end
| Some (r) -> begin
(let _112_636 = (Support.Microsoft.FStar.Range.string_of_range r)
in (Support.Microsoft.FStar.Util.format1 "(Possible clash with related name at %s)" _112_636))
end)
in (let _112_641 = (let _112_640 = (let _112_639 = (let _112_637 = (Microsoft_FStar_Absyn_Syntax.text_of_lid lid)
in (Support.Microsoft.FStar.Util.format2 "Identifier not found: [%s] %s" _112_637 msg))
in (let _112_638 = (Microsoft_FStar_Absyn_Syntax.range_of_lid lid)
in (_112_639, _112_638)))
in Microsoft_FStar_Absyn_Syntax.Error (_112_640))
in (raise (_112_641)))))
end
| Some (r) -> begin
r
end))

let fail_or2 = (fun ( lookup ) ( id ) -> (match ((lookup id)) with
| None -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (((Support.String.strcat (Support.String.strcat "Identifier not found [" id.Microsoft_FStar_Absyn_Syntax.idText) "]"), id.Microsoft_FStar_Absyn_Syntax.idRange))))
end
| Some (r) -> begin
r
end))




