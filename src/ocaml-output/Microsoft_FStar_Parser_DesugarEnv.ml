
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

let qual = (fun ( lid ) ( id ) -> (let _70_18316 = (Microsoft_FStar_Absyn_Syntax.lid_of_ids (Support.List.append lid.Microsoft_FStar_Absyn_Syntax.ns ((lid.Microsoft_FStar_Absyn_Syntax.ident)::(id)::[])))
in (Microsoft_FStar_Absyn_Util.set_lid_range _70_18316 id.Microsoft_FStar_Absyn_Syntax.idRange)))

let qualify = (fun ( env ) ( id ) -> (let _70_18321 = (current_module env)
in (qual _70_18321 id)))

let qualify_lid = (fun ( env ) ( lid ) -> (let cur = (current_module env)
in (let _70_18327 = (Microsoft_FStar_Absyn_Syntax.lid_of_ids (Support.List.append (Support.List.append (Support.List.append cur.Microsoft_FStar_Absyn_Syntax.ns ((cur.Microsoft_FStar_Absyn_Syntax.ident)::[])) lid.Microsoft_FStar_Absyn_Syntax.ns) ((lid.Microsoft_FStar_Absyn_Syntax.ident)::[])))
in (let _70_18326 = (Microsoft_FStar_Absyn_Syntax.range_of_lid lid)
in (Microsoft_FStar_Absyn_Util.set_lid_range _70_18327 _70_18326)))))

let new_sigmap = (fun ( _41_48 ) -> (match (()) with
| () -> begin
(Support.Microsoft.FStar.Util.smap_create 100)
end))

let empty_env = (fun ( _41_49 ) -> (match (()) with
| () -> begin
(let _70_18332 = (let _70_18331 = (new_sigmap ())
in (_70_18331)::[])
in {curmodule = None; modules = []; open_namespaces = []; sigaccum = []; localbindings = []; recbindings = []; phase = Microsoft_FStar_Parser_AST.Un; sigmap = _70_18332; default_result_effect = Microsoft_FStar_Absyn_Util.ml_comp; iface = false; admitted_iface = false})
end))

let sigmap = (fun ( env ) -> (Support.List.hd env.sigmap))

let default_total = (fun ( env ) -> (let _41_52 = env
in {curmodule = _41_52.curmodule; modules = _41_52.modules; open_namespaces = _41_52.open_namespaces; sigaccum = _41_52.sigaccum; localbindings = _41_52.localbindings; recbindings = _41_52.recbindings; phase = _41_52.phase; sigmap = _41_52.sigmap; default_result_effect = (fun ( t ) ( _41_55 ) -> (Microsoft_FStar_Absyn_Syntax.mk_Total t)); iface = _41_52.iface; admitted_iface = _41_52.admitted_iface}))

let default_ml = (fun ( env ) -> (let _41_58 = env
in {curmodule = _41_58.curmodule; modules = _41_58.modules; open_namespaces = _41_58.open_namespaces; sigaccum = _41_58.sigaccum; localbindings = _41_58.localbindings; recbindings = _41_58.recbindings; phase = _41_58.phase; sigmap = _41_58.sigmap; default_result_effect = Microsoft_FStar_Absyn_Util.ml_comp; iface = _41_58.iface; admitted_iface = _41_58.admitted_iface}))

let range_of_binding = (fun ( _41_1 ) -> (match (_41_1) with
| (Binding_typ_var (id)) | (Binding_var (id)) -> begin
id.Microsoft_FStar_Absyn_Syntax.idRange
end
| (Binding_let (lid)) | (Binding_tycon (lid)) -> begin
(Microsoft_FStar_Absyn_Syntax.range_of_lid lid)
end))

let try_lookup_typ_var = (fun ( env ) ( id ) -> (let fopt = (Support.List.tryFind (fun ( _41_72 ) -> (match (_41_72) with
| (_41_70, b) -> begin
(match (b) with
| (Binding_typ_var (id')) | (Binding_var (id')) -> begin
(id.Microsoft_FStar_Absyn_Syntax.idText = id'.Microsoft_FStar_Absyn_Syntax.idText)
end
| _41_77 -> begin
false
end)
end)) env.localbindings)
in (match (fopt) with
| Some ((Support.Microsoft.FStar.Util.Inl (bvd), Binding_typ_var (_41_82))) -> begin
(let _70_18349 = (let _70_18348 = (Microsoft_FStar_Absyn_Util.set_bvd_range bvd id.Microsoft_FStar_Absyn_Syntax.idRange)
in (Microsoft_FStar_Absyn_Util.bvd_to_typ _70_18348 Microsoft_FStar_Absyn_Syntax.kun))
in Some (_70_18349))
end
| _41_87 -> begin
None
end)))

let resolve_in_open_namespaces = (fun ( env ) ( lid ) ( finder ) -> (let aux = (fun ( namespaces ) -> (match ((finder lid)) with
| Some (r) -> begin
Some (r)
end
| _41_97 -> begin
(let ids = (Microsoft_FStar_Absyn_Syntax.ids_of_lid lid)
in (Support.Microsoft.FStar.Util.find_map namespaces (fun ( ns ) -> (let full_name = (let _70_18364 = (let _70_18363 = (Microsoft_FStar_Absyn_Syntax.ids_of_lid ns)
in (Support.List.append _70_18363 ids))
in (Microsoft_FStar_Absyn_Syntax.lid_of_ids _70_18364))
in (finder full_name)))))
end))
in (let _70_18366 = (let _70_18365 = (current_module env)
in (_70_18365)::env.open_namespaces)
in (aux _70_18366))))

let unmangleMap = (("op_ColonColon", "Cons"))::(("not", "op_Negation"))::[]

let unmangleOpName = (fun ( id ) -> (Support.Microsoft.FStar.Util.find_map unmangleMap (fun ( _41_104 ) -> (match (_41_104) with
| (x, y) -> begin
(match ((id.Microsoft_FStar_Absyn_Syntax.idText = x)) with
| true -> begin
(let _70_18370 = (Microsoft_FStar_Absyn_Syntax.lid_of_path (("Prims")::(y)::[]) id.Microsoft_FStar_Absyn_Syntax.idRange)
in Some (_70_18370))
end
| false -> begin
None
end)
end))))

let try_lookup_id' = (fun ( env ) ( id ) -> (match ((unmangleOpName id)) with
| Some (l) -> begin
(let _70_18378 = (let _70_18377 = (let _70_18376 = (let _70_18375 = (Microsoft_FStar_Absyn_Util.fv l)
in (_70_18375, None))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_fvar _70_18376 None id.Microsoft_FStar_Absyn_Syntax.idRange))
in (l, _70_18377))
in Some (_70_18378))
end
| _41_110 -> begin
(let found = (Support.Microsoft.FStar.Util.find_map env.localbindings (fun ( _41_2 ) -> (match (_41_2) with
| (Support.Microsoft.FStar.Util.Inl (_41_113), Binding_typ_var (id')) when (id'.Microsoft_FStar_Absyn_Syntax.idText = id.Microsoft_FStar_Absyn_Syntax.idText) -> begin
Some (Support.Microsoft.FStar.Util.Inl (()))
end
| (Support.Microsoft.FStar.Util.Inr (bvd), Binding_var (id')) when (id'.Microsoft_FStar_Absyn_Syntax.idText = id.Microsoft_FStar_Absyn_Syntax.idText) -> begin
(let _70_18384 = (let _70_18383 = (let _70_18382 = (Microsoft_FStar_Absyn_Syntax.lid_of_ids ((id')::[]))
in (let _70_18381 = (let _70_18380 = (Microsoft_FStar_Absyn_Util.set_bvd_range bvd id.Microsoft_FStar_Absyn_Syntax.idRange)
in (Microsoft_FStar_Absyn_Util.bvd_to_exp _70_18380 Microsoft_FStar_Absyn_Syntax.tun))
in (_70_18382, _70_18381)))
in Support.Microsoft.FStar.Util.Inr (_70_18383))
in Some (_70_18384))
end
| _41_124 -> begin
None
end)))
in (match (found) with
| Some (Support.Microsoft.FStar.Util.Inr (x)) -> begin
Some (x)
end
| _41_130 -> begin
None
end))
end))

let try_lookup_id = (fun ( env ) ( id ) -> (match ((try_lookup_id' env id)) with
| Some ((_41_134, e)) -> begin
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

let fv_qual_of_se = (fun ( _41_5 ) -> (match (_41_5) with
| Microsoft_FStar_Absyn_Syntax.Sig_datacon ((_41_161, _41_163, (l, _41_166, _41_168), quals, _41_172, _41_174)) -> begin
(let qopt = (Support.Microsoft.FStar.Util.find_map quals (fun ( _41_4 ) -> (match (_41_4) with
| Microsoft_FStar_Absyn_Syntax.RecordConstructor (fs) -> begin
Some (Microsoft_FStar_Absyn_Syntax.Record_ctor ((l, fs)))
end
| _41_181 -> begin
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
| Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((_41_186, _41_188, quals, _41_191)) -> begin
None
end
| _41_195 -> begin
None
end))

let try_lookup_name = (fun ( any_val ) ( exclude_interf ) ( env ) ( lid ) -> (let find_in_sig = (fun ( lid ) -> (match ((let _70_18453 = (sigmap env)
in (Support.Microsoft.FStar.Util.smap_try_find _70_18453 lid.Microsoft_FStar_Absyn_Syntax.str))) with
| Some ((_41_203, true)) when exclude_interf -> begin
None
end
| None -> begin
None
end
| Some ((se, _41_210)) -> begin
(match (se) with
| (Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_tycon (_)) -> begin
(let _70_18456 = (let _70_18455 = (let _70_18454 = (Microsoft_FStar_Absyn_Util.ftv lid Microsoft_FStar_Absyn_Syntax.kun)
in (OSig (se), _70_18454))
in Typ_name (_70_18455))
in Some (_70_18456))
end
| Microsoft_FStar_Absyn_Syntax.Sig_kind_abbrev (_41_220) -> begin
Some (Knd_name ((OSig (se), lid)))
end
| Microsoft_FStar_Absyn_Syntax.Sig_new_effect ((ne, _41_224)) -> begin
(let _70_18460 = (let _70_18459 = (let _70_18458 = (let _70_18457 = (Microsoft_FStar_Absyn_Syntax.range_of_lid lid)
in (Microsoft_FStar_Absyn_Util.set_lid_range ne.Microsoft_FStar_Absyn_Syntax.mname _70_18457))
in (OSig (se), _70_18458))
in Eff_name (_70_18459))
in Some (_70_18460))
end
| Microsoft_FStar_Absyn_Syntax.Sig_effect_abbrev (_41_228) -> begin
Some (Eff_name ((OSig (se), lid)))
end
| Microsoft_FStar_Absyn_Syntax.Sig_datacon (_41_231) -> begin
(let _70_18465 = (let _70_18464 = (let _70_18463 = (let _70_18462 = (fv_qual_of_se se)
in (let _70_18461 = (Microsoft_FStar_Absyn_Syntax.range_of_lid lid)
in (Microsoft_FStar_Absyn_Util.fvar _70_18462 lid _70_18461)))
in (OSig (se), _70_18463))
in Exp_name (_70_18464))
in Some (_70_18465))
end
| Microsoft_FStar_Absyn_Syntax.Sig_let (_41_234) -> begin
(let _70_18469 = (let _70_18468 = (let _70_18467 = (let _70_18466 = (Microsoft_FStar_Absyn_Syntax.range_of_lid lid)
in (Microsoft_FStar_Absyn_Util.fvar None lid _70_18466))
in (OSig (se), _70_18467))
in Exp_name (_70_18468))
in Some (_70_18469))
end
| Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((_41_237, _41_239, quals, _41_242)) -> begin
(match ((any_val || (Support.All.pipe_right quals (Support.Microsoft.FStar.Util.for_some (fun ( _41_6 ) -> (match (_41_6) with
| Microsoft_FStar_Absyn_Syntax.Assumption -> begin
true
end
| _41_248 -> begin
false
end)))))) with
| true -> begin
(let _70_18475 = (let _70_18474 = (let _70_18473 = (let _70_18472 = (fv_qual_of_se se)
in (let _70_18471 = (Microsoft_FStar_Absyn_Syntax.range_of_lid lid)
in (Microsoft_FStar_Absyn_Util.fvar _70_18472 lid _70_18471)))
in (OSig (se), _70_18473))
in Exp_name (_70_18474))
in Some (_70_18475))
end
| false -> begin
None
end)
end
| _41_250 -> begin
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
(let _70_18480 = (let _70_18479 = (let _70_18478 = (let _70_18477 = (Microsoft_FStar_Absyn_Syntax.range_of_lid recname)
in (Microsoft_FStar_Absyn_Util.fvar None recname _70_18477))
in (ORec (l), _70_18478))
in Exp_name (_70_18479))
in Some (_70_18480))
end
| Binding_tycon (l) when (Microsoft_FStar_Absyn_Syntax.lid_equals l recname) -> begin
(let _70_18483 = (let _70_18482 = (let _70_18481 = (Microsoft_FStar_Absyn_Util.ftv recname Microsoft_FStar_Absyn_Syntax.kun)
in (ORec (l), _70_18481))
in Typ_name (_70_18482))
in Some (_70_18483))
end
| _41_264 -> begin
None
end))))
end)
end
| _41_266 -> begin
None
end)
in (match (found_id) with
| Some (_41_269) -> begin
found_id
end
| _41_272 -> begin
(resolve_in_open_namespaces env lid find_in_sig)
end))))

let try_lookup_typ_name' = (fun ( exclude_interf ) ( env ) ( lid ) -> (match ((try_lookup_name true exclude_interf env lid)) with
| Some (Typ_name ((_41_277, t))) -> begin
Some (t)
end
| Some (Eff_name ((_41_283, l))) -> begin
(let _70_18490 = (Microsoft_FStar_Absyn_Util.ftv l Microsoft_FStar_Absyn_Syntax.mk_Kind_unknown)
in Some (_70_18490))
end
| _41_289 -> begin
None
end))

let try_lookup_typ_name = (fun ( env ) ( l ) -> (try_lookup_typ_name' (not (env.iface)) env l))

let try_lookup_effect_name' = (fun ( exclude_interf ) ( env ) ( lid ) -> (match ((try_lookup_name true exclude_interf env lid)) with
| Some (Eff_name ((o, l))) -> begin
Some ((o, l))
end
| _41_301 -> begin
None
end))

let try_lookup_effect_name = (fun ( env ) ( l ) -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some ((o, l)) -> begin
Some (l)
end
| _41_309 -> begin
None
end))

let try_lookup_effect_defn = (fun ( env ) ( l ) -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some ((OSig (Microsoft_FStar_Absyn_Syntax.Sig_new_effect ((ne, _41_314))), _41_319)) -> begin
Some (ne)
end
| _41_323 -> begin
None
end))

let is_effect_name = (fun ( env ) ( lid ) -> (match ((try_lookup_effect_name env lid)) with
| None -> begin
false
end
| Some (_41_328) -> begin
true
end))

let try_resolve_typ_abbrev = (fun ( env ) ( lid ) -> (let find_in_sig = (fun ( lid ) -> (match ((let _70_18519 = (sigmap env)
in (Support.Microsoft.FStar.Util.smap_try_find _70_18519 lid.Microsoft_FStar_Absyn_Syntax.str))) with
| Some ((Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev ((lid, tps, k, def, _41_339, _41_341)), _41_345)) -> begin
(let t = (let _70_18522 = (let _70_18521 = (let _70_18520 = (Microsoft_FStar_Absyn_Util.close_with_lam tps def)
in (_70_18520, lid))
in Microsoft_FStar_Absyn_Syntax.Meta_named (_70_18521))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta _70_18522))
in Some (t))
end
| _41_350 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))

let lookup_letbinding_quals = (fun ( env ) ( lid ) -> (let find_in_sig = (fun ( lid ) -> (match ((let _70_18529 = (sigmap env)
in (Support.Microsoft.FStar.Util.smap_try_find _70_18529 lid.Microsoft_FStar_Absyn_Syntax.str))) with
| Some ((Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((lid, _41_357, quals, _41_360)), _41_364)) -> begin
Some (quals)
end
| _41_368 -> begin
None
end))
in (match ((resolve_in_open_namespaces env lid find_in_sig)) with
| Some (quals) -> begin
quals
end
| _41_372 -> begin
[]
end)))

let try_lookup_module = (fun ( env ) ( path ) -> (match ((Support.List.tryFind (fun ( _41_377 ) -> (match (_41_377) with
| (mlid, modul) -> begin
((Microsoft_FStar_Absyn_Syntax.path_of_lid mlid) = path)
end)) env.modules)) with
| Some ((_41_379, modul)) -> begin
Some (modul)
end
| None -> begin
None
end))

let try_lookup_let = (fun ( env ) ( lid ) -> (let find_in_sig = (fun ( lid ) -> (match ((let _70_18541 = (sigmap env)
in (Support.Microsoft.FStar.Util.smap_try_find _70_18541 lid.Microsoft_FStar_Absyn_Syntax.str))) with
| Some ((Microsoft_FStar_Absyn_Syntax.Sig_let (_41_389), _41_392)) -> begin
(let _70_18543 = (let _70_18542 = (Microsoft_FStar_Absyn_Syntax.range_of_lid lid)
in (Microsoft_FStar_Absyn_Util.fvar None lid _70_18542))
in Some (_70_18543))
end
| _41_396 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))

let try_lookup_lid' = (fun ( any_val ) ( exclude_interf ) ( env ) ( lid ) -> (match ((try_lookup_name any_val exclude_interf env lid)) with
| Some (Exp_name ((_41_402, e))) -> begin
Some (e)
end
| _41_408 -> begin
None
end))

let try_lookup_lid = (fun ( env ) ( l ) -> (try_lookup_lid' env.iface false env l))

let try_lookup_datacon = (fun ( env ) ( lid ) -> (let find_in_sig = (fun ( lid ) -> (match ((let _70_18562 = (sigmap env)
in (Support.Microsoft.FStar.Util.smap_try_find _70_18562 lid.Microsoft_FStar_Absyn_Syntax.str))) with
| Some ((Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((_41_416, _41_418, quals, _41_421)), _41_425)) -> begin
(match ((Support.All.pipe_right quals (Support.Microsoft.FStar.Util.for_some (fun ( _41_8 ) -> (match (_41_8) with
| Microsoft_FStar_Absyn_Syntax.Assumption -> begin
true
end
| _41_431 -> begin
false
end))))) with
| true -> begin
(let _70_18564 = (Microsoft_FStar_Absyn_Util.fv lid)
in Some (_70_18564))
end
| false -> begin
None
end)
end
| Some ((Microsoft_FStar_Absyn_Syntax.Sig_datacon (_41_433), _41_436)) -> begin
(let _70_18565 = (Microsoft_FStar_Absyn_Util.fv lid)
in Some (_70_18565))
end
| _41_440 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))

let find_all_datacons = (fun ( env ) ( lid ) -> (let find_in_sig = (fun ( lid ) -> (match ((let _70_18572 = (sigmap env)
in (Support.Microsoft.FStar.Util.smap_try_find _70_18572 lid.Microsoft_FStar_Absyn_Syntax.str))) with
| Some ((Microsoft_FStar_Absyn_Syntax.Sig_tycon ((_41_446, _41_448, _41_450, _41_452, datas, _41_455, _41_457)), _41_461)) -> begin
Some (datas)
end
| _41_465 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))

type record =
{typename : Microsoft_FStar_Absyn_Syntax.lident; constrname : Microsoft_FStar_Absyn_Syntax.lident; parms : Microsoft_FStar_Absyn_Syntax.binders; fields : (Microsoft_FStar_Absyn_Syntax.fieldname * Microsoft_FStar_Absyn_Syntax.typ) list}

let is_Mkrecord = (fun ( _ ) -> (Support.All.failwith "Not yet implemented:is_Mkrecord"))

let record_cache = (Support.Microsoft.FStar.Util.mk_ref [])

let extract_record = (fun ( e ) ( _41_12 ) -> (match (_41_12) with
| Microsoft_FStar_Absyn_Syntax.Sig_bundle ((sigs, _41_475, _41_477, _41_479)) -> begin
(let is_rec = (Support.Microsoft.FStar.Util.for_some (fun ( _41_9 ) -> (match (_41_9) with
| (Microsoft_FStar_Absyn_Syntax.RecordType (_)) | (Microsoft_FStar_Absyn_Syntax.RecordConstructor (_)) -> begin
true
end
| _41_490 -> begin
false
end)))
in (let find_dc = (fun ( dc ) -> (Support.All.pipe_right sigs (Support.Microsoft.FStar.Util.find_opt (fun ( _41_10 ) -> (match (_41_10) with
| Microsoft_FStar_Absyn_Syntax.Sig_datacon ((lid, _41_497, _41_499, _41_501, _41_503, _41_505)) -> begin
(Microsoft_FStar_Absyn_Syntax.lid_equals dc lid)
end
| _41_509 -> begin
false
end)))))
in (Support.All.pipe_right sigs (Support.List.iter (fun ( _41_11 ) -> (match (_41_11) with
| Microsoft_FStar_Absyn_Syntax.Sig_tycon ((typename, parms, _41_514, _41_516, dc::[], tags, _41_521)) -> begin
(match ((is_rec tags)) with
| true -> begin
(match ((let _70_18596 = (find_dc dc)
in (Support.All.pipe_left Support.Microsoft.FStar.Util.must _70_18596))) with
| Microsoft_FStar_Absyn_Syntax.Sig_datacon ((constrname, t, _41_527, _41_529, _41_531, _41_533)) -> begin
(let formals = (match ((Microsoft_FStar_Absyn_Util.function_formals t)) with
| Some ((x, _41_538)) -> begin
x
end
| _41_542 -> begin
[]
end)
in (let fields = (Support.All.pipe_right formals (Support.List.collect (fun ( b ) -> (match (b) with
| (Support.Microsoft.FStar.Util.Inr (x), q) -> begin
(match (((Microsoft_FStar_Absyn_Syntax.is_null_binder b) || (q = Some (Microsoft_FStar_Absyn_Syntax.Implicit)))) with
| true -> begin
[]
end
| false -> begin
(let _70_18600 = (let _70_18599 = (let _70_18598 = (Microsoft_FStar_Absyn_Util.unmangle_field_name x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ppname)
in (qual constrname _70_18598))
in (_70_18599, x.Microsoft_FStar_Absyn_Syntax.sort))
in (_70_18600)::[])
end)
end
| _41_550 -> begin
[]
end))))
in (let record = {typename = typename; constrname = constrname; parms = parms; fields = fields}
in (let _70_18602 = (let _70_18601 = (Support.ST.read record_cache)
in (record)::_70_18601)
in (Support.ST.op_Colon_Equals record_cache _70_18602)))))
end
| _41_554 -> begin
()
end)
end
| false -> begin
()
end)
end
| _41_556 -> begin
()
end))))))
end
| _41_558 -> begin
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
(let _70_18613 = (aux tl)
in (hd)::_70_18613)
end))
in (aux ns)))
in (let find_in_cache = (fun ( fieldname ) -> (let _41_576 = (fieldname.Microsoft_FStar_Absyn_Syntax.ns, fieldname.Microsoft_FStar_Absyn_Syntax.ident)
in (match (_41_576) with
| (ns, fieldname) -> begin
(let _70_18618 = (Support.ST.read record_cache)
in (Support.Microsoft.FStar.Util.find_map _70_18618 (fun ( record ) -> (let constrname = record.constrname.Microsoft_FStar_Absyn_Syntax.ident
in (let ns = (maybe_add_constrname ns constrname)
in (let fname = (Microsoft_FStar_Absyn_Syntax.lid_of_ids (Support.List.append ns ((fieldname)::[])))
in (Support.Microsoft.FStar.Util.find_map record.fields (fun ( _41_584 ) -> (match (_41_584) with
| (f, _41_583) -> begin
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

let qualify_field_to_record = (fun ( env ) ( recd ) ( f ) -> (let qualify = (fun ( fieldname ) -> (let _41_592 = (fieldname.Microsoft_FStar_Absyn_Syntax.ns, fieldname.Microsoft_FStar_Absyn_Syntax.ident)
in (match (_41_592) with
| (ns, fieldname) -> begin
(let constrname = recd.constrname.Microsoft_FStar_Absyn_Syntax.ident
in (let fname = (Microsoft_FStar_Absyn_Syntax.lid_of_ids (Support.List.append (Support.List.append ns ((constrname)::[])) ((fieldname)::[])))
in (Support.Microsoft.FStar.Util.find_map recd.fields (fun ( _41_598 ) -> (match (_41_598) with
| (f, _41_597) -> begin
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
| Some (Knd_name ((_41_602, l))) -> begin
Some (l)
end
| _41_608 -> begin
None
end))

let is_kind_abbrev = (fun ( env ) ( l ) -> (match ((find_kind_abbrev env l)) with
| None -> begin
false
end
| Some (_41_613) -> begin
true
end))

let unique_name = (fun ( any_val ) ( exclude_if ) ( env ) ( lid ) -> (match ((try_lookup_lid' any_val exclude_if env lid)) with
| None -> begin
(match ((find_kind_abbrev env lid)) with
| None -> begin
true
end
| Some (_41_622) -> begin
false
end)
end
| Some (_41_625) -> begin
false
end))

let unique_typ_name = (fun ( env ) ( lid ) -> (match ((try_lookup_typ_name' true env lid)) with
| None -> begin
true
end
| Some (a) -> begin
false
end))

let unique = (fun ( any_val ) ( exclude_if ) ( env ) ( lid ) -> (let this_env = (let _41_636 = env
in {curmodule = _41_636.curmodule; modules = _41_636.modules; open_namespaces = []; sigaccum = _41_636.sigaccum; localbindings = _41_636.localbindings; recbindings = _41_636.recbindings; phase = _41_636.phase; sigmap = _41_636.sigmap; default_result_effect = _41_636.default_result_effect; iface = _41_636.iface; admitted_iface = _41_636.admitted_iface})
in ((unique_name any_val exclude_if this_env lid) && (unique_typ_name this_env lid))))

let gen_bvd = (fun ( _41_13 ) -> (match (_41_13) with
| Binding_typ_var (id) -> begin
(let _70_18659 = (let _70_18658 = (let _70_18657 = (Microsoft_FStar_Absyn_Util.genident (Some (id.Microsoft_FStar_Absyn_Syntax.idRange)))
in (id, _70_18657))
in (Microsoft_FStar_Absyn_Util.mkbvd _70_18658))
in Support.Microsoft.FStar.Util.Inl (_70_18659))
end
| Binding_var (id) -> begin
(let _70_18662 = (let _70_18661 = (let _70_18660 = (Microsoft_FStar_Absyn_Util.genident (Some (id.Microsoft_FStar_Absyn_Syntax.idRange)))
in (id, _70_18660))
in (Microsoft_FStar_Absyn_Util.mkbvd _70_18661))
in Support.Microsoft.FStar.Util.Inr (_70_18662))
end
| _41_645 -> begin
(Support.All.failwith "Tried to generate a bound variable for a type constructor")
end))

let push_bvvdef = (fun ( env ) ( x ) -> (let b = Binding_var (x.Microsoft_FStar_Absyn_Syntax.ppname)
in (let _41_649 = env
in {curmodule = _41_649.curmodule; modules = _41_649.modules; open_namespaces = _41_649.open_namespaces; sigaccum = _41_649.sigaccum; localbindings = ((Support.Microsoft.FStar.Util.Inr (x), b))::env.localbindings; recbindings = _41_649.recbindings; phase = _41_649.phase; sigmap = _41_649.sigmap; default_result_effect = _41_649.default_result_effect; iface = _41_649.iface; admitted_iface = _41_649.admitted_iface})))

let push_btvdef = (fun ( env ) ( x ) -> (let b = Binding_typ_var (x.Microsoft_FStar_Absyn_Syntax.ppname)
in (let _41_654 = env
in {curmodule = _41_654.curmodule; modules = _41_654.modules; open_namespaces = _41_654.open_namespaces; sigaccum = _41_654.sigaccum; localbindings = ((Support.Microsoft.FStar.Util.Inl (x), b))::env.localbindings; recbindings = _41_654.recbindings; phase = _41_654.phase; sigmap = _41_654.sigmap; default_result_effect = _41_654.default_result_effect; iface = _41_654.iface; admitted_iface = _41_654.admitted_iface})))

let push_local_binding = (fun ( env ) ( b ) -> (let bvd = (gen_bvd b)
in ((let _41_659 = env
in {curmodule = _41_659.curmodule; modules = _41_659.modules; open_namespaces = _41_659.open_namespaces; sigaccum = _41_659.sigaccum; localbindings = ((bvd, b))::env.localbindings; recbindings = _41_659.recbindings; phase = _41_659.phase; sigmap = _41_659.sigmap; default_result_effect = _41_659.default_result_effect; iface = _41_659.iface; admitted_iface = _41_659.admitted_iface}), bvd)))

let push_local_tbinding = (fun ( env ) ( a ) -> (match ((push_local_binding env (Binding_typ_var (a)))) with
| (env, Support.Microsoft.FStar.Util.Inl (x)) -> begin
(env, x)
end
| _41_668 -> begin
(Support.All.failwith "impossible")
end))

let push_local_vbinding = (fun ( env ) ( b ) -> (match ((push_local_binding env (Binding_var (b)))) with
| (env, Support.Microsoft.FStar.Util.Inr (x)) -> begin
(env, x)
end
| _41_676 -> begin
(Support.All.failwith "impossible")
end))

let push_rec_binding = (fun ( env ) ( b ) -> (match (b) with
| (Binding_let (lid)) | (Binding_tycon (lid)) -> begin
(match ((unique false true env lid)) with
| true -> begin
(let _41_682 = env
in {curmodule = _41_682.curmodule; modules = _41_682.modules; open_namespaces = _41_682.open_namespaces; sigaccum = _41_682.sigaccum; localbindings = _41_682.localbindings; recbindings = (b)::env.recbindings; phase = _41_682.phase; sigmap = _41_682.sigmap; default_result_effect = _41_682.default_result_effect; iface = _41_682.iface; admitted_iface = _41_682.admitted_iface})
end
| false -> begin
(let _70_18689 = (let _70_18688 = (let _70_18687 = (Microsoft_FStar_Absyn_Syntax.range_of_lid lid)
in ((Support.String.strcat "Duplicate top-level names " lid.Microsoft_FStar_Absyn_Syntax.str), _70_18687))
in Microsoft_FStar_Absyn_Syntax.Error (_70_18688))
in (raise (_70_18689)))
end)
end
| _41_685 -> begin
(Support.All.failwith "Unexpected rec_binding")
end))

let push_sigelt = (fun ( env ) ( s ) -> (let err = (fun ( l ) -> (let sopt = (let _70_18696 = (sigmap env)
in (Support.Microsoft.FStar.Util.smap_try_find _70_18696 l.Microsoft_FStar_Absyn_Syntax.str))
in (let r = (match (sopt) with
| Some ((se, _41_693)) -> begin
(match ((let _70_18697 = (Microsoft_FStar_Absyn_Util.lids_of_sigelt se)
in (Support.Microsoft.FStar.Util.find_opt (Microsoft_FStar_Absyn_Syntax.lid_equals l) _70_18697))) with
| Some (l) -> begin
(let _70_18698 = (Microsoft_FStar_Absyn_Syntax.range_of_lid l)
in (Support.All.pipe_left Support.Microsoft.FStar.Range.string_of_range _70_18698))
end
| None -> begin
"<unknown>"
end)
end
| None -> begin
"<unknown>"
end)
in (let _70_18703 = (let _70_18702 = (let _70_18701 = (let _70_18699 = (Microsoft_FStar_Absyn_Syntax.text_of_lid l)
in (Support.Microsoft.FStar.Util.format2 "Duplicate top-level names [%s]; previously declared at %s" _70_18699 r))
in (let _70_18700 = (Microsoft_FStar_Absyn_Syntax.range_of_lid l)
in (_70_18701, _70_18700)))
in Microsoft_FStar_Absyn_Syntax.Error (_70_18702))
in (raise (_70_18703))))))
in (let env = (let _41_711 = (match (s) with
| Microsoft_FStar_Absyn_Syntax.Sig_let (_41_702) -> begin
(false, true)
end
| Microsoft_FStar_Absyn_Syntax.Sig_bundle (_41_705) -> begin
(true, true)
end
| _41_708 -> begin
(false, false)
end)
in (match (_41_711) with
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
(let _41_715 = (extract_record env s)
in (let _41_717 = env
in {curmodule = _41_717.curmodule; modules = _41_717.modules; open_namespaces = _41_717.open_namespaces; sigaccum = (s)::env.sigaccum; localbindings = _41_717.localbindings; recbindings = _41_717.recbindings; phase = _41_717.phase; sigmap = _41_717.sigmap; default_result_effect = _41_717.default_result_effect; iface = _41_717.iface; admitted_iface = _41_717.admitted_iface}))
end
| Some (l) -> begin
(err l)
end))
end))
in (let _41_736 = (match (s) with
| Microsoft_FStar_Absyn_Syntax.Sig_bundle ((ses, _41_724, _41_726, _41_728)) -> begin
(let _70_18707 = (Support.List.map (fun ( se ) -> (let _70_18706 = (Microsoft_FStar_Absyn_Util.lids_of_sigelt se)
in (_70_18706, se))) ses)
in (env, _70_18707))
end
| _41_733 -> begin
(let _70_18710 = (let _70_18709 = (let _70_18708 = (Microsoft_FStar_Absyn_Util.lids_of_sigelt s)
in (_70_18708, s))
in (_70_18709)::[])
in (env, _70_18710))
end)
in (match (_41_736) with
| (env, lss) -> begin
(let _41_741 = (Support.All.pipe_right lss (Support.List.iter (fun ( _41_739 ) -> (match (_41_739) with
| (lids, se) -> begin
(Support.All.pipe_right lids (Support.List.iter (fun ( lid ) -> (let _70_18713 = (sigmap env)
in (Support.Microsoft.FStar.Util.smap_add _70_18713 lid.Microsoft_FStar_Absyn_Syntax.str (se, (env.iface && (not (env.admitted_iface)))))))))
end))))
in env)
end)))))

let push_namespace = (fun ( env ) ( lid ) -> (let _41_745 = env
in {curmodule = _41_745.curmodule; modules = _41_745.modules; open_namespaces = (lid)::env.open_namespaces; sigaccum = _41_745.sigaccum; localbindings = _41_745.localbindings; recbindings = _41_745.recbindings; phase = _41_745.phase; sigmap = _41_745.sigmap; default_result_effect = _41_745.default_result_effect; iface = _41_745.iface; admitted_iface = _41_745.admitted_iface}))

let is_type_lid = (fun ( env ) ( lid ) -> (let aux = (fun ( _41_750 ) -> (match (()) with
| () -> begin
(match ((try_lookup_typ_name' false env lid)) with
| Some (_41_752) -> begin
true
end
| _41_755 -> begin
false
end)
end))
in (match ((lid.Microsoft_FStar_Absyn_Syntax.ns = [])) with
| true -> begin
(match ((try_lookup_id env lid.Microsoft_FStar_Absyn_Syntax.ident)) with
| Some (_41_757) -> begin
false
end
| _41_760 -> begin
(aux ())
end)
end
| false -> begin
(aux ())
end)))

let check_admits = (fun ( nm ) ( env ) -> (let warn = (not ((let _70_18729 = (Support.ST.read Microsoft_FStar_Options.admit_fsi)
in (Support.All.pipe_right _70_18729 (Support.Microsoft.FStar.Util.for_some (fun ( l ) -> (nm.Microsoft_FStar_Absyn_Syntax.str = l)))))))
in (Support.All.pipe_right env.sigaccum (Support.List.iter (fun ( se ) -> (match (se) with
| Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((l, t, quals, r)) -> begin
(match ((try_lookup_lid env l)) with
| None -> begin
(let _41_773 = (match (warn) with
| true -> begin
(let _70_18734 = (let _70_18733 = (let _70_18731 = (Microsoft_FStar_Absyn_Syntax.range_of_lid l)
in (Support.Microsoft.FStar.Range.string_of_range _70_18731))
in (let _70_18732 = (Microsoft_FStar_Absyn_Print.sli l)
in (Support.Microsoft.FStar.Util.format2 "%s: Warning: Admitting %s without a definition\n" _70_18733 _70_18732)))
in (Support.Microsoft.FStar.Util.print_string _70_18734))
end
| false -> begin
()
end)
in (let _70_18735 = (sigmap env)
in (Support.Microsoft.FStar.Util.smap_add _70_18735 l.Microsoft_FStar_Absyn_Syntax.str (Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((l, t, (Microsoft_FStar_Absyn_Syntax.Assumption)::quals, r)), false))))
end
| Some (_41_776) -> begin
()
end)
end
| _41_779 -> begin
()
end))))))

let finish = (fun ( env ) ( modul ) -> (let _41_817 = (Support.All.pipe_right modul.Microsoft_FStar_Absyn_Syntax.declarations (Support.List.iter (fun ( _41_15 ) -> (match (_41_15) with
| Microsoft_FStar_Absyn_Syntax.Sig_bundle ((ses, quals, _41_786, _41_788)) -> begin
(match ((Support.List.contains Microsoft_FStar_Absyn_Syntax.Private quals)) with
| true -> begin
(Support.All.pipe_right ses (Support.List.iter (fun ( _41_14 ) -> (match (_41_14) with
| Microsoft_FStar_Absyn_Syntax.Sig_datacon ((lid, _41_794, _41_796, _41_798, _41_800, _41_802)) -> begin
(let _70_18742 = (sigmap env)
in (Support.Microsoft.FStar.Util.smap_remove _70_18742 lid.Microsoft_FStar_Absyn_Syntax.str))
end
| _41_806 -> begin
()
end))))
end
| false -> begin
()
end)
end
| Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((lid, _41_809, quals, _41_812)) -> begin
(match ((Support.List.contains Microsoft_FStar_Absyn_Syntax.Private quals)) with
| true -> begin
(let _70_18743 = (sigmap env)
in (Support.Microsoft.FStar.Util.smap_remove _70_18743 lid.Microsoft_FStar_Absyn_Syntax.str))
end
| false -> begin
()
end)
end
| _41_816 -> begin
()
end))))
in (let _41_819 = env
in {curmodule = None; modules = ((modul.Microsoft_FStar_Absyn_Syntax.name, modul))::env.modules; open_namespaces = []; sigaccum = []; localbindings = []; recbindings = []; phase = Microsoft_FStar_Parser_AST.Un; sigmap = _41_819.sigmap; default_result_effect = _41_819.default_result_effect; iface = _41_819.iface; admitted_iface = _41_819.admitted_iface})))

let push = (fun ( env ) -> (let _41_822 = env
in (let _70_18748 = (let _70_18747 = (let _70_18746 = (sigmap env)
in (Support.Microsoft.FStar.Util.smap_copy _70_18746))
in (_70_18747)::env.sigmap)
in {curmodule = _41_822.curmodule; modules = _41_822.modules; open_namespaces = _41_822.open_namespaces; sigaccum = _41_822.sigaccum; localbindings = _41_822.localbindings; recbindings = _41_822.recbindings; phase = _41_822.phase; sigmap = _70_18748; default_result_effect = _41_822.default_result_effect; iface = _41_822.iface; admitted_iface = _41_822.admitted_iface})))

let mark = (fun ( env ) -> (push env))

let reset_mark = (fun ( env ) -> (let _41_826 = env
in (let _70_18753 = (Support.List.tl env.sigmap)
in {curmodule = _41_826.curmodule; modules = _41_826.modules; open_namespaces = _41_826.open_namespaces; sigaccum = _41_826.sigaccum; localbindings = _41_826.localbindings; recbindings = _41_826.recbindings; phase = _41_826.phase; sigmap = _70_18753; default_result_effect = _41_826.default_result_effect; iface = _41_826.iface; admitted_iface = _41_826.admitted_iface})))

let commit_mark = (fun ( env ) -> (match (env.sigmap) with
| hd::_41_831::tl -> begin
(let _41_835 = env
in {curmodule = _41_835.curmodule; modules = _41_835.modules; open_namespaces = _41_835.open_namespaces; sigaccum = _41_835.sigaccum; localbindings = _41_835.localbindings; recbindings = _41_835.recbindings; phase = _41_835.phase; sigmap = (hd)::tl; default_result_effect = _41_835.default_result_effect; iface = _41_835.iface; admitted_iface = _41_835.admitted_iface})
end
| _41_838 -> begin
(Support.All.failwith "Impossible")
end))

let pop = (fun ( env ) -> (match (env.sigmap) with
| _41_842::maps -> begin
(let _41_844 = env
in {curmodule = _41_844.curmodule; modules = _41_844.modules; open_namespaces = _41_844.open_namespaces; sigaccum = _41_844.sigaccum; localbindings = _41_844.localbindings; recbindings = _41_844.recbindings; phase = _41_844.phase; sigmap = maps; default_result_effect = _41_844.default_result_effect; iface = _41_844.iface; admitted_iface = _41_844.admitted_iface})
end
| _41_847 -> begin
(Support.All.failwith "No more modules to pop")
end))

let finish_module_or_interface = (fun ( env ) ( modul ) -> (let _41_850 = (match ((not (modul.Microsoft_FStar_Absyn_Syntax.is_interface))) with
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
in (let _41_859 = env
in {curmodule = Some (mname); modules = _41_859.modules; open_namespaces = open_ns; sigaccum = _41_859.sigaccum; localbindings = _41_859.localbindings; recbindings = _41_859.recbindings; phase = _41_859.phase; sigmap = env.sigmap; default_result_effect = _41_859.default_result_effect; iface = intf; admitted_iface = admitted})))
in (match ((Support.All.pipe_right env.modules (Support.Microsoft.FStar.Util.find_opt (fun ( _41_864 ) -> (match (_41_864) with
| (l, _41_863) -> begin
(Microsoft_FStar_Absyn_Syntax.lid_equals l mname)
end))))) with
| None -> begin
(prep env)
end
| Some ((_41_867, m)) -> begin
(let _41_871 = (match (intf) with
| true -> begin
(let _70_18776 = (let _70_18775 = (let _70_18774 = (Support.Microsoft.FStar.Util.format1 "Duplicate module or interface name: %s" mname.Microsoft_FStar_Absyn_Syntax.str)
in (let _70_18773 = (Microsoft_FStar_Absyn_Syntax.range_of_lid mname)
in (_70_18774, _70_18773)))
in Microsoft_FStar_Absyn_Syntax.Error (_70_18775))
in (raise (_70_18776)))
end
| false -> begin
()
end)
in (prep env))
end)))

let enter_monad_scope = (fun ( env ) ( mname ) -> (let curmod = (current_module env)
in (let mscope = (Microsoft_FStar_Absyn_Syntax.lid_of_ids (Support.List.append curmod.Microsoft_FStar_Absyn_Syntax.ns ((curmod.Microsoft_FStar_Absyn_Syntax.ident)::(mname)::[])))
in (let _41_877 = env
in {curmodule = Some (mscope); modules = _41_877.modules; open_namespaces = (curmod)::env.open_namespaces; sigaccum = _41_877.sigaccum; localbindings = _41_877.localbindings; recbindings = _41_877.recbindings; phase = _41_877.phase; sigmap = _41_877.sigmap; default_result_effect = _41_877.default_result_effect; iface = _41_877.iface; admitted_iface = _41_877.admitted_iface}))))

let exit_monad_scope = (fun ( env0 ) ( env ) -> (let _41_881 = env
in {curmodule = env0.curmodule; modules = _41_881.modules; open_namespaces = env0.open_namespaces; sigaccum = _41_881.sigaccum; localbindings = _41_881.localbindings; recbindings = _41_881.recbindings; phase = _41_881.phase; sigmap = _41_881.sigmap; default_result_effect = _41_881.default_result_effect; iface = _41_881.iface; admitted_iface = _41_881.admitted_iface}))

let fail_or = (fun ( env ) ( lookup ) ( lid ) -> (match ((lookup lid)) with
| None -> begin
(let r = (match ((try_lookup_name true false env lid)) with
| None -> begin
None
end
| (Some (Knd_name ((o, _)))) | (Some (Eff_name ((o, _)))) | (Some (Typ_name ((o, _)))) | (Some (Exp_name ((o, _)))) -> begin
(let _70_18791 = (range_of_occurrence o)
in Some (_70_18791))
end)
in (let msg = (match (r) with
| None -> begin
""
end
| Some (r) -> begin
(let _70_18792 = (Support.Microsoft.FStar.Range.string_of_range r)
in (Support.Microsoft.FStar.Util.format1 "(Possible clash with related name at %s)" _70_18792))
end)
in (let _70_18797 = (let _70_18796 = (let _70_18795 = (let _70_18793 = (Microsoft_FStar_Absyn_Syntax.text_of_lid lid)
in (Support.Microsoft.FStar.Util.format2 "Identifier not found: [%s] %s" _70_18793 msg))
in (let _70_18794 = (Microsoft_FStar_Absyn_Syntax.range_of_lid lid)
in (_70_18795, _70_18794)))
in Microsoft_FStar_Absyn_Syntax.Error (_70_18796))
in (raise (_70_18797)))))
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




