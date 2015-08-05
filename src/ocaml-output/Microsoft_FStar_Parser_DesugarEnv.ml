
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

let is_Mkenv = (fun ( _ ) -> (failwith ("Not yet implemented:is_Mkenv")))

let open_modules = (fun ( e ) -> e.modules)

let current_module = (fun ( env ) -> (match (env.curmodule) with
| None -> begin
(failwith ("Unset current module"))
end
| Some (m) -> begin
m
end))

let qual = (fun ( lid ) ( id ) -> (let _68_18194 = (Microsoft_FStar_Absyn_Syntax.lid_of_ids (Support.List.append lid.Microsoft_FStar_Absyn_Syntax.ns ((lid.Microsoft_FStar_Absyn_Syntax.ident)::(id)::[])))
in (Microsoft_FStar_Absyn_Util.set_lid_range _68_18194 id.Microsoft_FStar_Absyn_Syntax.idRange)))

let qualify = (fun ( env ) ( id ) -> (let _68_18199 = (current_module env)
in (qual _68_18199 id)))

let qualify_lid = (fun ( env ) ( lid ) -> (let cur = (current_module env)
in (let _68_18205 = (Microsoft_FStar_Absyn_Syntax.lid_of_ids (Support.List.append (Support.List.append (Support.List.append cur.Microsoft_FStar_Absyn_Syntax.ns ((cur.Microsoft_FStar_Absyn_Syntax.ident)::[])) lid.Microsoft_FStar_Absyn_Syntax.ns) ((lid.Microsoft_FStar_Absyn_Syntax.ident)::[])))
in (let _68_18204 = (Microsoft_FStar_Absyn_Syntax.range_of_lid lid)
in (Microsoft_FStar_Absyn_Util.set_lid_range _68_18205 _68_18204)))))

let new_sigmap = (fun ( _39_48 ) -> (match (()) with
| () -> begin
(Support.Microsoft.FStar.Util.smap_create 100)
end))

let empty_env = (fun ( _39_49 ) -> (match (()) with
| () -> begin
(let _68_18210 = (let _68_18209 = (new_sigmap ())
in (_68_18209)::[])
in {curmodule = None; modules = []; open_namespaces = []; sigaccum = []; localbindings = []; recbindings = []; phase = Microsoft_FStar_Parser_AST.Un; sigmap = _68_18210; default_result_effect = Microsoft_FStar_Absyn_Util.ml_comp; iface = false; admitted_iface = false})
end))

let sigmap = (fun ( env ) -> (Support.List.hd env.sigmap))

let default_total = (fun ( env ) -> (let _39_52 = env
in {curmodule = _39_52.curmodule; modules = _39_52.modules; open_namespaces = _39_52.open_namespaces; sigaccum = _39_52.sigaccum; localbindings = _39_52.localbindings; recbindings = _39_52.recbindings; phase = _39_52.phase; sigmap = _39_52.sigmap; default_result_effect = (fun ( t ) ( _39_55 ) -> (Microsoft_FStar_Absyn_Syntax.mk_Total t)); iface = _39_52.iface; admitted_iface = _39_52.admitted_iface}))

let default_ml = (fun ( env ) -> (let _39_58 = env
in {curmodule = _39_58.curmodule; modules = _39_58.modules; open_namespaces = _39_58.open_namespaces; sigaccum = _39_58.sigaccum; localbindings = _39_58.localbindings; recbindings = _39_58.recbindings; phase = _39_58.phase; sigmap = _39_58.sigmap; default_result_effect = Microsoft_FStar_Absyn_Util.ml_comp; iface = _39_58.iface; admitted_iface = _39_58.admitted_iface}))

let range_of_binding = (fun ( _39_1 ) -> (match (_39_1) with
| (Binding_typ_var (id)) | (Binding_var (id)) -> begin
id.Microsoft_FStar_Absyn_Syntax.idRange
end
| (Binding_let (lid)) | (Binding_tycon (lid)) -> begin
(Microsoft_FStar_Absyn_Syntax.range_of_lid lid)
end))

let try_lookup_typ_var = (fun ( env ) ( id ) -> (let fopt = (Support.List.tryFind (fun ( _39_72 ) -> (match (_39_72) with
| (_39_70, b) -> begin
(match (b) with
| (Binding_typ_var (id')) | (Binding_var (id')) -> begin
(id.Microsoft_FStar_Absyn_Syntax.idText = id'.Microsoft_FStar_Absyn_Syntax.idText)
end
| _39_77 -> begin
false
end)
end)) env.localbindings)
in (match (fopt) with
| Some ((Support.Microsoft.FStar.Util.Inl (bvd), Binding_typ_var (_39_82))) -> begin
(let _68_18227 = (let _68_18226 = (Microsoft_FStar_Absyn_Util.set_bvd_range bvd id.Microsoft_FStar_Absyn_Syntax.idRange)
in (Microsoft_FStar_Absyn_Util.bvd_to_typ _68_18226 Microsoft_FStar_Absyn_Syntax.kun))
in Some (_68_18227))
end
| _39_87 -> begin
None
end)))

let resolve_in_open_namespaces = (fun ( env ) ( lid ) ( finder ) -> (let aux = (fun ( namespaces ) -> (match ((finder lid)) with
| Some (r) -> begin
Some (r)
end
| _39_97 -> begin
(let ids = (Microsoft_FStar_Absyn_Syntax.ids_of_lid lid)
in (Support.Microsoft.FStar.Util.find_map namespaces (fun ( ns ) -> (let full_name = (let _68_18242 = (let _68_18241 = (Microsoft_FStar_Absyn_Syntax.ids_of_lid ns)
in (Support.List.append _68_18241 ids))
in (Microsoft_FStar_Absyn_Syntax.lid_of_ids _68_18242))
in (finder full_name)))))
end))
in (let _68_18244 = (let _68_18243 = (current_module env)
in (_68_18243)::env.open_namespaces)
in (aux _68_18244))))

let unmangleMap = (("op_ColonColon", "Cons"))::(("not", "op_Negation"))::[]

let unmangleOpName = (fun ( id ) -> (Support.Microsoft.FStar.Util.find_map unmangleMap (fun ( _39_104 ) -> (match (_39_104) with
| (x, y) -> begin
(match ((id.Microsoft_FStar_Absyn_Syntax.idText = x)) with
| true -> begin
(let _68_18248 = (Microsoft_FStar_Absyn_Syntax.lid_of_path (("Prims")::(y)::[]) id.Microsoft_FStar_Absyn_Syntax.idRange)
in Some (_68_18248))
end
| false -> begin
None
end)
end))))

let try_lookup_id' = (fun ( env ) ( id ) -> (match ((unmangleOpName id)) with
| Some (l) -> begin
(let _68_18256 = (let _68_18255 = (let _68_18254 = (let _68_18253 = (Microsoft_FStar_Absyn_Util.fv l)
in (_68_18253, None))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_fvar _68_18254 None id.Microsoft_FStar_Absyn_Syntax.idRange))
in (l, _68_18255))
in Some (_68_18256))
end
| _39_110 -> begin
(let found = (Support.Microsoft.FStar.Util.find_map env.localbindings (fun ( _39_2 ) -> (match (_39_2) with
| (Support.Microsoft.FStar.Util.Inl (_39_113), Binding_typ_var (id')) when (id'.Microsoft_FStar_Absyn_Syntax.idText = id.Microsoft_FStar_Absyn_Syntax.idText) -> begin
Some (Support.Microsoft.FStar.Util.Inl (()))
end
| (Support.Microsoft.FStar.Util.Inr (bvd), Binding_var (id')) when (id'.Microsoft_FStar_Absyn_Syntax.idText = id.Microsoft_FStar_Absyn_Syntax.idText) -> begin
(let _68_18262 = (let _68_18261 = (let _68_18260 = (Microsoft_FStar_Absyn_Syntax.lid_of_ids ((id')::[]))
in (let _68_18259 = (let _68_18258 = (Microsoft_FStar_Absyn_Util.set_bvd_range bvd id.Microsoft_FStar_Absyn_Syntax.idRange)
in (Microsoft_FStar_Absyn_Util.bvd_to_exp _68_18258 Microsoft_FStar_Absyn_Syntax.tun))
in (_68_18260, _68_18259)))
in Support.Microsoft.FStar.Util.Inr (_68_18261))
in Some (_68_18262))
end
| _39_124 -> begin
None
end)))
in (match (found) with
| Some (Support.Microsoft.FStar.Util.Inr (x)) -> begin
Some (x)
end
| _39_130 -> begin
None
end))
end))

let try_lookup_id = (fun ( env ) ( id ) -> (match ((try_lookup_id' env id)) with
| Some ((_39_134, e)) -> begin
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

let range_of_occurrence = (fun ( _39_3 ) -> (match (_39_3) with
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

let fv_qual_of_se = (fun ( _39_5 ) -> (match (_39_5) with
| Microsoft_FStar_Absyn_Syntax.Sig_datacon ((_39_161, _39_163, (l, _39_166, _39_168), quals, _39_172, _39_174)) -> begin
(let qopt = (Support.Microsoft.FStar.Util.find_map quals (fun ( _39_4 ) -> (match (_39_4) with
| Microsoft_FStar_Absyn_Syntax.RecordConstructor (fs) -> begin
Some (Microsoft_FStar_Absyn_Syntax.Record_ctor ((l, fs)))
end
| _39_181 -> begin
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
| Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((_39_186, _39_188, quals, _39_191)) -> begin
None
end
| _39_195 -> begin
None
end))

let try_lookup_name = (fun ( any_val ) ( exclude_interf ) ( env ) ( lid ) -> (let find_in_sig = (fun ( lid ) -> (match ((let _68_18331 = (sigmap env)
in (Support.Microsoft.FStar.Util.smap_try_find _68_18331 lid.Microsoft_FStar_Absyn_Syntax.str))) with
| Some ((_39_203, true)) when exclude_interf -> begin
None
end
| None -> begin
None
end
| Some ((se, _39_210)) -> begin
(match (se) with
| (Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_tycon (_)) -> begin
(let _68_18334 = (let _68_18333 = (let _68_18332 = (Microsoft_FStar_Absyn_Util.ftv lid Microsoft_FStar_Absyn_Syntax.kun)
in (OSig (se), _68_18332))
in Typ_name (_68_18333))
in Some (_68_18334))
end
| Microsoft_FStar_Absyn_Syntax.Sig_kind_abbrev (_39_220) -> begin
Some (Knd_name ((OSig (se), lid)))
end
| Microsoft_FStar_Absyn_Syntax.Sig_new_effect ((ne, _39_224)) -> begin
(let _68_18338 = (let _68_18337 = (let _68_18336 = (let _68_18335 = (Microsoft_FStar_Absyn_Syntax.range_of_lid lid)
in (Microsoft_FStar_Absyn_Util.set_lid_range ne.Microsoft_FStar_Absyn_Syntax.mname _68_18335))
in (OSig (se), _68_18336))
in Eff_name (_68_18337))
in Some (_68_18338))
end
| Microsoft_FStar_Absyn_Syntax.Sig_effect_abbrev (_39_228) -> begin
Some (Eff_name ((OSig (se), lid)))
end
| Microsoft_FStar_Absyn_Syntax.Sig_datacon (_39_231) -> begin
(let _68_18343 = (let _68_18342 = (let _68_18341 = (let _68_18340 = (fv_qual_of_se se)
in (let _68_18339 = (Microsoft_FStar_Absyn_Syntax.range_of_lid lid)
in (Microsoft_FStar_Absyn_Util.fvar _68_18340 lid _68_18339)))
in (OSig (se), _68_18341))
in Exp_name (_68_18342))
in Some (_68_18343))
end
| Microsoft_FStar_Absyn_Syntax.Sig_let (_39_234) -> begin
(let _68_18347 = (let _68_18346 = (let _68_18345 = (let _68_18344 = (Microsoft_FStar_Absyn_Syntax.range_of_lid lid)
in (Microsoft_FStar_Absyn_Util.fvar None lid _68_18344))
in (OSig (se), _68_18345))
in Exp_name (_68_18346))
in Some (_68_18347))
end
| Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((_39_237, _39_239, quals, _39_242)) -> begin
(match ((any_val || (Support.Prims.pipe_right quals (Support.Microsoft.FStar.Util.for_some (fun ( _39_6 ) -> (match (_39_6) with
| Microsoft_FStar_Absyn_Syntax.Assumption -> begin
true
end
| _39_248 -> begin
false
end)))))) with
| true -> begin
(let _68_18353 = (let _68_18352 = (let _68_18351 = (let _68_18350 = (fv_qual_of_se se)
in (let _68_18349 = (Microsoft_FStar_Absyn_Syntax.range_of_lid lid)
in (Microsoft_FStar_Absyn_Util.fvar _68_18350 lid _68_18349)))
in (OSig (se), _68_18351))
in Exp_name (_68_18352))
in Some (_68_18353))
end
| false -> begin
None
end)
end
| _39_250 -> begin
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
in (Support.Microsoft.FStar.Util.find_map env.recbindings (fun ( _39_7 ) -> (match (_39_7) with
| Binding_let (l) when (Microsoft_FStar_Absyn_Syntax.lid_equals l recname) -> begin
(let _68_18358 = (let _68_18357 = (let _68_18356 = (let _68_18355 = (Microsoft_FStar_Absyn_Syntax.range_of_lid recname)
in (Microsoft_FStar_Absyn_Util.fvar None recname _68_18355))
in (ORec (l), _68_18356))
in Exp_name (_68_18357))
in Some (_68_18358))
end
| Binding_tycon (l) when (Microsoft_FStar_Absyn_Syntax.lid_equals l recname) -> begin
(let _68_18361 = (let _68_18360 = (let _68_18359 = (Microsoft_FStar_Absyn_Util.ftv recname Microsoft_FStar_Absyn_Syntax.kun)
in (ORec (l), _68_18359))
in Typ_name (_68_18360))
in Some (_68_18361))
end
| _39_264 -> begin
None
end))))
end)
end
| _39_266 -> begin
None
end)
in (match (found_id) with
| Some (_39_269) -> begin
found_id
end
| _39_272 -> begin
(resolve_in_open_namespaces env lid find_in_sig)
end))))

let try_lookup_typ_name' = (fun ( exclude_interf ) ( env ) ( lid ) -> (match ((try_lookup_name true exclude_interf env lid)) with
| Some (Typ_name ((_39_277, t))) -> begin
Some (t)
end
| Some (Eff_name ((_39_283, l))) -> begin
(let _68_18368 = (Microsoft_FStar_Absyn_Util.ftv l Microsoft_FStar_Absyn_Syntax.mk_Kind_unknown)
in Some (_68_18368))
end
| _39_289 -> begin
None
end))

let try_lookup_typ_name = (fun ( env ) ( l ) -> (try_lookup_typ_name' (not (env.iface)) env l))

let try_lookup_effect_name' = (fun ( exclude_interf ) ( env ) ( lid ) -> (match ((try_lookup_name true exclude_interf env lid)) with
| Some (Eff_name ((o, l))) -> begin
Some ((o, l))
end
| _39_301 -> begin
None
end))

let try_lookup_effect_name = (fun ( env ) ( l ) -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some ((o, l)) -> begin
Some (l)
end
| _39_309 -> begin
None
end))

let try_lookup_effect_defn = (fun ( env ) ( l ) -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some ((OSig (Microsoft_FStar_Absyn_Syntax.Sig_new_effect ((ne, _39_314))), _39_319)) -> begin
Some (ne)
end
| _39_323 -> begin
None
end))

let is_effect_name = (fun ( env ) ( lid ) -> (match ((try_lookup_effect_name env lid)) with
| None -> begin
false
end
| Some (_39_328) -> begin
true
end))

let try_resolve_typ_abbrev = (fun ( env ) ( lid ) -> (let find_in_sig = (fun ( lid ) -> (match ((let _68_18397 = (sigmap env)
in (Support.Microsoft.FStar.Util.smap_try_find _68_18397 lid.Microsoft_FStar_Absyn_Syntax.str))) with
| Some ((Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev ((lid, tps, k, def, _39_339, _39_341)), _39_345)) -> begin
(let t = (let _68_18400 = (let _68_18399 = (let _68_18398 = (Microsoft_FStar_Absyn_Util.close_with_lam tps def)
in (_68_18398, lid))
in Microsoft_FStar_Absyn_Syntax.Meta_named (_68_18399))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta _68_18400))
in Some (t))
end
| _39_350 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))

let lookup_letbinding_quals = (fun ( env ) ( lid ) -> (let find_in_sig = (fun ( lid ) -> (match ((let _68_18407 = (sigmap env)
in (Support.Microsoft.FStar.Util.smap_try_find _68_18407 lid.Microsoft_FStar_Absyn_Syntax.str))) with
| Some ((Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((lid, _39_357, quals, _39_360)), _39_364)) -> begin
Some (quals)
end
| _39_368 -> begin
None
end))
in (match ((resolve_in_open_namespaces env lid find_in_sig)) with
| Some (quals) -> begin
quals
end
| _39_372 -> begin
[]
end)))

let try_lookup_module = (fun ( env ) ( path ) -> (match ((Support.List.tryFind (fun ( _39_377 ) -> (match (_39_377) with
| (mlid, modul) -> begin
((Microsoft_FStar_Absyn_Syntax.path_of_lid mlid) = path)
end)) env.modules)) with
| Some ((_39_379, modul)) -> begin
Some (modul)
end
| None -> begin
None
end))

let try_lookup_let = (fun ( env ) ( lid ) -> (let find_in_sig = (fun ( lid ) -> (match ((let _68_18419 = (sigmap env)
in (Support.Microsoft.FStar.Util.smap_try_find _68_18419 lid.Microsoft_FStar_Absyn_Syntax.str))) with
| Some ((Microsoft_FStar_Absyn_Syntax.Sig_let (_39_389), _39_392)) -> begin
(let _68_18421 = (let _68_18420 = (Microsoft_FStar_Absyn_Syntax.range_of_lid lid)
in (Microsoft_FStar_Absyn_Util.fvar None lid _68_18420))
in Some (_68_18421))
end
| _39_396 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))

let try_lookup_lid' = (fun ( any_val ) ( exclude_interf ) ( env ) ( lid ) -> (match ((try_lookup_name any_val exclude_interf env lid)) with
| Some (Exp_name ((_39_402, e))) -> begin
Some (e)
end
| _39_408 -> begin
None
end))

let try_lookup_lid = (fun ( env ) ( l ) -> (try_lookup_lid' env.iface false env l))

let try_lookup_datacon = (fun ( env ) ( lid ) -> (let find_in_sig = (fun ( lid ) -> (match ((let _68_18440 = (sigmap env)
in (Support.Microsoft.FStar.Util.smap_try_find _68_18440 lid.Microsoft_FStar_Absyn_Syntax.str))) with
| Some ((Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((_39_416, _39_418, quals, _39_421)), _39_425)) -> begin
(match ((Support.Prims.pipe_right quals (Support.Microsoft.FStar.Util.for_some (fun ( _39_8 ) -> (match (_39_8) with
| Microsoft_FStar_Absyn_Syntax.Assumption -> begin
true
end
| _39_431 -> begin
false
end))))) with
| true -> begin
(let _68_18442 = (Microsoft_FStar_Absyn_Util.fv lid)
in Some (_68_18442))
end
| false -> begin
None
end)
end
| Some ((Microsoft_FStar_Absyn_Syntax.Sig_datacon (_39_433), _39_436)) -> begin
(let _68_18443 = (Microsoft_FStar_Absyn_Util.fv lid)
in Some (_68_18443))
end
| _39_440 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))

let find_all_datacons = (fun ( env ) ( lid ) -> (let find_in_sig = (fun ( lid ) -> (match ((let _68_18450 = (sigmap env)
in (Support.Microsoft.FStar.Util.smap_try_find _68_18450 lid.Microsoft_FStar_Absyn_Syntax.str))) with
| Some ((Microsoft_FStar_Absyn_Syntax.Sig_tycon ((_39_446, _39_448, _39_450, _39_452, datas, _39_455, _39_457)), _39_461)) -> begin
Some (datas)
end
| _39_465 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))

type record =
{typename : Microsoft_FStar_Absyn_Syntax.lident; constrname : Microsoft_FStar_Absyn_Syntax.lident; parms : Microsoft_FStar_Absyn_Syntax.binders; fields : (Microsoft_FStar_Absyn_Syntax.fieldname * Microsoft_FStar_Absyn_Syntax.typ) list}

let is_Mkrecord = (fun ( _ ) -> (failwith ("Not yet implemented:is_Mkrecord")))

let record_cache = (Support.Microsoft.FStar.Util.mk_ref [])

let extract_record = (fun ( e ) ( _39_12 ) -> (match (_39_12) with
| Microsoft_FStar_Absyn_Syntax.Sig_bundle ((sigs, _39_475, _39_477, _39_479)) -> begin
(let is_rec = (Support.Microsoft.FStar.Util.for_some (fun ( _39_9 ) -> (match (_39_9) with
| (Microsoft_FStar_Absyn_Syntax.RecordType (_)) | (Microsoft_FStar_Absyn_Syntax.RecordConstructor (_)) -> begin
true
end
| _39_490 -> begin
false
end)))
in (let find_dc = (fun ( dc ) -> (Support.Prims.pipe_right sigs (Support.Microsoft.FStar.Util.find_opt (fun ( _39_10 ) -> (match (_39_10) with
| Microsoft_FStar_Absyn_Syntax.Sig_datacon ((lid, _39_497, _39_499, _39_501, _39_503, _39_505)) -> begin
(Microsoft_FStar_Absyn_Syntax.lid_equals dc lid)
end
| _39_509 -> begin
false
end)))))
in (Support.Prims.pipe_right sigs (Support.List.iter (fun ( _39_11 ) -> (match (_39_11) with
| Microsoft_FStar_Absyn_Syntax.Sig_tycon ((typename, parms, _39_514, _39_516, dc::[], tags, _39_521)) -> begin
(match ((is_rec tags)) with
| true -> begin
(match ((let _68_18474 = (find_dc dc)
in (Support.Prims.pipe_left Support.Microsoft.FStar.Util.must _68_18474))) with
| Microsoft_FStar_Absyn_Syntax.Sig_datacon ((constrname, t, _39_527, _39_529, _39_531, _39_533)) -> begin
(let formals = (match ((Microsoft_FStar_Absyn_Util.function_formals t)) with
| Some ((x, _39_538)) -> begin
x
end
| _39_542 -> begin
[]
end)
in (let fields = (Support.Prims.pipe_right formals (Support.List.collect (fun ( b ) -> (match (b) with
| (Support.Microsoft.FStar.Util.Inr (x), q) -> begin
(match (((Microsoft_FStar_Absyn_Syntax.is_null_binder b) || (q = Some (Microsoft_FStar_Absyn_Syntax.Implicit)))) with
| true -> begin
[]
end
| false -> begin
(let _68_18478 = (let _68_18477 = (let _68_18476 = (Microsoft_FStar_Absyn_Util.unmangle_field_name x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ppname)
in (qual constrname _68_18476))
in (_68_18477, x.Microsoft_FStar_Absyn_Syntax.sort))
in (_68_18478)::[])
end)
end
| _39_550 -> begin
[]
end))))
in (let record = {typename = typename; constrname = constrname; parms = parms; fields = fields}
in (let _68_18480 = (let _68_18479 = (Support.ST.read record_cache)
in (record)::_68_18479)
in (Support.ST.op_Colon_Equals record_cache _68_18480)))))
end
| _39_554 -> begin
()
end)
end
| false -> begin
()
end)
end
| _39_556 -> begin
()
end))))))
end
| _39_558 -> begin
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
(let _68_18491 = (aux tl)
in (hd)::_68_18491)
end))
in (aux ns)))
in (let find_in_cache = (fun ( fieldname ) -> (let _39_576 = (fieldname.Microsoft_FStar_Absyn_Syntax.ns, fieldname.Microsoft_FStar_Absyn_Syntax.ident)
in (match (_39_576) with
| (ns, fieldname) -> begin
(let _68_18496 = (Support.ST.read record_cache)
in (Support.Microsoft.FStar.Util.find_map _68_18496 (fun ( record ) -> (let constrname = record.constrname.Microsoft_FStar_Absyn_Syntax.ident
in (let ns = (maybe_add_constrname ns constrname)
in (let fname = (Microsoft_FStar_Absyn_Syntax.lid_of_ids (Support.List.append ns ((fieldname)::[])))
in (Support.Microsoft.FStar.Util.find_map record.fields (fun ( _39_584 ) -> (match (_39_584) with
| (f, _39_583) -> begin
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

let qualify_field_to_record = (fun ( env ) ( recd ) ( f ) -> (let qualify = (fun ( fieldname ) -> (let _39_592 = (fieldname.Microsoft_FStar_Absyn_Syntax.ns, fieldname.Microsoft_FStar_Absyn_Syntax.ident)
in (match (_39_592) with
| (ns, fieldname) -> begin
(let constrname = recd.constrname.Microsoft_FStar_Absyn_Syntax.ident
in (let fname = (Microsoft_FStar_Absyn_Syntax.lid_of_ids (Support.List.append (Support.List.append ns ((constrname)::[])) ((fieldname)::[])))
in (Support.Microsoft.FStar.Util.find_map recd.fields (fun ( _39_598 ) -> (match (_39_598) with
| (f, _39_597) -> begin
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
| Some (Knd_name ((_39_602, l))) -> begin
Some (l)
end
| _39_608 -> begin
None
end))

let is_kind_abbrev = (fun ( env ) ( l ) -> (match ((find_kind_abbrev env l)) with
| None -> begin
false
end
| Some (_39_613) -> begin
true
end))

let unique_name = (fun ( any_val ) ( exclude_if ) ( env ) ( lid ) -> (match ((try_lookup_lid' any_val exclude_if env lid)) with
| None -> begin
(match ((find_kind_abbrev env lid)) with
| None -> begin
true
end
| Some (_39_622) -> begin
false
end)
end
| Some (_39_625) -> begin
false
end))

let unique_typ_name = (fun ( env ) ( lid ) -> (match ((try_lookup_typ_name' true env lid)) with
| None -> begin
true
end
| Some (a) -> begin
false
end))

let unique = (fun ( any_val ) ( exclude_if ) ( env ) ( lid ) -> (let this_env = (let _39_636 = env
in {curmodule = _39_636.curmodule; modules = _39_636.modules; open_namespaces = []; sigaccum = _39_636.sigaccum; localbindings = _39_636.localbindings; recbindings = _39_636.recbindings; phase = _39_636.phase; sigmap = _39_636.sigmap; default_result_effect = _39_636.default_result_effect; iface = _39_636.iface; admitted_iface = _39_636.admitted_iface})
in ((unique_name any_val exclude_if this_env lid) && (unique_typ_name this_env lid))))

let gen_bvd = (fun ( _39_13 ) -> (match (_39_13) with
| Binding_typ_var (id) -> begin
(let _68_18537 = (let _68_18536 = (let _68_18535 = (Microsoft_FStar_Absyn_Util.genident (Some (id.Microsoft_FStar_Absyn_Syntax.idRange)))
in (id, _68_18535))
in (Microsoft_FStar_Absyn_Util.mkbvd _68_18536))
in Support.Microsoft.FStar.Util.Inl (_68_18537))
end
| Binding_var (id) -> begin
(let _68_18540 = (let _68_18539 = (let _68_18538 = (Microsoft_FStar_Absyn_Util.genident (Some (id.Microsoft_FStar_Absyn_Syntax.idRange)))
in (id, _68_18538))
in (Microsoft_FStar_Absyn_Util.mkbvd _68_18539))
in Support.Microsoft.FStar.Util.Inr (_68_18540))
end
| _39_645 -> begin
(failwith ("Tried to generate a bound variable for a type constructor"))
end))

let push_bvvdef = (fun ( env ) ( x ) -> (let b = Binding_var (x.Microsoft_FStar_Absyn_Syntax.ppname)
in (let _39_649 = env
in {curmodule = _39_649.curmodule; modules = _39_649.modules; open_namespaces = _39_649.open_namespaces; sigaccum = _39_649.sigaccum; localbindings = ((Support.Microsoft.FStar.Util.Inr (x), b))::env.localbindings; recbindings = _39_649.recbindings; phase = _39_649.phase; sigmap = _39_649.sigmap; default_result_effect = _39_649.default_result_effect; iface = _39_649.iface; admitted_iface = _39_649.admitted_iface})))

let push_btvdef = (fun ( env ) ( x ) -> (let b = Binding_typ_var (x.Microsoft_FStar_Absyn_Syntax.ppname)
in (let _39_654 = env
in {curmodule = _39_654.curmodule; modules = _39_654.modules; open_namespaces = _39_654.open_namespaces; sigaccum = _39_654.sigaccum; localbindings = ((Support.Microsoft.FStar.Util.Inl (x), b))::env.localbindings; recbindings = _39_654.recbindings; phase = _39_654.phase; sigmap = _39_654.sigmap; default_result_effect = _39_654.default_result_effect; iface = _39_654.iface; admitted_iface = _39_654.admitted_iface})))

let push_local_binding = (fun ( env ) ( b ) -> (let bvd = (gen_bvd b)
in ((let _39_659 = env
in {curmodule = _39_659.curmodule; modules = _39_659.modules; open_namespaces = _39_659.open_namespaces; sigaccum = _39_659.sigaccum; localbindings = ((bvd, b))::env.localbindings; recbindings = _39_659.recbindings; phase = _39_659.phase; sigmap = _39_659.sigmap; default_result_effect = _39_659.default_result_effect; iface = _39_659.iface; admitted_iface = _39_659.admitted_iface}), bvd)))

let push_local_tbinding = (fun ( env ) ( a ) -> (match ((push_local_binding env (Binding_typ_var (a)))) with
| (env, Support.Microsoft.FStar.Util.Inl (x)) -> begin
(env, x)
end
| _39_668 -> begin
(failwith ("impossible"))
end))

let push_local_vbinding = (fun ( env ) ( b ) -> (match ((push_local_binding env (Binding_var (b)))) with
| (env, Support.Microsoft.FStar.Util.Inr (x)) -> begin
(env, x)
end
| _39_676 -> begin
(failwith ("impossible"))
end))

let push_rec_binding = (fun ( env ) ( b ) -> (match (b) with
| (Binding_let (lid)) | (Binding_tycon (lid)) -> begin
(match ((unique false true env lid)) with
| true -> begin
(let _39_682 = env
in {curmodule = _39_682.curmodule; modules = _39_682.modules; open_namespaces = _39_682.open_namespaces; sigaccum = _39_682.sigaccum; localbindings = _39_682.localbindings; recbindings = (b)::env.recbindings; phase = _39_682.phase; sigmap = _39_682.sigmap; default_result_effect = _39_682.default_result_effect; iface = _39_682.iface; admitted_iface = _39_682.admitted_iface})
end
| false -> begin
(let _68_18567 = (let _68_18566 = (let _68_18565 = (Microsoft_FStar_Absyn_Syntax.range_of_lid lid)
in ((Support.String.strcat "Duplicate top-level names " lid.Microsoft_FStar_Absyn_Syntax.str), _68_18565))
in Microsoft_FStar_Absyn_Syntax.Error (_68_18566))
in (raise (_68_18567)))
end)
end
| _39_685 -> begin
(failwith ("Unexpected rec_binding"))
end))

let push_sigelt = (fun ( env ) ( s ) -> (let err = (fun ( l ) -> (let sopt = (let _68_18574 = (sigmap env)
in (Support.Microsoft.FStar.Util.smap_try_find _68_18574 l.Microsoft_FStar_Absyn_Syntax.str))
in (let r = (match (sopt) with
| Some ((se, _39_693)) -> begin
(match ((let _68_18575 = (Microsoft_FStar_Absyn_Util.lids_of_sigelt se)
in (Support.Microsoft.FStar.Util.find_opt (Microsoft_FStar_Absyn_Syntax.lid_equals l) _68_18575))) with
| Some (l) -> begin
(let _68_18576 = (Microsoft_FStar_Absyn_Syntax.range_of_lid l)
in (Support.Prims.pipe_left Support.Microsoft.FStar.Range.string_of_range _68_18576))
end
| None -> begin
"<unknown>"
end)
end
| None -> begin
"<unknown>"
end)
in (let _68_18581 = (let _68_18580 = (let _68_18579 = (let _68_18577 = (Microsoft_FStar_Absyn_Syntax.text_of_lid l)
in (Support.Microsoft.FStar.Util.format2 "Duplicate top-level names [%s]; previously declared at %s" _68_18577 r))
in (let _68_18578 = (Microsoft_FStar_Absyn_Syntax.range_of_lid l)
in (_68_18579, _68_18578)))
in Microsoft_FStar_Absyn_Syntax.Error (_68_18580))
in (raise (_68_18581))))))
in (let env = (let _39_711 = (match (s) with
| Microsoft_FStar_Absyn_Syntax.Sig_let (_39_702) -> begin
(false, true)
end
| Microsoft_FStar_Absyn_Syntax.Sig_bundle (_39_705) -> begin
(true, true)
end
| _39_708 -> begin
(false, false)
end)
in (match (_39_711) with
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
(let _39_715 = (extract_record env s)
in (let _39_717 = env
in {curmodule = _39_717.curmodule; modules = _39_717.modules; open_namespaces = _39_717.open_namespaces; sigaccum = (s)::env.sigaccum; localbindings = _39_717.localbindings; recbindings = _39_717.recbindings; phase = _39_717.phase; sigmap = _39_717.sigmap; default_result_effect = _39_717.default_result_effect; iface = _39_717.iface; admitted_iface = _39_717.admitted_iface}))
end
| Some (l) -> begin
(err l)
end))
end))
in (let _39_736 = (match (s) with
| Microsoft_FStar_Absyn_Syntax.Sig_bundle ((ses, _39_724, _39_726, _39_728)) -> begin
(let _68_18585 = (Support.List.map (fun ( se ) -> (let _68_18584 = (Microsoft_FStar_Absyn_Util.lids_of_sigelt se)
in (_68_18584, se))) ses)
in (env, _68_18585))
end
| _39_733 -> begin
(let _68_18588 = (let _68_18587 = (let _68_18586 = (Microsoft_FStar_Absyn_Util.lids_of_sigelt s)
in (_68_18586, s))
in (_68_18587)::[])
in (env, _68_18588))
end)
in (match (_39_736) with
| (env, lss) -> begin
(let _39_741 = (Support.Prims.pipe_right lss (Support.List.iter (fun ( _39_739 ) -> (match (_39_739) with
| (lids, se) -> begin
(Support.Prims.pipe_right lids (Support.List.iter (fun ( lid ) -> (let _68_18591 = (sigmap env)
in (Support.Microsoft.FStar.Util.smap_add _68_18591 lid.Microsoft_FStar_Absyn_Syntax.str (se, (env.iface && (not (env.admitted_iface)))))))))
end))))
in env)
end)))))

let push_namespace = (fun ( env ) ( lid ) -> (let _39_745 = env
in {curmodule = _39_745.curmodule; modules = _39_745.modules; open_namespaces = (lid)::env.open_namespaces; sigaccum = _39_745.sigaccum; localbindings = _39_745.localbindings; recbindings = _39_745.recbindings; phase = _39_745.phase; sigmap = _39_745.sigmap; default_result_effect = _39_745.default_result_effect; iface = _39_745.iface; admitted_iface = _39_745.admitted_iface}))

let is_type_lid = (fun ( env ) ( lid ) -> (let aux = (fun ( _39_750 ) -> (match (()) with
| () -> begin
(match ((try_lookup_typ_name' false env lid)) with
| Some (_39_752) -> begin
true
end
| _39_755 -> begin
false
end)
end))
in (match ((lid.Microsoft_FStar_Absyn_Syntax.ns = [])) with
| true -> begin
(match ((try_lookup_id env lid.Microsoft_FStar_Absyn_Syntax.ident)) with
| Some (_39_757) -> begin
false
end
| _39_760 -> begin
(aux ())
end)
end
| false -> begin
(aux ())
end)))

let check_admits = (fun ( nm ) ( env ) -> (let warn = (not ((let _68_18607 = (Support.ST.read Microsoft_FStar_Options.admit_fsi)
in (Support.Prims.pipe_right _68_18607 (Support.Microsoft.FStar.Util.for_some (fun ( l ) -> (nm.Microsoft_FStar_Absyn_Syntax.str = l)))))))
in (Support.Prims.pipe_right env.sigaccum (Support.List.iter (fun ( se ) -> (match (se) with
| Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((l, t, quals, r)) -> begin
(match ((try_lookup_lid env l)) with
| None -> begin
(let _39_773 = (match (warn) with
| true -> begin
(let _68_18612 = (let _68_18611 = (let _68_18609 = (Microsoft_FStar_Absyn_Syntax.range_of_lid l)
in (Support.Microsoft.FStar.Range.string_of_range _68_18609))
in (let _68_18610 = (Microsoft_FStar_Absyn_Print.sli l)
in (Support.Microsoft.FStar.Util.format2 "%s: Warning: Admitting %s without a definition\n" _68_18611 _68_18610)))
in (Support.Microsoft.FStar.Util.print_string _68_18612))
end
| false -> begin
()
end)
in (let _68_18613 = (sigmap env)
in (Support.Microsoft.FStar.Util.smap_add _68_18613 l.Microsoft_FStar_Absyn_Syntax.str (Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((l, t, (Microsoft_FStar_Absyn_Syntax.Assumption)::quals, r)), false))))
end
| Some (_39_776) -> begin
()
end)
end
| _39_779 -> begin
()
end))))))

let finish = (fun ( env ) ( modul ) -> (let _39_817 = (Support.Prims.pipe_right modul.Microsoft_FStar_Absyn_Syntax.declarations (Support.List.iter (fun ( _39_15 ) -> (match (_39_15) with
| Microsoft_FStar_Absyn_Syntax.Sig_bundle ((ses, quals, _39_786, _39_788)) -> begin
(match ((Support.List.contains Microsoft_FStar_Absyn_Syntax.Private quals)) with
| true -> begin
(Support.Prims.pipe_right ses (Support.List.iter (fun ( _39_14 ) -> (match (_39_14) with
| Microsoft_FStar_Absyn_Syntax.Sig_datacon ((lid, _39_794, _39_796, _39_798, _39_800, _39_802)) -> begin
(let _68_18620 = (sigmap env)
in (Support.Microsoft.FStar.Util.smap_remove _68_18620 lid.Microsoft_FStar_Absyn_Syntax.str))
end
| _39_806 -> begin
()
end))))
end
| false -> begin
()
end)
end
| Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((lid, _39_809, quals, _39_812)) -> begin
(match ((Support.List.contains Microsoft_FStar_Absyn_Syntax.Private quals)) with
| true -> begin
(let _68_18621 = (sigmap env)
in (Support.Microsoft.FStar.Util.smap_remove _68_18621 lid.Microsoft_FStar_Absyn_Syntax.str))
end
| false -> begin
()
end)
end
| _39_816 -> begin
()
end))))
in (let _39_819 = env
in {curmodule = None; modules = ((modul.Microsoft_FStar_Absyn_Syntax.name, modul))::env.modules; open_namespaces = []; sigaccum = []; localbindings = []; recbindings = []; phase = Microsoft_FStar_Parser_AST.Un; sigmap = _39_819.sigmap; default_result_effect = _39_819.default_result_effect; iface = _39_819.iface; admitted_iface = _39_819.admitted_iface})))

let push = (fun ( env ) -> (let _39_822 = env
in (let _68_18626 = (let _68_18625 = (let _68_18624 = (sigmap env)
in (Support.Microsoft.FStar.Util.smap_copy _68_18624))
in (_68_18625)::env.sigmap)
in {curmodule = _39_822.curmodule; modules = _39_822.modules; open_namespaces = _39_822.open_namespaces; sigaccum = _39_822.sigaccum; localbindings = _39_822.localbindings; recbindings = _39_822.recbindings; phase = _39_822.phase; sigmap = _68_18626; default_result_effect = _39_822.default_result_effect; iface = _39_822.iface; admitted_iface = _39_822.admitted_iface})))

let mark = (fun ( env ) -> (push env))

let reset_mark = (fun ( env ) -> (let _39_826 = env
in (let _68_18631 = (Support.List.tl env.sigmap)
in {curmodule = _39_826.curmodule; modules = _39_826.modules; open_namespaces = _39_826.open_namespaces; sigaccum = _39_826.sigaccum; localbindings = _39_826.localbindings; recbindings = _39_826.recbindings; phase = _39_826.phase; sigmap = _68_18631; default_result_effect = _39_826.default_result_effect; iface = _39_826.iface; admitted_iface = _39_826.admitted_iface})))

let commit_mark = (fun ( env ) -> (match (env.sigmap) with
| hd::_39_831::tl -> begin
(let _39_835 = env
in {curmodule = _39_835.curmodule; modules = _39_835.modules; open_namespaces = _39_835.open_namespaces; sigaccum = _39_835.sigaccum; localbindings = _39_835.localbindings; recbindings = _39_835.recbindings; phase = _39_835.phase; sigmap = (hd)::tl; default_result_effect = _39_835.default_result_effect; iface = _39_835.iface; admitted_iface = _39_835.admitted_iface})
end
| _39_838 -> begin
(failwith ("Impossible"))
end))

let pop = (fun ( env ) -> (match (env.sigmap) with
| _39_842::maps -> begin
(let _39_844 = env
in {curmodule = _39_844.curmodule; modules = _39_844.modules; open_namespaces = _39_844.open_namespaces; sigaccum = _39_844.sigaccum; localbindings = _39_844.localbindings; recbindings = _39_844.recbindings; phase = _39_844.phase; sigmap = maps; default_result_effect = _39_844.default_result_effect; iface = _39_844.iface; admitted_iface = _39_844.admitted_iface})
end
| _39_847 -> begin
(failwith ("No more modules to pop"))
end))

let finish_module_or_interface = (fun ( env ) ( modul ) -> (let _39_850 = (match ((not (modul.Microsoft_FStar_Absyn_Syntax.is_interface))) with
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
(Microsoft_FStar_Absyn_Const.prims_lid)::[]
end)
in (let _39_859 = env
in {curmodule = Some (mname); modules = _39_859.modules; open_namespaces = open_ns; sigaccum = _39_859.sigaccum; localbindings = _39_859.localbindings; recbindings = _39_859.recbindings; phase = _39_859.phase; sigmap = env.sigmap; default_result_effect = _39_859.default_result_effect; iface = intf; admitted_iface = admitted})))
in (match ((Support.Prims.pipe_right env.modules (Support.Microsoft.FStar.Util.find_opt (fun ( _39_864 ) -> (match (_39_864) with
| (l, _39_863) -> begin
(Microsoft_FStar_Absyn_Syntax.lid_equals l mname)
end))))) with
| None -> begin
(prep env)
end
| Some ((_39_867, m)) -> begin
(let _39_871 = (match (intf) with
| true -> begin
(let _68_18654 = (let _68_18653 = (let _68_18652 = (Support.Microsoft.FStar.Util.format1 "Duplicate module or interface name: %s" mname.Microsoft_FStar_Absyn_Syntax.str)
in (let _68_18651 = (Microsoft_FStar_Absyn_Syntax.range_of_lid mname)
in (_68_18652, _68_18651)))
in Microsoft_FStar_Absyn_Syntax.Error (_68_18653))
in (raise (_68_18654)))
end
| false -> begin
()
end)
in (prep env))
end)))

let enter_monad_scope = (fun ( env ) ( mname ) -> (let curmod = (current_module env)
in (let mscope = (Microsoft_FStar_Absyn_Syntax.lid_of_ids (Support.List.append curmod.Microsoft_FStar_Absyn_Syntax.ns ((curmod.Microsoft_FStar_Absyn_Syntax.ident)::(mname)::[])))
in (let _39_877 = env
in {curmodule = Some (mscope); modules = _39_877.modules; open_namespaces = (curmod)::env.open_namespaces; sigaccum = _39_877.sigaccum; localbindings = _39_877.localbindings; recbindings = _39_877.recbindings; phase = _39_877.phase; sigmap = _39_877.sigmap; default_result_effect = _39_877.default_result_effect; iface = _39_877.iface; admitted_iface = _39_877.admitted_iface}))))

let exit_monad_scope = (fun ( env0 ) ( env ) -> (let _39_881 = env
in {curmodule = env0.curmodule; modules = _39_881.modules; open_namespaces = env0.open_namespaces; sigaccum = _39_881.sigaccum; localbindings = _39_881.localbindings; recbindings = _39_881.recbindings; phase = _39_881.phase; sigmap = _39_881.sigmap; default_result_effect = _39_881.default_result_effect; iface = _39_881.iface; admitted_iface = _39_881.admitted_iface}))

let fail_or = (fun ( env ) ( lookup ) ( lid ) -> (match ((lookup lid)) with
| None -> begin
(let r = (match ((try_lookup_name true false env lid)) with
| None -> begin
None
end
| (Some (Knd_name ((o, _)))) | (Some (Eff_name ((o, _)))) | (Some (Typ_name ((o, _)))) | (Some (Exp_name ((o, _)))) -> begin
(let _68_18669 = (range_of_occurrence o)
in Some (_68_18669))
end)
in (let msg = (match (r) with
| None -> begin
""
end
| Some (r) -> begin
(let _68_18670 = (Support.Microsoft.FStar.Range.string_of_range r)
in (Support.Microsoft.FStar.Util.format1 "(Possible clash with related name at %s)" _68_18670))
end)
in (let _68_18675 = (let _68_18674 = (let _68_18673 = (let _68_18671 = (Microsoft_FStar_Absyn_Syntax.text_of_lid lid)
in (Support.Microsoft.FStar.Util.format2 "Identifier not found: [%s] %s" _68_18671 msg))
in (let _68_18672 = (Microsoft_FStar_Absyn_Syntax.range_of_lid lid)
in (_68_18673, _68_18672)))
in Microsoft_FStar_Absyn_Syntax.Error (_68_18674))
in (raise (_68_18675)))))
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




