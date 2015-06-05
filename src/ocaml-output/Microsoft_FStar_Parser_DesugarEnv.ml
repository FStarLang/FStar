
type binding =
| Binding_typ_var of Microsoft_FStar_Absyn_Syntax.ident
| Binding_var of Microsoft_FStar_Absyn_Syntax.ident
| Binding_let of Microsoft_FStar_Absyn_Syntax.lident
| Binding_tycon of Microsoft_FStar_Absyn_Syntax.lident

type kind_abbrev =
(Microsoft_FStar_Absyn_Syntax.lident * (Microsoft_FStar_Absyn_Syntax.btvdef, Microsoft_FStar_Absyn_Syntax.bvvdef) Support.Microsoft.FStar.Util.either list * Microsoft_FStar_Absyn_Syntax.knd)

type env =
{curmodule : Microsoft_FStar_Absyn_Syntax.lident option; modules : (Microsoft_FStar_Absyn_Syntax.lident * Microsoft_FStar_Absyn_Syntax.modul) list; open_namespaces : Microsoft_FStar_Absyn_Syntax.lident list; sigaccum : Microsoft_FStar_Absyn_Syntax.sigelts; localbindings : ((Microsoft_FStar_Absyn_Syntax.btvdef, Microsoft_FStar_Absyn_Syntax.bvvdef) Support.Microsoft.FStar.Util.either * binding) list; recbindings : binding list; phase : Microsoft_FStar_Parser_AST.level; sigmap : (Microsoft_FStar_Absyn_Syntax.sigelt * bool) Support.Microsoft.FStar.Util.smap list; default_result_effect : Microsoft_FStar_Absyn_Syntax.typ  ->  Support.Microsoft.FStar.Range.range  ->  Microsoft_FStar_Absyn_Syntax.comp; iface : bool; admitted_iface : bool}

let open_modules = (fun e -> e.modules)

let current_module = (fun env -> (match (env.curmodule) with
| None -> begin
(failwith ("Unset current module"))
end
| Some (m) -> begin
m
end))

let qual = (fun lid id -> (Microsoft_FStar_Absyn_Util.set_lid_range (Microsoft_FStar_Absyn_Syntax.lid_of_ids (Support.List.append lid.Microsoft_FStar_Absyn_Syntax.ns ((lid.Microsoft_FStar_Absyn_Syntax.ident)::(id)::[]))) id.Microsoft_FStar_Absyn_Syntax.idRange))

let qualify = (fun env id -> (qual (current_module env) id))

let qualify_lid = (fun env lid -> (let cur = (current_module env)
in (Microsoft_FStar_Absyn_Util.set_lid_range (Microsoft_FStar_Absyn_Syntax.lid_of_ids (Support.List.append (Support.List.append (Support.List.append cur.Microsoft_FStar_Absyn_Syntax.ns ((cur.Microsoft_FStar_Absyn_Syntax.ident)::[])) lid.Microsoft_FStar_Absyn_Syntax.ns) ((lid.Microsoft_FStar_Absyn_Syntax.ident)::[]))) (Microsoft_FStar_Absyn_Syntax.range_of_lid lid))))

let new_sigmap = (fun _116454 -> (match (_116454) with
| () -> begin
(Support.Microsoft.FStar.Util.smap_create 100)
end))

let empty_env = (fun _116455 -> (match (_116455) with
| () -> begin
{curmodule = None; modules = []; open_namespaces = []; sigaccum = []; localbindings = []; recbindings = []; phase = Microsoft_FStar_Parser_AST.Un; sigmap = ((new_sigmap ()))::[]; default_result_effect = Microsoft_FStar_Absyn_Util.ml_comp; iface = false; admitted_iface = false}
end))

let sigmap = (fun env -> (Support.List.hd env.sigmap))

let default_total = (fun env -> (let _116458 = env
in {curmodule = _116458.curmodule; modules = _116458.modules; open_namespaces = _116458.open_namespaces; sigaccum = _116458.sigaccum; localbindings = _116458.localbindings; recbindings = _116458.recbindings; phase = _116458.phase; sigmap = _116458.sigmap; default_result_effect = (fun t _116461 -> (Microsoft_FStar_Absyn_Syntax.mk_Total t)); iface = _116458.iface; admitted_iface = _116458.admitted_iface}))

let default_ml = (fun env -> (let _116464 = env
in {curmodule = _116464.curmodule; modules = _116464.modules; open_namespaces = _116464.open_namespaces; sigaccum = _116464.sigaccum; localbindings = _116464.localbindings; recbindings = _116464.recbindings; phase = _116464.phase; sigmap = _116464.sigmap; default_result_effect = Microsoft_FStar_Absyn_Util.ml_comp; iface = _116464.iface; admitted_iface = _116464.admitted_iface}))

let range_of_binding = (fun _116411 -> (match (_116411) with
| (Binding_typ_var (id)) | (Binding_var (id)) -> begin
id.Microsoft_FStar_Absyn_Syntax.idRange
end
| (Binding_let (lid)) | (Binding_tycon (lid)) -> begin
(Microsoft_FStar_Absyn_Syntax.range_of_lid lid)
end))

let try_lookup_typ_var = (fun env id -> (let fopt = (Support.List.tryFind (fun _116478 -> (match (_116478) with
| (_, b) -> begin
(match (b) with
| (Binding_typ_var (id')) | (Binding_var (id')) -> begin
(id.Microsoft_FStar_Absyn_Syntax.idText = id'.Microsoft_FStar_Absyn_Syntax.idText)
end
| _ -> begin
false
end)
end)) env.localbindings)
in (match (fopt) with
| Some ((Support.Microsoft.FStar.Util.Inl (bvd), Binding_typ_var (_))) -> begin
Some ((Microsoft_FStar_Absyn_Util.bvd_to_typ (Microsoft_FStar_Absyn_Util.set_bvd_range bvd id.Microsoft_FStar_Absyn_Syntax.idRange) Microsoft_FStar_Absyn_Syntax.kun))
end
| _ -> begin
None
end)))

let resolve_in_open_namespaces = (fun env lid finder -> (let aux = (fun namespaces -> (match ((finder lid)) with
| Some (r) -> begin
Some (r)
end
| _ -> begin
(let ids = (Microsoft_FStar_Absyn_Syntax.ids_of_lid lid)
in (Support.Microsoft.FStar.Util.find_map namespaces (fun ns -> (let full_name = (Microsoft_FStar_Absyn_Syntax.lid_of_ids (Support.List.append (Microsoft_FStar_Absyn_Syntax.ids_of_lid ns) ids))
in (finder full_name)))))
end))
in (aux (((current_module env))::env.open_namespaces))))

let unmangleMap = (("op_ColonColon", "Cons"))::(("not", "op_Negation"))::[]

let unmangleOpName = (fun id -> (Support.Microsoft.FStar.Util.find_map unmangleMap (fun _116510 -> (match (_116510) with
| (x, y) -> begin
if (id.Microsoft_FStar_Absyn_Syntax.idText = x) then begin
Some ((Microsoft_FStar_Absyn_Syntax.lid_of_path (("Prims")::(y)::[]) id.Microsoft_FStar_Absyn_Syntax.idRange))
end else begin
None
end
end))))

let try_lookup_id' = (fun env id -> (match ((unmangleOpName id)) with
| Some (l) -> begin
Some ((l, (Microsoft_FStar_Absyn_Syntax.mk_Exp_fvar ((Microsoft_FStar_Absyn_Util.fv l), false) None id.Microsoft_FStar_Absyn_Syntax.idRange)))
end
| _ -> begin
(let found = (Support.Microsoft.FStar.Util.find_map env.localbindings (fun _116412 -> (match (_116412) with
| (Support.Microsoft.FStar.Util.Inl (_), Binding_typ_var (id')) when (id'.Microsoft_FStar_Absyn_Syntax.idText = id.Microsoft_FStar_Absyn_Syntax.idText) -> begin
Some (Support.Microsoft.FStar.Util.Inl (()))
end
| (Support.Microsoft.FStar.Util.Inr (bvd), Binding_var (id')) when (id'.Microsoft_FStar_Absyn_Syntax.idText = id.Microsoft_FStar_Absyn_Syntax.idText) -> begin
Some (Support.Microsoft.FStar.Util.Inr (((Microsoft_FStar_Absyn_Syntax.lid_of_ids ((id')::[])), (Microsoft_FStar_Absyn_Util.bvd_to_exp (Microsoft_FStar_Absyn_Util.set_bvd_range bvd id.Microsoft_FStar_Absyn_Syntax.idRange) Microsoft_FStar_Absyn_Syntax.tun))))
end
| _ -> begin
None
end)))
in (match (found) with
| Some (Support.Microsoft.FStar.Util.Inr (x)) -> begin
Some (x)
end
| _ -> begin
None
end))
end))

let try_lookup_id = (fun env id -> (match ((try_lookup_id' env id)) with
| Some ((_, e)) -> begin
Some (e)
end
| None -> begin
None
end))

type occurrence =
| OSig of Microsoft_FStar_Absyn_Syntax.sigelt
| OLet of Microsoft_FStar_Absyn_Syntax.lident
| ORec of Microsoft_FStar_Absyn_Syntax.lident

let range_of_occurrence = (fun _116413 -> (match (_116413) with
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

let try_lookup_name = (fun any_val exclude_interf env lid -> (let find_in_sig = (fun lid -> (match ((Support.Microsoft.FStar.Util.smap_try_find (sigmap env) lid.Microsoft_FStar_Absyn_Syntax.str)) with
| Some ((_, true)) when exclude_interf -> begin
None
end
| None -> begin
None
end
| Some ((se, _)) -> begin
(match (se) with
| (Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_tycon (_)) -> begin
Some (Typ_name ((OSig (se), (Microsoft_FStar_Absyn_Util.ftv lid Microsoft_FStar_Absyn_Syntax.kun))))
end
| Microsoft_FStar_Absyn_Syntax.Sig_kind_abbrev (_) -> begin
Some (Knd_name ((OSig (se), lid)))
end
| Microsoft_FStar_Absyn_Syntax.Sig_new_effect ((ne, _)) -> begin
Some (Eff_name ((OSig (se), (Microsoft_FStar_Absyn_Util.set_lid_range ne.Microsoft_FStar_Absyn_Syntax.mname (Microsoft_FStar_Absyn_Syntax.range_of_lid lid)))))
end
| Microsoft_FStar_Absyn_Syntax.Sig_effect_abbrev (_) -> begin
Some (Eff_name ((OSig (se), lid)))
end
| Microsoft_FStar_Absyn_Syntax.Sig_datacon (_) -> begin
Some (Exp_name ((OSig (se), (Microsoft_FStar_Absyn_Util.fvar true lid (Microsoft_FStar_Absyn_Syntax.range_of_lid lid)))))
end
| Microsoft_FStar_Absyn_Syntax.Sig_let (_) -> begin
Some (Exp_name ((OSig (se), (Microsoft_FStar_Absyn_Util.fvar false lid (Microsoft_FStar_Absyn_Syntax.range_of_lid lid)))))
end
| Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((_, _, quals, _)) -> begin
if (any_val || ((Support.Microsoft.FStar.Util.for_some (fun _116414 -> (match (_116414) with
| Microsoft_FStar_Absyn_Syntax.Assumption -> begin
true
end
| _ -> begin
false
end))) quals)) then begin
Some (Exp_name ((OSig (se), (Microsoft_FStar_Absyn_Util.fvar false lid (Microsoft_FStar_Absyn_Syntax.range_of_lid lid)))))
end else begin
None
end
end
| _ -> begin
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
in (Support.Microsoft.FStar.Util.find_map env.recbindings (fun _116415 -> (match (_116415) with
| Binding_let (l) when (Microsoft_FStar_Absyn_Syntax.lid_equals l recname) -> begin
Some (Exp_name ((ORec (l), (Microsoft_FStar_Absyn_Util.fvar false recname (Microsoft_FStar_Absyn_Syntax.range_of_lid recname)))))
end
| Binding_tycon (l) when (Microsoft_FStar_Absyn_Syntax.lid_equals l recname) -> begin
Some (Typ_name ((ORec (l), (Microsoft_FStar_Absyn_Util.ftv recname Microsoft_FStar_Absyn_Syntax.kun))))
end
| _ -> begin
None
end))))
end)
end
| _ -> begin
None
end)
in (match (found_id) with
| Some (_) -> begin
found_id
end
| _ -> begin
(resolve_in_open_namespaces env lid find_in_sig)
end))))

let try_lookup_typ_name' = (fun exclude_interf env lid -> (match ((try_lookup_name true exclude_interf env lid)) with
| Some (Typ_name ((_, t))) -> begin
Some (t)
end
| Some (Eff_name ((_, l))) -> begin
Some ((Microsoft_FStar_Absyn_Util.ftv l Microsoft_FStar_Absyn_Syntax.mk_Kind_unknown))
end
| _ -> begin
None
end))

let try_lookup_typ_name = (fun env l -> (try_lookup_typ_name' (not (env.iface)) env l))

let try_lookup_effect_name' = (fun exclude_interf env lid -> (match ((try_lookup_name true exclude_interf env lid)) with
| Some (Eff_name ((o, l))) -> begin
Some ((o, l))
end
| _ -> begin
None
end))

let try_lookup_effect_name = (fun env l -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some ((o, l)) -> begin
Some (l)
end
| _ -> begin
None
end))

let try_lookup_effect_defn = (fun env l -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some ((OSig (Microsoft_FStar_Absyn_Syntax.Sig_new_effect ((ne, _))), _)) -> begin
Some (ne)
end
| _ -> begin
None
end))

let is_effect_name = (fun env lid -> (match ((try_lookup_effect_name env lid)) with
| None -> begin
false
end
| Some (_) -> begin
true
end))

let try_resolve_typ_abbrev = (fun env lid -> (let find_in_sig = (fun lid -> (match ((Support.Microsoft.FStar.Util.smap_try_find (sigmap env) lid.Microsoft_FStar_Absyn_Syntax.str)) with
| Some ((Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev ((lid, tps, k, def, _, _)), _)) -> begin
(let t = (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_named (((Microsoft_FStar_Absyn_Util.close_with_lam tps def), lid))))
in Some (t))
end
| _ -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))

let lookup_letbinding_quals = (fun env lid -> (let find_in_sig = (fun lid -> (match ((Support.Microsoft.FStar.Util.smap_try_find (sigmap env) lid.Microsoft_FStar_Absyn_Syntax.str)) with
| Some ((Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((lid, _, quals, _)), _)) -> begin
Some (quals)
end
| _ -> begin
None
end))
in (match ((resolve_in_open_namespaces env lid find_in_sig)) with
| Some (quals) -> begin
quals
end
| _ -> begin
[]
end)))

let try_lookup_module = (fun env path -> (match ((Support.List.tryFind (fun _116746 -> (match (_116746) with
| (mlid, modul) -> begin
((Microsoft_FStar_Absyn_Syntax.path_of_lid mlid) = path)
end)) env.modules)) with
| Some ((_, modul)) -> begin
Some (modul)
end
| None -> begin
None
end))

let try_lookup_let = (fun env lid -> (let find_in_sig = (fun lid -> (match ((Support.Microsoft.FStar.Util.smap_try_find (sigmap env) lid.Microsoft_FStar_Absyn_Syntax.str)) with
| Some ((Microsoft_FStar_Absyn_Syntax.Sig_let (_), _)) -> begin
Some ((Microsoft_FStar_Absyn_Util.fvar false lid (Microsoft_FStar_Absyn_Syntax.range_of_lid lid)))
end
| _ -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))

let try_lookup_lid' = (fun any_val exclude_interf env lid -> (match ((try_lookup_name any_val exclude_interf env lid)) with
| Some (Exp_name ((_, e))) -> begin
Some (e)
end
| _ -> begin
None
end))

let try_lookup_lid = (fun env l -> (try_lookup_lid' env.iface false env l))

let try_lookup_datacon = (fun env lid -> (let find_in_sig = (fun lid -> (match ((Support.Microsoft.FStar.Util.smap_try_find (sigmap env) lid.Microsoft_FStar_Absyn_Syntax.str)) with
| Some ((Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((_, _, quals, _)), _)) -> begin
if ((Support.Microsoft.FStar.Util.for_some (fun _116416 -> (match (_116416) with
| Microsoft_FStar_Absyn_Syntax.Assumption -> begin
true
end
| _ -> begin
false
end))) quals) then begin
Some ((Microsoft_FStar_Absyn_Util.fv lid))
end else begin
None
end
end
| Some ((Microsoft_FStar_Absyn_Syntax.Sig_datacon (_), _)) -> begin
Some ((Microsoft_FStar_Absyn_Util.fv lid))
end
| _ -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))

let find_all_datacons = (fun env lid -> (let find_in_sig = (fun lid -> (match ((Support.Microsoft.FStar.Util.smap_try_find (sigmap env) lid.Microsoft_FStar_Absyn_Syntax.str)) with
| Some ((Microsoft_FStar_Absyn_Syntax.Sig_tycon ((_, _, _, _, datas, _, _)), _)) -> begin
Some (datas)
end
| _ -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))

type record =
{typename : Microsoft_FStar_Absyn_Syntax.lident; constrname : Microsoft_FStar_Absyn_Syntax.lident; parms : Microsoft_FStar_Absyn_Syntax.binders; fields : (Microsoft_FStar_Absyn_Syntax.fieldname * Microsoft_FStar_Absyn_Syntax.typ) list}

let record_cache = (Support.Microsoft.FStar.Util.mk_ref [])

let extract_record = (fun e _116420 -> (match (_116420) with
| Microsoft_FStar_Absyn_Syntax.Sig_bundle ((sigs, _, _, _)) -> begin
(let is_rec = (Support.Microsoft.FStar.Util.for_some (fun _116417 -> (match (_116417) with
| (Microsoft_FStar_Absyn_Syntax.RecordType (_)) | (Microsoft_FStar_Absyn_Syntax.RecordConstructor (_)) -> begin
true
end
| _ -> begin
false
end)))
in (let find_dc = (fun dc -> ((Support.Microsoft.FStar.Util.find_opt (fun _116418 -> (match (_116418) with
| Microsoft_FStar_Absyn_Syntax.Sig_datacon ((lid, _, _, _, _, _)) -> begin
(Microsoft_FStar_Absyn_Syntax.lid_equals dc lid)
end
| _ -> begin
false
end))) sigs))
in ((Support.List.iter (fun _116419 -> (match (_116419) with
| Microsoft_FStar_Absyn_Syntax.Sig_tycon ((typename, parms, _, _, dc::[], tags, _)) -> begin
if (is_rec tags) then begin
(match (((Support.Microsoft.FStar.Util.must) (find_dc dc))) with
| Microsoft_FStar_Absyn_Syntax.Sig_datacon ((constrname, t, _, _, _, _)) -> begin
(let formals = (match ((Microsoft_FStar_Absyn_Util.function_formals t)) with
| Some ((x, _)) -> begin
x
end
| _ -> begin
[]
end)
in (let fields = ((Support.List.collect (fun b -> (match (b) with
| (Support.Microsoft.FStar.Util.Inr (x), q) -> begin
if ((Microsoft_FStar_Absyn_Syntax.is_null_binder b) || (q = Some (Microsoft_FStar_Absyn_Syntax.Implicit))) then begin
[]
end else begin
(((qual constrname (Microsoft_FStar_Absyn_Util.unmangle_field_name x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ppname)), x.Microsoft_FStar_Absyn_Syntax.sort))::[]
end
end
| _ -> begin
[]
end))) formals)
in (let record = {typename = typename; constrname = constrname; parms = parms; fields = fields}
in (Support.ST.op_ColonEquals record_cache ((record)::(Support.ST.read record_cache))))))
end
| _ -> begin
()
end)
end
end
| _ -> begin
()
end))) sigs)))
end
| _ -> begin
()
end))

let try_lookup_record_by_field_name = (fun env fieldname -> (let maybe_add_constrname = (fun ns c -> (let rec aux = (fun ns -> (match (ns) with
| [] -> begin
(c)::[]
end
| c'::[] -> begin
if (c'.Microsoft_FStar_Absyn_Syntax.idText = c.Microsoft_FStar_Absyn_Syntax.idText) then begin
(c)::[]
end else begin
(c')::(c)::[]
end
end
| hd::tl -> begin
(hd)::(aux tl)
end))
in (aux ns)))
in (let find_in_cache = (fun fieldname -> (let _116945 = (fieldname.Microsoft_FStar_Absyn_Syntax.ns, fieldname.Microsoft_FStar_Absyn_Syntax.ident)
in (match (_116945) with
| (ns, fieldname) -> begin
(Support.Microsoft.FStar.Util.find_map (Support.ST.read record_cache) (fun record -> (let constrname = record.constrname.Microsoft_FStar_Absyn_Syntax.ident
in (let ns = (maybe_add_constrname ns constrname)
in (let fname = (Microsoft_FStar_Absyn_Syntax.lid_of_ids (Support.List.append ns ((fieldname)::[])))
in (Support.Microsoft.FStar.Util.find_map record.fields (fun _116953 -> (match (_116953) with
| (f, _) -> begin
if (Microsoft_FStar_Absyn_Syntax.lid_equals fname f) then begin
Some ((record, fname))
end else begin
None
end
end))))))))
end)))
in (resolve_in_open_namespaces env fieldname find_in_cache))))

let qualify_field_to_record = (fun env recd f -> (let qualify = (fun fieldname -> (let _116961 = (fieldname.Microsoft_FStar_Absyn_Syntax.ns, fieldname.Microsoft_FStar_Absyn_Syntax.ident)
in (match (_116961) with
| (ns, fieldname) -> begin
(let constrname = recd.constrname.Microsoft_FStar_Absyn_Syntax.ident
in (let fname = (Microsoft_FStar_Absyn_Syntax.lid_of_ids (Support.List.append (Support.List.append ns ((constrname)::[])) ((fieldname)::[])))
in (Support.Microsoft.FStar.Util.find_map recd.fields (fun _116967 -> (match (_116967) with
| (f, _) -> begin
if (Microsoft_FStar_Absyn_Syntax.lid_equals fname f) then begin
Some (fname)
end else begin
None
end
end)))))
end)))
in (resolve_in_open_namespaces env f qualify)))

let find_kind_abbrev = (fun env l -> (match ((try_lookup_name true (not (env.iface)) env l)) with
| Some (Knd_name ((_, l))) -> begin
Some (l)
end
| _ -> begin
None
end))

let is_kind_abbrev = (fun env l -> (match ((find_kind_abbrev env l)) with
| None -> begin
false
end
| Some (_) -> begin
true
end))

let unique_name = (fun any_val exclude_if env lid -> (match ((try_lookup_lid' any_val exclude_if env lid)) with
| None -> begin
(match ((find_kind_abbrev env lid)) with
| None -> begin
true
end
| Some (_) -> begin
false
end)
end
| Some (_) -> begin
false
end))

let unique_typ_name = (fun env lid -> (match ((try_lookup_typ_name' true env lid)) with
| None -> begin
true
end
| Some (a) -> begin
false
end))

let unique = (fun any_val exclude_if env lid -> (let this_env = (let _117005 = env
in {curmodule = _117005.curmodule; modules = _117005.modules; open_namespaces = []; sigaccum = _117005.sigaccum; localbindings = _117005.localbindings; recbindings = _117005.recbindings; phase = _117005.phase; sigmap = _117005.sigmap; default_result_effect = _117005.default_result_effect; iface = _117005.iface; admitted_iface = _117005.admitted_iface})
in ((unique_name any_val exclude_if this_env lid) && (unique_typ_name this_env lid))))

let gen_bvd = (fun _116421 -> (match (_116421) with
| Binding_typ_var (id) -> begin
Support.Microsoft.FStar.Util.Inl ((Microsoft_FStar_Absyn_Util.mkbvd (id, (Microsoft_FStar_Absyn_Util.genident (Some (id.Microsoft_FStar_Absyn_Syntax.idRange))))))
end
| Binding_var (id) -> begin
Support.Microsoft.FStar.Util.Inr ((Microsoft_FStar_Absyn_Util.mkbvd (id, (Microsoft_FStar_Absyn_Util.genident (Some (id.Microsoft_FStar_Absyn_Syntax.idRange))))))
end
| _ -> begin
(failwith ("Tried to generate a bound variable for a type constructor"))
end))

let push_bvvdef = (fun env x -> (let b = Binding_var (x.Microsoft_FStar_Absyn_Syntax.ppname)
in (let _117018 = env
in {curmodule = _117018.curmodule; modules = _117018.modules; open_namespaces = _117018.open_namespaces; sigaccum = _117018.sigaccum; localbindings = ((Support.Microsoft.FStar.Util.Inr (x), b))::env.localbindings; recbindings = _117018.recbindings; phase = _117018.phase; sigmap = _117018.sigmap; default_result_effect = _117018.default_result_effect; iface = _117018.iface; admitted_iface = _117018.admitted_iface})))

let push_btvdef = (fun env x -> (let b = Binding_typ_var (x.Microsoft_FStar_Absyn_Syntax.ppname)
in (let _117023 = env
in {curmodule = _117023.curmodule; modules = _117023.modules; open_namespaces = _117023.open_namespaces; sigaccum = _117023.sigaccum; localbindings = ((Support.Microsoft.FStar.Util.Inl (x), b))::env.localbindings; recbindings = _117023.recbindings; phase = _117023.phase; sigmap = _117023.sigmap; default_result_effect = _117023.default_result_effect; iface = _117023.iface; admitted_iface = _117023.admitted_iface})))

let push_local_binding = (fun env b -> (let bvd = (gen_bvd b)
in ((let _117028 = env
in {curmodule = _117028.curmodule; modules = _117028.modules; open_namespaces = _117028.open_namespaces; sigaccum = _117028.sigaccum; localbindings = ((bvd, b))::env.localbindings; recbindings = _117028.recbindings; phase = _117028.phase; sigmap = _117028.sigmap; default_result_effect = _117028.default_result_effect; iface = _117028.iface; admitted_iface = _117028.admitted_iface}), bvd)))

let push_local_tbinding = (fun env a -> (match ((push_local_binding env (Binding_typ_var (a)))) with
| (env, Support.Microsoft.FStar.Util.Inl (x)) -> begin
(env, x)
end
| _ -> begin
(failwith ("impossible"))
end))

let push_local_vbinding = (fun env b -> (match ((push_local_binding env (Binding_var (b)))) with
| (env, Support.Microsoft.FStar.Util.Inr (x)) -> begin
(env, x)
end
| _ -> begin
(failwith ("impossible"))
end))

let push_rec_binding = (fun env b -> (match (b) with
| (Binding_let (lid)) | (Binding_tycon (lid)) -> begin
if (unique false true env lid) then begin
(let _117051 = env
in {curmodule = _117051.curmodule; modules = _117051.modules; open_namespaces = _117051.open_namespaces; sigaccum = _117051.sigaccum; localbindings = _117051.localbindings; recbindings = (b)::env.recbindings; phase = _117051.phase; sigmap = _117051.sigmap; default_result_effect = _117051.default_result_effect; iface = _117051.iface; admitted_iface = _117051.admitted_iface})
end else begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (((Support.String.strcat "Duplicate top-level names " lid.Microsoft_FStar_Absyn_Syntax.str), (Microsoft_FStar_Absyn_Syntax.range_of_lid lid)))))
end
end
| _ -> begin
(failwith ("Unexpected rec_binding"))
end))

let push_sigelt = (fun env s -> (let err = (fun l -> (let sopt = (Support.Microsoft.FStar.Util.smap_try_find (sigmap env) l.Microsoft_FStar_Absyn_Syntax.str)
in (let r = (match (sopt) with
| Some ((se, _)) -> begin
(match ((Support.Microsoft.FStar.Util.find_opt (Microsoft_FStar_Absyn_Syntax.lid_equals l) (Microsoft_FStar_Absyn_Util.lids_of_sigelt se))) with
| Some (l) -> begin
(Support.Microsoft.FStar.Range.string_of_range (Microsoft_FStar_Absyn_Syntax.range_of_lid l))
end
| None -> begin
"<unknown>"
end)
end
| None -> begin
"<unknown>"
end)
in (raise (Microsoft_FStar_Absyn_Syntax.Error (((Support.Microsoft.FStar.Util.format2 "Duplicate top-level names [%s]; previously declared at %s" (Microsoft_FStar_Absyn_Syntax.text_of_lid l) r), (Microsoft_FStar_Absyn_Syntax.range_of_lid l))))))))
in (let env = (let _117080 = (match (s) with
| Microsoft_FStar_Absyn_Syntax.Sig_let (_) -> begin
(false, true)
end
| Microsoft_FStar_Absyn_Syntax.Sig_bundle (_) -> begin
(true, true)
end
| _ -> begin
(false, false)
end)
in (match (_117080) with
| (any_val, exclude_if) -> begin
(let lids = (Microsoft_FStar_Absyn_Util.lids_of_sigelt s)
in (match ((Support.Microsoft.FStar.Util.find_map lids (fun l -> if (not ((unique any_val exclude_if env l))) then begin
Some (l)
end else begin
None
end))) with
| None -> begin
(let _117084 = (extract_record env s)
in (let _117086 = env
in {curmodule = _117086.curmodule; modules = _117086.modules; open_namespaces = _117086.open_namespaces; sigaccum = (s)::env.sigaccum; localbindings = _117086.localbindings; recbindings = _117086.recbindings; phase = _117086.phase; sigmap = _117086.sigmap; default_result_effect = _117086.default_result_effect; iface = _117086.iface; admitted_iface = _117086.admitted_iface}))
end
| Some (l) -> begin
(err l)
end))
end))
in (let _117105 = (match (s) with
| Microsoft_FStar_Absyn_Syntax.Sig_bundle ((ses, _, _, _)) -> begin
(env, (Support.List.map (fun se -> ((Microsoft_FStar_Absyn_Util.lids_of_sigelt se), se)) ses))
end
| _ -> begin
(env, (((Microsoft_FStar_Absyn_Util.lids_of_sigelt s), s))::[])
end)
in (match (_117105) with
| (env, lss) -> begin
(let _117110 = ((Support.List.iter (fun _117108 -> (match (_117108) with
| (lids, se) -> begin
((Support.List.iter (fun lid -> (Support.Microsoft.FStar.Util.smap_add (sigmap env) lid.Microsoft_FStar_Absyn_Syntax.str (se, (env.iface && (not (env.admitted_iface))))))) lids)
end))) lss)
in env)
end)))))

let push_namespace = (fun env lid -> (let _117114 = env
in {curmodule = _117114.curmodule; modules = _117114.modules; open_namespaces = (lid)::env.open_namespaces; sigaccum = _117114.sigaccum; localbindings = _117114.localbindings; recbindings = _117114.recbindings; phase = _117114.phase; sigmap = _117114.sigmap; default_result_effect = _117114.default_result_effect; iface = _117114.iface; admitted_iface = _117114.admitted_iface}))

let is_type_lid = (fun env lid -> (let aux = (fun _117119 -> (match (_117119) with
| () -> begin
(match ((try_lookup_typ_name' false env lid)) with
| Some (_) -> begin
true
end
| _ -> begin
false
end)
end))
in if (lid.Microsoft_FStar_Absyn_Syntax.ns = []) then begin
(match ((try_lookup_id env lid.Microsoft_FStar_Absyn_Syntax.ident)) with
| Some (_) -> begin
false
end
| _ -> begin
(aux ())
end)
end else begin
(aux ())
end))

let check_admits = (fun nm env -> (let warn = (not (((Support.Microsoft.FStar.Util.for_some (fun l -> (nm.Microsoft_FStar_Absyn_Syntax.str = l))) (Support.ST.read Microsoft_FStar_Options.admit_fsi))))
in ((Support.List.iter (fun se -> (match (se) with
| Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((l, t, quals, r)) -> begin
(match ((try_lookup_lid env l)) with
| None -> begin
(let _117142 = if warn then begin
(Support.Microsoft.FStar.Util.print_string (Support.Microsoft.FStar.Util.format2 "%s: Warning: Admitting %s without a definition\n" (Support.Microsoft.FStar.Range.string_of_range (Microsoft_FStar_Absyn_Syntax.range_of_lid l)) (Microsoft_FStar_Absyn_Print.sli l)))
end
in (Support.Microsoft.FStar.Util.smap_add (sigmap env) l.Microsoft_FStar_Absyn_Syntax.str (Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((l, t, (Microsoft_FStar_Absyn_Syntax.Assumption)::quals, r)), false)))
end
| Some (_) -> begin
()
end)
end
| _ -> begin
()
end))) env.sigaccum)))

let finish = (fun env modul -> (let _117151 = env
in {curmodule = None; modules = ((modul.Microsoft_FStar_Absyn_Syntax.name, modul))::env.modules; open_namespaces = []; sigaccum = []; localbindings = []; recbindings = []; phase = Microsoft_FStar_Parser_AST.Un; sigmap = _117151.sigmap; default_result_effect = _117151.default_result_effect; iface = _117151.iface; admitted_iface = _117151.admitted_iface}))

let push = (fun env -> (let _117154 = env
in {curmodule = _117154.curmodule; modules = _117154.modules; open_namespaces = _117154.open_namespaces; sigaccum = _117154.sigaccum; localbindings = _117154.localbindings; recbindings = _117154.recbindings; phase = _117154.phase; sigmap = ((Support.Microsoft.FStar.Util.smap_copy (sigmap env)))::env.sigmap; default_result_effect = _117154.default_result_effect; iface = _117154.iface; admitted_iface = _117154.admitted_iface}))

let mark = (fun env -> (push env))

let reset_mark = (fun env -> (let _117158 = env
in {curmodule = _117158.curmodule; modules = _117158.modules; open_namespaces = _117158.open_namespaces; sigaccum = _117158.sigaccum; localbindings = _117158.localbindings; recbindings = _117158.recbindings; phase = _117158.phase; sigmap = (Support.List.tl env.sigmap); default_result_effect = _117158.default_result_effect; iface = _117158.iface; admitted_iface = _117158.admitted_iface}))

let commit_mark = (fun env -> (match (env.sigmap) with
| hd::_::tl -> begin
(let _117167 = env
in {curmodule = _117167.curmodule; modules = _117167.modules; open_namespaces = _117167.open_namespaces; sigaccum = _117167.sigaccum; localbindings = _117167.localbindings; recbindings = _117167.recbindings; phase = _117167.phase; sigmap = (hd)::tl; default_result_effect = _117167.default_result_effect; iface = _117167.iface; admitted_iface = _117167.admitted_iface})
end
| _ -> begin
(failwith ("Impossible"))
end))

let pop = (fun env -> (match (env.sigmap) with
| _::maps -> begin
(let _117176 = env
in {curmodule = _117176.curmodule; modules = _117176.modules; open_namespaces = _117176.open_namespaces; sigaccum = _117176.sigaccum; localbindings = _117176.localbindings; recbindings = _117176.recbindings; phase = _117176.phase; sigmap = maps; default_result_effect = _117176.default_result_effect; iface = _117176.iface; admitted_iface = _117176.admitted_iface})
end
| _ -> begin
(failwith ("No more modules to pop"))
end))

let finish_module_or_interface = (fun env modul -> (let _117182 = if (not (modul.Microsoft_FStar_Absyn_Syntax.is_interface)) then begin
(check_admits modul.Microsoft_FStar_Absyn_Syntax.name env)
end
in (finish env modul)))

let prepare_module_or_interface = (fun intf admitted env mname -> (let prep = (fun env -> (let open_ns = if (Microsoft_FStar_Absyn_Syntax.lid_equals mname Microsoft_FStar_Absyn_Const.prims_lid) then begin
[]
end else begin
(Microsoft_FStar_Absyn_Const.prims_lid)::[]
end
in (let _117191 = env
in {curmodule = Some (mname); modules = _117191.modules; open_namespaces = open_ns; sigaccum = _117191.sigaccum; localbindings = _117191.localbindings; recbindings = _117191.recbindings; phase = _117191.phase; sigmap = env.sigmap; default_result_effect = _117191.default_result_effect; iface = intf; admitted_iface = admitted})))
in (match (((Support.Microsoft.FStar.Util.find_opt (fun _117196 -> (match (_117196) with
| (l, _) -> begin
(Microsoft_FStar_Absyn_Syntax.lid_equals l mname)
end))) env.modules)) with
| None -> begin
(prep env)
end
| Some ((_, m)) -> begin
(let _117203 = if intf then begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (((Support.Microsoft.FStar.Util.format1 "Duplicate module or interface name: %s" mname.Microsoft_FStar_Absyn_Syntax.str), (Microsoft_FStar_Absyn_Syntax.range_of_lid mname)))))
end
in (prep env))
end)))

let enter_monad_scope = (fun env mname -> (let curmod = (current_module env)
in (let mscope = (Microsoft_FStar_Absyn_Syntax.lid_of_ids (Support.List.append curmod.Microsoft_FStar_Absyn_Syntax.ns ((curmod.Microsoft_FStar_Absyn_Syntax.ident)::(mname)::[])))
in (let _117209 = env
in {curmodule = Some (mscope); modules = _117209.modules; open_namespaces = (curmod)::env.open_namespaces; sigaccum = _117209.sigaccum; localbindings = _117209.localbindings; recbindings = _117209.recbindings; phase = _117209.phase; sigmap = _117209.sigmap; default_result_effect = _117209.default_result_effect; iface = _117209.iface; admitted_iface = _117209.admitted_iface}))))

let exit_monad_scope = (fun env0 env -> (let _117213 = env
in {curmodule = env0.curmodule; modules = _117213.modules; open_namespaces = env0.open_namespaces; sigaccum = _117213.sigaccum; localbindings = _117213.localbindings; recbindings = _117213.recbindings; phase = _117213.phase; sigmap = _117213.sigmap; default_result_effect = _117213.default_result_effect; iface = _117213.iface; admitted_iface = _117213.admitted_iface}))

let fail_or = (fun env lookup lid -> (match ((lookup lid)) with
| None -> begin
(let r = (match ((try_lookup_name true false env lid)) with
| None -> begin
None
end
| (Some (Knd_name ((o, _)))) | (Some (Eff_name ((o, _)))) | (Some (Typ_name ((o, _)))) | (Some (Exp_name ((o, _)))) -> begin
Some ((range_of_occurrence o))
end)
in (let msg = (match (r) with
| None -> begin
""
end
| Some (r) -> begin
(Support.Microsoft.FStar.Util.format1 "(Possible clash with related name at %s)" (Support.Microsoft.FStar.Range.string_of_range r))
end)
in (raise (Microsoft_FStar_Absyn_Syntax.Error (((Support.Microsoft.FStar.Util.format2 "Identifier not found: [%s] %s" (Microsoft_FStar_Absyn_Syntax.text_of_lid lid) msg), (Microsoft_FStar_Absyn_Syntax.range_of_lid lid)))))))
end
| Some (r) -> begin
r
end))

let fail_or2 = (fun lookup id -> (match ((lookup id)) with
| None -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (((Support.String.strcat (Support.String.strcat "Identifier not found [" id.Microsoft_FStar_Absyn_Syntax.idText) "]"), id.Microsoft_FStar_Absyn_Syntax.idRange))))
end
| Some (r) -> begin
r
end))




