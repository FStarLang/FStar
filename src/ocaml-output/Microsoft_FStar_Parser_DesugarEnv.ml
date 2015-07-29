
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

let is_Mkenv = (fun ( _  :  env ) -> (failwith ("Not yet implemented")))

let open_modules = (fun ( e  :  env ) -> e.modules)

let current_module = (fun ( env  :  env ) -> (match (env.curmodule) with
| None -> begin
(failwith ("Unset current module"))
end
| Some (m) -> begin
m
end))

let qual = (fun ( lid  :  Microsoft_FStar_Absyn_Syntax.l__LongIdent ) ( id  :  Microsoft_FStar_Absyn_Syntax.ident ) -> (let _52_14848 = (Microsoft_FStar_Absyn_Syntax.lid_of_ids (Support.List.append lid.Microsoft_FStar_Absyn_Syntax.ns ((lid.Microsoft_FStar_Absyn_Syntax.ident)::(id)::[])))
in (Microsoft_FStar_Absyn_Util.set_lid_range _52_14848 id.Microsoft_FStar_Absyn_Syntax.idRange)))

let qualify = (fun ( env  :  env ) ( id  :  Microsoft_FStar_Absyn_Syntax.ident ) -> (let _52_14853 = (current_module env)
in (qual _52_14853 id)))

let qualify_lid = (fun ( env  :  env ) ( lid  :  Microsoft_FStar_Absyn_Syntax.lident ) -> (let cur = (current_module env)
in (let _52_14859 = (Microsoft_FStar_Absyn_Syntax.lid_of_ids (Support.List.append (Support.List.append (Support.List.append cur.Microsoft_FStar_Absyn_Syntax.ns ((cur.Microsoft_FStar_Absyn_Syntax.ident)::[])) lid.Microsoft_FStar_Absyn_Syntax.ns) ((lid.Microsoft_FStar_Absyn_Syntax.ident)::[])))
in (let _52_14858 = (Microsoft_FStar_Absyn_Syntax.range_of_lid lid)
in (Microsoft_FStar_Absyn_Util.set_lid_range _52_14859 _52_14858)))))

let new_sigmap = (fun ( _39_48  :  unit ) -> (match (()) with
| () -> begin
(Support.Microsoft.FStar.Util.smap_create 100)
end))

let empty_env = (fun ( _39_49  :  unit ) -> (match (()) with
| () -> begin
(let _52_14864 = (let _52_14863 = (new_sigmap ())
in (_52_14863)::[])
in {curmodule = None; modules = []; open_namespaces = []; sigaccum = []; localbindings = []; recbindings = []; phase = Microsoft_FStar_Parser_AST.Un; sigmap = _52_14864; default_result_effect = Microsoft_FStar_Absyn_Util.ml_comp; iface = false; admitted_iface = false})
end))

let sigmap = (fun ( env  :  env ) -> (Support.List.hd env.sigmap))

let default_total = (fun ( env  :  env ) -> (let _39_52 = env
in {curmodule = _39_52.curmodule; modules = _39_52.modules; open_namespaces = _39_52.open_namespaces; sigaccum = _39_52.sigaccum; localbindings = _39_52.localbindings; recbindings = _39_52.recbindings; phase = _39_52.phase; sigmap = _39_52.sigmap; default_result_effect = (fun ( t  :  Microsoft_FStar_Absyn_Syntax.typ ) ( _39_55  :  Support.Microsoft.FStar.Range.range ) -> (Microsoft_FStar_Absyn_Syntax.mk_Total t)); iface = _39_52.iface; admitted_iface = _39_52.admitted_iface}))

let default_ml = (fun ( env  :  env ) -> (let _39_58 = env
in {curmodule = _39_58.curmodule; modules = _39_58.modules; open_namespaces = _39_58.open_namespaces; sigaccum = _39_58.sigaccum; localbindings = _39_58.localbindings; recbindings = _39_58.recbindings; phase = _39_58.phase; sigmap = _39_58.sigmap; default_result_effect = Microsoft_FStar_Absyn_Util.ml_comp; iface = _39_58.iface; admitted_iface = _39_58.admitted_iface}))

let range_of_binding = (fun ( _39_1  :  binding ) -> (match (_39_1) with
| (Binding_typ_var (id)) | (Binding_var (id)) -> begin
id.Microsoft_FStar_Absyn_Syntax.idRange
end
| (Binding_let (lid)) | (Binding_tycon (lid)) -> begin
(Microsoft_FStar_Absyn_Syntax.range_of_lid lid)
end))

let try_lookup_typ_var = (fun ( env  :  env ) ( id  :  Microsoft_FStar_Absyn_Syntax.ident ) -> (let fopt = (Support.List.tryFind (fun ( _39_72  :  ((Microsoft_FStar_Absyn_Syntax.btvdef, Microsoft_FStar_Absyn_Syntax.bvvdef) Support.Microsoft.FStar.Util.either * binding) ) -> (match (_39_72) with
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
(let _52_14881 = (let _52_14880 = (Microsoft_FStar_Absyn_Util.set_bvd_range bvd id.Microsoft_FStar_Absyn_Syntax.idRange)
in (Microsoft_FStar_Absyn_Util.bvd_to_typ _52_14880 Microsoft_FStar_Absyn_Syntax.kun))
in Some (_52_14881))
end
| _ -> begin
None
end)))

let resolve_in_open_namespaces = (fun ( env  :  env ) ( lid  :  Microsoft_FStar_Absyn_Syntax.lident ) ( finder  :  Microsoft_FStar_Absyn_Syntax.lident  ->  'a option ) -> (let aux = (fun ( namespaces  :  Microsoft_FStar_Absyn_Syntax.lident list ) -> (match ((finder lid)) with
| Some (r) -> begin
Some (r)
end
| _ -> begin
(let ids = (Microsoft_FStar_Absyn_Syntax.ids_of_lid lid)
in (Support.Microsoft.FStar.Util.find_map namespaces (fun ( ns  :  Microsoft_FStar_Absyn_Syntax.lident ) -> (let full_name = (let _52_14896 = (let _52_14895 = (Microsoft_FStar_Absyn_Syntax.ids_of_lid ns)
in (Support.List.append _52_14895 ids))
in (Microsoft_FStar_Absyn_Syntax.lid_of_ids _52_14896))
in (finder full_name)))))
end))
in (let _52_14898 = (let _52_14897 = (current_module env)
in (_52_14897)::env.open_namespaces)
in (aux _52_14898))))

let unmangleMap = (("op_ColonColon", "Cons"))::(("not", "op_Negation"))::[]

let unmangleOpName = (fun ( id  :  Microsoft_FStar_Absyn_Syntax.ident ) -> (Support.Microsoft.FStar.Util.find_map unmangleMap (fun ( _39_104  :  (string * string) ) -> (match (_39_104) with
| (x, y) -> begin
(match ((id.Microsoft_FStar_Absyn_Syntax.idText = x)) with
| true -> begin
(let _52_14902 = (Microsoft_FStar_Absyn_Syntax.lid_of_path (("Prims")::(y)::[]) id.Microsoft_FStar_Absyn_Syntax.idRange)
in Some (_52_14902))
end
| false -> begin
None
end)
end))))

let try_lookup_id' = (fun ( env  :  env ) ( id  :  Microsoft_FStar_Absyn_Syntax.ident ) -> (match ((unmangleOpName id)) with
| Some (l) -> begin
(let _52_14910 = (let _52_14909 = (let _52_14908 = (let _52_14907 = (Microsoft_FStar_Absyn_Util.fv l)
in (_52_14907, None))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_fvar _52_14908 None id.Microsoft_FStar_Absyn_Syntax.idRange))
in (l, _52_14909))
in Some (_52_14910))
end
| _ -> begin
(let found = (Support.Microsoft.FStar.Util.find_map env.localbindings (fun ( _39_2  :  ((Microsoft_FStar_Absyn_Syntax.btvdef, Microsoft_FStar_Absyn_Syntax.bvvdef) Support.Microsoft.FStar.Util.either * binding) ) -> (match (_39_2) with
| (Support.Microsoft.FStar.Util.Inl (_), Binding_typ_var (id')) when (id'.Microsoft_FStar_Absyn_Syntax.idText = id.Microsoft_FStar_Absyn_Syntax.idText) -> begin
Some (Support.Microsoft.FStar.Util.Inl (()))
end
| (Support.Microsoft.FStar.Util.Inr (bvd), Binding_var (id')) when (id'.Microsoft_FStar_Absyn_Syntax.idText = id.Microsoft_FStar_Absyn_Syntax.idText) -> begin
(let _52_14916 = (let _52_14915 = (let _52_14914 = (Microsoft_FStar_Absyn_Syntax.lid_of_ids ((id')::[]))
in (let _52_14913 = (let _52_14912 = (Microsoft_FStar_Absyn_Util.set_bvd_range bvd id.Microsoft_FStar_Absyn_Syntax.idRange)
in (Microsoft_FStar_Absyn_Util.bvd_to_exp _52_14912 Microsoft_FStar_Absyn_Syntax.tun))
in (_52_14914, _52_14913)))
in Support.Microsoft.FStar.Util.Inr (_52_14915))
in Some (_52_14916))
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

let try_lookup_id = (fun ( env  :  env ) ( id  :  Microsoft_FStar_Absyn_Syntax.ident ) -> (match ((try_lookup_id' env id)) with
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

let range_of_occurrence = (fun ( _39_3  :  occurrence ) -> (match (_39_3) with
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

let fv_qual_of_se = (fun ( _39_5  :  Microsoft_FStar_Absyn_Syntax.sigelt ) -> (match (_39_5) with
| Microsoft_FStar_Absyn_Syntax.Sig_datacon ((_, _, (l, _, _), quals, _, _)) -> begin
(let qopt = (Support.Microsoft.FStar.Util.find_map quals (fun ( _39_4  :  Microsoft_FStar_Absyn_Syntax.qualifier ) -> (match (_39_4) with
| Microsoft_FStar_Absyn_Syntax.RecordConstructor (fs) -> begin
Some (Microsoft_FStar_Absyn_Syntax.Record_ctor ((l, fs)))
end
| _ -> begin
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
| Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((_, _, quals, _)) -> begin
None
end
| _ -> begin
None
end))

let try_lookup_name = (fun ( any_val  :  bool ) ( exclude_interf  :  bool ) ( env  :  env ) ( lid  :  Microsoft_FStar_Absyn_Syntax.lident ) -> (let find_in_sig = (fun ( lid  :  Microsoft_FStar_Absyn_Syntax.l__LongIdent ) -> (match ((let _52_14985 = (sigmap env)
in (Support.Microsoft.FStar.Util.smap_try_find _52_14985 lid.Microsoft_FStar_Absyn_Syntax.str))) with
| Some ((_, true)) when exclude_interf -> begin
None
end
| None -> begin
None
end
| Some ((se, _)) -> begin
(match (se) with
| (Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_tycon (_)) -> begin
(let _52_14988 = (let _52_14987 = (let _52_14986 = (Microsoft_FStar_Absyn_Util.ftv lid Microsoft_FStar_Absyn_Syntax.kun)
in (OSig (se), _52_14986))
in Typ_name (_52_14987))
in Some (_52_14988))
end
| Microsoft_FStar_Absyn_Syntax.Sig_kind_abbrev (_) -> begin
Some (Knd_name ((OSig (se), lid)))
end
| Microsoft_FStar_Absyn_Syntax.Sig_new_effect ((ne, _)) -> begin
(let _52_14992 = (let _52_14991 = (let _52_14990 = (let _52_14989 = (Microsoft_FStar_Absyn_Syntax.range_of_lid lid)
in (Microsoft_FStar_Absyn_Util.set_lid_range ne.Microsoft_FStar_Absyn_Syntax.mname _52_14989))
in (OSig (se), _52_14990))
in Eff_name (_52_14991))
in Some (_52_14992))
end
| Microsoft_FStar_Absyn_Syntax.Sig_effect_abbrev (_) -> begin
Some (Eff_name ((OSig (se), lid)))
end
| Microsoft_FStar_Absyn_Syntax.Sig_datacon (_) -> begin
(let _52_14997 = (let _52_14996 = (let _52_14995 = (let _52_14994 = (fv_qual_of_se se)
in (let _52_14993 = (Microsoft_FStar_Absyn_Syntax.range_of_lid lid)
in (Microsoft_FStar_Absyn_Util.fvar _52_14994 lid _52_14993)))
in (OSig (se), _52_14995))
in Exp_name (_52_14996))
in Some (_52_14997))
end
| Microsoft_FStar_Absyn_Syntax.Sig_let (_) -> begin
(let _52_15001 = (let _52_15000 = (let _52_14999 = (let _52_14998 = (Microsoft_FStar_Absyn_Syntax.range_of_lid lid)
in (Microsoft_FStar_Absyn_Util.fvar None lid _52_14998))
in (OSig (se), _52_14999))
in Exp_name (_52_15000))
in Some (_52_15001))
end
| Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((_, _, quals, _)) -> begin
(match ((let _52_15003 = (Support.Prims.pipe_right quals (Support.Microsoft.FStar.Util.for_some (fun ( _39_6  :  Microsoft_FStar_Absyn_Syntax.qualifier ) -> (match (_39_6) with
| Microsoft_FStar_Absyn_Syntax.Assumption -> begin
true
end
| _ -> begin
false
end))))
in (any_val || _52_15003))) with
| true -> begin
(let _52_15008 = (let _52_15007 = (let _52_15006 = (let _52_15005 = (fv_qual_of_se se)
in (let _52_15004 = (Microsoft_FStar_Absyn_Syntax.range_of_lid lid)
in (Microsoft_FStar_Absyn_Util.fvar _52_15005 lid _52_15004)))
in (OSig (se), _52_15006))
in Exp_name (_52_15007))
in Some (_52_15008))
end
| false -> begin
None
end)
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
in (Support.Microsoft.FStar.Util.find_map env.recbindings (fun ( _39_7  :  binding ) -> (match (_39_7) with
| Binding_let (l) when (Microsoft_FStar_Absyn_Syntax.lid_equals l recname) -> begin
(let _52_15013 = (let _52_15012 = (let _52_15011 = (let _52_15010 = (Microsoft_FStar_Absyn_Syntax.range_of_lid recname)
in (Microsoft_FStar_Absyn_Util.fvar None recname _52_15010))
in (ORec (l), _52_15011))
in Exp_name (_52_15012))
in Some (_52_15013))
end
| Binding_tycon (l) when (Microsoft_FStar_Absyn_Syntax.lid_equals l recname) -> begin
(let _52_15016 = (let _52_15015 = (let _52_15014 = (Microsoft_FStar_Absyn_Util.ftv recname Microsoft_FStar_Absyn_Syntax.kun)
in (ORec (l), _52_15014))
in Typ_name (_52_15015))
in Some (_52_15016))
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

let try_lookup_typ_name' = (fun ( exclude_interf  :  bool ) ( env  :  env ) ( lid  :  Microsoft_FStar_Absyn_Syntax.lident ) -> (match ((try_lookup_name true exclude_interf env lid)) with
| Some (Typ_name ((_, t))) -> begin
Some (t)
end
| Some (Eff_name ((_, l))) -> begin
(let _52_15023 = (Microsoft_FStar_Absyn_Util.ftv l Microsoft_FStar_Absyn_Syntax.mk_Kind_unknown)
in Some (_52_15023))
end
| _ -> begin
None
end))

let try_lookup_typ_name = (fun ( env  :  env ) ( l  :  Microsoft_FStar_Absyn_Syntax.lident ) -> (try_lookup_typ_name' (not (env.iface)) env l))

let try_lookup_effect_name' = (fun ( exclude_interf  :  bool ) ( env  :  env ) ( lid  :  Microsoft_FStar_Absyn_Syntax.lident ) -> (match ((try_lookup_name true exclude_interf env lid)) with
| Some (Eff_name ((o, l))) -> begin
Some ((o, l))
end
| _ -> begin
None
end))

let try_lookup_effect_name = (fun ( env  :  env ) ( l  :  Microsoft_FStar_Absyn_Syntax.lident ) -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some ((o, l)) -> begin
Some (l)
end
| _ -> begin
None
end))

let try_lookup_effect_defn = (fun ( env  :  env ) ( l  :  Microsoft_FStar_Absyn_Syntax.lident ) -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some ((OSig (Microsoft_FStar_Absyn_Syntax.Sig_new_effect ((ne, _))), _)) -> begin
Some (ne)
end
| _ -> begin
None
end))

let is_effect_name = (fun ( env  :  env ) ( lid  :  Microsoft_FStar_Absyn_Syntax.lident ) -> (match ((try_lookup_effect_name env lid)) with
| None -> begin
false
end
| Some (_) -> begin
true
end))

let try_resolve_typ_abbrev = (fun ( env  :  env ) ( lid  :  Microsoft_FStar_Absyn_Syntax.lident ) -> (let find_in_sig = (fun ( lid  :  Microsoft_FStar_Absyn_Syntax.l__LongIdent ) -> (match ((let _52_15052 = (sigmap env)
in (Support.Microsoft.FStar.Util.smap_try_find _52_15052 lid.Microsoft_FStar_Absyn_Syntax.str))) with
| Some ((Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev ((lid, tps, k, def, _, _)), _)) -> begin
(let t = (let _52_15055 = (let _52_15054 = (let _52_15053 = (Microsoft_FStar_Absyn_Util.close_with_lam tps def)
in (_52_15053, lid))
in Microsoft_FStar_Absyn_Syntax.Meta_named (_52_15054))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta _52_15055))
in Some (t))
end
| _ -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))

let lookup_letbinding_quals = (fun ( env  :  env ) ( lid  :  Microsoft_FStar_Absyn_Syntax.lident ) -> (let find_in_sig = (fun ( lid  :  Microsoft_FStar_Absyn_Syntax.l__LongIdent ) -> (match ((let _52_15062 = (sigmap env)
in (Support.Microsoft.FStar.Util.smap_try_find _52_15062 lid.Microsoft_FStar_Absyn_Syntax.str))) with
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

let try_lookup_module = (fun ( env  :  env ) ( path  :  Microsoft_FStar_Absyn_Syntax.path ) -> (match ((Support.List.tryFind (fun ( _39_377  :  (Microsoft_FStar_Absyn_Syntax.lident * Microsoft_FStar_Absyn_Syntax.modul) ) -> (match (_39_377) with
| (mlid, modul) -> begin
(let _52_15068 = (Microsoft_FStar_Absyn_Syntax.path_of_lid mlid)
in (_52_15068 = path))
end)) env.modules)) with
| Some ((_, modul)) -> begin
Some (modul)
end
| None -> begin
None
end))

let try_lookup_let = (fun ( env  :  env ) ( lid  :  Microsoft_FStar_Absyn_Syntax.lident ) -> (let find_in_sig = (fun ( lid  :  Microsoft_FStar_Absyn_Syntax.l__LongIdent ) -> (match ((let _52_15075 = (sigmap env)
in (Support.Microsoft.FStar.Util.smap_try_find _52_15075 lid.Microsoft_FStar_Absyn_Syntax.str))) with
| Some ((Microsoft_FStar_Absyn_Syntax.Sig_let (_), _)) -> begin
(let _52_15077 = (let _52_15076 = (Microsoft_FStar_Absyn_Syntax.range_of_lid lid)
in (Microsoft_FStar_Absyn_Util.fvar None lid _52_15076))
in Some (_52_15077))
end
| _ -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))

let try_lookup_lid' = (fun ( any_val  :  bool ) ( exclude_interf  :  bool ) ( env  :  env ) ( lid  :  Microsoft_FStar_Absyn_Syntax.lident ) -> (match ((try_lookup_name any_val exclude_interf env lid)) with
| Some (Exp_name ((_, e))) -> begin
Some (e)
end
| _ -> begin
None
end))

let try_lookup_lid = (fun ( env  :  env ) ( l  :  Microsoft_FStar_Absyn_Syntax.lident ) -> (try_lookup_lid' env.iface false env l))

let try_lookup_datacon = (fun ( env  :  env ) ( lid  :  Microsoft_FStar_Absyn_Syntax.lident ) -> (let find_in_sig = (fun ( lid  :  Microsoft_FStar_Absyn_Syntax.l__LongIdent ) -> (match ((let _52_15096 = (sigmap env)
in (Support.Microsoft.FStar.Util.smap_try_find _52_15096 lid.Microsoft_FStar_Absyn_Syntax.str))) with
| Some ((Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((_, _, quals, _)), _)) -> begin
(match ((Support.Prims.pipe_right quals (Support.Microsoft.FStar.Util.for_some (fun ( _39_8  :  Microsoft_FStar_Absyn_Syntax.qualifier ) -> (match (_39_8) with
| Microsoft_FStar_Absyn_Syntax.Assumption -> begin
true
end
| _ -> begin
false
end))))) with
| true -> begin
(let _52_15098 = (Microsoft_FStar_Absyn_Util.fv lid)
in Some (_52_15098))
end
| false -> begin
None
end)
end
| Some ((Microsoft_FStar_Absyn_Syntax.Sig_datacon (_), _)) -> begin
(let _52_15099 = (Microsoft_FStar_Absyn_Util.fv lid)
in Some (_52_15099))
end
| _ -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))

let find_all_datacons = (fun ( env  :  env ) ( lid  :  Microsoft_FStar_Absyn_Syntax.lident ) -> (let find_in_sig = (fun ( lid  :  Microsoft_FStar_Absyn_Syntax.l__LongIdent ) -> (match ((let _52_15106 = (sigmap env)
in (Support.Microsoft.FStar.Util.smap_try_find _52_15106 lid.Microsoft_FStar_Absyn_Syntax.str))) with
| Some ((Microsoft_FStar_Absyn_Syntax.Sig_tycon ((_, _, _, _, datas, _, _)), _)) -> begin
Some (datas)
end
| _ -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))

type record =
{typename : Microsoft_FStar_Absyn_Syntax.lident; constrname : Microsoft_FStar_Absyn_Syntax.lident; parms : Microsoft_FStar_Absyn_Syntax.binders; fields : (Microsoft_FStar_Absyn_Syntax.fieldname * Microsoft_FStar_Absyn_Syntax.typ) list}

let is_Mkrecord = (fun ( _  :  record ) -> (failwith ("Not yet implemented")))

let record_cache = (Support.Microsoft.FStar.Util.mk_ref [])

let extract_record = (fun ( e  :  env ) ( _39_12  :  Microsoft_FStar_Absyn_Syntax.sigelt ) -> (match (_39_12) with
| Microsoft_FStar_Absyn_Syntax.Sig_bundle ((sigs, _, _, _)) -> begin
(let is_rec = (Support.Microsoft.FStar.Util.for_some (fun ( _39_9  :  Microsoft_FStar_Absyn_Syntax.qualifier ) -> (match (_39_9) with
| (Microsoft_FStar_Absyn_Syntax.RecordType (_)) | (Microsoft_FStar_Absyn_Syntax.RecordConstructor (_)) -> begin
true
end
| _ -> begin
false
end)))
in (let find_dc = (fun ( dc  :  Microsoft_FStar_Absyn_Syntax.lident ) -> (Support.Prims.pipe_right sigs (Support.Microsoft.FStar.Util.find_opt (fun ( _39_10  :  Microsoft_FStar_Absyn_Syntax.sigelt ) -> (match (_39_10) with
| Microsoft_FStar_Absyn_Syntax.Sig_datacon ((lid, _, _, _, _, _)) -> begin
(Microsoft_FStar_Absyn_Syntax.lid_equals dc lid)
end
| _ -> begin
false
end)))))
in (Support.Prims.pipe_right sigs (Support.List.iter (fun ( _39_11  :  Microsoft_FStar_Absyn_Syntax.sigelt ) -> (match (_39_11) with
| Microsoft_FStar_Absyn_Syntax.Sig_tycon ((typename, parms, _, _, dc::[], tags, _)) -> begin
(match ((is_rec tags)) with
| true -> begin
(match ((let _52_15130 = (find_dc dc)
in (Support.Prims.pipe_left Support.Microsoft.FStar.Util.must _52_15130))) with
| Microsoft_FStar_Absyn_Syntax.Sig_datacon ((constrname, t, _, _, _, _)) -> begin
(let formals = (match ((Microsoft_FStar_Absyn_Util.function_formals t)) with
| Some ((x, _)) -> begin
x
end
| _ -> begin
[]
end)
in (let fields = (Support.Prims.pipe_right formals (Support.List.collect (fun ( b  :  ((((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.withinfo_t, ((Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.withinfo_t) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.arg_qualifier option) ) -> (match (b) with
| (Support.Microsoft.FStar.Util.Inr (x), q) -> begin
(match ((let _52_15132 = (Microsoft_FStar_Absyn_Syntax.is_null_binder b)
in (_52_15132 || (q = Some (Microsoft_FStar_Absyn_Syntax.Implicit))))) with
| true -> begin
[]
end
| false -> begin
(let _52_15135 = (let _52_15134 = (let _52_15133 = (Microsoft_FStar_Absyn_Util.unmangle_field_name x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ppname)
in (qual constrname _52_15133))
in (_52_15134, x.Microsoft_FStar_Absyn_Syntax.sort))
in (_52_15135)::[])
end)
end
| _ -> begin
[]
end))))
in (let record = {typename = typename; constrname = constrname; parms = parms; fields = fields}
in (let _52_15137 = (let _52_15136 = (Support.ST.read record_cache)
in (record)::_52_15136)
in (Support.ST.op_Colon_Equals record_cache _52_15137)))))
end
| _ -> begin
()
end)
end
| false -> begin
()
end)
end
| _ -> begin
()
end))))))
end
| _ -> begin
()
end))

let try_lookup_record_by_field_name = (fun ( env  :  env ) ( fieldname  :  Microsoft_FStar_Absyn_Syntax.lident ) -> (let maybe_add_constrname = (fun ( ns  :  Microsoft_FStar_Absyn_Syntax.ident list ) ( c  :  Microsoft_FStar_Absyn_Syntax.ident ) -> (let rec aux = (fun ( ns  :  Microsoft_FStar_Absyn_Syntax.ident list ) -> (match (ns) with
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
(let _52_15148 = (aux tl)
in (hd)::_52_15148)
end))
in (aux ns)))
in (let find_in_cache = (fun ( fieldname  :  Microsoft_FStar_Absyn_Syntax.l__LongIdent ) -> (let _39_576 = (fieldname.Microsoft_FStar_Absyn_Syntax.ns, fieldname.Microsoft_FStar_Absyn_Syntax.ident)
in (match (_39_576) with
| (ns, fieldname) -> begin
(let _52_15153 = (Support.ST.read record_cache)
in (Support.Microsoft.FStar.Util.find_map _52_15153 (fun ( record  :  record ) -> (let constrname = record.constrname.Microsoft_FStar_Absyn_Syntax.ident
in (let ns = (maybe_add_constrname ns constrname)
in (let fname = (Microsoft_FStar_Absyn_Syntax.lid_of_ids (Support.List.append ns ((fieldname)::[])))
in (Support.Microsoft.FStar.Util.find_map record.fields (fun ( _39_584  :  (Microsoft_FStar_Absyn_Syntax.fieldname * Microsoft_FStar_Absyn_Syntax.typ) ) -> (match (_39_584) with
| (f, _) -> begin
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

let qualify_field_to_record = (fun ( env  :  env ) ( recd  :  record ) ( f  :  Microsoft_FStar_Absyn_Syntax.lident ) -> (let qualify = (fun ( fieldname  :  Microsoft_FStar_Absyn_Syntax.l__LongIdent ) -> (let _39_592 = (fieldname.Microsoft_FStar_Absyn_Syntax.ns, fieldname.Microsoft_FStar_Absyn_Syntax.ident)
in (match (_39_592) with
| (ns, fieldname) -> begin
(let constrname = recd.constrname.Microsoft_FStar_Absyn_Syntax.ident
in (let fname = (Microsoft_FStar_Absyn_Syntax.lid_of_ids (Support.List.append (Support.List.append ns ((constrname)::[])) ((fieldname)::[])))
in (Support.Microsoft.FStar.Util.find_map recd.fields (fun ( _39_598  :  (Microsoft_FStar_Absyn_Syntax.fieldname * Microsoft_FStar_Absyn_Syntax.typ) ) -> (match (_39_598) with
| (f, _) -> begin
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

let find_kind_abbrev = (fun ( env  :  env ) ( l  :  Microsoft_FStar_Absyn_Syntax.lident ) -> (match ((try_lookup_name true (not (env.iface)) env l)) with
| Some (Knd_name ((_, l))) -> begin
Some (l)
end
| _ -> begin
None
end))

let is_kind_abbrev = (fun ( env  :  env ) ( l  :  Microsoft_FStar_Absyn_Syntax.lident ) -> (match ((find_kind_abbrev env l)) with
| None -> begin
false
end
| Some (_) -> begin
true
end))

let unique_name = (fun ( any_val  :  bool ) ( exclude_if  :  bool ) ( env  :  env ) ( lid  :  Microsoft_FStar_Absyn_Syntax.lident ) -> (match ((try_lookup_lid' any_val exclude_if env lid)) with
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

let unique_typ_name = (fun ( env  :  env ) ( lid  :  Microsoft_FStar_Absyn_Syntax.lident ) -> (match ((try_lookup_typ_name' true env lid)) with
| None -> begin
true
end
| Some (a) -> begin
false
end))

let unique = (fun ( any_val  :  bool ) ( exclude_if  :  bool ) ( env  :  env ) ( lid  :  Microsoft_FStar_Absyn_Syntax.lident ) -> (let this_env = (let _39_636 = env
in {curmodule = _39_636.curmodule; modules = _39_636.modules; open_namespaces = []; sigaccum = _39_636.sigaccum; localbindings = _39_636.localbindings; recbindings = _39_636.recbindings; phase = _39_636.phase; sigmap = _39_636.sigmap; default_result_effect = _39_636.default_result_effect; iface = _39_636.iface; admitted_iface = _39_636.admitted_iface})
in (let _52_15192 = (unique_name any_val exclude_if this_env lid)
in (let _52_15191 = (unique_typ_name this_env lid)
in (_52_15192 && _52_15191)))))

let gen_bvd = (fun ( _39_13  :  binding ) -> (match (_39_13) with
| Binding_typ_var (id) -> begin
(let _52_15196 = (let _52_15195 = (let _52_15194 = (Microsoft_FStar_Absyn_Util.genident (Some (id.Microsoft_FStar_Absyn_Syntax.idRange)))
in (id, _52_15194))
in (Microsoft_FStar_Absyn_Util.mkbvd _52_15195))
in Support.Microsoft.FStar.Util.Inl (_52_15196))
end
| Binding_var (id) -> begin
(let _52_15199 = (let _52_15198 = (let _52_15197 = (Microsoft_FStar_Absyn_Util.genident (Some (id.Microsoft_FStar_Absyn_Syntax.idRange)))
in (id, _52_15197))
in (Microsoft_FStar_Absyn_Util.mkbvd _52_15198))
in Support.Microsoft.FStar.Util.Inr (_52_15199))
end
| _ -> begin
(failwith ("Tried to generate a bound variable for a type constructor"))
end))

let push_bvvdef = (fun ( env  :  env ) ( x  :  Microsoft_FStar_Absyn_Syntax.bvvdef ) -> (let b = Binding_var (x.Microsoft_FStar_Absyn_Syntax.ppname)
in (let _39_649 = env
in {curmodule = _39_649.curmodule; modules = _39_649.modules; open_namespaces = _39_649.open_namespaces; sigaccum = _39_649.sigaccum; localbindings = ((Support.Microsoft.FStar.Util.Inr (x), b))::env.localbindings; recbindings = _39_649.recbindings; phase = _39_649.phase; sigmap = _39_649.sigmap; default_result_effect = _39_649.default_result_effect; iface = _39_649.iface; admitted_iface = _39_649.admitted_iface})))

let push_btvdef = (fun ( env  :  env ) ( x  :  Microsoft_FStar_Absyn_Syntax.btvdef ) -> (let b = Binding_typ_var (x.Microsoft_FStar_Absyn_Syntax.ppname)
in (let _39_654 = env
in {curmodule = _39_654.curmodule; modules = _39_654.modules; open_namespaces = _39_654.open_namespaces; sigaccum = _39_654.sigaccum; localbindings = ((Support.Microsoft.FStar.Util.Inl (x), b))::env.localbindings; recbindings = _39_654.recbindings; phase = _39_654.phase; sigmap = _39_654.sigmap; default_result_effect = _39_654.default_result_effect; iface = _39_654.iface; admitted_iface = _39_654.admitted_iface})))

let push_local_binding = (fun ( env  :  env ) ( b  :  binding ) -> (let bvd = (gen_bvd b)
in ((let _39_659 = env
in {curmodule = _39_659.curmodule; modules = _39_659.modules; open_namespaces = _39_659.open_namespaces; sigaccum = _39_659.sigaccum; localbindings = ((bvd, b))::env.localbindings; recbindings = _39_659.recbindings; phase = _39_659.phase; sigmap = _39_659.sigmap; default_result_effect = _39_659.default_result_effect; iface = _39_659.iface; admitted_iface = _39_659.admitted_iface}), bvd)))

let push_local_tbinding = (fun ( env  :  env ) ( a  :  Microsoft_FStar_Absyn_Syntax.ident ) -> (match ((push_local_binding env (Binding_typ_var (a)))) with
| (env, Support.Microsoft.FStar.Util.Inl (x)) -> begin
(env, x)
end
| _ -> begin
(failwith ("impossible"))
end))

let push_local_vbinding = (fun ( env  :  env ) ( b  :  Microsoft_FStar_Absyn_Syntax.ident ) -> (match ((push_local_binding env (Binding_var (b)))) with
| (env, Support.Microsoft.FStar.Util.Inr (x)) -> begin
(env, x)
end
| _ -> begin
(failwith ("impossible"))
end))

let push_rec_binding = (fun ( env  :  env ) ( b  :  binding ) -> (match (b) with
| (Binding_let (lid)) | (Binding_tycon (lid)) -> begin
(match ((unique false true env lid)) with
| true -> begin
(let _39_682 = env
in {curmodule = _39_682.curmodule; modules = _39_682.modules; open_namespaces = _39_682.open_namespaces; sigaccum = _39_682.sigaccum; localbindings = _39_682.localbindings; recbindings = (b)::env.recbindings; phase = _39_682.phase; sigmap = _39_682.sigmap; default_result_effect = _39_682.default_result_effect; iface = _39_682.iface; admitted_iface = _39_682.admitted_iface})
end
| false -> begin
(let _52_15226 = (let _52_15225 = (let _52_15224 = (Microsoft_FStar_Absyn_Syntax.range_of_lid lid)
in ((Support.String.strcat "Duplicate top-level names " lid.Microsoft_FStar_Absyn_Syntax.str), _52_15224))
in Microsoft_FStar_Absyn_Syntax.Error (_52_15225))
in (raise (_52_15226)))
end)
end
| _ -> begin
(failwith ("Unexpected rec_binding"))
end))

let push_sigelt = (fun ( env  :  env ) ( s  :  Microsoft_FStar_Absyn_Syntax.sigelt ) -> (let err = (fun ( l  :  Microsoft_FStar_Absyn_Syntax.l__LongIdent ) -> (let sopt = (let _52_15233 = (sigmap env)
in (Support.Microsoft.FStar.Util.smap_try_find _52_15233 l.Microsoft_FStar_Absyn_Syntax.str))
in (let r = (match (sopt) with
| Some ((se, _)) -> begin
(match ((let _52_15234 = (Microsoft_FStar_Absyn_Util.lids_of_sigelt se)
in (Support.Microsoft.FStar.Util.find_opt (Microsoft_FStar_Absyn_Syntax.lid_equals l) _52_15234))) with
| Some (l) -> begin
(let _52_15235 = (Microsoft_FStar_Absyn_Syntax.range_of_lid l)
in (Support.Prims.pipe_left Support.Microsoft.FStar.Range.string_of_range _52_15235))
end
| None -> begin
"<unknown>"
end)
end
| None -> begin
"<unknown>"
end)
in (let _52_15240 = (let _52_15239 = (let _52_15238 = (let _52_15236 = (Microsoft_FStar_Absyn_Syntax.text_of_lid l)
in (Support.Microsoft.FStar.Util.format2 "Duplicate top-level names [%s]; previously declared at %s" _52_15236 r))
in (let _52_15237 = (Microsoft_FStar_Absyn_Syntax.range_of_lid l)
in (_52_15238, _52_15237)))
in Microsoft_FStar_Absyn_Syntax.Error (_52_15239))
in (raise (_52_15240))))))
in (let env = (let _39_711 = (match (s) with
| Microsoft_FStar_Absyn_Syntax.Sig_let (_) -> begin
(false, true)
end
| Microsoft_FStar_Absyn_Syntax.Sig_bundle (_) -> begin
(true, true)
end
| _ -> begin
(false, false)
end)
in (match (_39_711) with
| (any_val, exclude_if) -> begin
(let lids = (Microsoft_FStar_Absyn_Util.lids_of_sigelt s)
in (match ((Support.Microsoft.FStar.Util.find_map lids (fun ( l  :  Microsoft_FStar_Absyn_Syntax.lident ) -> (match ((let _52_15242 = (unique any_val exclude_if env l)
in (not (_52_15242)))) with
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
| Microsoft_FStar_Absyn_Syntax.Sig_bundle ((ses, _, _, _)) -> begin
(let _52_15245 = (Support.List.map (fun ( se  :  Microsoft_FStar_Absyn_Syntax.sigelt ) -> (let _52_15244 = (Microsoft_FStar_Absyn_Util.lids_of_sigelt se)
in (_52_15244, se))) ses)
in (env, _52_15245))
end
| _ -> begin
(let _52_15248 = (let _52_15247 = (let _52_15246 = (Microsoft_FStar_Absyn_Util.lids_of_sigelt s)
in (_52_15246, s))
in (_52_15247)::[])
in (env, _52_15248))
end)
in (match (_39_736) with
| (env, lss) -> begin
(let _39_741 = (Support.Prims.pipe_right lss (Support.List.iter (fun ( _39_739  :  (Microsoft_FStar_Absyn_Syntax.l__LongIdent list * Microsoft_FStar_Absyn_Syntax.sigelt) ) -> (match (_39_739) with
| (lids, se) -> begin
(Support.Prims.pipe_right lids (Support.List.iter (fun ( lid  :  Microsoft_FStar_Absyn_Syntax.l__LongIdent ) -> (let _52_15251 = (sigmap env)
in (Support.Microsoft.FStar.Util.smap_add _52_15251 lid.Microsoft_FStar_Absyn_Syntax.str (se, (env.iface && (not (env.admitted_iface)))))))))
end))))
in env)
end)))))

let push_namespace = (fun ( env  :  env ) ( lid  :  Microsoft_FStar_Absyn_Syntax.lident ) -> (let _39_745 = env
in {curmodule = _39_745.curmodule; modules = _39_745.modules; open_namespaces = (lid)::env.open_namespaces; sigaccum = _39_745.sigaccum; localbindings = _39_745.localbindings; recbindings = _39_745.recbindings; phase = _39_745.phase; sigmap = _39_745.sigmap; default_result_effect = _39_745.default_result_effect; iface = _39_745.iface; admitted_iface = _39_745.admitted_iface}))

let is_type_lid = (fun ( env  :  env ) ( lid  :  Microsoft_FStar_Absyn_Syntax.lident ) -> (let aux = (fun ( _39_750  :  unit ) -> (match (()) with
| () -> begin
(match ((try_lookup_typ_name' false env lid)) with
| Some (_) -> begin
true
end
| _ -> begin
false
end)
end))
in (match ((lid.Microsoft_FStar_Absyn_Syntax.ns = [])) with
| true -> begin
(match ((try_lookup_id env lid.Microsoft_FStar_Absyn_Syntax.ident)) with
| Some (_) -> begin
false
end
| _ -> begin
(aux ())
end)
end
| false -> begin
(aux ())
end)))

let check_admits = (fun ( nm  :  Microsoft_FStar_Absyn_Syntax.lident ) ( env  :  env ) -> (let warn = (let _52_15268 = (let _52_15267 = (Support.ST.read Microsoft_FStar_Options.admit_fsi)
in (Support.Prims.pipe_right _52_15267 (Support.Microsoft.FStar.Util.for_some (fun ( l  :  string ) -> (nm.Microsoft_FStar_Absyn_Syntax.str = l)))))
in (not (_52_15268)))
in (Support.Prims.pipe_right env.sigaccum (Support.List.iter (fun ( se  :  Microsoft_FStar_Absyn_Syntax.sigelt ) -> (match (se) with
| Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((l, t, quals, r)) -> begin
(match ((try_lookup_lid env l)) with
| None -> begin
(let _39_773 = (match (warn) with
| true -> begin
(let _52_15273 = (let _52_15272 = (let _52_15270 = (Microsoft_FStar_Absyn_Syntax.range_of_lid l)
in (Support.Microsoft.FStar.Range.string_of_range _52_15270))
in (let _52_15271 = (Microsoft_FStar_Absyn_Print.sli l)
in (Support.Microsoft.FStar.Util.format2 "%s: Warning: Admitting %s without a definition\n" _52_15272 _52_15271)))
in (Support.Microsoft.FStar.Util.print_string _52_15273))
end
| false -> begin
()
end)
in (let _52_15274 = (sigmap env)
in (Support.Microsoft.FStar.Util.smap_add _52_15274 l.Microsoft_FStar_Absyn_Syntax.str (Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((l, t, (Microsoft_FStar_Absyn_Syntax.Assumption)::quals, r)), false))))
end
| Some (_) -> begin
()
end)
end
| _ -> begin
()
end))))))

let finish = (fun ( env  :  env ) ( modul  :  Microsoft_FStar_Absyn_Syntax.modul ) -> (let _39_817 = (Support.Prims.pipe_right modul.Microsoft_FStar_Absyn_Syntax.declarations (Support.List.iter (fun ( _39_15  :  Microsoft_FStar_Absyn_Syntax.sigelt ) -> (match (_39_15) with
| Microsoft_FStar_Absyn_Syntax.Sig_bundle ((ses, quals, _, _)) -> begin
(match ((Support.List.contains Microsoft_FStar_Absyn_Syntax.Private quals)) with
| true -> begin
(Support.Prims.pipe_right ses (Support.List.iter (fun ( _39_14  :  Microsoft_FStar_Absyn_Syntax.sigelt ) -> (match (_39_14) with
| Microsoft_FStar_Absyn_Syntax.Sig_datacon ((lid, _, _, _, _, _)) -> begin
(let _52_15281 = (sigmap env)
in (Support.Microsoft.FStar.Util.smap_remove _52_15281 lid.Microsoft_FStar_Absyn_Syntax.str))
end
| _ -> begin
()
end))))
end
| false -> begin
()
end)
end
| Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((lid, _, quals, _)) -> begin
(match ((Support.List.contains Microsoft_FStar_Absyn_Syntax.Private quals)) with
| true -> begin
(let _52_15282 = (sigmap env)
in (Support.Microsoft.FStar.Util.smap_remove _52_15282 lid.Microsoft_FStar_Absyn_Syntax.str))
end
| false -> begin
()
end)
end
| _ -> begin
()
end))))
in (let _39_819 = env
in {curmodule = None; modules = ((modul.Microsoft_FStar_Absyn_Syntax.name, modul))::env.modules; open_namespaces = []; sigaccum = []; localbindings = []; recbindings = []; phase = Microsoft_FStar_Parser_AST.Un; sigmap = _39_819.sigmap; default_result_effect = _39_819.default_result_effect; iface = _39_819.iface; admitted_iface = _39_819.admitted_iface})))

let push = (fun ( env  :  env ) -> (let _39_822 = env
in (let _52_15287 = (let _52_15286 = (let _52_15285 = (sigmap env)
in (Support.Microsoft.FStar.Util.smap_copy _52_15285))
in (_52_15286)::env.sigmap)
in {curmodule = _39_822.curmodule; modules = _39_822.modules; open_namespaces = _39_822.open_namespaces; sigaccum = _39_822.sigaccum; localbindings = _39_822.localbindings; recbindings = _39_822.recbindings; phase = _39_822.phase; sigmap = _52_15287; default_result_effect = _39_822.default_result_effect; iface = _39_822.iface; admitted_iface = _39_822.admitted_iface})))

let mark = (fun ( env  :  env ) -> (push env))

let reset_mark = (fun ( env  :  env ) -> (let _39_826 = env
in (let _52_15292 = (Support.List.tl env.sigmap)
in {curmodule = _39_826.curmodule; modules = _39_826.modules; open_namespaces = _39_826.open_namespaces; sigaccum = _39_826.sigaccum; localbindings = _39_826.localbindings; recbindings = _39_826.recbindings; phase = _39_826.phase; sigmap = _52_15292; default_result_effect = _39_826.default_result_effect; iface = _39_826.iface; admitted_iface = _39_826.admitted_iface})))

let commit_mark = (fun ( env  :  env ) -> (match (env.sigmap) with
| hd::_::tl -> begin
(let _39_835 = env
in {curmodule = _39_835.curmodule; modules = _39_835.modules; open_namespaces = _39_835.open_namespaces; sigaccum = _39_835.sigaccum; localbindings = _39_835.localbindings; recbindings = _39_835.recbindings; phase = _39_835.phase; sigmap = (hd)::tl; default_result_effect = _39_835.default_result_effect; iface = _39_835.iface; admitted_iface = _39_835.admitted_iface})
end
| _ -> begin
(failwith ("Impossible"))
end))

let pop = (fun ( env  :  env ) -> (match (env.sigmap) with
| _::maps -> begin
(let _39_844 = env
in {curmodule = _39_844.curmodule; modules = _39_844.modules; open_namespaces = _39_844.open_namespaces; sigaccum = _39_844.sigaccum; localbindings = _39_844.localbindings; recbindings = _39_844.recbindings; phase = _39_844.phase; sigmap = maps; default_result_effect = _39_844.default_result_effect; iface = _39_844.iface; admitted_iface = _39_844.admitted_iface})
end
| _ -> begin
(failwith ("No more modules to pop"))
end))

let finish_module_or_interface = (fun ( env  :  env ) ( modul  :  Microsoft_FStar_Absyn_Syntax.modul ) -> (let _39_850 = (match ((not (modul.Microsoft_FStar_Absyn_Syntax.is_interface))) with
| true -> begin
(check_admits modul.Microsoft_FStar_Absyn_Syntax.name env)
end
| false -> begin
()
end)
in (finish env modul)))

let prepare_module_or_interface = (fun ( intf  :  bool ) ( admitted  :  bool ) ( env  :  env ) ( mname  :  Microsoft_FStar_Absyn_Syntax.lident ) -> (let prep = (fun ( env  :  env ) -> (let open_ns = (match ((Microsoft_FStar_Absyn_Syntax.lid_equals mname Microsoft_FStar_Absyn_Const.prims_lid)) with
| true -> begin
[]
end
| false -> begin
(Microsoft_FStar_Absyn_Const.prims_lid)::[]
end)
in (let _39_859 = env
in {curmodule = Some (mname); modules = _39_859.modules; open_namespaces = open_ns; sigaccum = _39_859.sigaccum; localbindings = _39_859.localbindings; recbindings = _39_859.recbindings; phase = _39_859.phase; sigmap = env.sigmap; default_result_effect = _39_859.default_result_effect; iface = intf; admitted_iface = admitted})))
in (match ((Support.Prims.pipe_right env.modules (Support.Microsoft.FStar.Util.find_opt (fun ( _39_864  :  (Microsoft_FStar_Absyn_Syntax.lident * Microsoft_FStar_Absyn_Syntax.modul) ) -> (match (_39_864) with
| (l, _) -> begin
(Microsoft_FStar_Absyn_Syntax.lid_equals l mname)
end))))) with
| None -> begin
(prep env)
end
| Some ((_, m)) -> begin
(let _39_871 = (match (intf) with
| true -> begin
(let _52_15315 = (let _52_15314 = (let _52_15313 = (Support.Microsoft.FStar.Util.format1 "Duplicate module or interface name: %s" mname.Microsoft_FStar_Absyn_Syntax.str)
in (let _52_15312 = (Microsoft_FStar_Absyn_Syntax.range_of_lid mname)
in (_52_15313, _52_15312)))
in Microsoft_FStar_Absyn_Syntax.Error (_52_15314))
in (raise (_52_15315)))
end
| false -> begin
()
end)
in (prep env))
end)))

let enter_monad_scope = (fun ( env  :  env ) ( mname  :  Microsoft_FStar_Absyn_Syntax.ident ) -> (let curmod = (current_module env)
in (let mscope = (Microsoft_FStar_Absyn_Syntax.lid_of_ids (Support.List.append curmod.Microsoft_FStar_Absyn_Syntax.ns ((curmod.Microsoft_FStar_Absyn_Syntax.ident)::(mname)::[])))
in (let _39_877 = env
in {curmodule = Some (mscope); modules = _39_877.modules; open_namespaces = (curmod)::env.open_namespaces; sigaccum = _39_877.sigaccum; localbindings = _39_877.localbindings; recbindings = _39_877.recbindings; phase = _39_877.phase; sigmap = _39_877.sigmap; default_result_effect = _39_877.default_result_effect; iface = _39_877.iface; admitted_iface = _39_877.admitted_iface}))))

let exit_monad_scope = (fun ( env0  :  env ) ( env  :  env ) -> (let _39_881 = env
in {curmodule = env0.curmodule; modules = _39_881.modules; open_namespaces = env0.open_namespaces; sigaccum = _39_881.sigaccum; localbindings = _39_881.localbindings; recbindings = _39_881.recbindings; phase = _39_881.phase; sigmap = _39_881.sigmap; default_result_effect = _39_881.default_result_effect; iface = _39_881.iface; admitted_iface = _39_881.admitted_iface}))

let fail_or = (fun ( env  :  env ) ( lookup  :  Microsoft_FStar_Absyn_Syntax.lident  ->  'a option ) ( lid  :  Microsoft_FStar_Absyn_Syntax.lident ) -> (match ((lookup lid)) with
| None -> begin
(let r = (match ((try_lookup_name true false env lid)) with
| None -> begin
None
end
| (Some (Knd_name ((o, _)))) | (Some (Eff_name ((o, _)))) | (Some (Typ_name ((o, _)))) | (Some (Exp_name ((o, _)))) -> begin
(let _52_15330 = (range_of_occurrence o)
in Some (_52_15330))
end)
in (let msg = (match (r) with
| None -> begin
""
end
| Some (r) -> begin
(let _52_15331 = (Support.Microsoft.FStar.Range.string_of_range r)
in (Support.Microsoft.FStar.Util.format1 "(Possible clash with related name at %s)" _52_15331))
end)
in (let _52_15336 = (let _52_15335 = (let _52_15334 = (let _52_15332 = (Microsoft_FStar_Absyn_Syntax.text_of_lid lid)
in (Support.Microsoft.FStar.Util.format2 "Identifier not found: [%s] %s" _52_15332 msg))
in (let _52_15333 = (Microsoft_FStar_Absyn_Syntax.range_of_lid lid)
in (_52_15334, _52_15333)))
in Microsoft_FStar_Absyn_Syntax.Error (_52_15335))
in (raise (_52_15336)))))
end
| Some (r) -> begin
r
end))

let fail_or2 = (fun ( lookup  :  Microsoft_FStar_Absyn_Syntax.ident  ->  'a option ) ( id  :  Microsoft_FStar_Absyn_Syntax.ident ) -> (match ((lookup id)) with
| None -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (((Support.String.strcat (Support.String.strcat "Identifier not found [" id.Microsoft_FStar_Absyn_Syntax.idText) "]"), id.Microsoft_FStar_Absyn_Syntax.idRange))))
end
| Some (r) -> begin
r
end))




