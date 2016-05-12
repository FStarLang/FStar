
open Prims
# 34 "FStar.Parser.Env.fst"
type env =
{curmodule : FStar_Ident.lident Prims.option; modules : (FStar_Ident.lident * FStar_Syntax_Syntax.modul) Prims.list; open_namespaces : FStar_Ident.lident Prims.list; modul_abbrevs : (FStar_Ident.ident * FStar_Ident.lident) Prims.list; sigaccum : FStar_Syntax_Syntax.sigelts; localbindings : (FStar_Ident.ident * FStar_Syntax_Syntax.bv) Prims.list; recbindings : (FStar_Ident.ident * FStar_Ident.lid * FStar_Syntax_Syntax.delta_depth) Prims.list; sigmap : (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap; default_result_effect : FStar_Ident.lident; iface : Prims.bool; admitted_iface : Prims.bool; expect_typ : Prims.bool}

# 34 "FStar.Parser.Env.fst"
let is_Mkenv : env  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv"))))

# 49 "FStar.Parser.Env.fst"
type foundname =
| Term_name of FStar_Syntax_Syntax.typ
| Eff_name of (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident)

# 50 "FStar.Parser.Env.fst"
let is_Term_name = (fun _discr_ -> (match (_discr_) with
| Term_name (_) -> begin
true
end
| _ -> begin
false
end))

# 51 "FStar.Parser.Env.fst"
let is_Eff_name = (fun _discr_ -> (match (_discr_) with
| Eff_name (_) -> begin
true
end
| _ -> begin
false
end))

# 50 "FStar.Parser.Env.fst"
let ___Term_name____0 = (fun projectee -> (match (projectee) with
| Term_name (_61_28) -> begin
_61_28
end))

# 51 "FStar.Parser.Env.fst"
let ___Eff_name____0 = (fun projectee -> (match (projectee) with
| Eff_name (_61_31) -> begin
_61_31
end))

# 53 "FStar.Parser.Env.fst"
type record_or_dc =
{typename : FStar_Ident.lident; constrname : FStar_Ident.lident; parms : FStar_Syntax_Syntax.binders; fields : (FStar_Syntax_Syntax.fieldname * FStar_Syntax_Syntax.typ) Prims.list; is_record : Prims.bool}

# 53 "FStar.Parser.Env.fst"
let is_Mkrecord_or_dc : record_or_dc  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkrecord_or_dc"))))

# 97 "FStar.Parser.Env.fst"
let open_modules : env  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.modul) Prims.list = (fun e -> e.modules)

# 98 "FStar.Parser.Env.fst"
let current_module : env  ->  FStar_Ident.lident = (fun env -> (match (env.curmodule) with
| None -> begin
(FStar_All.failwith "Unset current module")
end
| Some (m) -> begin
m
end))

# 101 "FStar.Parser.Env.fst"
let qual : FStar_Ident.lident  ->  FStar_Ident.ident  ->  FStar_Ident.lident = (fun lid id -> (let _150_90 = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns ((lid.FStar_Ident.ident)::(id)::[])))
in (FStar_Ident.set_lid_range _150_90 id.FStar_Ident.idRange)))

# 102 "FStar.Parser.Env.fst"
let qualify : env  ->  FStar_Ident.ident  ->  FStar_Ident.lident = (fun env id -> (let _150_95 = (current_module env)
in (qual _150_95 id)))

# 103 "FStar.Parser.Env.fst"
let qualify_lid : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (
# 104 "FStar.Parser.Env.fst"
let cur = (current_module env)
in (let _150_100 = (FStar_Ident.lid_of_ids (FStar_List.append (FStar_List.append (FStar_List.append cur.FStar_Ident.ns ((cur.FStar_Ident.ident)::[])) lid.FStar_Ident.ns) ((lid.FStar_Ident.ident)::[])))
in (FStar_Ident.set_lid_range _150_100 (FStar_Ident.range_of_lid lid)))))

# 106 "FStar.Parser.Env.fst"
let new_sigmap = (fun _61_52 -> (match (()) with
| () -> begin
(FStar_Util.smap_create 100)
end))

# 107 "FStar.Parser.Env.fst"
let empty_env : Prims.unit  ->  env = (fun _61_53 -> (match (()) with
| () -> begin
(let _150_104 = (new_sigmap ())
in {curmodule = None; modules = []; open_namespaces = []; modul_abbrevs = []; sigaccum = []; localbindings = []; recbindings = []; sigmap = _150_104; default_result_effect = FStar_Syntax_Const.effect_ML_lid; iface = false; admitted_iface = false; expect_typ = false})
end))

# 119 "FStar.Parser.Env.fst"
let sigmap : env  ->  (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap = (fun env -> env.sigmap)

# 120 "FStar.Parser.Env.fst"
let default_total : env  ->  env = (fun env -> (
# 120 "FStar.Parser.Env.fst"
let _61_56 = env
in {curmodule = _61_56.curmodule; modules = _61_56.modules; open_namespaces = _61_56.open_namespaces; modul_abbrevs = _61_56.modul_abbrevs; sigaccum = _61_56.sigaccum; localbindings = _61_56.localbindings; recbindings = _61_56.recbindings; sigmap = _61_56.sigmap; default_result_effect = FStar_Syntax_Const.effect_Tot_lid; iface = _61_56.iface; admitted_iface = _61_56.admitted_iface; expect_typ = _61_56.expect_typ}))

# 121 "FStar.Parser.Env.fst"
let default_ml : env  ->  env = (fun env -> (
# 121 "FStar.Parser.Env.fst"
let _61_59 = env
in {curmodule = _61_59.curmodule; modules = _61_59.modules; open_namespaces = _61_59.open_namespaces; modul_abbrevs = _61_59.modul_abbrevs; sigaccum = _61_59.sigaccum; localbindings = _61_59.localbindings; recbindings = _61_59.recbindings; sigmap = _61_59.sigmap; default_result_effect = FStar_Syntax_Const.effect_ML_lid; iface = _61_59.iface; admitted_iface = _61_59.admitted_iface; expect_typ = _61_59.expect_typ}))

# 124 "FStar.Parser.Env.fst"
let set_bv_range : FStar_Syntax_Syntax.bv  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.bv = (fun bv r -> (
# 125 "FStar.Parser.Env.fst"
let id = (
# 125 "FStar.Parser.Env.fst"
let _61_63 = bv.FStar_Syntax_Syntax.ppname
in {FStar_Ident.idText = _61_63.FStar_Ident.idText; FStar_Ident.idRange = r})
in (
# 126 "FStar.Parser.Env.fst"
let _61_66 = bv
in {FStar_Syntax_Syntax.ppname = id; FStar_Syntax_Syntax.index = _61_66.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _61_66.FStar_Syntax_Syntax.sort})))

# 128 "FStar.Parser.Env.fst"
let bv_to_name : FStar_Syntax_Syntax.bv  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.term = (fun bv r -> (FStar_Syntax_Syntax.bv_to_name (set_bv_range bv r)))

# 130 "FStar.Parser.Env.fst"
let unmangleMap : (Prims.string * Prims.string * FStar_Syntax_Syntax.delta_depth * FStar_Syntax_Syntax.fv_qual Prims.option) Prims.list = (("op_ColonColon", "Cons", FStar_Syntax_Syntax.Delta_constant, Some (FStar_Syntax_Syntax.Data_ctor)))::(("not", "op_Negation", FStar_Syntax_Syntax.Delta_equational, None))::[]

# 133 "FStar.Parser.Env.fst"
let unmangleOpName : FStar_Ident.ident  ->  FStar_Syntax_Syntax.term Prims.option = (fun id -> (FStar_Util.find_map unmangleMap (fun _61_75 -> (match (_61_75) with
| (x, y, dd, dq) -> begin
if (id.FStar_Ident.idText = x) then begin
(let _150_123 = (let _150_122 = (FStar_Ident.lid_of_path (("Prims")::(y)::[]) id.FStar_Ident.idRange)
in (FStar_Syntax_Syntax.fvar _150_122 dd dq))
in Some (_150_123))
end else begin
None
end
end))))

# 138 "FStar.Parser.Env.fst"
let try_lookup_id : env  ->  FStar_Ident.ident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env id -> (match ((unmangleOpName id)) with
| Some (f) -> begin
Some (f)
end
| _61_81 -> begin
(FStar_Util.find_map env.localbindings (fun _61_1 -> (match (_61_1) with
| (id', x) when (id'.FStar_Ident.idText = id.FStar_Ident.idText) -> begin
(let _150_129 = (bv_to_name x id.FStar_Ident.idRange)
in Some (_150_129))
end
| _61_87 -> begin
None
end)))
end))

# 147 "FStar.Parser.Env.fst"
let resolve_in_open_namespaces' = (fun env lid finder -> (
# 148 "FStar.Parser.Env.fst"
let aux = (fun namespaces -> (match ((finder lid)) with
| Some (r) -> begin
Some (r)
end
| _61_97 -> begin
(
# 152 "FStar.Parser.Env.fst"
let ids = (FStar_Ident.ids_of_lid lid)
in (FStar_Util.find_map namespaces (fun ns -> (
# 154 "FStar.Parser.Env.fst"
let full_name = (FStar_Ident.lid_of_ids (FStar_List.append (FStar_Ident.ids_of_lid ns) ids))
in (finder full_name)))))
end))
in (let _150_140 = (let _150_139 = (current_module env)
in (_150_139)::env.open_namespaces)
in (aux _150_140))))

# 158 "FStar.Parser.Env.fst"
let expand_module_abbrevs : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (match (lid.FStar_Ident.ns) with
| id::[] -> begin
(match ((FStar_All.pipe_right env.modul_abbrevs (FStar_List.tryFind (fun _61_108 -> (match (_61_108) with
| (id', _61_107) -> begin
(id.FStar_Ident.idText = id'.FStar_Ident.idText)
end))))) with
| None -> begin
lid
end
| Some (_61_111, lid') -> begin
(FStar_Ident.lid_of_ids (FStar_List.append (FStar_Ident.ids_of_lid lid') ((lid.FStar_Ident.ident)::[])))
end)
end
| _61_116 -> begin
lid
end))

# 168 "FStar.Parser.Env.fst"
let resolve_in_open_namespaces = (fun env lid finder -> (let _150_152 = (expand_module_abbrevs env lid)
in (resolve_in_open_namespaces' env _150_152 finder)))

# 171 "FStar.Parser.Env.fst"
let fv_qual_of_se : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.fv_qual Prims.option = (fun _61_3 -> (match (_61_3) with
| FStar_Syntax_Syntax.Sig_datacon (_61_123, _61_125, _61_127, l, _61_130, quals, _61_133, _61_135) -> begin
(
# 173 "FStar.Parser.Env.fst"
let qopt = (FStar_Util.find_map quals (fun _61_2 -> (match (_61_2) with
| FStar_Syntax_Syntax.RecordConstructor (fs) -> begin
Some (FStar_Syntax_Syntax.Record_ctor ((l, fs)))
end
| _61_142 -> begin
None
end)))
in (match (qopt) with
| None -> begin
Some (FStar_Syntax_Syntax.Data_ctor)
end
| x -> begin
x
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (_61_147, _61_149, _61_151, quals, _61_154) -> begin
None
end
| _61_158 -> begin
None
end))

# 184 "FStar.Parser.Env.fst"
let lb_fv : FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.fv = (fun lbs lid -> (let _150_161 = (FStar_Util.find_map lbs (fun lb -> (
# 186 "FStar.Parser.Env.fst"
let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in if (FStar_Syntax_Syntax.fv_eq_lid fv lid) then begin
Some (fv)
end else begin
None
end)))
in (FStar_All.pipe_right _150_161 FStar_Util.must)))

# 189 "FStar.Parser.Env.fst"
let try_lookup_name : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  foundname Prims.option = (fun any_val exclude_interf env lid -> (
# 195 "FStar.Parser.Env.fst"
let find_in_sig = (fun lid -> (match ((FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str)) with
| Some (_61_170, true) when exclude_interf -> begin
None
end
| None -> begin
None
end
| Some (se, _61_177) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_61_181) -> begin
(let _150_173 = (let _150_172 = (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.Delta_constant None)
in Term_name (_150_172))
in Some (_150_173))
end
| FStar_Syntax_Syntax.Sig_datacon (_61_184) -> begin
(let _150_176 = (let _150_175 = (let _150_174 = (fv_qual_of_se se)
in (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.Delta_constant _150_174))
in Term_name (_150_175))
in Some (_150_176))
end
| FStar_Syntax_Syntax.Sig_let ((_61_187, lbs), _61_191, _61_193, _61_195) -> begin
(
# 204 "FStar.Parser.Env.fst"
let fv = (lb_fv lbs lid)
in (let _150_178 = (let _150_177 = (FStar_Syntax_Syntax.fvar lid fv.FStar_Syntax_Syntax.fv_delta fv.FStar_Syntax_Syntax.fv_qual)
in Term_name (_150_177))
in Some (_150_178)))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _61_201, _61_203, quals, _61_206) -> begin
if (any_val || (FStar_All.pipe_right quals (FStar_Util.for_some (fun _61_4 -> (match (_61_4) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| _61_212 -> begin
false
end))))) then begin
(
# 209 "FStar.Parser.Env.fst"
let dd = if ((FStar_Syntax_Util.is_primop_lid lid) || ((FStar_Util.starts_with lid.FStar_Ident.nsstr "Prims.") && (FStar_All.pipe_right quals (FStar_Util.for_some (fun _61_5 -> (match (_61_5) with
| (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) -> begin
true
end
| _61_221 -> begin
false
end)))))) then begin
FStar_Syntax_Syntax.Delta_equational
end else begin
FStar_Syntax_Syntax.Delta_constant
end
in (let _150_183 = (let _150_182 = (let _150_181 = (fv_qual_of_se se)
in (FStar_Syntax_Syntax.fvar lid dd _150_181))
in Term_name (_150_182))
in Some (_150_183)))
end else begin
None
end
end
| FStar_Syntax_Syntax.Sig_new_effect (ne, _61_225) -> begin
(let _150_186 = (let _150_185 = (let _150_184 = (FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname (FStar_Ident.range_of_lid lid))
in (se, _150_184))
in Eff_name (_150_185))
in Some (_150_186))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (_61_229) -> begin
Some (Eff_name ((se, lid)))
end
| _61_232 -> begin
None
end)
end))
in (
# 220 "FStar.Parser.Env.fst"
let found_id = (match (lid.FStar_Ident.ns) with
| [] -> begin
(match ((try_lookup_id env lid.FStar_Ident.ident)) with
| Some (e) -> begin
Some (Term_name (e))
end
| None -> begin
(
# 225 "FStar.Parser.Env.fst"
let recname = (qualify env lid.FStar_Ident.ident)
in (FStar_Util.find_map env.recbindings (fun _61_241 -> (match (_61_241) with
| (id, l, dd) -> begin
if (id.FStar_Ident.idText = lid.FStar_Ident.ident.FStar_Ident.idText) then begin
(let _150_190 = (let _150_189 = (let _150_188 = (FStar_Ident.set_lid_range l (FStar_Ident.range_of_lid lid))
in (FStar_Syntax_Syntax.fvar _150_188 dd None))
in Term_name (_150_189))
in Some (_150_190))
end else begin
None
end
end))))
end)
end
| _61_243 -> begin
None
end)
in (match (found_id) with
| Some (_61_246) -> begin
found_id
end
| _61_249 -> begin
(resolve_in_open_namespaces env lid find_in_sig)
end))))

# 236 "FStar.Parser.Env.fst"
let try_lookup_effect_name' : Prims.bool  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident) Prims.option = (fun exclude_interf env lid -> (match ((try_lookup_name true exclude_interf env lid)) with
| Some (Eff_name (o, l)) -> begin
Some ((o, l))
end
| _61_259 -> begin
None
end))

# 240 "FStar.Parser.Env.fst"
let try_lookup_effect_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env l -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some (o, l) -> begin
Some (l)
end
| _61_267 -> begin
None
end))

# 244 "FStar.Parser.Env.fst"
let try_lookup_effect_defn : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl Prims.option = (fun env l -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some (FStar_Syntax_Syntax.Sig_new_effect (ne, _61_272), _61_276) -> begin
Some (ne)
end
| _61_280 -> begin
None
end))

# 248 "FStar.Parser.Env.fst"
let is_effect_name : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((try_lookup_effect_name env lid)) with
| None -> begin
false
end
| Some (_61_285) -> begin
true
end))

# 253 "FStar.Parser.Env.fst"
let lookup_letbinding_quals : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.qualifier Prims.list = (fun env lid -> (
# 254 "FStar.Parser.Env.fst"
let find_in_sig = (fun lid -> (match ((FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str)) with
| Some (FStar_Syntax_Syntax.Sig_declare_typ (lid, _61_293, _61_295, quals, _61_298), _61_302) -> begin
Some (quals)
end
| _61_306 -> begin
None
end))
in (match ((resolve_in_open_namespaces env lid find_in_sig)) with
| Some (quals) -> begin
quals
end
| _61_310 -> begin
[]
end)))

# 262 "FStar.Parser.Env.fst"
let try_lookup_module : env  ->  Prims.string Prims.list  ->  FStar_Syntax_Syntax.modul Prims.option = (fun env path -> (match ((FStar_List.tryFind (fun _61_315 -> (match (_61_315) with
| (mlid, modul) -> begin
((FStar_Ident.path_of_lid mlid) = path)
end)) env.modules)) with
| Some (_61_317, modul) -> begin
Some (modul)
end
| None -> begin
None
end))

# 267 "FStar.Parser.Env.fst"
let try_lookup_let : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env lid -> (
# 268 "FStar.Parser.Env.fst"
let find_in_sig = (fun lid -> (match ((FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str)) with
| Some (FStar_Syntax_Syntax.Sig_let ((_61_327, lbs), _61_331, _61_333, _61_335), _61_339) -> begin
(
# 271 "FStar.Parser.Env.fst"
let fv = (lb_fv lbs lid)
in (let _150_226 = (FStar_Syntax_Syntax.fvar lid fv.FStar_Syntax_Syntax.fv_delta fv.FStar_Syntax_Syntax.fv_qual)
in Some (_150_226)))
end
| _61_344 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))

# 276 "FStar.Parser.Env.fst"
let try_lookup_definition : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env lid -> (
# 277 "FStar.Parser.Env.fst"
let find_in_sig = (fun lid -> (match ((FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str)) with
| Some (FStar_Syntax_Syntax.Sig_let (lbs, _61_351, _61_353, _61_355), _61_359) -> begin
(FStar_Util.find_map (Prims.snd lbs) (fun lb -> (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv lid) -> begin
Some (lb.FStar_Syntax_Syntax.lbdef)
end
| _61_366 -> begin
None
end)))
end
| _61_368 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))

# 289 "FStar.Parser.Env.fst"
let try_lookup_lid' : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun any_val exclude_interf env lid -> (match ((try_lookup_name any_val exclude_interf env lid)) with
| Some (Term_name (e)) -> begin
Some (e)
end
| _61_377 -> begin
None
end))

# 293 "FStar.Parser.Env.fst"
let try_lookup_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env l -> (try_lookup_lid' env.iface false env l))

# 295 "FStar.Parser.Env.fst"
let try_lookup_datacon : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.fv Prims.option = (fun env lid -> (
# 296 "FStar.Parser.Env.fst"
let find_in_sig = (fun lid -> (match ((FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str)) with
| Some (FStar_Syntax_Syntax.Sig_declare_typ (_61_385, _61_387, _61_389, quals, _61_392), _61_396) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _61_6 -> (match (_61_6) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| _61_402 -> begin
false
end)))) then begin
(let _150_253 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant None)
in Some (_150_253))
end else begin
None
end
end
| Some (FStar_Syntax_Syntax.Sig_datacon (_61_404), _61_407) -> begin
(let _150_254 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in Some (_150_254))
end
| _61_411 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))

# 306 "FStar.Parser.Env.fst"
let find_all_datacons : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.list Prims.option = (fun env lid -> (
# 307 "FStar.Parser.Env.fst"
let find_in_sig = (fun lid -> (match ((FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str)) with
| Some (FStar_Syntax_Syntax.Sig_inductive_typ (_61_417, _61_419, _61_421, _61_423, _61_425, datas, _61_428, _61_430), _61_434) -> begin
Some (datas)
end
| _61_438 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))

# 314 "FStar.Parser.Env.fst"
let record_cache_aux : ((Prims.unit  ->  Prims.unit) * (Prims.unit  ->  Prims.unit) * (Prims.unit  ->  record_or_dc Prims.list) * (record_or_dc  ->  Prims.unit) * (Prims.unit  ->  Prims.unit)) = (
# 315 "FStar.Parser.Env.fst"
let record_cache = (FStar_Util.mk_ref (([])::[]))
in (
# 316 "FStar.Parser.Env.fst"
let push = (fun _61_441 -> (match (()) with
| () -> begin
(let _150_276 = (let _150_275 = (let _150_273 = (FStar_ST.read record_cache)
in (FStar_List.hd _150_273))
in (let _150_274 = (FStar_ST.read record_cache)
in (_150_275)::_150_274))
in (FStar_ST.op_Colon_Equals record_cache _150_276))
end))
in (
# 318 "FStar.Parser.Env.fst"
let pop = (fun _61_443 -> (match (()) with
| () -> begin
(let _150_280 = (let _150_279 = (FStar_ST.read record_cache)
in (FStar_List.tl _150_279))
in (FStar_ST.op_Colon_Equals record_cache _150_280))
end))
in (
# 320 "FStar.Parser.Env.fst"
let peek = (fun _61_445 -> (match (()) with
| () -> begin
(let _150_283 = (FStar_ST.read record_cache)
in (FStar_List.hd _150_283))
end))
in (
# 321 "FStar.Parser.Env.fst"
let insert = (fun r -> (let _150_290 = (let _150_289 = (let _150_286 = (peek ())
in (r)::_150_286)
in (let _150_288 = (let _150_287 = (FStar_ST.read record_cache)
in (FStar_List.tl _150_287))
in (_150_289)::_150_288))
in (FStar_ST.op_Colon_Equals record_cache _150_290)))
in (
# 322 "FStar.Parser.Env.fst"
let commit = (fun _61_449 -> (match (()) with
| () -> begin
(match ((FStar_ST.read record_cache)) with
| hd::_61_452::tl -> begin
(FStar_ST.op_Colon_Equals record_cache ((hd)::tl))
end
| _61_457 -> begin
(FStar_All.failwith "Impossible")
end)
end))
in (push, pop, peek, insert, commit)))))))

# 327 "FStar.Parser.Env.fst"
let push_record_cache : Prims.unit  ->  Prims.unit = (
# 328 "FStar.Parser.Env.fst"
let _61_467 = record_cache_aux
in (match (_61_467) with
| (push, _61_460, _61_462, _61_464, _61_466) -> begin
push
end))

# 331 "FStar.Parser.Env.fst"
let pop_record_cache : Prims.unit  ->  Prims.unit = (
# 332 "FStar.Parser.Env.fst"
let _61_477 = record_cache_aux
in (match (_61_477) with
| (_61_469, pop, _61_472, _61_474, _61_476) -> begin
pop
end))

# 335 "FStar.Parser.Env.fst"
let peek_record_cache : Prims.unit  ->  record_or_dc Prims.list = (
# 336 "FStar.Parser.Env.fst"
let _61_487 = record_cache_aux
in (match (_61_487) with
| (_61_479, _61_481, peek, _61_484, _61_486) -> begin
peek
end))

# 339 "FStar.Parser.Env.fst"
let insert_record_cache : record_or_dc  ->  Prims.unit = (
# 340 "FStar.Parser.Env.fst"
let _61_497 = record_cache_aux
in (match (_61_497) with
| (_61_489, _61_491, _61_493, insert, _61_496) -> begin
insert
end))

# 343 "FStar.Parser.Env.fst"
let commit_record_cache : Prims.unit  ->  Prims.unit = (
# 344 "FStar.Parser.Env.fst"
let _61_507 = record_cache_aux
in (match (_61_507) with
| (_61_499, _61_501, _61_503, _61_505, commit) -> begin
commit
end))

# 347 "FStar.Parser.Env.fst"
let extract_record : env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun e _61_10 -> (match (_61_10) with
| FStar_Syntax_Syntax.Sig_bundle (sigs, _61_512, _61_514, _61_516) -> begin
(
# 349 "FStar.Parser.Env.fst"
let is_rec = (FStar_Util.for_some (fun _61_7 -> (match (_61_7) with
| (FStar_Syntax_Syntax.RecordType (_)) | (FStar_Syntax_Syntax.RecordConstructor (_)) -> begin
true
end
| _61_527 -> begin
false
end)))
in (
# 354 "FStar.Parser.Env.fst"
let find_dc = (fun dc -> (FStar_All.pipe_right sigs (FStar_Util.find_opt (fun _61_8 -> (match (_61_8) with
| FStar_Syntax_Syntax.Sig_datacon (lid, _61_534, _61_536, _61_538, _61_540, _61_542, _61_544, _61_546) -> begin
(FStar_Ident.lid_equals dc lid)
end
| _61_550 -> begin
false
end)))))
in (FStar_All.pipe_right sigs (FStar_List.iter (fun _61_9 -> (match (_61_9) with
| FStar_Syntax_Syntax.Sig_inductive_typ (typename, univs, parms, _61_556, _61_558, dc::[], tags, _61_563) -> begin
(match ((let _150_393 = (find_dc dc)
in (FStar_All.pipe_left FStar_Util.must _150_393))) with
| FStar_Syntax_Syntax.Sig_datacon (constrname, _61_568, t, _61_571, _61_573, _61_575, _61_577, _61_579) -> begin
(
# 363 "FStar.Parser.Env.fst"
let _61_585 = (FStar_Syntax_Util.arrow_formals t)
in (match (_61_585) with
| (formals, _61_584) -> begin
(
# 364 "FStar.Parser.Env.fst"
let is_rec = (is_rec tags)
in (
# 365 "FStar.Parser.Env.fst"
let fields = (FStar_All.pipe_right formals (FStar_List.collect (fun _61_589 -> (match (_61_589) with
| (x, q) -> begin
if ((FStar_Syntax_Syntax.is_null_bv x) || (is_rec && (FStar_Syntax_Syntax.is_implicit q))) then begin
[]
end else begin
(let _150_397 = (let _150_396 = (let _150_395 = if is_rec then begin
(FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname)
end else begin
x.FStar_Syntax_Syntax.ppname
end
in (qual constrname _150_395))
in (_150_396, x.FStar_Syntax_Syntax.sort))
in (_150_397)::[])
end
end))))
in (
# 370 "FStar.Parser.Env.fst"
let record = {typename = typename; constrname = constrname; parms = parms; fields = fields; is_record = is_rec}
in (insert_record_cache record))))
end))
end
| _61_593 -> begin
()
end)
end
| _61_595 -> begin
()
end))))))
end
| _61_597 -> begin
()
end))

# 382 "FStar.Parser.Env.fst"
let try_lookup_record_or_dc_by_field_name : env  ->  FStar_Ident.lident  ->  (record_or_dc * FStar_Ident.lident) Prims.option = (fun env fieldname -> (
# 383 "FStar.Parser.Env.fst"
let maybe_add_constrname = (fun ns c -> (
# 384 "FStar.Parser.Env.fst"
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
(let _150_408 = (aux tl)
in (hd)::_150_408)
end))
in (aux ns)))
in (
# 389 "FStar.Parser.Env.fst"
let find_in_cache = (fun fieldname -> (
# 391 "FStar.Parser.Env.fst"
let _61_615 = (fieldname.FStar_Ident.ns, fieldname.FStar_Ident.ident)
in (match (_61_615) with
| (ns, fieldname) -> begin
(let _150_413 = (peek_record_cache ())
in (FStar_Util.find_map _150_413 (fun record -> (
# 393 "FStar.Parser.Env.fst"
let constrname = record.constrname.FStar_Ident.ident
in (
# 394 "FStar.Parser.Env.fst"
let ns = (maybe_add_constrname ns constrname)
in (
# 395 "FStar.Parser.Env.fst"
let fname = (FStar_Ident.lid_of_ids (FStar_List.append ns ((fieldname)::[])))
in (FStar_Util.find_map record.fields (fun _61_623 -> (match (_61_623) with
| (f, _61_622) -> begin
if (FStar_Ident.lid_equals fname f) then begin
Some ((record, fname))
end else begin
None
end
end)))))))))
end)))
in (resolve_in_open_namespaces env fieldname find_in_cache))))

# 402 "FStar.Parser.Env.fst"
let try_lookup_record_by_field_name : env  ->  FStar_Ident.lident  ->  (record_or_dc * FStar_Ident.lident) Prims.option = (fun env fieldname -> (match ((try_lookup_record_or_dc_by_field_name env fieldname)) with
| Some (r, f) when r.is_record -> begin
Some ((r, f))
end
| _61_631 -> begin
None
end))

# 407 "FStar.Parser.Env.fst"
let try_lookup_projector_by_field_name : env  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * Prims.bool) Prims.option = (fun env fieldname -> (match ((try_lookup_record_or_dc_by_field_name env fieldname)) with
| Some (r, f) -> begin
Some ((f, r.is_record))
end
| _61_639 -> begin
None
end))

# 412 "FStar.Parser.Env.fst"
let qualify_field_to_record : env  ->  record_or_dc  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env recd f -> (
# 413 "FStar.Parser.Env.fst"
let qualify = (fun fieldname -> (
# 414 "FStar.Parser.Env.fst"
let _61_647 = (fieldname.FStar_Ident.ns, fieldname.FStar_Ident.ident)
in (match (_61_647) with
| (ns, fieldname) -> begin
(
# 415 "FStar.Parser.Env.fst"
let constrname = recd.constrname.FStar_Ident.ident
in (
# 416 "FStar.Parser.Env.fst"
let fname = (FStar_Ident.lid_of_ids (FStar_List.append (FStar_List.append ns ((constrname)::[])) ((fieldname)::[])))
in (FStar_Util.find_map recd.fields (fun _61_653 -> (match (_61_653) with
| (f, _61_652) -> begin
if (FStar_Ident.lid_equals fname f) then begin
Some (fname)
end else begin
None
end
end)))))
end)))
in (resolve_in_open_namespaces env f qualify)))

# 423 "FStar.Parser.Env.fst"
let unique : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  Prims.bool = (fun any_val exclude_if env lid -> (
# 424 "FStar.Parser.Env.fst"
let this_env = (
# 424 "FStar.Parser.Env.fst"
let _61_658 = env
in {curmodule = _61_658.curmodule; modules = _61_658.modules; open_namespaces = []; modul_abbrevs = _61_658.modul_abbrevs; sigaccum = _61_658.sigaccum; localbindings = _61_658.localbindings; recbindings = _61_658.recbindings; sigmap = _61_658.sigmap; default_result_effect = _61_658.default_result_effect; iface = _61_658.iface; admitted_iface = _61_658.admitted_iface; expect_typ = _61_658.expect_typ})
in (match ((try_lookup_lid' any_val exclude_if env lid)) with
| None -> begin
true
end
| Some (_61_663) -> begin
false
end)))

# 429 "FStar.Parser.Env.fst"
let push_bv : env  ->  FStar_Ident.ident  ->  (env * FStar_Syntax_Syntax.bv) = (fun env x -> (
# 430 "FStar.Parser.Env.fst"
let bv = (FStar_Syntax_Syntax.gen_bv x.FStar_Ident.idText (Some (x.FStar_Ident.idRange)) FStar_Syntax_Syntax.tun)
in ((
# 431 "FStar.Parser.Env.fst"
let _61_668 = env
in {curmodule = _61_668.curmodule; modules = _61_668.modules; open_namespaces = _61_668.open_namespaces; modul_abbrevs = _61_668.modul_abbrevs; sigaccum = _61_668.sigaccum; localbindings = ((x, bv))::env.localbindings; recbindings = _61_668.recbindings; sigmap = _61_668.sigmap; default_result_effect = _61_668.default_result_effect; iface = _61_668.iface; admitted_iface = _61_668.admitted_iface; expect_typ = _61_668.expect_typ}), bv)))

# 433 "FStar.Parser.Env.fst"
let push_top_level_rec_binding : env  ->  FStar_Ident.ident  ->  FStar_Syntax_Syntax.delta_depth  ->  env = (fun env x dd -> (
# 434 "FStar.Parser.Env.fst"
let l = (qualify env x)
in if (unique false true env l) then begin
(
# 436 "FStar.Parser.Env.fst"
let _61_674 = env
in {curmodule = _61_674.curmodule; modules = _61_674.modules; open_namespaces = _61_674.open_namespaces; modul_abbrevs = _61_674.modul_abbrevs; sigaccum = _61_674.sigaccum; localbindings = _61_674.localbindings; recbindings = ((x, l, dd))::env.recbindings; sigmap = _61_674.sigmap; default_result_effect = _61_674.default_result_effect; iface = _61_674.iface; admitted_iface = _61_674.admitted_iface; expect_typ = _61_674.expect_typ})
end else begin
(Prims.raise (FStar_Syntax_Syntax.Error (((Prims.strcat "Duplicate top-level names " l.FStar_Ident.str), (FStar_Ident.range_of_lid l)))))
end))

# 439 "FStar.Parser.Env.fst"
let push_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env s -> (
# 440 "FStar.Parser.Env.fst"
let err = (fun l -> (
# 441 "FStar.Parser.Env.fst"
let sopt = (FStar_Util.smap_try_find (sigmap env) l.FStar_Ident.str)
in (
# 442 "FStar.Parser.Env.fst"
let r = (match (sopt) with
| Some (se, _61_683) -> begin
(match ((let _150_455 = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_Util.find_opt (FStar_Ident.lid_equals l) _150_455))) with
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
in (let _150_458 = (let _150_457 = (let _150_456 = (FStar_Util.format2 "Duplicate top-level names [%s]; previously declared at %s" (FStar_Ident.text_of_lid l) r)
in (_150_456, (FStar_Ident.range_of_lid l)))
in FStar_Syntax_Syntax.Error (_150_457))
in (Prims.raise _150_458)))))
in (
# 450 "FStar.Parser.Env.fst"
let env = (
# 451 "FStar.Parser.Env.fst"
let _61_701 = (match (s) with
| FStar_Syntax_Syntax.Sig_let (_61_692) -> begin
(false, true)
end
| FStar_Syntax_Syntax.Sig_bundle (_61_695) -> begin
(true, true)
end
| _61_698 -> begin
(false, false)
end)
in (match (_61_701) with
| (any_val, exclude_if) -> begin
(
# 455 "FStar.Parser.Env.fst"
let lids = (FStar_Syntax_Util.lids_of_sigelt s)
in (match ((FStar_Util.find_map lids (fun l -> if (not ((unique any_val exclude_if env l))) then begin
Some (l)
end else begin
None
end))) with
| None -> begin
(
# 457 "FStar.Parser.Env.fst"
let _61_705 = (extract_record env s)
in (
# 457 "FStar.Parser.Env.fst"
let _61_707 = env
in {curmodule = _61_707.curmodule; modules = _61_707.modules; open_namespaces = _61_707.open_namespaces; modul_abbrevs = _61_707.modul_abbrevs; sigaccum = (s)::env.sigaccum; localbindings = _61_707.localbindings; recbindings = _61_707.recbindings; sigmap = _61_707.sigmap; default_result_effect = _61_707.default_result_effect; iface = _61_707.iface; admitted_iface = _61_707.admitted_iface; expect_typ = _61_707.expect_typ}))
end
| Some (l) -> begin
(err l)
end))
end))
in (
# 460 "FStar.Parser.Env.fst"
let _61_726 = (match (s) with
| FStar_Syntax_Syntax.Sig_bundle (ses, _61_714, _61_716, _61_718) -> begin
(let _150_462 = (FStar_List.map (fun se -> (let _150_461 = (FStar_Syntax_Util.lids_of_sigelt se)
in (_150_461, se))) ses)
in (env, _150_462))
end
| _61_723 -> begin
(let _150_465 = (let _150_464 = (let _150_463 = (FStar_Syntax_Util.lids_of_sigelt s)
in (_150_463, s))
in (_150_464)::[])
in (env, _150_465))
end)
in (match (_61_726) with
| (env, lss) -> begin
(
# 463 "FStar.Parser.Env.fst"
let _61_731 = (FStar_All.pipe_right lss (FStar_List.iter (fun _61_729 -> (match (_61_729) with
| (lids, se) -> begin
(FStar_All.pipe_right lids (FStar_List.iter (fun lid -> (FStar_Util.smap_add (sigmap env) lid.FStar_Ident.str (se, (env.iface && (not (env.admitted_iface))))))))
end))))
in env)
end)))))

# 468 "FStar.Parser.Env.fst"
let push_namespace : env  ->  FStar_Ident.lident  ->  env = (fun env lid -> (
# 469 "FStar.Parser.Env.fst"
let _61_735 = env
in {curmodule = _61_735.curmodule; modules = _61_735.modules; open_namespaces = (lid)::env.open_namespaces; modul_abbrevs = _61_735.modul_abbrevs; sigaccum = _61_735.sigaccum; localbindings = _61_735.localbindings; recbindings = _61_735.recbindings; sigmap = _61_735.sigmap; default_result_effect = _61_735.default_result_effect; iface = _61_735.iface; admitted_iface = _61_735.admitted_iface; expect_typ = _61_735.expect_typ}))

# 471 "FStar.Parser.Env.fst"
let push_module_abbrev : env  ->  FStar_Ident.ident  ->  FStar_Ident.lident  ->  env = (fun env x l -> if (FStar_All.pipe_right env.modul_abbrevs (FStar_Util.for_some (fun _61_743 -> (match (_61_743) with
| (y, _61_742) -> begin
(x.FStar_Ident.idText = y.FStar_Ident.idText)
end)))) then begin
(let _150_481 = (let _150_480 = (let _150_479 = (FStar_Util.format1 "Module %s is already defined" x.FStar_Ident.idText)
in (_150_479, x.FStar_Ident.idRange))
in FStar_Syntax_Syntax.Error (_150_480))
in (Prims.raise _150_481))
end else begin
(
# 474 "FStar.Parser.Env.fst"
let _61_744 = env
in {curmodule = _61_744.curmodule; modules = _61_744.modules; open_namespaces = _61_744.open_namespaces; modul_abbrevs = ((x, l))::env.modul_abbrevs; sigaccum = _61_744.sigaccum; localbindings = _61_744.localbindings; recbindings = _61_744.recbindings; sigmap = _61_744.sigmap; default_result_effect = _61_744.default_result_effect; iface = _61_744.iface; admitted_iface = _61_744.admitted_iface; expect_typ = _61_744.expect_typ})
end)

# 476 "FStar.Parser.Env.fst"
let check_admits : env  ->  Prims.unit = (fun env -> (FStar_All.pipe_right env.sigaccum (FStar_List.iter (fun se -> (match (se) with
| FStar_Syntax_Syntax.Sig_declare_typ (l, u, t, quals, r) -> begin
(match ((try_lookup_lid env l)) with
| None -> begin
(
# 481 "FStar.Parser.Env.fst"
let _61_756 = (let _150_487 = (let _150_486 = (FStar_Range.string_of_range (FStar_Ident.range_of_lid l))
in (let _150_485 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format2 "%s: Warning: Admitting %s without a definition\n" _150_486 _150_485)))
in (FStar_Util.print_string _150_487))
in (FStar_Util.smap_add (sigmap env) l.FStar_Ident.str (FStar_Syntax_Syntax.Sig_declare_typ ((l, u, t, (FStar_Syntax_Syntax.Assumption)::quals, r)), false)))
end
| Some (_61_759) -> begin
()
end)
end
| _61_762 -> begin
()
end)))))

# 487 "FStar.Parser.Env.fst"
let finish : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env modul -> (
# 488 "FStar.Parser.Env.fst"
let _61_822 = (FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations (FStar_List.iter (fun _61_12 -> (match (_61_12) with
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _61_769, _61_771) -> begin
if ((FStar_List.contains FStar_Syntax_Syntax.Private quals) || (FStar_List.contains FStar_Syntax_Syntax.Abstract quals)) then begin
(FStar_All.pipe_right ses (FStar_List.iter (fun _61_11 -> (match (_61_11) with
| FStar_Syntax_Syntax.Sig_datacon (lid, _61_777, _61_779, _61_781, _61_783, _61_785, _61_787, _61_789) -> begin
(FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str)
end
| _61_793 -> begin
()
end))))
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _61_796, _61_798, quals, _61_801) -> begin
if (FStar_List.contains FStar_Syntax_Syntax.Private quals) then begin
(FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str)
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_let ((_61_805, lbs), r, _61_810, quals) -> begin
(
# 501 "FStar.Parser.Env.fst"
let _61_815 = if ((FStar_List.contains FStar_Syntax_Syntax.Private quals) || (FStar_List.contains FStar_Syntax_Syntax.Abstract quals)) then begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (let _150_498 = (let _150_497 = (let _150_496 = (let _150_495 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _150_495.FStar_Syntax_Syntax.fv_name)
in _150_496.FStar_Syntax_Syntax.v)
in _150_497.FStar_Ident.str)
in (FStar_Util.smap_remove (sigmap env) _150_498)))))
end else begin
()
end
in if ((FStar_List.contains FStar_Syntax_Syntax.Abstract quals) && (not ((FStar_List.contains FStar_Syntax_Syntax.Private quals)))) then begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (
# 509 "FStar.Parser.Env.fst"
let lid = (let _150_501 = (let _150_500 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _150_500.FStar_Syntax_Syntax.fv_name)
in _150_501.FStar_Syntax_Syntax.v)
in (
# 510 "FStar.Parser.Env.fst"
let decl = FStar_Syntax_Syntax.Sig_declare_typ ((lid, lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp, (FStar_Syntax_Syntax.Assumption)::quals, r))
in (FStar_Util.smap_add (sigmap env) lid.FStar_Ident.str (decl, false)))))))
end else begin
()
end)
end
| _61_821 -> begin
()
end))))
in (
# 514 "FStar.Parser.Env.fst"
let _61_824 = env
in {curmodule = None; modules = ((modul.FStar_Syntax_Syntax.name, modul))::env.modules; open_namespaces = []; modul_abbrevs = []; sigaccum = []; localbindings = []; recbindings = []; sigmap = _61_824.sigmap; default_result_effect = _61_824.default_result_effect; iface = _61_824.iface; admitted_iface = _61_824.admitted_iface; expect_typ = _61_824.expect_typ})))

# 523 "FStar.Parser.Env.fst"
type env_stack_ops =
{push : env  ->  env; mark : env  ->  env; reset_mark : env  ->  env; commit_mark : env  ->  env; pop : env  ->  env}

# 523 "FStar.Parser.Env.fst"
let is_Mkenv_stack_ops : env_stack_ops  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv_stack_ops"))))

# 531 "FStar.Parser.Env.fst"
let stack_ops : env_stack_ops = (
# 532 "FStar.Parser.Env.fst"
let stack = (FStar_Util.mk_ref [])
in (
# 533 "FStar.Parser.Env.fst"
let push = (fun env -> (
# 534 "FStar.Parser.Env.fst"
let _61_835 = (push_record_cache ())
in (
# 535 "FStar.Parser.Env.fst"
let _61_837 = (let _150_551 = (let _150_550 = (FStar_ST.read stack)
in (env)::_150_550)
in (FStar_ST.op_Colon_Equals stack _150_551))
in (
# 536 "FStar.Parser.Env.fst"
let _61_839 = env
in (let _150_552 = (FStar_Util.smap_copy (sigmap env))
in {curmodule = _61_839.curmodule; modules = _61_839.modules; open_namespaces = _61_839.open_namespaces; modul_abbrevs = _61_839.modul_abbrevs; sigaccum = _61_839.sigaccum; localbindings = _61_839.localbindings; recbindings = _61_839.recbindings; sigmap = _150_552; default_result_effect = _61_839.default_result_effect; iface = _61_839.iface; admitted_iface = _61_839.admitted_iface; expect_typ = _61_839.expect_typ})))))
in (
# 537 "FStar.Parser.Env.fst"
let pop = (fun env -> (match ((FStar_ST.read stack)) with
| env::tl -> begin
(
# 539 "FStar.Parser.Env.fst"
let _61_846 = (pop_record_cache ())
in (
# 540 "FStar.Parser.Env.fst"
let _61_848 = (FStar_ST.op_Colon_Equals stack tl)
in env))
end
| _61_851 -> begin
(FStar_All.failwith "Impossible: Too many pops")
end))
in (
# 543 "FStar.Parser.Env.fst"
let commit_mark = (fun env -> (
# 544 "FStar.Parser.Env.fst"
let _61_854 = (commit_record_cache ())
in (match ((FStar_ST.read stack)) with
| _61_858::tl -> begin
(
# 546 "FStar.Parser.Env.fst"
let _61_860 = (FStar_ST.op_Colon_Equals stack tl)
in env)
end
| _61_863 -> begin
(FStar_All.failwith "Impossible: Too many pops")
end)))
in {push = push; mark = push; reset_mark = pop; commit_mark = commit_mark; pop = pop}))))

# 554 "FStar.Parser.Env.fst"
let push : env  ->  env = (fun env -> (stack_ops.push env))

# 555 "FStar.Parser.Env.fst"
let mark : env  ->  env = (fun env -> (stack_ops.mark env))

# 556 "FStar.Parser.Env.fst"
let reset_mark : env  ->  env = (fun env -> (stack_ops.reset_mark env))

# 557 "FStar.Parser.Env.fst"
let commit_mark : env  ->  env = (fun env -> (stack_ops.commit_mark env))

# 558 "FStar.Parser.Env.fst"
let pop : env  ->  env = (fun env -> (stack_ops.pop env))

# 560 "FStar.Parser.Env.fst"
let export_interface : FStar_Ident.lident  ->  env  ->  env = (fun m env -> (
# 562 "FStar.Parser.Env.fst"
let sigelt_in_m = (fun se -> (match ((FStar_Syntax_Util.lids_of_sigelt se)) with
| l::_61_874 -> begin
(l.FStar_Ident.nsstr = m.FStar_Ident.str)
end
| _61_878 -> begin
false
end))
in (
# 566 "FStar.Parser.Env.fst"
let sm = (sigmap env)
in (
# 567 "FStar.Parser.Env.fst"
let env = (pop env)
in (
# 568 "FStar.Parser.Env.fst"
let keys = (FStar_Util.smap_keys sm)
in (
# 569 "FStar.Parser.Env.fst"
let sm' = (sigmap env)
in (
# 570 "FStar.Parser.Env.fst"
let _61_902 = (FStar_All.pipe_right keys (FStar_List.iter (fun k -> (match ((FStar_Util.smap_try_find sm' k)) with
| Some (se, true) when (sigelt_in_m se) -> begin
(
# 573 "FStar.Parser.Env.fst"
let _61_888 = (FStar_Util.smap_remove sm' k)
in (
# 575 "FStar.Parser.Env.fst"
let se = (match (se) with
| FStar_Syntax_Syntax.Sig_declare_typ (l, u, t, q, r) -> begin
FStar_Syntax_Syntax.Sig_declare_typ ((l, u, t, (FStar_Syntax_Syntax.Assumption)::q, r))
end
| _61_898 -> begin
se
end)
in (FStar_Util.smap_add sm' k (se, false))))
end
| _61_901 -> begin
()
end))))
in env)))))))

# 582 "FStar.Parser.Env.fst"
let finish_module_or_interface : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env modul -> (
# 583 "FStar.Parser.Env.fst"
let _61_906 = if (not (modul.FStar_Syntax_Syntax.is_interface)) then begin
(check_admits env)
end else begin
()
end
in (finish env modul)))

# 587 "FStar.Parser.Env.fst"
let prepare_module_or_interface : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  (env * Prims.bool) = (fun intf admitted env mname -> (
# 588 "FStar.Parser.Env.fst"
let prep = (fun env -> (
# 589 "FStar.Parser.Env.fst"
let open_ns = if (FStar_Ident.lid_equals mname FStar_Syntax_Const.prims_lid) then begin
[]
end else begin
if (FStar_Ident.lid_equals mname FStar_Syntax_Const.st_lid) then begin
(FStar_Syntax_Const.prims_lid)::[]
end else begin
if (FStar_Ident.lid_equals mname FStar_Syntax_Const.all_lid) then begin
(FStar_Syntax_Const.prims_lid)::(FStar_Syntax_Const.st_lid)::[]
end else begin
(FStar_Syntax_Const.prims_lid)::(FStar_Syntax_Const.st_lid)::(FStar_Syntax_Const.all_lid)::(FStar_Syntax_Const.fstar_ns_lid)::[]
end
end
end
in (
# 593 "FStar.Parser.Env.fst"
let _61_915 = env
in {curmodule = Some (mname); modules = _61_915.modules; open_namespaces = open_ns; modul_abbrevs = _61_915.modul_abbrevs; sigaccum = _61_915.sigaccum; localbindings = _61_915.localbindings; recbindings = _61_915.recbindings; sigmap = env.sigmap; default_result_effect = _61_915.default_result_effect; iface = intf; admitted_iface = admitted; expect_typ = _61_915.expect_typ})))
in (match ((FStar_All.pipe_right env.modules (FStar_Util.find_opt (fun _61_920 -> (match (_61_920) with
| (l, _61_919) -> begin
(FStar_Ident.lid_equals l mname)
end))))) with
| None -> begin
((prep env), false)
end
| Some (_61_923, m) -> begin
(
# 598 "FStar.Parser.Env.fst"
let _61_927 = if ((not (m.FStar_Syntax_Syntax.is_interface)) || intf) then begin
(let _150_591 = (let _150_590 = (let _150_589 = (FStar_Util.format1 "Duplicate module or interface name: %s" mname.FStar_Ident.str)
in (_150_589, (FStar_Ident.range_of_lid mname)))
in FStar_Syntax_Syntax.Error (_150_590))
in (Prims.raise _150_591))
end else begin
()
end
in (let _150_593 = (let _150_592 = (push env)
in (prep _150_592))
in (_150_593, true)))
end)))

# 603 "FStar.Parser.Env.fst"
let enter_monad_scope : env  ->  FStar_Ident.ident  ->  env = (fun env mname -> (
# 604 "FStar.Parser.Env.fst"
let curmod = (current_module env)
in (
# 605 "FStar.Parser.Env.fst"
let mscope = (FStar_Ident.lid_of_ids (FStar_List.append curmod.FStar_Ident.ns ((curmod.FStar_Ident.ident)::(mname)::[])))
in (
# 606 "FStar.Parser.Env.fst"
let _61_933 = env
in {curmodule = Some (mscope); modules = _61_933.modules; open_namespaces = (curmod)::env.open_namespaces; modul_abbrevs = _61_933.modul_abbrevs; sigaccum = _61_933.sigaccum; localbindings = _61_933.localbindings; recbindings = _61_933.recbindings; sigmap = _61_933.sigmap; default_result_effect = _61_933.default_result_effect; iface = _61_933.iface; admitted_iface = _61_933.admitted_iface; expect_typ = _61_933.expect_typ}))))

# 610 "FStar.Parser.Env.fst"
let exit_monad_scope : env  ->  env  ->  env = (fun env0 env -> (
# 611 "FStar.Parser.Env.fst"
let _61_937 = env
in {curmodule = env0.curmodule; modules = _61_937.modules; open_namespaces = env0.open_namespaces; modul_abbrevs = _61_937.modul_abbrevs; sigaccum = _61_937.sigaccum; localbindings = _61_937.localbindings; recbindings = _61_937.recbindings; sigmap = _61_937.sigmap; default_result_effect = _61_937.default_result_effect; iface = _61_937.iface; admitted_iface = _61_937.admitted_iface; expect_typ = _61_937.expect_typ}))

# 615 "FStar.Parser.Env.fst"
let fail_or = (fun lookup lid -> (match ((lookup lid)) with
| None -> begin
(let _150_609 = (let _150_608 = (let _150_607 = (FStar_Util.format1 "Identifier not found: [%s]" (FStar_Ident.text_of_lid lid))
in (_150_607, (FStar_Ident.range_of_lid lid)))
in FStar_Syntax_Syntax.Error (_150_608))
in (Prims.raise _150_609))
end
| Some (r) -> begin
r
end))

# 620 "FStar.Parser.Env.fst"
let fail_or2 = (fun lookup id -> (match ((lookup id)) with
| None -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (((Prims.strcat (Prims.strcat "Identifier not found [" id.FStar_Ident.idText) "]"), id.FStar_Ident.idRange))))
end
| Some (r) -> begin
r
end))




