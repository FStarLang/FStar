
open Prims
# 32 "FStar.Parser.Env.fst"
type env =
{curmodule : FStar_Ident.lident Prims.option; modules : (FStar_Ident.lident * FStar_Syntax_Syntax.modul) Prims.list; open_namespaces : FStar_Ident.lident Prims.list; modul_abbrevs : (FStar_Ident.ident * FStar_Ident.lident) Prims.list; sigaccum : FStar_Syntax_Syntax.sigelts; localbindings : (FStar_Ident.ident * FStar_Syntax_Syntax.bv) Prims.list; recbindings : (FStar_Ident.ident * FStar_Ident.lid * FStar_Syntax_Syntax.delta_depth) Prims.list; sigmap : (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap Prims.list; default_result_effect : FStar_Ident.lident; iface : Prims.bool; admitted_iface : Prims.bool; expect_typ : Prims.bool}

# 34 "FStar.Parser.Env.fst"
let is_Mkenv : env  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv"))))

# 47 "FStar.Parser.Env.fst"
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

# 51 "FStar.Parser.Env.fst"
type record_or_dc =
{typename : FStar_Ident.lident; constrname : FStar_Ident.lident; parms : FStar_Syntax_Syntax.binders; fields : (FStar_Syntax_Syntax.fieldname * FStar_Syntax_Syntax.typ) Prims.list; is_record : Prims.bool}

# 53 "FStar.Parser.Env.fst"
let is_Mkrecord_or_dc : record_or_dc  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkrecord_or_dc"))))

# 95 "FStar.Parser.Env.fst"
let open_modules : env  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.modul) Prims.list = (fun e -> e.modules)

# 97 "FStar.Parser.Env.fst"
let current_module : env  ->  FStar_Ident.lident = (fun env -> (match (env.curmodule) with
| None -> begin
(FStar_All.failwith "Unset current module")
end
| Some (m) -> begin
m
end))

# 100 "FStar.Parser.Env.fst"
let qual : FStar_Ident.lident  ->  FStar_Ident.ident  ->  FStar_Ident.lident = (fun lid id -> (let _150_90 = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns ((lid.FStar_Ident.ident)::(id)::[])))
in (FStar_Ident.set_lid_range _150_90 id.FStar_Ident.idRange)))

# 101 "FStar.Parser.Env.fst"
let qualify : env  ->  FStar_Ident.ident  ->  FStar_Ident.lident = (fun env id -> (let _150_95 = (current_module env)
in (qual _150_95 id)))

# 102 "FStar.Parser.Env.fst"
let qualify_lid : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (
# 104 "FStar.Parser.Env.fst"
let cur = (current_module env)
in (let _150_100 = (FStar_Ident.lid_of_ids (FStar_List.append (FStar_List.append (FStar_List.append cur.FStar_Ident.ns ((cur.FStar_Ident.ident)::[])) lid.FStar_Ident.ns) ((lid.FStar_Ident.ident)::[])))
in (FStar_Ident.set_lid_range _150_100 (FStar_Ident.range_of_lid lid)))))

# 105 "FStar.Parser.Env.fst"
let new_sigmap = (fun _61_52 -> (match (()) with
| () -> begin
(FStar_Util.smap_create 100)
end))

# 106 "FStar.Parser.Env.fst"
let empty_env : Prims.unit  ->  env = (fun _61_53 -> (match (()) with
| () -> begin
(let _150_105 = (let _150_104 = (new_sigmap ())
in (_150_104)::[])
in {curmodule = None; modules = []; open_namespaces = []; modul_abbrevs = []; sigaccum = []; localbindings = []; recbindings = []; sigmap = _150_105; default_result_effect = FStar_Syntax_Const.effect_ML_lid; iface = false; admitted_iface = false; expect_typ = false})
end))

# 118 "FStar.Parser.Env.fst"
let sigmap : env  ->  (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap = (fun env -> (FStar_List.hd env.sigmap))

# 119 "FStar.Parser.Env.fst"
let default_total : env  ->  env = (fun env -> (
# 120 "FStar.Parser.Env.fst"
let _61_56 = env
in {curmodule = _61_56.curmodule; modules = _61_56.modules; open_namespaces = _61_56.open_namespaces; modul_abbrevs = _61_56.modul_abbrevs; sigaccum = _61_56.sigaccum; localbindings = _61_56.localbindings; recbindings = _61_56.recbindings; sigmap = _61_56.sigmap; default_result_effect = FStar_Syntax_Const.effect_Tot_lid; iface = _61_56.iface; admitted_iface = _61_56.admitted_iface; expect_typ = _61_56.expect_typ}))

# 120 "FStar.Parser.Env.fst"
let default_ml : env  ->  env = (fun env -> (
# 121 "FStar.Parser.Env.fst"
let _61_59 = env
in {curmodule = _61_59.curmodule; modules = _61_59.modules; open_namespaces = _61_59.open_namespaces; modul_abbrevs = _61_59.modul_abbrevs; sigaccum = _61_59.sigaccum; localbindings = _61_59.localbindings; recbindings = _61_59.recbindings; sigmap = _61_59.sigmap; default_result_effect = FStar_Syntax_Const.effect_ML_lid; iface = _61_59.iface; admitted_iface = _61_59.admitted_iface; expect_typ = _61_59.expect_typ}))

# 121 "FStar.Parser.Env.fst"
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

# 126 "FStar.Parser.Env.fst"
let bv_to_name : FStar_Syntax_Syntax.bv  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.term = (fun bv r -> (FStar_Syntax_Syntax.bv_to_name (set_bv_range bv r)))

# 128 "FStar.Parser.Env.fst"
let unmangleMap : (Prims.string * Prims.string * FStar_Syntax_Syntax.delta_depth * FStar_Syntax_Syntax.fv_qual Prims.option) Prims.list = (("op_ColonColon", "Cons", FStar_Syntax_Syntax.Delta_constant, Some (FStar_Syntax_Syntax.Data_ctor)))::(("not", "op_Negation", FStar_Syntax_Syntax.Delta_equational, None))::[]

# 131 "FStar.Parser.Env.fst"
let unmangleOpName : FStar_Ident.ident  ->  FStar_Syntax_Syntax.term Prims.option = (fun id -> (FStar_Util.find_map unmangleMap (fun _61_75 -> (match (_61_75) with
| (x, y, dd, dq) -> begin
if (id.FStar_Ident.idText = x) then begin
(let _150_124 = (let _150_123 = (FStar_Ident.lid_of_path (("Prims")::(y)::[]) id.FStar_Ident.idRange)
in (FStar_Syntax_Syntax.fvar _150_123 dd dq))
in Some (_150_124))
end else begin
None
end
end))))

# 136 "FStar.Parser.Env.fst"
let try_lookup_id : env  ->  FStar_Ident.ident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env id -> (match ((unmangleOpName id)) with
| Some (f) -> begin
Some (f)
end
| _61_81 -> begin
(FStar_Util.find_map env.localbindings (fun _61_1 -> (match (_61_1) with
| (id', x) when (id'.FStar_Ident.idText = id.FStar_Ident.idText) -> begin
(let _150_130 = (bv_to_name x id.FStar_Ident.idRange)
in Some (_150_130))
end
| _61_87 -> begin
None
end)))
end))

# 145 "FStar.Parser.Env.fst"
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
in (let _150_141 = (let _150_140 = (current_module env)
in (_150_140)::env.open_namespaces)
in (aux _150_141))))

# 156 "FStar.Parser.Env.fst"
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

# 166 "FStar.Parser.Env.fst"
let resolve_in_open_namespaces = (fun env lid finder -> (let _150_153 = (expand_module_abbrevs env lid)
in (resolve_in_open_namespaces' env _150_153 finder)))

# 169 "FStar.Parser.Env.fst"
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

# 182 "FStar.Parser.Env.fst"
let lb_fv : FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.fv = (fun lbs lid -> (let _150_162 = (FStar_Util.find_map lbs (fun lb -> (
# 186 "FStar.Parser.Env.fst"
let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in if (FStar_Syntax_Syntax.fv_eq_lid fv lid) then begin
Some (fv)
end else begin
None
end)))
in (FStar_All.pipe_right _150_162 FStar_Util.must)))

# 187 "FStar.Parser.Env.fst"
let try_lookup_name : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  foundname Prims.option = (fun any_val exclude_interf env lid -> (
# 195 "FStar.Parser.Env.fst"
let find_in_sig = (fun lid -> (match ((let _150_173 = (sigmap env)
in (FStar_Util.smap_try_find _150_173 lid.FStar_Ident.str))) with
| Some (_61_170, true) when exclude_interf -> begin
None
end
| None -> begin
None
end
| Some (se, _61_177) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_61_181) -> begin
(let _150_175 = (let _150_174 = (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.Delta_constant None)
in Term_name (_150_174))
in Some (_150_175))
end
| FStar_Syntax_Syntax.Sig_datacon (_61_184) -> begin
(let _150_178 = (let _150_177 = (let _150_176 = (fv_qual_of_se se)
in (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.Delta_constant _150_176))
in Term_name (_150_177))
in Some (_150_178))
end
| FStar_Syntax_Syntax.Sig_let ((_61_187, lbs), _61_191, _61_193, _61_195) -> begin
(
# 204 "FStar.Parser.Env.fst"
let fv = (lb_fv lbs lid)
in (let _150_180 = (let _150_179 = (FStar_Syntax_Syntax.fvar lid fv.FStar_Syntax_Syntax.fv_delta fv.FStar_Syntax_Syntax.fv_qual)
in Term_name (_150_179))
in Some (_150_180)))
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
in (let _150_185 = (let _150_184 = (let _150_183 = (fv_qual_of_se se)
in (FStar_Syntax_Syntax.fvar lid dd _150_183))
in Term_name (_150_184))
in Some (_150_185)))
end else begin
None
end
end
| FStar_Syntax_Syntax.Sig_new_effect (ne, _61_225) -> begin
(let _150_188 = (let _150_187 = (let _150_186 = (FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname (FStar_Ident.range_of_lid lid))
in (se, _150_186))
in Eff_name (_150_187))
in Some (_150_188))
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
(let _150_192 = (let _150_191 = (let _150_190 = (FStar_Ident.set_lid_range l (FStar_Ident.range_of_lid lid))
in (FStar_Syntax_Syntax.fvar _150_190 dd None))
in Term_name (_150_191))
in Some (_150_192))
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

# 234 "FStar.Parser.Env.fst"
let try_lookup_effect_name' : Prims.bool  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident) Prims.option = (fun exclude_interf env lid -> (match ((try_lookup_name true exclude_interf env lid)) with
| Some (Eff_name (o, l)) -> begin
Some ((o, l))
end
| _61_259 -> begin
None
end))

# 239 "FStar.Parser.Env.fst"
let try_lookup_effect_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env l -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some (o, l) -> begin
Some (l)
end
| _61_267 -> begin
None
end))

# 243 "FStar.Parser.Env.fst"
let try_lookup_effect_defn : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl Prims.option = (fun env l -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some (FStar_Syntax_Syntax.Sig_new_effect (ne, _61_272), _61_276) -> begin
Some (ne)
end
| _61_280 -> begin
None
end))

# 247 "FStar.Parser.Env.fst"
let is_effect_name : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((try_lookup_effect_name env lid)) with
| None -> begin
false
end
| Some (_61_285) -> begin
true
end))

# 251 "FStar.Parser.Env.fst"
let lookup_letbinding_quals : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.qualifier Prims.list = (fun env lid -> (
# 254 "FStar.Parser.Env.fst"
let find_in_sig = (fun lid -> (match ((let _150_217 = (sigmap env)
in (FStar_Util.smap_try_find _150_217 lid.FStar_Ident.str))) with
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

# 260 "FStar.Parser.Env.fst"
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

# 265 "FStar.Parser.Env.fst"
let try_lookup_let : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env lid -> (
# 268 "FStar.Parser.Env.fst"
let find_in_sig = (fun lid -> (match ((let _150_229 = (sigmap env)
in (FStar_Util.smap_try_find _150_229 lid.FStar_Ident.str))) with
| Some (FStar_Syntax_Syntax.Sig_let ((_61_327, lbs), _61_331, _61_333, _61_335), _61_339) -> begin
(
# 271 "FStar.Parser.Env.fst"
let fv = (lb_fv lbs lid)
in (let _150_230 = (FStar_Syntax_Syntax.fvar lid fv.FStar_Syntax_Syntax.fv_delta fv.FStar_Syntax_Syntax.fv_qual)
in Some (_150_230)))
end
| _61_344 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))

# 274 "FStar.Parser.Env.fst"
let try_lookup_definition : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env lid -> (
# 277 "FStar.Parser.Env.fst"
let find_in_sig = (fun lid -> (match ((let _150_237 = (sigmap env)
in (FStar_Util.smap_try_find _150_237 lid.FStar_Ident.str))) with
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

# 286 "FStar.Parser.Env.fst"
let try_lookup_lid' : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun any_val exclude_interf env lid -> (match ((try_lookup_name any_val exclude_interf env lid)) with
| Some (Term_name (e)) -> begin
Some (e)
end
| _61_377 -> begin
None
end))

# 292 "FStar.Parser.Env.fst"
let try_lookup_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env l -> (try_lookup_lid' env.iface false env l))

# 293 "FStar.Parser.Env.fst"
let try_lookup_datacon : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.fv Prims.option = (fun env lid -> (
# 296 "FStar.Parser.Env.fst"
let find_in_sig = (fun lid -> (match ((let _150_257 = (sigmap env)
in (FStar_Util.smap_try_find _150_257 lid.FStar_Ident.str))) with
| Some (FStar_Syntax_Syntax.Sig_declare_typ (_61_385, _61_387, _61_389, quals, _61_392), _61_396) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _61_6 -> (match (_61_6) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| _61_402 -> begin
false
end)))) then begin
(let _150_259 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant None)
in Some (_150_259))
end else begin
None
end
end
| Some (FStar_Syntax_Syntax.Sig_datacon (_61_404), _61_407) -> begin
(let _150_260 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in Some (_150_260))
end
| _61_411 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))

# 304 "FStar.Parser.Env.fst"
let find_all_datacons : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.list Prims.option = (fun env lid -> (
# 307 "FStar.Parser.Env.fst"
let find_in_sig = (fun lid -> (match ((let _150_267 = (sigmap env)
in (FStar_Util.smap_try_find _150_267 lid.FStar_Ident.str))) with
| Some (FStar_Syntax_Syntax.Sig_inductive_typ (_61_417, _61_419, _61_421, _61_423, _61_425, datas, _61_428, _61_430), _61_434) -> begin
Some (datas)
end
| _61_438 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))

# 311 "FStar.Parser.Env.fst"
let record_cache_aux : ((Prims.unit  ->  Prims.unit) * (Prims.unit  ->  Prims.unit) * (Prims.unit  ->  record_or_dc Prims.list) * (record_or_dc  ->  Prims.unit)) = (
# 315 "FStar.Parser.Env.fst"
let record_cache = (FStar_Util.mk_ref (([])::[]))
in (
# 316 "FStar.Parser.Env.fst"
let push = (fun _61_441 -> (match (()) with
| () -> begin
(let _150_281 = (let _150_280 = (let _150_278 = (FStar_ST.read record_cache)
in (FStar_List.hd _150_278))
in (let _150_279 = (FStar_ST.read record_cache)
in (_150_280)::_150_279))
in (FStar_ST.op_Colon_Equals record_cache _150_281))
end))
in (
# 318 "FStar.Parser.Env.fst"
let pop = (fun _61_443 -> (match (()) with
| () -> begin
(let _150_285 = (let _150_284 = (FStar_ST.read record_cache)
in (FStar_List.tl _150_284))
in (FStar_ST.op_Colon_Equals record_cache _150_285))
end))
in (
# 320 "FStar.Parser.Env.fst"
let peek = (fun _61_445 -> (match (()) with
| () -> begin
(let _150_288 = (FStar_ST.read record_cache)
in (FStar_List.hd _150_288))
end))
in (
# 321 "FStar.Parser.Env.fst"
let insert = (fun r -> (let _150_295 = (let _150_294 = (let _150_291 = (peek ())
in (r)::_150_291)
in (let _150_293 = (let _150_292 = (FStar_ST.read record_cache)
in (FStar_List.tl _150_292))
in (_150_294)::_150_293))
in (FStar_ST.op_Colon_Equals record_cache _150_295)))
in (push, pop, peek, insert))))))

# 322 "FStar.Parser.Env.fst"
let push_record_cache : Prims.unit  ->  Prims.unit = (
# 325 "FStar.Parser.Env.fst"
let _61_455 = record_cache_aux
in (match (_61_455) with
| (push, _61_450, _61_452, _61_454) -> begin
push
end))

# 326 "FStar.Parser.Env.fst"
let pop_record_cache : Prims.unit  ->  Prims.unit = (
# 329 "FStar.Parser.Env.fst"
let _61_463 = record_cache_aux
in (match (_61_463) with
| (_61_457, pop, _61_460, _61_462) -> begin
pop
end))

# 330 "FStar.Parser.Env.fst"
let peek_record_cache : Prims.unit  ->  record_or_dc Prims.list = (
# 333 "FStar.Parser.Env.fst"
let _61_471 = record_cache_aux
in (match (_61_471) with
| (_61_465, _61_467, peek, _61_470) -> begin
peek
end))

# 334 "FStar.Parser.Env.fst"
let insert_record_cache : record_or_dc  ->  Prims.unit = (
# 337 "FStar.Parser.Env.fst"
let _61_479 = record_cache_aux
in (match (_61_479) with
| (_61_473, _61_475, _61_477, insert) -> begin
insert
end))

# 338 "FStar.Parser.Env.fst"
let extract_record : env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun e _61_10 -> (match (_61_10) with
| FStar_Syntax_Syntax.Sig_bundle (sigs, _61_484, _61_486, _61_488) -> begin
(
# 342 "FStar.Parser.Env.fst"
let is_rec = (FStar_Util.for_some (fun _61_7 -> (match (_61_7) with
| (FStar_Syntax_Syntax.RecordType (_)) | (FStar_Syntax_Syntax.RecordConstructor (_)) -> begin
true
end
| _61_499 -> begin
false
end)))
in (
# 347 "FStar.Parser.Env.fst"
let find_dc = (fun dc -> (FStar_All.pipe_right sigs (FStar_Util.find_opt (fun _61_8 -> (match (_61_8) with
| FStar_Syntax_Syntax.Sig_datacon (lid, _61_506, _61_508, _61_510, _61_512, _61_514, _61_516, _61_518) -> begin
(FStar_Ident.lid_equals dc lid)
end
| _61_522 -> begin
false
end)))))
in (FStar_All.pipe_right sigs (FStar_List.iter (fun _61_9 -> (match (_61_9) with
| FStar_Syntax_Syntax.Sig_inductive_typ (typename, univs, parms, _61_528, _61_530, dc::[], tags, _61_535) -> begin
(match ((let _150_366 = (find_dc dc)
in (FStar_All.pipe_left FStar_Util.must _150_366))) with
| FStar_Syntax_Syntax.Sig_datacon (constrname, _61_540, t, _61_543, _61_545, _61_547, _61_549, _61_551) -> begin
(
# 356 "FStar.Parser.Env.fst"
let _61_557 = (FStar_Syntax_Util.arrow_formals t)
in (match (_61_557) with
| (formals, _61_556) -> begin
(
# 357 "FStar.Parser.Env.fst"
let is_rec = (is_rec tags)
in (
# 358 "FStar.Parser.Env.fst"
let fields = (FStar_All.pipe_right formals (FStar_List.collect (fun _61_561 -> (match (_61_561) with
| (x, q) -> begin
if ((FStar_Syntax_Syntax.is_null_bv x) || (is_rec && (FStar_Syntax_Syntax.is_implicit q))) then begin
[]
end else begin
(let _150_370 = (let _150_369 = (let _150_368 = if is_rec then begin
(FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname)
end else begin
x.FStar_Syntax_Syntax.ppname
end
in (qual constrname _150_368))
in (_150_369, x.FStar_Syntax_Syntax.sort))
in (_150_370)::[])
end
end))))
in (
# 363 "FStar.Parser.Env.fst"
let record = {typename = typename; constrname = constrname; parms = parms; fields = fields; is_record = is_rec}
in (insert_record_cache record))))
end))
end
| _61_565 -> begin
()
end)
end
| _61_567 -> begin
()
end))))))
end
| _61_569 -> begin
()
end))

# 373 "FStar.Parser.Env.fst"
let try_lookup_record_or_dc_by_field_name : env  ->  FStar_Ident.lident  ->  (record_or_dc * FStar_Ident.lident) Prims.option = (fun env fieldname -> (
# 376 "FStar.Parser.Env.fst"
let maybe_add_constrname = (fun ns c -> (
# 377 "FStar.Parser.Env.fst"
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
(let _150_381 = (aux tl)
in (hd)::_150_381)
end))
in (aux ns)))
in (
# 382 "FStar.Parser.Env.fst"
let find_in_cache = (fun fieldname -> (
# 384 "FStar.Parser.Env.fst"
let _61_587 = (fieldname.FStar_Ident.ns, fieldname.FStar_Ident.ident)
in (match (_61_587) with
| (ns, fieldname) -> begin
(let _150_386 = (peek_record_cache ())
in (FStar_Util.find_map _150_386 (fun record -> (
# 386 "FStar.Parser.Env.fst"
let constrname = record.constrname.FStar_Ident.ident
in (
# 387 "FStar.Parser.Env.fst"
let ns = (maybe_add_constrname ns constrname)
in (
# 388 "FStar.Parser.Env.fst"
let fname = (FStar_Ident.lid_of_ids (FStar_List.append ns ((fieldname)::[])))
in (FStar_Util.find_map record.fields (fun _61_595 -> (match (_61_595) with
| (f, _61_594) -> begin
if (FStar_Ident.lid_equals fname f) then begin
Some ((record, fname))
end else begin
None
end
end)))))))))
end)))
in (resolve_in_open_namespaces env fieldname find_in_cache))))

# 393 "FStar.Parser.Env.fst"
let try_lookup_record_by_field_name : env  ->  FStar_Ident.lident  ->  (record_or_dc * FStar_Ident.lident) Prims.option = (fun env fieldname -> (match ((try_lookup_record_or_dc_by_field_name env fieldname)) with
| Some (r, f) when r.is_record -> begin
Some ((r, f))
end
| _61_603 -> begin
None
end))

# 398 "FStar.Parser.Env.fst"
let try_lookup_projector_by_field_name : env  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * Prims.bool) Prims.option = (fun env fieldname -> (match ((try_lookup_record_or_dc_by_field_name env fieldname)) with
| Some (r, f) -> begin
Some ((f, r.is_record))
end
| _61_611 -> begin
None
end))

# 403 "FStar.Parser.Env.fst"
let qualify_field_to_record : env  ->  record_or_dc  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env recd f -> (
# 406 "FStar.Parser.Env.fst"
let qualify = (fun fieldname -> (
# 407 "FStar.Parser.Env.fst"
let _61_619 = (fieldname.FStar_Ident.ns, fieldname.FStar_Ident.ident)
in (match (_61_619) with
| (ns, fieldname) -> begin
(
# 408 "FStar.Parser.Env.fst"
let constrname = recd.constrname.FStar_Ident.ident
in (
# 409 "FStar.Parser.Env.fst"
let fname = (FStar_Ident.lid_of_ids (FStar_List.append (FStar_List.append ns ((constrname)::[])) ((fieldname)::[])))
in (FStar_Util.find_map recd.fields (fun _61_625 -> (match (_61_625) with
| (f, _61_624) -> begin
if (FStar_Ident.lid_equals fname f) then begin
Some (fname)
end else begin
None
end
end)))))
end)))
in (resolve_in_open_namespaces env f qualify)))

# 414 "FStar.Parser.Env.fst"
let unique : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  Prims.bool = (fun any_val exclude_if env lid -> (
# 417 "FStar.Parser.Env.fst"
let this_env = (
# 417 "FStar.Parser.Env.fst"
let _61_630 = env
in {curmodule = _61_630.curmodule; modules = _61_630.modules; open_namespaces = []; modul_abbrevs = _61_630.modul_abbrevs; sigaccum = _61_630.sigaccum; localbindings = _61_630.localbindings; recbindings = _61_630.recbindings; sigmap = _61_630.sigmap; default_result_effect = _61_630.default_result_effect; iface = _61_630.iface; admitted_iface = _61_630.admitted_iface; expect_typ = _61_630.expect_typ})
in (match ((try_lookup_lid' any_val exclude_if env lid)) with
| None -> begin
true
end
| Some (_61_635) -> begin
false
end)))

# 420 "FStar.Parser.Env.fst"
let push_bv : env  ->  FStar_Ident.ident  ->  (env * FStar_Syntax_Syntax.bv) = (fun env x -> (
# 423 "FStar.Parser.Env.fst"
let bv = (FStar_Syntax_Syntax.gen_bv x.FStar_Ident.idText (Some (x.FStar_Ident.idRange)) FStar_Syntax_Syntax.tun)
in ((
# 424 "FStar.Parser.Env.fst"
let _61_640 = env
in {curmodule = _61_640.curmodule; modules = _61_640.modules; open_namespaces = _61_640.open_namespaces; modul_abbrevs = _61_640.modul_abbrevs; sigaccum = _61_640.sigaccum; localbindings = ((x, bv))::env.localbindings; recbindings = _61_640.recbindings; sigmap = _61_640.sigmap; default_result_effect = _61_640.default_result_effect; iface = _61_640.iface; admitted_iface = _61_640.admitted_iface; expect_typ = _61_640.expect_typ}), bv)))

# 424 "FStar.Parser.Env.fst"
let push_top_level_rec_binding : env  ->  FStar_Ident.ident  ->  FStar_Syntax_Syntax.delta_depth  ->  env = (fun env x dd -> (
# 427 "FStar.Parser.Env.fst"
let l = (qualify env x)
in if (unique false true env l) then begin
(
# 429 "FStar.Parser.Env.fst"
let _61_646 = env
in {curmodule = _61_646.curmodule; modules = _61_646.modules; open_namespaces = _61_646.open_namespaces; modul_abbrevs = _61_646.modul_abbrevs; sigaccum = _61_646.sigaccum; localbindings = _61_646.localbindings; recbindings = ((x, l, dd))::env.recbindings; sigmap = _61_646.sigmap; default_result_effect = _61_646.default_result_effect; iface = _61_646.iface; admitted_iface = _61_646.admitted_iface; expect_typ = _61_646.expect_typ})
end else begin
(Prims.raise (FStar_Syntax_Syntax.Error (((Prims.strcat "Duplicate top-level names " l.FStar_Ident.str), (FStar_Ident.range_of_lid l)))))
end))

# 430 "FStar.Parser.Env.fst"
let push_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env s -> (
# 433 "FStar.Parser.Env.fst"
let err = (fun l -> (
# 434 "FStar.Parser.Env.fst"
let sopt = (let _150_428 = (sigmap env)
in (FStar_Util.smap_try_find _150_428 l.FStar_Ident.str))
in (
# 435 "FStar.Parser.Env.fst"
let r = (match (sopt) with
| Some (se, _61_655) -> begin
(match ((let _150_429 = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_Util.find_opt (FStar_Ident.lid_equals l) _150_429))) with
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
in (let _150_432 = (let _150_431 = (let _150_430 = (FStar_Util.format2 "Duplicate top-level names [%s]; previously declared at %s" (FStar_Ident.text_of_lid l) r)
in (_150_430, (FStar_Ident.range_of_lid l)))
in FStar_Syntax_Syntax.Error (_150_431))
in (Prims.raise _150_432)))))
in (
# 443 "FStar.Parser.Env.fst"
let env = (
# 444 "FStar.Parser.Env.fst"
let _61_673 = (match (s) with
| FStar_Syntax_Syntax.Sig_let (_61_664) -> begin
(false, true)
end
| FStar_Syntax_Syntax.Sig_bundle (_61_667) -> begin
(true, true)
end
| _61_670 -> begin
(false, false)
end)
in (match (_61_673) with
| (any_val, exclude_if) -> begin
(
# 448 "FStar.Parser.Env.fst"
let lids = (FStar_Syntax_Util.lids_of_sigelt s)
in (match ((FStar_Util.find_map lids (fun l -> if (not ((unique any_val exclude_if env l))) then begin
Some (l)
end else begin
None
end))) with
| None -> begin
(
# 450 "FStar.Parser.Env.fst"
let _61_677 = (extract_record env s)
in (
# 450 "FStar.Parser.Env.fst"
let _61_679 = env
in {curmodule = _61_679.curmodule; modules = _61_679.modules; open_namespaces = _61_679.open_namespaces; modul_abbrevs = _61_679.modul_abbrevs; sigaccum = (s)::env.sigaccum; localbindings = _61_679.localbindings; recbindings = _61_679.recbindings; sigmap = _61_679.sigmap; default_result_effect = _61_679.default_result_effect; iface = _61_679.iface; admitted_iface = _61_679.admitted_iface; expect_typ = _61_679.expect_typ}))
end
| Some (l) -> begin
(err l)
end))
end))
in (
# 453 "FStar.Parser.Env.fst"
let _61_698 = (match (s) with
| FStar_Syntax_Syntax.Sig_bundle (ses, _61_686, _61_688, _61_690) -> begin
(let _150_436 = (FStar_List.map (fun se -> (let _150_435 = (FStar_Syntax_Util.lids_of_sigelt se)
in (_150_435, se))) ses)
in (env, _150_436))
end
| _61_695 -> begin
(let _150_439 = (let _150_438 = (let _150_437 = (FStar_Syntax_Util.lids_of_sigelt s)
in (_150_437, s))
in (_150_438)::[])
in (env, _150_439))
end)
in (match (_61_698) with
| (env, lss) -> begin
(
# 456 "FStar.Parser.Env.fst"
let _61_703 = (FStar_All.pipe_right lss (FStar_List.iter (fun _61_701 -> (match (_61_701) with
| (lids, se) -> begin
(FStar_All.pipe_right lids (FStar_List.iter (fun lid -> (let _150_442 = (sigmap env)
in (FStar_Util.smap_add _150_442 lid.FStar_Ident.str (se, (env.iface && (not (env.admitted_iface)))))))))
end))))
in env)
end)))))

# 459 "FStar.Parser.Env.fst"
let push_namespace : env  ->  FStar_Ident.lident  ->  env = (fun env lid -> (
# 462 "FStar.Parser.Env.fst"
let _61_707 = env
in {curmodule = _61_707.curmodule; modules = _61_707.modules; open_namespaces = (lid)::env.open_namespaces; modul_abbrevs = _61_707.modul_abbrevs; sigaccum = _61_707.sigaccum; localbindings = _61_707.localbindings; recbindings = _61_707.recbindings; sigmap = _61_707.sigmap; default_result_effect = _61_707.default_result_effect; iface = _61_707.iface; admitted_iface = _61_707.admitted_iface; expect_typ = _61_707.expect_typ}))

# 462 "FStar.Parser.Env.fst"
let push_module_abbrev : env  ->  FStar_Ident.ident  ->  FStar_Ident.lident  ->  env = (fun env x l -> if (FStar_All.pipe_right env.modul_abbrevs (FStar_Util.for_some (fun _61_715 -> (match (_61_715) with
| (y, _61_714) -> begin
(x.FStar_Ident.idText = y.FStar_Ident.idText)
end)))) then begin
(let _150_456 = (let _150_455 = (let _150_454 = (FStar_Util.format1 "Module %s is already defined" x.FStar_Ident.idText)
in (_150_454, x.FStar_Ident.idRange))
in FStar_Syntax_Syntax.Error (_150_455))
in (Prims.raise _150_456))
end else begin
(
# 467 "FStar.Parser.Env.fst"
let _61_716 = env
in {curmodule = _61_716.curmodule; modules = _61_716.modules; open_namespaces = _61_716.open_namespaces; modul_abbrevs = ((x, l))::env.modul_abbrevs; sigaccum = _61_716.sigaccum; localbindings = _61_716.localbindings; recbindings = _61_716.recbindings; sigmap = _61_716.sigmap; default_result_effect = _61_716.default_result_effect; iface = _61_716.iface; admitted_iface = _61_716.admitted_iface; expect_typ = _61_716.expect_typ})
end)

# 467 "FStar.Parser.Env.fst"
let check_admits : env  ->  Prims.unit = (fun env -> (FStar_All.pipe_right env.sigaccum (FStar_List.iter (fun se -> (match (se) with
| FStar_Syntax_Syntax.Sig_declare_typ (l, u, t, quals, r) -> begin
(match ((try_lookup_lid env l)) with
| None -> begin
(
# 474 "FStar.Parser.Env.fst"
let _61_728 = (let _150_462 = (let _150_461 = (FStar_Range.string_of_range (FStar_Ident.range_of_lid l))
in (let _150_460 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format2 "%s: Warning: Admitting %s without a definition\n" _150_461 _150_460)))
in (FStar_Util.print_string _150_462))
in (let _150_463 = (sigmap env)
in (FStar_Util.smap_add _150_463 l.FStar_Ident.str (FStar_Syntax_Syntax.Sig_declare_typ ((l, u, t, (FStar_Syntax_Syntax.Assumption)::quals, r)), false))))
end
| Some (_61_731) -> begin
()
end)
end
| _61_734 -> begin
()
end)))))

# 478 "FStar.Parser.Env.fst"
let finish : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env modul -> (
# 481 "FStar.Parser.Env.fst"
let _61_794 = (FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations (FStar_List.iter (fun _61_12 -> (match (_61_12) with
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _61_741, _61_743) -> begin
if ((FStar_List.contains FStar_Syntax_Syntax.Private quals) || (FStar_List.contains FStar_Syntax_Syntax.Abstract quals)) then begin
(FStar_All.pipe_right ses (FStar_List.iter (fun _61_11 -> (match (_61_11) with
| FStar_Syntax_Syntax.Sig_datacon (lid, _61_749, _61_751, _61_753, _61_755, _61_757, _61_759, _61_761) -> begin
(let _150_470 = (sigmap env)
in (FStar_Util.smap_remove _150_470 lid.FStar_Ident.str))
end
| _61_765 -> begin
()
end))))
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _61_768, _61_770, quals, _61_773) -> begin
if (FStar_List.contains FStar_Syntax_Syntax.Private quals) then begin
(let _150_471 = (sigmap env)
in (FStar_Util.smap_remove _150_471 lid.FStar_Ident.str))
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_let ((_61_777, lbs), r, _61_782, quals) -> begin
(
# 494 "FStar.Parser.Env.fst"
let _61_787 = if ((FStar_List.contains FStar_Syntax_Syntax.Private quals) || (FStar_List.contains FStar_Syntax_Syntax.Abstract quals)) then begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (let _150_477 = (sigmap env)
in (let _150_476 = (let _150_475 = (let _150_474 = (let _150_473 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _150_473.FStar_Syntax_Syntax.fv_name)
in _150_474.FStar_Syntax_Syntax.v)
in _150_475.FStar_Ident.str)
in (FStar_Util.smap_remove _150_477 _150_476))))))
end else begin
()
end
in if ((FStar_List.contains FStar_Syntax_Syntax.Abstract quals) && (not ((FStar_List.contains FStar_Syntax_Syntax.Private quals)))) then begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (
# 502 "FStar.Parser.Env.fst"
let lid = (let _150_480 = (let _150_479 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _150_479.FStar_Syntax_Syntax.fv_name)
in _150_480.FStar_Syntax_Syntax.v)
in (
# 503 "FStar.Parser.Env.fst"
let decl = FStar_Syntax_Syntax.Sig_declare_typ ((lid, lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp, (FStar_Syntax_Syntax.Assumption)::quals, r))
in (let _150_481 = (sigmap env)
in (FStar_Util.smap_add _150_481 lid.FStar_Ident.str (decl, false))))))))
end else begin
()
end)
end
| _61_793 -> begin
()
end))))
in (
# 507 "FStar.Parser.Env.fst"
let _61_796 = env
in {curmodule = None; modules = ((modul.FStar_Syntax_Syntax.name, modul))::env.modules; open_namespaces = []; modul_abbrevs = _61_796.modul_abbrevs; sigaccum = []; localbindings = []; recbindings = []; sigmap = _61_796.sigmap; default_result_effect = _61_796.default_result_effect; iface = _61_796.iface; admitted_iface = _61_796.admitted_iface; expect_typ = _61_796.expect_typ})))

# 513 "FStar.Parser.Env.fst"
let push : env  ->  env = (fun env -> (
# 516 "FStar.Parser.Env.fst"
let _61_799 = (push_record_cache ())
in (
# 517 "FStar.Parser.Env.fst"
let _61_801 = env
in (let _150_486 = (let _150_485 = (let _150_484 = (sigmap env)
in (FStar_Util.smap_copy _150_484))
in (_150_485)::env.sigmap)
in {curmodule = _61_801.curmodule; modules = _61_801.modules; open_namespaces = _61_801.open_namespaces; modul_abbrevs = _61_801.modul_abbrevs; sigaccum = _61_801.sigaccum; localbindings = _61_801.localbindings; recbindings = _61_801.recbindings; sigmap = _150_486; default_result_effect = _61_801.default_result_effect; iface = _61_801.iface; admitted_iface = _61_801.admitted_iface; expect_typ = _61_801.expect_typ}))))

# 518 "FStar.Parser.Env.fst"
let mark : env  ->  env = (fun env -> (push env))

# 520 "FStar.Parser.Env.fst"
let reset_mark : env  ->  env = (fun env -> (
# 521 "FStar.Parser.Env.fst"
let _61_805 = env
in (let _150_491 = (FStar_List.tl env.sigmap)
in {curmodule = _61_805.curmodule; modules = _61_805.modules; open_namespaces = _61_805.open_namespaces; modul_abbrevs = _61_805.modul_abbrevs; sigaccum = _61_805.sigaccum; localbindings = _61_805.localbindings; recbindings = _61_805.recbindings; sigmap = _150_491; default_result_effect = _61_805.default_result_effect; iface = _61_805.iface; admitted_iface = _61_805.admitted_iface; expect_typ = _61_805.expect_typ})))

# 521 "FStar.Parser.Env.fst"
let commit_mark : env  ->  env = (fun env -> (match (env.sigmap) with
| hd::_61_810::tl -> begin
(
# 523 "FStar.Parser.Env.fst"
let _61_814 = env
in {curmodule = _61_814.curmodule; modules = _61_814.modules; open_namespaces = _61_814.open_namespaces; modul_abbrevs = _61_814.modul_abbrevs; sigaccum = _61_814.sigaccum; localbindings = _61_814.localbindings; recbindings = _61_814.recbindings; sigmap = (hd)::tl; default_result_effect = _61_814.default_result_effect; iface = _61_814.iface; admitted_iface = _61_814.admitted_iface; expect_typ = _61_814.expect_typ})
end
| _61_817 -> begin
(FStar_All.failwith "Impossible")
end))

# 524 "FStar.Parser.Env.fst"
let pop : env  ->  env = (fun env -> (match (env.sigmap) with
| _61_821::maps -> begin
(
# 527 "FStar.Parser.Env.fst"
let _61_823 = (pop_record_cache ())
in (
# 528 "FStar.Parser.Env.fst"
let _61_825 = env
in {curmodule = _61_825.curmodule; modules = _61_825.modules; open_namespaces = _61_825.open_namespaces; modul_abbrevs = _61_825.modul_abbrevs; sigaccum = _61_825.sigaccum; localbindings = _61_825.localbindings; recbindings = _61_825.recbindings; sigmap = maps; default_result_effect = _61_825.default_result_effect; iface = _61_825.iface; admitted_iface = _61_825.admitted_iface; expect_typ = _61_825.expect_typ}))
end
| _61_828 -> begin
(FStar_All.failwith "No more modules to pop")
end))

# 530 "FStar.Parser.Env.fst"
let export_interface : FStar_Ident.lident  ->  env  ->  env = (fun m env -> (
# 534 "FStar.Parser.Env.fst"
let sigelt_in_m = (fun se -> (match ((FStar_Syntax_Util.lids_of_sigelt se)) with
| l::_61_834 -> begin
(l.FStar_Ident.nsstr = m.FStar_Ident.str)
end
| _61_838 -> begin
false
end))
in (
# 538 "FStar.Parser.Env.fst"
let sm = (sigmap env)
in (
# 539 "FStar.Parser.Env.fst"
let env = (pop env)
in (
# 540 "FStar.Parser.Env.fst"
let keys = (FStar_Util.smap_keys sm)
in (
# 541 "FStar.Parser.Env.fst"
let sm' = (sigmap env)
in (
# 542 "FStar.Parser.Env.fst"
let _61_862 = (FStar_All.pipe_right keys (FStar_List.iter (fun k -> (match ((FStar_Util.smap_try_find sm' k)) with
| Some (se, true) when (sigelt_in_m se) -> begin
(
# 545 "FStar.Parser.Env.fst"
let _61_848 = (FStar_Util.smap_remove sm' k)
in (
# 547 "FStar.Parser.Env.fst"
let se = (match (se) with
| FStar_Syntax_Syntax.Sig_declare_typ (l, u, t, q, r) -> begin
FStar_Syntax_Syntax.Sig_declare_typ ((l, u, t, (FStar_Syntax_Syntax.Assumption)::q, r))
end
| _61_858 -> begin
se
end)
in (FStar_Util.smap_add sm' k (se, false))))
end
| _61_861 -> begin
()
end))))
in env)))))))

# 552 "FStar.Parser.Env.fst"
let finish_module_or_interface : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env modul -> (
# 555 "FStar.Parser.Env.fst"
let _61_866 = if (not (modul.FStar_Syntax_Syntax.is_interface)) then begin
(check_admits env)
end else begin
()
end
in (finish env modul)))

# 557 "FStar.Parser.Env.fst"
let prepare_module_or_interface : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  (env * Prims.bool) = (fun intf admitted env mname -> (
# 560 "FStar.Parser.Env.fst"
let prep = (fun env -> (
# 561 "FStar.Parser.Env.fst"
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
# 565 "FStar.Parser.Env.fst"
let _61_875 = env
in {curmodule = Some (mname); modules = _61_875.modules; open_namespaces = open_ns; modul_abbrevs = _61_875.modul_abbrevs; sigaccum = _61_875.sigaccum; localbindings = _61_875.localbindings; recbindings = _61_875.recbindings; sigmap = env.sigmap; default_result_effect = _61_875.default_result_effect; iface = intf; admitted_iface = admitted; expect_typ = _61_875.expect_typ})))
in (match ((FStar_All.pipe_right env.modules (FStar_Util.find_opt (fun _61_880 -> (match (_61_880) with
| (l, _61_879) -> begin
(FStar_Ident.lid_equals l mname)
end))))) with
| None -> begin
((prep env), false)
end
| Some (_61_883, m) -> begin
(
# 570 "FStar.Parser.Env.fst"
let _61_887 = if ((not (m.FStar_Syntax_Syntax.is_interface)) || intf) then begin
(let _150_520 = (let _150_519 = (let _150_518 = (FStar_Util.format1 "Duplicate module or interface name: %s" mname.FStar_Ident.str)
in (_150_518, (FStar_Ident.range_of_lid mname)))
in FStar_Syntax_Syntax.Error (_150_519))
in (Prims.raise _150_520))
end else begin
()
end
in (let _150_522 = (let _150_521 = (push env)
in (prep _150_521))
in (_150_522, true)))
end)))

# 573 "FStar.Parser.Env.fst"
let enter_monad_scope : env  ->  FStar_Ident.ident  ->  env = (fun env mname -> (
# 576 "FStar.Parser.Env.fst"
let curmod = (current_module env)
in (
# 577 "FStar.Parser.Env.fst"
let mscope = (FStar_Ident.lid_of_ids (FStar_List.append curmod.FStar_Ident.ns ((curmod.FStar_Ident.ident)::(mname)::[])))
in (
# 578 "FStar.Parser.Env.fst"
let _61_893 = env
in {curmodule = Some (mscope); modules = _61_893.modules; open_namespaces = (curmod)::env.open_namespaces; modul_abbrevs = _61_893.modul_abbrevs; sigaccum = _61_893.sigaccum; localbindings = _61_893.localbindings; recbindings = _61_893.recbindings; sigmap = _61_893.sigmap; default_result_effect = _61_893.default_result_effect; iface = _61_893.iface; admitted_iface = _61_893.admitted_iface; expect_typ = _61_893.expect_typ}))))

# 580 "FStar.Parser.Env.fst"
let exit_monad_scope : env  ->  env  ->  env = (fun env0 env -> (
# 583 "FStar.Parser.Env.fst"
let _61_897 = env
in {curmodule = env0.curmodule; modules = _61_897.modules; open_namespaces = env0.open_namespaces; modul_abbrevs = _61_897.modul_abbrevs; sigaccum = _61_897.sigaccum; localbindings = _61_897.localbindings; recbindings = _61_897.recbindings; sigmap = _61_897.sigmap; default_result_effect = _61_897.default_result_effect; iface = _61_897.iface; admitted_iface = _61_897.admitted_iface; expect_typ = _61_897.expect_typ}))

# 585 "FStar.Parser.Env.fst"
let fail_or = (fun lookup lid -> (match ((lookup lid)) with
| None -> begin
(let _150_538 = (let _150_537 = (let _150_536 = (FStar_Util.format1 "Identifier not found: [%s]" (FStar_Ident.text_of_lid lid))
in (_150_536, (FStar_Ident.range_of_lid lid)))
in FStar_Syntax_Syntax.Error (_150_537))
in (Prims.raise _150_538))
end
| Some (r) -> begin
r
end))

# 590 "FStar.Parser.Env.fst"
let fail_or2 = (fun lookup id -> (match ((lookup id)) with
| None -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (((Prims.strcat (Prims.strcat "Identifier not found [" id.FStar_Ident.idText) "]"), id.FStar_Ident.idRange))))
end
| Some (r) -> begin
r
end))




