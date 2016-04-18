
open Prims
# 34 "FStar.Parser.Env.fst"
type env =
{curmodule : FStar_Ident.lident Prims.option; modules : (FStar_Ident.lident * FStar_Syntax_Syntax.modul) Prims.list; open_namespaces : FStar_Ident.lident Prims.list; modul_abbrevs : (FStar_Ident.ident * FStar_Ident.lident) Prims.list; sigaccum : FStar_Syntax_Syntax.sigelts; localbindings : (FStar_Ident.ident * FStar_Syntax_Syntax.bv) Prims.list; recbindings : (FStar_Ident.ident * FStar_Ident.lid * FStar_Syntax_Syntax.delta_depth) Prims.list; sigmap : (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap Prims.list; default_result_effect : FStar_Ident.lident; iface : Prims.bool; admitted_iface : Prims.bool; expect_typ : Prims.bool}

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
| Term_name (_61_27) -> begin
_61_27
end))

# 51 "FStar.Parser.Env.fst"
let ___Eff_name____0 = (fun projectee -> (match (projectee) with
| Eff_name (_61_30) -> begin
_61_30
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
let new_sigmap = (fun _61_51 -> (match (()) with
| () -> begin
(FStar_Util.smap_create 100)
end))

# 107 "FStar.Parser.Env.fst"
let empty_env : Prims.unit  ->  env = (fun _61_52 -> (match (()) with
| () -> begin
(let _150_105 = (let _150_104 = (new_sigmap ())
in (_150_104)::[])
in {curmodule = None; modules = []; open_namespaces = []; modul_abbrevs = []; sigaccum = []; localbindings = []; recbindings = []; sigmap = _150_105; default_result_effect = FStar_Syntax_Const.effect_ML_lid; iface = false; admitted_iface = false; expect_typ = false})
end))

# 119 "FStar.Parser.Env.fst"
let sigmap : env  ->  (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap = (fun env -> (FStar_List.hd env.sigmap))

# 120 "FStar.Parser.Env.fst"
let default_total : env  ->  env = (fun env -> (
# 120 "FStar.Parser.Env.fst"
let _61_55 = env
in {curmodule = _61_55.curmodule; modules = _61_55.modules; open_namespaces = _61_55.open_namespaces; modul_abbrevs = _61_55.modul_abbrevs; sigaccum = _61_55.sigaccum; localbindings = _61_55.localbindings; recbindings = _61_55.recbindings; sigmap = _61_55.sigmap; default_result_effect = FStar_Syntax_Const.effect_Tot_lid; iface = _61_55.iface; admitted_iface = _61_55.admitted_iface; expect_typ = _61_55.expect_typ}))

# 121 "FStar.Parser.Env.fst"
let default_ml : env  ->  env = (fun env -> (
# 121 "FStar.Parser.Env.fst"
let _61_58 = env
in {curmodule = _61_58.curmodule; modules = _61_58.modules; open_namespaces = _61_58.open_namespaces; modul_abbrevs = _61_58.modul_abbrevs; sigaccum = _61_58.sigaccum; localbindings = _61_58.localbindings; recbindings = _61_58.recbindings; sigmap = _61_58.sigmap; default_result_effect = FStar_Syntax_Const.effect_ML_lid; iface = _61_58.iface; admitted_iface = _61_58.admitted_iface; expect_typ = _61_58.expect_typ}))

# 124 "FStar.Parser.Env.fst"
let set_bv_range : FStar_Syntax_Syntax.bv  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.bv = (fun bv r -> (
# 125 "FStar.Parser.Env.fst"
let id = (
# 125 "FStar.Parser.Env.fst"
let _61_62 = bv.FStar_Syntax_Syntax.ppname
in {FStar_Ident.idText = _61_62.FStar_Ident.idText; FStar_Ident.idRange = r})
in (
# 126 "FStar.Parser.Env.fst"
let _61_65 = bv
in {FStar_Syntax_Syntax.ppname = id; FStar_Syntax_Syntax.index = _61_65.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _61_65.FStar_Syntax_Syntax.sort})))

# 128 "FStar.Parser.Env.fst"
let bv_to_name : FStar_Syntax_Syntax.bv  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.term = (fun bv r -> (FStar_Syntax_Syntax.bv_to_name (set_bv_range bv r)))

# 130 "FStar.Parser.Env.fst"
let unmangleMap : (Prims.string * Prims.string * FStar_Syntax_Syntax.delta_depth * FStar_Syntax_Syntax.fv_qual Prims.option) Prims.list = (("op_ColonColon", "Cons", FStar_Syntax_Syntax.Delta_constant, Some (FStar_Syntax_Syntax.Data_ctor)))::(("not", "op_Negation", FStar_Syntax_Syntax.Delta_equational, None))::[]

# 133 "FStar.Parser.Env.fst"
let unmangleOpName : FStar_Ident.ident  ->  FStar_Syntax_Syntax.term Prims.option = (fun id -> (FStar_Util.find_map unmangleMap (fun _61_74 -> (match (_61_74) with
| (x, y, dd, dq) -> begin
if (id.FStar_Ident.idText = x) then begin
(let _150_124 = (let _150_123 = (FStar_Ident.lid_of_path (("Prims")::(y)::[]) id.FStar_Ident.idRange)
in (FStar_Syntax_Syntax.fvar _150_123 dd dq))
in Some (_150_124))
end else begin
None
end
end))))

# 138 "FStar.Parser.Env.fst"
let try_lookup_id : env  ->  FStar_Ident.ident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env id -> (match ((unmangleOpName id)) with
| Some (f) -> begin
Some (f)
end
| _61_80 -> begin
(FStar_Util.find_map env.localbindings (fun _61_1 -> (match (_61_1) with
| (id', x) when (id'.FStar_Ident.idText = id.FStar_Ident.idText) -> begin
(let _150_130 = (bv_to_name x id.FStar_Ident.idRange)
in Some (_150_130))
end
| _61_86 -> begin
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
| _61_96 -> begin
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

# 158 "FStar.Parser.Env.fst"
let expand_module_abbrevs : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (match (lid.FStar_Ident.ns) with
| id::[] -> begin
(match ((FStar_All.pipe_right env.modul_abbrevs (FStar_List.tryFind (fun _61_107 -> (match (_61_107) with
| (id', _61_106) -> begin
(id.FStar_Ident.idText = id'.FStar_Ident.idText)
end))))) with
| None -> begin
lid
end
| Some (_61_110, lid') -> begin
(FStar_Ident.lid_of_ids (FStar_List.append (FStar_Ident.ids_of_lid lid') ((lid.FStar_Ident.ident)::[])))
end)
end
| _61_115 -> begin
lid
end))

# 168 "FStar.Parser.Env.fst"
let resolve_in_open_namespaces = (fun env lid finder -> (let _150_153 = (expand_module_abbrevs env lid)
in (resolve_in_open_namespaces' env _150_153 finder)))

# 171 "FStar.Parser.Env.fst"
let fv_qual_of_se : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.fv_qual Prims.option = (fun _61_3 -> (match (_61_3) with
| FStar_Syntax_Syntax.Sig_datacon (_61_122, _61_124, _61_126, l, _61_129, quals, _61_132, _61_134) -> begin
(
# 173 "FStar.Parser.Env.fst"
let qopt = (FStar_Util.find_map quals (fun _61_2 -> (match (_61_2) with
| FStar_Syntax_Syntax.RecordConstructor (fs) -> begin
Some (FStar_Syntax_Syntax.Record_ctor ((l, fs)))
end
| _61_141 -> begin
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
| FStar_Syntax_Syntax.Sig_declare_typ (_61_146, _61_148, _61_150, quals, _61_153) -> begin
None
end
| _61_157 -> begin
None
end))

# 184 "FStar.Parser.Env.fst"
let lb_fv : FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.fv = (fun lbs lid -> (let _150_162 = (FStar_Util.find_map lbs (fun lb -> (
# 186 "FStar.Parser.Env.fst"
let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in if (FStar_Syntax_Syntax.fv_eq_lid fv lid) then begin
Some (fv)
end else begin
None
end)))
in (FStar_All.pipe_right _150_162 FStar_Util.must)))

# 189 "FStar.Parser.Env.fst"
let try_lookup_name : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  foundname Prims.option = (fun any_val exclude_interf env lid -> (
# 195 "FStar.Parser.Env.fst"
let find_in_sig = (fun lid -> (match ((let _150_173 = (sigmap env)
in (FStar_Util.smap_try_find _150_173 lid.FStar_Ident.str))) with
| Some (_61_169, true) when exclude_interf -> begin
None
end
| None -> begin
None
end
| Some (se, _61_176) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_61_180) -> begin
(let _150_175 = (let _150_174 = (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.Delta_constant None)
in Term_name (_150_174))
in Some (_150_175))
end
| FStar_Syntax_Syntax.Sig_datacon (_61_183) -> begin
(let _150_178 = (let _150_177 = (let _150_176 = (fv_qual_of_se se)
in (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.Delta_constant _150_176))
in Term_name (_150_177))
in Some (_150_178))
end
| FStar_Syntax_Syntax.Sig_let ((_61_186, lbs), _61_190, _61_192, _61_194) -> begin
(
# 204 "FStar.Parser.Env.fst"
let fv = (lb_fv lbs lid)
in (let _150_180 = (let _150_179 = (FStar_Syntax_Syntax.fvar lid fv.FStar_Syntax_Syntax.fv_delta fv.FStar_Syntax_Syntax.fv_qual)
in Term_name (_150_179))
in Some (_150_180)))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _61_200, _61_202, quals, _61_205) -> begin
if (any_val || (FStar_All.pipe_right quals (FStar_Util.for_some (fun _61_4 -> (match (_61_4) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| _61_211 -> begin
false
end))))) then begin
(
# 209 "FStar.Parser.Env.fst"
let dd = if (FStar_Syntax_Util.is_primop_lid lid) then begin
FStar_Syntax_Syntax.Delta_equational
end else begin
FStar_Syntax_Syntax.Delta_constant
end
in (let _150_184 = (let _150_183 = (let _150_182 = (fv_qual_of_se se)
in (FStar_Syntax_Syntax.fvar lid dd _150_182))
in Term_name (_150_183))
in Some (_150_184)))
end else begin
None
end
end
| FStar_Syntax_Syntax.Sig_new_effect (ne, _61_215) -> begin
(let _150_187 = (let _150_186 = (let _150_185 = (FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname (FStar_Ident.range_of_lid lid))
in (se, _150_185))
in Eff_name (_150_186))
in Some (_150_187))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (_61_219) -> begin
Some (Eff_name ((se, lid)))
end
| _61_222 -> begin
None
end)
end))
in (
# 219 "FStar.Parser.Env.fst"
let found_id = (match (lid.FStar_Ident.ns) with
| [] -> begin
(match ((try_lookup_id env lid.FStar_Ident.ident)) with
| Some (e) -> begin
Some (Term_name (e))
end
| None -> begin
(
# 224 "FStar.Parser.Env.fst"
let recname = (qualify env lid.FStar_Ident.ident)
in (FStar_Util.find_map env.recbindings (fun _61_231 -> (match (_61_231) with
| (id, l, dd) -> begin
if (id.FStar_Ident.idText = lid.FStar_Ident.ident.FStar_Ident.idText) then begin
(let _150_191 = (let _150_190 = (let _150_189 = (FStar_Ident.set_lid_range l (FStar_Ident.range_of_lid lid))
in (FStar_Syntax_Syntax.fvar _150_189 dd None))
in Term_name (_150_190))
in Some (_150_191))
end else begin
None
end
end))))
end)
end
| _61_233 -> begin
None
end)
in (match (found_id) with
| Some (_61_236) -> begin
found_id
end
| _61_239 -> begin
(resolve_in_open_namespaces env lid find_in_sig)
end))))

# 235 "FStar.Parser.Env.fst"
let try_lookup_effect_name' : Prims.bool  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident) Prims.option = (fun exclude_interf env lid -> (match ((try_lookup_name true exclude_interf env lid)) with
| Some (Eff_name (o, l)) -> begin
Some ((o, l))
end
| _61_249 -> begin
None
end))

# 239 "FStar.Parser.Env.fst"
let try_lookup_effect_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env l -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some (o, l) -> begin
Some (l)
end
| _61_257 -> begin
None
end))

# 243 "FStar.Parser.Env.fst"
let try_lookup_effect_defn : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl Prims.option = (fun env l -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some (FStar_Syntax_Syntax.Sig_new_effect (ne, _61_262), _61_266) -> begin
Some (ne)
end
| _61_270 -> begin
None
end))

# 247 "FStar.Parser.Env.fst"
let is_effect_name : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((try_lookup_effect_name env lid)) with
| None -> begin
false
end
| Some (_61_275) -> begin
true
end))

# 252 "FStar.Parser.Env.fst"
let lookup_letbinding_quals : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.qualifier Prims.list = (fun env lid -> (
# 253 "FStar.Parser.Env.fst"
let find_in_sig = (fun lid -> (match ((let _150_216 = (sigmap env)
in (FStar_Util.smap_try_find _150_216 lid.FStar_Ident.str))) with
| Some (FStar_Syntax_Syntax.Sig_declare_typ (lid, _61_283, _61_285, quals, _61_288), _61_292) -> begin
Some (quals)
end
| _61_296 -> begin
None
end))
in (match ((resolve_in_open_namespaces env lid find_in_sig)) with
| Some (quals) -> begin
quals
end
| _61_300 -> begin
[]
end)))

# 261 "FStar.Parser.Env.fst"
let try_lookup_module : env  ->  Prims.string Prims.list  ->  FStar_Syntax_Syntax.modul Prims.option = (fun env path -> (match ((FStar_List.tryFind (fun _61_305 -> (match (_61_305) with
| (mlid, modul) -> begin
((FStar_Ident.path_of_lid mlid) = path)
end)) env.modules)) with
| Some (_61_307, modul) -> begin
Some (modul)
end
| None -> begin
None
end))

# 266 "FStar.Parser.Env.fst"
let try_lookup_let : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env lid -> (
# 267 "FStar.Parser.Env.fst"
let find_in_sig = (fun lid -> (match ((let _150_228 = (sigmap env)
in (FStar_Util.smap_try_find _150_228 lid.FStar_Ident.str))) with
| Some (FStar_Syntax_Syntax.Sig_let ((_61_317, lbs), _61_321, _61_323, _61_325), _61_329) -> begin
(
# 270 "FStar.Parser.Env.fst"
let fv = (lb_fv lbs lid)
in (let _150_229 = (FStar_Syntax_Syntax.fvar lid fv.FStar_Syntax_Syntax.fv_delta fv.FStar_Syntax_Syntax.fv_qual)
in Some (_150_229)))
end
| _61_334 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))

# 275 "FStar.Parser.Env.fst"
let try_lookup_definition : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env lid -> (
# 276 "FStar.Parser.Env.fst"
let find_in_sig = (fun lid -> (match ((let _150_236 = (sigmap env)
in (FStar_Util.smap_try_find _150_236 lid.FStar_Ident.str))) with
| Some (FStar_Syntax_Syntax.Sig_let (lbs, _61_341, _61_343, _61_345), _61_349) -> begin
(FStar_Util.find_map (Prims.snd lbs) (fun lb -> (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv lid) -> begin
Some (lb.FStar_Syntax_Syntax.lbdef)
end
| _61_356 -> begin
None
end)))
end
| _61_358 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))

# 288 "FStar.Parser.Env.fst"
let try_lookup_lid' : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun any_val exclude_interf env lid -> (match ((try_lookup_name any_val exclude_interf env lid)) with
| Some (Term_name (e)) -> begin
Some (e)
end
| _61_367 -> begin
None
end))

# 292 "FStar.Parser.Env.fst"
let try_lookup_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env l -> (try_lookup_lid' env.iface false env l))

# 294 "FStar.Parser.Env.fst"
let try_lookup_datacon : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.fv Prims.option = (fun env lid -> (
# 295 "FStar.Parser.Env.fst"
let find_in_sig = (fun lid -> (match ((let _150_256 = (sigmap env)
in (FStar_Util.smap_try_find _150_256 lid.FStar_Ident.str))) with
| Some (FStar_Syntax_Syntax.Sig_declare_typ (_61_375, _61_377, _61_379, quals, _61_382), _61_386) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _61_5 -> (match (_61_5) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| _61_392 -> begin
false
end)))) then begin
(let _150_258 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant None)
in Some (_150_258))
end else begin
None
end
end
| Some (FStar_Syntax_Syntax.Sig_datacon (_61_394), _61_397) -> begin
(let _150_259 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in Some (_150_259))
end
| _61_401 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))

# 305 "FStar.Parser.Env.fst"
let find_all_datacons : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.list Prims.option = (fun env lid -> (
# 306 "FStar.Parser.Env.fst"
let find_in_sig = (fun lid -> (match ((let _150_266 = (sigmap env)
in (FStar_Util.smap_try_find _150_266 lid.FStar_Ident.str))) with
| Some (FStar_Syntax_Syntax.Sig_inductive_typ (_61_407, _61_409, _61_411, _61_413, _61_415, datas, _61_418, _61_420), _61_424) -> begin
Some (datas)
end
| _61_428 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))

# 313 "FStar.Parser.Env.fst"
let record_cache_aux : ((Prims.unit  ->  Prims.unit) * (Prims.unit  ->  Prims.unit) * (Prims.unit  ->  record_or_dc Prims.list) * (record_or_dc  ->  Prims.unit)) = (
# 314 "FStar.Parser.Env.fst"
let record_cache = (FStar_Util.mk_ref (([])::[]))
in (
# 315 "FStar.Parser.Env.fst"
let push = (fun _61_431 -> (match (()) with
| () -> begin
(let _150_280 = (let _150_279 = (let _150_277 = (FStar_ST.read record_cache)
in (FStar_List.hd _150_277))
in (let _150_278 = (FStar_ST.read record_cache)
in (_150_279)::_150_278))
in (FStar_ST.op_Colon_Equals record_cache _150_280))
end))
in (
# 317 "FStar.Parser.Env.fst"
let pop = (fun _61_433 -> (match (()) with
| () -> begin
(let _150_284 = (let _150_283 = (FStar_ST.read record_cache)
in (FStar_List.tl _150_283))
in (FStar_ST.op_Colon_Equals record_cache _150_284))
end))
in (
# 319 "FStar.Parser.Env.fst"
let peek = (fun _61_435 -> (match (()) with
| () -> begin
(let _150_287 = (FStar_ST.read record_cache)
in (FStar_List.hd _150_287))
end))
in (
# 320 "FStar.Parser.Env.fst"
let insert = (fun r -> (let _150_294 = (let _150_293 = (let _150_290 = (peek ())
in (r)::_150_290)
in (let _150_292 = (let _150_291 = (FStar_ST.read record_cache)
in (FStar_List.tl _150_291))
in (_150_293)::_150_292))
in (FStar_ST.op_Colon_Equals record_cache _150_294)))
in (push, pop, peek, insert))))))

# 323 "FStar.Parser.Env.fst"
let push_record_cache : Prims.unit  ->  Prims.unit = (
# 324 "FStar.Parser.Env.fst"
let _61_445 = record_cache_aux
in (match (_61_445) with
| (push, _61_440, _61_442, _61_444) -> begin
push
end))

# 327 "FStar.Parser.Env.fst"
let pop_record_cache : Prims.unit  ->  Prims.unit = (
# 328 "FStar.Parser.Env.fst"
let _61_453 = record_cache_aux
in (match (_61_453) with
| (_61_447, pop, _61_450, _61_452) -> begin
pop
end))

# 331 "FStar.Parser.Env.fst"
let peek_record_cache : Prims.unit  ->  record_or_dc Prims.list = (
# 332 "FStar.Parser.Env.fst"
let _61_461 = record_cache_aux
in (match (_61_461) with
| (_61_455, _61_457, peek, _61_460) -> begin
peek
end))

# 335 "FStar.Parser.Env.fst"
let insert_record_cache : record_or_dc  ->  Prims.unit = (
# 336 "FStar.Parser.Env.fst"
let _61_469 = record_cache_aux
in (match (_61_469) with
| (_61_463, _61_465, _61_467, insert) -> begin
insert
end))

# 339 "FStar.Parser.Env.fst"
let extract_record : env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun e _61_9 -> (match (_61_9) with
| FStar_Syntax_Syntax.Sig_bundle (sigs, _61_474, _61_476, _61_478) -> begin
(
# 341 "FStar.Parser.Env.fst"
let is_rec = (FStar_Util.for_some (fun _61_6 -> (match (_61_6) with
| (FStar_Syntax_Syntax.RecordType (_)) | (FStar_Syntax_Syntax.RecordConstructor (_)) -> begin
true
end
| _61_489 -> begin
false
end)))
in (
# 346 "FStar.Parser.Env.fst"
let find_dc = (fun dc -> (FStar_All.pipe_right sigs (FStar_Util.find_opt (fun _61_7 -> (match (_61_7) with
| FStar_Syntax_Syntax.Sig_datacon (lid, _61_496, _61_498, _61_500, _61_502, _61_504, _61_506, _61_508) -> begin
(FStar_Ident.lid_equals dc lid)
end
| _61_512 -> begin
false
end)))))
in (FStar_All.pipe_right sigs (FStar_List.iter (fun _61_8 -> (match (_61_8) with
| FStar_Syntax_Syntax.Sig_inductive_typ (typename, univs, parms, _61_518, _61_520, dc::[], tags, _61_525) -> begin
(match ((let _150_365 = (find_dc dc)
in (FStar_All.pipe_left FStar_Util.must _150_365))) with
| FStar_Syntax_Syntax.Sig_datacon (constrname, _61_530, t, _61_533, _61_535, _61_537, _61_539, _61_541) -> begin
(
# 355 "FStar.Parser.Env.fst"
let _61_547 = (FStar_Syntax_Util.arrow_formals t)
in (match (_61_547) with
| (formals, _61_546) -> begin
(
# 356 "FStar.Parser.Env.fst"
let is_rec = (is_rec tags)
in (
# 357 "FStar.Parser.Env.fst"
let fields = (FStar_All.pipe_right formals (FStar_List.collect (fun _61_551 -> (match (_61_551) with
| (x, q) -> begin
if ((FStar_Syntax_Syntax.is_null_bv x) || (is_rec && (FStar_Syntax_Syntax.is_implicit q))) then begin
[]
end else begin
(let _150_369 = (let _150_368 = (let _150_367 = if is_rec then begin
(FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname)
end else begin
x.FStar_Syntax_Syntax.ppname
end
in (qual constrname _150_367))
in (_150_368, x.FStar_Syntax_Syntax.sort))
in (_150_369)::[])
end
end))))
in (
# 362 "FStar.Parser.Env.fst"
let record = {typename = typename; constrname = constrname; parms = parms; fields = fields; is_record = is_rec}
in (insert_record_cache record))))
end))
end
| _61_555 -> begin
()
end)
end
| _61_557 -> begin
()
end))))))
end
| _61_559 -> begin
()
end))

# 374 "FStar.Parser.Env.fst"
let try_lookup_record_or_dc_by_field_name : env  ->  FStar_Ident.lident  ->  (record_or_dc * FStar_Ident.lident) Prims.option = (fun env fieldname -> (
# 375 "FStar.Parser.Env.fst"
let maybe_add_constrname = (fun ns c -> (
# 376 "FStar.Parser.Env.fst"
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
(let _150_380 = (aux tl)
in (hd)::_150_380)
end))
in (aux ns)))
in (
# 381 "FStar.Parser.Env.fst"
let find_in_cache = (fun fieldname -> (
# 383 "FStar.Parser.Env.fst"
let _61_577 = (fieldname.FStar_Ident.ns, fieldname.FStar_Ident.ident)
in (match (_61_577) with
| (ns, fieldname) -> begin
(let _150_385 = (peek_record_cache ())
in (FStar_Util.find_map _150_385 (fun record -> (
# 385 "FStar.Parser.Env.fst"
let constrname = record.constrname.FStar_Ident.ident
in (
# 386 "FStar.Parser.Env.fst"
let ns = (maybe_add_constrname ns constrname)
in (
# 387 "FStar.Parser.Env.fst"
let fname = (FStar_Ident.lid_of_ids (FStar_List.append ns ((fieldname)::[])))
in (FStar_Util.find_map record.fields (fun _61_585 -> (match (_61_585) with
| (f, _61_584) -> begin
if (FStar_Ident.lid_equals fname f) then begin
Some ((record, fname))
end else begin
None
end
end)))))))))
end)))
in (resolve_in_open_namespaces env fieldname find_in_cache))))

# 394 "FStar.Parser.Env.fst"
let try_lookup_record_by_field_name : env  ->  FStar_Ident.lident  ->  (record_or_dc * FStar_Ident.lident) Prims.option = (fun env fieldname -> (match ((try_lookup_record_or_dc_by_field_name env fieldname)) with
| Some (r, f) when r.is_record -> begin
Some ((r, f))
end
| _61_593 -> begin
None
end))

# 399 "FStar.Parser.Env.fst"
let try_lookup_projector_by_field_name : env  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * Prims.bool) Prims.option = (fun env fieldname -> (match ((try_lookup_record_or_dc_by_field_name env fieldname)) with
| Some (r, f) -> begin
Some ((f, r.is_record))
end
| _61_601 -> begin
None
end))

# 404 "FStar.Parser.Env.fst"
let qualify_field_to_record : env  ->  record_or_dc  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env recd f -> (
# 405 "FStar.Parser.Env.fst"
let qualify = (fun fieldname -> (
# 406 "FStar.Parser.Env.fst"
let _61_609 = (fieldname.FStar_Ident.ns, fieldname.FStar_Ident.ident)
in (match (_61_609) with
| (ns, fieldname) -> begin
(
# 407 "FStar.Parser.Env.fst"
let constrname = recd.constrname.FStar_Ident.ident
in (
# 408 "FStar.Parser.Env.fst"
let fname = (FStar_Ident.lid_of_ids (FStar_List.append (FStar_List.append ns ((constrname)::[])) ((fieldname)::[])))
in (FStar_Util.find_map recd.fields (fun _61_615 -> (match (_61_615) with
| (f, _61_614) -> begin
if (FStar_Ident.lid_equals fname f) then begin
Some (fname)
end else begin
None
end
end)))))
end)))
in (resolve_in_open_namespaces env f qualify)))

# 415 "FStar.Parser.Env.fst"
let unique : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  Prims.bool = (fun any_val exclude_if env lid -> (
# 416 "FStar.Parser.Env.fst"
let this_env = (
# 416 "FStar.Parser.Env.fst"
let _61_620 = env
in {curmodule = _61_620.curmodule; modules = _61_620.modules; open_namespaces = []; modul_abbrevs = _61_620.modul_abbrevs; sigaccum = _61_620.sigaccum; localbindings = _61_620.localbindings; recbindings = _61_620.recbindings; sigmap = _61_620.sigmap; default_result_effect = _61_620.default_result_effect; iface = _61_620.iface; admitted_iface = _61_620.admitted_iface; expect_typ = _61_620.expect_typ})
in (match ((try_lookup_lid' any_val exclude_if env lid)) with
| None -> begin
true
end
| Some (_61_625) -> begin
false
end)))

# 421 "FStar.Parser.Env.fst"
let push_bv : env  ->  FStar_Ident.ident  ->  (env * FStar_Syntax_Syntax.bv) = (fun env x -> (
# 422 "FStar.Parser.Env.fst"
let bv = (FStar_Syntax_Syntax.gen_bv x.FStar_Ident.idText (Some (x.FStar_Ident.idRange)) FStar_Syntax_Syntax.tun)
in ((
# 423 "FStar.Parser.Env.fst"
let _61_630 = env
in {curmodule = _61_630.curmodule; modules = _61_630.modules; open_namespaces = _61_630.open_namespaces; modul_abbrevs = _61_630.modul_abbrevs; sigaccum = _61_630.sigaccum; localbindings = ((x, bv))::env.localbindings; recbindings = _61_630.recbindings; sigmap = _61_630.sigmap; default_result_effect = _61_630.default_result_effect; iface = _61_630.iface; admitted_iface = _61_630.admitted_iface; expect_typ = _61_630.expect_typ}), bv)))

# 425 "FStar.Parser.Env.fst"
let push_top_level_rec_binding : env  ->  FStar_Ident.ident  ->  FStar_Syntax_Syntax.delta_depth  ->  env = (fun env x dd -> (
# 426 "FStar.Parser.Env.fst"
let l = (qualify env x)
in if (unique false true env l) then begin
(
# 428 "FStar.Parser.Env.fst"
let _61_636 = env
in {curmodule = _61_636.curmodule; modules = _61_636.modules; open_namespaces = _61_636.open_namespaces; modul_abbrevs = _61_636.modul_abbrevs; sigaccum = _61_636.sigaccum; localbindings = _61_636.localbindings; recbindings = ((x, l, dd))::env.recbindings; sigmap = _61_636.sigmap; default_result_effect = _61_636.default_result_effect; iface = _61_636.iface; admitted_iface = _61_636.admitted_iface; expect_typ = _61_636.expect_typ})
end else begin
(Prims.raise (FStar_Syntax_Syntax.Error (((Prims.strcat "Duplicate top-level names " l.FStar_Ident.str), (FStar_Ident.range_of_lid l)))))
end))

# 431 "FStar.Parser.Env.fst"
let push_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env s -> (
# 432 "FStar.Parser.Env.fst"
let err = (fun l -> (
# 433 "FStar.Parser.Env.fst"
let sopt = (let _150_427 = (sigmap env)
in (FStar_Util.smap_try_find _150_427 l.FStar_Ident.str))
in (
# 434 "FStar.Parser.Env.fst"
let r = (match (sopt) with
| Some (se, _61_645) -> begin
(match ((let _150_428 = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_Util.find_opt (FStar_Ident.lid_equals l) _150_428))) with
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
in (let _150_431 = (let _150_430 = (let _150_429 = (FStar_Util.format2 "Duplicate top-level names [%s]; previously declared at %s" (FStar_Ident.text_of_lid l) r)
in (_150_429, (FStar_Ident.range_of_lid l)))
in FStar_Syntax_Syntax.Error (_150_430))
in (Prims.raise _150_431)))))
in (
# 442 "FStar.Parser.Env.fst"
let env = (
# 443 "FStar.Parser.Env.fst"
let _61_663 = (match (s) with
| FStar_Syntax_Syntax.Sig_let (_61_654) -> begin
(false, true)
end
| FStar_Syntax_Syntax.Sig_bundle (_61_657) -> begin
(true, true)
end
| _61_660 -> begin
(false, false)
end)
in (match (_61_663) with
| (any_val, exclude_if) -> begin
(
# 447 "FStar.Parser.Env.fst"
let lids = (FStar_Syntax_Util.lids_of_sigelt s)
in (match ((FStar_Util.find_map lids (fun l -> if (not ((unique any_val exclude_if env l))) then begin
Some (l)
end else begin
None
end))) with
| None -> begin
(
# 449 "FStar.Parser.Env.fst"
let _61_667 = (extract_record env s)
in (
# 449 "FStar.Parser.Env.fst"
let _61_669 = env
in {curmodule = _61_669.curmodule; modules = _61_669.modules; open_namespaces = _61_669.open_namespaces; modul_abbrevs = _61_669.modul_abbrevs; sigaccum = (s)::env.sigaccum; localbindings = _61_669.localbindings; recbindings = _61_669.recbindings; sigmap = _61_669.sigmap; default_result_effect = _61_669.default_result_effect; iface = _61_669.iface; admitted_iface = _61_669.admitted_iface; expect_typ = _61_669.expect_typ}))
end
| Some (l) -> begin
(err l)
end))
end))
in (
# 452 "FStar.Parser.Env.fst"
let _61_688 = (match (s) with
| FStar_Syntax_Syntax.Sig_bundle (ses, _61_676, _61_678, _61_680) -> begin
(let _150_435 = (FStar_List.map (fun se -> (let _150_434 = (FStar_Syntax_Util.lids_of_sigelt se)
in (_150_434, se))) ses)
in (env, _150_435))
end
| _61_685 -> begin
(let _150_438 = (let _150_437 = (let _150_436 = (FStar_Syntax_Util.lids_of_sigelt s)
in (_150_436, s))
in (_150_437)::[])
in (env, _150_438))
end)
in (match (_61_688) with
| (env, lss) -> begin
(
# 455 "FStar.Parser.Env.fst"
let _61_693 = (FStar_All.pipe_right lss (FStar_List.iter (fun _61_691 -> (match (_61_691) with
| (lids, se) -> begin
(FStar_All.pipe_right lids (FStar_List.iter (fun lid -> (let _150_441 = (sigmap env)
in (FStar_Util.smap_add _150_441 lid.FStar_Ident.str (se, (env.iface && (not (env.admitted_iface)))))))))
end))))
in env)
end)))))

# 460 "FStar.Parser.Env.fst"
let push_namespace : env  ->  FStar_Ident.lident  ->  env = (fun env lid -> (
# 461 "FStar.Parser.Env.fst"
let _61_697 = env
in {curmodule = _61_697.curmodule; modules = _61_697.modules; open_namespaces = (lid)::env.open_namespaces; modul_abbrevs = _61_697.modul_abbrevs; sigaccum = _61_697.sigaccum; localbindings = _61_697.localbindings; recbindings = _61_697.recbindings; sigmap = _61_697.sigmap; default_result_effect = _61_697.default_result_effect; iface = _61_697.iface; admitted_iface = _61_697.admitted_iface; expect_typ = _61_697.expect_typ}))

# 463 "FStar.Parser.Env.fst"
let push_module_abbrev : env  ->  FStar_Ident.ident  ->  FStar_Ident.lident  ->  env = (fun env x l -> if (FStar_All.pipe_right env.modul_abbrevs (FStar_Util.for_some (fun _61_705 -> (match (_61_705) with
| (y, _61_704) -> begin
(x.FStar_Ident.idText = y.FStar_Ident.idText)
end)))) then begin
(let _150_455 = (let _150_454 = (let _150_453 = (FStar_Util.format1 "Module %s is already defined" x.FStar_Ident.idText)
in (_150_453, x.FStar_Ident.idRange))
in FStar_Syntax_Syntax.Error (_150_454))
in (Prims.raise _150_455))
end else begin
(
# 466 "FStar.Parser.Env.fst"
let _61_706 = env
in {curmodule = _61_706.curmodule; modules = _61_706.modules; open_namespaces = _61_706.open_namespaces; modul_abbrevs = ((x, l))::env.modul_abbrevs; sigaccum = _61_706.sigaccum; localbindings = _61_706.localbindings; recbindings = _61_706.recbindings; sigmap = _61_706.sigmap; default_result_effect = _61_706.default_result_effect; iface = _61_706.iface; admitted_iface = _61_706.admitted_iface; expect_typ = _61_706.expect_typ})
end)

# 468 "FStar.Parser.Env.fst"
let check_admits : env  ->  Prims.unit = (fun env -> (FStar_All.pipe_right env.sigaccum (FStar_List.iter (fun se -> (match (se) with
| FStar_Syntax_Syntax.Sig_declare_typ (l, u, t, quals, r) -> begin
(match ((try_lookup_lid env l)) with
| None -> begin
(
# 473 "FStar.Parser.Env.fst"
let _61_718 = (let _150_461 = (let _150_460 = (FStar_Range.string_of_range (FStar_Ident.range_of_lid l))
in (let _150_459 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format2 "%s: Warning: Admitting %s without a definition\n" _150_460 _150_459)))
in (FStar_Util.print_string _150_461))
in (let _150_462 = (sigmap env)
in (FStar_Util.smap_add _150_462 l.FStar_Ident.str (FStar_Syntax_Syntax.Sig_declare_typ ((l, u, t, (FStar_Syntax_Syntax.Assumption)::quals, r)), false))))
end
| Some (_61_721) -> begin
()
end)
end
| _61_724 -> begin
()
end)))))

# 479 "FStar.Parser.Env.fst"
let finish : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env modul -> (
# 480 "FStar.Parser.Env.fst"
let _61_784 = (FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations (FStar_List.iter (fun _61_11 -> (match (_61_11) with
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _61_731, _61_733) -> begin
if ((FStar_List.contains FStar_Syntax_Syntax.Private quals) || (FStar_List.contains FStar_Syntax_Syntax.Abstract quals)) then begin
(FStar_All.pipe_right ses (FStar_List.iter (fun _61_10 -> (match (_61_10) with
| FStar_Syntax_Syntax.Sig_datacon (lid, _61_739, _61_741, _61_743, _61_745, _61_747, _61_749, _61_751) -> begin
(let _150_469 = (sigmap env)
in (FStar_Util.smap_remove _150_469 lid.FStar_Ident.str))
end
| _61_755 -> begin
()
end))))
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _61_758, _61_760, quals, _61_763) -> begin
if (FStar_List.contains FStar_Syntax_Syntax.Private quals) then begin
(let _150_470 = (sigmap env)
in (FStar_Util.smap_remove _150_470 lid.FStar_Ident.str))
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_let ((_61_767, lbs), r, _61_772, quals) -> begin
(
# 493 "FStar.Parser.Env.fst"
let _61_777 = if ((FStar_List.contains FStar_Syntax_Syntax.Private quals) || (FStar_List.contains FStar_Syntax_Syntax.Abstract quals)) then begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (let _150_476 = (sigmap env)
in (let _150_475 = (let _150_474 = (let _150_473 = (let _150_472 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _150_472.FStar_Syntax_Syntax.fv_name)
in _150_473.FStar_Syntax_Syntax.v)
in _150_474.FStar_Ident.str)
in (FStar_Util.smap_remove _150_476 _150_475))))))
end else begin
()
end
in if ((FStar_List.contains FStar_Syntax_Syntax.Abstract quals) && (not ((FStar_List.contains FStar_Syntax_Syntax.Private quals)))) then begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (
# 501 "FStar.Parser.Env.fst"
let lid = (let _150_479 = (let _150_478 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _150_478.FStar_Syntax_Syntax.fv_name)
in _150_479.FStar_Syntax_Syntax.v)
in (
# 502 "FStar.Parser.Env.fst"
let decl = FStar_Syntax_Syntax.Sig_declare_typ ((lid, lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp, (FStar_Syntax_Syntax.Assumption)::quals, r))
in (let _150_480 = (sigmap env)
in (FStar_Util.smap_add _150_480 lid.FStar_Ident.str (decl, false))))))))
end else begin
()
end)
end
| _61_783 -> begin
()
end))))
in (
# 506 "FStar.Parser.Env.fst"
let _61_786 = env
in {curmodule = None; modules = ((modul.FStar_Syntax_Syntax.name, modul))::env.modules; open_namespaces = []; modul_abbrevs = _61_786.modul_abbrevs; sigaccum = []; localbindings = []; recbindings = []; sigmap = _61_786.sigmap; default_result_effect = _61_786.default_result_effect; iface = _61_786.iface; admitted_iface = _61_786.admitted_iface; expect_typ = _61_786.expect_typ})))

# 514 "FStar.Parser.Env.fst"
let push : env  ->  env = (fun env -> (
# 515 "FStar.Parser.Env.fst"
let _61_789 = (push_record_cache ())
in (
# 516 "FStar.Parser.Env.fst"
let _61_791 = env
in (let _150_485 = (let _150_484 = (let _150_483 = (sigmap env)
in (FStar_Util.smap_copy _150_483))
in (_150_484)::env.sigmap)
in {curmodule = _61_791.curmodule; modules = _61_791.modules; open_namespaces = _61_791.open_namespaces; modul_abbrevs = _61_791.modul_abbrevs; sigaccum = _61_791.sigaccum; localbindings = _61_791.localbindings; recbindings = _61_791.recbindings; sigmap = _150_485; default_result_effect = _61_791.default_result_effect; iface = _61_791.iface; admitted_iface = _61_791.admitted_iface; expect_typ = _61_791.expect_typ}))))

# 519 "FStar.Parser.Env.fst"
let mark : env  ->  env = (fun env -> (push env))

# 520 "FStar.Parser.Env.fst"
let reset_mark : env  ->  env = (fun env -> (
# 520 "FStar.Parser.Env.fst"
let _61_795 = env
in (let _150_490 = (FStar_List.tl env.sigmap)
in {curmodule = _61_795.curmodule; modules = _61_795.modules; open_namespaces = _61_795.open_namespaces; modul_abbrevs = _61_795.modul_abbrevs; sigaccum = _61_795.sigaccum; localbindings = _61_795.localbindings; recbindings = _61_795.recbindings; sigmap = _150_490; default_result_effect = _61_795.default_result_effect; iface = _61_795.iface; admitted_iface = _61_795.admitted_iface; expect_typ = _61_795.expect_typ})))

# 521 "FStar.Parser.Env.fst"
let commit_mark : env  ->  env = (fun env -> (match (env.sigmap) with
| hd::_61_800::tl -> begin
(
# 522 "FStar.Parser.Env.fst"
let _61_804 = env
in {curmodule = _61_804.curmodule; modules = _61_804.modules; open_namespaces = _61_804.open_namespaces; modul_abbrevs = _61_804.modul_abbrevs; sigaccum = _61_804.sigaccum; localbindings = _61_804.localbindings; recbindings = _61_804.recbindings; sigmap = (hd)::tl; default_result_effect = _61_804.default_result_effect; iface = _61_804.iface; admitted_iface = _61_804.admitted_iface; expect_typ = _61_804.expect_typ})
end
| _61_807 -> begin
(FStar_All.failwith "Impossible")
end))

# 524 "FStar.Parser.Env.fst"
let pop : env  ->  env = (fun env -> (match (env.sigmap) with
| _61_811::maps -> begin
(
# 526 "FStar.Parser.Env.fst"
let _61_813 = (pop_record_cache ())
in (
# 527 "FStar.Parser.Env.fst"
let _61_815 = env
in {curmodule = _61_815.curmodule; modules = _61_815.modules; open_namespaces = _61_815.open_namespaces; modul_abbrevs = _61_815.modul_abbrevs; sigaccum = _61_815.sigaccum; localbindings = _61_815.localbindings; recbindings = _61_815.recbindings; sigmap = maps; default_result_effect = _61_815.default_result_effect; iface = _61_815.iface; admitted_iface = _61_815.admitted_iface; expect_typ = _61_815.expect_typ}))
end
| _61_818 -> begin
(FStar_All.failwith "No more modules to pop")
end))

# 531 "FStar.Parser.Env.fst"
let export_interface : FStar_Ident.lident  ->  env  ->  env = (fun m env -> (
# 533 "FStar.Parser.Env.fst"
let sigelt_in_m = (fun se -> (match ((FStar_Syntax_Util.lids_of_sigelt se)) with
| l::_61_824 -> begin
(l.FStar_Ident.nsstr = m.FStar_Ident.str)
end
| _61_828 -> begin
false
end))
in (
# 537 "FStar.Parser.Env.fst"
let sm = (sigmap env)
in (
# 538 "FStar.Parser.Env.fst"
let env = (pop env)
in (
# 539 "FStar.Parser.Env.fst"
let keys = (FStar_Util.smap_keys sm)
in (
# 540 "FStar.Parser.Env.fst"
let sm' = (sigmap env)
in (
# 541 "FStar.Parser.Env.fst"
let _61_852 = (FStar_All.pipe_right keys (FStar_List.iter (fun k -> (match ((FStar_Util.smap_try_find sm' k)) with
| Some (se, true) when (sigelt_in_m se) -> begin
(
# 544 "FStar.Parser.Env.fst"
let _61_838 = (FStar_Util.smap_remove sm' k)
in (
# 546 "FStar.Parser.Env.fst"
let se = (match (se) with
| FStar_Syntax_Syntax.Sig_declare_typ (l, u, t, q, r) -> begin
FStar_Syntax_Syntax.Sig_declare_typ ((l, u, t, (FStar_Syntax_Syntax.Assumption)::q, r))
end
| _61_848 -> begin
se
end)
in (FStar_Util.smap_add sm' k (se, false))))
end
| _61_851 -> begin
()
end))))
in env)))))))

# 553 "FStar.Parser.Env.fst"
let finish_module_or_interface : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env modul -> (
# 554 "FStar.Parser.Env.fst"
let _61_856 = if (not (modul.FStar_Syntax_Syntax.is_interface)) then begin
(check_admits env)
end else begin
()
end
in (finish env modul)))

# 558 "FStar.Parser.Env.fst"
let prepare_module_or_interface : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  (env * Prims.bool) = (fun intf admitted env mname -> (
# 559 "FStar.Parser.Env.fst"
let prep = (fun env -> (
# 560 "FStar.Parser.Env.fst"
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
# 564 "FStar.Parser.Env.fst"
let _61_865 = env
in {curmodule = Some (mname); modules = _61_865.modules; open_namespaces = open_ns; modul_abbrevs = _61_865.modul_abbrevs; sigaccum = _61_865.sigaccum; localbindings = _61_865.localbindings; recbindings = _61_865.recbindings; sigmap = env.sigmap; default_result_effect = _61_865.default_result_effect; iface = intf; admitted_iface = admitted; expect_typ = _61_865.expect_typ})))
in (match ((FStar_All.pipe_right env.modules (FStar_Util.find_opt (fun _61_870 -> (match (_61_870) with
| (l, _61_869) -> begin
(FStar_Ident.lid_equals l mname)
end))))) with
| None -> begin
((prep env), false)
end
| Some (_61_873, m) -> begin
(
# 569 "FStar.Parser.Env.fst"
let _61_877 = if ((not (m.FStar_Syntax_Syntax.is_interface)) || intf) then begin
(let _150_519 = (let _150_518 = (let _150_517 = (FStar_Util.format1 "Duplicate module or interface name: %s" mname.FStar_Ident.str)
in (_150_517, (FStar_Ident.range_of_lid mname)))
in FStar_Syntax_Syntax.Error (_150_518))
in (Prims.raise _150_519))
end else begin
()
end
in (let _150_521 = (let _150_520 = (push env)
in (prep _150_520))
in (_150_521, true)))
end)))

# 574 "FStar.Parser.Env.fst"
let enter_monad_scope : env  ->  FStar_Ident.ident  ->  env = (fun env mname -> (
# 575 "FStar.Parser.Env.fst"
let curmod = (current_module env)
in (
# 576 "FStar.Parser.Env.fst"
let mscope = (FStar_Ident.lid_of_ids (FStar_List.append curmod.FStar_Ident.ns ((curmod.FStar_Ident.ident)::(mname)::[])))
in (
# 577 "FStar.Parser.Env.fst"
let _61_883 = env
in {curmodule = Some (mscope); modules = _61_883.modules; open_namespaces = (curmod)::env.open_namespaces; modul_abbrevs = _61_883.modul_abbrevs; sigaccum = _61_883.sigaccum; localbindings = _61_883.localbindings; recbindings = _61_883.recbindings; sigmap = _61_883.sigmap; default_result_effect = _61_883.default_result_effect; iface = _61_883.iface; admitted_iface = _61_883.admitted_iface; expect_typ = _61_883.expect_typ}))))

# 581 "FStar.Parser.Env.fst"
let exit_monad_scope : env  ->  env  ->  env = (fun env0 env -> (
# 582 "FStar.Parser.Env.fst"
let _61_887 = env
in {curmodule = env0.curmodule; modules = _61_887.modules; open_namespaces = env0.open_namespaces; modul_abbrevs = _61_887.modul_abbrevs; sigaccum = _61_887.sigaccum; localbindings = _61_887.localbindings; recbindings = _61_887.recbindings; sigmap = _61_887.sigmap; default_result_effect = _61_887.default_result_effect; iface = _61_887.iface; admitted_iface = _61_887.admitted_iface; expect_typ = _61_887.expect_typ}))

# 586 "FStar.Parser.Env.fst"
let fail_or = (fun lookup lid -> (match ((lookup lid)) with
| None -> begin
(let _150_537 = (let _150_536 = (let _150_535 = (FStar_Util.format1 "Identifier not found: [%s]" (FStar_Ident.text_of_lid lid))
in (_150_535, (FStar_Ident.range_of_lid lid)))
in FStar_Syntax_Syntax.Error (_150_536))
in (Prims.raise _150_537))
end
| Some (r) -> begin
r
end))

# 591 "FStar.Parser.Env.fst"
let fail_or2 = (fun lookup id -> (match ((lookup id)) with
| None -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (((Prims.strcat (Prims.strcat "Identifier not found [" id.FStar_Ident.idText) "]"), id.FStar_Ident.idRange))))
end
| Some (r) -> begin
r
end))




