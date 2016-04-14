
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
| Term_name (_54_27) -> begin
_54_27
end))

# 51 "FStar.Parser.Env.fst"
let ___Eff_name____0 = (fun projectee -> (match (projectee) with
| Eff_name (_54_30) -> begin
_54_30
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
let qual : FStar_Ident.lident  ->  FStar_Ident.ident  ->  FStar_Ident.lident = (fun lid id -> (let _143_90 = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns ((lid.FStar_Ident.ident)::(id)::[])))
in (FStar_Ident.set_lid_range _143_90 id.FStar_Ident.idRange)))

# 102 "FStar.Parser.Env.fst"
let qualify : env  ->  FStar_Ident.ident  ->  FStar_Ident.lident = (fun env id -> (let _143_95 = (current_module env)
in (qual _143_95 id)))

# 103 "FStar.Parser.Env.fst"
let qualify_lid : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (
# 104 "FStar.Parser.Env.fst"
let cur = (current_module env)
in (let _143_100 = (FStar_Ident.lid_of_ids (FStar_List.append (FStar_List.append (FStar_List.append cur.FStar_Ident.ns ((cur.FStar_Ident.ident)::[])) lid.FStar_Ident.ns) ((lid.FStar_Ident.ident)::[])))
in (FStar_Ident.set_lid_range _143_100 (FStar_Ident.range_of_lid lid)))))

# 106 "FStar.Parser.Env.fst"
let new_sigmap = (fun _54_51 -> (match (()) with
| () -> begin
(FStar_Util.smap_create 100)
end))

# 107 "FStar.Parser.Env.fst"
let empty_env : Prims.unit  ->  env = (fun _54_52 -> (match (()) with
| () -> begin
(let _143_105 = (let _143_104 = (new_sigmap ())
in (_143_104)::[])
in {curmodule = None; modules = []; open_namespaces = []; modul_abbrevs = []; sigaccum = []; localbindings = []; recbindings = []; sigmap = _143_105; default_result_effect = FStar_Syntax_Const.effect_ML_lid; iface = false; admitted_iface = false; expect_typ = false})
end))

# 119 "FStar.Parser.Env.fst"
let sigmap : env  ->  (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap = (fun env -> (FStar_List.hd env.sigmap))

# 120 "FStar.Parser.Env.fst"
let default_total : env  ->  env = (fun env -> (
# 120 "FStar.Parser.Env.fst"
let _54_55 = env
in {curmodule = _54_55.curmodule; modules = _54_55.modules; open_namespaces = _54_55.open_namespaces; modul_abbrevs = _54_55.modul_abbrevs; sigaccum = _54_55.sigaccum; localbindings = _54_55.localbindings; recbindings = _54_55.recbindings; sigmap = _54_55.sigmap; default_result_effect = FStar_Syntax_Const.effect_Tot_lid; iface = _54_55.iface; admitted_iface = _54_55.admitted_iface; expect_typ = _54_55.expect_typ}))

# 121 "FStar.Parser.Env.fst"
let default_ml : env  ->  env = (fun env -> (
# 121 "FStar.Parser.Env.fst"
let _54_58 = env
in {curmodule = _54_58.curmodule; modules = _54_58.modules; open_namespaces = _54_58.open_namespaces; modul_abbrevs = _54_58.modul_abbrevs; sigaccum = _54_58.sigaccum; localbindings = _54_58.localbindings; recbindings = _54_58.recbindings; sigmap = _54_58.sigmap; default_result_effect = FStar_Syntax_Const.effect_ML_lid; iface = _54_58.iface; admitted_iface = _54_58.admitted_iface; expect_typ = _54_58.expect_typ}))

# 124 "FStar.Parser.Env.fst"
let set_bv_range : FStar_Syntax_Syntax.bv  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.bv = (fun bv r -> (
# 125 "FStar.Parser.Env.fst"
let id = (
# 125 "FStar.Parser.Env.fst"
let _54_62 = bv.FStar_Syntax_Syntax.ppname
in {FStar_Ident.idText = _54_62.FStar_Ident.idText; FStar_Ident.idRange = r})
in (
# 126 "FStar.Parser.Env.fst"
let _54_65 = bv
in {FStar_Syntax_Syntax.ppname = id; FStar_Syntax_Syntax.index = _54_65.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _54_65.FStar_Syntax_Syntax.sort})))

# 128 "FStar.Parser.Env.fst"
let bv_to_name : FStar_Syntax_Syntax.bv  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.term = (fun bv r -> (FStar_Syntax_Syntax.bv_to_name (set_bv_range bv r)))

# 130 "FStar.Parser.Env.fst"
let unmangleMap : (Prims.string * Prims.string * FStar_Syntax_Syntax.delta_depth * FStar_Syntax_Syntax.fv_qual Prims.option) Prims.list = (("op_ColonColon", "Cons", FStar_Syntax_Syntax.Delta_constant, Some (FStar_Syntax_Syntax.Data_ctor)))::(("not", "op_Negation", FStar_Syntax_Syntax.Delta_equational, None))::[]

# 133 "FStar.Parser.Env.fst"
let unmangleOpName : FStar_Ident.ident  ->  FStar_Syntax_Syntax.term Prims.option = (fun id -> (FStar_Util.find_map unmangleMap (fun _54_74 -> (match (_54_74) with
| (x, y, dd, dq) -> begin
if (id.FStar_Ident.idText = x) then begin
(let _143_124 = (let _143_123 = (FStar_Ident.lid_of_path (("Prims")::(y)::[]) id.FStar_Ident.idRange)
in (FStar_Syntax_Syntax.fvar _143_123 dd dq))
in Some (_143_124))
end else begin
None
end
end))))

# 138 "FStar.Parser.Env.fst"
let try_lookup_id : env  ->  FStar_Ident.ident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env id -> (match ((unmangleOpName id)) with
| Some (f) -> begin
Some (f)
end
| _54_80 -> begin
(FStar_Util.find_map env.localbindings (fun _54_1 -> (match (_54_1) with
| (id', x) when (id'.FStar_Ident.idText = id.FStar_Ident.idText) -> begin
(let _143_130 = (bv_to_name x id.FStar_Ident.idRange)
in Some (_143_130))
end
| _54_86 -> begin
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
| _54_96 -> begin
(
# 152 "FStar.Parser.Env.fst"
let ids = (FStar_Ident.ids_of_lid lid)
in (FStar_Util.find_map namespaces (fun ns -> (
# 154 "FStar.Parser.Env.fst"
let full_name = (FStar_Ident.lid_of_ids (FStar_List.append (FStar_Ident.ids_of_lid ns) ids))
in (finder full_name)))))
end))
in (let _143_141 = (let _143_140 = (current_module env)
in (_143_140)::env.open_namespaces)
in (aux _143_141))))

# 158 "FStar.Parser.Env.fst"
let expand_module_abbrevs : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (match (lid.FStar_Ident.ns) with
| id::[] -> begin
(match ((FStar_All.pipe_right env.modul_abbrevs (FStar_List.tryFind (fun _54_107 -> (match (_54_107) with
| (id', _54_106) -> begin
(id.FStar_Ident.idText = id'.FStar_Ident.idText)
end))))) with
| None -> begin
lid
end
| Some (_54_110, lid') -> begin
(FStar_Ident.lid_of_ids (FStar_List.append (FStar_Ident.ids_of_lid lid') ((lid.FStar_Ident.ident)::[])))
end)
end
| _54_115 -> begin
lid
end))

# 168 "FStar.Parser.Env.fst"
let resolve_in_open_namespaces = (fun env lid finder -> (let _143_153 = (expand_module_abbrevs env lid)
in (resolve_in_open_namespaces' env _143_153 finder)))

# 171 "FStar.Parser.Env.fst"
let fv_qual_of_se : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.fv_qual Prims.option = (fun _54_3 -> (match (_54_3) with
| FStar_Syntax_Syntax.Sig_datacon (_54_122, _54_124, _54_126, l, _54_129, quals, _54_132, _54_134) -> begin
(
# 173 "FStar.Parser.Env.fst"
let qopt = (FStar_Util.find_map quals (fun _54_2 -> (match (_54_2) with
| FStar_Syntax_Syntax.RecordConstructor (fs) -> begin
Some (FStar_Syntax_Syntax.Record_ctor ((l, fs)))
end
| _54_141 -> begin
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
| FStar_Syntax_Syntax.Sig_declare_typ (_54_146, _54_148, _54_150, quals, _54_153) -> begin
None
end
| _54_157 -> begin
None
end))

# 184 "FStar.Parser.Env.fst"
let lb_fv : FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.fv = (fun lbs lid -> (let _143_162 = (FStar_Util.find_map lbs (fun lb -> (
# 186 "FStar.Parser.Env.fst"
let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in if (FStar_Syntax_Syntax.fv_eq_lid fv lid) then begin
Some (fv)
end else begin
None
end)))
in (FStar_All.pipe_right _143_162 FStar_Util.must)))

# 189 "FStar.Parser.Env.fst"
let try_lookup_name : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  foundname Prims.option = (fun any_val exclude_interf env lid -> (
# 195 "FStar.Parser.Env.fst"
let find_in_sig = (fun lid -> (match ((let _143_173 = (sigmap env)
in (FStar_Util.smap_try_find _143_173 lid.FStar_Ident.str))) with
| Some (_54_169, true) when exclude_interf -> begin
None
end
| None -> begin
None
end
| Some (se, _54_176) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_54_180) -> begin
(let _143_175 = (let _143_174 = (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.Delta_constant None)
in Term_name (_143_174))
in Some (_143_175))
end
| FStar_Syntax_Syntax.Sig_datacon (_54_183) -> begin
(let _143_178 = (let _143_177 = (let _143_176 = (fv_qual_of_se se)
in (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.Delta_constant _143_176))
in Term_name (_143_177))
in Some (_143_178))
end
| FStar_Syntax_Syntax.Sig_let ((_54_186, lbs), _54_190, _54_192, _54_194) -> begin
(
# 204 "FStar.Parser.Env.fst"
let fv = (lb_fv lbs lid)
in (let _143_180 = (let _143_179 = (FStar_Syntax_Syntax.fvar lid fv.FStar_Syntax_Syntax.fv_delta fv.FStar_Syntax_Syntax.fv_qual)
in Term_name (_143_179))
in Some (_143_180)))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _54_200, _54_202, quals, _54_205) -> begin
if (any_val || (FStar_All.pipe_right quals (FStar_Util.for_some (fun _54_4 -> (match (_54_4) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| _54_211 -> begin
false
end))))) then begin
(
# 209 "FStar.Parser.Env.fst"
let dd = if (FStar_Syntax_Util.is_primop_lid lid) then begin
FStar_Syntax_Syntax.Delta_equational
end else begin
FStar_Syntax_Syntax.Delta_constant
end
in (let _143_184 = (let _143_183 = (let _143_182 = (fv_qual_of_se se)
in (FStar_Syntax_Syntax.fvar lid dd _143_182))
in Term_name (_143_183))
in Some (_143_184)))
end else begin
None
end
end
| FStar_Syntax_Syntax.Sig_new_effect (ne, _54_215) -> begin
(let _143_187 = (let _143_186 = (let _143_185 = (FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname (FStar_Ident.range_of_lid lid))
in (se, _143_185))
in Eff_name (_143_186))
in Some (_143_187))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (_54_219) -> begin
Some (Eff_name ((se, lid)))
end
| _54_222 -> begin
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
in (FStar_Util.find_map env.recbindings (fun _54_231 -> (match (_54_231) with
| (id, l, dd) -> begin
if (id.FStar_Ident.idText = lid.FStar_Ident.ident.FStar_Ident.idText) then begin
(let _143_191 = (let _143_190 = (let _143_189 = (FStar_Ident.set_lid_range l (FStar_Ident.range_of_lid lid))
in (FStar_Syntax_Syntax.fvar _143_189 dd None))
in Term_name (_143_190))
in Some (_143_191))
end else begin
None
end
end))))
end)
end
| _54_233 -> begin
None
end)
in (match (found_id) with
| Some (_54_236) -> begin
found_id
end
| _54_239 -> begin
(resolve_in_open_namespaces env lid find_in_sig)
end))))

# 235 "FStar.Parser.Env.fst"
let try_lookup_effect_name' : Prims.bool  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident) Prims.option = (fun exclude_interf env lid -> (match ((try_lookup_name true exclude_interf env lid)) with
| Some (Eff_name (o, l)) -> begin
Some ((o, l))
end
| _54_249 -> begin
None
end))

# 239 "FStar.Parser.Env.fst"
let try_lookup_effect_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env l -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some (o, l) -> begin
Some (l)
end
| _54_257 -> begin
None
end))

# 243 "FStar.Parser.Env.fst"
let try_lookup_effect_defn : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl Prims.option = (fun env l -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some (FStar_Syntax_Syntax.Sig_new_effect (ne, _54_262), _54_266) -> begin
Some (ne)
end
| _54_270 -> begin
None
end))

# 247 "FStar.Parser.Env.fst"
let is_effect_name : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((try_lookup_effect_name env lid)) with
| None -> begin
false
end
| Some (_54_275) -> begin
true
end))

# 252 "FStar.Parser.Env.fst"
let lookup_letbinding_quals : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.qualifier Prims.list = (fun env lid -> (
# 253 "FStar.Parser.Env.fst"
let find_in_sig = (fun lid -> (match ((let _143_216 = (sigmap env)
in (FStar_Util.smap_try_find _143_216 lid.FStar_Ident.str))) with
| Some (FStar_Syntax_Syntax.Sig_declare_typ (lid, _54_283, _54_285, quals, _54_288), _54_292) -> begin
Some (quals)
end
| _54_296 -> begin
None
end))
in (match ((resolve_in_open_namespaces env lid find_in_sig)) with
| Some (quals) -> begin
quals
end
| _54_300 -> begin
[]
end)))

# 261 "FStar.Parser.Env.fst"
let try_lookup_module : env  ->  Prims.string Prims.list  ->  FStar_Syntax_Syntax.modul Prims.option = (fun env path -> (match ((FStar_List.tryFind (fun _54_305 -> (match (_54_305) with
| (mlid, modul) -> begin
((FStar_Ident.path_of_lid mlid) = path)
end)) env.modules)) with
| Some (_54_307, modul) -> begin
Some (modul)
end
| None -> begin
None
end))

# 266 "FStar.Parser.Env.fst"
let try_lookup_let : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env lid -> (
# 267 "FStar.Parser.Env.fst"
let find_in_sig = (fun lid -> (match ((let _143_228 = (sigmap env)
in (FStar_Util.smap_try_find _143_228 lid.FStar_Ident.str))) with
| Some (FStar_Syntax_Syntax.Sig_let ((_54_317, lbs), _54_321, _54_323, _54_325), _54_329) -> begin
(
# 270 "FStar.Parser.Env.fst"
let fv = (lb_fv lbs lid)
in (let _143_229 = (FStar_Syntax_Syntax.fvar lid fv.FStar_Syntax_Syntax.fv_delta fv.FStar_Syntax_Syntax.fv_qual)
in Some (_143_229)))
end
| _54_334 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))

# 275 "FStar.Parser.Env.fst"
let try_lookup_definition : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env lid -> (
# 276 "FStar.Parser.Env.fst"
let find_in_sig = (fun lid -> (match ((let _143_236 = (sigmap env)
in (FStar_Util.smap_try_find _143_236 lid.FStar_Ident.str))) with
| Some (FStar_Syntax_Syntax.Sig_let (lbs, _54_341, _54_343, _54_345), _54_349) -> begin
(FStar_Util.find_map (Prims.snd lbs) (fun lb -> (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv lid) -> begin
Some (lb.FStar_Syntax_Syntax.lbdef)
end
| _54_356 -> begin
None
end)))
end
| _54_358 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))

# 288 "FStar.Parser.Env.fst"
let try_lookup_lid' : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun any_val exclude_interf env lid -> (match ((try_lookup_name any_val exclude_interf env lid)) with
| Some (Term_name (e)) -> begin
Some (e)
end
| _54_367 -> begin
None
end))

# 292 "FStar.Parser.Env.fst"
let try_lookup_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env l -> (try_lookup_lid' env.iface false env l))

# 294 "FStar.Parser.Env.fst"
let try_lookup_datacon : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.fv Prims.option = (fun env lid -> (
# 295 "FStar.Parser.Env.fst"
let find_in_sig = (fun lid -> (match ((let _143_256 = (sigmap env)
in (FStar_Util.smap_try_find _143_256 lid.FStar_Ident.str))) with
| Some (FStar_Syntax_Syntax.Sig_declare_typ (_54_375, _54_377, _54_379, quals, _54_382), _54_386) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _54_5 -> (match (_54_5) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| _54_392 -> begin
false
end)))) then begin
(let _143_258 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant None)
in Some (_143_258))
end else begin
None
end
end
| Some (FStar_Syntax_Syntax.Sig_datacon (_54_394), _54_397) -> begin
(let _143_259 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in Some (_143_259))
end
| _54_401 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))

# 305 "FStar.Parser.Env.fst"
let find_all_datacons : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.list Prims.option = (fun env lid -> (
# 306 "FStar.Parser.Env.fst"
let find_in_sig = (fun lid -> (match ((let _143_266 = (sigmap env)
in (FStar_Util.smap_try_find _143_266 lid.FStar_Ident.str))) with
| Some (FStar_Syntax_Syntax.Sig_inductive_typ (_54_407, _54_409, _54_411, _54_413, _54_415, datas, _54_418, _54_420), _54_424) -> begin
Some (datas)
end
| _54_428 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))

# 313 "FStar.Parser.Env.fst"
let record_cache_aux : ((Prims.unit  ->  Prims.unit) * (Prims.unit  ->  Prims.unit) * (Prims.unit  ->  record_or_dc Prims.list) * (record_or_dc  ->  Prims.unit)) = (
# 314 "FStar.Parser.Env.fst"
let record_cache = (FStar_Util.mk_ref (([])::[]))
in (
# 315 "FStar.Parser.Env.fst"
let push = (fun _54_431 -> (match (()) with
| () -> begin
(let _143_280 = (let _143_279 = (let _143_277 = (FStar_ST.read record_cache)
in (FStar_List.hd _143_277))
in (let _143_278 = (FStar_ST.read record_cache)
in (_143_279)::_143_278))
in (FStar_ST.op_Colon_Equals record_cache _143_280))
end))
in (
# 317 "FStar.Parser.Env.fst"
let pop = (fun _54_433 -> (match (()) with
| () -> begin
(let _143_284 = (let _143_283 = (FStar_ST.read record_cache)
in (FStar_List.tl _143_283))
in (FStar_ST.op_Colon_Equals record_cache _143_284))
end))
in (
# 319 "FStar.Parser.Env.fst"
let peek = (fun _54_435 -> (match (()) with
| () -> begin
(let _143_287 = (FStar_ST.read record_cache)
in (FStar_List.hd _143_287))
end))
in (
# 320 "FStar.Parser.Env.fst"
let insert = (fun r -> (let _143_294 = (let _143_293 = (let _143_290 = (peek ())
in (r)::_143_290)
in (let _143_292 = (let _143_291 = (FStar_ST.read record_cache)
in (FStar_List.tl _143_291))
in (_143_293)::_143_292))
in (FStar_ST.op_Colon_Equals record_cache _143_294)))
in (push, pop, peek, insert))))))

# 323 "FStar.Parser.Env.fst"
let push_record_cache : Prims.unit  ->  Prims.unit = (
# 324 "FStar.Parser.Env.fst"
let _54_445 = record_cache_aux
in (match (_54_445) with
| (push, _54_440, _54_442, _54_444) -> begin
push
end))

# 327 "FStar.Parser.Env.fst"
let pop_record_cache : Prims.unit  ->  Prims.unit = (
# 328 "FStar.Parser.Env.fst"
let _54_453 = record_cache_aux
in (match (_54_453) with
| (_54_447, pop, _54_450, _54_452) -> begin
pop
end))

# 331 "FStar.Parser.Env.fst"
let peek_record_cache : Prims.unit  ->  record_or_dc Prims.list = (
# 332 "FStar.Parser.Env.fst"
let _54_461 = record_cache_aux
in (match (_54_461) with
| (_54_455, _54_457, peek, _54_460) -> begin
peek
end))

# 335 "FStar.Parser.Env.fst"
let insert_record_cache : record_or_dc  ->  Prims.unit = (
# 336 "FStar.Parser.Env.fst"
let _54_469 = record_cache_aux
in (match (_54_469) with
| (_54_463, _54_465, _54_467, insert) -> begin
insert
end))

# 339 "FStar.Parser.Env.fst"
let extract_record : env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun e _54_9 -> (match (_54_9) with
| FStar_Syntax_Syntax.Sig_bundle (sigs, _54_474, _54_476, _54_478) -> begin
(
# 341 "FStar.Parser.Env.fst"
let is_rec = (FStar_Util.for_some (fun _54_6 -> (match (_54_6) with
| (FStar_Syntax_Syntax.RecordType (_)) | (FStar_Syntax_Syntax.RecordConstructor (_)) -> begin
true
end
| _54_489 -> begin
false
end)))
in (
# 346 "FStar.Parser.Env.fst"
let find_dc = (fun dc -> (FStar_All.pipe_right sigs (FStar_Util.find_opt (fun _54_7 -> (match (_54_7) with
| FStar_Syntax_Syntax.Sig_datacon (lid, _54_496, _54_498, _54_500, _54_502, _54_504, _54_506, _54_508) -> begin
(FStar_Ident.lid_equals dc lid)
end
| _54_512 -> begin
false
end)))))
in (FStar_All.pipe_right sigs (FStar_List.iter (fun _54_8 -> (match (_54_8) with
| FStar_Syntax_Syntax.Sig_inductive_typ (typename, univs, parms, _54_518, _54_520, dc::[], tags, _54_525) -> begin
(match ((let _143_365 = (find_dc dc)
in (FStar_All.pipe_left FStar_Util.must _143_365))) with
| FStar_Syntax_Syntax.Sig_datacon (constrname, _54_530, t, _54_533, _54_535, _54_537, _54_539, _54_541) -> begin
(
# 355 "FStar.Parser.Env.fst"
let _54_547 = (FStar_Syntax_Util.arrow_formals t)
in (match (_54_547) with
| (formals, _54_546) -> begin
(
# 356 "FStar.Parser.Env.fst"
let is_rec = (is_rec tags)
in (
# 357 "FStar.Parser.Env.fst"
let fields = (FStar_All.pipe_right formals (FStar_List.collect (fun _54_551 -> (match (_54_551) with
| (x, q) -> begin
if ((FStar_Syntax_Syntax.is_null_bv x) || (is_rec && (FStar_Syntax_Syntax.is_implicit q))) then begin
[]
end else begin
(let _143_369 = (let _143_368 = (let _143_367 = if is_rec then begin
(FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname)
end else begin
x.FStar_Syntax_Syntax.ppname
end
in (qual constrname _143_367))
in (_143_368, x.FStar_Syntax_Syntax.sort))
in (_143_369)::[])
end
end))))
in (
# 362 "FStar.Parser.Env.fst"
let record = {typename = typename; constrname = constrname; parms = parms; fields = fields; is_record = is_rec}
in (insert_record_cache record))))
end))
end
| _54_555 -> begin
()
end)
end
| _54_557 -> begin
()
end))))))
end
| _54_559 -> begin
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
(let _143_380 = (aux tl)
in (hd)::_143_380)
end))
in (aux ns)))
in (
# 381 "FStar.Parser.Env.fst"
let find_in_cache = (fun fieldname -> (
# 383 "FStar.Parser.Env.fst"
let _54_577 = (fieldname.FStar_Ident.ns, fieldname.FStar_Ident.ident)
in (match (_54_577) with
| (ns, fieldname) -> begin
(let _143_385 = (peek_record_cache ())
in (FStar_Util.find_map _143_385 (fun record -> (
# 385 "FStar.Parser.Env.fst"
let constrname = record.constrname.FStar_Ident.ident
in (
# 386 "FStar.Parser.Env.fst"
let ns = (maybe_add_constrname ns constrname)
in (
# 387 "FStar.Parser.Env.fst"
let fname = (FStar_Ident.lid_of_ids (FStar_List.append ns ((fieldname)::[])))
in (FStar_Util.find_map record.fields (fun _54_585 -> (match (_54_585) with
| (f, _54_584) -> begin
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
| _54_593 -> begin
None
end))

# 399 "FStar.Parser.Env.fst"
let try_lookup_projector_by_field_name : env  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * Prims.bool) Prims.option = (fun env fieldname -> (match ((try_lookup_record_or_dc_by_field_name env fieldname)) with
| Some (r, f) -> begin
Some ((f, r.is_record))
end
| _54_601 -> begin
None
end))

# 404 "FStar.Parser.Env.fst"
let qualify_field_to_record : env  ->  record_or_dc  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env recd f -> (
# 405 "FStar.Parser.Env.fst"
let qualify = (fun fieldname -> (
# 406 "FStar.Parser.Env.fst"
let _54_609 = (fieldname.FStar_Ident.ns, fieldname.FStar_Ident.ident)
in (match (_54_609) with
| (ns, fieldname) -> begin
(
# 407 "FStar.Parser.Env.fst"
let constrname = recd.constrname.FStar_Ident.ident
in (
# 408 "FStar.Parser.Env.fst"
let fname = (FStar_Ident.lid_of_ids (FStar_List.append (FStar_List.append ns ((constrname)::[])) ((fieldname)::[])))
in (FStar_Util.find_map recd.fields (fun _54_615 -> (match (_54_615) with
| (f, _54_614) -> begin
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
let _54_620 = env
in {curmodule = _54_620.curmodule; modules = _54_620.modules; open_namespaces = []; modul_abbrevs = _54_620.modul_abbrevs; sigaccum = _54_620.sigaccum; localbindings = _54_620.localbindings; recbindings = _54_620.recbindings; sigmap = _54_620.sigmap; default_result_effect = _54_620.default_result_effect; iface = _54_620.iface; admitted_iface = _54_620.admitted_iface; expect_typ = _54_620.expect_typ})
in (match ((try_lookup_lid' any_val exclude_if env lid)) with
| None -> begin
true
end
| Some (_54_625) -> begin
false
end)))

# 421 "FStar.Parser.Env.fst"
let push_bv : env  ->  FStar_Ident.ident  ->  (env * FStar_Syntax_Syntax.bv) = (fun env x -> (
# 422 "FStar.Parser.Env.fst"
let bv = (FStar_Syntax_Syntax.gen_bv x.FStar_Ident.idText (Some (x.FStar_Ident.idRange)) FStar_Syntax_Syntax.tun)
in ((
# 423 "FStar.Parser.Env.fst"
let _54_630 = env
in {curmodule = _54_630.curmodule; modules = _54_630.modules; open_namespaces = _54_630.open_namespaces; modul_abbrevs = _54_630.modul_abbrevs; sigaccum = _54_630.sigaccum; localbindings = ((x, bv))::env.localbindings; recbindings = _54_630.recbindings; sigmap = _54_630.sigmap; default_result_effect = _54_630.default_result_effect; iface = _54_630.iface; admitted_iface = _54_630.admitted_iface; expect_typ = _54_630.expect_typ}), bv)))

# 425 "FStar.Parser.Env.fst"
let push_top_level_rec_binding : env  ->  FStar_Ident.ident  ->  FStar_Syntax_Syntax.delta_depth  ->  env = (fun env x dd -> (
# 426 "FStar.Parser.Env.fst"
let l = (qualify env x)
in if (unique false true env l) then begin
(
# 428 "FStar.Parser.Env.fst"
let _54_636 = env
in {curmodule = _54_636.curmodule; modules = _54_636.modules; open_namespaces = _54_636.open_namespaces; modul_abbrevs = _54_636.modul_abbrevs; sigaccum = _54_636.sigaccum; localbindings = _54_636.localbindings; recbindings = ((x, l, dd))::env.recbindings; sigmap = _54_636.sigmap; default_result_effect = _54_636.default_result_effect; iface = _54_636.iface; admitted_iface = _54_636.admitted_iface; expect_typ = _54_636.expect_typ})
end else begin
(Prims.raise (FStar_Syntax_Syntax.Error (((Prims.strcat "Duplicate top-level names " l.FStar_Ident.str), (FStar_Ident.range_of_lid l)))))
end))

# 431 "FStar.Parser.Env.fst"
let push_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env s -> (
# 432 "FStar.Parser.Env.fst"
let err = (fun l -> (
# 433 "FStar.Parser.Env.fst"
let sopt = (let _143_427 = (sigmap env)
in (FStar_Util.smap_try_find _143_427 l.FStar_Ident.str))
in (
# 434 "FStar.Parser.Env.fst"
let r = (match (sopt) with
| Some (se, _54_645) -> begin
(match ((let _143_428 = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_Util.find_opt (FStar_Ident.lid_equals l) _143_428))) with
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
in (let _143_431 = (let _143_430 = (let _143_429 = (FStar_Util.format2 "Duplicate top-level names [%s]; previously declared at %s" (FStar_Ident.text_of_lid l) r)
in (_143_429, (FStar_Ident.range_of_lid l)))
in FStar_Syntax_Syntax.Error (_143_430))
in (Prims.raise _143_431)))))
in (
# 442 "FStar.Parser.Env.fst"
let env = (
# 443 "FStar.Parser.Env.fst"
let _54_663 = (match (s) with
| FStar_Syntax_Syntax.Sig_let (_54_654) -> begin
(false, true)
end
| FStar_Syntax_Syntax.Sig_bundle (_54_657) -> begin
(true, true)
end
| _54_660 -> begin
(false, false)
end)
in (match (_54_663) with
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
let _54_667 = (extract_record env s)
in (
# 449 "FStar.Parser.Env.fst"
let _54_669 = env
in {curmodule = _54_669.curmodule; modules = _54_669.modules; open_namespaces = _54_669.open_namespaces; modul_abbrevs = _54_669.modul_abbrevs; sigaccum = (s)::env.sigaccum; localbindings = _54_669.localbindings; recbindings = _54_669.recbindings; sigmap = _54_669.sigmap; default_result_effect = _54_669.default_result_effect; iface = _54_669.iface; admitted_iface = _54_669.admitted_iface; expect_typ = _54_669.expect_typ}))
end
| Some (l) -> begin
(err l)
end))
end))
in (
# 452 "FStar.Parser.Env.fst"
let _54_688 = (match (s) with
| FStar_Syntax_Syntax.Sig_bundle (ses, _54_676, _54_678, _54_680) -> begin
(let _143_435 = (FStar_List.map (fun se -> (let _143_434 = (FStar_Syntax_Util.lids_of_sigelt se)
in (_143_434, se))) ses)
in (env, _143_435))
end
| _54_685 -> begin
(let _143_438 = (let _143_437 = (let _143_436 = (FStar_Syntax_Util.lids_of_sigelt s)
in (_143_436, s))
in (_143_437)::[])
in (env, _143_438))
end)
in (match (_54_688) with
| (env, lss) -> begin
(
# 455 "FStar.Parser.Env.fst"
let _54_693 = (FStar_All.pipe_right lss (FStar_List.iter (fun _54_691 -> (match (_54_691) with
| (lids, se) -> begin
(FStar_All.pipe_right lids (FStar_List.iter (fun lid -> (let _143_441 = (sigmap env)
in (FStar_Util.smap_add _143_441 lid.FStar_Ident.str (se, (env.iface && (not (env.admitted_iface)))))))))
end))))
in env)
end)))))

# 460 "FStar.Parser.Env.fst"
let push_namespace : env  ->  FStar_Ident.lident  ->  env = (fun env lid -> (
# 461 "FStar.Parser.Env.fst"
let _54_697 = env
in {curmodule = _54_697.curmodule; modules = _54_697.modules; open_namespaces = (lid)::env.open_namespaces; modul_abbrevs = _54_697.modul_abbrevs; sigaccum = _54_697.sigaccum; localbindings = _54_697.localbindings; recbindings = _54_697.recbindings; sigmap = _54_697.sigmap; default_result_effect = _54_697.default_result_effect; iface = _54_697.iface; admitted_iface = _54_697.admitted_iface; expect_typ = _54_697.expect_typ}))

# 463 "FStar.Parser.Env.fst"
let push_module_abbrev : env  ->  FStar_Ident.ident  ->  FStar_Ident.lident  ->  env = (fun env x l -> if (FStar_All.pipe_right env.modul_abbrevs (FStar_Util.for_some (fun _54_705 -> (match (_54_705) with
| (y, _54_704) -> begin
(x.FStar_Ident.idText = y.FStar_Ident.idText)
end)))) then begin
(let _143_455 = (let _143_454 = (let _143_453 = (FStar_Util.format1 "Module %s is already defined" x.FStar_Ident.idText)
in (_143_453, x.FStar_Ident.idRange))
in FStar_Syntax_Syntax.Error (_143_454))
in (Prims.raise _143_455))
end else begin
(
# 466 "FStar.Parser.Env.fst"
let _54_706 = env
in {curmodule = _54_706.curmodule; modules = _54_706.modules; open_namespaces = _54_706.open_namespaces; modul_abbrevs = ((x, l))::env.modul_abbrevs; sigaccum = _54_706.sigaccum; localbindings = _54_706.localbindings; recbindings = _54_706.recbindings; sigmap = _54_706.sigmap; default_result_effect = _54_706.default_result_effect; iface = _54_706.iface; admitted_iface = _54_706.admitted_iface; expect_typ = _54_706.expect_typ})
end)

# 468 "FStar.Parser.Env.fst"
let check_admits : env  ->  Prims.unit = (fun env -> (FStar_All.pipe_right env.sigaccum (FStar_List.iter (fun se -> (match (se) with
| FStar_Syntax_Syntax.Sig_declare_typ (l, u, t, quals, r) -> begin
(match ((try_lookup_lid env l)) with
| None -> begin
(
# 473 "FStar.Parser.Env.fst"
let _54_718 = (let _143_461 = (let _143_460 = (FStar_Range.string_of_range (FStar_Ident.range_of_lid l))
in (let _143_459 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format2 "%s: Warning: Admitting %s without a definition\n" _143_460 _143_459)))
in (FStar_Util.print_string _143_461))
in (let _143_462 = (sigmap env)
in (FStar_Util.smap_add _143_462 l.FStar_Ident.str (FStar_Syntax_Syntax.Sig_declare_typ ((l, u, t, (FStar_Syntax_Syntax.Assumption)::quals, r)), false))))
end
| Some (_54_721) -> begin
()
end)
end
| _54_724 -> begin
()
end)))))

# 479 "FStar.Parser.Env.fst"
let finish : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env modul -> (
# 480 "FStar.Parser.Env.fst"
let _54_784 = (FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations (FStar_List.iter (fun _54_11 -> (match (_54_11) with
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _54_731, _54_733) -> begin
if ((FStar_List.contains FStar_Syntax_Syntax.Private quals) || (FStar_List.contains FStar_Syntax_Syntax.Abstract quals)) then begin
(FStar_All.pipe_right ses (FStar_List.iter (fun _54_10 -> (match (_54_10) with
| FStar_Syntax_Syntax.Sig_datacon (lid, _54_739, _54_741, _54_743, _54_745, _54_747, _54_749, _54_751) -> begin
(let _143_469 = (sigmap env)
in (FStar_Util.smap_remove _143_469 lid.FStar_Ident.str))
end
| _54_755 -> begin
()
end))))
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _54_758, _54_760, quals, _54_763) -> begin
if (FStar_List.contains FStar_Syntax_Syntax.Private quals) then begin
(let _143_470 = (sigmap env)
in (FStar_Util.smap_remove _143_470 lid.FStar_Ident.str))
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_let ((_54_767, lbs), r, _54_772, quals) -> begin
(
# 493 "FStar.Parser.Env.fst"
let _54_777 = if ((FStar_List.contains FStar_Syntax_Syntax.Private quals) || (FStar_List.contains FStar_Syntax_Syntax.Abstract quals)) then begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (let _143_476 = (sigmap env)
in (let _143_475 = (let _143_474 = (let _143_473 = (let _143_472 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _143_472.FStar_Syntax_Syntax.fv_name)
in _143_473.FStar_Syntax_Syntax.v)
in _143_474.FStar_Ident.str)
in (FStar_Util.smap_remove _143_476 _143_475))))))
end else begin
()
end
in if ((FStar_List.contains FStar_Syntax_Syntax.Abstract quals) && (not ((FStar_List.contains FStar_Syntax_Syntax.Private quals)))) then begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (
# 501 "FStar.Parser.Env.fst"
let lid = (let _143_479 = (let _143_478 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _143_478.FStar_Syntax_Syntax.fv_name)
in _143_479.FStar_Syntax_Syntax.v)
in (
# 502 "FStar.Parser.Env.fst"
let decl = FStar_Syntax_Syntax.Sig_declare_typ ((lid, lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp, (FStar_Syntax_Syntax.Assumption)::quals, r))
in (let _143_480 = (sigmap env)
in (FStar_Util.smap_add _143_480 lid.FStar_Ident.str (decl, false))))))))
end else begin
()
end)
end
| _54_783 -> begin
()
end))))
in (
# 506 "FStar.Parser.Env.fst"
let _54_786 = env
in {curmodule = None; modules = ((modul.FStar_Syntax_Syntax.name, modul))::env.modules; open_namespaces = []; modul_abbrevs = _54_786.modul_abbrevs; sigaccum = []; localbindings = []; recbindings = []; sigmap = _54_786.sigmap; default_result_effect = _54_786.default_result_effect; iface = _54_786.iface; admitted_iface = _54_786.admitted_iface; expect_typ = _54_786.expect_typ})))

# 514 "FStar.Parser.Env.fst"
let push : env  ->  env = (fun env -> (
# 515 "FStar.Parser.Env.fst"
let _54_789 = (push_record_cache ())
in (
# 516 "FStar.Parser.Env.fst"
let _54_791 = env
in (let _143_485 = (let _143_484 = (let _143_483 = (sigmap env)
in (FStar_Util.smap_copy _143_483))
in (_143_484)::env.sigmap)
in {curmodule = _54_791.curmodule; modules = _54_791.modules; open_namespaces = _54_791.open_namespaces; modul_abbrevs = _54_791.modul_abbrevs; sigaccum = _54_791.sigaccum; localbindings = _54_791.localbindings; recbindings = _54_791.recbindings; sigmap = _143_485; default_result_effect = _54_791.default_result_effect; iface = _54_791.iface; admitted_iface = _54_791.admitted_iface; expect_typ = _54_791.expect_typ}))))

# 519 "FStar.Parser.Env.fst"
let mark : env  ->  env = (fun env -> (push env))

# 520 "FStar.Parser.Env.fst"
let reset_mark : env  ->  env = (fun env -> (
# 520 "FStar.Parser.Env.fst"
let _54_795 = env
in (let _143_490 = (FStar_List.tl env.sigmap)
in {curmodule = _54_795.curmodule; modules = _54_795.modules; open_namespaces = _54_795.open_namespaces; modul_abbrevs = _54_795.modul_abbrevs; sigaccum = _54_795.sigaccum; localbindings = _54_795.localbindings; recbindings = _54_795.recbindings; sigmap = _143_490; default_result_effect = _54_795.default_result_effect; iface = _54_795.iface; admitted_iface = _54_795.admitted_iface; expect_typ = _54_795.expect_typ})))

# 521 "FStar.Parser.Env.fst"
let commit_mark : env  ->  env = (fun env -> (match (env.sigmap) with
| hd::_54_800::tl -> begin
(
# 522 "FStar.Parser.Env.fst"
let _54_804 = env
in {curmodule = _54_804.curmodule; modules = _54_804.modules; open_namespaces = _54_804.open_namespaces; modul_abbrevs = _54_804.modul_abbrevs; sigaccum = _54_804.sigaccum; localbindings = _54_804.localbindings; recbindings = _54_804.recbindings; sigmap = (hd)::tl; default_result_effect = _54_804.default_result_effect; iface = _54_804.iface; admitted_iface = _54_804.admitted_iface; expect_typ = _54_804.expect_typ})
end
| _54_807 -> begin
(FStar_All.failwith "Impossible")
end))

# 524 "FStar.Parser.Env.fst"
let pop : env  ->  env = (fun env -> (match (env.sigmap) with
| _54_811::maps -> begin
(
# 526 "FStar.Parser.Env.fst"
let _54_813 = (pop_record_cache ())
in (
# 527 "FStar.Parser.Env.fst"
let _54_815 = env
in {curmodule = _54_815.curmodule; modules = _54_815.modules; open_namespaces = _54_815.open_namespaces; modul_abbrevs = _54_815.modul_abbrevs; sigaccum = _54_815.sigaccum; localbindings = _54_815.localbindings; recbindings = _54_815.recbindings; sigmap = maps; default_result_effect = _54_815.default_result_effect; iface = _54_815.iface; admitted_iface = _54_815.admitted_iface; expect_typ = _54_815.expect_typ}))
end
| _54_818 -> begin
(FStar_All.failwith "No more modules to pop")
end))

# 531 "FStar.Parser.Env.fst"
let export_interface : FStar_Ident.lident  ->  env  ->  env = (fun m env -> (
# 533 "FStar.Parser.Env.fst"
let sigelt_in_m = (fun se -> (match ((FStar_Syntax_Util.lids_of_sigelt se)) with
| l::_54_824 -> begin
(l.FStar_Ident.nsstr = m.FStar_Ident.str)
end
| _54_828 -> begin
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
let _54_852 = (FStar_All.pipe_right keys (FStar_List.iter (fun k -> (match ((FStar_Util.smap_try_find sm' k)) with
| Some (se, true) when (sigelt_in_m se) -> begin
(
# 544 "FStar.Parser.Env.fst"
let _54_838 = (FStar_Util.smap_remove sm' k)
in (
# 546 "FStar.Parser.Env.fst"
let se = (match (se) with
| FStar_Syntax_Syntax.Sig_declare_typ (l, u, t, q, r) -> begin
FStar_Syntax_Syntax.Sig_declare_typ ((l, u, t, (FStar_Syntax_Syntax.Assumption)::q, r))
end
| _54_848 -> begin
se
end)
in (FStar_Util.smap_add sm' k (se, false))))
end
| _54_851 -> begin
()
end))))
in env)))))))

# 553 "FStar.Parser.Env.fst"
let finish_module_or_interface : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env modul -> (
# 554 "FStar.Parser.Env.fst"
let _54_856 = if (not (modul.FStar_Syntax_Syntax.is_interface)) then begin
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
let _54_865 = env
in {curmodule = Some (mname); modules = _54_865.modules; open_namespaces = open_ns; modul_abbrevs = _54_865.modul_abbrevs; sigaccum = _54_865.sigaccum; localbindings = _54_865.localbindings; recbindings = _54_865.recbindings; sigmap = env.sigmap; default_result_effect = _54_865.default_result_effect; iface = intf; admitted_iface = admitted; expect_typ = _54_865.expect_typ})))
in (match ((FStar_All.pipe_right env.modules (FStar_Util.find_opt (fun _54_870 -> (match (_54_870) with
| (l, _54_869) -> begin
(FStar_Ident.lid_equals l mname)
end))))) with
| None -> begin
((prep env), false)
end
| Some (_54_873, m) -> begin
(
# 569 "FStar.Parser.Env.fst"
let _54_877 = if ((not (m.FStar_Syntax_Syntax.is_interface)) || intf) then begin
(let _143_519 = (let _143_518 = (let _143_517 = (FStar_Util.format1 "Duplicate module or interface name: %s" mname.FStar_Ident.str)
in (_143_517, (FStar_Ident.range_of_lid mname)))
in FStar_Syntax_Syntax.Error (_143_518))
in (Prims.raise _143_519))
end else begin
()
end
in (let _143_521 = (let _143_520 = (push env)
in (prep _143_520))
in (_143_521, true)))
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
let _54_883 = env
in {curmodule = Some (mscope); modules = _54_883.modules; open_namespaces = (curmod)::env.open_namespaces; modul_abbrevs = _54_883.modul_abbrevs; sigaccum = _54_883.sigaccum; localbindings = _54_883.localbindings; recbindings = _54_883.recbindings; sigmap = _54_883.sigmap; default_result_effect = _54_883.default_result_effect; iface = _54_883.iface; admitted_iface = _54_883.admitted_iface; expect_typ = _54_883.expect_typ}))))

# 581 "FStar.Parser.Env.fst"
let exit_monad_scope : env  ->  env  ->  env = (fun env0 env -> (
# 582 "FStar.Parser.Env.fst"
let _54_887 = env
in {curmodule = env0.curmodule; modules = _54_887.modules; open_namespaces = env0.open_namespaces; modul_abbrevs = _54_887.modul_abbrevs; sigaccum = _54_887.sigaccum; localbindings = _54_887.localbindings; recbindings = _54_887.recbindings; sigmap = _54_887.sigmap; default_result_effect = _54_887.default_result_effect; iface = _54_887.iface; admitted_iface = _54_887.admitted_iface; expect_typ = _54_887.expect_typ}))

# 586 "FStar.Parser.Env.fst"
let fail_or = (fun lookup lid -> (match ((lookup lid)) with
| None -> begin
(let _143_537 = (let _143_536 = (let _143_535 = (FStar_Util.format1 "Identifier not found: [%s]" (FStar_Ident.text_of_lid lid))
in (_143_535, (FStar_Ident.range_of_lid lid)))
in FStar_Syntax_Syntax.Error (_143_536))
in (Prims.raise _143_537))
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




