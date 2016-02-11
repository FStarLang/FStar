
open Prims
# 34 "FStar.Parser.Env.fst"
type env =
{curmodule : FStar_Ident.lident Prims.option; modules : (FStar_Ident.lident * FStar_Syntax_Syntax.modul) Prims.list; open_namespaces : FStar_Ident.lident Prims.list; sigaccum : FStar_Syntax_Syntax.sigelts; localbindings : (FStar_Ident.ident * FStar_Syntax_Syntax.bv) Prims.list; recbindings : (FStar_Ident.ident * FStar_Ident.lident) Prims.list; sigmap : (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap Prims.list; default_result_effect : FStar_Ident.lident; iface : Prims.bool; admitted_iface : Prims.bool; expect_typ : Prims.bool}

# 34 "FStar.Parser.Env.fst"
let is_Mkenv : env  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv"))))

# 48 "FStar.Parser.Env.fst"
type foundname =
| Term_name of FStar_Syntax_Syntax.typ
| Eff_name of (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident)

# 49 "FStar.Parser.Env.fst"
let is_Term_name = (fun _discr_ -> (match (_discr_) with
| Term_name (_) -> begin
true
end
| _ -> begin
false
end))

# 50 "FStar.Parser.Env.fst"
let is_Eff_name = (fun _discr_ -> (match (_discr_) with
| Eff_name (_) -> begin
true
end
| _ -> begin
false
end))

# 49 "FStar.Parser.Env.fst"
let ___Term_name____0 : foundname  ->  FStar_Syntax_Syntax.typ = (fun projectee -> (match (projectee) with
| Term_name (_51_26) -> begin
_51_26
end))

# 50 "FStar.Parser.Env.fst"
let ___Eff_name____0 : foundname  ->  (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident) = (fun projectee -> (match (projectee) with
| Eff_name (_51_29) -> begin
_51_29
end))

# 52 "FStar.Parser.Env.fst"
type record_or_dc =
{typename : FStar_Ident.lident; constrname : FStar_Ident.lident; parms : FStar_Syntax_Syntax.binders; fields : (FStar_Syntax_Syntax.fieldname * FStar_Syntax_Syntax.typ) Prims.list; is_record : Prims.bool}

# 52 "FStar.Parser.Env.fst"
let is_Mkrecord_or_dc : record_or_dc  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkrecord_or_dc"))))

# 95 "FStar.Parser.Env.fst"
let open_modules : env  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.modul) Prims.list = (fun e -> e.modules)

# 96 "FStar.Parser.Env.fst"
let current_module : env  ->  FStar_Ident.lident = (fun env -> (match (env.curmodule) with
| None -> begin
(FStar_All.failwith "Unset current module")
end
| Some (m) -> begin
m
end))

# 99 "FStar.Parser.Env.fst"
let qual : FStar_Ident.lident  ->  FStar_Ident.ident  ->  FStar_Ident.lident = (fun lid id -> (let _130_87 = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns ((lid.FStar_Ident.ident)::(id)::[])))
in (FStar_Ident.set_lid_range _130_87 id.FStar_Ident.idRange)))

# 100 "FStar.Parser.Env.fst"
let qualify : env  ->  FStar_Ident.ident  ->  FStar_Ident.lident = (fun env id -> (let _130_92 = (current_module env)
in (qual _130_92 id)))

# 101 "FStar.Parser.Env.fst"
let qualify_lid : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (
# 102 "FStar.Parser.Env.fst"
let cur = (current_module env)
in (let _130_97 = (FStar_Ident.lid_of_ids (FStar_List.append (FStar_List.append (FStar_List.append cur.FStar_Ident.ns ((cur.FStar_Ident.ident)::[])) lid.FStar_Ident.ns) ((lid.FStar_Ident.ident)::[])))
in (FStar_Ident.set_lid_range _130_97 (FStar_Ident.range_of_lid lid)))))

# 104 "FStar.Parser.Env.fst"
let new_sigmap = (fun _51_50 -> (match (()) with
| () -> begin
(FStar_Util.smap_create 100)
end))

# 105 "FStar.Parser.Env.fst"
let empty_env : Prims.unit  ->  env = (fun _51_51 -> (match (()) with
| () -> begin
(let _130_102 = (let _130_101 = (new_sigmap ())
in (_130_101)::[])
in {curmodule = None; modules = []; open_namespaces = []; sigaccum = []; localbindings = []; recbindings = []; sigmap = _130_102; default_result_effect = FStar_Syntax_Const.effect_ML_lid; iface = false; admitted_iface = false; expect_typ = false})
end))

# 116 "FStar.Parser.Env.fst"
let sigmap : env  ->  (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap = (fun env -> (FStar_List.hd env.sigmap))

# 117 "FStar.Parser.Env.fst"
let default_total : env  ->  env = (fun env -> (
# 117 "FStar.Parser.Env.fst"
let _51_54 = env
in {curmodule = _51_54.curmodule; modules = _51_54.modules; open_namespaces = _51_54.open_namespaces; sigaccum = _51_54.sigaccum; localbindings = _51_54.localbindings; recbindings = _51_54.recbindings; sigmap = _51_54.sigmap; default_result_effect = FStar_Syntax_Const.effect_Tot_lid; iface = _51_54.iface; admitted_iface = _51_54.admitted_iface; expect_typ = _51_54.expect_typ}))

# 118 "FStar.Parser.Env.fst"
let default_ml : env  ->  env = (fun env -> (
# 118 "FStar.Parser.Env.fst"
let _51_57 = env
in {curmodule = _51_57.curmodule; modules = _51_57.modules; open_namespaces = _51_57.open_namespaces; sigaccum = _51_57.sigaccum; localbindings = _51_57.localbindings; recbindings = _51_57.recbindings; sigmap = _51_57.sigmap; default_result_effect = FStar_Syntax_Const.effect_ML_lid; iface = _51_57.iface; admitted_iface = _51_57.admitted_iface; expect_typ = _51_57.expect_typ}))

# 121 "FStar.Parser.Env.fst"
let set_bv_range : FStar_Syntax_Syntax.bv  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.bv = (fun bv r -> (
# 122 "FStar.Parser.Env.fst"
let id = (
# 122 "FStar.Parser.Env.fst"
let _51_61 = bv.FStar_Syntax_Syntax.ppname
in {FStar_Ident.idText = _51_61.FStar_Ident.idText; FStar_Ident.idRange = r})
in (
# 123 "FStar.Parser.Env.fst"
let _51_64 = bv
in {FStar_Syntax_Syntax.ppname = id; FStar_Syntax_Syntax.index = _51_64.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _51_64.FStar_Syntax_Syntax.sort})))

# 125 "FStar.Parser.Env.fst"
let bv_to_name : FStar_Syntax_Syntax.bv  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.term = (fun bv r -> (FStar_Syntax_Syntax.bv_to_name (set_bv_range bv r)))

# 127 "FStar.Parser.Env.fst"
let unmangleMap : (Prims.string * Prims.string) Prims.list = (("op_ColonColon", "Cons"))::(("not", "op_Negation"))::[]

# 130 "FStar.Parser.Env.fst"
let unmangleOpName : FStar_Ident.ident  ->  FStar_Ident.lident Prims.option = (fun id -> (FStar_Util.find_map unmangleMap (fun _51_71 -> (match (_51_71) with
| (x, y) -> begin
if (id.FStar_Ident.idText = x) then begin
(let _130_120 = (FStar_Ident.lid_of_path (("Prims")::(y)::[]) id.FStar_Ident.idRange)
in Some (_130_120))
end else begin
None
end
end))))

# 135 "FStar.Parser.Env.fst"
let try_lookup_id : env  ->  FStar_Ident.ident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env id -> (match ((unmangleOpName id)) with
| Some (l) -> begin
(let _130_125 = (FStar_Syntax_Syntax.fvar None l id.FStar_Ident.idRange)
in Some (_130_125))
end
| _51_77 -> begin
(FStar_Util.find_map env.localbindings (fun _51_1 -> (match (_51_1) with
| (id', x) when (id'.FStar_Ident.idText = id.FStar_Ident.idText) -> begin
(let _130_127 = (bv_to_name x id.FStar_Ident.idRange)
in Some (_130_127))
end
| _51_83 -> begin
None
end)))
end))

# 144 "FStar.Parser.Env.fst"
let resolve_in_open_namespaces = (fun env lid finder -> (
# 145 "FStar.Parser.Env.fst"
let aux = (fun namespaces -> (match ((finder lid)) with
| Some (r) -> begin
Some (r)
end
| _51_93 -> begin
(
# 149 "FStar.Parser.Env.fst"
let ids = (FStar_Ident.ids_of_lid lid)
in (FStar_Util.find_map namespaces (fun ns -> (
# 151 "FStar.Parser.Env.fst"
let full_name = (FStar_Ident.lid_of_ids (FStar_List.append (FStar_Ident.ids_of_lid ns) ids))
in (finder full_name)))))
end))
in (let _130_138 = (let _130_137 = (current_module env)
in (_130_137)::env.open_namespaces)
in (aux _130_138))))

# 155 "FStar.Parser.Env.fst"
let fv_qual_of_se : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.fv_qual Prims.option = (fun _51_3 -> (match (_51_3) with
| FStar_Syntax_Syntax.Sig_datacon (_51_99, _51_101, _51_103, l, _51_106, quals, _51_109, _51_111) -> begin
(
# 157 "FStar.Parser.Env.fst"
let qopt = (FStar_Util.find_map quals (fun _51_2 -> (match (_51_2) with
| FStar_Syntax_Syntax.RecordConstructor (fs) -> begin
Some (FStar_Syntax_Syntax.Record_ctor ((l, fs)))
end
| _51_118 -> begin
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
| FStar_Syntax_Syntax.Sig_declare_typ (_51_123, _51_125, _51_127, quals, _51_130) -> begin
None
end
| _51_134 -> begin
None
end))

# 168 "FStar.Parser.Env.fst"
let try_lookup_name : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  foundname Prims.option = (fun any_val exclude_interf env lid -> (
# 174 "FStar.Parser.Env.fst"
let find_in_sig = (fun lid -> (match ((let _130_152 = (sigmap env)
in (FStar_Util.smap_try_find _130_152 lid.FStar_Ident.str))) with
| Some (_51_142, true) when exclude_interf -> begin
None
end
| None -> begin
None
end
| Some (se, _51_149) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_51_153) -> begin
(let _130_154 = (let _130_153 = (FStar_Syntax_Syntax.fvar None lid (FStar_Ident.range_of_lid lid))
in Term_name (_130_153))
in Some (_130_154))
end
| FStar_Syntax_Syntax.Sig_datacon (_51_156) -> begin
(let _130_157 = (let _130_156 = (let _130_155 = (fv_qual_of_se se)
in (FStar_Syntax_Syntax.fvar _130_155 lid (FStar_Ident.range_of_lid lid)))
in Term_name (_130_156))
in Some (_130_157))
end
| FStar_Syntax_Syntax.Sig_let (_51_159) -> begin
(let _130_159 = (let _130_158 = (FStar_Syntax_Syntax.fvar None lid (FStar_Ident.range_of_lid lid))
in Term_name (_130_158))
in Some (_130_159))
end
| FStar_Syntax_Syntax.Sig_declare_typ (_51_162, _51_164, _51_166, quals, _51_169) -> begin
if (any_val || (FStar_All.pipe_right quals (FStar_Util.for_some (fun _51_4 -> (match (_51_4) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| _51_175 -> begin
false
end))))) then begin
(let _130_163 = (let _130_162 = (let _130_161 = (fv_qual_of_se se)
in (FStar_Syntax_Syntax.fvar _130_161 lid (FStar_Ident.range_of_lid lid)))
in Term_name (_130_162))
in Some (_130_163))
end else begin
None
end
end
| FStar_Syntax_Syntax.Sig_new_effect (ne, _51_178) -> begin
(let _130_166 = (let _130_165 = (let _130_164 = (FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname (FStar_Ident.range_of_lid lid))
in (se, _130_164))
in Eff_name (_130_165))
in Some (_130_166))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (_51_182) -> begin
Some (Eff_name ((se, lid)))
end
| _51_185 -> begin
None
end)
end))
in (
# 193 "FStar.Parser.Env.fst"
let found_id = (match (lid.FStar_Ident.ns) with
| [] -> begin
(match ((try_lookup_id env lid.FStar_Ident.ident)) with
| Some (e) -> begin
Some (Term_name (e))
end
| None -> begin
(
# 198 "FStar.Parser.Env.fst"
let recname = (qualify env lid.FStar_Ident.ident)
in (FStar_Util.find_map env.recbindings (fun _51_193 -> (match (_51_193) with
| (id, l) -> begin
if (id.FStar_Ident.idText = lid.FStar_Ident.ident.FStar_Ident.idText) then begin
(let _130_170 = (let _130_169 = (let _130_168 = (FStar_Ident.set_lid_range l (FStar_Ident.range_of_lid lid))
in (FStar_Syntax_Syntax.fvar None _130_168 (FStar_Ident.range_of_lid lid)))
in Term_name (_130_169))
in Some (_130_170))
end else begin
None
end
end))))
end)
end
| _51_195 -> begin
None
end)
in (match (found_id) with
| Some (_51_198) -> begin
found_id
end
| _51_201 -> begin
(resolve_in_open_namespaces env lid find_in_sig)
end))))

# 209 "FStar.Parser.Env.fst"
let try_lookup_effect_name' : Prims.bool  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident) Prims.option = (fun exclude_interf env lid -> (match ((try_lookup_name true exclude_interf env lid)) with
| Some (Eff_name (o, l)) -> begin
Some ((o, l))
end
| _51_211 -> begin
None
end))

# 213 "FStar.Parser.Env.fst"
let try_lookup_effect_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env l -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some (o, l) -> begin
Some (l)
end
| _51_219 -> begin
None
end))

# 217 "FStar.Parser.Env.fst"
let try_lookup_effect_defn : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl Prims.option = (fun env l -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some (FStar_Syntax_Syntax.Sig_new_effect (ne, _51_224), _51_228) -> begin
Some (ne)
end
| _51_232 -> begin
None
end))

# 221 "FStar.Parser.Env.fst"
let is_effect_name : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((try_lookup_effect_name env lid)) with
| None -> begin
false
end
| Some (_51_237) -> begin
true
end))

# 226 "FStar.Parser.Env.fst"
let lookup_letbinding_quals : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.qualifier Prims.list = (fun env lid -> (
# 227 "FStar.Parser.Env.fst"
let find_in_sig = (fun lid -> (match ((let _130_195 = (sigmap env)
in (FStar_Util.smap_try_find _130_195 lid.FStar_Ident.str))) with
| Some (FStar_Syntax_Syntax.Sig_declare_typ (lid, _51_245, _51_247, quals, _51_250), _51_254) -> begin
Some (quals)
end
| _51_258 -> begin
None
end))
in (match ((resolve_in_open_namespaces env lid find_in_sig)) with
| Some (quals) -> begin
quals
end
| _51_262 -> begin
[]
end)))

# 235 "FStar.Parser.Env.fst"
let try_lookup_module : env  ->  Prims.string Prims.list  ->  FStar_Syntax_Syntax.modul Prims.option = (fun env path -> (match ((FStar_List.tryFind (fun _51_267 -> (match (_51_267) with
| (mlid, modul) -> begin
((FStar_Ident.path_of_lid mlid) = path)
end)) env.modules)) with
| Some (_51_269, modul) -> begin
Some (modul)
end
| None -> begin
None
end))

# 240 "FStar.Parser.Env.fst"
let try_lookup_let : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env lid -> (
# 241 "FStar.Parser.Env.fst"
let find_in_sig = (fun lid -> (match ((let _130_207 = (sigmap env)
in (FStar_Util.smap_try_find _130_207 lid.FStar_Ident.str))) with
| Some (FStar_Syntax_Syntax.Sig_let (_51_279), _51_282) -> begin
(let _130_208 = (FStar_Syntax_Syntax.fvar None lid (FStar_Ident.range_of_lid lid))
in Some (_130_208))
end
| _51_286 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))

# 247 "FStar.Parser.Env.fst"
let try_lookup_definition : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env lid -> (
# 248 "FStar.Parser.Env.fst"
let find_in_sig = (fun lid -> (match ((let _130_215 = (sigmap env)
in (FStar_Util.smap_try_find _130_215 lid.FStar_Ident.str))) with
| Some (FStar_Syntax_Syntax.Sig_let (lbs, _51_293, _51_295, _51_297), _51_301) -> begin
(FStar_Util.find_map (Prims.snd lbs) (fun lb -> (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (lid') when (FStar_Ident.lid_equals lid lid') -> begin
Some (lb.FStar_Syntax_Syntax.lbdef)
end
| _51_308 -> begin
None
end)))
end
| _51_310 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))

# 260 "FStar.Parser.Env.fst"
let try_lookup_lid' : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun any_val exclude_interf env lid -> (match ((try_lookup_name any_val exclude_interf env lid)) with
| Some (Term_name (e)) -> begin
Some (e)
end
| _51_319 -> begin
None
end))

# 264 "FStar.Parser.Env.fst"
let try_lookup_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env l -> (try_lookup_lid' env.iface false env l))

# 266 "FStar.Parser.Env.fst"
let try_lookup_datacon : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.fv Prims.option = (fun env lid -> (
# 267 "FStar.Parser.Env.fst"
let find_in_sig = (fun lid -> (match ((let _130_235 = (sigmap env)
in (FStar_Util.smap_try_find _130_235 lid.FStar_Ident.str))) with
| Some (FStar_Syntax_Syntax.Sig_declare_typ (_51_327, _51_329, _51_331, quals, _51_334), _51_338) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _51_5 -> (match (_51_5) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| _51_344 -> begin
false
end)))) then begin
(let _130_237 = (FStar_Syntax_Syntax.lid_as_fv lid None)
in Some (_130_237))
end else begin
None
end
end
| Some (FStar_Syntax_Syntax.Sig_datacon (_51_346), _51_349) -> begin
(let _130_238 = (FStar_Syntax_Syntax.lid_as_fv lid (Some (FStar_Syntax_Syntax.Data_ctor)))
in Some (_130_238))
end
| _51_353 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))

# 277 "FStar.Parser.Env.fst"
let find_all_datacons : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.list Prims.option = (fun env lid -> (
# 278 "FStar.Parser.Env.fst"
let find_in_sig = (fun lid -> (match ((let _130_245 = (sigmap env)
in (FStar_Util.smap_try_find _130_245 lid.FStar_Ident.str))) with
| Some (FStar_Syntax_Syntax.Sig_inductive_typ (_51_359, _51_361, _51_363, _51_365, _51_367, datas, _51_370, _51_372), _51_376) -> begin
Some (datas)
end
| _51_380 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))

# 285 "FStar.Parser.Env.fst"
let record_cache_aux : ((Prims.unit  ->  Prims.unit) * (Prims.unit  ->  Prims.unit) * (Prims.unit  ->  record_or_dc Prims.list) * (record_or_dc  ->  Prims.unit)) = (
# 286 "FStar.Parser.Env.fst"
let record_cache = (FStar_Util.mk_ref (([])::[]))
in (
# 287 "FStar.Parser.Env.fst"
let push = (fun _51_383 -> (match (()) with
| () -> begin
(let _130_259 = (let _130_258 = (let _130_256 = (FStar_ST.read record_cache)
in (FStar_List.hd _130_256))
in (let _130_257 = (FStar_ST.read record_cache)
in (_130_258)::_130_257))
in (FStar_ST.op_Colon_Equals record_cache _130_259))
end))
in (
# 289 "FStar.Parser.Env.fst"
let pop = (fun _51_385 -> (match (()) with
| () -> begin
(let _130_263 = (let _130_262 = (FStar_ST.read record_cache)
in (FStar_List.tl _130_262))
in (FStar_ST.op_Colon_Equals record_cache _130_263))
end))
in (
# 291 "FStar.Parser.Env.fst"
let peek = (fun _51_387 -> (match (()) with
| () -> begin
(let _130_266 = (FStar_ST.read record_cache)
in (FStar_List.hd _130_266))
end))
in (
# 292 "FStar.Parser.Env.fst"
let insert = (fun r -> (let _130_273 = (let _130_272 = (let _130_269 = (peek ())
in (r)::_130_269)
in (let _130_271 = (let _130_270 = (FStar_ST.read record_cache)
in (FStar_List.tl _130_270))
in (_130_272)::_130_271))
in (FStar_ST.op_Colon_Equals record_cache _130_273)))
in (push, pop, peek, insert))))))

# 295 "FStar.Parser.Env.fst"
let push_record_cache : Prims.unit  ->  Prims.unit = (
# 296 "FStar.Parser.Env.fst"
let _51_397 = record_cache_aux
in (match (_51_397) with
| (push, _51_392, _51_394, _51_396) -> begin
push
end))

# 299 "FStar.Parser.Env.fst"
let pop_record_cache : Prims.unit  ->  Prims.unit = (
# 300 "FStar.Parser.Env.fst"
let _51_405 = record_cache_aux
in (match (_51_405) with
| (_51_399, pop, _51_402, _51_404) -> begin
pop
end))

# 303 "FStar.Parser.Env.fst"
let peek_record_cache : Prims.unit  ->  record_or_dc Prims.list = (
# 304 "FStar.Parser.Env.fst"
let _51_413 = record_cache_aux
in (match (_51_413) with
| (_51_407, _51_409, peek, _51_412) -> begin
peek
end))

# 307 "FStar.Parser.Env.fst"
let insert_record_cache : record_or_dc  ->  Prims.unit = (
# 308 "FStar.Parser.Env.fst"
let _51_421 = record_cache_aux
in (match (_51_421) with
| (_51_415, _51_417, _51_419, insert) -> begin
insert
end))

# 311 "FStar.Parser.Env.fst"
let extract_record : env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun e _51_9 -> (match (_51_9) with
| FStar_Syntax_Syntax.Sig_bundle (sigs, _51_426, _51_428, _51_430) -> begin
(
# 313 "FStar.Parser.Env.fst"
let is_rec = (FStar_Util.for_some (fun _51_6 -> (match (_51_6) with
| (FStar_Syntax_Syntax.RecordType (_)) | (FStar_Syntax_Syntax.RecordConstructor (_)) -> begin
true
end
| _51_441 -> begin
false
end)))
in (
# 318 "FStar.Parser.Env.fst"
let find_dc = (fun dc -> (FStar_All.pipe_right sigs (FStar_Util.find_opt (fun _51_7 -> (match (_51_7) with
| FStar_Syntax_Syntax.Sig_datacon (lid, _51_448, _51_450, _51_452, _51_454, _51_456, _51_458, _51_460) -> begin
(FStar_Ident.lid_equals dc lid)
end
| _51_464 -> begin
false
end)))))
in (FStar_All.pipe_right sigs (FStar_List.iter (fun _51_8 -> (match (_51_8) with
| FStar_Syntax_Syntax.Sig_inductive_typ (typename, univs, parms, _51_470, _51_472, dc::[], tags, _51_477) -> begin
(match ((let _130_344 = (find_dc dc)
in (FStar_All.pipe_left FStar_Util.must _130_344))) with
| FStar_Syntax_Syntax.Sig_datacon (constrname, _51_482, t, _51_485, _51_487, _51_489, _51_491, _51_493) -> begin
(
# 327 "FStar.Parser.Env.fst"
let _51_499 = (FStar_Syntax_Util.arrow_formals t)
in (match (_51_499) with
| (formals, _51_498) -> begin
(
# 328 "FStar.Parser.Env.fst"
let is_rec = (is_rec tags)
in (
# 329 "FStar.Parser.Env.fst"
let fields = (FStar_All.pipe_right formals (FStar_List.collect (fun _51_503 -> (match (_51_503) with
| (x, q) -> begin
if ((FStar_Syntax_Syntax.is_null_bv x) || (is_rec && (q = Some (FStar_Syntax_Syntax.Implicit)))) then begin
[]
end else begin
(let _130_348 = (let _130_347 = (let _130_346 = if is_rec then begin
(FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname)
end else begin
x.FStar_Syntax_Syntax.ppname
end
in (qual constrname _130_346))
in (_130_347, x.FStar_Syntax_Syntax.sort))
in (_130_348)::[])
end
end))))
in (
# 334 "FStar.Parser.Env.fst"
let record = {typename = typename; constrname = constrname; parms = parms; fields = fields; is_record = is_rec}
in (insert_record_cache record))))
end))
end
| _51_507 -> begin
()
end)
end
| _51_509 -> begin
()
end))))))
end
| _51_511 -> begin
()
end))

# 346 "FStar.Parser.Env.fst"
let try_lookup_record_or_dc_by_field_name : env  ->  FStar_Ident.lident  ->  (record_or_dc * FStar_Ident.lident) Prims.option = (fun env fieldname -> (
# 347 "FStar.Parser.Env.fst"
let maybe_add_constrname = (fun ns c -> (
# 348 "FStar.Parser.Env.fst"
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
(let _130_359 = (aux tl)
in (hd)::_130_359)
end))
in (aux ns)))
in (
# 353 "FStar.Parser.Env.fst"
let find_in_cache = (fun fieldname -> (
# 355 "FStar.Parser.Env.fst"
let _51_529 = (fieldname.FStar_Ident.ns, fieldname.FStar_Ident.ident)
in (match (_51_529) with
| (ns, fieldname) -> begin
(let _130_364 = (peek_record_cache ())
in (FStar_Util.find_map _130_364 (fun record -> (
# 357 "FStar.Parser.Env.fst"
let constrname = record.constrname.FStar_Ident.ident
in (
# 358 "FStar.Parser.Env.fst"
let ns = (maybe_add_constrname ns constrname)
in (
# 359 "FStar.Parser.Env.fst"
let fname = (FStar_Ident.lid_of_ids (FStar_List.append ns ((fieldname)::[])))
in (FStar_Util.find_map record.fields (fun _51_537 -> (match (_51_537) with
| (f, _51_536) -> begin
if (FStar_Ident.lid_equals fname f) then begin
Some ((record, fname))
end else begin
None
end
end)))))))))
end)))
in (resolve_in_open_namespaces env fieldname find_in_cache))))

# 366 "FStar.Parser.Env.fst"
let try_lookup_record_by_field_name : env  ->  FStar_Ident.lident  ->  (record_or_dc * FStar_Ident.lident) Prims.option = (fun env fieldname -> (match ((try_lookup_record_or_dc_by_field_name env fieldname)) with
| Some (r, f) when r.is_record -> begin
Some ((r, f))
end
| _51_545 -> begin
None
end))

# 371 "FStar.Parser.Env.fst"
let try_lookup_projector_by_field_name : env  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * Prims.bool) Prims.option = (fun env fieldname -> (match ((try_lookup_record_or_dc_by_field_name env fieldname)) with
| Some (r, f) -> begin
Some ((f, r.is_record))
end
| _51_553 -> begin
None
end))

# 376 "FStar.Parser.Env.fst"
let qualify_field_to_record : env  ->  record_or_dc  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env recd f -> (
# 377 "FStar.Parser.Env.fst"
let qualify = (fun fieldname -> (
# 378 "FStar.Parser.Env.fst"
let _51_561 = (fieldname.FStar_Ident.ns, fieldname.FStar_Ident.ident)
in (match (_51_561) with
| (ns, fieldname) -> begin
(
# 379 "FStar.Parser.Env.fst"
let constrname = recd.constrname.FStar_Ident.ident
in (
# 380 "FStar.Parser.Env.fst"
let fname = (FStar_Ident.lid_of_ids (FStar_List.append (FStar_List.append ns ((constrname)::[])) ((fieldname)::[])))
in (FStar_Util.find_map recd.fields (fun _51_567 -> (match (_51_567) with
| (f, _51_566) -> begin
if (FStar_Ident.lid_equals fname f) then begin
Some (fname)
end else begin
None
end
end)))))
end)))
in (resolve_in_open_namespaces env f qualify)))

# 387 "FStar.Parser.Env.fst"
let unique : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  Prims.bool = (fun any_val exclude_if env lid -> (
# 388 "FStar.Parser.Env.fst"
let this_env = (
# 388 "FStar.Parser.Env.fst"
let _51_572 = env
in {curmodule = _51_572.curmodule; modules = _51_572.modules; open_namespaces = []; sigaccum = _51_572.sigaccum; localbindings = _51_572.localbindings; recbindings = _51_572.recbindings; sigmap = _51_572.sigmap; default_result_effect = _51_572.default_result_effect; iface = _51_572.iface; admitted_iface = _51_572.admitted_iface; expect_typ = _51_572.expect_typ})
in (match ((try_lookup_lid' any_val exclude_if env lid)) with
| None -> begin
true
end
| Some (_51_577) -> begin
false
end)))

# 393 "FStar.Parser.Env.fst"
let push_bv : env  ->  FStar_Ident.ident  ->  (env * FStar_Syntax_Syntax.bv) = (fun env x -> (
# 394 "FStar.Parser.Env.fst"
let bv = (FStar_Syntax_Syntax.gen_bv x.FStar_Ident.idText (Some (x.FStar_Ident.idRange)) FStar_Syntax_Syntax.tun)
in ((
# 395 "FStar.Parser.Env.fst"
let _51_582 = env
in {curmodule = _51_582.curmodule; modules = _51_582.modules; open_namespaces = _51_582.open_namespaces; sigaccum = _51_582.sigaccum; localbindings = ((x, bv))::env.localbindings; recbindings = _51_582.recbindings; sigmap = _51_582.sigmap; default_result_effect = _51_582.default_result_effect; iface = _51_582.iface; admitted_iface = _51_582.admitted_iface; expect_typ = _51_582.expect_typ}), bv)))

# 397 "FStar.Parser.Env.fst"
let push_top_level_rec_binding : env  ->  FStar_Ident.ident  ->  env = (fun env x -> (
# 398 "FStar.Parser.Env.fst"
let l = (qualify env x)
in if (unique false true env l) then begin
(
# 400 "FStar.Parser.Env.fst"
let _51_587 = env
in {curmodule = _51_587.curmodule; modules = _51_587.modules; open_namespaces = _51_587.open_namespaces; sigaccum = _51_587.sigaccum; localbindings = _51_587.localbindings; recbindings = ((x, l))::env.recbindings; sigmap = _51_587.sigmap; default_result_effect = _51_587.default_result_effect; iface = _51_587.iface; admitted_iface = _51_587.admitted_iface; expect_typ = _51_587.expect_typ})
end else begin
(Prims.raise (FStar_Syntax_Syntax.Error (((Prims.strcat "Duplicate top-level names " l.FStar_Ident.str), (FStar_Ident.range_of_lid l)))))
end))

# 403 "FStar.Parser.Env.fst"
let push_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env s -> (
# 404 "FStar.Parser.Env.fst"
let err = (fun l -> (
# 405 "FStar.Parser.Env.fst"
let sopt = (let _130_404 = (sigmap env)
in (FStar_Util.smap_try_find _130_404 l.FStar_Ident.str))
in (
# 406 "FStar.Parser.Env.fst"
let r = (match (sopt) with
| Some (se, _51_596) -> begin
(match ((let _130_405 = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_Util.find_opt (FStar_Ident.lid_equals l) _130_405))) with
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
in (let _130_408 = (let _130_407 = (let _130_406 = (FStar_Util.format2 "Duplicate top-level names [%s]; previously declared at %s" (FStar_Ident.text_of_lid l) r)
in (_130_406, (FStar_Ident.range_of_lid l)))
in FStar_Syntax_Syntax.Error (_130_407))
in (Prims.raise _130_408)))))
in (
# 414 "FStar.Parser.Env.fst"
let env = (
# 415 "FStar.Parser.Env.fst"
let _51_614 = (match (s) with
| FStar_Syntax_Syntax.Sig_let (_51_605) -> begin
(false, true)
end
| FStar_Syntax_Syntax.Sig_bundle (_51_608) -> begin
(true, true)
end
| _51_611 -> begin
(false, false)
end)
in (match (_51_614) with
| (any_val, exclude_if) -> begin
(
# 419 "FStar.Parser.Env.fst"
let lids = (FStar_Syntax_Util.lids_of_sigelt s)
in (match ((FStar_Util.find_map lids (fun l -> if (not ((unique any_val exclude_if env l))) then begin
Some (l)
end else begin
None
end))) with
| None -> begin
(
# 421 "FStar.Parser.Env.fst"
let _51_618 = (extract_record env s)
in (
# 421 "FStar.Parser.Env.fst"
let _51_620 = env
in {curmodule = _51_620.curmodule; modules = _51_620.modules; open_namespaces = _51_620.open_namespaces; sigaccum = (s)::env.sigaccum; localbindings = _51_620.localbindings; recbindings = _51_620.recbindings; sigmap = _51_620.sigmap; default_result_effect = _51_620.default_result_effect; iface = _51_620.iface; admitted_iface = _51_620.admitted_iface; expect_typ = _51_620.expect_typ}))
end
| Some (l) -> begin
(err l)
end))
end))
in (
# 424 "FStar.Parser.Env.fst"
let _51_639 = (match (s) with
| FStar_Syntax_Syntax.Sig_bundle (ses, _51_627, _51_629, _51_631) -> begin
(let _130_412 = (FStar_List.map (fun se -> (let _130_411 = (FStar_Syntax_Util.lids_of_sigelt se)
in (_130_411, se))) ses)
in (env, _130_412))
end
| _51_636 -> begin
(let _130_415 = (let _130_414 = (let _130_413 = (FStar_Syntax_Util.lids_of_sigelt s)
in (_130_413, s))
in (_130_414)::[])
in (env, _130_415))
end)
in (match (_51_639) with
| (env, lss) -> begin
(
# 427 "FStar.Parser.Env.fst"
let _51_644 = (FStar_All.pipe_right lss (FStar_List.iter (fun _51_642 -> (match (_51_642) with
| (lids, se) -> begin
(FStar_All.pipe_right lids (FStar_List.iter (fun lid -> (let _130_418 = (sigmap env)
in (FStar_Util.smap_add _130_418 lid.FStar_Ident.str (se, (env.iface && (not (env.admitted_iface)))))))))
end))))
in env)
end)))))

# 432 "FStar.Parser.Env.fst"
let push_namespace : env  ->  FStar_Ident.lident  ->  env = (fun env lid -> (
# 433 "FStar.Parser.Env.fst"
let _51_648 = env
in {curmodule = _51_648.curmodule; modules = _51_648.modules; open_namespaces = (lid)::env.open_namespaces; sigaccum = _51_648.sigaccum; localbindings = _51_648.localbindings; recbindings = _51_648.recbindings; sigmap = _51_648.sigmap; default_result_effect = _51_648.default_result_effect; iface = _51_648.iface; admitted_iface = _51_648.admitted_iface; expect_typ = _51_648.expect_typ}))

# 435 "FStar.Parser.Env.fst"
let check_admits : env  ->  Prims.unit = (fun env -> (FStar_All.pipe_right env.sigaccum (FStar_List.iter (fun se -> (match (se) with
| FStar_Syntax_Syntax.Sig_declare_typ (l, u, t, quals, r) -> begin
(match ((try_lookup_lid env l)) with
| None -> begin
(
# 440 "FStar.Parser.Env.fst"
let _51_660 = (let _130_428 = (let _130_427 = (FStar_Range.string_of_range (FStar_Ident.range_of_lid l))
in (let _130_426 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format2 "%s: Warning: Admitting %s without a definition\n" _130_427 _130_426)))
in (FStar_Util.print_string _130_428))
in (let _130_429 = (sigmap env)
in (FStar_Util.smap_add _130_429 l.FStar_Ident.str (FStar_Syntax_Syntax.Sig_declare_typ ((l, u, t, (FStar_Syntax_Syntax.Assumption)::quals, r)), false))))
end
| Some (_51_663) -> begin
()
end)
end
| _51_666 -> begin
()
end)))))

# 446 "FStar.Parser.Env.fst"
let finish : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env modul -> (
# 447 "FStar.Parser.Env.fst"
let _51_710 = (FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations (FStar_List.iter (fun _51_11 -> (match (_51_11) with
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _51_673, _51_675) -> begin
if (FStar_List.contains FStar_Syntax_Syntax.Private quals) then begin
(FStar_All.pipe_right ses (FStar_List.iter (fun _51_10 -> (match (_51_10) with
| FStar_Syntax_Syntax.Sig_datacon (lid, _51_681, _51_683, _51_685, _51_687, _51_689, _51_691, _51_693) -> begin
(let _130_436 = (sigmap env)
in (FStar_Util.smap_remove _130_436 lid.FStar_Ident.str))
end
| _51_697 -> begin
()
end))))
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _51_700, _51_702, quals, _51_705) -> begin
if (FStar_List.contains FStar_Syntax_Syntax.Private quals) then begin
(let _130_437 = (sigmap env)
in (FStar_Util.smap_remove _130_437 lid.FStar_Ident.str))
end else begin
()
end
end
| _51_709 -> begin
()
end))))
in (
# 457 "FStar.Parser.Env.fst"
let _51_712 = env
in {curmodule = None; modules = ((modul.FStar_Syntax_Syntax.name, modul))::env.modules; open_namespaces = []; sigaccum = []; localbindings = []; recbindings = []; sigmap = _51_712.sigmap; default_result_effect = _51_712.default_result_effect; iface = _51_712.iface; admitted_iface = _51_712.admitted_iface; expect_typ = _51_712.expect_typ})))

# 465 "FStar.Parser.Env.fst"
let push : env  ->  env = (fun env -> (
# 466 "FStar.Parser.Env.fst"
let _51_715 = (push_record_cache ())
in (
# 467 "FStar.Parser.Env.fst"
let _51_717 = env
in (let _130_442 = (let _130_441 = (let _130_440 = (sigmap env)
in (FStar_Util.smap_copy _130_440))
in (_130_441)::env.sigmap)
in {curmodule = _51_717.curmodule; modules = _51_717.modules; open_namespaces = _51_717.open_namespaces; sigaccum = _51_717.sigaccum; localbindings = _51_717.localbindings; recbindings = _51_717.recbindings; sigmap = _130_442; default_result_effect = _51_717.default_result_effect; iface = _51_717.iface; admitted_iface = _51_717.admitted_iface; expect_typ = _51_717.expect_typ}))))

# 470 "FStar.Parser.Env.fst"
let mark : env  ->  env = (fun env -> (push env))

# 471 "FStar.Parser.Env.fst"
let reset_mark : env  ->  env = (fun env -> (
# 471 "FStar.Parser.Env.fst"
let _51_721 = env
in (let _130_447 = (FStar_List.tl env.sigmap)
in {curmodule = _51_721.curmodule; modules = _51_721.modules; open_namespaces = _51_721.open_namespaces; sigaccum = _51_721.sigaccum; localbindings = _51_721.localbindings; recbindings = _51_721.recbindings; sigmap = _130_447; default_result_effect = _51_721.default_result_effect; iface = _51_721.iface; admitted_iface = _51_721.admitted_iface; expect_typ = _51_721.expect_typ})))

# 472 "FStar.Parser.Env.fst"
let commit_mark : env  ->  env = (fun env -> (match (env.sigmap) with
| hd::_51_726::tl -> begin
(
# 473 "FStar.Parser.Env.fst"
let _51_730 = env
in {curmodule = _51_730.curmodule; modules = _51_730.modules; open_namespaces = _51_730.open_namespaces; sigaccum = _51_730.sigaccum; localbindings = _51_730.localbindings; recbindings = _51_730.recbindings; sigmap = (hd)::tl; default_result_effect = _51_730.default_result_effect; iface = _51_730.iface; admitted_iface = _51_730.admitted_iface; expect_typ = _51_730.expect_typ})
end
| _51_733 -> begin
(FStar_All.failwith "Impossible")
end))

# 475 "FStar.Parser.Env.fst"
let pop : env  ->  env = (fun env -> (match (env.sigmap) with
| _51_737::maps -> begin
(
# 477 "FStar.Parser.Env.fst"
let _51_739 = (pop_record_cache ())
in (
# 478 "FStar.Parser.Env.fst"
let _51_741 = env
in {curmodule = _51_741.curmodule; modules = _51_741.modules; open_namespaces = _51_741.open_namespaces; sigaccum = _51_741.sigaccum; localbindings = _51_741.localbindings; recbindings = _51_741.recbindings; sigmap = maps; default_result_effect = _51_741.default_result_effect; iface = _51_741.iface; admitted_iface = _51_741.admitted_iface; expect_typ = _51_741.expect_typ}))
end
| _51_744 -> begin
(FStar_All.failwith "No more modules to pop")
end))

# 482 "FStar.Parser.Env.fst"
let export_interface : FStar_Ident.lident  ->  env  ->  env = (fun m env -> (
# 484 "FStar.Parser.Env.fst"
let sigelt_in_m = (fun se -> (match ((FStar_Syntax_Util.lids_of_sigelt se)) with
| l::_51_750 -> begin
(l.FStar_Ident.nsstr = m.FStar_Ident.str)
end
| _51_754 -> begin
false
end))
in (
# 488 "FStar.Parser.Env.fst"
let sm = (sigmap env)
in (
# 489 "FStar.Parser.Env.fst"
let env = (pop env)
in (
# 490 "FStar.Parser.Env.fst"
let keys = (FStar_Util.smap_keys sm)
in (
# 491 "FStar.Parser.Env.fst"
let sm' = (sigmap env)
in (
# 492 "FStar.Parser.Env.fst"
let _51_778 = (FStar_All.pipe_right keys (FStar_List.iter (fun k -> (match ((FStar_Util.smap_try_find sm' k)) with
| Some (se, true) when (sigelt_in_m se) -> begin
(
# 495 "FStar.Parser.Env.fst"
let _51_764 = (FStar_Util.smap_remove sm' k)
in (
# 497 "FStar.Parser.Env.fst"
let se = (match (se) with
| FStar_Syntax_Syntax.Sig_declare_typ (l, u, t, q, r) -> begin
FStar_Syntax_Syntax.Sig_declare_typ ((l, u, t, (FStar_Syntax_Syntax.Assumption)::q, r))
end
| _51_774 -> begin
se
end)
in (FStar_Util.smap_add sm' k (se, false))))
end
| _51_777 -> begin
()
end))))
in env)))))))

# 504 "FStar.Parser.Env.fst"
let finish_module_or_interface : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env modul -> (
# 505 "FStar.Parser.Env.fst"
let _51_782 = if (not (modul.FStar_Syntax_Syntax.is_interface)) then begin
(check_admits env)
end else begin
()
end
in (finish env modul)))

# 509 "FStar.Parser.Env.fst"
let prepare_module_or_interface : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  (env * Prims.bool) = (fun intf admitted env mname -> (
# 510 "FStar.Parser.Env.fst"
let prep = (fun env -> (
# 511 "FStar.Parser.Env.fst"
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
# 515 "FStar.Parser.Env.fst"
let _51_791 = env
in {curmodule = Some (mname); modules = _51_791.modules; open_namespaces = open_ns; sigaccum = _51_791.sigaccum; localbindings = _51_791.localbindings; recbindings = _51_791.recbindings; sigmap = env.sigmap; default_result_effect = _51_791.default_result_effect; iface = intf; admitted_iface = admitted; expect_typ = _51_791.expect_typ})))
in (match ((FStar_All.pipe_right env.modules (FStar_Util.find_opt (fun _51_796 -> (match (_51_796) with
| (l, _51_795) -> begin
(FStar_Ident.lid_equals l mname)
end))))) with
| None -> begin
((prep env), false)
end
| Some (_51_799, m) -> begin
(
# 520 "FStar.Parser.Env.fst"
let _51_803 = if ((not (m.FStar_Syntax_Syntax.is_interface)) || intf) then begin
(let _130_476 = (let _130_475 = (let _130_474 = (FStar_Util.format1 "Duplicate module or interface name: %s" mname.FStar_Ident.str)
in (_130_474, (FStar_Ident.range_of_lid mname)))
in FStar_Syntax_Syntax.Error (_130_475))
in (Prims.raise _130_476))
end else begin
()
end
in (let _130_478 = (let _130_477 = (push env)
in (prep _130_477))
in (_130_478, true)))
end)))

# 525 "FStar.Parser.Env.fst"
let enter_monad_scope : env  ->  FStar_Ident.ident  ->  env = (fun env mname -> (
# 526 "FStar.Parser.Env.fst"
let curmod = (current_module env)
in (
# 527 "FStar.Parser.Env.fst"
let mscope = (FStar_Ident.lid_of_ids (FStar_List.append curmod.FStar_Ident.ns ((curmod.FStar_Ident.ident)::(mname)::[])))
in (
# 528 "FStar.Parser.Env.fst"
let _51_809 = env
in {curmodule = Some (mscope); modules = _51_809.modules; open_namespaces = (curmod)::env.open_namespaces; sigaccum = _51_809.sigaccum; localbindings = _51_809.localbindings; recbindings = _51_809.recbindings; sigmap = _51_809.sigmap; default_result_effect = _51_809.default_result_effect; iface = _51_809.iface; admitted_iface = _51_809.admitted_iface; expect_typ = _51_809.expect_typ}))))

# 532 "FStar.Parser.Env.fst"
let exit_monad_scope : env  ->  env  ->  env = (fun env0 env -> (
# 533 "FStar.Parser.Env.fst"
let _51_813 = env
in {curmodule = env0.curmodule; modules = _51_813.modules; open_namespaces = env0.open_namespaces; sigaccum = _51_813.sigaccum; localbindings = _51_813.localbindings; recbindings = _51_813.recbindings; sigmap = _51_813.sigmap; default_result_effect = _51_813.default_result_effect; iface = _51_813.iface; admitted_iface = _51_813.admitted_iface; expect_typ = _51_813.expect_typ}))

# 537 "FStar.Parser.Env.fst"
let fail_or = (fun lookup lid -> (match ((lookup lid)) with
| None -> begin
(let _130_494 = (let _130_493 = (let _130_492 = (FStar_Util.format1 "Identifier not found: [%s]" (FStar_Ident.text_of_lid lid))
in (_130_492, (FStar_Ident.range_of_lid lid)))
in FStar_Syntax_Syntax.Error (_130_493))
in (Prims.raise _130_494))
end
| Some (r) -> begin
r
end))

# 542 "FStar.Parser.Env.fst"
let fail_or2 = (fun lookup id -> (match ((lookup id)) with
| None -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (((Prims.strcat (Prims.strcat "Identifier not found [" id.FStar_Ident.idText) "]"), id.FStar_Ident.idRange))))
end
| Some (r) -> begin
r
end))




