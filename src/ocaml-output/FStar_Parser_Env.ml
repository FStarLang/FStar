
open Prims
# 34 "FStar.Parser.Env.fst"
type env =
{curmodule : FStar_Ident.lident Prims.option; modules : (FStar_Ident.lident * FStar_Syntax_Syntax.modul) Prims.list; open_namespaces : FStar_Ident.lident Prims.list; sigaccum : FStar_Syntax_Syntax.sigelts; localbindings : (FStar_Ident.ident * FStar_Syntax_Syntax.bv) Prims.list; recbindings : (FStar_Ident.ident * FStar_Ident.lid * FStar_Syntax_Syntax.delta_depth) Prims.list; sigmap : (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap Prims.list; default_result_effect : FStar_Ident.lident; iface : Prims.bool; admitted_iface : Prims.bool; expect_typ : Prims.bool}

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
| Term_name (_50_26) -> begin
_50_26
end))

# 50 "FStar.Parser.Env.fst"
let ___Eff_name____0 : foundname  ->  (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident) = (fun projectee -> (match (projectee) with
| Eff_name (_50_29) -> begin
_50_29
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
let qual : FStar_Ident.lident  ->  FStar_Ident.ident  ->  FStar_Ident.lident = (fun lid id -> (let _132_87 = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns ((lid.FStar_Ident.ident)::(id)::[])))
in (FStar_Ident.set_lid_range _132_87 id.FStar_Ident.idRange)))

# 100 "FStar.Parser.Env.fst"
let qualify : env  ->  FStar_Ident.ident  ->  FStar_Ident.lident = (fun env id -> (let _132_92 = (current_module env)
in (qual _132_92 id)))

# 101 "FStar.Parser.Env.fst"
let qualify_lid : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (
# 102 "FStar.Parser.Env.fst"
let cur = (current_module env)
in (let _132_97 = (FStar_Ident.lid_of_ids (FStar_List.append (FStar_List.append (FStar_List.append cur.FStar_Ident.ns ((cur.FStar_Ident.ident)::[])) lid.FStar_Ident.ns) ((lid.FStar_Ident.ident)::[])))
in (FStar_Ident.set_lid_range _132_97 (FStar_Ident.range_of_lid lid)))))

# 104 "FStar.Parser.Env.fst"
let new_sigmap = (fun _50_50 -> (match (()) with
| () -> begin
(FStar_Util.smap_create 100)
end))

# 105 "FStar.Parser.Env.fst"
let empty_env : Prims.unit  ->  env = (fun _50_51 -> (match (()) with
| () -> begin
(let _132_102 = (let _132_101 = (new_sigmap ())
in (_132_101)::[])
in {curmodule = None; modules = []; open_namespaces = []; sigaccum = []; localbindings = []; recbindings = []; sigmap = _132_102; default_result_effect = FStar_Syntax_Const.effect_ML_lid; iface = false; admitted_iface = false; expect_typ = false})
end))

# 116 "FStar.Parser.Env.fst"
let sigmap : env  ->  (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap = (fun env -> (FStar_List.hd env.sigmap))

# 117 "FStar.Parser.Env.fst"
let default_total : env  ->  env = (fun env -> (
# 117 "FStar.Parser.Env.fst"
let _50_54 = env
in {curmodule = _50_54.curmodule; modules = _50_54.modules; open_namespaces = _50_54.open_namespaces; sigaccum = _50_54.sigaccum; localbindings = _50_54.localbindings; recbindings = _50_54.recbindings; sigmap = _50_54.sigmap; default_result_effect = FStar_Syntax_Const.effect_Tot_lid; iface = _50_54.iface; admitted_iface = _50_54.admitted_iface; expect_typ = _50_54.expect_typ}))

# 118 "FStar.Parser.Env.fst"
let default_ml : env  ->  env = (fun env -> (
# 118 "FStar.Parser.Env.fst"
let _50_57 = env
in {curmodule = _50_57.curmodule; modules = _50_57.modules; open_namespaces = _50_57.open_namespaces; sigaccum = _50_57.sigaccum; localbindings = _50_57.localbindings; recbindings = _50_57.recbindings; sigmap = _50_57.sigmap; default_result_effect = FStar_Syntax_Const.effect_ML_lid; iface = _50_57.iface; admitted_iface = _50_57.admitted_iface; expect_typ = _50_57.expect_typ}))

# 121 "FStar.Parser.Env.fst"
let set_bv_range : FStar_Syntax_Syntax.bv  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.bv = (fun bv r -> (
# 122 "FStar.Parser.Env.fst"
let id = (
# 122 "FStar.Parser.Env.fst"
let _50_61 = bv.FStar_Syntax_Syntax.ppname
in {FStar_Ident.idText = _50_61.FStar_Ident.idText; FStar_Ident.idRange = r})
in (
# 123 "FStar.Parser.Env.fst"
let _50_64 = bv
in {FStar_Syntax_Syntax.ppname = id; FStar_Syntax_Syntax.index = _50_64.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _50_64.FStar_Syntax_Syntax.sort})))

# 125 "FStar.Parser.Env.fst"
let bv_to_name : FStar_Syntax_Syntax.bv  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.term = (fun bv r -> (FStar_Syntax_Syntax.bv_to_name (set_bv_range bv r)))

# 127 "FStar.Parser.Env.fst"
let unmangleMap : (Prims.string * Prims.string * FStar_Syntax_Syntax.delta_depth * FStar_Syntax_Syntax.fv_qual Prims.option) Prims.list = (("op_ColonColon", "Cons", FStar_Syntax_Syntax.Delta_constant, Some (FStar_Syntax_Syntax.Data_ctor)))::(("not", "op_Negation", FStar_Syntax_Syntax.Delta_equational, None))::[]

# 130 "FStar.Parser.Env.fst"
let unmangleOpName : FStar_Ident.ident  ->  FStar_Syntax_Syntax.term Prims.option = (fun id -> (FStar_Util.find_map unmangleMap (fun _50_73 -> (match (_50_73) with
| (x, y, dd, dq) -> begin
if (id.FStar_Ident.idText = x) then begin
(let _132_121 = (let _132_120 = (FStar_Ident.lid_of_path (("Prims")::(y)::[]) id.FStar_Ident.idRange)
in (FStar_Syntax_Syntax.fvar _132_120 dd dq))
in Some (_132_121))
end else begin
None
end
end))))

# 135 "FStar.Parser.Env.fst"
let try_lookup_id : env  ->  FStar_Ident.ident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env id -> (match ((unmangleOpName id)) with
| Some (f) -> begin
Some (f)
end
| _50_79 -> begin
(FStar_Util.find_map env.localbindings (fun _50_1 -> (match (_50_1) with
| (id', x) when (id'.FStar_Ident.idText = id.FStar_Ident.idText) -> begin
(let _132_127 = (bv_to_name x id.FStar_Ident.idRange)
in Some (_132_127))
end
| _50_85 -> begin
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
| _50_95 -> begin
(
# 149 "FStar.Parser.Env.fst"
let ids = (FStar_Ident.ids_of_lid lid)
in (FStar_Util.find_map namespaces (fun ns -> (
# 151 "FStar.Parser.Env.fst"
let full_name = (FStar_Ident.lid_of_ids (FStar_List.append (FStar_Ident.ids_of_lid ns) ids))
in (finder full_name)))))
end))
in (let _132_138 = (let _132_137 = (current_module env)
in (_132_137)::env.open_namespaces)
in (aux _132_138))))

# 155 "FStar.Parser.Env.fst"
let fv_qual_of_se : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.fv_qual Prims.option = (fun _50_3 -> (match (_50_3) with
| FStar_Syntax_Syntax.Sig_datacon (_50_101, _50_103, _50_105, l, _50_108, quals, _50_111, _50_113) -> begin
(
# 157 "FStar.Parser.Env.fst"
let qopt = (FStar_Util.find_map quals (fun _50_2 -> (match (_50_2) with
| FStar_Syntax_Syntax.RecordConstructor (fs) -> begin
Some (FStar_Syntax_Syntax.Record_ctor ((l, fs)))
end
| _50_120 -> begin
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
| FStar_Syntax_Syntax.Sig_declare_typ (_50_125, _50_127, _50_129, quals, _50_132) -> begin
None
end
| _50_136 -> begin
None
end))

# 168 "FStar.Parser.Env.fst"
let lb_fv : FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.fv = (fun lbs lid -> (let _132_147 = (FStar_Util.find_map lbs (fun lb -> (
# 170 "FStar.Parser.Env.fst"
let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in if (FStar_Syntax_Syntax.fv_eq_lid fv lid) then begin
Some (fv)
end else begin
None
end)))
in (FStar_All.pipe_right _132_147 FStar_Util.must)))

# 173 "FStar.Parser.Env.fst"
let try_lookup_name : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  foundname Prims.option = (fun any_val exclude_interf env lid -> (
# 179 "FStar.Parser.Env.fst"
let find_in_sig = (fun lid -> (match ((let _132_158 = (sigmap env)
in (FStar_Util.smap_try_find _132_158 lid.FStar_Ident.str))) with
| Some (_50_148, true) when exclude_interf -> begin
None
end
| None -> begin
None
end
| Some (se, _50_155) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_50_159) -> begin
(let _132_160 = (let _132_159 = (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.Delta_constant None)
in Term_name (_132_159))
in Some (_132_160))
end
| FStar_Syntax_Syntax.Sig_datacon (_50_162) -> begin
(let _132_163 = (let _132_162 = (let _132_161 = (fv_qual_of_se se)
in (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.Delta_constant _132_161))
in Term_name (_132_162))
in Some (_132_163))
end
| FStar_Syntax_Syntax.Sig_let ((_50_165, lbs), _50_169, _50_171, _50_173) -> begin
(
# 188 "FStar.Parser.Env.fst"
let fv = (lb_fv lbs lid)
in (let _132_165 = (let _132_164 = (FStar_Syntax_Syntax.fvar lid fv.FStar_Syntax_Syntax.fv_delta fv.FStar_Syntax_Syntax.fv_qual)
in Term_name (_132_164))
in Some (_132_165)))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _50_179, _50_181, quals, _50_184) -> begin
if (any_val || (FStar_All.pipe_right quals (FStar_Util.for_some (fun _50_4 -> (match (_50_4) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| _50_190 -> begin
false
end))))) then begin
(
# 193 "FStar.Parser.Env.fst"
let dd = if (FStar_Syntax_Util.is_primop_lid lid) then begin
FStar_Syntax_Syntax.Delta_equational
end else begin
FStar_Syntax_Syntax.Delta_constant
end
in (let _132_169 = (let _132_168 = (let _132_167 = (fv_qual_of_se se)
in (FStar_Syntax_Syntax.fvar lid dd _132_167))
in Term_name (_132_168))
in Some (_132_169)))
end else begin
None
end
end
| FStar_Syntax_Syntax.Sig_new_effect (ne, _50_194) -> begin
(let _132_172 = (let _132_171 = (let _132_170 = (FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname (FStar_Ident.range_of_lid lid))
in (se, _132_170))
in Eff_name (_132_171))
in Some (_132_172))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (_50_198) -> begin
Some (Eff_name ((se, lid)))
end
| _50_201 -> begin
None
end)
end))
in (
# 203 "FStar.Parser.Env.fst"
let found_id = (match (lid.FStar_Ident.ns) with
| [] -> begin
(match ((try_lookup_id env lid.FStar_Ident.ident)) with
| Some (e) -> begin
Some (Term_name (e))
end
| None -> begin
(
# 208 "FStar.Parser.Env.fst"
let recname = (qualify env lid.FStar_Ident.ident)
in (FStar_Util.find_map env.recbindings (fun _50_210 -> (match (_50_210) with
| (id, l, dd) -> begin
if (id.FStar_Ident.idText = lid.FStar_Ident.ident.FStar_Ident.idText) then begin
(let _132_176 = (let _132_175 = (let _132_174 = (FStar_Ident.set_lid_range l (FStar_Ident.range_of_lid lid))
in (FStar_Syntax_Syntax.fvar _132_174 dd None))
in Term_name (_132_175))
in Some (_132_176))
end else begin
None
end
end))))
end)
end
| _50_212 -> begin
None
end)
in (match (found_id) with
| Some (_50_215) -> begin
found_id
end
| _50_218 -> begin
(resolve_in_open_namespaces env lid find_in_sig)
end))))

# 219 "FStar.Parser.Env.fst"
let try_lookup_effect_name' : Prims.bool  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident) Prims.option = (fun exclude_interf env lid -> (match ((try_lookup_name true exclude_interf env lid)) with
| Some (Eff_name (o, l)) -> begin
Some ((o, l))
end
| _50_228 -> begin
None
end))

# 223 "FStar.Parser.Env.fst"
let try_lookup_effect_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env l -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some (o, l) -> begin
Some (l)
end
| _50_236 -> begin
None
end))

# 227 "FStar.Parser.Env.fst"
let try_lookup_effect_defn : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl Prims.option = (fun env l -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some (FStar_Syntax_Syntax.Sig_new_effect (ne, _50_241), _50_245) -> begin
Some (ne)
end
| _50_249 -> begin
None
end))

# 231 "FStar.Parser.Env.fst"
let is_effect_name : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((try_lookup_effect_name env lid)) with
| None -> begin
false
end
| Some (_50_254) -> begin
true
end))

# 236 "FStar.Parser.Env.fst"
let lookup_letbinding_quals : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.qualifier Prims.list = (fun env lid -> (
# 237 "FStar.Parser.Env.fst"
let find_in_sig = (fun lid -> (match ((let _132_201 = (sigmap env)
in (FStar_Util.smap_try_find _132_201 lid.FStar_Ident.str))) with
| Some (FStar_Syntax_Syntax.Sig_declare_typ (lid, _50_262, _50_264, quals, _50_267), _50_271) -> begin
Some (quals)
end
| _50_275 -> begin
None
end))
in (match ((resolve_in_open_namespaces env lid find_in_sig)) with
| Some (quals) -> begin
quals
end
| _50_279 -> begin
[]
end)))

# 245 "FStar.Parser.Env.fst"
let try_lookup_module : env  ->  Prims.string Prims.list  ->  FStar_Syntax_Syntax.modul Prims.option = (fun env path -> (match ((FStar_List.tryFind (fun _50_284 -> (match (_50_284) with
| (mlid, modul) -> begin
((FStar_Ident.path_of_lid mlid) = path)
end)) env.modules)) with
| Some (_50_286, modul) -> begin
Some (modul)
end
| None -> begin
None
end))

# 250 "FStar.Parser.Env.fst"
let try_lookup_let : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env lid -> (
# 251 "FStar.Parser.Env.fst"
let find_in_sig = (fun lid -> (match ((let _132_213 = (sigmap env)
in (FStar_Util.smap_try_find _132_213 lid.FStar_Ident.str))) with
| Some (FStar_Syntax_Syntax.Sig_let ((_50_296, lbs), _50_300, _50_302, _50_304), _50_308) -> begin
(
# 254 "FStar.Parser.Env.fst"
let fv = (lb_fv lbs lid)
in (let _132_214 = (FStar_Syntax_Syntax.fvar lid fv.FStar_Syntax_Syntax.fv_delta fv.FStar_Syntax_Syntax.fv_qual)
in Some (_132_214)))
end
| _50_313 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))

# 259 "FStar.Parser.Env.fst"
let try_lookup_definition : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env lid -> (
# 260 "FStar.Parser.Env.fst"
let find_in_sig = (fun lid -> (match ((let _132_221 = (sigmap env)
in (FStar_Util.smap_try_find _132_221 lid.FStar_Ident.str))) with
| Some (FStar_Syntax_Syntax.Sig_let (lbs, _50_320, _50_322, _50_324), _50_328) -> begin
(FStar_Util.find_map (Prims.snd lbs) (fun lb -> (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv lid) -> begin
Some (lb.FStar_Syntax_Syntax.lbdef)
end
| _50_335 -> begin
None
end)))
end
| _50_337 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))

# 272 "FStar.Parser.Env.fst"
let try_lookup_lid' : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun any_val exclude_interf env lid -> (match ((try_lookup_name any_val exclude_interf env lid)) with
| Some (Term_name (e)) -> begin
Some (e)
end
| _50_346 -> begin
None
end))

# 276 "FStar.Parser.Env.fst"
let try_lookup_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env l -> (try_lookup_lid' env.iface false env l))

# 278 "FStar.Parser.Env.fst"
let try_lookup_datacon : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.fv Prims.option = (fun env lid -> (
# 279 "FStar.Parser.Env.fst"
let find_in_sig = (fun lid -> (match ((let _132_241 = (sigmap env)
in (FStar_Util.smap_try_find _132_241 lid.FStar_Ident.str))) with
| Some (FStar_Syntax_Syntax.Sig_declare_typ (_50_354, _50_356, _50_358, quals, _50_361), _50_365) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _50_5 -> (match (_50_5) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| _50_371 -> begin
false
end)))) then begin
(let _132_243 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant None)
in Some (_132_243))
end else begin
None
end
end
| Some (FStar_Syntax_Syntax.Sig_datacon (_50_373), _50_376) -> begin
(let _132_244 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in Some (_132_244))
end
| _50_380 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))

# 289 "FStar.Parser.Env.fst"
let find_all_datacons : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.list Prims.option = (fun env lid -> (
# 290 "FStar.Parser.Env.fst"
let find_in_sig = (fun lid -> (match ((let _132_251 = (sigmap env)
in (FStar_Util.smap_try_find _132_251 lid.FStar_Ident.str))) with
| Some (FStar_Syntax_Syntax.Sig_inductive_typ (_50_386, _50_388, _50_390, _50_392, _50_394, datas, _50_397, _50_399), _50_403) -> begin
Some (datas)
end
| _50_407 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))

# 297 "FStar.Parser.Env.fst"
let record_cache_aux : ((Prims.unit  ->  Prims.unit) * (Prims.unit  ->  Prims.unit) * (Prims.unit  ->  record_or_dc Prims.list) * (record_or_dc  ->  Prims.unit)) = (
# 298 "FStar.Parser.Env.fst"
let record_cache = (FStar_Util.mk_ref (([])::[]))
in (
# 299 "FStar.Parser.Env.fst"
let push = (fun _50_410 -> (match (()) with
| () -> begin
(let _132_265 = (let _132_264 = (let _132_262 = (FStar_ST.read record_cache)
in (FStar_List.hd _132_262))
in (let _132_263 = (FStar_ST.read record_cache)
in (_132_264)::_132_263))
in (FStar_ST.op_Colon_Equals record_cache _132_265))
end))
in (
# 301 "FStar.Parser.Env.fst"
let pop = (fun _50_412 -> (match (()) with
| () -> begin
(let _132_269 = (let _132_268 = (FStar_ST.read record_cache)
in (FStar_List.tl _132_268))
in (FStar_ST.op_Colon_Equals record_cache _132_269))
end))
in (
# 303 "FStar.Parser.Env.fst"
let peek = (fun _50_414 -> (match (()) with
| () -> begin
(let _132_272 = (FStar_ST.read record_cache)
in (FStar_List.hd _132_272))
end))
in (
# 304 "FStar.Parser.Env.fst"
let insert = (fun r -> (let _132_279 = (let _132_278 = (let _132_275 = (peek ())
in (r)::_132_275)
in (let _132_277 = (let _132_276 = (FStar_ST.read record_cache)
in (FStar_List.tl _132_276))
in (_132_278)::_132_277))
in (FStar_ST.op_Colon_Equals record_cache _132_279)))
in (push, pop, peek, insert))))))

# 307 "FStar.Parser.Env.fst"
let push_record_cache : Prims.unit  ->  Prims.unit = (
# 308 "FStar.Parser.Env.fst"
let _50_424 = record_cache_aux
in (match (_50_424) with
| (push, _50_419, _50_421, _50_423) -> begin
push
end))

# 311 "FStar.Parser.Env.fst"
let pop_record_cache : Prims.unit  ->  Prims.unit = (
# 312 "FStar.Parser.Env.fst"
let _50_432 = record_cache_aux
in (match (_50_432) with
| (_50_426, pop, _50_429, _50_431) -> begin
pop
end))

# 315 "FStar.Parser.Env.fst"
let peek_record_cache : Prims.unit  ->  record_or_dc Prims.list = (
# 316 "FStar.Parser.Env.fst"
let _50_440 = record_cache_aux
in (match (_50_440) with
| (_50_434, _50_436, peek, _50_439) -> begin
peek
end))

# 319 "FStar.Parser.Env.fst"
let insert_record_cache : record_or_dc  ->  Prims.unit = (
# 320 "FStar.Parser.Env.fst"
let _50_448 = record_cache_aux
in (match (_50_448) with
| (_50_442, _50_444, _50_446, insert) -> begin
insert
end))

# 323 "FStar.Parser.Env.fst"
let extract_record : env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun e _50_9 -> (match (_50_9) with
| FStar_Syntax_Syntax.Sig_bundle (sigs, _50_453, _50_455, _50_457) -> begin
(
# 325 "FStar.Parser.Env.fst"
let is_rec = (FStar_Util.for_some (fun _50_6 -> (match (_50_6) with
| (FStar_Syntax_Syntax.RecordType (_)) | (FStar_Syntax_Syntax.RecordConstructor (_)) -> begin
true
end
| _50_468 -> begin
false
end)))
in (
# 330 "FStar.Parser.Env.fst"
let find_dc = (fun dc -> (FStar_All.pipe_right sigs (FStar_Util.find_opt (fun _50_7 -> (match (_50_7) with
| FStar_Syntax_Syntax.Sig_datacon (lid, _50_475, _50_477, _50_479, _50_481, _50_483, _50_485, _50_487) -> begin
(FStar_Ident.lid_equals dc lid)
end
| _50_491 -> begin
false
end)))))
in (FStar_All.pipe_right sigs (FStar_List.iter (fun _50_8 -> (match (_50_8) with
| FStar_Syntax_Syntax.Sig_inductive_typ (typename, univs, parms, _50_497, _50_499, dc::[], tags, _50_504) -> begin
(match ((let _132_350 = (find_dc dc)
in (FStar_All.pipe_left FStar_Util.must _132_350))) with
| FStar_Syntax_Syntax.Sig_datacon (constrname, _50_509, t, _50_512, _50_514, _50_516, _50_518, _50_520) -> begin
(
# 339 "FStar.Parser.Env.fst"
let _50_526 = (FStar_Syntax_Util.arrow_formals t)
in (match (_50_526) with
| (formals, _50_525) -> begin
(
# 340 "FStar.Parser.Env.fst"
let is_rec = (is_rec tags)
in (
# 341 "FStar.Parser.Env.fst"
let fields = (FStar_All.pipe_right formals (FStar_List.collect (fun _50_530 -> (match (_50_530) with
| (x, q) -> begin
if ((FStar_Syntax_Syntax.is_null_bv x) || (is_rec && (FStar_Syntax_Syntax.is_implicit q))) then begin
[]
end else begin
(let _132_354 = (let _132_353 = (let _132_352 = if is_rec then begin
(FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname)
end else begin
x.FStar_Syntax_Syntax.ppname
end
in (qual constrname _132_352))
in (_132_353, x.FStar_Syntax_Syntax.sort))
in (_132_354)::[])
end
end))))
in (
# 346 "FStar.Parser.Env.fst"
let record = {typename = typename; constrname = constrname; parms = parms; fields = fields; is_record = is_rec}
in (insert_record_cache record))))
end))
end
| _50_534 -> begin
()
end)
end
| _50_536 -> begin
()
end))))))
end
| _50_538 -> begin
()
end))

# 358 "FStar.Parser.Env.fst"
let try_lookup_record_or_dc_by_field_name : env  ->  FStar_Ident.lident  ->  (record_or_dc * FStar_Ident.lident) Prims.option = (fun env fieldname -> (
# 359 "FStar.Parser.Env.fst"
let maybe_add_constrname = (fun ns c -> (
# 360 "FStar.Parser.Env.fst"
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
(let _132_365 = (aux tl)
in (hd)::_132_365)
end))
in (aux ns)))
in (
# 365 "FStar.Parser.Env.fst"
let find_in_cache = (fun fieldname -> (
# 367 "FStar.Parser.Env.fst"
let _50_556 = (fieldname.FStar_Ident.ns, fieldname.FStar_Ident.ident)
in (match (_50_556) with
| (ns, fieldname) -> begin
(let _132_370 = (peek_record_cache ())
in (FStar_Util.find_map _132_370 (fun record -> (
# 369 "FStar.Parser.Env.fst"
let constrname = record.constrname.FStar_Ident.ident
in (
# 370 "FStar.Parser.Env.fst"
let ns = (maybe_add_constrname ns constrname)
in (
# 371 "FStar.Parser.Env.fst"
let fname = (FStar_Ident.lid_of_ids (FStar_List.append ns ((fieldname)::[])))
in (FStar_Util.find_map record.fields (fun _50_564 -> (match (_50_564) with
| (f, _50_563) -> begin
if (FStar_Ident.lid_equals fname f) then begin
Some ((record, fname))
end else begin
None
end
end)))))))))
end)))
in (resolve_in_open_namespaces env fieldname find_in_cache))))

# 378 "FStar.Parser.Env.fst"
let try_lookup_record_by_field_name : env  ->  FStar_Ident.lident  ->  (record_or_dc * FStar_Ident.lident) Prims.option = (fun env fieldname -> (match ((try_lookup_record_or_dc_by_field_name env fieldname)) with
| Some (r, f) when r.is_record -> begin
Some ((r, f))
end
| _50_572 -> begin
None
end))

# 383 "FStar.Parser.Env.fst"
let try_lookup_projector_by_field_name : env  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * Prims.bool) Prims.option = (fun env fieldname -> (match ((try_lookup_record_or_dc_by_field_name env fieldname)) with
| Some (r, f) -> begin
Some ((f, r.is_record))
end
| _50_580 -> begin
None
end))

# 388 "FStar.Parser.Env.fst"
let qualify_field_to_record : env  ->  record_or_dc  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env recd f -> (
# 389 "FStar.Parser.Env.fst"
let qualify = (fun fieldname -> (
# 390 "FStar.Parser.Env.fst"
let _50_588 = (fieldname.FStar_Ident.ns, fieldname.FStar_Ident.ident)
in (match (_50_588) with
| (ns, fieldname) -> begin
(
# 391 "FStar.Parser.Env.fst"
let constrname = recd.constrname.FStar_Ident.ident
in (
# 392 "FStar.Parser.Env.fst"
let fname = (FStar_Ident.lid_of_ids (FStar_List.append (FStar_List.append ns ((constrname)::[])) ((fieldname)::[])))
in (FStar_Util.find_map recd.fields (fun _50_594 -> (match (_50_594) with
| (f, _50_593) -> begin
if (FStar_Ident.lid_equals fname f) then begin
Some (fname)
end else begin
None
end
end)))))
end)))
in (resolve_in_open_namespaces env f qualify)))

# 399 "FStar.Parser.Env.fst"
let unique : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  Prims.bool = (fun any_val exclude_if env lid -> (
# 400 "FStar.Parser.Env.fst"
let this_env = (
# 400 "FStar.Parser.Env.fst"
let _50_599 = env
in {curmodule = _50_599.curmodule; modules = _50_599.modules; open_namespaces = []; sigaccum = _50_599.sigaccum; localbindings = _50_599.localbindings; recbindings = _50_599.recbindings; sigmap = _50_599.sigmap; default_result_effect = _50_599.default_result_effect; iface = _50_599.iface; admitted_iface = _50_599.admitted_iface; expect_typ = _50_599.expect_typ})
in (match ((try_lookup_lid' any_val exclude_if env lid)) with
| None -> begin
true
end
| Some (_50_604) -> begin
false
end)))

# 405 "FStar.Parser.Env.fst"
let push_bv : env  ->  FStar_Ident.ident  ->  (env * FStar_Syntax_Syntax.bv) = (fun env x -> (
# 406 "FStar.Parser.Env.fst"
let bv = (FStar_Syntax_Syntax.gen_bv x.FStar_Ident.idText (Some (x.FStar_Ident.idRange)) FStar_Syntax_Syntax.tun)
in ((
# 407 "FStar.Parser.Env.fst"
let _50_609 = env
in {curmodule = _50_609.curmodule; modules = _50_609.modules; open_namespaces = _50_609.open_namespaces; sigaccum = _50_609.sigaccum; localbindings = ((x, bv))::env.localbindings; recbindings = _50_609.recbindings; sigmap = _50_609.sigmap; default_result_effect = _50_609.default_result_effect; iface = _50_609.iface; admitted_iface = _50_609.admitted_iface; expect_typ = _50_609.expect_typ}), bv)))

# 409 "FStar.Parser.Env.fst"
let push_top_level_rec_binding : env  ->  FStar_Ident.ident  ->  FStar_Syntax_Syntax.delta_depth  ->  env = (fun env x dd -> (
# 410 "FStar.Parser.Env.fst"
let l = (qualify env x)
in if (unique false true env l) then begin
(
# 412 "FStar.Parser.Env.fst"
let _50_615 = env
in {curmodule = _50_615.curmodule; modules = _50_615.modules; open_namespaces = _50_615.open_namespaces; sigaccum = _50_615.sigaccum; localbindings = _50_615.localbindings; recbindings = ((x, l, dd))::env.recbindings; sigmap = _50_615.sigmap; default_result_effect = _50_615.default_result_effect; iface = _50_615.iface; admitted_iface = _50_615.admitted_iface; expect_typ = _50_615.expect_typ})
end else begin
(Prims.raise (FStar_Syntax_Syntax.Error (((Prims.strcat "Duplicate top-level names " l.FStar_Ident.str), (FStar_Ident.range_of_lid l)))))
end))

# 415 "FStar.Parser.Env.fst"
let push_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env s -> (
# 416 "FStar.Parser.Env.fst"
let err = (fun l -> (
# 417 "FStar.Parser.Env.fst"
let sopt = (let _132_412 = (sigmap env)
in (FStar_Util.smap_try_find _132_412 l.FStar_Ident.str))
in (
# 418 "FStar.Parser.Env.fst"
let r = (match (sopt) with
| Some (se, _50_624) -> begin
(match ((let _132_413 = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_Util.find_opt (FStar_Ident.lid_equals l) _132_413))) with
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
in (let _132_416 = (let _132_415 = (let _132_414 = (FStar_Util.format2 "Duplicate top-level names [%s]; previously declared at %s" (FStar_Ident.text_of_lid l) r)
in (_132_414, (FStar_Ident.range_of_lid l)))
in FStar_Syntax_Syntax.Error (_132_415))
in (Prims.raise _132_416)))))
in (
# 426 "FStar.Parser.Env.fst"
let env = (
# 427 "FStar.Parser.Env.fst"
let _50_642 = (match (s) with
| FStar_Syntax_Syntax.Sig_let (_50_633) -> begin
(false, true)
end
| FStar_Syntax_Syntax.Sig_bundle (_50_636) -> begin
(true, true)
end
| _50_639 -> begin
(false, false)
end)
in (match (_50_642) with
| (any_val, exclude_if) -> begin
(
# 431 "FStar.Parser.Env.fst"
let lids = (FStar_Syntax_Util.lids_of_sigelt s)
in (match ((FStar_Util.find_map lids (fun l -> if (not ((unique any_val exclude_if env l))) then begin
Some (l)
end else begin
None
end))) with
| None -> begin
(
# 433 "FStar.Parser.Env.fst"
let _50_646 = (extract_record env s)
in (
# 433 "FStar.Parser.Env.fst"
let _50_648 = env
in {curmodule = _50_648.curmodule; modules = _50_648.modules; open_namespaces = _50_648.open_namespaces; sigaccum = (s)::env.sigaccum; localbindings = _50_648.localbindings; recbindings = _50_648.recbindings; sigmap = _50_648.sigmap; default_result_effect = _50_648.default_result_effect; iface = _50_648.iface; admitted_iface = _50_648.admitted_iface; expect_typ = _50_648.expect_typ}))
end
| Some (l) -> begin
(err l)
end))
end))
in (
# 436 "FStar.Parser.Env.fst"
let _50_667 = (match (s) with
| FStar_Syntax_Syntax.Sig_bundle (ses, _50_655, _50_657, _50_659) -> begin
(let _132_420 = (FStar_List.map (fun se -> (let _132_419 = (FStar_Syntax_Util.lids_of_sigelt se)
in (_132_419, se))) ses)
in (env, _132_420))
end
| _50_664 -> begin
(let _132_423 = (let _132_422 = (let _132_421 = (FStar_Syntax_Util.lids_of_sigelt s)
in (_132_421, s))
in (_132_422)::[])
in (env, _132_423))
end)
in (match (_50_667) with
| (env, lss) -> begin
(
# 439 "FStar.Parser.Env.fst"
let _50_672 = (FStar_All.pipe_right lss (FStar_List.iter (fun _50_670 -> (match (_50_670) with
| (lids, se) -> begin
(FStar_All.pipe_right lids (FStar_List.iter (fun lid -> (let _132_426 = (sigmap env)
in (FStar_Util.smap_add _132_426 lid.FStar_Ident.str (se, (env.iface && (not (env.admitted_iface)))))))))
end))))
in env)
end)))))

# 444 "FStar.Parser.Env.fst"
let push_namespace : env  ->  FStar_Ident.lident  ->  env = (fun env lid -> (
# 445 "FStar.Parser.Env.fst"
let _50_676 = env
in {curmodule = _50_676.curmodule; modules = _50_676.modules; open_namespaces = (lid)::env.open_namespaces; sigaccum = _50_676.sigaccum; localbindings = _50_676.localbindings; recbindings = _50_676.recbindings; sigmap = _50_676.sigmap; default_result_effect = _50_676.default_result_effect; iface = _50_676.iface; admitted_iface = _50_676.admitted_iface; expect_typ = _50_676.expect_typ}))

# 447 "FStar.Parser.Env.fst"
let check_admits : env  ->  Prims.unit = (fun env -> (FStar_All.pipe_right env.sigaccum (FStar_List.iter (fun se -> (match (se) with
| FStar_Syntax_Syntax.Sig_declare_typ (l, u, t, quals, r) -> begin
(match ((try_lookup_lid env l)) with
| None -> begin
(
# 452 "FStar.Parser.Env.fst"
let _50_688 = (let _132_436 = (let _132_435 = (FStar_Range.string_of_range (FStar_Ident.range_of_lid l))
in (let _132_434 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format2 "%s: Warning: Admitting %s without a definition\n" _132_435 _132_434)))
in (FStar_Util.print_string _132_436))
in (let _132_437 = (sigmap env)
in (FStar_Util.smap_add _132_437 l.FStar_Ident.str (FStar_Syntax_Syntax.Sig_declare_typ ((l, u, t, (FStar_Syntax_Syntax.Assumption)::quals, r)), false))))
end
| Some (_50_691) -> begin
()
end)
end
| _50_694 -> begin
()
end)))))

# 458 "FStar.Parser.Env.fst"
let finish : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env modul -> (
# 459 "FStar.Parser.Env.fst"
let _50_754 = (FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations (FStar_List.iter (fun _50_11 -> (match (_50_11) with
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _50_701, _50_703) -> begin
if ((FStar_List.contains FStar_Syntax_Syntax.Private quals) || (FStar_List.contains FStar_Syntax_Syntax.Abstract quals)) then begin
(FStar_All.pipe_right ses (FStar_List.iter (fun _50_10 -> (match (_50_10) with
| FStar_Syntax_Syntax.Sig_datacon (lid, _50_709, _50_711, _50_713, _50_715, _50_717, _50_719, _50_721) -> begin
(let _132_444 = (sigmap env)
in (FStar_Util.smap_remove _132_444 lid.FStar_Ident.str))
end
| _50_725 -> begin
()
end))))
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _50_728, _50_730, quals, _50_733) -> begin
if (FStar_List.contains FStar_Syntax_Syntax.Private quals) then begin
(let _132_445 = (sigmap env)
in (FStar_Util.smap_remove _132_445 lid.FStar_Ident.str))
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_let ((_50_737, lbs), r, _50_742, quals) -> begin
(
# 472 "FStar.Parser.Env.fst"
let _50_747 = if ((FStar_List.contains FStar_Syntax_Syntax.Private quals) || (FStar_List.contains FStar_Syntax_Syntax.Abstract quals)) then begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (let _132_451 = (sigmap env)
in (let _132_450 = (let _132_449 = (let _132_448 = (let _132_447 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _132_447.FStar_Syntax_Syntax.fv_name)
in _132_448.FStar_Syntax_Syntax.v)
in _132_449.FStar_Ident.str)
in (FStar_Util.smap_remove _132_451 _132_450))))))
end else begin
()
end
in if (FStar_List.contains FStar_Syntax_Syntax.Abstract quals) then begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (
# 479 "FStar.Parser.Env.fst"
let lid = (let _132_454 = (let _132_453 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _132_453.FStar_Syntax_Syntax.fv_name)
in _132_454.FStar_Syntax_Syntax.v)
in (
# 480 "FStar.Parser.Env.fst"
let decl = FStar_Syntax_Syntax.Sig_declare_typ ((lid, lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp, (FStar_Syntax_Syntax.Assumption)::quals, r))
in (let _132_455 = (sigmap env)
in (FStar_Util.smap_add _132_455 lid.FStar_Ident.str (decl, false))))))))
end else begin
()
end)
end
| _50_753 -> begin
()
end))))
in (
# 484 "FStar.Parser.Env.fst"
let _50_756 = env
in {curmodule = None; modules = ((modul.FStar_Syntax_Syntax.name, modul))::env.modules; open_namespaces = []; sigaccum = []; localbindings = []; recbindings = []; sigmap = _50_756.sigmap; default_result_effect = _50_756.default_result_effect; iface = _50_756.iface; admitted_iface = _50_756.admitted_iface; expect_typ = _50_756.expect_typ})))

# 492 "FStar.Parser.Env.fst"
let push : env  ->  env = (fun env -> (
# 493 "FStar.Parser.Env.fst"
let _50_759 = (push_record_cache ())
in (
# 494 "FStar.Parser.Env.fst"
let _50_761 = env
in (let _132_460 = (let _132_459 = (let _132_458 = (sigmap env)
in (FStar_Util.smap_copy _132_458))
in (_132_459)::env.sigmap)
in {curmodule = _50_761.curmodule; modules = _50_761.modules; open_namespaces = _50_761.open_namespaces; sigaccum = _50_761.sigaccum; localbindings = _50_761.localbindings; recbindings = _50_761.recbindings; sigmap = _132_460; default_result_effect = _50_761.default_result_effect; iface = _50_761.iface; admitted_iface = _50_761.admitted_iface; expect_typ = _50_761.expect_typ}))))

# 497 "FStar.Parser.Env.fst"
let mark : env  ->  env = (fun env -> (push env))

# 498 "FStar.Parser.Env.fst"
let reset_mark : env  ->  env = (fun env -> (
# 498 "FStar.Parser.Env.fst"
let _50_765 = env
in (let _132_465 = (FStar_List.tl env.sigmap)
in {curmodule = _50_765.curmodule; modules = _50_765.modules; open_namespaces = _50_765.open_namespaces; sigaccum = _50_765.sigaccum; localbindings = _50_765.localbindings; recbindings = _50_765.recbindings; sigmap = _132_465; default_result_effect = _50_765.default_result_effect; iface = _50_765.iface; admitted_iface = _50_765.admitted_iface; expect_typ = _50_765.expect_typ})))

# 499 "FStar.Parser.Env.fst"
let commit_mark : env  ->  env = (fun env -> (match (env.sigmap) with
| hd::_50_770::tl -> begin
(
# 500 "FStar.Parser.Env.fst"
let _50_774 = env
in {curmodule = _50_774.curmodule; modules = _50_774.modules; open_namespaces = _50_774.open_namespaces; sigaccum = _50_774.sigaccum; localbindings = _50_774.localbindings; recbindings = _50_774.recbindings; sigmap = (hd)::tl; default_result_effect = _50_774.default_result_effect; iface = _50_774.iface; admitted_iface = _50_774.admitted_iface; expect_typ = _50_774.expect_typ})
end
| _50_777 -> begin
(FStar_All.failwith "Impossible")
end))

# 502 "FStar.Parser.Env.fst"
let pop : env  ->  env = (fun env -> (match (env.sigmap) with
| _50_781::maps -> begin
(
# 504 "FStar.Parser.Env.fst"
let _50_783 = (pop_record_cache ())
in (
# 505 "FStar.Parser.Env.fst"
let _50_785 = env
in {curmodule = _50_785.curmodule; modules = _50_785.modules; open_namespaces = _50_785.open_namespaces; sigaccum = _50_785.sigaccum; localbindings = _50_785.localbindings; recbindings = _50_785.recbindings; sigmap = maps; default_result_effect = _50_785.default_result_effect; iface = _50_785.iface; admitted_iface = _50_785.admitted_iface; expect_typ = _50_785.expect_typ}))
end
| _50_788 -> begin
(FStar_All.failwith "No more modules to pop")
end))

# 509 "FStar.Parser.Env.fst"
let export_interface : FStar_Ident.lident  ->  env  ->  env = (fun m env -> (
# 511 "FStar.Parser.Env.fst"
let sigelt_in_m = (fun se -> (match ((FStar_Syntax_Util.lids_of_sigelt se)) with
| l::_50_794 -> begin
(l.FStar_Ident.nsstr = m.FStar_Ident.str)
end
| _50_798 -> begin
false
end))
in (
# 515 "FStar.Parser.Env.fst"
let sm = (sigmap env)
in (
# 516 "FStar.Parser.Env.fst"
let env = (pop env)
in (
# 517 "FStar.Parser.Env.fst"
let keys = (FStar_Util.smap_keys sm)
in (
# 518 "FStar.Parser.Env.fst"
let sm' = (sigmap env)
in (
# 519 "FStar.Parser.Env.fst"
let _50_822 = (FStar_All.pipe_right keys (FStar_List.iter (fun k -> (match ((FStar_Util.smap_try_find sm' k)) with
| Some (se, true) when (sigelt_in_m se) -> begin
(
# 522 "FStar.Parser.Env.fst"
let _50_808 = (FStar_Util.smap_remove sm' k)
in (
# 524 "FStar.Parser.Env.fst"
let se = (match (se) with
| FStar_Syntax_Syntax.Sig_declare_typ (l, u, t, q, r) -> begin
FStar_Syntax_Syntax.Sig_declare_typ ((l, u, t, (FStar_Syntax_Syntax.Assumption)::q, r))
end
| _50_818 -> begin
se
end)
in (FStar_Util.smap_add sm' k (se, false))))
end
| _50_821 -> begin
()
end))))
in env)))))))

# 531 "FStar.Parser.Env.fst"
let finish_module_or_interface : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env modul -> (
# 532 "FStar.Parser.Env.fst"
let _50_826 = if (not (modul.FStar_Syntax_Syntax.is_interface)) then begin
(check_admits env)
end else begin
()
end
in (finish env modul)))

# 536 "FStar.Parser.Env.fst"
let prepare_module_or_interface : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  (env * Prims.bool) = (fun intf admitted env mname -> (
# 537 "FStar.Parser.Env.fst"
let prep = (fun env -> (
# 538 "FStar.Parser.Env.fst"
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
# 542 "FStar.Parser.Env.fst"
let _50_835 = env
in {curmodule = Some (mname); modules = _50_835.modules; open_namespaces = open_ns; sigaccum = _50_835.sigaccum; localbindings = _50_835.localbindings; recbindings = _50_835.recbindings; sigmap = env.sigmap; default_result_effect = _50_835.default_result_effect; iface = intf; admitted_iface = admitted; expect_typ = _50_835.expect_typ})))
in (match ((FStar_All.pipe_right env.modules (FStar_Util.find_opt (fun _50_840 -> (match (_50_840) with
| (l, _50_839) -> begin
(FStar_Ident.lid_equals l mname)
end))))) with
| None -> begin
((prep env), false)
end
| Some (_50_843, m) -> begin
(
# 547 "FStar.Parser.Env.fst"
let _50_847 = if ((not (m.FStar_Syntax_Syntax.is_interface)) || intf) then begin
(let _132_494 = (let _132_493 = (let _132_492 = (FStar_Util.format1 "Duplicate module or interface name: %s" mname.FStar_Ident.str)
in (_132_492, (FStar_Ident.range_of_lid mname)))
in FStar_Syntax_Syntax.Error (_132_493))
in (Prims.raise _132_494))
end else begin
()
end
in (let _132_496 = (let _132_495 = (push env)
in (prep _132_495))
in (_132_496, true)))
end)))

# 552 "FStar.Parser.Env.fst"
let enter_monad_scope : env  ->  FStar_Ident.ident  ->  env = (fun env mname -> (
# 553 "FStar.Parser.Env.fst"
let curmod = (current_module env)
in (
# 554 "FStar.Parser.Env.fst"
let mscope = (FStar_Ident.lid_of_ids (FStar_List.append curmod.FStar_Ident.ns ((curmod.FStar_Ident.ident)::(mname)::[])))
in (
# 555 "FStar.Parser.Env.fst"
let _50_853 = env
in {curmodule = Some (mscope); modules = _50_853.modules; open_namespaces = (curmod)::env.open_namespaces; sigaccum = _50_853.sigaccum; localbindings = _50_853.localbindings; recbindings = _50_853.recbindings; sigmap = _50_853.sigmap; default_result_effect = _50_853.default_result_effect; iface = _50_853.iface; admitted_iface = _50_853.admitted_iface; expect_typ = _50_853.expect_typ}))))

# 559 "FStar.Parser.Env.fst"
let exit_monad_scope : env  ->  env  ->  env = (fun env0 env -> (
# 560 "FStar.Parser.Env.fst"
let _50_857 = env
in {curmodule = env0.curmodule; modules = _50_857.modules; open_namespaces = env0.open_namespaces; sigaccum = _50_857.sigaccum; localbindings = _50_857.localbindings; recbindings = _50_857.recbindings; sigmap = _50_857.sigmap; default_result_effect = _50_857.default_result_effect; iface = _50_857.iface; admitted_iface = _50_857.admitted_iface; expect_typ = _50_857.expect_typ}))

# 564 "FStar.Parser.Env.fst"
let fail_or = (fun lookup lid -> (match ((lookup lid)) with
| None -> begin
(let _132_512 = (let _132_511 = (let _132_510 = (FStar_Util.format1 "Identifier not found: [%s]" (FStar_Ident.text_of_lid lid))
in (_132_510, (FStar_Ident.range_of_lid lid)))
in FStar_Syntax_Syntax.Error (_132_511))
in (Prims.raise _132_512))
end
| Some (r) -> begin
r
end))

# 569 "FStar.Parser.Env.fst"
let fail_or2 = (fun lookup id -> (match ((lookup id)) with
| None -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (((Prims.strcat (Prims.strcat "Identifier not found [" id.FStar_Ident.idText) "]"), id.FStar_Ident.idRange))))
end
| Some (r) -> begin
r
end))




