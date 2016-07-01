
open Prims

type env =
{curmodule : FStar_Ident.lident Prims.option; modules : (FStar_Ident.lident * FStar_Syntax_Syntax.modul) Prims.list; open_namespaces : FStar_Ident.lident Prims.list; modul_abbrevs : (FStar_Ident.ident * FStar_Ident.lident) Prims.list; sigaccum : FStar_Syntax_Syntax.sigelts; localbindings : (FStar_Ident.ident * FStar_Syntax_Syntax.bv * Prims.bool) Prims.list; recbindings : (FStar_Ident.ident * FStar_Ident.lid * FStar_Syntax_Syntax.delta_depth) Prims.list; sigmap : (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap; default_result_effect : FStar_Ident.lident; iface : Prims.bool; admitted_iface : Prims.bool; expect_typ : Prims.bool}


let is_Mkenv : env  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv"))))


type foundname =
| Term_name of (FStar_Syntax_Syntax.typ * Prims.bool)
| Eff_name of (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident)


let is_Term_name = (fun _discr_ -> (match (_discr_) with
| Term_name (_) -> begin
true
end
| _ -> begin
false
end))


let is_Eff_name = (fun _discr_ -> (match (_discr_) with
| Eff_name (_) -> begin
true
end
| _ -> begin
false
end))


let ___Term_name____0 = (fun projectee -> (match (projectee) with
| Term_name (_61_28) -> begin
_61_28
end))


let ___Eff_name____0 = (fun projectee -> (match (projectee) with
| Eff_name (_61_31) -> begin
_61_31
end))


type record_or_dc =
{typename : FStar_Ident.lident; constrname : FStar_Ident.lident; parms : FStar_Syntax_Syntax.binders; fields : (FStar_Syntax_Syntax.fieldname * FStar_Syntax_Syntax.typ) Prims.list; is_record : Prims.bool}


let is_Mkrecord_or_dc : record_or_dc  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkrecord_or_dc"))))


let open_modules : env  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.modul) Prims.list = (fun e -> e.modules)


let current_module : env  ->  FStar_Ident.lident = (fun env -> (match (env.curmodule) with
| None -> begin
(FStar_All.failwith "Unset current module")
end
| Some (m) -> begin
m
end))


let qual : FStar_Ident.lident  ->  FStar_Ident.ident  ->  FStar_Ident.lident = (fun lid id -> (let _152_90 = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns ((lid.FStar_Ident.ident)::(id)::[])))
in (FStar_Ident.set_lid_range _152_90 id.FStar_Ident.idRange)))


let qualify : env  ->  FStar_Ident.ident  ->  FStar_Ident.lident = (fun env id -> (let _152_95 = (current_module env)
in (qual _152_95 id)))


let qualify_lid : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (

let cur = (current_module env)
in (let _152_100 = (FStar_Ident.lid_of_ids (FStar_List.append (FStar_List.append (FStar_List.append cur.FStar_Ident.ns ((cur.FStar_Ident.ident)::[])) lid.FStar_Ident.ns) ((lid.FStar_Ident.ident)::[])))
in (FStar_Ident.set_lid_range _152_100 (FStar_Ident.range_of_lid lid)))))


let new_sigmap = (fun _61_52 -> (match (()) with
| () -> begin
(FStar_Util.smap_create 100)
end))


let empty_env : Prims.unit  ->  env = (fun _61_53 -> (match (()) with
| () -> begin
(let _152_104 = (new_sigmap ())
in {curmodule = None; modules = []; open_namespaces = []; modul_abbrevs = []; sigaccum = []; localbindings = []; recbindings = []; sigmap = _152_104; default_result_effect = FStar_Syntax_Const.effect_ML_lid; iface = false; admitted_iface = false; expect_typ = false})
end))


let sigmap : env  ->  (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap = (fun env -> env.sigmap)


let default_total : env  ->  env = (fun env -> (

let _61_56 = env
in {curmodule = _61_56.curmodule; modules = _61_56.modules; open_namespaces = _61_56.open_namespaces; modul_abbrevs = _61_56.modul_abbrevs; sigaccum = _61_56.sigaccum; localbindings = _61_56.localbindings; recbindings = _61_56.recbindings; sigmap = _61_56.sigmap; default_result_effect = FStar_Syntax_Const.effect_Tot_lid; iface = _61_56.iface; admitted_iface = _61_56.admitted_iface; expect_typ = _61_56.expect_typ}))


let default_ml : env  ->  env = (fun env -> (

let _61_59 = env
in {curmodule = _61_59.curmodule; modules = _61_59.modules; open_namespaces = _61_59.open_namespaces; modul_abbrevs = _61_59.modul_abbrevs; sigaccum = _61_59.sigaccum; localbindings = _61_59.localbindings; recbindings = _61_59.recbindings; sigmap = _61_59.sigmap; default_result_effect = FStar_Syntax_Const.effect_ML_lid; iface = _61_59.iface; admitted_iface = _61_59.admitted_iface; expect_typ = _61_59.expect_typ}))


let set_bv_range : FStar_Syntax_Syntax.bv  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.bv = (fun bv r -> (

let id = (

let _61_63 = bv.FStar_Syntax_Syntax.ppname
in {FStar_Ident.idText = _61_63.FStar_Ident.idText; FStar_Ident.idRange = r})
in (

let _61_66 = bv
in {FStar_Syntax_Syntax.ppname = id; FStar_Syntax_Syntax.index = _61_66.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _61_66.FStar_Syntax_Syntax.sort})))


let bv_to_name : FStar_Syntax_Syntax.bv  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.term = (fun bv r -> (FStar_Syntax_Syntax.bv_to_name (set_bv_range bv r)))


let unmangleMap : (Prims.string * Prims.string * FStar_Syntax_Syntax.delta_depth * FStar_Syntax_Syntax.fv_qual Prims.option) Prims.list = (("op_ColonColon", "Cons", FStar_Syntax_Syntax.Delta_constant, Some (FStar_Syntax_Syntax.Data_ctor)))::(("not", "op_Negation", FStar_Syntax_Syntax.Delta_equational, None))::[]


let unmangleOpName : FStar_Ident.ident  ->  FStar_Syntax_Syntax.term Prims.option = (fun id -> (FStar_Util.find_map unmangleMap (fun _61_75 -> (match (_61_75) with
| (x, y, dd, dq) -> begin
if (id.FStar_Ident.idText = x) then begin
(let _152_123 = (let _152_122 = (FStar_Ident.lid_of_path (("Prims")::(y)::[]) id.FStar_Ident.idRange)
in (FStar_Syntax_Syntax.fvar _152_122 dd dq))
in Some (_152_123))
end else begin
None
end
end))))


let try_lookup_id : env  ->  FStar_Ident.ident  ->  (FStar_Syntax_Syntax.term * Prims.bool) Prims.option = (fun env id -> (match ((unmangleOpName id)) with
| Some (f) -> begin
Some ((f, false))
end
| _61_81 -> begin
(FStar_Util.find_map env.localbindings (fun _61_1 -> (match (_61_1) with
| (id', x, mut) when (id'.FStar_Ident.idText = id.FStar_Ident.idText) -> begin
(let _152_130 = (let _152_129 = (bv_to_name x id.FStar_Ident.idRange)
in (_152_129, mut))
in Some (_152_130))
end
| _61_88 -> begin
None
end)))
end))


let resolve_in_open_namespaces' = (fun env lid finder -> (

let aux = (fun namespaces -> (match ((finder lid)) with
| Some (r) -> begin
Some (r)
end
| _61_98 -> begin
(

let ids = (FStar_Ident.ids_of_lid lid)
in (FStar_Util.find_map namespaces (fun ns -> (

let full_name = (FStar_Ident.lid_of_ids (FStar_List.append (FStar_Ident.ids_of_lid ns) ids))
in (finder full_name)))))
end))
in (let _152_141 = (let _152_140 = (current_module env)
in (_152_140)::env.open_namespaces)
in (aux _152_141))))


let expand_module_abbrevs : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (match (lid.FStar_Ident.ns) with
| (id)::rest -> begin
(match ((FStar_All.pipe_right env.modul_abbrevs (FStar_List.tryFind (fun _61_110 -> (match (_61_110) with
| (id', _61_109) -> begin
(id.FStar_Ident.idText = id'.FStar_Ident.idText)
end))))) with
| None -> begin
lid
end
| Some (_61_113, lid') -> begin
(FStar_Ident.lid_of_ids (FStar_List.append (FStar_List.append (FStar_Ident.ids_of_lid lid') rest) ((lid.FStar_Ident.ident)::[])))
end)
end
| _61_118 -> begin
lid
end))


let resolve_in_open_namespaces = (fun env lid finder -> (let _152_153 = (expand_module_abbrevs env lid)
in (resolve_in_open_namespaces' env _152_153 finder)))


let fv_qual_of_se : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.fv_qual Prims.option = (fun _61_3 -> (match (_61_3) with
| FStar_Syntax_Syntax.Sig_datacon (_61_125, _61_127, _61_129, l, _61_132, quals, _61_135, _61_137) -> begin
(

let qopt = (FStar_Util.find_map quals (fun _61_2 -> (match (_61_2) with
| FStar_Syntax_Syntax.RecordConstructor (fs) -> begin
Some (FStar_Syntax_Syntax.Record_ctor ((l, fs)))
end
| _61_144 -> begin
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
| FStar_Syntax_Syntax.Sig_declare_typ (_61_149, _61_151, _61_153, quals, _61_156) -> begin
None
end
| _61_160 -> begin
None
end))


let lb_fv : FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.fv = (fun lbs lid -> (let _152_162 = (FStar_Util.find_map lbs (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in if (FStar_Syntax_Syntax.fv_eq_lid fv lid) then begin
Some (fv)
end else begin
None
end)))
in (FStar_All.pipe_right _152_162 FStar_Util.must)))


let try_lookup_name : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  foundname Prims.option = (fun any_val exclude_interf env lid -> (

let occurrence_range = (FStar_Ident.range_of_lid lid)
in (

let find_in_sig = (fun lid -> (match ((FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str)) with
| Some (_61_173, true) when exclude_interf -> begin
None
end
| None -> begin
None
end
| Some (se, _61_180) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_61_184) -> begin
(let _152_175 = (let _152_174 = (let _152_173 = (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.Delta_constant None)
in (_152_173, false))
in Term_name (_152_174))
in Some (_152_175))
end
| FStar_Syntax_Syntax.Sig_datacon (_61_187) -> begin
(let _152_179 = (let _152_178 = (let _152_177 = (let _152_176 = (fv_qual_of_se se)
in (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.Delta_constant _152_176))
in (_152_177, false))
in Term_name (_152_178))
in Some (_152_179))
end
| FStar_Syntax_Syntax.Sig_let ((_61_190, lbs), _61_194, _61_196, _61_198) -> begin
(

let fv = (lb_fv lbs lid)
in (let _152_182 = (let _152_181 = (let _152_180 = (FStar_Syntax_Syntax.fvar lid fv.FStar_Syntax_Syntax.fv_delta fv.FStar_Syntax_Syntax.fv_qual)
in (_152_180, false))
in Term_name (_152_181))
in Some (_152_182)))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _61_204, _61_206, quals, _61_209) -> begin
if (any_val || (FStar_All.pipe_right quals (FStar_Util.for_some (fun _61_4 -> (match (_61_4) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| _61_215 -> begin
false
end))))) then begin
(

let dd = if ((FStar_Syntax_Util.is_primop_lid lid) || ((FStar_Util.starts_with lid.FStar_Ident.nsstr "Prims.") && (FStar_All.pipe_right quals (FStar_Util.for_some (fun _61_5 -> (match (_61_5) with
| (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) -> begin
true
end
| _61_224 -> begin
false
end)))))) then begin
FStar_Syntax_Syntax.Delta_equational
end else begin
FStar_Syntax_Syntax.Delta_constant
end
in if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Reflectable)) then begin
(

let refl_monad = (let _152_186 = (FStar_All.pipe_right lid.FStar_Ident.ns (FStar_List.map (fun x -> x.FStar_Ident.idText)))
in (FStar_Ident.lid_of_path _152_186 occurrence_range))
in (

let refl_const = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (refl_monad))) None occurrence_range)
in Some (Term_name ((refl_const, false)))))
end else begin
(let _152_190 = (let _152_189 = (let _152_188 = (let _152_187 = (fv_qual_of_se se)
in (FStar_Syntax_Syntax.fvar lid dd _152_187))
in (_152_188, false))
in Term_name (_152_189))
in Some (_152_190))
end)
end else begin
None
end
end
| FStar_Syntax_Syntax.Sig_new_effect (ne, _61_231) -> begin
(let _152_193 = (let _152_192 = (let _152_191 = (FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname (FStar_Ident.range_of_lid lid))
in (se, _152_191))
in Eff_name (_152_192))
in Some (_152_193))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (_61_235) -> begin
Some (Eff_name ((se, lid)))
end
| _61_238 -> begin
None
end)
end))
in (

let found_id = (match (lid.FStar_Ident.ns) with
| [] -> begin
(match ((try_lookup_id env lid.FStar_Ident.ident)) with
| Some (e, mut) -> begin
Some (Term_name ((e, mut)))
end
| None -> begin
(

let recname = (qualify env lid.FStar_Ident.ident)
in (FStar_Util.find_map env.recbindings (fun _61_249 -> (match (_61_249) with
| (id, l, dd) -> begin
if (id.FStar_Ident.idText = lid.FStar_Ident.ident.FStar_Ident.idText) then begin
(let _152_198 = (let _152_197 = (let _152_196 = (let _152_195 = (FStar_Ident.set_lid_range l (FStar_Ident.range_of_lid lid))
in (FStar_Syntax_Syntax.fvar _152_195 dd None))
in (_152_196, false))
in Term_name (_152_197))
in Some (_152_198))
end else begin
None
end
end))))
end)
end
| _61_251 -> begin
None
end)
in (match (found_id) with
| Some (_61_254) -> begin
found_id
end
| _61_257 -> begin
(resolve_in_open_namespaces env lid find_in_sig)
end)))))


let try_lookup_effect_name' : Prims.bool  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident) Prims.option = (fun exclude_interf env lid -> (match ((try_lookup_name true exclude_interf env lid)) with
| Some (Eff_name (o, l)) -> begin
Some ((o, l))
end
| _61_267 -> begin
None
end))


let try_lookup_effect_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env l -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some (o, l) -> begin
Some (l)
end
| _61_275 -> begin
None
end))


let try_lookup_effect_defn : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl Prims.option = (fun env l -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some (FStar_Syntax_Syntax.Sig_new_effect (ne, _61_280), _61_284) -> begin
Some (ne)
end
| _61_288 -> begin
None
end))


let is_effect_name : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((try_lookup_effect_name env lid)) with
| None -> begin
false
end
| Some (_61_293) -> begin
true
end))


let lookup_letbinding_quals : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.qualifier Prims.list = (fun env lid -> (

let find_in_sig = (fun lid -> (match ((FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str)) with
| Some (FStar_Syntax_Syntax.Sig_declare_typ (lid, _61_301, _61_303, quals, _61_306), _61_310) -> begin
Some (quals)
end
| _61_314 -> begin
None
end))
in (match ((resolve_in_open_namespaces env lid find_in_sig)) with
| Some (quals) -> begin
quals
end
| _61_318 -> begin
[]
end)))


let try_lookup_module : env  ->  Prims.string Prims.list  ->  FStar_Syntax_Syntax.modul Prims.option = (fun env path -> (match ((FStar_List.tryFind (fun _61_323 -> (match (_61_323) with
| (mlid, modul) -> begin
((FStar_Ident.path_of_lid mlid) = path)
end)) env.modules)) with
| Some (_61_325, modul) -> begin
Some (modul)
end
| None -> begin
None
end))


let try_lookup_let : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env lid -> (

let find_in_sig = (fun lid -> (match ((FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str)) with
| Some (FStar_Syntax_Syntax.Sig_let ((_61_335, lbs), _61_339, _61_341, _61_343), _61_347) -> begin
(

let fv = (lb_fv lbs lid)
in (let _152_234 = (FStar_Syntax_Syntax.fvar lid fv.FStar_Syntax_Syntax.fv_delta fv.FStar_Syntax_Syntax.fv_qual)
in Some (_152_234)))
end
| _61_352 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))


let try_lookup_definition : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env lid -> (

let find_in_sig = (fun lid -> (match ((FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str)) with
| Some (FStar_Syntax_Syntax.Sig_let (lbs, _61_359, _61_361, _61_363), _61_367) -> begin
(FStar_Util.find_map (Prims.snd lbs) (fun lb -> (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv lid) -> begin
Some (lb.FStar_Syntax_Syntax.lbdef)
end
| _61_374 -> begin
None
end)))
end
| _61_376 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))


let try_lookup_lid' : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term * Prims.bool) Prims.option = (fun any_val exclude_interf env lid -> (match ((try_lookup_name any_val exclude_interf env lid)) with
| Some (Term_name (e, mut)) -> begin
Some ((e, mut))
end
| _61_387 -> begin
None
end))


let try_lookup_lid : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term * Prims.bool) Prims.option = (fun env l -> (try_lookup_lid' env.iface false env l))


let try_lookup_datacon : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.fv Prims.option = (fun env lid -> (

let find_in_sig = (fun lid -> (match ((FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str)) with
| Some (FStar_Syntax_Syntax.Sig_declare_typ (_61_395, _61_397, _61_399, quals, _61_402), _61_406) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _61_6 -> (match (_61_6) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| _61_412 -> begin
false
end)))) then begin
(let _152_261 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant None)
in Some (_152_261))
end else begin
None
end
end
| Some (FStar_Syntax_Syntax.Sig_datacon (_61_414), _61_417) -> begin
(let _152_262 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in Some (_152_262))
end
| _61_421 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))


let find_all_datacons : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.list Prims.option = (fun env lid -> (

let find_in_sig = (fun lid -> (match ((FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str)) with
| Some (FStar_Syntax_Syntax.Sig_inductive_typ (_61_427, _61_429, _61_431, _61_433, _61_435, datas, _61_438, _61_440), _61_444) -> begin
Some (datas)
end
| _61_448 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))


let record_cache_aux : ((Prims.unit  ->  Prims.unit) * (Prims.unit  ->  Prims.unit) * (Prims.unit  ->  record_or_dc Prims.list) * (record_or_dc  ->  Prims.unit) * (Prims.unit  ->  Prims.unit)) = (

let record_cache = (FStar_Util.mk_ref (([])::[]))
in (

let push = (fun _61_451 -> (match (()) with
| () -> begin
(let _152_284 = (let _152_283 = (let _152_281 = (FStar_ST.read record_cache)
in (FStar_List.hd _152_281))
in (let _152_282 = (FStar_ST.read record_cache)
in (_152_283)::_152_282))
in (FStar_ST.op_Colon_Equals record_cache _152_284))
end))
in (

let pop = (fun _61_453 -> (match (()) with
| () -> begin
(let _152_288 = (let _152_287 = (FStar_ST.read record_cache)
in (FStar_List.tl _152_287))
in (FStar_ST.op_Colon_Equals record_cache _152_288))
end))
in (

let peek = (fun _61_455 -> (match (()) with
| () -> begin
(let _152_291 = (FStar_ST.read record_cache)
in (FStar_List.hd _152_291))
end))
in (

let insert = (fun r -> (let _152_298 = (let _152_297 = (let _152_294 = (peek ())
in (r)::_152_294)
in (let _152_296 = (let _152_295 = (FStar_ST.read record_cache)
in (FStar_List.tl _152_295))
in (_152_297)::_152_296))
in (FStar_ST.op_Colon_Equals record_cache _152_298)))
in (

let commit = (fun _61_459 -> (match (()) with
| () -> begin
(match ((FStar_ST.read record_cache)) with
| (hd)::(_61_462)::tl -> begin
(FStar_ST.op_Colon_Equals record_cache ((hd)::tl))
end
| _61_467 -> begin
(FStar_All.failwith "Impossible")
end)
end))
in (push, pop, peek, insert, commit)))))))


let push_record_cache : Prims.unit  ->  Prims.unit = (

let _61_477 = record_cache_aux
in (match (_61_477) with
| (push, _61_470, _61_472, _61_474, _61_476) -> begin
push
end))


let pop_record_cache : Prims.unit  ->  Prims.unit = (

let _61_487 = record_cache_aux
in (match (_61_487) with
| (_61_479, pop, _61_482, _61_484, _61_486) -> begin
pop
end))


let peek_record_cache : Prims.unit  ->  record_or_dc Prims.list = (

let _61_497 = record_cache_aux
in (match (_61_497) with
| (_61_489, _61_491, peek, _61_494, _61_496) -> begin
peek
end))


let insert_record_cache : record_or_dc  ->  Prims.unit = (

let _61_507 = record_cache_aux
in (match (_61_507) with
| (_61_499, _61_501, _61_503, insert, _61_506) -> begin
insert
end))


let commit_record_cache : Prims.unit  ->  Prims.unit = (

let _61_517 = record_cache_aux
in (match (_61_517) with
| (_61_509, _61_511, _61_513, _61_515, commit) -> begin
commit
end))


let extract_record : env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun e _61_10 -> (match (_61_10) with
| FStar_Syntax_Syntax.Sig_bundle (sigs, _61_522, _61_524, _61_526) -> begin
(

let is_rec = (FStar_Util.for_some (fun _61_7 -> (match (_61_7) with
| (FStar_Syntax_Syntax.RecordType (_)) | (FStar_Syntax_Syntax.RecordConstructor (_)) -> begin
true
end
| _61_537 -> begin
false
end)))
in (

let find_dc = (fun dc -> (FStar_All.pipe_right sigs (FStar_Util.find_opt (fun _61_8 -> (match (_61_8) with
| FStar_Syntax_Syntax.Sig_datacon (lid, _61_544, _61_546, _61_548, _61_550, _61_552, _61_554, _61_556) -> begin
(FStar_Ident.lid_equals dc lid)
end
| _61_560 -> begin
false
end)))))
in (FStar_All.pipe_right sigs (FStar_List.iter (fun _61_9 -> (match (_61_9) with
| FStar_Syntax_Syntax.Sig_inductive_typ (typename, univs, parms, _61_566, _61_568, (dc)::[], tags, _61_573) -> begin
(match ((let _152_401 = (find_dc dc)
in (FStar_All.pipe_left FStar_Util.must _152_401))) with
| FStar_Syntax_Syntax.Sig_datacon (constrname, _61_578, t, _61_581, _61_583, _61_585, _61_587, _61_589) -> begin
(

let _61_595 = (FStar_Syntax_Util.arrow_formals t)
in (match (_61_595) with
| (formals, _61_594) -> begin
(

let is_rec = (is_rec tags)
in (

let fields = (FStar_All.pipe_right formals (FStar_List.collect (fun _61_599 -> (match (_61_599) with
| (x, q) -> begin
if ((FStar_Syntax_Syntax.is_null_bv x) || (is_rec && (FStar_Syntax_Syntax.is_implicit q))) then begin
[]
end else begin
(let _152_405 = (let _152_404 = (let _152_403 = if is_rec then begin
(FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname)
end else begin
x.FStar_Syntax_Syntax.ppname
end
in (qual constrname _152_403))
in (_152_404, x.FStar_Syntax_Syntax.sort))
in (_152_405)::[])
end
end))))
in (

let record = {typename = typename; constrname = constrname; parms = parms; fields = fields; is_record = is_rec}
in (insert_record_cache record))))
end))
end
| _61_603 -> begin
()
end)
end
| _61_605 -> begin
()
end))))))
end
| _61_607 -> begin
()
end))


let try_lookup_record_or_dc_by_field_name : env  ->  FStar_Ident.lident  ->  (record_or_dc * FStar_Ident.lident) Prims.option = (fun env fieldname -> (

let maybe_add_constrname = (fun ns c -> (

let rec aux = (fun ns -> (match (ns) with
| [] -> begin
(c)::[]
end
| (c')::[] -> begin
if (c'.FStar_Ident.idText = c.FStar_Ident.idText) then begin
(c)::[]
end else begin
(c')::(c)::[]
end
end
| (hd)::tl -> begin
(let _152_416 = (aux tl)
in (hd)::_152_416)
end))
in (aux ns)))
in (

let find_in_cache = (fun fieldname -> (

let _61_625 = (fieldname.FStar_Ident.ns, fieldname.FStar_Ident.ident)
in (match (_61_625) with
| (ns, fieldname) -> begin
(let _152_421 = (peek_record_cache ())
in (FStar_Util.find_map _152_421 (fun record -> (

let constrname = record.constrname.FStar_Ident.ident
in (

let ns = (maybe_add_constrname ns constrname)
in (

let fname = (FStar_Ident.lid_of_ids (FStar_List.append ns ((fieldname)::[])))
in (FStar_Util.find_map record.fields (fun _61_633 -> (match (_61_633) with
| (f, _61_632) -> begin
if (FStar_Ident.lid_equals fname f) then begin
Some ((record, fname))
end else begin
None
end
end)))))))))
end)))
in (resolve_in_open_namespaces env fieldname find_in_cache))))


let try_lookup_record_by_field_name : env  ->  FStar_Ident.lident  ->  (record_or_dc * FStar_Ident.lident) Prims.option = (fun env fieldname -> (match ((try_lookup_record_or_dc_by_field_name env fieldname)) with
| Some (r, f) when r.is_record -> begin
Some ((r, f))
end
| _61_641 -> begin
None
end))


let try_lookup_projector_by_field_name : env  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * Prims.bool) Prims.option = (fun env fieldname -> (match ((try_lookup_record_or_dc_by_field_name env fieldname)) with
| Some (r, f) -> begin
Some ((f, r.is_record))
end
| _61_649 -> begin
None
end))


let qualify_field_to_record : env  ->  record_or_dc  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env recd f -> (

let qualify = (fun fieldname -> (

let _61_657 = (fieldname.FStar_Ident.ns, fieldname.FStar_Ident.ident)
in (match (_61_657) with
| (ns, fieldname) -> begin
(

let constrname = recd.constrname.FStar_Ident.ident
in (

let fname = (FStar_Ident.lid_of_ids (FStar_List.append (FStar_List.append ns ((constrname)::[])) ((fieldname)::[])))
in (FStar_Util.find_map recd.fields (fun _61_663 -> (match (_61_663) with
| (f, _61_662) -> begin
if (FStar_Ident.lid_equals fname f) then begin
Some (fname)
end else begin
None
end
end)))))
end)))
in (resolve_in_open_namespaces env f qualify)))


let unique : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  Prims.bool = (fun any_val exclude_if env lid -> (

let this_env = (

let _61_668 = env
in {curmodule = _61_668.curmodule; modules = _61_668.modules; open_namespaces = []; modul_abbrevs = _61_668.modul_abbrevs; sigaccum = _61_668.sigaccum; localbindings = _61_668.localbindings; recbindings = _61_668.recbindings; sigmap = _61_668.sigmap; default_result_effect = _61_668.default_result_effect; iface = _61_668.iface; admitted_iface = _61_668.admitted_iface; expect_typ = _61_668.expect_typ})
in (match ((try_lookup_lid' any_val exclude_if env lid)) with
| None -> begin
true
end
| Some (_61_673) -> begin
false
end)))


let push_bv' : env  ->  FStar_Ident.ident  ->  Prims.bool  ->  (env * FStar_Syntax_Syntax.bv) = (fun env x is_mutable -> (

let bv = (FStar_Syntax_Syntax.gen_bv x.FStar_Ident.idText (Some (x.FStar_Ident.idRange)) FStar_Syntax_Syntax.tun)
in ((

let _61_679 = env
in {curmodule = _61_679.curmodule; modules = _61_679.modules; open_namespaces = _61_679.open_namespaces; modul_abbrevs = _61_679.modul_abbrevs; sigaccum = _61_679.sigaccum; localbindings = ((x, bv, is_mutable))::env.localbindings; recbindings = _61_679.recbindings; sigmap = _61_679.sigmap; default_result_effect = _61_679.default_result_effect; iface = _61_679.iface; admitted_iface = _61_679.admitted_iface; expect_typ = _61_679.expect_typ}), bv)))


let push_bv_mutable : env  ->  FStar_Ident.ident  ->  (env * FStar_Syntax_Syntax.bv) = (fun env x -> (push_bv' env x true))


let push_bv : env  ->  FStar_Ident.ident  ->  (env * FStar_Syntax_Syntax.bv) = (fun env x -> (push_bv' env x false))


let push_top_level_rec_binding : env  ->  FStar_Ident.ident  ->  FStar_Syntax_Syntax.delta_depth  ->  env = (fun env x dd -> (

let l = (qualify env x)
in if (unique false true env l) then begin
(

let _61_689 = env
in {curmodule = _61_689.curmodule; modules = _61_689.modules; open_namespaces = _61_689.open_namespaces; modul_abbrevs = _61_689.modul_abbrevs; sigaccum = _61_689.sigaccum; localbindings = _61_689.localbindings; recbindings = ((x, l, dd))::env.recbindings; sigmap = _61_689.sigmap; default_result_effect = _61_689.default_result_effect; iface = _61_689.iface; admitted_iface = _61_689.admitted_iface; expect_typ = _61_689.expect_typ})
end else begin
(Prims.raise (FStar_Syntax_Syntax.Error (((Prims.strcat "Duplicate top-level names " l.FStar_Ident.str), (FStar_Ident.range_of_lid l)))))
end))


let push_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env s -> (

let err = (fun l -> (

let sopt = (FStar_Util.smap_try_find (sigmap env) l.FStar_Ident.str)
in (

let r = (match (sopt) with
| Some (se, _61_698) -> begin
(match ((let _152_473 = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_Util.find_opt (FStar_Ident.lid_equals l) _152_473))) with
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
in (let _152_476 = (let _152_475 = (let _152_474 = (FStar_Util.format2 "Duplicate top-level names [%s]; previously declared at %s" (FStar_Ident.text_of_lid l) r)
in (_152_474, (FStar_Ident.range_of_lid l)))
in FStar_Syntax_Syntax.Error (_152_475))
in (Prims.raise _152_476)))))
in (

let env = (

let _61_716 = (match (s) with
| FStar_Syntax_Syntax.Sig_let (_61_707) -> begin
(false, true)
end
| FStar_Syntax_Syntax.Sig_bundle (_61_710) -> begin
(true, true)
end
| _61_713 -> begin
(false, false)
end)
in (match (_61_716) with
| (any_val, exclude_if) -> begin
(

let lids = (FStar_Syntax_Util.lids_of_sigelt s)
in (match ((FStar_Util.find_map lids (fun l -> if (not ((unique any_val exclude_if env l))) then begin
Some (l)
end else begin
None
end))) with
| None -> begin
(

let _61_720 = (extract_record env s)
in (

let _61_722 = env
in {curmodule = _61_722.curmodule; modules = _61_722.modules; open_namespaces = _61_722.open_namespaces; modul_abbrevs = _61_722.modul_abbrevs; sigaccum = (s)::env.sigaccum; localbindings = _61_722.localbindings; recbindings = _61_722.recbindings; sigmap = _61_722.sigmap; default_result_effect = _61_722.default_result_effect; iface = _61_722.iface; admitted_iface = _61_722.admitted_iface; expect_typ = _61_722.expect_typ}))
end
| Some (l) -> begin
(err l)
end))
end))
in (

let _61_741 = (match (s) with
| FStar_Syntax_Syntax.Sig_bundle (ses, _61_729, _61_731, _61_733) -> begin
(let _152_480 = (FStar_List.map (fun se -> (let _152_479 = (FStar_Syntax_Util.lids_of_sigelt se)
in (_152_479, se))) ses)
in (env, _152_480))
end
| _61_738 -> begin
(let _152_483 = (let _152_482 = (let _152_481 = (FStar_Syntax_Util.lids_of_sigelt s)
in (_152_481, s))
in (_152_482)::[])
in (env, _152_483))
end)
in (match (_61_741) with
| (env, lss) -> begin
(

let _61_746 = (FStar_All.pipe_right lss (FStar_List.iter (fun _61_744 -> (match (_61_744) with
| (lids, se) -> begin
(FStar_All.pipe_right lids (FStar_List.iter (fun lid -> (FStar_Util.smap_add (sigmap env) lid.FStar_Ident.str (se, (env.iface && (not (env.admitted_iface))))))))
end))))
in env)
end)))))


let push_namespace : env  ->  FStar_Ident.lident  ->  env = (fun env ns -> (

let modules = env.modules
in if (FStar_All.pipe_right modules (FStar_Util.for_some (fun _61_754 -> (match (_61_754) with
| (m, _61_753) -> begin
(FStar_Util.starts_with (FStar_Ident.text_of_lid m) (FStar_Ident.text_of_lid ns))
end)))) then begin
(

let _61_755 = env
in {curmodule = _61_755.curmodule; modules = _61_755.modules; open_namespaces = (ns)::env.open_namespaces; modul_abbrevs = _61_755.modul_abbrevs; sigaccum = _61_755.sigaccum; localbindings = _61_755.localbindings; recbindings = _61_755.recbindings; sigmap = _61_755.sigmap; default_result_effect = _61_755.default_result_effect; iface = _61_755.iface; admitted_iface = _61_755.admitted_iface; expect_typ = _61_755.expect_typ})
end else begin
(let _152_493 = (let _152_492 = (let _152_491 = (FStar_Util.format1 "Namespace %s cannot be found" (FStar_Ident.text_of_lid ns))
in (_152_491, (FStar_Ident.range_of_lid ns)))
in FStar_Syntax_Syntax.Error (_152_492))
in (Prims.raise _152_493))
end))


let push_module_abbrev : env  ->  FStar_Ident.ident  ->  FStar_Ident.lident  ->  env = (fun env x l -> if (FStar_All.pipe_right env.modul_abbrevs (FStar_Util.for_some (fun _61_763 -> (match (_61_763) with
| (y, _61_762) -> begin
(x.FStar_Ident.idText = y.FStar_Ident.idText)
end)))) then begin
(let _152_503 = (let _152_502 = (let _152_501 = (FStar_Util.format1 "Module %s is already defined" x.FStar_Ident.idText)
in (_152_501, x.FStar_Ident.idRange))
in FStar_Syntax_Syntax.Error (_152_502))
in (Prims.raise _152_503))
end else begin
(

let modules = env.modules
in if (FStar_All.pipe_right modules (FStar_Util.for_some (fun _61_768 -> (match (_61_768) with
| (m, _61_767) -> begin
(FStar_Ident.lid_equals m l)
end)))) then begin
(

let _61_769 = env
in {curmodule = _61_769.curmodule; modules = _61_769.modules; open_namespaces = _61_769.open_namespaces; modul_abbrevs = ((x, l))::env.modul_abbrevs; sigaccum = _61_769.sigaccum; localbindings = _61_769.localbindings; recbindings = _61_769.recbindings; sigmap = _61_769.sigmap; default_result_effect = _61_769.default_result_effect; iface = _61_769.iface; admitted_iface = _61_769.admitted_iface; expect_typ = _61_769.expect_typ})
end else begin
(let _152_507 = (let _152_506 = (let _152_505 = (FStar_Util.format1 "Module %s cannot be found" (FStar_Ident.text_of_lid l))
in (_152_505, (FStar_Ident.range_of_lid l)))
in FStar_Syntax_Syntax.Error (_152_506))
in (Prims.raise _152_507))
end)
end)


let check_admits : env  ->  Prims.unit = (fun env -> (FStar_All.pipe_right env.sigaccum (FStar_List.iter (fun se -> (match (se) with
| FStar_Syntax_Syntax.Sig_declare_typ (l, u, t, quals, r) -> begin
(match ((try_lookup_lid env l)) with
| None -> begin
(

let _61_781 = (let _152_513 = (let _152_512 = (FStar_Range.string_of_range (FStar_Ident.range_of_lid l))
in (let _152_511 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format2 "%s: Warning: Admitting %s without a definition\n" _152_512 _152_511)))
in (FStar_Util.print_string _152_513))
in (FStar_Util.smap_add (sigmap env) l.FStar_Ident.str (FStar_Syntax_Syntax.Sig_declare_typ ((l, u, t, (FStar_Syntax_Syntax.Assumption)::quals, r)), false)))
end
| Some (_61_784) -> begin
()
end)
end
| _61_787 -> begin
()
end)))))


let finish : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env modul -> (

let _61_847 = (FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations (FStar_List.iter (fun _61_12 -> (match (_61_12) with
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _61_794, _61_796) -> begin
if ((FStar_List.contains FStar_Syntax_Syntax.Private quals) || (FStar_List.contains FStar_Syntax_Syntax.Abstract quals)) then begin
(FStar_All.pipe_right ses (FStar_List.iter (fun _61_11 -> (match (_61_11) with
| FStar_Syntax_Syntax.Sig_datacon (lid, _61_802, _61_804, _61_806, _61_808, _61_810, _61_812, _61_814) -> begin
(FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str)
end
| _61_818 -> begin
()
end))))
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _61_821, _61_823, quals, _61_826) -> begin
if (FStar_List.contains FStar_Syntax_Syntax.Private quals) then begin
(FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str)
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_let ((_61_830, lbs), r, _61_835, quals) -> begin
(

let _61_840 = if ((FStar_List.contains FStar_Syntax_Syntax.Private quals) || (FStar_List.contains FStar_Syntax_Syntax.Abstract quals)) then begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (let _152_524 = (let _152_523 = (let _152_522 = (let _152_521 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _152_521.FStar_Syntax_Syntax.fv_name)
in _152_522.FStar_Syntax_Syntax.v)
in _152_523.FStar_Ident.str)
in (FStar_Util.smap_remove (sigmap env) _152_524)))))
end else begin
()
end
in if ((FStar_List.contains FStar_Syntax_Syntax.Abstract quals) && (not ((FStar_List.contains FStar_Syntax_Syntax.Private quals)))) then begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (

let lid = (let _152_527 = (let _152_526 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _152_526.FStar_Syntax_Syntax.fv_name)
in _152_527.FStar_Syntax_Syntax.v)
in (

let decl = FStar_Syntax_Syntax.Sig_declare_typ ((lid, lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp, (FStar_Syntax_Syntax.Assumption)::quals, r))
in (FStar_Util.smap_add (sigmap env) lid.FStar_Ident.str (decl, false)))))))
end else begin
()
end)
end
| _61_846 -> begin
()
end))))
in (

let _61_849 = env
in {curmodule = None; modules = ((modul.FStar_Syntax_Syntax.name, modul))::env.modules; open_namespaces = []; modul_abbrevs = []; sigaccum = []; localbindings = []; recbindings = []; sigmap = _61_849.sigmap; default_result_effect = _61_849.default_result_effect; iface = _61_849.iface; admitted_iface = _61_849.admitted_iface; expect_typ = _61_849.expect_typ})))


type env_stack_ops =
{push : env  ->  env; mark : env  ->  env; reset_mark : env  ->  env; commit_mark : env  ->  env; pop : env  ->  env}


let is_Mkenv_stack_ops : env_stack_ops  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv_stack_ops"))))


let stack_ops : env_stack_ops = (

let stack = (FStar_Util.mk_ref [])
in (

let push = (fun env -> (

let _61_860 = (push_record_cache ())
in (

let _61_862 = (let _152_577 = (let _152_576 = (FStar_ST.read stack)
in (env)::_152_576)
in (FStar_ST.op_Colon_Equals stack _152_577))
in (

let _61_864 = env
in (let _152_578 = (FStar_Util.smap_copy (sigmap env))
in {curmodule = _61_864.curmodule; modules = _61_864.modules; open_namespaces = _61_864.open_namespaces; modul_abbrevs = _61_864.modul_abbrevs; sigaccum = _61_864.sigaccum; localbindings = _61_864.localbindings; recbindings = _61_864.recbindings; sigmap = _152_578; default_result_effect = _61_864.default_result_effect; iface = _61_864.iface; admitted_iface = _61_864.admitted_iface; expect_typ = _61_864.expect_typ})))))
in (

let pop = (fun env -> (match ((FStar_ST.read stack)) with
| (env)::tl -> begin
(

let _61_871 = (pop_record_cache ())
in (

let _61_873 = (FStar_ST.op_Colon_Equals stack tl)
in env))
end
| _61_876 -> begin
(FStar_All.failwith "Impossible: Too many pops")
end))
in (

let commit_mark = (fun env -> (

let _61_879 = (commit_record_cache ())
in (match ((FStar_ST.read stack)) with
| (_61_883)::tl -> begin
(

let _61_885 = (FStar_ST.op_Colon_Equals stack tl)
in env)
end
| _61_888 -> begin
(FStar_All.failwith "Impossible: Too many pops")
end)))
in {push = push; mark = push; reset_mark = pop; commit_mark = commit_mark; pop = pop}))))


let push : env  ->  env = (fun env -> (stack_ops.push env))


let mark : env  ->  env = (fun env -> (stack_ops.mark env))


let reset_mark : env  ->  env = (fun env -> (stack_ops.reset_mark env))


let commit_mark : env  ->  env = (fun env -> (stack_ops.commit_mark env))


let pop : env  ->  env = (fun env -> (stack_ops.pop env))


let export_interface : FStar_Ident.lident  ->  env  ->  env = (fun m env -> (

let sigelt_in_m = (fun se -> (match ((FStar_Syntax_Util.lids_of_sigelt se)) with
| (l)::_61_899 -> begin
(l.FStar_Ident.nsstr = m.FStar_Ident.str)
end
| _61_903 -> begin
false
end))
in (

let sm = (sigmap env)
in (

let env = (pop env)
in (

let keys = (FStar_Util.smap_keys sm)
in (

let sm' = (sigmap env)
in (

let _61_927 = (FStar_All.pipe_right keys (FStar_List.iter (fun k -> (match ((FStar_Util.smap_try_find sm' k)) with
| Some (se, true) when (sigelt_in_m se) -> begin
(

let _61_913 = (FStar_Util.smap_remove sm' k)
in (

let se = (match (se) with
| FStar_Syntax_Syntax.Sig_declare_typ (l, u, t, q, r) -> begin
FStar_Syntax_Syntax.Sig_declare_typ ((l, u, t, (FStar_Syntax_Syntax.Assumption)::q, r))
end
| _61_923 -> begin
se
end)
in (FStar_Util.smap_add sm' k (se, false))))
end
| _61_926 -> begin
()
end))))
in env)))))))


let finish_module_or_interface : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env modul -> (

let _61_931 = if (not (modul.FStar_Syntax_Syntax.is_interface)) then begin
(check_admits env)
end else begin
()
end
in (finish env modul)))


let prepare_module_or_interface : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  (env * Prims.bool) = (fun intf admitted env mname -> (

let prep = (fun env -> (

let open_ns = if (FStar_Ident.lid_equals mname FStar_Syntax_Const.prims_lid) then begin
[]
end else begin
if (FStar_Util.starts_with "FStar." (FStar_Ident.text_of_lid mname)) then begin
(FStar_Syntax_Const.prims_lid)::(FStar_Syntax_Const.fstar_ns_lid)::[]
end else begin
(FStar_Syntax_Const.prims_lid)::(FStar_Syntax_Const.st_lid)::(FStar_Syntax_Const.all_lid)::(FStar_Syntax_Const.fstar_ns_lid)::[]
end
end
in (

let open_ns = if ((FStar_List.length mname.FStar_Ident.ns) <> 0) then begin
(

let ns = (FStar_Ident.lid_of_ids mname.FStar_Ident.ns)
in (ns)::open_ns)
end else begin
open_ns
end
in (

let _61_942 = env
in {curmodule = Some (mname); modules = _61_942.modules; open_namespaces = open_ns; modul_abbrevs = _61_942.modul_abbrevs; sigaccum = _61_942.sigaccum; localbindings = _61_942.localbindings; recbindings = _61_942.recbindings; sigmap = env.sigmap; default_result_effect = _61_942.default_result_effect; iface = intf; admitted_iface = admitted; expect_typ = _61_942.expect_typ}))))
in (match ((FStar_All.pipe_right env.modules (FStar_Util.find_opt (fun _61_947 -> (match (_61_947) with
| (l, _61_946) -> begin
(FStar_Ident.lid_equals l mname)
end))))) with
| None -> begin
(let _152_615 = (prep env)
in (_152_615, false))
end
| Some (_61_950, m) -> begin
(

let _61_954 = if ((not (m.FStar_Syntax_Syntax.is_interface)) || intf) then begin
(let _152_618 = (let _152_617 = (let _152_616 = (FStar_Util.format1 "Duplicate module or interface name: %s" mname.FStar_Ident.str)
in (_152_616, (FStar_Ident.range_of_lid mname)))
in FStar_Syntax_Syntax.Error (_152_617))
in (Prims.raise _152_618))
end else begin
()
end
in (let _152_620 = (let _152_619 = (push env)
in (prep _152_619))
in (_152_620, true)))
end)))


let enter_monad_scope : env  ->  FStar_Ident.ident  ->  env = (fun env mname -> (

let curmod = (current_module env)
in (

let mscope = (FStar_Ident.lid_of_ids (FStar_List.append curmod.FStar_Ident.ns ((curmod.FStar_Ident.ident)::(mname)::[])))
in (

let _61_960 = env
in {curmodule = Some (mscope); modules = _61_960.modules; open_namespaces = (curmod)::env.open_namespaces; modul_abbrevs = _61_960.modul_abbrevs; sigaccum = _61_960.sigaccum; localbindings = _61_960.localbindings; recbindings = _61_960.recbindings; sigmap = _61_960.sigmap; default_result_effect = _61_960.default_result_effect; iface = _61_960.iface; admitted_iface = _61_960.admitted_iface; expect_typ = _61_960.expect_typ}))))


let exit_monad_scope : env  ->  env  ->  env = (fun env0 env -> (

let _61_964 = env
in {curmodule = env0.curmodule; modules = _61_964.modules; open_namespaces = env0.open_namespaces; modul_abbrevs = _61_964.modul_abbrevs; sigaccum = _61_964.sigaccum; localbindings = _61_964.localbindings; recbindings = _61_964.recbindings; sigmap = _61_964.sigmap; default_result_effect = _61_964.default_result_effect; iface = _61_964.iface; admitted_iface = _61_964.admitted_iface; expect_typ = _61_964.expect_typ}))


let fail_or = (fun env lookup lid -> (match ((lookup lid)) with
| None -> begin
(

let opened_modules = (FStar_List.map (fun _61_973 -> (match (_61_973) with
| (lid, _61_972) -> begin
(FStar_Ident.text_of_lid lid)
end)) env.modules)
in (

let module_of_the_lid = (let _152_636 = (FStar_Ident.path_of_ns lid.FStar_Ident.ns)
in (FStar_Ident.text_of_path _152_636))
in (

let msg = (FStar_Util.format1 "Identifier not found: [%s]" (FStar_Ident.text_of_lid lid))
in (

let msg = (match (env.curmodule) with
| Some (m) when (((FStar_Ident.text_of_lid m) = module_of_the_lid) || (module_of_the_lid = "")) -> begin
msg
end
| _61_980 when (FStar_List.existsb (fun m -> (m = module_of_the_lid)) opened_modules) -> begin
msg
end
| _61_983 -> begin
(let _152_640 = (let _152_639 = (let _152_638 = (FStar_Ident.path_of_ns lid.FStar_Ident.ns)
in (FStar_Ident.text_of_path _152_638))
in (FStar_Util.format3 "Hint: %s belongs to module %s, which does not belong to the list of modules in scope, namely %s" (FStar_Ident.text_of_lid lid) _152_639 (FStar_String.concat ", " opened_modules)))
in (Prims.strcat (Prims.strcat msg "\n") _152_640))
end)
in (Prims.raise (FStar_Syntax_Syntax.Error ((msg, (FStar_Ident.range_of_lid lid)))))))))
end
| Some (r) -> begin
r
end))


let fail_or2 = (fun lookup id -> (match ((lookup id)) with
| None -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (((Prims.strcat (Prims.strcat "Identifier not found [" id.FStar_Ident.idText) "]"), id.FStar_Ident.idRange))))
end
| Some (r) -> begin
r
end))




