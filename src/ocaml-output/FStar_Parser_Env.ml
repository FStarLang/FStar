
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
| Term_name (_62_28) -> begin
_62_28
end))


let ___Eff_name____0 = (fun projectee -> (match (projectee) with
| Eff_name (_62_31) -> begin
_62_31
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


let qual : FStar_Ident.lident  ->  FStar_Ident.ident  ->  FStar_Ident.lident = (fun lid id -> (let _154_90 = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns ((lid.FStar_Ident.ident)::(id)::[])))
in (FStar_Ident.set_lid_range _154_90 id.FStar_Ident.idRange)))


let qualify : env  ->  FStar_Ident.ident  ->  FStar_Ident.lident = (fun env id -> (let _154_95 = (current_module env)
in (qual _154_95 id)))


let qualify_lid : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (

let cur = (current_module env)
in (let _154_100 = (FStar_Ident.lid_of_ids (FStar_List.append (FStar_List.append (FStar_List.append cur.FStar_Ident.ns ((cur.FStar_Ident.ident)::[])) lid.FStar_Ident.ns) ((lid.FStar_Ident.ident)::[])))
in (FStar_Ident.set_lid_range _154_100 (FStar_Ident.range_of_lid lid)))))


let new_sigmap = (fun _62_52 -> (match (()) with
| () -> begin
(FStar_Util.smap_create 100)
end))


let empty_env : Prims.unit  ->  env = (fun _62_53 -> (match (()) with
| () -> begin
(let _154_104 = (new_sigmap ())
in {curmodule = None; modules = []; open_namespaces = []; modul_abbrevs = []; sigaccum = []; localbindings = []; recbindings = []; sigmap = _154_104; default_result_effect = FStar_Syntax_Const.effect_Tot_lid; iface = false; admitted_iface = false; expect_typ = false})
end))


let sigmap : env  ->  (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap = (fun env -> env.sigmap)


let has_all_in_scope : env  ->  Prims.bool = (fun env -> (FStar_List.existsb (fun _62_59 -> (match (_62_59) with
| (m, _62_58) -> begin
(FStar_Ident.lid_equals m FStar_Syntax_Const.all_lid)
end)) env.modules))


let default_total : env  ->  env = (fun env -> (

let _62_61 = env
in {curmodule = _62_61.curmodule; modules = _62_61.modules; open_namespaces = _62_61.open_namespaces; modul_abbrevs = _62_61.modul_abbrevs; sigaccum = _62_61.sigaccum; localbindings = _62_61.localbindings; recbindings = _62_61.recbindings; sigmap = _62_61.sigmap; default_result_effect = FStar_Syntax_Const.effect_Tot_lid; iface = _62_61.iface; admitted_iface = _62_61.admitted_iface; expect_typ = _62_61.expect_typ}))


let default_ml : env  ->  env = (fun env -> if (has_all_in_scope env) then begin
(

let _62_64 = env
in {curmodule = _62_64.curmodule; modules = _62_64.modules; open_namespaces = _62_64.open_namespaces; modul_abbrevs = _62_64.modul_abbrevs; sigaccum = _62_64.sigaccum; localbindings = _62_64.localbindings; recbindings = _62_64.recbindings; sigmap = _62_64.sigmap; default_result_effect = FStar_Syntax_Const.effect_ML_lid; iface = _62_64.iface; admitted_iface = _62_64.admitted_iface; expect_typ = _62_64.expect_typ})
end else begin
env
end)


let set_bv_range : FStar_Syntax_Syntax.bv  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.bv = (fun bv r -> (

let id = (

let _62_68 = bv.FStar_Syntax_Syntax.ppname
in {FStar_Ident.idText = _62_68.FStar_Ident.idText; FStar_Ident.idRange = r})
in (

let _62_71 = bv
in {FStar_Syntax_Syntax.ppname = id; FStar_Syntax_Syntax.index = _62_71.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _62_71.FStar_Syntax_Syntax.sort})))


let bv_to_name : FStar_Syntax_Syntax.bv  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.term = (fun bv r -> (FStar_Syntax_Syntax.bv_to_name (set_bv_range bv r)))


let unmangleMap : (Prims.string * Prims.string * FStar_Syntax_Syntax.delta_depth * FStar_Syntax_Syntax.fv_qual Prims.option) Prims.list = (("op_ColonColon", "Cons", FStar_Syntax_Syntax.Delta_constant, Some (FStar_Syntax_Syntax.Data_ctor)))::(("not", "op_Negation", FStar_Syntax_Syntax.Delta_equational, None))::[]


let unmangleOpName : FStar_Ident.ident  ->  FStar_Syntax_Syntax.term Prims.option = (fun id -> (FStar_Util.find_map unmangleMap (fun _62_80 -> (match (_62_80) with
| (x, y, dd, dq) -> begin
if (id.FStar_Ident.idText = x) then begin
(let _154_126 = (let _154_125 = (FStar_Ident.lid_of_path (("Prims")::(y)::[]) id.FStar_Ident.idRange)
in (FStar_Syntax_Syntax.fvar _154_125 dd dq))
in Some (_154_126))
end else begin
None
end
end))))


let try_lookup_id : env  ->  FStar_Ident.ident  ->  (FStar_Syntax_Syntax.term * Prims.bool) Prims.option = (fun env id -> (match ((unmangleOpName id)) with
| Some (f) -> begin
Some ((f, false))
end
| _62_86 -> begin
(FStar_Util.find_map env.localbindings (fun _62_1 -> (match (_62_1) with
| (id', x, mut) when (id'.FStar_Ident.idText = id.FStar_Ident.idText) -> begin
(let _154_133 = (let _154_132 = (bv_to_name x id.FStar_Ident.idRange)
in (_154_132, mut))
in Some (_154_133))
end
| _62_93 -> begin
None
end)))
end))


let resolve_in_open_namespaces' = (fun env lid finder -> (

let aux = (fun namespaces -> (match ((finder lid)) with
| Some (r) -> begin
Some (r)
end
| _62_103 -> begin
(

let ids = (FStar_Ident.ids_of_lid lid)
in (FStar_Util.find_map namespaces (fun ns -> (

let full_name = (FStar_Ident.lid_of_ids (FStar_List.append (FStar_Ident.ids_of_lid ns) ids))
in (finder full_name)))))
end))
in (let _154_144 = (let _154_143 = (current_module env)
in (_154_143)::env.open_namespaces)
in (aux _154_144))))


let expand_module_abbrevs : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (match (lid.FStar_Ident.ns) with
| (id)::rest -> begin
(match ((FStar_All.pipe_right env.modul_abbrevs (FStar_List.tryFind (fun _62_115 -> (match (_62_115) with
| (id', _62_114) -> begin
(id.FStar_Ident.idText = id'.FStar_Ident.idText)
end))))) with
| None -> begin
lid
end
| Some (_62_118, lid') -> begin
(FStar_Ident.lid_of_ids (FStar_List.append (FStar_List.append (FStar_Ident.ids_of_lid lid') rest) ((lid.FStar_Ident.ident)::[])))
end)
end
| _62_123 -> begin
lid
end))


let resolve_in_open_namespaces = (fun env lid finder -> (let _154_156 = (expand_module_abbrevs env lid)
in (resolve_in_open_namespaces' env _154_156 finder)))


let fv_qual_of_se : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.fv_qual Prims.option = (fun _62_3 -> (match (_62_3) with
| FStar_Syntax_Syntax.Sig_datacon (_62_130, _62_132, _62_134, l, _62_137, quals, _62_140, _62_142) -> begin
(

let qopt = (FStar_Util.find_map quals (fun _62_2 -> (match (_62_2) with
| FStar_Syntax_Syntax.RecordConstructor (fs) -> begin
Some (FStar_Syntax_Syntax.Record_ctor ((l, fs)))
end
| _62_149 -> begin
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
| FStar_Syntax_Syntax.Sig_declare_typ (_62_154, _62_156, _62_158, quals, _62_161) -> begin
None
end
| _62_165 -> begin
None
end))


let lb_fv : FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.fv = (fun lbs lid -> (let _154_165 = (FStar_Util.find_map lbs (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in if (FStar_Syntax_Syntax.fv_eq_lid fv lid) then begin
Some (fv)
end else begin
None
end)))
in (FStar_All.pipe_right _154_165 FStar_Util.must)))


let try_lookup_name : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  foundname Prims.option = (fun any_val exclude_interf env lid -> (

let occurrence_range = (FStar_Ident.range_of_lid lid)
in (

let find_in_sig = (fun lid -> (match ((FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str)) with
| Some (_62_178, true) when exclude_interf -> begin
None
end
| None -> begin
None
end
| Some (se, _62_185) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_62_189) -> begin
(let _154_178 = (let _154_177 = (let _154_176 = (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.Delta_constant None)
in (_154_176, false))
in Term_name (_154_177))
in Some (_154_178))
end
| FStar_Syntax_Syntax.Sig_datacon (_62_192) -> begin
(let _154_182 = (let _154_181 = (let _154_180 = (let _154_179 = (fv_qual_of_se se)
in (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.Delta_constant _154_179))
in (_154_180, false))
in Term_name (_154_181))
in Some (_154_182))
end
| FStar_Syntax_Syntax.Sig_let ((_62_195, lbs), _62_199, _62_201, _62_203) -> begin
(

let fv = (lb_fv lbs lid)
in (let _154_185 = (let _154_184 = (let _154_183 = (FStar_Syntax_Syntax.fvar lid fv.FStar_Syntax_Syntax.fv_delta fv.FStar_Syntax_Syntax.fv_qual)
in (_154_183, false))
in Term_name (_154_184))
in Some (_154_185)))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _62_209, _62_211, quals, _62_214) -> begin
if (any_val || (FStar_All.pipe_right quals (FStar_Util.for_some (fun _62_4 -> (match (_62_4) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| _62_220 -> begin
false
end))))) then begin
(

let dd = if ((FStar_Syntax_Util.is_primop_lid lid) || ((FStar_Util.starts_with lid.FStar_Ident.nsstr "Prims.") && (FStar_All.pipe_right quals (FStar_Util.for_some (fun _62_5 -> (match (_62_5) with
| (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) -> begin
true
end
| _62_229 -> begin
false
end)))))) then begin
FStar_Syntax_Syntax.Delta_equational
end else begin
FStar_Syntax_Syntax.Delta_constant
end
in if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Reflectable)) then begin
(

let refl_monad = (let _154_189 = (FStar_All.pipe_right lid.FStar_Ident.ns (FStar_List.map (fun x -> x.FStar_Ident.idText)))
in (FStar_Ident.lid_of_path _154_189 occurrence_range))
in (

let refl_const = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (refl_monad))) None occurrence_range)
in Some (Term_name ((refl_const, false)))))
end else begin
(let _154_193 = (let _154_192 = (let _154_191 = (let _154_190 = (fv_qual_of_se se)
in (FStar_Syntax_Syntax.fvar lid dd _154_190))
in (_154_191, false))
in Term_name (_154_192))
in Some (_154_193))
end)
end else begin
None
end
end
| FStar_Syntax_Syntax.Sig_new_effect (ne, _62_236) -> begin
(let _154_196 = (let _154_195 = (let _154_194 = (FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname (FStar_Ident.range_of_lid lid))
in (se, _154_194))
in Eff_name (_154_195))
in Some (_154_196))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (_62_240) -> begin
Some (Eff_name ((se, lid)))
end
| _62_243 -> begin
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
in (FStar_Util.find_map env.recbindings (fun _62_254 -> (match (_62_254) with
| (id, l, dd) -> begin
if (id.FStar_Ident.idText = lid.FStar_Ident.ident.FStar_Ident.idText) then begin
(let _154_201 = (let _154_200 = (let _154_199 = (let _154_198 = (FStar_Ident.set_lid_range l (FStar_Ident.range_of_lid lid))
in (FStar_Syntax_Syntax.fvar _154_198 dd None))
in (_154_199, false))
in Term_name (_154_200))
in Some (_154_201))
end else begin
None
end
end))))
end)
end
| _62_256 -> begin
None
end)
in (match (found_id) with
| Some (_62_259) -> begin
found_id
end
| _62_262 -> begin
(resolve_in_open_namespaces env lid find_in_sig)
end)))))


let try_lookup_effect_name' : Prims.bool  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident) Prims.option = (fun exclude_interf env lid -> (match ((try_lookup_name true exclude_interf env lid)) with
| Some (Eff_name (o, l)) -> begin
Some ((o, l))
end
| _62_272 -> begin
None
end))


let try_lookup_effect_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env l -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some (o, l) -> begin
Some (l)
end
| _62_280 -> begin
None
end))


let try_lookup_effect_defn : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl Prims.option = (fun env l -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some (FStar_Syntax_Syntax.Sig_new_effect (ne, _62_285), _62_289) -> begin
Some (ne)
end
| _62_293 -> begin
None
end))


let is_effect_name : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((try_lookup_effect_name env lid)) with
| None -> begin
false
end
| Some (_62_298) -> begin
true
end))


let lookup_letbinding_quals : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.qualifier Prims.list = (fun env lid -> (

let find_in_sig = (fun lid -> (match ((FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str)) with
| Some (FStar_Syntax_Syntax.Sig_declare_typ (lid, _62_306, _62_308, quals, _62_311), _62_315) -> begin
Some (quals)
end
| _62_319 -> begin
None
end))
in (match ((resolve_in_open_namespaces env lid find_in_sig)) with
| Some (quals) -> begin
quals
end
| _62_323 -> begin
[]
end)))


let try_lookup_module : env  ->  Prims.string Prims.list  ->  FStar_Syntax_Syntax.modul Prims.option = (fun env path -> (match ((FStar_List.tryFind (fun _62_328 -> (match (_62_328) with
| (mlid, modul) -> begin
((FStar_Ident.path_of_lid mlid) = path)
end)) env.modules)) with
| Some (_62_330, modul) -> begin
Some (modul)
end
| None -> begin
None
end))


let try_lookup_let : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env lid -> (

let find_in_sig = (fun lid -> (match ((FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str)) with
| Some (FStar_Syntax_Syntax.Sig_let ((_62_340, lbs), _62_344, _62_346, _62_348), _62_352) -> begin
(

let fv = (lb_fv lbs lid)
in (let _154_237 = (FStar_Syntax_Syntax.fvar lid fv.FStar_Syntax_Syntax.fv_delta fv.FStar_Syntax_Syntax.fv_qual)
in Some (_154_237)))
end
| _62_357 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))


let try_lookup_definition : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env lid -> (

let find_in_sig = (fun lid -> (match ((FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str)) with
| Some (FStar_Syntax_Syntax.Sig_let (lbs, _62_364, _62_366, _62_368), _62_372) -> begin
(FStar_Util.find_map (Prims.snd lbs) (fun lb -> (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv lid) -> begin
Some (lb.FStar_Syntax_Syntax.lbdef)
end
| _62_379 -> begin
None
end)))
end
| _62_381 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))


let try_lookup_lid' : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term * Prims.bool) Prims.option = (fun any_val exclude_interf env lid -> (match ((try_lookup_name any_val exclude_interf env lid)) with
| Some (Term_name (e, mut)) -> begin
Some ((e, mut))
end
| _62_392 -> begin
None
end))


let try_lookup_lid : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term * Prims.bool) Prims.option = (fun env l -> (try_lookup_lid' env.iface false env l))


let try_lookup_datacon : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.fv Prims.option = (fun env lid -> (

let find_in_sig = (fun lid -> (match ((FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str)) with
| Some (FStar_Syntax_Syntax.Sig_declare_typ (_62_400, _62_402, _62_404, quals, _62_407), _62_411) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _62_6 -> (match (_62_6) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| _62_417 -> begin
false
end)))) then begin
(let _154_264 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant None)
in Some (_154_264))
end else begin
None
end
end
| Some (FStar_Syntax_Syntax.Sig_datacon (_62_419), _62_422) -> begin
(let _154_265 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in Some (_154_265))
end
| _62_426 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))


let find_all_datacons : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.list Prims.option = (fun env lid -> (

let find_in_sig = (fun lid -> (match ((FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str)) with
| Some (FStar_Syntax_Syntax.Sig_inductive_typ (_62_432, _62_434, _62_436, _62_438, _62_440, datas, _62_443, _62_445), _62_449) -> begin
Some (datas)
end
| _62_453 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))


let record_cache_aux : ((Prims.unit  ->  Prims.unit) * (Prims.unit  ->  Prims.unit) * (Prims.unit  ->  record_or_dc Prims.list) * (record_or_dc  ->  Prims.unit) * (Prims.unit  ->  Prims.unit)) = (

let record_cache = (FStar_Util.mk_ref (([])::[]))
in (

let push = (fun _62_456 -> (match (()) with
| () -> begin
(let _154_287 = (let _154_286 = (let _154_284 = (FStar_ST.read record_cache)
in (FStar_List.hd _154_284))
in (let _154_285 = (FStar_ST.read record_cache)
in (_154_286)::_154_285))
in (FStar_ST.op_Colon_Equals record_cache _154_287))
end))
in (

let pop = (fun _62_458 -> (match (()) with
| () -> begin
(let _154_291 = (let _154_290 = (FStar_ST.read record_cache)
in (FStar_List.tl _154_290))
in (FStar_ST.op_Colon_Equals record_cache _154_291))
end))
in (

let peek = (fun _62_460 -> (match (()) with
| () -> begin
(let _154_294 = (FStar_ST.read record_cache)
in (FStar_List.hd _154_294))
end))
in (

let insert = (fun r -> (let _154_301 = (let _154_300 = (let _154_297 = (peek ())
in (r)::_154_297)
in (let _154_299 = (let _154_298 = (FStar_ST.read record_cache)
in (FStar_List.tl _154_298))
in (_154_300)::_154_299))
in (FStar_ST.op_Colon_Equals record_cache _154_301)))
in (

let commit = (fun _62_464 -> (match (()) with
| () -> begin
(match ((FStar_ST.read record_cache)) with
| (hd)::(_62_467)::tl -> begin
(FStar_ST.op_Colon_Equals record_cache ((hd)::tl))
end
| _62_472 -> begin
(FStar_All.failwith "Impossible")
end)
end))
in (push, pop, peek, insert, commit)))))))


let push_record_cache : Prims.unit  ->  Prims.unit = (

let _62_482 = record_cache_aux
in (match (_62_482) with
| (push, _62_475, _62_477, _62_479, _62_481) -> begin
push
end))


let pop_record_cache : Prims.unit  ->  Prims.unit = (

let _62_492 = record_cache_aux
in (match (_62_492) with
| (_62_484, pop, _62_487, _62_489, _62_491) -> begin
pop
end))


let peek_record_cache : Prims.unit  ->  record_or_dc Prims.list = (

let _62_502 = record_cache_aux
in (match (_62_502) with
| (_62_494, _62_496, peek, _62_499, _62_501) -> begin
peek
end))


let insert_record_cache : record_or_dc  ->  Prims.unit = (

let _62_512 = record_cache_aux
in (match (_62_512) with
| (_62_504, _62_506, _62_508, insert, _62_511) -> begin
insert
end))


let commit_record_cache : Prims.unit  ->  Prims.unit = (

let _62_522 = record_cache_aux
in (match (_62_522) with
| (_62_514, _62_516, _62_518, _62_520, commit) -> begin
commit
end))


let extract_record : env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun e _62_10 -> (match (_62_10) with
| FStar_Syntax_Syntax.Sig_bundle (sigs, _62_527, _62_529, _62_531) -> begin
(

let is_rec = (FStar_Util.for_some (fun _62_7 -> (match (_62_7) with
| (FStar_Syntax_Syntax.RecordType (_)) | (FStar_Syntax_Syntax.RecordConstructor (_)) -> begin
true
end
| _62_542 -> begin
false
end)))
in (

let find_dc = (fun dc -> (FStar_All.pipe_right sigs (FStar_Util.find_opt (fun _62_8 -> (match (_62_8) with
| FStar_Syntax_Syntax.Sig_datacon (lid, _62_549, _62_551, _62_553, _62_555, _62_557, _62_559, _62_561) -> begin
(FStar_Ident.lid_equals dc lid)
end
| _62_565 -> begin
false
end)))))
in (FStar_All.pipe_right sigs (FStar_List.iter (fun _62_9 -> (match (_62_9) with
| FStar_Syntax_Syntax.Sig_inductive_typ (typename, univs, parms, _62_571, _62_573, (dc)::[], tags, _62_578) -> begin
(match ((let _154_404 = (find_dc dc)
in (FStar_All.pipe_left FStar_Util.must _154_404))) with
| FStar_Syntax_Syntax.Sig_datacon (constrname, _62_583, t, _62_586, _62_588, _62_590, _62_592, _62_594) -> begin
(

let _62_600 = (FStar_Syntax_Util.arrow_formals t)
in (match (_62_600) with
| (formals, _62_599) -> begin
(

let is_rec = (is_rec tags)
in (

let fields = (FStar_All.pipe_right formals (FStar_List.collect (fun _62_604 -> (match (_62_604) with
| (x, q) -> begin
if ((FStar_Syntax_Syntax.is_null_bv x) || (is_rec && (FStar_Syntax_Syntax.is_implicit q))) then begin
[]
end else begin
(let _154_408 = (let _154_407 = (let _154_406 = if is_rec then begin
(FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname)
end else begin
x.FStar_Syntax_Syntax.ppname
end
in (qual constrname _154_406))
in (_154_407, x.FStar_Syntax_Syntax.sort))
in (_154_408)::[])
end
end))))
in (

let record = {typename = typename; constrname = constrname; parms = parms; fields = fields; is_record = is_rec}
in (insert_record_cache record))))
end))
end
| _62_608 -> begin
()
end)
end
| _62_610 -> begin
()
end))))))
end
| _62_612 -> begin
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
(let _154_419 = (aux tl)
in (hd)::_154_419)
end))
in (aux ns)))
in (

let find_in_cache = (fun fieldname -> (

let _62_630 = (fieldname.FStar_Ident.ns, fieldname.FStar_Ident.ident)
in (match (_62_630) with
| (ns, fieldname) -> begin
(let _154_424 = (peek_record_cache ())
in (FStar_Util.find_map _154_424 (fun record -> (

let constrname = record.constrname.FStar_Ident.ident
in (

let ns = (maybe_add_constrname ns constrname)
in (

let fname = (FStar_Ident.lid_of_ids (FStar_List.append ns ((fieldname)::[])))
in (FStar_Util.find_map record.fields (fun _62_638 -> (match (_62_638) with
| (f, _62_637) -> begin
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
| _62_646 -> begin
None
end))


let try_lookup_projector_by_field_name : env  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * Prims.bool) Prims.option = (fun env fieldname -> (match ((try_lookup_record_or_dc_by_field_name env fieldname)) with
| Some (r, f) -> begin
Some ((f, r.is_record))
end
| _62_654 -> begin
None
end))


let qualify_field_to_record : env  ->  record_or_dc  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env recd f -> (

let qualify = (fun fieldname -> (

let _62_662 = (fieldname.FStar_Ident.ns, fieldname.FStar_Ident.ident)
in (match (_62_662) with
| (ns, fieldname) -> begin
(

let constrname = recd.constrname.FStar_Ident.ident
in (

let fname = (FStar_Ident.lid_of_ids (FStar_List.append (FStar_List.append ns ((constrname)::[])) ((fieldname)::[])))
in (FStar_Util.find_map recd.fields (fun _62_668 -> (match (_62_668) with
| (f, _62_667) -> begin
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

let _62_673 = env
in {curmodule = _62_673.curmodule; modules = _62_673.modules; open_namespaces = []; modul_abbrevs = _62_673.modul_abbrevs; sigaccum = _62_673.sigaccum; localbindings = _62_673.localbindings; recbindings = _62_673.recbindings; sigmap = _62_673.sigmap; default_result_effect = _62_673.default_result_effect; iface = _62_673.iface; admitted_iface = _62_673.admitted_iface; expect_typ = _62_673.expect_typ})
in (match ((try_lookup_lid' any_val exclude_if env lid)) with
| None -> begin
true
end
| Some (_62_678) -> begin
false
end)))


let push_bv' : env  ->  FStar_Ident.ident  ->  Prims.bool  ->  (env * FStar_Syntax_Syntax.bv) = (fun env x is_mutable -> (

let bv = (FStar_Syntax_Syntax.gen_bv x.FStar_Ident.idText (Some (x.FStar_Ident.idRange)) FStar_Syntax_Syntax.tun)
in ((

let _62_684 = env
in {curmodule = _62_684.curmodule; modules = _62_684.modules; open_namespaces = _62_684.open_namespaces; modul_abbrevs = _62_684.modul_abbrevs; sigaccum = _62_684.sigaccum; localbindings = ((x, bv, is_mutable))::env.localbindings; recbindings = _62_684.recbindings; sigmap = _62_684.sigmap; default_result_effect = _62_684.default_result_effect; iface = _62_684.iface; admitted_iface = _62_684.admitted_iface; expect_typ = _62_684.expect_typ}), bv)))


let push_bv_mutable : env  ->  FStar_Ident.ident  ->  (env * FStar_Syntax_Syntax.bv) = (fun env x -> (push_bv' env x true))


let push_bv : env  ->  FStar_Ident.ident  ->  (env * FStar_Syntax_Syntax.bv) = (fun env x -> (push_bv' env x false))


let push_top_level_rec_binding : env  ->  FStar_Ident.ident  ->  FStar_Syntax_Syntax.delta_depth  ->  env = (fun env x dd -> (

let l = (qualify env x)
in if (unique false true env l) then begin
(

let _62_694 = env
in {curmodule = _62_694.curmodule; modules = _62_694.modules; open_namespaces = _62_694.open_namespaces; modul_abbrevs = _62_694.modul_abbrevs; sigaccum = _62_694.sigaccum; localbindings = _62_694.localbindings; recbindings = ((x, l, dd))::env.recbindings; sigmap = _62_694.sigmap; default_result_effect = _62_694.default_result_effect; iface = _62_694.iface; admitted_iface = _62_694.admitted_iface; expect_typ = _62_694.expect_typ})
end else begin
(Prims.raise (FStar_Syntax_Syntax.Error (((Prims.strcat "Duplicate top-level names " l.FStar_Ident.str), (FStar_Ident.range_of_lid l)))))
end))


let push_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env s -> (

let err = (fun l -> (

let sopt = (FStar_Util.smap_try_find (sigmap env) l.FStar_Ident.str)
in (

let r = (match (sopt) with
| Some (se, _62_703) -> begin
(match ((let _154_476 = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_Util.find_opt (FStar_Ident.lid_equals l) _154_476))) with
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
in (let _154_479 = (let _154_478 = (let _154_477 = (FStar_Util.format2 "Duplicate top-level names [%s]; previously declared at %s" (FStar_Ident.text_of_lid l) r)
in (_154_477, (FStar_Ident.range_of_lid l)))
in FStar_Syntax_Syntax.Error (_154_478))
in (Prims.raise _154_479)))))
in (

let env = (

let _62_721 = (match (s) with
| FStar_Syntax_Syntax.Sig_let (_62_712) -> begin
(false, true)
end
| FStar_Syntax_Syntax.Sig_bundle (_62_715) -> begin
(true, true)
end
| _62_718 -> begin
(false, false)
end)
in (match (_62_721) with
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

let _62_725 = (extract_record env s)
in (

let _62_727 = env
in {curmodule = _62_727.curmodule; modules = _62_727.modules; open_namespaces = _62_727.open_namespaces; modul_abbrevs = _62_727.modul_abbrevs; sigaccum = (s)::env.sigaccum; localbindings = _62_727.localbindings; recbindings = _62_727.recbindings; sigmap = _62_727.sigmap; default_result_effect = _62_727.default_result_effect; iface = _62_727.iface; admitted_iface = _62_727.admitted_iface; expect_typ = _62_727.expect_typ}))
end
| Some (l) -> begin
(err l)
end))
end))
in (

let _62_746 = (match (s) with
| FStar_Syntax_Syntax.Sig_bundle (ses, _62_734, _62_736, _62_738) -> begin
(let _154_483 = (FStar_List.map (fun se -> (let _154_482 = (FStar_Syntax_Util.lids_of_sigelt se)
in (_154_482, se))) ses)
in (env, _154_483))
end
| _62_743 -> begin
(let _154_486 = (let _154_485 = (let _154_484 = (FStar_Syntax_Util.lids_of_sigelt s)
in (_154_484, s))
in (_154_485)::[])
in (env, _154_486))
end)
in (match (_62_746) with
| (env, lss) -> begin
(

let _62_751 = (FStar_All.pipe_right lss (FStar_List.iter (fun _62_749 -> (match (_62_749) with
| (lids, se) -> begin
(FStar_All.pipe_right lids (FStar_List.iter (fun lid -> (FStar_Util.smap_add (sigmap env) lid.FStar_Ident.str (se, (env.iface && (not (env.admitted_iface))))))))
end))))
in env)
end)))))


let push_namespace : env  ->  FStar_Ident.lident  ->  env = (fun env ns -> (

let modules = env.modules
in if (FStar_All.pipe_right modules (FStar_Util.for_some (fun _62_759 -> (match (_62_759) with
| (m, _62_758) -> begin
(FStar_Util.starts_with (FStar_Ident.text_of_lid m) (FStar_Ident.text_of_lid ns))
end)))) then begin
(

let _62_760 = env
in {curmodule = _62_760.curmodule; modules = _62_760.modules; open_namespaces = (ns)::env.open_namespaces; modul_abbrevs = _62_760.modul_abbrevs; sigaccum = _62_760.sigaccum; localbindings = _62_760.localbindings; recbindings = _62_760.recbindings; sigmap = _62_760.sigmap; default_result_effect = _62_760.default_result_effect; iface = _62_760.iface; admitted_iface = _62_760.admitted_iface; expect_typ = _62_760.expect_typ})
end else begin
(let _154_496 = (let _154_495 = (let _154_494 = (FStar_Util.format1 "Namespace %s cannot be found" (FStar_Ident.text_of_lid ns))
in (_154_494, (FStar_Ident.range_of_lid ns)))
in FStar_Syntax_Syntax.Error (_154_495))
in (Prims.raise _154_496))
end))


let push_module_abbrev : env  ->  FStar_Ident.ident  ->  FStar_Ident.lident  ->  env = (fun env x l -> if (FStar_All.pipe_right env.modul_abbrevs (FStar_Util.for_some (fun _62_768 -> (match (_62_768) with
| (y, _62_767) -> begin
(x.FStar_Ident.idText = y.FStar_Ident.idText)
end)))) then begin
(let _154_506 = (let _154_505 = (let _154_504 = (FStar_Util.format1 "Module %s is already defined" x.FStar_Ident.idText)
in (_154_504, x.FStar_Ident.idRange))
in FStar_Syntax_Syntax.Error (_154_505))
in (Prims.raise _154_506))
end else begin
(

let modules = env.modules
in if (FStar_All.pipe_right modules (FStar_Util.for_some (fun _62_773 -> (match (_62_773) with
| (m, _62_772) -> begin
(FStar_Ident.lid_equals m l)
end)))) then begin
(

let _62_774 = env
in {curmodule = _62_774.curmodule; modules = _62_774.modules; open_namespaces = _62_774.open_namespaces; modul_abbrevs = ((x, l))::env.modul_abbrevs; sigaccum = _62_774.sigaccum; localbindings = _62_774.localbindings; recbindings = _62_774.recbindings; sigmap = _62_774.sigmap; default_result_effect = _62_774.default_result_effect; iface = _62_774.iface; admitted_iface = _62_774.admitted_iface; expect_typ = _62_774.expect_typ})
end else begin
(let _154_510 = (let _154_509 = (let _154_508 = (FStar_Util.format1 "Module %s cannot be found" (FStar_Ident.text_of_lid l))
in (_154_508, (FStar_Ident.range_of_lid l)))
in FStar_Syntax_Syntax.Error (_154_509))
in (Prims.raise _154_510))
end)
end)


let check_admits : env  ->  Prims.unit = (fun env -> (FStar_All.pipe_right env.sigaccum (FStar_List.iter (fun se -> (match (se) with
| FStar_Syntax_Syntax.Sig_declare_typ (l, u, t, quals, r) -> begin
(match ((try_lookup_lid env l)) with
| None -> begin
(

let _62_786 = (let _154_516 = (let _154_515 = (FStar_Range.string_of_range (FStar_Ident.range_of_lid l))
in (let _154_514 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format2 "%s: Warning: Admitting %s without a definition\n" _154_515 _154_514)))
in (FStar_Util.print_string _154_516))
in (FStar_Util.smap_add (sigmap env) l.FStar_Ident.str (FStar_Syntax_Syntax.Sig_declare_typ ((l, u, t, (FStar_Syntax_Syntax.Assumption)::quals, r)), false)))
end
| Some (_62_789) -> begin
()
end)
end
| _62_792 -> begin
()
end)))))


let finish : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env modul -> (

let _62_852 = (FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations (FStar_List.iter (fun _62_12 -> (match (_62_12) with
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _62_799, _62_801) -> begin
if ((FStar_List.contains FStar_Syntax_Syntax.Private quals) || (FStar_List.contains FStar_Syntax_Syntax.Abstract quals)) then begin
(FStar_All.pipe_right ses (FStar_List.iter (fun _62_11 -> (match (_62_11) with
| FStar_Syntax_Syntax.Sig_datacon (lid, _62_807, _62_809, _62_811, _62_813, _62_815, _62_817, _62_819) -> begin
(FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str)
end
| _62_823 -> begin
()
end))))
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _62_826, _62_828, quals, _62_831) -> begin
if (FStar_List.contains FStar_Syntax_Syntax.Private quals) then begin
(FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str)
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_let ((_62_835, lbs), r, _62_840, quals) -> begin
(

let _62_845 = if ((FStar_List.contains FStar_Syntax_Syntax.Private quals) || (FStar_List.contains FStar_Syntax_Syntax.Abstract quals)) then begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (let _154_527 = (let _154_526 = (let _154_525 = (let _154_524 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _154_524.FStar_Syntax_Syntax.fv_name)
in _154_525.FStar_Syntax_Syntax.v)
in _154_526.FStar_Ident.str)
in (FStar_Util.smap_remove (sigmap env) _154_527)))))
end else begin
()
end
in if ((FStar_List.contains FStar_Syntax_Syntax.Abstract quals) && (not ((FStar_List.contains FStar_Syntax_Syntax.Private quals)))) then begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (

let lid = (let _154_530 = (let _154_529 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _154_529.FStar_Syntax_Syntax.fv_name)
in _154_530.FStar_Syntax_Syntax.v)
in (

let decl = FStar_Syntax_Syntax.Sig_declare_typ ((lid, lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp, (FStar_Syntax_Syntax.Assumption)::quals, r))
in (FStar_Util.smap_add (sigmap env) lid.FStar_Ident.str (decl, false)))))))
end else begin
()
end)
end
| _62_851 -> begin
()
end))))
in (

let _62_854 = env
in {curmodule = None; modules = ((modul.FStar_Syntax_Syntax.name, modul))::env.modules; open_namespaces = []; modul_abbrevs = []; sigaccum = []; localbindings = []; recbindings = []; sigmap = _62_854.sigmap; default_result_effect = _62_854.default_result_effect; iface = _62_854.iface; admitted_iface = _62_854.admitted_iface; expect_typ = _62_854.expect_typ})))


type env_stack_ops =
{push : env  ->  env; mark : env  ->  env; reset_mark : env  ->  env; commit_mark : env  ->  env; pop : env  ->  env}


let is_Mkenv_stack_ops : env_stack_ops  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv_stack_ops"))))


let stack_ops : env_stack_ops = (

let stack = (FStar_Util.mk_ref [])
in (

let push = (fun env -> (

let _62_865 = (push_record_cache ())
in (

let _62_867 = (let _154_580 = (let _154_579 = (FStar_ST.read stack)
in (env)::_154_579)
in (FStar_ST.op_Colon_Equals stack _154_580))
in (

let _62_869 = env
in (let _154_581 = (FStar_Util.smap_copy (sigmap env))
in {curmodule = _62_869.curmodule; modules = _62_869.modules; open_namespaces = _62_869.open_namespaces; modul_abbrevs = _62_869.modul_abbrevs; sigaccum = _62_869.sigaccum; localbindings = _62_869.localbindings; recbindings = _62_869.recbindings; sigmap = _154_581; default_result_effect = _62_869.default_result_effect; iface = _62_869.iface; admitted_iface = _62_869.admitted_iface; expect_typ = _62_869.expect_typ})))))
in (

let pop = (fun env -> (match ((FStar_ST.read stack)) with
| (env)::tl -> begin
(

let _62_876 = (pop_record_cache ())
in (

let _62_878 = (FStar_ST.op_Colon_Equals stack tl)
in env))
end
| _62_881 -> begin
(FStar_All.failwith "Impossible: Too many pops")
end))
in (

let commit_mark = (fun env -> (

let _62_884 = (commit_record_cache ())
in (match ((FStar_ST.read stack)) with
| (_62_888)::tl -> begin
(

let _62_890 = (FStar_ST.op_Colon_Equals stack tl)
in env)
end
| _62_893 -> begin
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
| (l)::_62_904 -> begin
(l.FStar_Ident.nsstr = m.FStar_Ident.str)
end
| _62_908 -> begin
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

let _62_932 = (FStar_All.pipe_right keys (FStar_List.iter (fun k -> (match ((FStar_Util.smap_try_find sm' k)) with
| Some (se, true) when (sigelt_in_m se) -> begin
(

let _62_918 = (FStar_Util.smap_remove sm' k)
in (

let se = (match (se) with
| FStar_Syntax_Syntax.Sig_declare_typ (l, u, t, q, r) -> begin
FStar_Syntax_Syntax.Sig_declare_typ ((l, u, t, (FStar_Syntax_Syntax.Assumption)::q, r))
end
| _62_928 -> begin
se
end)
in (FStar_Util.smap_add sm' k (se, false))))
end
| _62_931 -> begin
()
end))))
in env)))))))


let finish_module_or_interface : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env modul -> (

let _62_936 = if (not (modul.FStar_Syntax_Syntax.is_interface)) then begin
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

let _62_947 = env
in {curmodule = Some (mname); modules = _62_947.modules; open_namespaces = open_ns; modul_abbrevs = _62_947.modul_abbrevs; sigaccum = _62_947.sigaccum; localbindings = _62_947.localbindings; recbindings = _62_947.recbindings; sigmap = env.sigmap; default_result_effect = if ((FStar_Ident.lid_equals mname FStar_Syntax_Const.all_lid) || (has_all_in_scope env)) then begin
FStar_Syntax_Const.effect_ML_lid
end else begin
FStar_Syntax_Const.effect_Tot_lid
end; iface = intf; admitted_iface = admitted; expect_typ = _62_947.expect_typ}))))
in (match ((FStar_All.pipe_right env.modules (FStar_Util.find_opt (fun _62_952 -> (match (_62_952) with
| (l, _62_951) -> begin
(FStar_Ident.lid_equals l mname)
end))))) with
| None -> begin
(let _154_618 = (prep env)
in (_154_618, false))
end
| Some (_62_955, m) -> begin
(

let _62_959 = if ((not (m.FStar_Syntax_Syntax.is_interface)) || intf) then begin
(let _154_621 = (let _154_620 = (let _154_619 = (FStar_Util.format1 "Duplicate module or interface name: %s" mname.FStar_Ident.str)
in (_154_619, (FStar_Ident.range_of_lid mname)))
in FStar_Syntax_Syntax.Error (_154_620))
in (Prims.raise _154_621))
end else begin
()
end
in (let _154_623 = (let _154_622 = (push env)
in (prep _154_622))
in (_154_623, true)))
end)))


let enter_monad_scope : env  ->  FStar_Ident.ident  ->  env = (fun env mname -> (

let curmod = (current_module env)
in (

let mscope = (FStar_Ident.lid_of_ids (FStar_List.append curmod.FStar_Ident.ns ((curmod.FStar_Ident.ident)::(mname)::[])))
in (

let _62_965 = env
in {curmodule = Some (mscope); modules = _62_965.modules; open_namespaces = (curmod)::env.open_namespaces; modul_abbrevs = _62_965.modul_abbrevs; sigaccum = _62_965.sigaccum; localbindings = _62_965.localbindings; recbindings = _62_965.recbindings; sigmap = _62_965.sigmap; default_result_effect = _62_965.default_result_effect; iface = _62_965.iface; admitted_iface = _62_965.admitted_iface; expect_typ = _62_965.expect_typ}))))


let exit_monad_scope : env  ->  env  ->  env = (fun env0 env -> (

let _62_969 = env
in {curmodule = env0.curmodule; modules = _62_969.modules; open_namespaces = env0.open_namespaces; modul_abbrevs = _62_969.modul_abbrevs; sigaccum = _62_969.sigaccum; localbindings = _62_969.localbindings; recbindings = _62_969.recbindings; sigmap = _62_969.sigmap; default_result_effect = _62_969.default_result_effect; iface = _62_969.iface; admitted_iface = _62_969.admitted_iface; expect_typ = _62_969.expect_typ}))


let fail_or = (fun env lookup lid -> (match ((lookup lid)) with
| None -> begin
(

let opened_modules = (FStar_List.map (fun _62_978 -> (match (_62_978) with
| (lid, _62_977) -> begin
(FStar_Ident.text_of_lid lid)
end)) env.modules)
in (

let module_of_the_lid = (let _154_639 = (FStar_Ident.path_of_ns lid.FStar_Ident.ns)
in (FStar_Ident.text_of_path _154_639))
in (

let msg = (FStar_Util.format1 "Identifier not found: [%s]" (FStar_Ident.text_of_lid lid))
in (

let msg = (match (env.curmodule) with
| Some (m) when (((FStar_Ident.text_of_lid m) = module_of_the_lid) || (module_of_the_lid = "")) -> begin
msg
end
| _62_985 when (FStar_List.existsb (fun m -> (m = module_of_the_lid)) opened_modules) -> begin
msg
end
| _62_988 -> begin
(let _154_643 = (let _154_642 = (let _154_641 = (FStar_Ident.path_of_ns lid.FStar_Ident.ns)
in (FStar_Ident.text_of_path _154_641))
in (FStar_Util.format3 "Hint: %s belongs to module %s, which does not belong to the list of modules in scope, namely %s" (FStar_Ident.text_of_lid lid) _154_642 (FStar_String.concat ", " opened_modules)))
in (Prims.strcat (Prims.strcat msg "\n") _154_643))
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




