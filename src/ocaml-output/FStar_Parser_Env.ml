
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


let qual : FStar_Ident.lident  ->  FStar_Ident.ident  ->  FStar_Ident.lident = (fun lid id -> (let _155_90 = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns ((lid.FStar_Ident.ident)::(id)::[])))
in (FStar_Ident.set_lid_range _155_90 id.FStar_Ident.idRange)))


let qualify : env  ->  FStar_Ident.ident  ->  FStar_Ident.lident = (fun env id -> (let _155_95 = (current_module env)
in (qual _155_95 id)))


let qualify_lid : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (

let cur = (current_module env)
in (let _155_100 = (FStar_Ident.lid_of_ids (FStar_List.append cur.FStar_Ident.ns (FStar_List.append ((cur.FStar_Ident.ident)::[]) (FStar_List.append lid.FStar_Ident.ns ((lid.FStar_Ident.ident)::[])))))
in (FStar_Ident.set_lid_range _155_100 (FStar_Ident.range_of_lid lid)))))


let new_sigmap = (fun _62_52 -> (match (()) with
| () -> begin
(FStar_Util.smap_create (Prims.parse_int "100"))
end))


let empty_env : Prims.unit  ->  env = (fun _62_53 -> (match (()) with
| () -> begin
(let _155_104 = (new_sigmap ())
in {curmodule = None; modules = []; open_namespaces = []; modul_abbrevs = []; sigaccum = []; localbindings = []; recbindings = []; sigmap = _155_104; default_result_effect = FStar_Syntax_Const.effect_Tot_lid; iface = false; admitted_iface = false; expect_typ = false})
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


let unmangleMap : (Prims.string * Prims.string * FStar_Syntax_Syntax.delta_depth * FStar_Syntax_Syntax.fv_qual Prims.option) Prims.list = ((("op_ColonColon"), ("Cons"), (FStar_Syntax_Syntax.Delta_constant), (Some (FStar_Syntax_Syntax.Data_ctor))))::((("not"), ("op_Negation"), (FStar_Syntax_Syntax.Delta_equational), (None)))::[]


let unmangleOpName : FStar_Ident.ident  ->  FStar_Syntax_Syntax.term Prims.option = (fun id -> (FStar_Util.find_map unmangleMap (fun _62_80 -> (match (_62_80) with
| (x, y, dd, dq) -> begin
if (id.FStar_Ident.idText = x) then begin
(let _155_126 = (let _155_125 = (FStar_Ident.lid_of_path (("Prims")::(y)::[]) id.FStar_Ident.idRange)
in (FStar_Syntax_Syntax.fvar _155_125 dd dq))
in Some (_155_126))
end else begin
None
end
end))))


let try_lookup_id : env  ->  FStar_Ident.ident  ->  (FStar_Syntax_Syntax.term * Prims.bool) Prims.option = (fun env id -> (match ((unmangleOpName id)) with
| Some (f) -> begin
Some (((f), (false)))
end
| _62_86 -> begin
(FStar_Util.find_map env.localbindings (fun _62_1 -> (match (_62_1) with
| (id', x, mut) when (id'.FStar_Ident.idText = id.FStar_Ident.idText) -> begin
(let _155_133 = (let _155_132 = (bv_to_name x id.FStar_Ident.idRange)
in ((_155_132), (mut)))
in Some (_155_133))
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
in (let _155_144 = (let _155_143 = (current_module env)
in (_155_143)::env.open_namespaces)
in (aux _155_144))))


let expand_module_abbrev : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (match (lid.FStar_Ident.ns) with
| (_62_112)::_62_110 -> begin
lid
end
| [] -> begin
(

let id = lid.FStar_Ident.ident
in (match ((FStar_List.tryFind (fun _62_119 -> (match (_62_119) with
| (id', _62_118) -> begin
(id.FStar_Ident.idText = id'.FStar_Ident.idText)
end)) env.modul_abbrevs)) with
| None -> begin
lid
end
| Some (_62_122, lid') -> begin
lid'
end))
end))


let expand_module_abbrevs : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (match (lid.FStar_Ident.ns) with
| (id)::rest -> begin
(match ((FStar_All.pipe_right env.modul_abbrevs (FStar_List.tryFind (fun _62_134 -> (match (_62_134) with
| (id', _62_133) -> begin
(id.FStar_Ident.idText = id'.FStar_Ident.idText)
end))))) with
| None -> begin
lid
end
| Some (_62_137, lid') -> begin
(FStar_Ident.lid_of_ids (FStar_List.append (FStar_Ident.ids_of_lid lid') (FStar_List.append rest ((lid.FStar_Ident.ident)::[]))))
end)
end
| _62_142 -> begin
lid
end))


let resolve_in_open_namespaces = (fun env lid finder -> (let _155_161 = (expand_module_abbrevs env lid)
in (resolve_in_open_namespaces' env _155_161 finder)))


let fv_qual_of_se : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.fv_qual Prims.option = (fun _62_3 -> (match (_62_3) with
| FStar_Syntax_Syntax.Sig_datacon (_62_149, _62_151, _62_153, l, _62_156, quals, _62_159, _62_161) -> begin
(

let qopt = (FStar_Util.find_map quals (fun _62_2 -> (match (_62_2) with
| FStar_Syntax_Syntax.RecordConstructor (fs) -> begin
Some (FStar_Syntax_Syntax.Record_ctor (((l), (fs))))
end
| _62_168 -> begin
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
| FStar_Syntax_Syntax.Sig_declare_typ (_62_173, _62_175, _62_177, quals, _62_180) -> begin
None
end
| _62_184 -> begin
None
end))


let lb_fv : FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.fv = (fun lbs lid -> (let _155_170 = (FStar_Util.find_map lbs (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in if (FStar_Syntax_Syntax.fv_eq_lid fv lid) then begin
Some (fv)
end else begin
None
end)))
in (FStar_All.pipe_right _155_170 FStar_Util.must)))


let try_lookup_name : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  foundname Prims.option = (fun any_val exclude_interf env lid -> (

let occurrence_range = (FStar_Ident.range_of_lid lid)
in (

let find_in_sig = (fun lid -> (match ((FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str)) with
| Some (_62_197, true) when exclude_interf -> begin
None
end
| None -> begin
None
end
| Some (se, _62_204) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_62_208) -> begin
(let _155_183 = (let _155_182 = (let _155_181 = (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.Delta_constant None)
in ((_155_181), (false)))
in Term_name (_155_182))
in Some (_155_183))
end
| FStar_Syntax_Syntax.Sig_datacon (_62_211) -> begin
(let _155_187 = (let _155_186 = (let _155_185 = (let _155_184 = (fv_qual_of_se se)
in (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.Delta_constant _155_184))
in ((_155_185), (false)))
in Term_name (_155_186))
in Some (_155_187))
end
| FStar_Syntax_Syntax.Sig_let ((_62_214, lbs), _62_218, _62_220, _62_222) -> begin
(

let fv = (lb_fv lbs lid)
in (let _155_190 = (let _155_189 = (let _155_188 = (FStar_Syntax_Syntax.fvar lid fv.FStar_Syntax_Syntax.fv_delta fv.FStar_Syntax_Syntax.fv_qual)
in ((_155_188), (false)))
in Term_name (_155_189))
in Some (_155_190)))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _62_228, _62_230, quals, _62_233) -> begin
if (any_val || (FStar_All.pipe_right quals (FStar_Util.for_some (fun _62_4 -> (match (_62_4) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| _62_239 -> begin
false
end))))) then begin
(

let dd = if ((FStar_Syntax_Util.is_primop_lid lid) || ((FStar_Util.starts_with lid.FStar_Ident.nsstr "Prims.") && (FStar_All.pipe_right quals (FStar_Util.for_some (fun _62_5 -> (match (_62_5) with
| (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) -> begin
true
end
| _62_248 -> begin
false
end)))))) then begin
FStar_Syntax_Syntax.Delta_equational
end else begin
FStar_Syntax_Syntax.Delta_constant
end
in if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Reflectable)) then begin
(

let refl_monad = (let _155_194 = (FStar_All.pipe_right lid.FStar_Ident.ns (FStar_List.map (fun x -> x.FStar_Ident.idText)))
in (FStar_Ident.lid_of_path _155_194 occurrence_range))
in (

let refl_const = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (refl_monad))) None occurrence_range)
in Some (Term_name (((refl_const), (false))))))
end else begin
(let _155_198 = (let _155_197 = (let _155_196 = (let _155_195 = (fv_qual_of_se se)
in (FStar_Syntax_Syntax.fvar lid dd _155_195))
in ((_155_196), (false)))
in Term_name (_155_197))
in Some (_155_198))
end)
end else begin
None
end
end
| (FStar_Syntax_Syntax.Sig_new_effect_for_free (ne, _)) | (FStar_Syntax_Syntax.Sig_new_effect (ne, _)) -> begin
(let _155_201 = (let _155_200 = (let _155_199 = (FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname (FStar_Ident.range_of_lid lid))
in ((se), (_155_199)))
in Eff_name (_155_200))
in Some (_155_201))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (_62_263) -> begin
Some (Eff_name (((se), (lid))))
end
| _62_266 -> begin
None
end)
end))
in (

let found_id = (match (lid.FStar_Ident.ns) with
| [] -> begin
(match ((try_lookup_id env lid.FStar_Ident.ident)) with
| Some (e, mut) -> begin
Some (Term_name (((e), (mut))))
end
| None -> begin
(

let recname = (qualify env lid.FStar_Ident.ident)
in (FStar_Util.find_map env.recbindings (fun _62_277 -> (match (_62_277) with
| (id, l, dd) -> begin
if (id.FStar_Ident.idText = lid.FStar_Ident.ident.FStar_Ident.idText) then begin
(let _155_206 = (let _155_205 = (let _155_204 = (let _155_203 = (FStar_Ident.set_lid_range l (FStar_Ident.range_of_lid lid))
in (FStar_Syntax_Syntax.fvar _155_203 dd None))
in ((_155_204), (false)))
in Term_name (_155_205))
in Some (_155_206))
end else begin
None
end
end))))
end)
end
| _62_279 -> begin
None
end)
in (match (found_id) with
| Some (_62_282) -> begin
found_id
end
| _62_285 -> begin
(resolve_in_open_namespaces env lid find_in_sig)
end)))))


let try_lookup_effect_name' : Prims.bool  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident) Prims.option = (fun exclude_interf env lid -> (match ((try_lookup_name true exclude_interf env lid)) with
| Some (Eff_name (o, l)) -> begin
Some (((o), (l)))
end
| _62_295 -> begin
None
end))


let try_lookup_effect_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env l -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some (o, l) -> begin
Some (l)
end
| _62_303 -> begin
None
end))


let try_lookup_effect_defn : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl Prims.option = (fun env l -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some (FStar_Syntax_Syntax.Sig_new_effect (ne, _62_308), _62_312) -> begin
Some (ne)
end
| Some (FStar_Syntax_Syntax.Sig_new_effect_for_free (ne, _62_317), _62_321) -> begin
Some (ne)
end
| _62_325 -> begin
None
end))


let is_effect_name : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((try_lookup_effect_name env lid)) with
| None -> begin
false
end
| Some (_62_330) -> begin
true
end))


let lookup_letbinding_quals : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.qualifier Prims.list = (fun env lid -> (

let find_in_sig = (fun lid -> (match ((FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str)) with
| Some (FStar_Syntax_Syntax.Sig_declare_typ (lid, _62_338, _62_340, quals, _62_343), _62_347) -> begin
Some (quals)
end
| _62_351 -> begin
None
end))
in (match ((resolve_in_open_namespaces env lid find_in_sig)) with
| Some (quals) -> begin
quals
end
| _62_355 -> begin
[]
end)))


let try_lookup_module : env  ->  Prims.string Prims.list  ->  FStar_Syntax_Syntax.modul Prims.option = (fun env path -> (match ((FStar_List.tryFind (fun _62_360 -> (match (_62_360) with
| (mlid, modul) -> begin
((FStar_Ident.path_of_lid mlid) = path)
end)) env.modules)) with
| Some (_62_362, modul) -> begin
Some (modul)
end
| None -> begin
None
end))


let try_lookup_let : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env lid -> (

let find_in_sig = (fun lid -> (match ((FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str)) with
| Some (FStar_Syntax_Syntax.Sig_let ((_62_372, lbs), _62_376, _62_378, _62_380), _62_384) -> begin
(

let fv = (lb_fv lbs lid)
in (let _155_242 = (FStar_Syntax_Syntax.fvar lid fv.FStar_Syntax_Syntax.fv_delta fv.FStar_Syntax_Syntax.fv_qual)
in Some (_155_242)))
end
| _62_389 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))


let try_lookup_definition : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env lid -> (

let find_in_sig = (fun lid -> (match ((FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str)) with
| Some (FStar_Syntax_Syntax.Sig_let (lbs, _62_396, _62_398, _62_400), _62_404) -> begin
(FStar_Util.find_map (Prims.snd lbs) (fun lb -> (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv lid) -> begin
Some (lb.FStar_Syntax_Syntax.lbdef)
end
| _62_411 -> begin
None
end)))
end
| _62_413 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))


let try_lookup_lid' : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term * Prims.bool) Prims.option = (fun any_val exclude_interf env lid -> (match ((try_lookup_name any_val exclude_interf env lid)) with
| Some (Term_name (e, mut)) -> begin
Some (((e), (mut)))
end
| _62_424 -> begin
None
end))


let try_lookup_lid : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term * Prims.bool) Prims.option = (fun env l -> (try_lookup_lid' env.iface false env l))


let try_lookup_datacon : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.fv Prims.option = (fun env lid -> (

let find_in_sig = (fun lid -> (match ((FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str)) with
| Some (FStar_Syntax_Syntax.Sig_declare_typ (_62_432, _62_434, _62_436, quals, _62_439), _62_443) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _62_6 -> (match (_62_6) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| _62_449 -> begin
false
end)))) then begin
(let _155_269 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant None)
in Some (_155_269))
end else begin
None
end
end
| Some (FStar_Syntax_Syntax.Sig_datacon (_62_451), _62_454) -> begin
(let _155_270 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in Some (_155_270))
end
| _62_458 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))


let find_all_datacons : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.list Prims.option = (fun env lid -> (

let find_in_sig = (fun lid -> (match ((FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str)) with
| Some (FStar_Syntax_Syntax.Sig_inductive_typ (_62_464, _62_466, _62_468, _62_470, _62_472, datas, _62_475, _62_477), _62_481) -> begin
Some (datas)
end
| _62_485 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))


let record_cache_aux : ((Prims.unit  ->  Prims.unit) * (Prims.unit  ->  Prims.unit) * (Prims.unit  ->  record_or_dc Prims.list) * (record_or_dc  ->  Prims.unit) * (Prims.unit  ->  Prims.unit)) = (

let record_cache = (FStar_Util.mk_ref (([])::[]))
in (

let push = (fun _62_488 -> (match (()) with
| () -> begin
(let _155_292 = (let _155_291 = (let _155_289 = (FStar_ST.read record_cache)
in (FStar_List.hd _155_289))
in (let _155_290 = (FStar_ST.read record_cache)
in (_155_291)::_155_290))
in (FStar_ST.op_Colon_Equals record_cache _155_292))
end))
in (

let pop = (fun _62_490 -> (match (()) with
| () -> begin
(let _155_296 = (let _155_295 = (FStar_ST.read record_cache)
in (FStar_List.tl _155_295))
in (FStar_ST.op_Colon_Equals record_cache _155_296))
end))
in (

let peek = (fun _62_492 -> (match (()) with
| () -> begin
(let _155_299 = (FStar_ST.read record_cache)
in (FStar_List.hd _155_299))
end))
in (

let insert = (fun r -> (let _155_306 = (let _155_305 = (let _155_302 = (peek ())
in (r)::_155_302)
in (let _155_304 = (let _155_303 = (FStar_ST.read record_cache)
in (FStar_List.tl _155_303))
in (_155_305)::_155_304))
in (FStar_ST.op_Colon_Equals record_cache _155_306)))
in (

let commit = (fun _62_496 -> (match (()) with
| () -> begin
(match ((FStar_ST.read record_cache)) with
| (hd)::(_62_499)::tl -> begin
(FStar_ST.op_Colon_Equals record_cache ((hd)::tl))
end
| _62_504 -> begin
(FStar_All.failwith "Impossible")
end)
end))
in ((push), (pop), (peek), (insert), (commit))))))))


let push_record_cache : Prims.unit  ->  Prims.unit = (

let _62_514 = record_cache_aux
in (match (_62_514) with
| (push, _62_507, _62_509, _62_511, _62_513) -> begin
push
end))


let pop_record_cache : Prims.unit  ->  Prims.unit = (

let _62_524 = record_cache_aux
in (match (_62_524) with
| (_62_516, pop, _62_519, _62_521, _62_523) -> begin
pop
end))


let peek_record_cache : Prims.unit  ->  record_or_dc Prims.list = (

let _62_534 = record_cache_aux
in (match (_62_534) with
| (_62_526, _62_528, peek, _62_531, _62_533) -> begin
peek
end))


let insert_record_cache : record_or_dc  ->  Prims.unit = (

let _62_544 = record_cache_aux
in (match (_62_544) with
| (_62_536, _62_538, _62_540, insert, _62_543) -> begin
insert
end))


let commit_record_cache : Prims.unit  ->  Prims.unit = (

let _62_554 = record_cache_aux
in (match (_62_554) with
| (_62_546, _62_548, _62_550, _62_552, commit) -> begin
commit
end))


let extract_record : env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun e _62_10 -> (match (_62_10) with
| FStar_Syntax_Syntax.Sig_bundle (sigs, _62_559, _62_561, _62_563) -> begin
(

let is_rec = (FStar_Util.for_some (fun _62_7 -> (match (_62_7) with
| (FStar_Syntax_Syntax.RecordType (_)) | (FStar_Syntax_Syntax.RecordConstructor (_)) -> begin
true
end
| _62_574 -> begin
false
end)))
in (

let find_dc = (fun dc -> (FStar_All.pipe_right sigs (FStar_Util.find_opt (fun _62_8 -> (match (_62_8) with
| FStar_Syntax_Syntax.Sig_datacon (lid, _62_581, _62_583, _62_585, _62_587, _62_589, _62_591, _62_593) -> begin
(FStar_Ident.lid_equals dc lid)
end
| _62_597 -> begin
false
end)))))
in (FStar_All.pipe_right sigs (FStar_List.iter (fun _62_9 -> (match (_62_9) with
| FStar_Syntax_Syntax.Sig_inductive_typ (typename, univs, parms, _62_603, _62_605, (dc)::[], tags, _62_610) -> begin
(match ((let _155_409 = (find_dc dc)
in (FStar_All.pipe_left FStar_Util.must _155_409))) with
| FStar_Syntax_Syntax.Sig_datacon (constrname, _62_615, t, _62_618, _62_620, _62_622, _62_624, _62_626) -> begin
(

let _62_632 = (FStar_Syntax_Util.arrow_formals t)
in (match (_62_632) with
| (formals, _62_631) -> begin
(

let is_rec = (is_rec tags)
in (

let fields = (FStar_All.pipe_right formals (FStar_List.collect (fun _62_636 -> (match (_62_636) with
| (x, q) -> begin
if ((FStar_Syntax_Syntax.is_null_bv x) || (is_rec && (FStar_Syntax_Syntax.is_implicit q))) then begin
[]
end else begin
(let _155_413 = (let _155_412 = (let _155_411 = if is_rec then begin
(FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname)
end else begin
x.FStar_Syntax_Syntax.ppname
end
in (qual constrname _155_411))
in ((_155_412), (x.FStar_Syntax_Syntax.sort)))
in (_155_413)::[])
end
end))))
in (

let record = {typename = typename; constrname = constrname; parms = parms; fields = fields; is_record = is_rec}
in (insert_record_cache record))))
end))
end
| _62_640 -> begin
()
end)
end
| _62_642 -> begin
()
end))))))
end
| _62_644 -> begin
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
(let _155_424 = (aux tl)
in (hd)::_155_424)
end))
in (aux ns)))
in (

let find_in_cache = (fun fieldname -> (

let _62_662 = ((fieldname.FStar_Ident.ns), (fieldname.FStar_Ident.ident))
in (match (_62_662) with
| (ns, fieldname) -> begin
(let _155_429 = (peek_record_cache ())
in (FStar_Util.find_map _155_429 (fun record -> (

let constrname = record.constrname.FStar_Ident.ident
in (

let ns = (maybe_add_constrname ns constrname)
in (

let fname = (FStar_Ident.lid_of_ids (FStar_List.append ns ((fieldname)::[])))
in (FStar_Util.find_map record.fields (fun _62_670 -> (match (_62_670) with
| (f, _62_669) -> begin
if (FStar_Ident.lid_equals fname f) then begin
Some (((record), (fname)))
end else begin
None
end
end)))))))))
end)))
in (resolve_in_open_namespaces env fieldname find_in_cache))))


let try_lookup_record_by_field_name : env  ->  FStar_Ident.lident  ->  (record_or_dc * FStar_Ident.lident) Prims.option = (fun env fieldname -> (match ((try_lookup_record_or_dc_by_field_name env fieldname)) with
| Some (r, f) when r.is_record -> begin
Some (((r), (f)))
end
| _62_678 -> begin
None
end))


let try_lookup_projector_by_field_name : env  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * Prims.bool) Prims.option = (fun env fieldname -> (match ((try_lookup_record_or_dc_by_field_name env fieldname)) with
| Some (r, f) -> begin
Some (((f), (r.is_record)))
end
| _62_686 -> begin
None
end))


let qualify_field_to_record : env  ->  record_or_dc  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env recd f -> (

let qualify = (fun fieldname -> (

let _62_694 = ((fieldname.FStar_Ident.ns), (fieldname.FStar_Ident.ident))
in (match (_62_694) with
| (ns, fieldname) -> begin
(

let constrname = recd.constrname.FStar_Ident.ident
in (

let fname = (FStar_Ident.lid_of_ids (FStar_List.append ns (FStar_List.append ((constrname)::[]) ((fieldname)::[]))))
in (FStar_Util.find_map recd.fields (fun _62_700 -> (match (_62_700) with
| (f, _62_699) -> begin
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

let _62_705 = env
in {curmodule = _62_705.curmodule; modules = _62_705.modules; open_namespaces = []; modul_abbrevs = _62_705.modul_abbrevs; sigaccum = _62_705.sigaccum; localbindings = _62_705.localbindings; recbindings = _62_705.recbindings; sigmap = _62_705.sigmap; default_result_effect = _62_705.default_result_effect; iface = _62_705.iface; admitted_iface = _62_705.admitted_iface; expect_typ = _62_705.expect_typ})
in (match ((try_lookup_lid' any_val exclude_if env lid)) with
| None -> begin
true
end
| Some (_62_710) -> begin
false
end)))


let push_bv' : env  ->  FStar_Ident.ident  ->  Prims.bool  ->  (env * FStar_Syntax_Syntax.bv) = (fun env x is_mutable -> (

let bv = (FStar_Syntax_Syntax.gen_bv x.FStar_Ident.idText (Some (x.FStar_Ident.idRange)) FStar_Syntax_Syntax.tun)
in (((

let _62_716 = env
in {curmodule = _62_716.curmodule; modules = _62_716.modules; open_namespaces = _62_716.open_namespaces; modul_abbrevs = _62_716.modul_abbrevs; sigaccum = _62_716.sigaccum; localbindings = (((x), (bv), (is_mutable)))::env.localbindings; recbindings = _62_716.recbindings; sigmap = _62_716.sigmap; default_result_effect = _62_716.default_result_effect; iface = _62_716.iface; admitted_iface = _62_716.admitted_iface; expect_typ = _62_716.expect_typ})), (bv))))


let push_bv_mutable : env  ->  FStar_Ident.ident  ->  (env * FStar_Syntax_Syntax.bv) = (fun env x -> (push_bv' env x true))


let push_bv : env  ->  FStar_Ident.ident  ->  (env * FStar_Syntax_Syntax.bv) = (fun env x -> (push_bv' env x false))


let push_top_level_rec_binding : env  ->  FStar_Ident.ident  ->  FStar_Syntax_Syntax.delta_depth  ->  env = (fun env x dd -> (

let l = (qualify env x)
in if (unique false true env l) then begin
(

let _62_726 = env
in {curmodule = _62_726.curmodule; modules = _62_726.modules; open_namespaces = _62_726.open_namespaces; modul_abbrevs = _62_726.modul_abbrevs; sigaccum = _62_726.sigaccum; localbindings = _62_726.localbindings; recbindings = (((x), (l), (dd)))::env.recbindings; sigmap = _62_726.sigmap; default_result_effect = _62_726.default_result_effect; iface = _62_726.iface; admitted_iface = _62_726.admitted_iface; expect_typ = _62_726.expect_typ})
end else begin
(Prims.raise (FStar_Syntax_Syntax.Error ((((Prims.strcat "Duplicate top-level names " l.FStar_Ident.str)), ((FStar_Ident.range_of_lid l))))))
end))


let push_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env s -> (

let err = (fun l -> (

let sopt = (FStar_Util.smap_try_find (sigmap env) l.FStar_Ident.str)
in (

let r = (match (sopt) with
| Some (se, _62_735) -> begin
(match ((let _155_481 = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_Util.find_opt (FStar_Ident.lid_equals l) _155_481))) with
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
in (let _155_484 = (let _155_483 = (let _155_482 = (FStar_Util.format2 "Duplicate top-level names [%s]; previously declared at %s" (FStar_Ident.text_of_lid l) r)
in ((_155_482), ((FStar_Ident.range_of_lid l))))
in FStar_Syntax_Syntax.Error (_155_483))
in (Prims.raise _155_484)))))
in (

let env = (

let _62_753 = (match (s) with
| FStar_Syntax_Syntax.Sig_let (_62_744) -> begin
((false), (true))
end
| FStar_Syntax_Syntax.Sig_bundle (_62_747) -> begin
((true), (true))
end
| _62_750 -> begin
((false), (false))
end)
in (match (_62_753) with
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

let _62_757 = (extract_record env s)
in (

let _62_759 = env
in {curmodule = _62_759.curmodule; modules = _62_759.modules; open_namespaces = _62_759.open_namespaces; modul_abbrevs = _62_759.modul_abbrevs; sigaccum = (s)::env.sigaccum; localbindings = _62_759.localbindings; recbindings = _62_759.recbindings; sigmap = _62_759.sigmap; default_result_effect = _62_759.default_result_effect; iface = _62_759.iface; admitted_iface = _62_759.admitted_iface; expect_typ = _62_759.expect_typ}))
end
| Some (l) -> begin
(err l)
end))
end))
in (

let _62_778 = (match (s) with
| FStar_Syntax_Syntax.Sig_bundle (ses, _62_766, _62_768, _62_770) -> begin
(let _155_488 = (FStar_List.map (fun se -> (let _155_487 = (FStar_Syntax_Util.lids_of_sigelt se)
in ((_155_487), (se)))) ses)
in ((env), (_155_488)))
end
| _62_775 -> begin
(let _155_491 = (let _155_490 = (let _155_489 = (FStar_Syntax_Util.lids_of_sigelt s)
in ((_155_489), (s)))
in (_155_490)::[])
in ((env), (_155_491)))
end)
in (match (_62_778) with
| (env, lss) -> begin
(

let _62_783 = (FStar_All.pipe_right lss (FStar_List.iter (fun _62_781 -> (match (_62_781) with
| (lids, se) -> begin
(FStar_All.pipe_right lids (FStar_List.iter (fun lid -> (FStar_Util.smap_add (sigmap env) lid.FStar_Ident.str ((se), ((env.iface && (not (env.admitted_iface)))))))))
end))))
in env)
end)))))


let push_namespace : env  ->  FStar_Ident.lident  ->  env = (fun env ns -> (

let modules = env.modules
in if (FStar_All.pipe_right modules (FStar_Util.for_some (fun _62_791 -> (match (_62_791) with
| (m, _62_790) -> begin
(FStar_Util.starts_with (FStar_Ident.text_of_lid m) (FStar_Ident.text_of_lid ns))
end)))) then begin
(

let _62_792 = env
in {curmodule = _62_792.curmodule; modules = _62_792.modules; open_namespaces = (ns)::env.open_namespaces; modul_abbrevs = _62_792.modul_abbrevs; sigaccum = _62_792.sigaccum; localbindings = _62_792.localbindings; recbindings = _62_792.recbindings; sigmap = _62_792.sigmap; default_result_effect = _62_792.default_result_effect; iface = _62_792.iface; admitted_iface = _62_792.admitted_iface; expect_typ = _62_792.expect_typ})
end else begin
(let _155_501 = (let _155_500 = (let _155_499 = (FStar_Util.format1 "Namespace %s cannot be found" (FStar_Ident.text_of_lid ns))
in ((_155_499), ((FStar_Ident.range_of_lid ns))))
in FStar_Syntax_Syntax.Error (_155_500))
in (Prims.raise _155_501))
end))


let push_module_abbrev : env  ->  FStar_Ident.ident  ->  FStar_Ident.lident  ->  env = (fun env x l -> if (FStar_All.pipe_right env.modul_abbrevs (FStar_Util.for_some (fun _62_800 -> (match (_62_800) with
| (y, _62_799) -> begin
(x.FStar_Ident.idText = y.FStar_Ident.idText)
end)))) then begin
(let _155_511 = (let _155_510 = (let _155_509 = (FStar_Util.format1 "Module %s is already defined" x.FStar_Ident.idText)
in ((_155_509), (x.FStar_Ident.idRange)))
in FStar_Syntax_Syntax.Error (_155_510))
in (Prims.raise _155_511))
end else begin
(

let modules = env.modules
in if (FStar_All.pipe_right modules (FStar_Util.for_some (fun _62_805 -> (match (_62_805) with
| (m, _62_804) -> begin
(FStar_Ident.lid_equals m l)
end)))) then begin
(

let _62_806 = env
in {curmodule = _62_806.curmodule; modules = _62_806.modules; open_namespaces = _62_806.open_namespaces; modul_abbrevs = (((x), (l)))::env.modul_abbrevs; sigaccum = _62_806.sigaccum; localbindings = _62_806.localbindings; recbindings = _62_806.recbindings; sigmap = _62_806.sigmap; default_result_effect = _62_806.default_result_effect; iface = _62_806.iface; admitted_iface = _62_806.admitted_iface; expect_typ = _62_806.expect_typ})
end else begin
(let _155_515 = (let _155_514 = (let _155_513 = (FStar_Util.format1 "Module %s cannot be found" (FStar_Ident.text_of_lid l))
in ((_155_513), ((FStar_Ident.range_of_lid l))))
in FStar_Syntax_Syntax.Error (_155_514))
in (Prims.raise _155_515))
end)
end)


let check_admits : env  ->  Prims.unit = (fun env -> (FStar_All.pipe_right env.sigaccum (FStar_List.iter (fun se -> (match (se) with
| FStar_Syntax_Syntax.Sig_declare_typ (l, u, t, quals, r) -> begin
(match ((try_lookup_lid env l)) with
| None -> begin
(

let _62_818 = (let _155_521 = (let _155_520 = (FStar_Range.string_of_range (FStar_Ident.range_of_lid l))
in (let _155_519 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format2 "%s: Warning: Admitting %s without a definition\n" _155_520 _155_519)))
in (FStar_Util.print_string _155_521))
in (FStar_Util.smap_add (sigmap env) l.FStar_Ident.str ((FStar_Syntax_Syntax.Sig_declare_typ (((l), (u), (t), ((FStar_Syntax_Syntax.Assumption)::quals), (r)))), (false))))
end
| Some (_62_821) -> begin
()
end)
end
| _62_824 -> begin
()
end)))))


let finish : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env modul -> (

let _62_884 = (FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations (FStar_List.iter (fun _62_12 -> (match (_62_12) with
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _62_831, _62_833) -> begin
if ((FStar_List.contains FStar_Syntax_Syntax.Private quals) || (FStar_List.contains FStar_Syntax_Syntax.Abstract quals)) then begin
(FStar_All.pipe_right ses (FStar_List.iter (fun _62_11 -> (match (_62_11) with
| FStar_Syntax_Syntax.Sig_datacon (lid, _62_839, _62_841, _62_843, _62_845, _62_847, _62_849, _62_851) -> begin
(FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str)
end
| _62_855 -> begin
()
end))))
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _62_858, _62_860, quals, _62_863) -> begin
if (FStar_List.contains FStar_Syntax_Syntax.Private quals) then begin
(FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str)
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_let ((_62_867, lbs), r, _62_872, quals) -> begin
(

let _62_877 = if ((FStar_List.contains FStar_Syntax_Syntax.Private quals) || (FStar_List.contains FStar_Syntax_Syntax.Abstract quals)) then begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (let _155_532 = (let _155_531 = (let _155_530 = (let _155_529 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _155_529.FStar_Syntax_Syntax.fv_name)
in _155_530.FStar_Syntax_Syntax.v)
in _155_531.FStar_Ident.str)
in (FStar_Util.smap_remove (sigmap env) _155_532)))))
end else begin
()
end
in if ((FStar_List.contains FStar_Syntax_Syntax.Abstract quals) && (not ((FStar_List.contains FStar_Syntax_Syntax.Private quals)))) then begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (

let lid = (let _155_535 = (let _155_534 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _155_534.FStar_Syntax_Syntax.fv_name)
in _155_535.FStar_Syntax_Syntax.v)
in (

let decl = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), ((FStar_Syntax_Syntax.Assumption)::quals), (r)))
in (FStar_Util.smap_add (sigmap env) lid.FStar_Ident.str ((decl), (false))))))))
end else begin
()
end)
end
| _62_883 -> begin
()
end))))
in (

let _62_886 = env
in {curmodule = None; modules = (((modul.FStar_Syntax_Syntax.name), (modul)))::env.modules; open_namespaces = []; modul_abbrevs = []; sigaccum = []; localbindings = []; recbindings = []; sigmap = _62_886.sigmap; default_result_effect = _62_886.default_result_effect; iface = _62_886.iface; admitted_iface = _62_886.admitted_iface; expect_typ = _62_886.expect_typ})))


type env_stack_ops =
{push : env  ->  env; mark : env  ->  env; reset_mark : env  ->  env; commit_mark : env  ->  env; pop : env  ->  env}


let is_Mkenv_stack_ops : env_stack_ops  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv_stack_ops"))))


let stack_ops : env_stack_ops = (

let stack = (FStar_Util.mk_ref [])
in (

let push = (fun env -> (

let _62_897 = (push_record_cache ())
in (

let _62_899 = (let _155_585 = (let _155_584 = (FStar_ST.read stack)
in (env)::_155_584)
in (FStar_ST.op_Colon_Equals stack _155_585))
in (

let _62_901 = env
in (let _155_586 = (FStar_Util.smap_copy (sigmap env))
in {curmodule = _62_901.curmodule; modules = _62_901.modules; open_namespaces = _62_901.open_namespaces; modul_abbrevs = _62_901.modul_abbrevs; sigaccum = _62_901.sigaccum; localbindings = _62_901.localbindings; recbindings = _62_901.recbindings; sigmap = _155_586; default_result_effect = _62_901.default_result_effect; iface = _62_901.iface; admitted_iface = _62_901.admitted_iface; expect_typ = _62_901.expect_typ})))))
in (

let pop = (fun env -> (match ((FStar_ST.read stack)) with
| (env)::tl -> begin
(

let _62_908 = (pop_record_cache ())
in (

let _62_910 = (FStar_ST.op_Colon_Equals stack tl)
in env))
end
| _62_913 -> begin
(FStar_All.failwith "Impossible: Too many pops")
end))
in (

let commit_mark = (fun env -> (

let _62_916 = (commit_record_cache ())
in (match ((FStar_ST.read stack)) with
| (_62_920)::tl -> begin
(

let _62_922 = (FStar_ST.op_Colon_Equals stack tl)
in env)
end
| _62_925 -> begin
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
| (l)::_62_936 -> begin
(l.FStar_Ident.nsstr = m.FStar_Ident.str)
end
| _62_940 -> begin
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

let _62_964 = (FStar_All.pipe_right keys (FStar_List.iter (fun k -> (match ((FStar_Util.smap_try_find sm' k)) with
| Some (se, true) when (sigelt_in_m se) -> begin
(

let _62_950 = (FStar_Util.smap_remove sm' k)
in (

let se = (match (se) with
| FStar_Syntax_Syntax.Sig_declare_typ (l, u, t, q, r) -> begin
FStar_Syntax_Syntax.Sig_declare_typ (((l), (u), (t), ((FStar_Syntax_Syntax.Assumption)::q), (r)))
end
| _62_960 -> begin
se
end)
in (FStar_Util.smap_add sm' k ((se), (false)))))
end
| _62_963 -> begin
()
end))))
in env)))))))


let finish_module_or_interface : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env modul -> (

let _62_968 = if (not (modul.FStar_Syntax_Syntax.is_interface)) then begin
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

let open_ns = if ((FStar_List.length mname.FStar_Ident.ns) <> (Prims.parse_int "0")) then begin
(

let ns = (FStar_Ident.lid_of_ids mname.FStar_Ident.ns)
in (ns)::open_ns)
end else begin
open_ns
end
in (

let _62_979 = env
in {curmodule = Some (mname); modules = _62_979.modules; open_namespaces = open_ns; modul_abbrevs = _62_979.modul_abbrevs; sigaccum = _62_979.sigaccum; localbindings = _62_979.localbindings; recbindings = _62_979.recbindings; sigmap = env.sigmap; default_result_effect = if ((FStar_Ident.lid_equals mname FStar_Syntax_Const.all_lid) || (has_all_in_scope env)) then begin
FStar_Syntax_Const.effect_ML_lid
end else begin
FStar_Syntax_Const.effect_Tot_lid
end; iface = intf; admitted_iface = admitted; expect_typ = _62_979.expect_typ}))))
in (match ((FStar_All.pipe_right env.modules (FStar_Util.find_opt (fun _62_984 -> (match (_62_984) with
| (l, _62_983) -> begin
(FStar_Ident.lid_equals l mname)
end))))) with
| None -> begin
(let _155_623 = (prep env)
in ((_155_623), (false)))
end
| Some (_62_987, m) -> begin
(

let _62_991 = if ((not (m.FStar_Syntax_Syntax.is_interface)) || intf) then begin
(let _155_626 = (let _155_625 = (let _155_624 = (FStar_Util.format1 "Duplicate module or interface name: %s" mname.FStar_Ident.str)
in ((_155_624), ((FStar_Ident.range_of_lid mname))))
in FStar_Syntax_Syntax.Error (_155_625))
in (Prims.raise _155_626))
end else begin
()
end
in (let _155_628 = (let _155_627 = (push env)
in (prep _155_627))
in ((_155_628), (true))))
end)))


let enter_monad_scope : env  ->  FStar_Ident.ident  ->  env = (fun env mname -> (

let curmod = (current_module env)
in (

let mscope = (FStar_Ident.lid_of_ids (FStar_List.append curmod.FStar_Ident.ns ((curmod.FStar_Ident.ident)::(mname)::[])))
in (

let _62_997 = env
in {curmodule = Some (mscope); modules = _62_997.modules; open_namespaces = (curmod)::env.open_namespaces; modul_abbrevs = _62_997.modul_abbrevs; sigaccum = _62_997.sigaccum; localbindings = _62_997.localbindings; recbindings = _62_997.recbindings; sigmap = _62_997.sigmap; default_result_effect = _62_997.default_result_effect; iface = _62_997.iface; admitted_iface = _62_997.admitted_iface; expect_typ = _62_997.expect_typ}))))


let exit_monad_scope : env  ->  env  ->  env = (fun env0 env -> (

let _62_1001 = env
in {curmodule = env0.curmodule; modules = _62_1001.modules; open_namespaces = env0.open_namespaces; modul_abbrevs = _62_1001.modul_abbrevs; sigaccum = _62_1001.sigaccum; localbindings = _62_1001.localbindings; recbindings = _62_1001.recbindings; sigmap = _62_1001.sigmap; default_result_effect = _62_1001.default_result_effect; iface = _62_1001.iface; admitted_iface = _62_1001.admitted_iface; expect_typ = _62_1001.expect_typ}))


let fail_or = (fun env lookup lid -> (match ((lookup lid)) with
| None -> begin
(

let opened_modules = (FStar_List.map (fun _62_1010 -> (match (_62_1010) with
| (lid, _62_1009) -> begin
(FStar_Ident.text_of_lid lid)
end)) env.modules)
in (

let module_of_the_lid = (let _155_644 = (FStar_Ident.path_of_ns lid.FStar_Ident.ns)
in (FStar_Ident.text_of_path _155_644))
in (

let msg = (FStar_Util.format1 "Identifier not found: [%s]" (FStar_Ident.text_of_lid lid))
in (

let msg = (match (env.curmodule) with
| Some (m) when (((FStar_Ident.text_of_lid m) = module_of_the_lid) || (module_of_the_lid = "")) -> begin
msg
end
| _62_1017 when (FStar_List.existsb (fun m -> (m = module_of_the_lid)) opened_modules) -> begin
msg
end
| _62_1020 -> begin
(let _155_649 = (let _155_648 = (let _155_647 = (let _155_646 = (FStar_Ident.path_of_ns lid.FStar_Ident.ns)
in (FStar_Ident.text_of_path _155_646))
in (FStar_Util.format3 "Hint: %s belongs to module %s, which does not belong to the list of modules in scope, namely %s" (FStar_Ident.text_of_lid lid) _155_647 (FStar_String.concat ", " opened_modules)))
in (Prims.strcat "\n" _155_648))
in (Prims.strcat msg _155_649))
end)
in (Prims.raise (FStar_Syntax_Syntax.Error (((msg), ((FStar_Ident.range_of_lid lid))))))))))
end
| Some (r) -> begin
r
end))


let fail_or2 = (fun lookup id -> (match ((lookup id)) with
| None -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((((Prims.strcat "Identifier not found [" (Prims.strcat id.FStar_Ident.idText "]"))), (id.FStar_Ident.idRange)))))
end
| Some (r) -> begin
r
end))




