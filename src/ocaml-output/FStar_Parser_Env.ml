
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
| Term_name (_63_28) -> begin
_63_28
end))


let ___Eff_name____0 = (fun projectee -> (match (projectee) with
| Eff_name (_63_31) -> begin
_63_31
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


let qual : FStar_Ident.lident  ->  FStar_Ident.ident  ->  FStar_Ident.lident = (fun lid id -> (let _160_90 = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns ((lid.FStar_Ident.ident)::(id)::[])))
in (FStar_Ident.set_lid_range _160_90 id.FStar_Ident.idRange)))


let qualify : env  ->  FStar_Ident.ident  ->  FStar_Ident.lident = (fun env id -> (let _160_95 = (current_module env)
in (qual _160_95 id)))


let qualify_lid : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (

let cur = (current_module env)
in (let _160_100 = (FStar_Ident.lid_of_ids (FStar_List.append cur.FStar_Ident.ns (FStar_List.append ((cur.FStar_Ident.ident)::[]) (FStar_List.append lid.FStar_Ident.ns ((lid.FStar_Ident.ident)::[])))))
in (FStar_Ident.set_lid_range _160_100 (FStar_Ident.range_of_lid lid)))))


let new_sigmap = (fun _63_52 -> (match (()) with
| () -> begin
(FStar_Util.smap_create (Prims.parse_int "100"))
end))


let empty_env : Prims.unit  ->  env = (fun _63_53 -> (match (()) with
| () -> begin
(let _160_104 = (new_sigmap ())
in {curmodule = None; modules = []; open_namespaces = []; modul_abbrevs = []; sigaccum = []; localbindings = []; recbindings = []; sigmap = _160_104; default_result_effect = FStar_Syntax_Const.effect_Tot_lid; iface = false; admitted_iface = false; expect_typ = false})
end))


let sigmap : env  ->  (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap = (fun env -> env.sigmap)


let has_all_in_scope : env  ->  Prims.bool = (fun env -> (FStar_List.existsb (fun _63_59 -> (match (_63_59) with
| (m, _63_58) -> begin
(FStar_Ident.lid_equals m FStar_Syntax_Const.all_lid)
end)) env.modules))


let default_total : env  ->  env = (fun env -> (

let _63_61 = env
in {curmodule = _63_61.curmodule; modules = _63_61.modules; open_namespaces = _63_61.open_namespaces; modul_abbrevs = _63_61.modul_abbrevs; sigaccum = _63_61.sigaccum; localbindings = _63_61.localbindings; recbindings = _63_61.recbindings; sigmap = _63_61.sigmap; default_result_effect = FStar_Syntax_Const.effect_Tot_lid; iface = _63_61.iface; admitted_iface = _63_61.admitted_iface; expect_typ = _63_61.expect_typ}))


let default_ml : env  ->  env = (fun env -> if (has_all_in_scope env) then begin
(

let _63_64 = env
in {curmodule = _63_64.curmodule; modules = _63_64.modules; open_namespaces = _63_64.open_namespaces; modul_abbrevs = _63_64.modul_abbrevs; sigaccum = _63_64.sigaccum; localbindings = _63_64.localbindings; recbindings = _63_64.recbindings; sigmap = _63_64.sigmap; default_result_effect = FStar_Syntax_Const.effect_ML_lid; iface = _63_64.iface; admitted_iface = _63_64.admitted_iface; expect_typ = _63_64.expect_typ})
end else begin
env
end)


let set_bv_range : FStar_Syntax_Syntax.bv  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.bv = (fun bv r -> (

let id = (

let _63_68 = bv.FStar_Syntax_Syntax.ppname
in {FStar_Ident.idText = _63_68.FStar_Ident.idText; FStar_Ident.idRange = r})
in (

let _63_71 = bv
in {FStar_Syntax_Syntax.ppname = id; FStar_Syntax_Syntax.index = _63_71.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _63_71.FStar_Syntax_Syntax.sort})))


let bv_to_name : FStar_Syntax_Syntax.bv  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.term = (fun bv r -> (FStar_Syntax_Syntax.bv_to_name (set_bv_range bv r)))


let unmangleMap : (Prims.string * Prims.string * FStar_Syntax_Syntax.delta_depth * FStar_Syntax_Syntax.fv_qual Prims.option) Prims.list = ((("op_ColonColon"), ("Cons"), (FStar_Syntax_Syntax.Delta_constant), (Some (FStar_Syntax_Syntax.Data_ctor))))::((("not"), ("op_Negation"), (FStar_Syntax_Syntax.Delta_equational), (None)))::[]


let unmangleOpName : FStar_Ident.ident  ->  FStar_Syntax_Syntax.term Prims.option = (fun id -> (FStar_Util.find_map unmangleMap (fun _63_80 -> (match (_63_80) with
| (x, y, dd, dq) -> begin
if (id.FStar_Ident.idText = x) then begin
(let _160_126 = (let _160_125 = (FStar_Ident.lid_of_path (("Prims")::(y)::[]) id.FStar_Ident.idRange)
in (FStar_Syntax_Syntax.fvar _160_125 dd dq))
in Some (_160_126))
end else begin
None
end
end))))


let try_lookup_id : env  ->  FStar_Ident.ident  ->  (FStar_Syntax_Syntax.term * Prims.bool) Prims.option = (fun env id -> (match ((unmangleOpName id)) with
| Some (f) -> begin
Some (((f), (false)))
end
| _63_86 -> begin
(FStar_Util.find_map env.localbindings (fun _63_1 -> (match (_63_1) with
| (id', x, mut) when (id'.FStar_Ident.idText = id.FStar_Ident.idText) -> begin
(let _160_133 = (let _160_132 = (bv_to_name x id.FStar_Ident.idRange)
in ((_160_132), (mut)))
in Some (_160_133))
end
| _63_93 -> begin
None
end)))
end))


let resolve_in_open_namespaces' = (fun env lid finder -> (

let aux = (fun namespaces -> (match ((finder lid)) with
| Some (r) -> begin
Some (r)
end
| _63_103 -> begin
(

let ids = (FStar_Ident.ids_of_lid lid)
in (FStar_Util.find_map namespaces (fun ns -> (

let full_name = (FStar_Ident.lid_of_ids (FStar_List.append (FStar_Ident.ids_of_lid ns) ids))
in (finder full_name)))))
end))
in (let _160_144 = (let _160_143 = (current_module env)
in (_160_143)::env.open_namespaces)
in (aux _160_144))))


let expand_module_abbrev : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (match (lid.FStar_Ident.ns) with
| (_63_112)::_63_110 -> begin
lid
end
| [] -> begin
(

let id = lid.FStar_Ident.ident
in (match ((FStar_List.tryFind (fun _63_119 -> (match (_63_119) with
| (id', _63_118) -> begin
(id.FStar_Ident.idText = id'.FStar_Ident.idText)
end)) env.modul_abbrevs)) with
| None -> begin
lid
end
| Some (_63_122, lid') -> begin
lid'
end))
end))


let expand_module_abbrevs : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (match (lid.FStar_Ident.ns) with
| (id)::rest -> begin
(match ((FStar_All.pipe_right env.modul_abbrevs (FStar_List.tryFind (fun _63_134 -> (match (_63_134) with
| (id', _63_133) -> begin
(id.FStar_Ident.idText = id'.FStar_Ident.idText)
end))))) with
| None -> begin
lid
end
| Some (_63_137, lid') -> begin
(FStar_Ident.lid_of_ids (FStar_List.append (FStar_Ident.ids_of_lid lid') (FStar_List.append rest ((lid.FStar_Ident.ident)::[]))))
end)
end
| _63_142 -> begin
lid
end))


let resolve_in_open_namespaces = (fun env lid finder -> (let _160_161 = (expand_module_abbrevs env lid)
in (resolve_in_open_namespaces' env _160_161 finder)))


let fv_qual_of_se : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.fv_qual Prims.option = (fun _63_3 -> (match (_63_3) with
| FStar_Syntax_Syntax.Sig_datacon (_63_149, _63_151, _63_153, l, _63_156, quals, _63_159, _63_161) -> begin
(

let qopt = (FStar_Util.find_map quals (fun _63_2 -> (match (_63_2) with
| FStar_Syntax_Syntax.RecordConstructor (fs) -> begin
Some (FStar_Syntax_Syntax.Record_ctor (((l), (fs))))
end
| _63_168 -> begin
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
| FStar_Syntax_Syntax.Sig_declare_typ (_63_173, _63_175, _63_177, quals, _63_180) -> begin
None
end
| _63_184 -> begin
None
end))


let lb_fv : FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.fv = (fun lbs lid -> (let _160_170 = (FStar_Util.find_map lbs (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in if (FStar_Syntax_Syntax.fv_eq_lid fv lid) then begin
Some (fv)
end else begin
None
end)))
in (FStar_All.pipe_right _160_170 FStar_Util.must)))


let try_lookup_name : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  foundname Prims.option = (fun any_val exclude_interf env lid -> (

let occurrence_range = (FStar_Ident.range_of_lid lid)
in (

let find_in_sig = (fun lid -> (match ((FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str)) with
| Some (_63_197, true) when exclude_interf -> begin
None
end
| None -> begin
None
end
| Some (se, _63_204) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_63_208) -> begin
(let _160_183 = (let _160_182 = (let _160_181 = (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.Delta_constant None)
in ((_160_181), (false)))
in Term_name (_160_182))
in Some (_160_183))
end
| FStar_Syntax_Syntax.Sig_datacon (_63_211) -> begin
(let _160_187 = (let _160_186 = (let _160_185 = (let _160_184 = (fv_qual_of_se se)
in (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.Delta_constant _160_184))
in ((_160_185), (false)))
in Term_name (_160_186))
in Some (_160_187))
end
| FStar_Syntax_Syntax.Sig_let ((_63_214, lbs), _63_218, _63_220, _63_222) -> begin
(

let fv = (lb_fv lbs lid)
in (let _160_190 = (let _160_189 = (let _160_188 = (FStar_Syntax_Syntax.fvar lid fv.FStar_Syntax_Syntax.fv_delta fv.FStar_Syntax_Syntax.fv_qual)
in ((_160_188), (false)))
in Term_name (_160_189))
in Some (_160_190)))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _63_228, _63_230, quals, _63_233) -> begin
if (any_val || (FStar_All.pipe_right quals (FStar_Util.for_some (fun _63_4 -> (match (_63_4) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| _63_239 -> begin
false
end))))) then begin
(

let dd = if ((FStar_Syntax_Util.is_primop_lid lid) || ((FStar_Util.starts_with lid.FStar_Ident.nsstr "Prims.") && (FStar_All.pipe_right quals (FStar_Util.for_some (fun _63_5 -> (match (_63_5) with
| (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) -> begin
true
end
| _63_248 -> begin
false
end)))))) then begin
FStar_Syntax_Syntax.Delta_equational
end else begin
FStar_Syntax_Syntax.Delta_constant
end
in if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Reflectable)) then begin
(

let refl_monad = (let _160_194 = (FStar_All.pipe_right lid.FStar_Ident.ns (FStar_List.map (fun x -> x.FStar_Ident.idText)))
in (FStar_Ident.lid_of_path _160_194 occurrence_range))
in (

let refl_const = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (refl_monad))) None occurrence_range)
in Some (Term_name (((refl_const), (false))))))
end else begin
(let _160_198 = (let _160_197 = (let _160_196 = (let _160_195 = (fv_qual_of_se se)
in (FStar_Syntax_Syntax.fvar lid dd _160_195))
in ((_160_196), (false)))
in Term_name (_160_197))
in Some (_160_198))
end)
end else begin
None
end
end
| (FStar_Syntax_Syntax.Sig_new_effect_for_free (ne, _)) | (FStar_Syntax_Syntax.Sig_new_effect (ne, _)) -> begin
(let _160_201 = (let _160_200 = (let _160_199 = (FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname (FStar_Ident.range_of_lid lid))
in ((se), (_160_199)))
in Eff_name (_160_200))
in Some (_160_201))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (_63_263) -> begin
Some (Eff_name (((se), (lid))))
end
| _63_266 -> begin
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
in (FStar_Util.find_map env.recbindings (fun _63_277 -> (match (_63_277) with
| (id, l, dd) -> begin
if (id.FStar_Ident.idText = lid.FStar_Ident.ident.FStar_Ident.idText) then begin
(let _160_206 = (let _160_205 = (let _160_204 = (let _160_203 = (FStar_Ident.set_lid_range l (FStar_Ident.range_of_lid lid))
in (FStar_Syntax_Syntax.fvar _160_203 dd None))
in ((_160_204), (false)))
in Term_name (_160_205))
in Some (_160_206))
end else begin
None
end
end))))
end)
end
| _63_279 -> begin
None
end)
in (match (found_id) with
| Some (_63_282) -> begin
found_id
end
| _63_285 -> begin
(resolve_in_open_namespaces env lid find_in_sig)
end)))))


let try_lookup_effect_name' : Prims.bool  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident) Prims.option = (fun exclude_interf env lid -> (match ((try_lookup_name true exclude_interf env lid)) with
| Some (Eff_name (o, l)) -> begin
Some (((o), (l)))
end
| _63_295 -> begin
None
end))


let try_lookup_effect_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env l -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some (o, l) -> begin
Some (l)
end
| _63_303 -> begin
None
end))


let try_lookup_effect_defn : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl Prims.option = (fun env l -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some (FStar_Syntax_Syntax.Sig_new_effect (ne, _63_308), _63_312) -> begin
Some (ne)
end
| Some (FStar_Syntax_Syntax.Sig_new_effect_for_free (ne, _63_317), _63_321) -> begin
Some (ne)
end
| _63_325 -> begin
None
end))


let is_effect_name : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((try_lookup_effect_name env lid)) with
| None -> begin
false
end
| Some (_63_330) -> begin
true
end))


let lookup_letbinding_quals : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.qualifier Prims.list = (fun env lid -> (

let find_in_sig = (fun lid -> (match ((FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str)) with
| Some (FStar_Syntax_Syntax.Sig_declare_typ (lid, _63_338, _63_340, quals, _63_343), _63_347) -> begin
Some (quals)
end
| _63_351 -> begin
None
end))
in (match ((resolve_in_open_namespaces env lid find_in_sig)) with
| Some (quals) -> begin
quals
end
| _63_355 -> begin
[]
end)))


let try_lookup_module : env  ->  Prims.string Prims.list  ->  FStar_Syntax_Syntax.modul Prims.option = (fun env path -> (match ((FStar_List.tryFind (fun _63_360 -> (match (_63_360) with
| (mlid, modul) -> begin
((FStar_Ident.path_of_lid mlid) = path)
end)) env.modules)) with
| Some (_63_362, modul) -> begin
Some (modul)
end
| None -> begin
None
end))


let try_lookup_let : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env lid -> (

let find_in_sig = (fun lid -> (match ((FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str)) with
| Some (FStar_Syntax_Syntax.Sig_let ((_63_372, lbs), _63_376, _63_378, _63_380), _63_384) -> begin
(

let fv = (lb_fv lbs lid)
in (let _160_242 = (FStar_Syntax_Syntax.fvar lid fv.FStar_Syntax_Syntax.fv_delta fv.FStar_Syntax_Syntax.fv_qual)
in Some (_160_242)))
end
| _63_389 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))


let try_lookup_definition : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env lid -> (

let find_in_sig = (fun lid -> (match ((FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str)) with
| Some (FStar_Syntax_Syntax.Sig_let (lbs, _63_396, _63_398, _63_400), _63_404) -> begin
(FStar_Util.find_map (Prims.snd lbs) (fun lb -> (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv lid) -> begin
Some (lb.FStar_Syntax_Syntax.lbdef)
end
| _63_411 -> begin
None
end)))
end
| _63_413 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))


let try_lookup_lid' : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term * Prims.bool) Prims.option = (fun any_val exclude_interf env lid -> (match ((try_lookup_name any_val exclude_interf env lid)) with
| Some (Term_name (e, mut)) -> begin
Some (((e), (mut)))
end
| _63_424 -> begin
None
end))


let try_lookup_lid : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term * Prims.bool) Prims.option = (fun env l -> (try_lookup_lid' env.iface false env l))


let try_lookup_datacon : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.fv Prims.option = (fun env lid -> (

let find_in_sig = (fun lid -> (match ((FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str)) with
| Some (FStar_Syntax_Syntax.Sig_declare_typ (_63_432, _63_434, _63_436, quals, _63_439), _63_443) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _63_6 -> (match (_63_6) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| _63_449 -> begin
false
end)))) then begin
(let _160_269 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant None)
in Some (_160_269))
end else begin
None
end
end
| Some (FStar_Syntax_Syntax.Sig_datacon (_63_451), _63_454) -> begin
(let _160_270 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in Some (_160_270))
end
| _63_458 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))


let find_all_datacons : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.list Prims.option = (fun env lid -> (

let find_in_sig = (fun lid -> (match ((FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str)) with
| Some (FStar_Syntax_Syntax.Sig_inductive_typ (_63_464, _63_466, _63_468, _63_470, _63_472, datas, _63_475, _63_477), _63_481) -> begin
Some (datas)
end
| _63_485 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))


let record_cache_aux : ((Prims.unit  ->  Prims.unit) * (Prims.unit  ->  Prims.unit) * (Prims.unit  ->  record_or_dc Prims.list) * (record_or_dc  ->  Prims.unit) * (Prims.unit  ->  Prims.unit)) = (

let record_cache = (FStar_Util.mk_ref (([])::[]))
in (

let push = (fun _63_488 -> (match (()) with
| () -> begin
(let _160_292 = (let _160_291 = (let _160_289 = (FStar_ST.read record_cache)
in (FStar_List.hd _160_289))
in (let _160_290 = (FStar_ST.read record_cache)
in (_160_291)::_160_290))
in (FStar_ST.op_Colon_Equals record_cache _160_292))
end))
in (

let pop = (fun _63_490 -> (match (()) with
| () -> begin
(let _160_296 = (let _160_295 = (FStar_ST.read record_cache)
in (FStar_List.tl _160_295))
in (FStar_ST.op_Colon_Equals record_cache _160_296))
end))
in (

let peek = (fun _63_492 -> (match (()) with
| () -> begin
(let _160_299 = (FStar_ST.read record_cache)
in (FStar_List.hd _160_299))
end))
in (

let insert = (fun r -> (let _160_306 = (let _160_305 = (let _160_302 = (peek ())
in (r)::_160_302)
in (let _160_304 = (let _160_303 = (FStar_ST.read record_cache)
in (FStar_List.tl _160_303))
in (_160_305)::_160_304))
in (FStar_ST.op_Colon_Equals record_cache _160_306)))
in (

let commit = (fun _63_496 -> (match (()) with
| () -> begin
(match ((FStar_ST.read record_cache)) with
| (hd)::(_63_499)::tl -> begin
(FStar_ST.op_Colon_Equals record_cache ((hd)::tl))
end
| _63_504 -> begin
(FStar_All.failwith "Impossible")
end)
end))
in ((push), (pop), (peek), (insert), (commit))))))))


let push_record_cache : Prims.unit  ->  Prims.unit = (

let _63_514 = record_cache_aux
in (match (_63_514) with
| (push, _63_507, _63_509, _63_511, _63_513) -> begin
push
end))


let pop_record_cache : Prims.unit  ->  Prims.unit = (

let _63_524 = record_cache_aux
in (match (_63_524) with
| (_63_516, pop, _63_519, _63_521, _63_523) -> begin
pop
end))


let peek_record_cache : Prims.unit  ->  record_or_dc Prims.list = (

let _63_534 = record_cache_aux
in (match (_63_534) with
| (_63_526, _63_528, peek, _63_531, _63_533) -> begin
peek
end))


let insert_record_cache : record_or_dc  ->  Prims.unit = (

let _63_544 = record_cache_aux
in (match (_63_544) with
| (_63_536, _63_538, _63_540, insert, _63_543) -> begin
insert
end))


let commit_record_cache : Prims.unit  ->  Prims.unit = (

let _63_554 = record_cache_aux
in (match (_63_554) with
| (_63_546, _63_548, _63_550, _63_552, commit) -> begin
commit
end))


let extract_record : env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun e _63_10 -> (match (_63_10) with
| FStar_Syntax_Syntax.Sig_bundle (sigs, _63_559, _63_561, _63_563) -> begin
(

let is_rec = (FStar_Util.for_some (fun _63_7 -> (match (_63_7) with
| (FStar_Syntax_Syntax.RecordType (_)) | (FStar_Syntax_Syntax.RecordConstructor (_)) -> begin
true
end
| _63_574 -> begin
false
end)))
in (

let find_dc = (fun dc -> (FStar_All.pipe_right sigs (FStar_Util.find_opt (fun _63_8 -> (match (_63_8) with
| FStar_Syntax_Syntax.Sig_datacon (lid, _63_581, _63_583, _63_585, _63_587, _63_589, _63_591, _63_593) -> begin
(FStar_Ident.lid_equals dc lid)
end
| _63_597 -> begin
false
end)))))
in (FStar_All.pipe_right sigs (FStar_List.iter (fun _63_9 -> (match (_63_9) with
| FStar_Syntax_Syntax.Sig_inductive_typ (typename, univs, parms, _63_603, _63_605, (dc)::[], tags, _63_610) -> begin
(match ((let _160_409 = (find_dc dc)
in (FStar_All.pipe_left FStar_Util.must _160_409))) with
| FStar_Syntax_Syntax.Sig_datacon (constrname, _63_615, t, _63_618, _63_620, _63_622, _63_624, _63_626) -> begin
(

let _63_632 = (FStar_Syntax_Util.arrow_formals t)
in (match (_63_632) with
| (formals, _63_631) -> begin
(

let is_rec = (is_rec tags)
in (

let fields = (FStar_All.pipe_right formals (FStar_List.collect (fun _63_636 -> (match (_63_636) with
| (x, q) -> begin
if ((FStar_Syntax_Syntax.is_null_bv x) || (is_rec && (FStar_Syntax_Syntax.is_implicit q))) then begin
[]
end else begin
(let _160_413 = (let _160_412 = (let _160_411 = if is_rec then begin
(FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname)
end else begin
x.FStar_Syntax_Syntax.ppname
end
in (qual constrname _160_411))
in ((_160_412), (x.FStar_Syntax_Syntax.sort)))
in (_160_413)::[])
end
end))))
in (

let record = {typename = typename; constrname = constrname; parms = parms; fields = fields; is_record = is_rec}
in (insert_record_cache record))))
end))
end
| _63_640 -> begin
()
end)
end
| _63_642 -> begin
()
end))))))
end
| _63_644 -> begin
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
(let _160_424 = (aux tl)
in (hd)::_160_424)
end))
in (aux ns)))
in (

let find_in_cache = (fun fieldname -> (

let _63_662 = ((fieldname.FStar_Ident.ns), (fieldname.FStar_Ident.ident))
in (match (_63_662) with
| (ns, fieldname) -> begin
(let _160_429 = (peek_record_cache ())
in (FStar_Util.find_map _160_429 (fun record -> (

let constrname = record.constrname.FStar_Ident.ident
in (

let ns = (maybe_add_constrname ns constrname)
in (

let fname = (FStar_Ident.lid_of_ids (FStar_List.append ns ((fieldname)::[])))
in (FStar_Util.find_map record.fields (fun _63_670 -> (match (_63_670) with
| (f, _63_669) -> begin
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
| _63_678 -> begin
None
end))


let try_lookup_projector_by_field_name : env  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * Prims.bool) Prims.option = (fun env fieldname -> (match ((try_lookup_record_or_dc_by_field_name env fieldname)) with
| Some (r, f) -> begin
Some (((f), (r.is_record)))
end
| _63_686 -> begin
None
end))


let qualify_field_to_record : env  ->  record_or_dc  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env recd f -> (

let qualify = (fun fieldname -> (

let _63_694 = ((fieldname.FStar_Ident.ns), (fieldname.FStar_Ident.ident))
in (match (_63_694) with
| (ns, fieldname) -> begin
(

let constrname = recd.constrname.FStar_Ident.ident
in (

let fname = (FStar_Ident.lid_of_ids (FStar_List.append ns (FStar_List.append ((constrname)::[]) ((fieldname)::[]))))
in (FStar_Util.find_map recd.fields (fun _63_700 -> (match (_63_700) with
| (f, _63_699) -> begin
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

let _63_705 = env
in {curmodule = _63_705.curmodule; modules = _63_705.modules; open_namespaces = []; modul_abbrevs = _63_705.modul_abbrevs; sigaccum = _63_705.sigaccum; localbindings = _63_705.localbindings; recbindings = _63_705.recbindings; sigmap = _63_705.sigmap; default_result_effect = _63_705.default_result_effect; iface = _63_705.iface; admitted_iface = _63_705.admitted_iface; expect_typ = _63_705.expect_typ})
in (match ((try_lookup_lid' any_val exclude_if env lid)) with
| None -> begin
true
end
| Some (_63_710) -> begin
false
end)))


let push_bv' : env  ->  FStar_Ident.ident  ->  Prims.bool  ->  (env * FStar_Syntax_Syntax.bv) = (fun env x is_mutable -> (

let bv = (FStar_Syntax_Syntax.gen_bv x.FStar_Ident.idText (Some (x.FStar_Ident.idRange)) FStar_Syntax_Syntax.tun)
in (((

let _63_716 = env
in {curmodule = _63_716.curmodule; modules = _63_716.modules; open_namespaces = _63_716.open_namespaces; modul_abbrevs = _63_716.modul_abbrevs; sigaccum = _63_716.sigaccum; localbindings = (((x), (bv), (is_mutable)))::env.localbindings; recbindings = _63_716.recbindings; sigmap = _63_716.sigmap; default_result_effect = _63_716.default_result_effect; iface = _63_716.iface; admitted_iface = _63_716.admitted_iface; expect_typ = _63_716.expect_typ})), (bv))))


let push_bv_mutable : env  ->  FStar_Ident.ident  ->  (env * FStar_Syntax_Syntax.bv) = (fun env x -> (push_bv' env x true))


let push_bv : env  ->  FStar_Ident.ident  ->  (env * FStar_Syntax_Syntax.bv) = (fun env x -> (push_bv' env x false))


let push_top_level_rec_binding : env  ->  FStar_Ident.ident  ->  FStar_Syntax_Syntax.delta_depth  ->  env = (fun env x dd -> (

let l = (qualify env x)
in if (unique false true env l) then begin
(

let _63_726 = env
in {curmodule = _63_726.curmodule; modules = _63_726.modules; open_namespaces = _63_726.open_namespaces; modul_abbrevs = _63_726.modul_abbrevs; sigaccum = _63_726.sigaccum; localbindings = _63_726.localbindings; recbindings = (((x), (l), (dd)))::env.recbindings; sigmap = _63_726.sigmap; default_result_effect = _63_726.default_result_effect; iface = _63_726.iface; admitted_iface = _63_726.admitted_iface; expect_typ = _63_726.expect_typ})
end else begin
(Prims.raise (FStar_Syntax_Syntax.Error ((((Prims.strcat "Duplicate top-level names " l.FStar_Ident.str)), ((FStar_Ident.range_of_lid l))))))
end))


let push_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env s -> (

let err = (fun l -> (

let sopt = (FStar_Util.smap_try_find (sigmap env) l.FStar_Ident.str)
in (

let r = (match (sopt) with
| Some (se, _63_735) -> begin
(match ((let _160_481 = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_Util.find_opt (FStar_Ident.lid_equals l) _160_481))) with
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
in (let _160_484 = (let _160_483 = (let _160_482 = (FStar_Util.format2 "Duplicate top-level names [%s]; previously declared at %s" (FStar_Ident.text_of_lid l) r)
in ((_160_482), ((FStar_Ident.range_of_lid l))))
in FStar_Syntax_Syntax.Error (_160_483))
in (Prims.raise _160_484)))))
in (

let env = (

let _63_753 = (match (s) with
| FStar_Syntax_Syntax.Sig_let (_63_744) -> begin
((false), (true))
end
| FStar_Syntax_Syntax.Sig_bundle (_63_747) -> begin
((true), (true))
end
| _63_750 -> begin
((false), (false))
end)
in (match (_63_753) with
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

let _63_757 = (extract_record env s)
in (

let _63_759 = env
in {curmodule = _63_759.curmodule; modules = _63_759.modules; open_namespaces = _63_759.open_namespaces; modul_abbrevs = _63_759.modul_abbrevs; sigaccum = (s)::env.sigaccum; localbindings = _63_759.localbindings; recbindings = _63_759.recbindings; sigmap = _63_759.sigmap; default_result_effect = _63_759.default_result_effect; iface = _63_759.iface; admitted_iface = _63_759.admitted_iface; expect_typ = _63_759.expect_typ}))
end
| Some (l) -> begin
(err l)
end))
end))
in (

let _63_778 = (match (s) with
| FStar_Syntax_Syntax.Sig_bundle (ses, _63_766, _63_768, _63_770) -> begin
(let _160_488 = (FStar_List.map (fun se -> (let _160_487 = (FStar_Syntax_Util.lids_of_sigelt se)
in ((_160_487), (se)))) ses)
in ((env), (_160_488)))
end
| _63_775 -> begin
(let _160_491 = (let _160_490 = (let _160_489 = (FStar_Syntax_Util.lids_of_sigelt s)
in ((_160_489), (s)))
in (_160_490)::[])
in ((env), (_160_491)))
end)
in (match (_63_778) with
| (env, lss) -> begin
(

let _63_783 = (FStar_All.pipe_right lss (FStar_List.iter (fun _63_781 -> (match (_63_781) with
| (lids, se) -> begin
(FStar_All.pipe_right lids (FStar_List.iter (fun lid -> (FStar_Util.smap_add (sigmap env) lid.FStar_Ident.str ((se), ((env.iface && (not (env.admitted_iface)))))))))
end))))
in env)
end)))))


let push_namespace : env  ->  FStar_Ident.lident  ->  env = (fun env ns -> (

let modules = env.modules
in if (FStar_All.pipe_right modules (FStar_Util.for_some (fun _63_791 -> (match (_63_791) with
| (m, _63_790) -> begin
(FStar_Util.starts_with (FStar_Ident.text_of_lid m) (FStar_Ident.text_of_lid ns))
end)))) then begin
(

let _63_792 = env
in {curmodule = _63_792.curmodule; modules = _63_792.modules; open_namespaces = (ns)::env.open_namespaces; modul_abbrevs = _63_792.modul_abbrevs; sigaccum = _63_792.sigaccum; localbindings = _63_792.localbindings; recbindings = _63_792.recbindings; sigmap = _63_792.sigmap; default_result_effect = _63_792.default_result_effect; iface = _63_792.iface; admitted_iface = _63_792.admitted_iface; expect_typ = _63_792.expect_typ})
end else begin
(let _160_501 = (let _160_500 = (let _160_499 = (FStar_Util.format1 "Namespace %s cannot be found" (FStar_Ident.text_of_lid ns))
in ((_160_499), ((FStar_Ident.range_of_lid ns))))
in FStar_Syntax_Syntax.Error (_160_500))
in (Prims.raise _160_501))
end))


let push_module_abbrev : env  ->  FStar_Ident.ident  ->  FStar_Ident.lident  ->  env = (fun env x l -> if (FStar_All.pipe_right env.modul_abbrevs (FStar_Util.for_some (fun _63_800 -> (match (_63_800) with
| (y, _63_799) -> begin
(x.FStar_Ident.idText = y.FStar_Ident.idText)
end)))) then begin
(let _160_511 = (let _160_510 = (let _160_509 = (FStar_Util.format1 "Module %s is already defined" x.FStar_Ident.idText)
in ((_160_509), (x.FStar_Ident.idRange)))
in FStar_Syntax_Syntax.Error (_160_510))
in (Prims.raise _160_511))
end else begin
(

let modules = env.modules
in if (FStar_All.pipe_right modules (FStar_Util.for_some (fun _63_805 -> (match (_63_805) with
| (m, _63_804) -> begin
(FStar_Ident.lid_equals m l)
end)))) then begin
(

let _63_806 = env
in {curmodule = _63_806.curmodule; modules = _63_806.modules; open_namespaces = _63_806.open_namespaces; modul_abbrevs = (((x), (l)))::env.modul_abbrevs; sigaccum = _63_806.sigaccum; localbindings = _63_806.localbindings; recbindings = _63_806.recbindings; sigmap = _63_806.sigmap; default_result_effect = _63_806.default_result_effect; iface = _63_806.iface; admitted_iface = _63_806.admitted_iface; expect_typ = _63_806.expect_typ})
end else begin
(let _160_515 = (let _160_514 = (let _160_513 = (FStar_Util.format1 "Module %s cannot be found" (FStar_Ident.text_of_lid l))
in ((_160_513), ((FStar_Ident.range_of_lid l))))
in FStar_Syntax_Syntax.Error (_160_514))
in (Prims.raise _160_515))
end)
end)


let check_admits : env  ->  Prims.unit = (fun env -> (FStar_All.pipe_right env.sigaccum (FStar_List.iter (fun se -> (match (se) with
| FStar_Syntax_Syntax.Sig_declare_typ (l, u, t, quals, r) -> begin
(match ((try_lookup_lid env l)) with
| None -> begin
(

let _63_818 = (let _160_521 = (let _160_520 = (FStar_Range.string_of_range (FStar_Ident.range_of_lid l))
in (let _160_519 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format2 "%s: Warning: Admitting %s without a definition\n" _160_520 _160_519)))
in (FStar_Util.print_string _160_521))
in (FStar_Util.smap_add (sigmap env) l.FStar_Ident.str ((FStar_Syntax_Syntax.Sig_declare_typ (((l), (u), (t), ((FStar_Syntax_Syntax.Assumption)::quals), (r)))), (false))))
end
| Some (_63_821) -> begin
()
end)
end
| _63_824 -> begin
()
end)))))


let finish : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env modul -> (

let _63_884 = (FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations (FStar_List.iter (fun _63_12 -> (match (_63_12) with
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _63_831, _63_833) -> begin
if ((FStar_List.contains FStar_Syntax_Syntax.Private quals) || (FStar_List.contains FStar_Syntax_Syntax.Abstract quals)) then begin
(FStar_All.pipe_right ses (FStar_List.iter (fun _63_11 -> (match (_63_11) with
| FStar_Syntax_Syntax.Sig_datacon (lid, _63_839, _63_841, _63_843, _63_845, _63_847, _63_849, _63_851) -> begin
(FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str)
end
| _63_855 -> begin
()
end))))
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _63_858, _63_860, quals, _63_863) -> begin
if (FStar_List.contains FStar_Syntax_Syntax.Private quals) then begin
(FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str)
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_let ((_63_867, lbs), r, _63_872, quals) -> begin
(

let _63_877 = if ((FStar_List.contains FStar_Syntax_Syntax.Private quals) || (FStar_List.contains FStar_Syntax_Syntax.Abstract quals)) then begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (let _160_532 = (let _160_531 = (let _160_530 = (let _160_529 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _160_529.FStar_Syntax_Syntax.fv_name)
in _160_530.FStar_Syntax_Syntax.v)
in _160_531.FStar_Ident.str)
in (FStar_Util.smap_remove (sigmap env) _160_532)))))
end else begin
()
end
in if ((FStar_List.contains FStar_Syntax_Syntax.Abstract quals) && (not ((FStar_List.contains FStar_Syntax_Syntax.Private quals)))) then begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (

let lid = (let _160_535 = (let _160_534 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _160_534.FStar_Syntax_Syntax.fv_name)
in _160_535.FStar_Syntax_Syntax.v)
in (

let decl = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), ((FStar_Syntax_Syntax.Assumption)::quals), (r)))
in (FStar_Util.smap_add (sigmap env) lid.FStar_Ident.str ((decl), (false))))))))
end else begin
()
end)
end
| _63_883 -> begin
()
end))))
in (

let _63_886 = env
in {curmodule = None; modules = (((modul.FStar_Syntax_Syntax.name), (modul)))::env.modules; open_namespaces = []; modul_abbrevs = []; sigaccum = []; localbindings = []; recbindings = []; sigmap = _63_886.sigmap; default_result_effect = _63_886.default_result_effect; iface = _63_886.iface; admitted_iface = _63_886.admitted_iface; expect_typ = _63_886.expect_typ})))


type env_stack_ops =
{push : env  ->  env; mark : env  ->  env; reset_mark : env  ->  env; commit_mark : env  ->  env; pop : env  ->  env}


let is_Mkenv_stack_ops : env_stack_ops  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv_stack_ops"))))


let stack_ops : env_stack_ops = (

let stack = (FStar_Util.mk_ref [])
in (

let push = (fun env -> (

let _63_897 = (push_record_cache ())
in (

let _63_899 = (let _160_585 = (let _160_584 = (FStar_ST.read stack)
in (env)::_160_584)
in (FStar_ST.op_Colon_Equals stack _160_585))
in (

let _63_901 = env
in (let _160_586 = (FStar_Util.smap_copy (sigmap env))
in {curmodule = _63_901.curmodule; modules = _63_901.modules; open_namespaces = _63_901.open_namespaces; modul_abbrevs = _63_901.modul_abbrevs; sigaccum = _63_901.sigaccum; localbindings = _63_901.localbindings; recbindings = _63_901.recbindings; sigmap = _160_586; default_result_effect = _63_901.default_result_effect; iface = _63_901.iface; admitted_iface = _63_901.admitted_iface; expect_typ = _63_901.expect_typ})))))
in (

let pop = (fun env -> (match ((FStar_ST.read stack)) with
| (env)::tl -> begin
(

let _63_908 = (pop_record_cache ())
in (

let _63_910 = (FStar_ST.op_Colon_Equals stack tl)
in env))
end
| _63_913 -> begin
(FStar_All.failwith "Impossible: Too many pops")
end))
in (

let commit_mark = (fun env -> (

let _63_916 = (commit_record_cache ())
in (match ((FStar_ST.read stack)) with
| (_63_920)::tl -> begin
(

let _63_922 = (FStar_ST.op_Colon_Equals stack tl)
in env)
end
| _63_925 -> begin
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
| (l)::_63_936 -> begin
(l.FStar_Ident.nsstr = m.FStar_Ident.str)
end
| _63_940 -> begin
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

let _63_964 = (FStar_All.pipe_right keys (FStar_List.iter (fun k -> (match ((FStar_Util.smap_try_find sm' k)) with
| Some (se, true) when (sigelt_in_m se) -> begin
(

let _63_950 = (FStar_Util.smap_remove sm' k)
in (

let se = (match (se) with
| FStar_Syntax_Syntax.Sig_declare_typ (l, u, t, q, r) -> begin
FStar_Syntax_Syntax.Sig_declare_typ (((l), (u), (t), ((FStar_Syntax_Syntax.Assumption)::q), (r)))
end
| _63_960 -> begin
se
end)
in (FStar_Util.smap_add sm' k ((se), (false)))))
end
| _63_963 -> begin
()
end))))
in env)))))))


let finish_module_or_interface : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env modul -> (

let _63_968 = if (not (modul.FStar_Syntax_Syntax.is_interface)) then begin
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

let _63_979 = env
in {curmodule = Some (mname); modules = _63_979.modules; open_namespaces = open_ns; modul_abbrevs = _63_979.modul_abbrevs; sigaccum = _63_979.sigaccum; localbindings = _63_979.localbindings; recbindings = _63_979.recbindings; sigmap = env.sigmap; default_result_effect = if ((FStar_Ident.lid_equals mname FStar_Syntax_Const.all_lid) || (has_all_in_scope env)) then begin
FStar_Syntax_Const.effect_ML_lid
end else begin
FStar_Syntax_Const.effect_Tot_lid
end; iface = intf; admitted_iface = admitted; expect_typ = _63_979.expect_typ}))))
in (match ((FStar_All.pipe_right env.modules (FStar_Util.find_opt (fun _63_984 -> (match (_63_984) with
| (l, _63_983) -> begin
(FStar_Ident.lid_equals l mname)
end))))) with
| None -> begin
(let _160_623 = (prep env)
in ((_160_623), (false)))
end
| Some (_63_987, m) -> begin
(

let _63_991 = if ((not (m.FStar_Syntax_Syntax.is_interface)) || intf) then begin
(let _160_626 = (let _160_625 = (let _160_624 = (FStar_Util.format1 "Duplicate module or interface name: %s" mname.FStar_Ident.str)
in ((_160_624), ((FStar_Ident.range_of_lid mname))))
in FStar_Syntax_Syntax.Error (_160_625))
in (Prims.raise _160_626))
end else begin
()
end
in (let _160_628 = (let _160_627 = (push env)
in (prep _160_627))
in ((_160_628), (true))))
end)))


let enter_monad_scope : env  ->  FStar_Ident.ident  ->  env = (fun env mname -> (

let curmod = (current_module env)
in (

let mscope = (FStar_Ident.lid_of_ids (FStar_List.append curmod.FStar_Ident.ns ((curmod.FStar_Ident.ident)::(mname)::[])))
in (

let _63_997 = env
in {curmodule = Some (mscope); modules = _63_997.modules; open_namespaces = (curmod)::env.open_namespaces; modul_abbrevs = _63_997.modul_abbrevs; sigaccum = _63_997.sigaccum; localbindings = _63_997.localbindings; recbindings = _63_997.recbindings; sigmap = _63_997.sigmap; default_result_effect = _63_997.default_result_effect; iface = _63_997.iface; admitted_iface = _63_997.admitted_iface; expect_typ = _63_997.expect_typ}))))


let exit_monad_scope : env  ->  env  ->  env = (fun env0 env -> (

let _63_1001 = env
in {curmodule = env0.curmodule; modules = _63_1001.modules; open_namespaces = env0.open_namespaces; modul_abbrevs = _63_1001.modul_abbrevs; sigaccum = _63_1001.sigaccum; localbindings = _63_1001.localbindings; recbindings = _63_1001.recbindings; sigmap = _63_1001.sigmap; default_result_effect = _63_1001.default_result_effect; iface = _63_1001.iface; admitted_iface = _63_1001.admitted_iface; expect_typ = _63_1001.expect_typ}))


let fail_or = (fun env lookup lid -> (match ((lookup lid)) with
| None -> begin
(

let opened_modules = (FStar_List.map (fun _63_1010 -> (match (_63_1010) with
| (lid, _63_1009) -> begin
(FStar_Ident.text_of_lid lid)
end)) env.modules)
in (

let module_of_the_lid = (let _160_644 = (FStar_Ident.path_of_ns lid.FStar_Ident.ns)
in (FStar_Ident.text_of_path _160_644))
in (

let msg = (FStar_Util.format1 "Identifier not found: [%s]" (FStar_Ident.text_of_lid lid))
in (

let msg = (match (env.curmodule) with
| Some (m) when (((FStar_Ident.text_of_lid m) = module_of_the_lid) || (module_of_the_lid = "")) -> begin
msg
end
| _63_1017 when (FStar_List.existsb (fun m -> (m = module_of_the_lid)) opened_modules) -> begin
msg
end
| _63_1020 -> begin
(let _160_649 = (let _160_648 = (let _160_647 = (let _160_646 = (FStar_Ident.path_of_ns lid.FStar_Ident.ns)
in (FStar_Ident.text_of_path _160_646))
in (FStar_Util.format3 "Hint: %s belongs to module %s, which does not belong to the list of modules in scope, namely %s" (FStar_Ident.text_of_lid lid) _160_647 (FStar_String.concat ", " opened_modules)))
in (Prims.strcat "\n" _160_648))
in (Prims.strcat msg _160_649))
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




