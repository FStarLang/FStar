
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
in (let _154_100 = (FStar_Ident.lid_of_ids (FStar_List.append cur.FStar_Ident.ns (FStar_List.append ((cur.FStar_Ident.ident)::[]) (FStar_List.append lid.FStar_Ident.ns ((lid.FStar_Ident.ident)::[])))))
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


let unmangleMap : (Prims.string * Prims.string * FStar_Syntax_Syntax.delta_depth * FStar_Syntax_Syntax.fv_qual Prims.option) Prims.list = ((("op_ColonColon"), ("Cons"), (FStar_Syntax_Syntax.Delta_constant), (Some (FStar_Syntax_Syntax.Data_ctor))))::((("not"), ("op_Negation"), (FStar_Syntax_Syntax.Delta_equational), (None)))::[]


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
Some (((f), (false)))
end
| _62_86 -> begin
(FStar_Util.find_map env.localbindings (fun _62_1 -> (match (_62_1) with
| (id', x, mut) when (id'.FStar_Ident.idText = id.FStar_Ident.idText) -> begin
(let _154_133 = (let _154_132 = (bv_to_name x id.FStar_Ident.idRange)
in ((_154_132), (mut)))
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


let resolve_in_open_namespaces = (fun env lid finder -> (let _154_161 = (expand_module_abbrevs env lid)
in (resolve_in_open_namespaces' env _154_161 finder)))


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


let lb_fv : FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.fv = (fun lbs lid -> (let _154_170 = (FStar_Util.find_map lbs (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in if (FStar_Syntax_Syntax.fv_eq_lid fv lid) then begin
Some (fv)
end else begin
None
end)))
in (FStar_All.pipe_right _154_170 FStar_Util.must)))


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
(let _154_183 = (let _154_182 = (let _154_181 = (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.Delta_constant None)
in ((_154_181), (false)))
in Term_name (_154_182))
in Some (_154_183))
end
| FStar_Syntax_Syntax.Sig_datacon (_62_211) -> begin
(let _154_187 = (let _154_186 = (let _154_185 = (let _154_184 = (fv_qual_of_se se)
in (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.Delta_constant _154_184))
in ((_154_185), (false)))
in Term_name (_154_186))
in Some (_154_187))
end
| FStar_Syntax_Syntax.Sig_let ((_62_214, lbs), _62_218, _62_220, _62_222) -> begin
(

let fv = (lb_fv lbs lid)
in (let _154_190 = (let _154_189 = (let _154_188 = (FStar_Syntax_Syntax.fvar lid fv.FStar_Syntax_Syntax.fv_delta fv.FStar_Syntax_Syntax.fv_qual)
in ((_154_188), (false)))
in Term_name (_154_189))
in Some (_154_190)))
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

let refl_monad = (let _154_194 = (FStar_All.pipe_right lid.FStar_Ident.ns (FStar_List.map (fun x -> x.FStar_Ident.idText)))
in (FStar_Ident.lid_of_path _154_194 occurrence_range))
in (

let refl_const = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (refl_monad))) None occurrence_range)
in Some (Term_name (((refl_const), (false))))))
end else begin
(let _154_198 = (let _154_197 = (let _154_196 = (let _154_195 = (fv_qual_of_se se)
in (FStar_Syntax_Syntax.fvar lid dd _154_195))
in ((_154_196), (false)))
in Term_name (_154_197))
in Some (_154_198))
end)
end else begin
None
end
end
| (FStar_Syntax_Syntax.Sig_new_effect_for_free (ne, _)) | (FStar_Syntax_Syntax.Sig_new_effect (ne, _)) -> begin
(let _154_201 = (let _154_200 = (let _154_199 = (FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname (FStar_Ident.range_of_lid lid))
in ((se), (_154_199)))
in Eff_name (_154_200))
in Some (_154_201))
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
(let _154_206 = (let _154_205 = (let _154_204 = (let _154_203 = (FStar_Ident.set_lid_range l (FStar_Ident.range_of_lid lid))
in (FStar_Syntax_Syntax.fvar _154_203 dd None))
in ((_154_204), (false)))
in Term_name (_154_205))
in Some (_154_206))
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
| _62_316 -> begin
None
end))


let is_effect_name : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((try_lookup_effect_name env lid)) with
| None -> begin
false
end
| Some (_62_321) -> begin
true
end))


let lookup_letbinding_quals : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.qualifier Prims.list = (fun env lid -> (

let find_in_sig = (fun lid -> (match ((FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str)) with
| Some (FStar_Syntax_Syntax.Sig_declare_typ (lid, _62_329, _62_331, quals, _62_334), _62_338) -> begin
Some (quals)
end
| _62_342 -> begin
None
end))
in (match ((resolve_in_open_namespaces env lid find_in_sig)) with
| Some (quals) -> begin
quals
end
| _62_346 -> begin
[]
end)))


let try_lookup_module : env  ->  Prims.string Prims.list  ->  FStar_Syntax_Syntax.modul Prims.option = (fun env path -> (match ((FStar_List.tryFind (fun _62_351 -> (match (_62_351) with
| (mlid, modul) -> begin
((FStar_Ident.path_of_lid mlid) = path)
end)) env.modules)) with
| Some (_62_353, modul) -> begin
Some (modul)
end
| None -> begin
None
end))


let try_lookup_let : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env lid -> (

let find_in_sig = (fun lid -> (match ((FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str)) with
| Some (FStar_Syntax_Syntax.Sig_let ((_62_363, lbs), _62_367, _62_369, _62_371), _62_375) -> begin
(

let fv = (lb_fv lbs lid)
in (let _154_242 = (FStar_Syntax_Syntax.fvar lid fv.FStar_Syntax_Syntax.fv_delta fv.FStar_Syntax_Syntax.fv_qual)
in Some (_154_242)))
end
| _62_380 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))


let try_lookup_definition : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env lid -> (

let find_in_sig = (fun lid -> (match ((FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str)) with
| Some (FStar_Syntax_Syntax.Sig_let (lbs, _62_387, _62_389, _62_391), _62_395) -> begin
(FStar_Util.find_map (Prims.snd lbs) (fun lb -> (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv lid) -> begin
Some (lb.FStar_Syntax_Syntax.lbdef)
end
| _62_402 -> begin
None
end)))
end
| _62_404 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))


let try_lookup_lid' : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term * Prims.bool) Prims.option = (fun any_val exclude_interf env lid -> (match ((try_lookup_name any_val exclude_interf env lid)) with
| Some (Term_name (e, mut)) -> begin
Some (((e), (mut)))
end
| _62_415 -> begin
None
end))


let try_lookup_lid : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term * Prims.bool) Prims.option = (fun env l -> (try_lookup_lid' env.iface false env l))


let try_lookup_datacon : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.fv Prims.option = (fun env lid -> (

let find_in_sig = (fun lid -> (match ((FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str)) with
| Some (FStar_Syntax_Syntax.Sig_declare_typ (_62_423, _62_425, _62_427, quals, _62_430), _62_434) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _62_6 -> (match (_62_6) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| _62_440 -> begin
false
end)))) then begin
(let _154_269 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant None)
in Some (_154_269))
end else begin
None
end
end
| Some (FStar_Syntax_Syntax.Sig_datacon (_62_442), _62_445) -> begin
(let _154_270 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in Some (_154_270))
end
| _62_449 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))


let find_all_datacons : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.list Prims.option = (fun env lid -> (

let find_in_sig = (fun lid -> (match ((FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str)) with
| Some (FStar_Syntax_Syntax.Sig_inductive_typ (_62_455, _62_457, _62_459, _62_461, _62_463, datas, _62_466, _62_468), _62_472) -> begin
Some (datas)
end
| _62_476 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))


let record_cache_aux : ((Prims.unit  ->  Prims.unit) * (Prims.unit  ->  Prims.unit) * (Prims.unit  ->  record_or_dc Prims.list) * (record_or_dc  ->  Prims.unit) * (Prims.unit  ->  Prims.unit)) = (

let record_cache = (FStar_Util.mk_ref (([])::[]))
in (

let push = (fun _62_479 -> (match (()) with
| () -> begin
(let _154_292 = (let _154_291 = (let _154_289 = (FStar_ST.read record_cache)
in (FStar_List.hd _154_289))
in (let _154_290 = (FStar_ST.read record_cache)
in (_154_291)::_154_290))
in (FStar_ST.op_Colon_Equals record_cache _154_292))
end))
in (

let pop = (fun _62_481 -> (match (()) with
| () -> begin
(let _154_296 = (let _154_295 = (FStar_ST.read record_cache)
in (FStar_List.tl _154_295))
in (FStar_ST.op_Colon_Equals record_cache _154_296))
end))
in (

let peek = (fun _62_483 -> (match (()) with
| () -> begin
(let _154_299 = (FStar_ST.read record_cache)
in (FStar_List.hd _154_299))
end))
in (

let insert = (fun r -> (let _154_306 = (let _154_305 = (let _154_302 = (peek ())
in (r)::_154_302)
in (let _154_304 = (let _154_303 = (FStar_ST.read record_cache)
in (FStar_List.tl _154_303))
in (_154_305)::_154_304))
in (FStar_ST.op_Colon_Equals record_cache _154_306)))
in (

let commit = (fun _62_487 -> (match (()) with
| () -> begin
(match ((FStar_ST.read record_cache)) with
| (hd)::(_62_490)::tl -> begin
(FStar_ST.op_Colon_Equals record_cache ((hd)::tl))
end
| _62_495 -> begin
(FStar_All.failwith "Impossible")
end)
end))
in ((push), (pop), (peek), (insert), (commit))))))))


let push_record_cache : Prims.unit  ->  Prims.unit = (

let _62_505 = record_cache_aux
in (match (_62_505) with
| (push, _62_498, _62_500, _62_502, _62_504) -> begin
push
end))


let pop_record_cache : Prims.unit  ->  Prims.unit = (

let _62_515 = record_cache_aux
in (match (_62_515) with
| (_62_507, pop, _62_510, _62_512, _62_514) -> begin
pop
end))


let peek_record_cache : Prims.unit  ->  record_or_dc Prims.list = (

let _62_525 = record_cache_aux
in (match (_62_525) with
| (_62_517, _62_519, peek, _62_522, _62_524) -> begin
peek
end))


let insert_record_cache : record_or_dc  ->  Prims.unit = (

let _62_535 = record_cache_aux
in (match (_62_535) with
| (_62_527, _62_529, _62_531, insert, _62_534) -> begin
insert
end))


let commit_record_cache : Prims.unit  ->  Prims.unit = (

let _62_545 = record_cache_aux
in (match (_62_545) with
| (_62_537, _62_539, _62_541, _62_543, commit) -> begin
commit
end))


let extract_record : env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun e _62_10 -> (match (_62_10) with
| FStar_Syntax_Syntax.Sig_bundle (sigs, _62_550, _62_552, _62_554) -> begin
(

let is_rec = (FStar_Util.for_some (fun _62_7 -> (match (_62_7) with
| (FStar_Syntax_Syntax.RecordType (_)) | (FStar_Syntax_Syntax.RecordConstructor (_)) -> begin
true
end
| _62_565 -> begin
false
end)))
in (

let find_dc = (fun dc -> (FStar_All.pipe_right sigs (FStar_Util.find_opt (fun _62_8 -> (match (_62_8) with
| FStar_Syntax_Syntax.Sig_datacon (lid, _62_572, _62_574, _62_576, _62_578, _62_580, _62_582, _62_584) -> begin
(FStar_Ident.lid_equals dc lid)
end
| _62_588 -> begin
false
end)))))
in (FStar_All.pipe_right sigs (FStar_List.iter (fun _62_9 -> (match (_62_9) with
| FStar_Syntax_Syntax.Sig_inductive_typ (typename, univs, parms, _62_594, _62_596, (dc)::[], tags, _62_601) -> begin
(match ((let _154_409 = (find_dc dc)
in (FStar_All.pipe_left FStar_Util.must _154_409))) with
| FStar_Syntax_Syntax.Sig_datacon (constrname, _62_606, t, _62_609, _62_611, _62_613, _62_615, _62_617) -> begin
(

let _62_623 = (FStar_Syntax_Util.arrow_formals t)
in (match (_62_623) with
| (formals, _62_622) -> begin
(

let is_rec = (is_rec tags)
in (

let fields = (FStar_All.pipe_right formals (FStar_List.collect (fun _62_627 -> (match (_62_627) with
| (x, q) -> begin
if ((FStar_Syntax_Syntax.is_null_bv x) || (is_rec && (FStar_Syntax_Syntax.is_implicit q))) then begin
[]
end else begin
(let _154_413 = (let _154_412 = (let _154_411 = if is_rec then begin
(FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname)
end else begin
x.FStar_Syntax_Syntax.ppname
end
in (qual constrname _154_411))
in ((_154_412), (x.FStar_Syntax_Syntax.sort)))
in (_154_413)::[])
end
end))))
in (

let record = {typename = typename; constrname = constrname; parms = parms; fields = fields; is_record = is_rec}
in (insert_record_cache record))))
end))
end
| _62_631 -> begin
()
end)
end
| _62_633 -> begin
()
end))))))
end
| _62_635 -> begin
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
(let _154_424 = (aux tl)
in (hd)::_154_424)
end))
in (aux ns)))
in (

let find_in_cache = (fun fieldname -> (

let _62_653 = ((fieldname.FStar_Ident.ns), (fieldname.FStar_Ident.ident))
in (match (_62_653) with
| (ns, fieldname) -> begin
(let _154_429 = (peek_record_cache ())
in (FStar_Util.find_map _154_429 (fun record -> (

let constrname = record.constrname.FStar_Ident.ident
in (

let ns = (maybe_add_constrname ns constrname)
in (

let fname = (FStar_Ident.lid_of_ids (FStar_List.append ns ((fieldname)::[])))
in (FStar_Util.find_map record.fields (fun _62_661 -> (match (_62_661) with
| (f, _62_660) -> begin
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
| _62_669 -> begin
None
end))


let try_lookup_projector_by_field_name : env  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * Prims.bool) Prims.option = (fun env fieldname -> (match ((try_lookup_record_or_dc_by_field_name env fieldname)) with
| Some (r, f) -> begin
Some (((f), (r.is_record)))
end
| _62_677 -> begin
None
end))


let qualify_field_to_record : env  ->  record_or_dc  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env recd f -> (

let qualify = (fun fieldname -> (

let _62_685 = ((fieldname.FStar_Ident.ns), (fieldname.FStar_Ident.ident))
in (match (_62_685) with
| (ns, fieldname) -> begin
(

let constrname = recd.constrname.FStar_Ident.ident
in (

let fname = (FStar_Ident.lid_of_ids (FStar_List.append ns (FStar_List.append ((constrname)::[]) ((fieldname)::[]))))
in (FStar_Util.find_map recd.fields (fun _62_691 -> (match (_62_691) with
| (f, _62_690) -> begin
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

let _62_696 = env
in {curmodule = _62_696.curmodule; modules = _62_696.modules; open_namespaces = []; modul_abbrevs = _62_696.modul_abbrevs; sigaccum = _62_696.sigaccum; localbindings = _62_696.localbindings; recbindings = _62_696.recbindings; sigmap = _62_696.sigmap; default_result_effect = _62_696.default_result_effect; iface = _62_696.iface; admitted_iface = _62_696.admitted_iface; expect_typ = _62_696.expect_typ})
in (match ((try_lookup_lid' any_val exclude_if env lid)) with
| None -> begin
true
end
| Some (_62_701) -> begin
false
end)))


let push_bv' : env  ->  FStar_Ident.ident  ->  Prims.bool  ->  (env * FStar_Syntax_Syntax.bv) = (fun env x is_mutable -> (

let bv = (FStar_Syntax_Syntax.gen_bv x.FStar_Ident.idText (Some (x.FStar_Ident.idRange)) FStar_Syntax_Syntax.tun)
in (((

let _62_707 = env
in {curmodule = _62_707.curmodule; modules = _62_707.modules; open_namespaces = _62_707.open_namespaces; modul_abbrevs = _62_707.modul_abbrevs; sigaccum = _62_707.sigaccum; localbindings = (((x), (bv), (is_mutable)))::env.localbindings; recbindings = _62_707.recbindings; sigmap = _62_707.sigmap; default_result_effect = _62_707.default_result_effect; iface = _62_707.iface; admitted_iface = _62_707.admitted_iface; expect_typ = _62_707.expect_typ})), (bv))))


let push_bv_mutable : env  ->  FStar_Ident.ident  ->  (env * FStar_Syntax_Syntax.bv) = (fun env x -> (push_bv' env x true))


let push_bv : env  ->  FStar_Ident.ident  ->  (env * FStar_Syntax_Syntax.bv) = (fun env x -> (push_bv' env x false))


let push_top_level_rec_binding : env  ->  FStar_Ident.ident  ->  FStar_Syntax_Syntax.delta_depth  ->  env = (fun env x dd -> (

let l = (qualify env x)
in if (unique false true env l) then begin
(

let _62_717 = env
in {curmodule = _62_717.curmodule; modules = _62_717.modules; open_namespaces = _62_717.open_namespaces; modul_abbrevs = _62_717.modul_abbrevs; sigaccum = _62_717.sigaccum; localbindings = _62_717.localbindings; recbindings = (((x), (l), (dd)))::env.recbindings; sigmap = _62_717.sigmap; default_result_effect = _62_717.default_result_effect; iface = _62_717.iface; admitted_iface = _62_717.admitted_iface; expect_typ = _62_717.expect_typ})
end else begin
(Prims.raise (FStar_Syntax_Syntax.Error ((((Prims.strcat "Duplicate top-level names " l.FStar_Ident.str)), ((FStar_Ident.range_of_lid l))))))
end))


let push_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env s -> (

let err = (fun l -> (

let sopt = (FStar_Util.smap_try_find (sigmap env) l.FStar_Ident.str)
in (

let r = (match (sopt) with
| Some (se, _62_726) -> begin
(match ((let _154_481 = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_Util.find_opt (FStar_Ident.lid_equals l) _154_481))) with
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
in (let _154_484 = (let _154_483 = (let _154_482 = (FStar_Util.format2 "Duplicate top-level names [%s]; previously declared at %s" (FStar_Ident.text_of_lid l) r)
in ((_154_482), ((FStar_Ident.range_of_lid l))))
in FStar_Syntax_Syntax.Error (_154_483))
in (Prims.raise _154_484)))))
in (

let env = (

let _62_744 = (match (s) with
| FStar_Syntax_Syntax.Sig_let (_62_735) -> begin
((false), (true))
end
| FStar_Syntax_Syntax.Sig_bundle (_62_738) -> begin
((true), (true))
end
| _62_741 -> begin
((false), (false))
end)
in (match (_62_744) with
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

let _62_748 = (extract_record env s)
in (

let _62_750 = env
in {curmodule = _62_750.curmodule; modules = _62_750.modules; open_namespaces = _62_750.open_namespaces; modul_abbrevs = _62_750.modul_abbrevs; sigaccum = (s)::env.sigaccum; localbindings = _62_750.localbindings; recbindings = _62_750.recbindings; sigmap = _62_750.sigmap; default_result_effect = _62_750.default_result_effect; iface = _62_750.iface; admitted_iface = _62_750.admitted_iface; expect_typ = _62_750.expect_typ}))
end
| Some (l) -> begin
(err l)
end))
end))
in (

let _62_769 = (match (s) with
| FStar_Syntax_Syntax.Sig_bundle (ses, _62_757, _62_759, _62_761) -> begin
(let _154_488 = (FStar_List.map (fun se -> (let _154_487 = (FStar_Syntax_Util.lids_of_sigelt se)
in ((_154_487), (se)))) ses)
in ((env), (_154_488)))
end
| _62_766 -> begin
(let _154_491 = (let _154_490 = (let _154_489 = (FStar_Syntax_Util.lids_of_sigelt s)
in ((_154_489), (s)))
in (_154_490)::[])
in ((env), (_154_491)))
end)
in (match (_62_769) with
| (env, lss) -> begin
(

let _62_774 = (FStar_All.pipe_right lss (FStar_List.iter (fun _62_772 -> (match (_62_772) with
| (lids, se) -> begin
(FStar_All.pipe_right lids (FStar_List.iter (fun lid -> (FStar_Util.smap_add (sigmap env) lid.FStar_Ident.str ((se), ((env.iface && (not (env.admitted_iface)))))))))
end))))
in env)
end)))))


let push_namespace : env  ->  FStar_Ident.lident  ->  env = (fun env ns -> (

let modules = env.modules
in if (FStar_All.pipe_right modules (FStar_Util.for_some (fun _62_782 -> (match (_62_782) with
| (m, _62_781) -> begin
(FStar_Util.starts_with (FStar_Ident.text_of_lid m) (FStar_Ident.text_of_lid ns))
end)))) then begin
(

let _62_783 = env
in {curmodule = _62_783.curmodule; modules = _62_783.modules; open_namespaces = (ns)::env.open_namespaces; modul_abbrevs = _62_783.modul_abbrevs; sigaccum = _62_783.sigaccum; localbindings = _62_783.localbindings; recbindings = _62_783.recbindings; sigmap = _62_783.sigmap; default_result_effect = _62_783.default_result_effect; iface = _62_783.iface; admitted_iface = _62_783.admitted_iface; expect_typ = _62_783.expect_typ})
end else begin
(let _154_501 = (let _154_500 = (let _154_499 = (FStar_Util.format1 "Namespace %s cannot be found" (FStar_Ident.text_of_lid ns))
in ((_154_499), ((FStar_Ident.range_of_lid ns))))
in FStar_Syntax_Syntax.Error (_154_500))
in (Prims.raise _154_501))
end))


let push_module_abbrev : env  ->  FStar_Ident.ident  ->  FStar_Ident.lident  ->  env = (fun env x l -> if (FStar_All.pipe_right env.modul_abbrevs (FStar_Util.for_some (fun _62_791 -> (match (_62_791) with
| (y, _62_790) -> begin
(x.FStar_Ident.idText = y.FStar_Ident.idText)
end)))) then begin
(let _154_511 = (let _154_510 = (let _154_509 = (FStar_Util.format1 "Module %s is already defined" x.FStar_Ident.idText)
in ((_154_509), (x.FStar_Ident.idRange)))
in FStar_Syntax_Syntax.Error (_154_510))
in (Prims.raise _154_511))
end else begin
(

let modules = env.modules
in if (FStar_All.pipe_right modules (FStar_Util.for_some (fun _62_796 -> (match (_62_796) with
| (m, _62_795) -> begin
(FStar_Ident.lid_equals m l)
end)))) then begin
(

let _62_797 = env
in {curmodule = _62_797.curmodule; modules = _62_797.modules; open_namespaces = _62_797.open_namespaces; modul_abbrevs = (((x), (l)))::env.modul_abbrevs; sigaccum = _62_797.sigaccum; localbindings = _62_797.localbindings; recbindings = _62_797.recbindings; sigmap = _62_797.sigmap; default_result_effect = _62_797.default_result_effect; iface = _62_797.iface; admitted_iface = _62_797.admitted_iface; expect_typ = _62_797.expect_typ})
end else begin
(let _154_515 = (let _154_514 = (let _154_513 = (FStar_Util.format1 "Module %s cannot be found" (FStar_Ident.text_of_lid l))
in ((_154_513), ((FStar_Ident.range_of_lid l))))
in FStar_Syntax_Syntax.Error (_154_514))
in (Prims.raise _154_515))
end)
end)


let check_admits : env  ->  Prims.unit = (fun env -> (FStar_All.pipe_right env.sigaccum (FStar_List.iter (fun se -> (match (se) with
| FStar_Syntax_Syntax.Sig_declare_typ (l, u, t, quals, r) -> begin
(match ((try_lookup_lid env l)) with
| None -> begin
(

let _62_809 = (let _154_521 = (let _154_520 = (FStar_Range.string_of_range (FStar_Ident.range_of_lid l))
in (let _154_519 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format2 "%s: Warning: Admitting %s without a definition\n" _154_520 _154_519)))
in (FStar_Util.print_string _154_521))
in (FStar_Util.smap_add (sigmap env) l.FStar_Ident.str ((FStar_Syntax_Syntax.Sig_declare_typ (((l), (u), (t), ((FStar_Syntax_Syntax.Assumption)::quals), (r)))), (false))))
end
| Some (_62_812) -> begin
()
end)
end
| _62_815 -> begin
()
end)))))


let finish : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env modul -> (

let _62_875 = (FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations (FStar_List.iter (fun _62_12 -> (match (_62_12) with
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _62_822, _62_824) -> begin
if ((FStar_List.contains FStar_Syntax_Syntax.Private quals) || (FStar_List.contains FStar_Syntax_Syntax.Abstract quals)) then begin
(FStar_All.pipe_right ses (FStar_List.iter (fun _62_11 -> (match (_62_11) with
| FStar_Syntax_Syntax.Sig_datacon (lid, _62_830, _62_832, _62_834, _62_836, _62_838, _62_840, _62_842) -> begin
(FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str)
end
| _62_846 -> begin
()
end))))
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _62_849, _62_851, quals, _62_854) -> begin
if (FStar_List.contains FStar_Syntax_Syntax.Private quals) then begin
(FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str)
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_let ((_62_858, lbs), r, _62_863, quals) -> begin
(

let _62_868 = if ((FStar_List.contains FStar_Syntax_Syntax.Private quals) || (FStar_List.contains FStar_Syntax_Syntax.Abstract quals)) then begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (let _154_532 = (let _154_531 = (let _154_530 = (let _154_529 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _154_529.FStar_Syntax_Syntax.fv_name)
in _154_530.FStar_Syntax_Syntax.v)
in _154_531.FStar_Ident.str)
in (FStar_Util.smap_remove (sigmap env) _154_532)))))
end else begin
()
end
in if ((FStar_List.contains FStar_Syntax_Syntax.Abstract quals) && (not ((FStar_List.contains FStar_Syntax_Syntax.Private quals)))) then begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (

let lid = (let _154_535 = (let _154_534 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _154_534.FStar_Syntax_Syntax.fv_name)
in _154_535.FStar_Syntax_Syntax.v)
in (

let decl = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), ((FStar_Syntax_Syntax.Assumption)::quals), (r)))
in (FStar_Util.smap_add (sigmap env) lid.FStar_Ident.str ((decl), (false))))))))
end else begin
()
end)
end
| _62_874 -> begin
()
end))))
in (

let _62_877 = env
in {curmodule = None; modules = (((modul.FStar_Syntax_Syntax.name), (modul)))::env.modules; open_namespaces = []; modul_abbrevs = []; sigaccum = []; localbindings = []; recbindings = []; sigmap = _62_877.sigmap; default_result_effect = _62_877.default_result_effect; iface = _62_877.iface; admitted_iface = _62_877.admitted_iface; expect_typ = _62_877.expect_typ})))


type env_stack_ops =
{push : env  ->  env; mark : env  ->  env; reset_mark : env  ->  env; commit_mark : env  ->  env; pop : env  ->  env}


let is_Mkenv_stack_ops : env_stack_ops  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv_stack_ops"))))


let stack_ops : env_stack_ops = (

let stack = (FStar_Util.mk_ref [])
in (

let push = (fun env -> (

let _62_888 = (push_record_cache ())
in (

let _62_890 = (let _154_585 = (let _154_584 = (FStar_ST.read stack)
in (env)::_154_584)
in (FStar_ST.op_Colon_Equals stack _154_585))
in (

let _62_892 = env
in (let _154_586 = (FStar_Util.smap_copy (sigmap env))
in {curmodule = _62_892.curmodule; modules = _62_892.modules; open_namespaces = _62_892.open_namespaces; modul_abbrevs = _62_892.modul_abbrevs; sigaccum = _62_892.sigaccum; localbindings = _62_892.localbindings; recbindings = _62_892.recbindings; sigmap = _154_586; default_result_effect = _62_892.default_result_effect; iface = _62_892.iface; admitted_iface = _62_892.admitted_iface; expect_typ = _62_892.expect_typ})))))
in (

let pop = (fun env -> (match ((FStar_ST.read stack)) with
| (env)::tl -> begin
(

let _62_899 = (pop_record_cache ())
in (

let _62_901 = (FStar_ST.op_Colon_Equals stack tl)
in env))
end
| _62_904 -> begin
(FStar_All.failwith "Impossible: Too many pops")
end))
in (

let commit_mark = (fun env -> (

let _62_907 = (commit_record_cache ())
in (match ((FStar_ST.read stack)) with
| (_62_911)::tl -> begin
(

let _62_913 = (FStar_ST.op_Colon_Equals stack tl)
in env)
end
| _62_916 -> begin
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
| (l)::_62_927 -> begin
(l.FStar_Ident.nsstr = m.FStar_Ident.str)
end
| _62_931 -> begin
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

let _62_955 = (FStar_All.pipe_right keys (FStar_List.iter (fun k -> (match ((FStar_Util.smap_try_find sm' k)) with
| Some (se, true) when (sigelt_in_m se) -> begin
(

let _62_941 = (FStar_Util.smap_remove sm' k)
in (

let se = (match (se) with
| FStar_Syntax_Syntax.Sig_declare_typ (l, u, t, q, r) -> begin
FStar_Syntax_Syntax.Sig_declare_typ (((l), (u), (t), ((FStar_Syntax_Syntax.Assumption)::q), (r)))
end
| _62_951 -> begin
se
end)
in (FStar_Util.smap_add sm' k ((se), (false)))))
end
| _62_954 -> begin
()
end))))
in env)))))))


let finish_module_or_interface : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env modul -> (

let _62_959 = if (not (modul.FStar_Syntax_Syntax.is_interface)) then begin
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

let _62_970 = env
in {curmodule = Some (mname); modules = _62_970.modules; open_namespaces = open_ns; modul_abbrevs = _62_970.modul_abbrevs; sigaccum = _62_970.sigaccum; localbindings = _62_970.localbindings; recbindings = _62_970.recbindings; sigmap = env.sigmap; default_result_effect = if ((FStar_Ident.lid_equals mname FStar_Syntax_Const.all_lid) || (has_all_in_scope env)) then begin
FStar_Syntax_Const.effect_ML_lid
end else begin
FStar_Syntax_Const.effect_Tot_lid
end; iface = intf; admitted_iface = admitted; expect_typ = _62_970.expect_typ}))))
in (match ((FStar_All.pipe_right env.modules (FStar_Util.find_opt (fun _62_975 -> (match (_62_975) with
| (l, _62_974) -> begin
(FStar_Ident.lid_equals l mname)
end))))) with
| None -> begin
(let _154_623 = (prep env)
in ((_154_623), (false)))
end
| Some (_62_978, m) -> begin
(

let _62_982 = if ((not (m.FStar_Syntax_Syntax.is_interface)) || intf) then begin
(let _154_626 = (let _154_625 = (let _154_624 = (FStar_Util.format1 "Duplicate module or interface name: %s" mname.FStar_Ident.str)
in ((_154_624), ((FStar_Ident.range_of_lid mname))))
in FStar_Syntax_Syntax.Error (_154_625))
in (Prims.raise _154_626))
end else begin
()
end
in (let _154_628 = (let _154_627 = (push env)
in (prep _154_627))
in ((_154_628), (true))))
end)))


let enter_monad_scope : env  ->  FStar_Ident.ident  ->  env = (fun env mname -> (

let curmod = (current_module env)
in (

let mscope = (FStar_Ident.lid_of_ids (FStar_List.append curmod.FStar_Ident.ns ((curmod.FStar_Ident.ident)::(mname)::[])))
in (

let _62_988 = env
in {curmodule = Some (mscope); modules = _62_988.modules; open_namespaces = (curmod)::env.open_namespaces; modul_abbrevs = _62_988.modul_abbrevs; sigaccum = _62_988.sigaccum; localbindings = _62_988.localbindings; recbindings = _62_988.recbindings; sigmap = _62_988.sigmap; default_result_effect = _62_988.default_result_effect; iface = _62_988.iface; admitted_iface = _62_988.admitted_iface; expect_typ = _62_988.expect_typ}))))


let exit_monad_scope : env  ->  env  ->  env = (fun env0 env -> (

let _62_992 = env
in {curmodule = env0.curmodule; modules = _62_992.modules; open_namespaces = env0.open_namespaces; modul_abbrevs = _62_992.modul_abbrevs; sigaccum = _62_992.sigaccum; localbindings = _62_992.localbindings; recbindings = _62_992.recbindings; sigmap = _62_992.sigmap; default_result_effect = _62_992.default_result_effect; iface = _62_992.iface; admitted_iface = _62_992.admitted_iface; expect_typ = _62_992.expect_typ}))


let fail_or = (fun env lookup lid -> (match ((lookup lid)) with
| None -> begin
(

let opened_modules = (FStar_List.map (fun _62_1001 -> (match (_62_1001) with
| (lid, _62_1000) -> begin
(FStar_Ident.text_of_lid lid)
end)) env.modules)
in (

let module_of_the_lid = (let _154_644 = (FStar_Ident.path_of_ns lid.FStar_Ident.ns)
in (FStar_Ident.text_of_path _154_644))
in (

let msg = (FStar_Util.format1 "Identifier not found: [%s]" (FStar_Ident.text_of_lid lid))
in (

let msg = (match (env.curmodule) with
| Some (m) when (((FStar_Ident.text_of_lid m) = module_of_the_lid) || (module_of_the_lid = "")) -> begin
msg
end
| _62_1008 when (FStar_List.existsb (fun m -> (m = module_of_the_lid)) opened_modules) -> begin
msg
end
| _62_1011 -> begin
(let _154_649 = (let _154_648 = (let _154_647 = (let _154_646 = (FStar_Ident.path_of_ns lid.FStar_Ident.ns)
in (FStar_Ident.text_of_path _154_646))
in (FStar_Util.format3 "Hint: %s belongs to module %s, which does not belong to the list of modules in scope, namely %s" (FStar_Ident.text_of_lid lid) _154_647 (FStar_String.concat ", " opened_modules)))
in (Prims.strcat "\n" _154_648))
in (Prims.strcat msg _154_649))
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




