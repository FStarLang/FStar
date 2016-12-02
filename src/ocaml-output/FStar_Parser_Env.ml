
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


let qual : FStar_Ident.lident  ->  FStar_Ident.ident  ->  FStar_Ident.lident = (fun lid id -> (let _158_90 = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns ((lid.FStar_Ident.ident)::(id)::[])))
in (FStar_Ident.set_lid_range _158_90 id.FStar_Ident.idRange)))


let qualify : env  ->  FStar_Ident.ident  ->  FStar_Ident.lident = (fun env id -> (let _158_95 = (current_module env)
in (qual _158_95 id)))


let qualify_lid : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (

let cur = (current_module env)
in (let _158_100 = (FStar_Ident.lid_of_ids (FStar_List.append cur.FStar_Ident.ns (FStar_List.append ((cur.FStar_Ident.ident)::[]) (FStar_List.append lid.FStar_Ident.ns ((lid.FStar_Ident.ident)::[])))))
in (FStar_Ident.set_lid_range _158_100 (FStar_Ident.range_of_lid lid)))))


let new_sigmap = (fun _63_52 -> (match (()) with
| () -> begin
(FStar_Util.smap_create (Prims.parse_int "100"))
end))


let empty_env : Prims.unit  ->  env = (fun _63_53 -> (match (()) with
| () -> begin
(let _158_104 = (new_sigmap ())
in {curmodule = None; modules = []; open_namespaces = []; modul_abbrevs = []; sigaccum = []; localbindings = []; recbindings = []; sigmap = _158_104; default_result_effect = FStar_Syntax_Const.effect_Tot_lid; iface = false; admitted_iface = false; expect_typ = false})
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
(let _158_126 = (let _158_125 = (FStar_Ident.lid_of_path (("Prims")::(y)::[]) id.FStar_Ident.idRange)
in (FStar_Syntax_Syntax.fvar _158_125 dd dq))
in Some (_158_126))
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
(let _158_133 = (let _158_132 = (bv_to_name x id.FStar_Ident.idRange)
in ((_158_132), (mut)))
in Some (_158_133))
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
in (let _158_144 = (let _158_143 = (current_module env)
in (_158_143)::env.open_namespaces)
in (aux _158_144))))


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


let resolve_in_open_namespaces = (fun env lid finder -> (let _158_161 = (expand_module_abbrevs env lid)
in (resolve_in_open_namespaces' env _158_161 finder)))


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


let lb_fv : FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.fv = (fun lbs lid -> (let _158_170 = (FStar_Util.find_map lbs (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in if (FStar_Syntax_Syntax.fv_eq_lid fv lid) then begin
Some (fv)
end else begin
None
end)))
in (FStar_All.pipe_right _158_170 FStar_Util.must)))


let try_lookup_name : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  foundname Prims.option = (fun any_val exclude_interf env lid -> (

let occurrence_range = (FStar_Ident.range_of_lid lid)
in (

let find_in_sig = (fun source_lid -> (match ((FStar_Util.smap_try_find (sigmap env) source_lid.FStar_Ident.str)) with
| Some (_63_197, true) when exclude_interf -> begin
None
end
| None -> begin
None
end
| Some (se, _63_204) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_63_208) -> begin
(let _158_183 = (let _158_182 = (let _158_181 = (FStar_Syntax_Syntax.fvar source_lid FStar_Syntax_Syntax.Delta_constant None)
in ((_158_181), (false)))
in Term_name (_158_182))
in Some (_158_183))
end
| FStar_Syntax_Syntax.Sig_datacon (_63_211) -> begin
(let _158_187 = (let _158_186 = (let _158_185 = (let _158_184 = (fv_qual_of_se se)
in (FStar_Syntax_Syntax.fvar source_lid FStar_Syntax_Syntax.Delta_constant _158_184))
in ((_158_185), (false)))
in Term_name (_158_186))
in Some (_158_187))
end
| FStar_Syntax_Syntax.Sig_let ((_63_214, lbs), _63_218, _63_220, _63_222) -> begin
(

let fv = (lb_fv lbs source_lid)
in (let _158_190 = (let _158_189 = (let _158_188 = (FStar_Syntax_Syntax.fvar source_lid fv.FStar_Syntax_Syntax.fv_delta fv.FStar_Syntax_Syntax.fv_qual)
in ((_158_188), (false)))
in Term_name (_158_189))
in Some (_158_190)))
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

let lid = (FStar_Ident.set_lid_range lid (FStar_Ident.range_of_lid source_lid))
in (

let dd = if ((FStar_Syntax_Util.is_primop_lid lid) || ((FStar_Util.starts_with lid.FStar_Ident.nsstr "Prims.") && (FStar_All.pipe_right quals (FStar_Util.for_some (fun _63_5 -> (match (_63_5) with
| (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) -> begin
true
end
| _63_249 -> begin
false
end)))))) then begin
FStar_Syntax_Syntax.Delta_equational
end else begin
FStar_Syntax_Syntax.Delta_constant
end
in if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Reflectable)) then begin
(

let refl_monad = (let _158_194 = (FStar_All.pipe_right lid.FStar_Ident.ns (FStar_List.map (fun x -> x.FStar_Ident.idText)))
in (FStar_Ident.lid_of_path _158_194 occurrence_range))
in (

let refl_const = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (refl_monad))) None occurrence_range)
in Some (Term_name (((refl_const), (false))))))
end else begin
(let _158_198 = (let _158_197 = (let _158_196 = (let _158_195 = (fv_qual_of_se se)
in (FStar_Syntax_Syntax.fvar lid dd _158_195))
in ((_158_196), (false)))
in Term_name (_158_197))
in Some (_158_198))
end))
end else begin
None
end
end
| (FStar_Syntax_Syntax.Sig_new_effect_for_free (ne, _)) | (FStar_Syntax_Syntax.Sig_new_effect (ne, _)) -> begin
Some (Eff_name (((se), ((FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname (FStar_Ident.range_of_lid source_lid))))))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (_63_264) -> begin
Some (Eff_name (((se), (source_lid))))
end
| _63_267 -> begin
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
in (FStar_Util.find_map env.recbindings (fun _63_278 -> (match (_63_278) with
| (id, l, dd) -> begin
if (id.FStar_Ident.idText = lid.FStar_Ident.ident.FStar_Ident.idText) then begin
(let _158_202 = (let _158_201 = (let _158_200 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range l (FStar_Ident.range_of_lid lid)) dd None)
in ((_158_200), (false)))
in Term_name (_158_201))
in Some (_158_202))
end else begin
None
end
end))))
end)
end
| _63_280 -> begin
None
end)
in (match (found_id) with
| Some (_63_283) -> begin
found_id
end
| _63_286 -> begin
(resolve_in_open_namespaces env lid find_in_sig)
end)))))


let try_lookup_effect_name' : Prims.bool  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident) Prims.option = (fun exclude_interf env lid -> (match ((try_lookup_name true exclude_interf env lid)) with
| Some (Eff_name (o, l)) -> begin
Some (((o), (l)))
end
| _63_296 -> begin
None
end))


let try_lookup_effect_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env l -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some (o, l) -> begin
Some (l)
end
| _63_304 -> begin
None
end))


let try_lookup_effect_defn : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl Prims.option = (fun env l -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some (FStar_Syntax_Syntax.Sig_new_effect (ne, _63_309), _63_313) -> begin
Some (ne)
end
| Some (FStar_Syntax_Syntax.Sig_new_effect_for_free (ne, _63_318), _63_322) -> begin
Some (ne)
end
| _63_326 -> begin
None
end))


let is_effect_name : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((try_lookup_effect_name env lid)) with
| None -> begin
false
end
| Some (_63_331) -> begin
true
end))


let lookup_letbinding_quals : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.qualifier Prims.list = (fun env lid -> (

let find_in_sig = (fun lid -> (match ((FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str)) with
| Some (FStar_Syntax_Syntax.Sig_declare_typ (lid, _63_339, _63_341, quals, _63_344), _63_348) -> begin
Some (quals)
end
| _63_352 -> begin
None
end))
in (match ((resolve_in_open_namespaces env lid find_in_sig)) with
| Some (quals) -> begin
quals
end
| _63_356 -> begin
[]
end)))


let try_lookup_module : env  ->  Prims.string Prims.list  ->  FStar_Syntax_Syntax.modul Prims.option = (fun env path -> (match ((FStar_List.tryFind (fun _63_361 -> (match (_63_361) with
| (mlid, modul) -> begin
((FStar_Ident.path_of_lid mlid) = path)
end)) env.modules)) with
| Some (_63_363, modul) -> begin
Some (modul)
end
| None -> begin
None
end))


let try_lookup_let : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env lid -> (

let find_in_sig = (fun lid -> (match ((FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str)) with
| Some (FStar_Syntax_Syntax.Sig_let ((_63_373, lbs), _63_377, _63_379, _63_381), _63_385) -> begin
(

let fv = (lb_fv lbs lid)
in (let _158_238 = (FStar_Syntax_Syntax.fvar lid fv.FStar_Syntax_Syntax.fv_delta fv.FStar_Syntax_Syntax.fv_qual)
in Some (_158_238)))
end
| _63_390 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))


let try_lookup_definition : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env lid -> (

let find_in_sig = (fun lid -> (match ((FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str)) with
| Some (FStar_Syntax_Syntax.Sig_let (lbs, _63_397, _63_399, _63_401), _63_405) -> begin
(FStar_Util.find_map (Prims.snd lbs) (fun lb -> (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv lid) -> begin
Some (lb.FStar_Syntax_Syntax.lbdef)
end
| _63_412 -> begin
None
end)))
end
| _63_414 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))


let try_lookup_lid' : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term * Prims.bool) Prims.option = (fun any_val exclude_interf env lid -> (match ((try_lookup_name any_val exclude_interf env lid)) with
| Some (Term_name (e, mut)) -> begin
Some (((e), (mut)))
end
| _63_425 -> begin
None
end))


let try_lookup_lid : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term * Prims.bool) Prims.option = (fun env l -> (try_lookup_lid' env.iface false env l))


let try_lookup_datacon : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.fv Prims.option = (fun env lid -> (

let find_in_sig = (fun lid -> (match ((FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str)) with
| Some (FStar_Syntax_Syntax.Sig_declare_typ (_63_433, _63_435, _63_437, quals, _63_440), _63_444) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _63_6 -> (match (_63_6) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| _63_450 -> begin
false
end)))) then begin
(let _158_265 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant None)
in Some (_158_265))
end else begin
None
end
end
| Some (FStar_Syntax_Syntax.Sig_datacon (_63_452), _63_455) -> begin
(let _158_266 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in Some (_158_266))
end
| _63_459 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))


let find_all_datacons : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.list Prims.option = (fun env lid -> (

let find_in_sig = (fun lid -> (match ((FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str)) with
| Some (FStar_Syntax_Syntax.Sig_inductive_typ (_63_465, _63_467, _63_469, _63_471, _63_473, datas, _63_476, _63_478), _63_482) -> begin
Some (datas)
end
| _63_486 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))


let record_cache_aux : ((Prims.unit  ->  Prims.unit) * (Prims.unit  ->  Prims.unit) * (Prims.unit  ->  record_or_dc Prims.list) * (record_or_dc  ->  Prims.unit) * (Prims.unit  ->  Prims.unit)) = (

let record_cache = (FStar_Util.mk_ref (([])::[]))
in (

let push = (fun _63_489 -> (match (()) with
| () -> begin
(let _158_288 = (let _158_287 = (let _158_285 = (FStar_ST.read record_cache)
in (FStar_List.hd _158_285))
in (let _158_286 = (FStar_ST.read record_cache)
in (_158_287)::_158_286))
in (FStar_ST.op_Colon_Equals record_cache _158_288))
end))
in (

let pop = (fun _63_491 -> (match (()) with
| () -> begin
(let _158_292 = (let _158_291 = (FStar_ST.read record_cache)
in (FStar_List.tl _158_291))
in (FStar_ST.op_Colon_Equals record_cache _158_292))
end))
in (

let peek = (fun _63_493 -> (match (()) with
| () -> begin
(let _158_295 = (FStar_ST.read record_cache)
in (FStar_List.hd _158_295))
end))
in (

let insert = (fun r -> (let _158_302 = (let _158_301 = (let _158_298 = (peek ())
in (r)::_158_298)
in (let _158_300 = (let _158_299 = (FStar_ST.read record_cache)
in (FStar_List.tl _158_299))
in (_158_301)::_158_300))
in (FStar_ST.op_Colon_Equals record_cache _158_302)))
in (

let commit = (fun _63_497 -> (match (()) with
| () -> begin
(match ((FStar_ST.read record_cache)) with
| (hd)::(_63_500)::tl -> begin
(FStar_ST.op_Colon_Equals record_cache ((hd)::tl))
end
| _63_505 -> begin
(FStar_All.failwith "Impossible")
end)
end))
in ((push), (pop), (peek), (insert), (commit))))))))


let push_record_cache : Prims.unit  ->  Prims.unit = (

let _63_515 = record_cache_aux
in (match (_63_515) with
| (push, _63_508, _63_510, _63_512, _63_514) -> begin
push
end))


let pop_record_cache : Prims.unit  ->  Prims.unit = (

let _63_525 = record_cache_aux
in (match (_63_525) with
| (_63_517, pop, _63_520, _63_522, _63_524) -> begin
pop
end))


let peek_record_cache : Prims.unit  ->  record_or_dc Prims.list = (

let _63_535 = record_cache_aux
in (match (_63_535) with
| (_63_527, _63_529, peek, _63_532, _63_534) -> begin
peek
end))


let insert_record_cache : record_or_dc  ->  Prims.unit = (

let _63_545 = record_cache_aux
in (match (_63_545) with
| (_63_537, _63_539, _63_541, insert, _63_544) -> begin
insert
end))


let commit_record_cache : Prims.unit  ->  Prims.unit = (

let _63_555 = record_cache_aux
in (match (_63_555) with
| (_63_547, _63_549, _63_551, _63_553, commit) -> begin
commit
end))


let extract_record : env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun e _63_10 -> (match (_63_10) with
| FStar_Syntax_Syntax.Sig_bundle (sigs, _63_560, _63_562, _63_564) -> begin
(

let is_rec = (FStar_Util.for_some (fun _63_7 -> (match (_63_7) with
| (FStar_Syntax_Syntax.RecordType (_)) | (FStar_Syntax_Syntax.RecordConstructor (_)) -> begin
true
end
| _63_575 -> begin
false
end)))
in (

let find_dc = (fun dc -> (FStar_All.pipe_right sigs (FStar_Util.find_opt (fun _63_8 -> (match (_63_8) with
| FStar_Syntax_Syntax.Sig_datacon (lid, _63_582, _63_584, _63_586, _63_588, _63_590, _63_592, _63_594) -> begin
(FStar_Ident.lid_equals dc lid)
end
| _63_598 -> begin
false
end)))))
in (FStar_All.pipe_right sigs (FStar_List.iter (fun _63_9 -> (match (_63_9) with
| FStar_Syntax_Syntax.Sig_inductive_typ (typename, univs, parms, _63_604, _63_606, (dc)::[], tags, _63_611) -> begin
(match ((let _158_405 = (find_dc dc)
in (FStar_All.pipe_left FStar_Util.must _158_405))) with
| FStar_Syntax_Syntax.Sig_datacon (constrname, _63_616, t, _63_619, _63_621, _63_623, _63_625, _63_627) -> begin
(

let _63_633 = (FStar_Syntax_Util.arrow_formals t)
in (match (_63_633) with
| (formals, _63_632) -> begin
(

let is_rec = (is_rec tags)
in (

let fields = (FStar_All.pipe_right formals (FStar_List.collect (fun _63_637 -> (match (_63_637) with
| (x, q) -> begin
if ((FStar_Syntax_Syntax.is_null_bv x) || (is_rec && (FStar_Syntax_Syntax.is_implicit q))) then begin
[]
end else begin
(let _158_409 = (let _158_408 = (let _158_407 = if is_rec then begin
(FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname)
end else begin
x.FStar_Syntax_Syntax.ppname
end
in (qual constrname _158_407))
in ((_158_408), (x.FStar_Syntax_Syntax.sort)))
in (_158_409)::[])
end
end))))
in (

let record = {typename = typename; constrname = constrname; parms = parms; fields = fields; is_record = is_rec}
in (insert_record_cache record))))
end))
end
| _63_641 -> begin
()
end)
end
| _63_643 -> begin
()
end))))))
end
| _63_645 -> begin
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
(let _158_420 = (aux tl)
in (hd)::_158_420)
end))
in (aux ns)))
in (

let find_in_cache = (fun fieldname -> (

let _63_663 = ((fieldname.FStar_Ident.ns), (fieldname.FStar_Ident.ident))
in (match (_63_663) with
| (ns, fieldname) -> begin
(let _158_425 = (peek_record_cache ())
in (FStar_Util.find_map _158_425 (fun record -> (

let constrname = record.constrname.FStar_Ident.ident
in (

let ns = (maybe_add_constrname ns constrname)
in (

let fname = (FStar_Ident.lid_of_ids (FStar_List.append ns ((fieldname)::[])))
in (FStar_Util.find_map record.fields (fun _63_671 -> (match (_63_671) with
| (f, _63_670) -> begin
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
| _63_679 -> begin
None
end))


let try_lookup_projector_by_field_name : env  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * Prims.bool) Prims.option = (fun env fieldname -> (match ((try_lookup_record_or_dc_by_field_name env fieldname)) with
| Some (r, f) -> begin
Some (((f), (r.is_record)))
end
| _63_687 -> begin
None
end))


let qualify_field_to_record : env  ->  record_or_dc  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env recd f -> (

let qualify = (fun fieldname -> (

let _63_695 = ((fieldname.FStar_Ident.ns), (fieldname.FStar_Ident.ident))
in (match (_63_695) with
| (ns, fieldname) -> begin
(

let constrname = recd.constrname.FStar_Ident.ident
in (

let fname = (FStar_Ident.lid_of_ids (FStar_List.append ns (FStar_List.append ((constrname)::[]) ((fieldname)::[]))))
in (FStar_Util.find_map recd.fields (fun _63_701 -> (match (_63_701) with
| (f, _63_700) -> begin
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

let _63_706 = env
in {curmodule = _63_706.curmodule; modules = _63_706.modules; open_namespaces = []; modul_abbrevs = _63_706.modul_abbrevs; sigaccum = _63_706.sigaccum; localbindings = _63_706.localbindings; recbindings = _63_706.recbindings; sigmap = _63_706.sigmap; default_result_effect = _63_706.default_result_effect; iface = _63_706.iface; admitted_iface = _63_706.admitted_iface; expect_typ = _63_706.expect_typ})
in (match ((try_lookup_lid' any_val exclude_if env lid)) with
| None -> begin
true
end
| Some (_63_711) -> begin
false
end)))


let push_bv' : env  ->  FStar_Ident.ident  ->  Prims.bool  ->  (env * FStar_Syntax_Syntax.bv) = (fun env x is_mutable -> (

let bv = (FStar_Syntax_Syntax.gen_bv x.FStar_Ident.idText (Some (x.FStar_Ident.idRange)) FStar_Syntax_Syntax.tun)
in (((

let _63_717 = env
in {curmodule = _63_717.curmodule; modules = _63_717.modules; open_namespaces = _63_717.open_namespaces; modul_abbrevs = _63_717.modul_abbrevs; sigaccum = _63_717.sigaccum; localbindings = (((x), (bv), (is_mutable)))::env.localbindings; recbindings = _63_717.recbindings; sigmap = _63_717.sigmap; default_result_effect = _63_717.default_result_effect; iface = _63_717.iface; admitted_iface = _63_717.admitted_iface; expect_typ = _63_717.expect_typ})), (bv))))


let push_bv_mutable : env  ->  FStar_Ident.ident  ->  (env * FStar_Syntax_Syntax.bv) = (fun env x -> (push_bv' env x true))


let push_bv : env  ->  FStar_Ident.ident  ->  (env * FStar_Syntax_Syntax.bv) = (fun env x -> (push_bv' env x false))


let push_top_level_rec_binding : env  ->  FStar_Ident.ident  ->  FStar_Syntax_Syntax.delta_depth  ->  env = (fun env x dd -> (

let l = (qualify env x)
in if (unique false true env l) then begin
(

let _63_727 = env
in {curmodule = _63_727.curmodule; modules = _63_727.modules; open_namespaces = _63_727.open_namespaces; modul_abbrevs = _63_727.modul_abbrevs; sigaccum = _63_727.sigaccum; localbindings = _63_727.localbindings; recbindings = (((x), (l), (dd)))::env.recbindings; sigmap = _63_727.sigmap; default_result_effect = _63_727.default_result_effect; iface = _63_727.iface; admitted_iface = _63_727.admitted_iface; expect_typ = _63_727.expect_typ})
end else begin
(Prims.raise (FStar_Syntax_Syntax.Error ((((Prims.strcat "Duplicate top-level names " l.FStar_Ident.str)), ((FStar_Ident.range_of_lid l))))))
end))


let push_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env s -> (

let err = (fun l -> (

let sopt = (FStar_Util.smap_try_find (sigmap env) l.FStar_Ident.str)
in (

let r = (match (sopt) with
| Some (se, _63_736) -> begin
(match ((let _158_477 = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_Util.find_opt (FStar_Ident.lid_equals l) _158_477))) with
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
in (let _158_480 = (let _158_479 = (let _158_478 = (FStar_Util.format2 "Duplicate top-level names [%s]; previously declared at %s" (FStar_Ident.text_of_lid l) r)
in ((_158_478), ((FStar_Ident.range_of_lid l))))
in FStar_Syntax_Syntax.Error (_158_479))
in (Prims.raise _158_480)))))
in (

let env = (

let _63_754 = (match (s) with
| FStar_Syntax_Syntax.Sig_let (_63_745) -> begin
((false), (true))
end
| FStar_Syntax_Syntax.Sig_bundle (_63_748) -> begin
((true), (true))
end
| _63_751 -> begin
((false), (false))
end)
in (match (_63_754) with
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

let _63_758 = (extract_record env s)
in (

let _63_760 = env
in {curmodule = _63_760.curmodule; modules = _63_760.modules; open_namespaces = _63_760.open_namespaces; modul_abbrevs = _63_760.modul_abbrevs; sigaccum = (s)::env.sigaccum; localbindings = _63_760.localbindings; recbindings = _63_760.recbindings; sigmap = _63_760.sigmap; default_result_effect = _63_760.default_result_effect; iface = _63_760.iface; admitted_iface = _63_760.admitted_iface; expect_typ = _63_760.expect_typ}))
end
| Some (l) -> begin
(err l)
end))
end))
in (

let _63_779 = (match (s) with
| FStar_Syntax_Syntax.Sig_bundle (ses, _63_767, _63_769, _63_771) -> begin
(let _158_484 = (FStar_List.map (fun se -> (let _158_483 = (FStar_Syntax_Util.lids_of_sigelt se)
in ((_158_483), (se)))) ses)
in ((env), (_158_484)))
end
| _63_776 -> begin
(let _158_487 = (let _158_486 = (let _158_485 = (FStar_Syntax_Util.lids_of_sigelt s)
in ((_158_485), (s)))
in (_158_486)::[])
in ((env), (_158_487)))
end)
in (match (_63_779) with
| (env, lss) -> begin
(

let _63_784 = (FStar_All.pipe_right lss (FStar_List.iter (fun _63_782 -> (match (_63_782) with
| (lids, se) -> begin
(FStar_All.pipe_right lids (FStar_List.iter (fun lid -> (FStar_Util.smap_add (sigmap env) lid.FStar_Ident.str ((se), ((env.iface && (not (env.admitted_iface)))))))))
end))))
in env)
end)))))


let push_namespace : env  ->  FStar_Ident.lident  ->  env = (fun env ns -> (

let modules = env.modules
in if (FStar_All.pipe_right modules (FStar_Util.for_some (fun _63_792 -> (match (_63_792) with
| (m, _63_791) -> begin
(FStar_Util.starts_with (FStar_Ident.text_of_lid m) (FStar_Ident.text_of_lid ns))
end)))) then begin
(

let _63_793 = env
in {curmodule = _63_793.curmodule; modules = _63_793.modules; open_namespaces = (ns)::env.open_namespaces; modul_abbrevs = _63_793.modul_abbrevs; sigaccum = _63_793.sigaccum; localbindings = _63_793.localbindings; recbindings = _63_793.recbindings; sigmap = _63_793.sigmap; default_result_effect = _63_793.default_result_effect; iface = _63_793.iface; admitted_iface = _63_793.admitted_iface; expect_typ = _63_793.expect_typ})
end else begin
(let _158_497 = (let _158_496 = (let _158_495 = (FStar_Util.format1 "Namespace %s cannot be found" (FStar_Ident.text_of_lid ns))
in ((_158_495), ((FStar_Ident.range_of_lid ns))))
in FStar_Syntax_Syntax.Error (_158_496))
in (Prims.raise _158_497))
end))


let push_module_abbrev : env  ->  FStar_Ident.ident  ->  FStar_Ident.lident  ->  env = (fun env x l -> if (FStar_All.pipe_right env.modul_abbrevs (FStar_Util.for_some (fun _63_801 -> (match (_63_801) with
| (y, _63_800) -> begin
(x.FStar_Ident.idText = y.FStar_Ident.idText)
end)))) then begin
(let _158_507 = (let _158_506 = (let _158_505 = (FStar_Util.format1 "Module %s is already defined" x.FStar_Ident.idText)
in ((_158_505), (x.FStar_Ident.idRange)))
in FStar_Syntax_Syntax.Error (_158_506))
in (Prims.raise _158_507))
end else begin
(

let modules = env.modules
in if (FStar_All.pipe_right modules (FStar_Util.for_some (fun _63_806 -> (match (_63_806) with
| (m, _63_805) -> begin
(FStar_Ident.lid_equals m l)
end)))) then begin
(

let _63_807 = env
in {curmodule = _63_807.curmodule; modules = _63_807.modules; open_namespaces = _63_807.open_namespaces; modul_abbrevs = (((x), (l)))::env.modul_abbrevs; sigaccum = _63_807.sigaccum; localbindings = _63_807.localbindings; recbindings = _63_807.recbindings; sigmap = _63_807.sigmap; default_result_effect = _63_807.default_result_effect; iface = _63_807.iface; admitted_iface = _63_807.admitted_iface; expect_typ = _63_807.expect_typ})
end else begin
(let _158_511 = (let _158_510 = (let _158_509 = (FStar_Util.format1 "Module %s cannot be found" (FStar_Ident.text_of_lid l))
in ((_158_509), ((FStar_Ident.range_of_lid l))))
in FStar_Syntax_Syntax.Error (_158_510))
in (Prims.raise _158_511))
end)
end)


let check_admits : env  ->  Prims.unit = (fun env -> (FStar_All.pipe_right env.sigaccum (FStar_List.iter (fun se -> (match (se) with
| FStar_Syntax_Syntax.Sig_declare_typ (l, u, t, quals, r) -> begin
(match ((try_lookup_lid env l)) with
| None -> begin
(

let _63_819 = (let _158_517 = (let _158_516 = (FStar_Range.string_of_range (FStar_Ident.range_of_lid l))
in (let _158_515 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format2 "%s: Warning: Admitting %s without a definition\n" _158_516 _158_515)))
in (FStar_Util.print_string _158_517))
in (FStar_Util.smap_add (sigmap env) l.FStar_Ident.str ((FStar_Syntax_Syntax.Sig_declare_typ (((l), (u), (t), ((FStar_Syntax_Syntax.Assumption)::quals), (r)))), (false))))
end
| Some (_63_822) -> begin
()
end)
end
| _63_825 -> begin
()
end)))))


let finish : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env modul -> (

let _63_885 = (FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations (FStar_List.iter (fun _63_12 -> (match (_63_12) with
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _63_832, _63_834) -> begin
if ((FStar_List.contains FStar_Syntax_Syntax.Private quals) || (FStar_List.contains FStar_Syntax_Syntax.Abstract quals)) then begin
(FStar_All.pipe_right ses (FStar_List.iter (fun _63_11 -> (match (_63_11) with
| FStar_Syntax_Syntax.Sig_datacon (lid, _63_840, _63_842, _63_844, _63_846, _63_848, _63_850, _63_852) -> begin
(FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str)
end
| _63_856 -> begin
()
end))))
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _63_859, _63_861, quals, _63_864) -> begin
if (FStar_List.contains FStar_Syntax_Syntax.Private quals) then begin
(FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str)
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_let ((_63_868, lbs), r, _63_873, quals) -> begin
(

let _63_878 = if ((FStar_List.contains FStar_Syntax_Syntax.Private quals) || (FStar_List.contains FStar_Syntax_Syntax.Abstract quals)) then begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (let _158_528 = (let _158_527 = (let _158_526 = (let _158_525 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _158_525.FStar_Syntax_Syntax.fv_name)
in _158_526.FStar_Syntax_Syntax.v)
in _158_527.FStar_Ident.str)
in (FStar_Util.smap_remove (sigmap env) _158_528)))))
end else begin
()
end
in if ((FStar_List.contains FStar_Syntax_Syntax.Abstract quals) && (not ((FStar_List.contains FStar_Syntax_Syntax.Private quals)))) then begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (

let lid = (let _158_531 = (let _158_530 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _158_530.FStar_Syntax_Syntax.fv_name)
in _158_531.FStar_Syntax_Syntax.v)
in (

let decl = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), ((FStar_Syntax_Syntax.Assumption)::quals), (r)))
in (FStar_Util.smap_add (sigmap env) lid.FStar_Ident.str ((decl), (false))))))))
end else begin
()
end)
end
| _63_884 -> begin
()
end))))
in (

let _63_887 = env
in {curmodule = None; modules = (((modul.FStar_Syntax_Syntax.name), (modul)))::env.modules; open_namespaces = []; modul_abbrevs = []; sigaccum = []; localbindings = []; recbindings = []; sigmap = _63_887.sigmap; default_result_effect = _63_887.default_result_effect; iface = _63_887.iface; admitted_iface = _63_887.admitted_iface; expect_typ = _63_887.expect_typ})))


type env_stack_ops =
{push : env  ->  env; mark : env  ->  env; reset_mark : env  ->  env; commit_mark : env  ->  env; pop : env  ->  env}


let is_Mkenv_stack_ops : env_stack_ops  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv_stack_ops"))))


let stack_ops : env_stack_ops = (

let stack = (FStar_Util.mk_ref [])
in (

let push = (fun env -> (

let _63_898 = (push_record_cache ())
in (

let _63_900 = (let _158_581 = (let _158_580 = (FStar_ST.read stack)
in (env)::_158_580)
in (FStar_ST.op_Colon_Equals stack _158_581))
in (

let _63_902 = env
in (let _158_582 = (FStar_Util.smap_copy (sigmap env))
in {curmodule = _63_902.curmodule; modules = _63_902.modules; open_namespaces = _63_902.open_namespaces; modul_abbrevs = _63_902.modul_abbrevs; sigaccum = _63_902.sigaccum; localbindings = _63_902.localbindings; recbindings = _63_902.recbindings; sigmap = _158_582; default_result_effect = _63_902.default_result_effect; iface = _63_902.iface; admitted_iface = _63_902.admitted_iface; expect_typ = _63_902.expect_typ})))))
in (

let pop = (fun env -> (match ((FStar_ST.read stack)) with
| (env)::tl -> begin
(

let _63_909 = (pop_record_cache ())
in (

let _63_911 = (FStar_ST.op_Colon_Equals stack tl)
in env))
end
| _63_914 -> begin
(FStar_All.failwith "Impossible: Too many pops")
end))
in (

let commit_mark = (fun env -> (

let _63_917 = (commit_record_cache ())
in (match ((FStar_ST.read stack)) with
| (_63_921)::tl -> begin
(

let _63_923 = (FStar_ST.op_Colon_Equals stack tl)
in env)
end
| _63_926 -> begin
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
| (l)::_63_937 -> begin
(l.FStar_Ident.nsstr = m.FStar_Ident.str)
end
| _63_941 -> begin
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

let _63_965 = (FStar_All.pipe_right keys (FStar_List.iter (fun k -> (match ((FStar_Util.smap_try_find sm' k)) with
| Some (se, true) when (sigelt_in_m se) -> begin
(

let _63_951 = (FStar_Util.smap_remove sm' k)
in (

let se = (match (se) with
| FStar_Syntax_Syntax.Sig_declare_typ (l, u, t, q, r) -> begin
FStar_Syntax_Syntax.Sig_declare_typ (((l), (u), (t), ((FStar_Syntax_Syntax.Assumption)::q), (r)))
end
| _63_961 -> begin
se
end)
in (FStar_Util.smap_add sm' k ((se), (false)))))
end
| _63_964 -> begin
()
end))))
in env)))))))


let finish_module_or_interface : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env modul -> (

let _63_969 = if (not (modul.FStar_Syntax_Syntax.is_interface)) then begin
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

let _63_980 = env
in {curmodule = Some (mname); modules = _63_980.modules; open_namespaces = open_ns; modul_abbrevs = _63_980.modul_abbrevs; sigaccum = _63_980.sigaccum; localbindings = _63_980.localbindings; recbindings = _63_980.recbindings; sigmap = env.sigmap; default_result_effect = if ((FStar_Ident.lid_equals mname FStar_Syntax_Const.all_lid) || (has_all_in_scope env)) then begin
FStar_Syntax_Const.effect_ML_lid
end else begin
FStar_Syntax_Const.effect_Tot_lid
end; iface = intf; admitted_iface = admitted; expect_typ = _63_980.expect_typ}))))
in (match ((FStar_All.pipe_right env.modules (FStar_Util.find_opt (fun _63_985 -> (match (_63_985) with
| (l, _63_984) -> begin
(FStar_Ident.lid_equals l mname)
end))))) with
| None -> begin
(let _158_619 = (prep env)
in ((_158_619), (false)))
end
| Some (_63_988, m) -> begin
(

let _63_992 = if ((not (m.FStar_Syntax_Syntax.is_interface)) || intf) then begin
(let _158_622 = (let _158_621 = (let _158_620 = (FStar_Util.format1 "Duplicate module or interface name: %s" mname.FStar_Ident.str)
in ((_158_620), ((FStar_Ident.range_of_lid mname))))
in FStar_Syntax_Syntax.Error (_158_621))
in (Prims.raise _158_622))
end else begin
()
end
in (let _158_624 = (let _158_623 = (push env)
in (prep _158_623))
in ((_158_624), (true))))
end)))


let enter_monad_scope : env  ->  FStar_Ident.ident  ->  env = (fun env mname -> (

let curmod = (current_module env)
in (

let mscope = (FStar_Ident.lid_of_ids (FStar_List.append curmod.FStar_Ident.ns ((curmod.FStar_Ident.ident)::(mname)::[])))
in (

let _63_998 = env
in {curmodule = Some (mscope); modules = _63_998.modules; open_namespaces = (curmod)::env.open_namespaces; modul_abbrevs = _63_998.modul_abbrevs; sigaccum = _63_998.sigaccum; localbindings = _63_998.localbindings; recbindings = _63_998.recbindings; sigmap = _63_998.sigmap; default_result_effect = _63_998.default_result_effect; iface = _63_998.iface; admitted_iface = _63_998.admitted_iface; expect_typ = _63_998.expect_typ}))))


let exit_monad_scope : env  ->  env  ->  env = (fun env0 env -> (

let _63_1002 = env
in {curmodule = env0.curmodule; modules = _63_1002.modules; open_namespaces = env0.open_namespaces; modul_abbrevs = _63_1002.modul_abbrevs; sigaccum = _63_1002.sigaccum; localbindings = _63_1002.localbindings; recbindings = _63_1002.recbindings; sigmap = _63_1002.sigmap; default_result_effect = _63_1002.default_result_effect; iface = _63_1002.iface; admitted_iface = _63_1002.admitted_iface; expect_typ = _63_1002.expect_typ}))


let fail_or = (fun env lookup lid -> (match ((lookup lid)) with
| None -> begin
(

let opened_modules = (FStar_List.map (fun _63_1011 -> (match (_63_1011) with
| (lid, _63_1010) -> begin
(FStar_Ident.text_of_lid lid)
end)) env.modules)
in (

let module_of_the_lid = (let _158_640 = (FStar_Ident.path_of_ns lid.FStar_Ident.ns)
in (FStar_Ident.text_of_path _158_640))
in (

let msg = (FStar_Util.format1 "Identifier not found: [%s]" (FStar_Ident.text_of_lid lid))
in (

let msg = (match (env.curmodule) with
| Some (m) when (((FStar_Ident.text_of_lid m) = module_of_the_lid) || (module_of_the_lid = "")) -> begin
msg
end
| _63_1018 when (FStar_List.existsb (fun m -> (m = module_of_the_lid)) opened_modules) -> begin
msg
end
| _63_1021 -> begin
(let _158_645 = (let _158_644 = (let _158_643 = (let _158_642 = (FStar_Ident.path_of_ns lid.FStar_Ident.ns)
in (FStar_Ident.text_of_path _158_642))
in (FStar_Util.format3 "Hint: %s belongs to module %s, which does not belong to the list of modules in scope, namely %s" (FStar_Ident.text_of_lid lid) _158_643 (FStar_String.concat ", " opened_modules)))
in (Prims.strcat "\n" _158_644))
in (Prims.strcat msg _158_645))
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




