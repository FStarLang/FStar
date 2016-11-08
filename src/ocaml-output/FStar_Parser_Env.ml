
open Prims

type env =
{curmodule : FStar_Ident.lident Prims.option; curmonad : FStar_Ident.ident Prims.option; modules : (FStar_Ident.lident * FStar_Syntax_Syntax.modul) Prims.list; open_namespaces : FStar_Ident.lident Prims.list; modul_abbrevs : (FStar_Ident.ident * FStar_Ident.lident) Prims.list; sigaccum : FStar_Syntax_Syntax.sigelts; localbindings : (FStar_Ident.ident * FStar_Syntax_Syntax.bv * Prims.bool) Prims.list; recbindings : (FStar_Ident.ident * FStar_Ident.lid * FStar_Syntax_Syntax.delta_depth) Prims.list; sigmap : (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap; default_result_effect : FStar_Ident.lident; iface : Prims.bool; admitted_iface : Prims.bool; expect_typ : Prims.bool}


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
| Term_name (_63_30) -> begin
_63_30
end))


let ___Eff_name____0 = (fun projectee -> (match (projectee) with
| Eff_name (_63_33) -> begin
_63_33
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


let qual : FStar_Ident.lident  ->  FStar_Ident.ident  ->  FStar_Ident.lident = FStar_Syntax_Util.qual_id


let qualify : env  ->  FStar_Ident.ident  ->  FStar_Ident.lident = (fun env id -> (match (env.curmonad) with
| None -> begin
(let _158_95 = (current_module env)
in (qual _158_95 id))
end
| Some (monad) -> begin
(let _158_97 = (let _158_96 = (current_module env)
in (qual _158_96 monad))
in (FStar_Syntax_Util.mk_field_projector_name_from_ident _158_97 id))
end))


let new_sigmap = (fun _63_52 -> (match (()) with
| () -> begin
(FStar_Util.smap_create (Prims.parse_int "100"))
end))


let empty_env : Prims.unit  ->  env = (fun _63_53 -> (match (()) with
| () -> begin
(let _158_101 = (new_sigmap ())
in {curmodule = None; curmonad = None; modules = []; open_namespaces = []; modul_abbrevs = []; sigaccum = []; localbindings = []; recbindings = []; sigmap = _158_101; default_result_effect = FStar_Syntax_Const.effect_Tot_lid; iface = false; admitted_iface = false; expect_typ = false})
end))


let sigmap : env  ->  (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap = (fun env -> env.sigmap)


let has_all_in_scope : env  ->  Prims.bool = (fun env -> (FStar_List.existsb (fun _63_59 -> (match (_63_59) with
| (m, _63_58) -> begin
(FStar_Ident.lid_equals m FStar_Syntax_Const.all_lid)
end)) env.modules))


let default_total : env  ->  env = (fun env -> (

let _63_61 = env
in {curmodule = _63_61.curmodule; curmonad = _63_61.curmonad; modules = _63_61.modules; open_namespaces = _63_61.open_namespaces; modul_abbrevs = _63_61.modul_abbrevs; sigaccum = _63_61.sigaccum; localbindings = _63_61.localbindings; recbindings = _63_61.recbindings; sigmap = _63_61.sigmap; default_result_effect = FStar_Syntax_Const.effect_Tot_lid; iface = _63_61.iface; admitted_iface = _63_61.admitted_iface; expect_typ = _63_61.expect_typ}))


let default_ml : env  ->  env = (fun env -> if (has_all_in_scope env) then begin
(

let _63_64 = env
in {curmodule = _63_64.curmodule; curmonad = _63_64.curmonad; modules = _63_64.modules; open_namespaces = _63_64.open_namespaces; modul_abbrevs = _63_64.modul_abbrevs; sigaccum = _63_64.sigaccum; localbindings = _63_64.localbindings; recbindings = _63_64.recbindings; sigmap = _63_64.sigmap; default_result_effect = FStar_Syntax_Const.effect_ML_lid; iface = _63_64.iface; admitted_iface = _63_64.admitted_iface; expect_typ = _63_64.expect_typ})
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
(let _158_123 = (let _158_122 = (FStar_Ident.lid_of_path (("Prims")::(y)::[]) id.FStar_Ident.idRange)
in (FStar_Syntax_Syntax.fvar _158_122 dd dq))
in Some (_158_123))
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
(let _158_130 = (let _158_129 = (bv_to_name x id.FStar_Ident.idRange)
in ((_158_129), (mut)))
in Some (_158_130))
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

let found_in_monad = (match (((lid.FStar_Ident.ns), (env.curmonad))) with
| ([], Some (_63_106)) -> begin
(let _158_139 = (qualify env lid.FStar_Ident.ident)
in (finder _158_139))
end
| _63_110 -> begin
None
end)
in (match (found_in_monad) with
| None -> begin
(

let ids = (FStar_Ident.ids_of_lid lid)
in (FStar_Util.find_map namespaces (fun ns -> (

let full_name = (FStar_Ident.lid_of_ids (FStar_List.append (FStar_Ident.ids_of_lid ns) ids))
in (finder full_name)))))
end
| x -> begin
x
end))
end))
in (let _158_142 = (let _158_141 = (current_module env)
in (_158_141)::env.open_namespaces)
in (aux _158_142))))


let expand_module_abbrev : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (match (lid.FStar_Ident.ns) with
| (_63_122)::_63_120 -> begin
lid
end
| [] -> begin
(

let id = lid.FStar_Ident.ident
in (match ((FStar_List.tryFind (fun _63_129 -> (match (_63_129) with
| (id', _63_128) -> begin
(id.FStar_Ident.idText = id'.FStar_Ident.idText)
end)) env.modul_abbrevs)) with
| None -> begin
lid
end
| Some (_63_132, lid') -> begin
lid'
end))
end))


let expand_module_abbrevs : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (match (lid.FStar_Ident.ns) with
| (id)::rest -> begin
(match ((FStar_All.pipe_right env.modul_abbrevs (FStar_List.tryFind (fun _63_144 -> (match (_63_144) with
| (id', _63_143) -> begin
(id.FStar_Ident.idText = id'.FStar_Ident.idText)
end))))) with
| None -> begin
lid
end
| Some (_63_147, lid') -> begin
(FStar_Ident.lid_of_ids (FStar_List.append (FStar_Ident.ids_of_lid lid') (FStar_List.append rest ((lid.FStar_Ident.ident)::[]))))
end)
end
| _63_152 -> begin
lid
end))


let resolve_in_open_namespaces = (fun env lid finder -> (let _158_159 = (expand_module_abbrevs env lid)
in (resolve_in_open_namespaces' env _158_159 finder)))


let fv_qual_of_se : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.fv_qual Prims.option = (fun _63_3 -> (match (_63_3) with
| FStar_Syntax_Syntax.Sig_datacon (_63_159, _63_161, _63_163, l, _63_166, quals, _63_169, _63_171) -> begin
(

let qopt = (FStar_Util.find_map quals (fun _63_2 -> (match (_63_2) with
| FStar_Syntax_Syntax.RecordConstructor (fs) -> begin
Some (FStar_Syntax_Syntax.Record_ctor (((l), (fs))))
end
| _63_178 -> begin
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
| FStar_Syntax_Syntax.Sig_declare_typ (_63_183, _63_185, _63_187, quals, _63_190) -> begin
None
end
| _63_194 -> begin
None
end))


let lb_fv : FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.fv = (fun lbs lid -> (let _158_168 = (FStar_Util.find_map lbs (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in if (FStar_Syntax_Syntax.fv_eq_lid fv lid) then begin
Some (fv)
end else begin
None
end)))
in (FStar_All.pipe_right _158_168 FStar_Util.must)))


let ns_of_lid_equals : FStar_Ident.lident  ->  FStar_Ident.lident  ->  Prims.bool = (fun lid ns -> (((FStar_List.length lid.FStar_Ident.ns) = (FStar_List.length (FStar_Ident.ids_of_lid ns))) && (let _158_173 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in (FStar_Ident.lid_equals _158_173 ns))))


let try_lookup_name : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  foundname Prims.option = (fun any_val exclude_interf env lid -> (

let occurrence_range = (FStar_Ident.range_of_lid lid)
in (

let find_in_sig = (fun source_lid -> (match ((FStar_Util.smap_try_find (sigmap env) source_lid.FStar_Ident.str)) with
| Some (_63_209, true) when exclude_interf -> begin
None
end
| None -> begin
None
end
| Some (se, _63_216) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_63_220) -> begin
(let _158_186 = (let _158_185 = (let _158_184 = (FStar_Syntax_Syntax.fvar source_lid FStar_Syntax_Syntax.Delta_constant None)
in ((_158_184), (false)))
in Term_name (_158_185))
in Some (_158_186))
end
| FStar_Syntax_Syntax.Sig_datacon (_63_223) -> begin
(let _158_190 = (let _158_189 = (let _158_188 = (let _158_187 = (fv_qual_of_se se)
in (FStar_Syntax_Syntax.fvar source_lid FStar_Syntax_Syntax.Delta_constant _158_187))
in ((_158_188), (false)))
in Term_name (_158_189))
in Some (_158_190))
end
| FStar_Syntax_Syntax.Sig_let ((_63_226, lbs), _63_230, _63_232, _63_234) -> begin
(

let fv = (lb_fv lbs source_lid)
in (let _158_193 = (let _158_192 = (let _158_191 = (FStar_Syntax_Syntax.fvar source_lid fv.FStar_Syntax_Syntax.fv_delta fv.FStar_Syntax_Syntax.fv_qual)
in ((_158_191), (false)))
in Term_name (_158_192))
in Some (_158_193)))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _63_240, _63_242, quals, _63_245) -> begin
if (any_val || (FStar_All.pipe_right quals (FStar_Util.for_some (fun _63_4 -> (match (_63_4) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| _63_251 -> begin
false
end))))) then begin
(

let lid = (FStar_Ident.set_lid_range lid (FStar_Ident.range_of_lid source_lid))
in (

let dd = if ((FStar_Syntax_Util.is_primop_lid lid) || ((ns_of_lid_equals lid FStar_Syntax_Const.prims_lid) && (FStar_All.pipe_right quals (FStar_Util.for_some (fun _63_5 -> (match (_63_5) with
| (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) -> begin
true
end
| _63_261 -> begin
false
end)))))) then begin
FStar_Syntax_Syntax.Delta_equational
end else begin
FStar_Syntax_Syntax.Delta_constant
end
in (match ((FStar_Util.find_map quals (fun _63_6 -> (match (_63_6) with
| FStar_Syntax_Syntax.Reflectable (refl_monad) -> begin
Some (refl_monad)
end
| _63_267 -> begin
None
end)))) with
| Some (refl_monad) -> begin
(

let refl_const = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (refl_monad))) None occurrence_range)
in Some (Term_name (((refl_const), (false)))))
end
| _63_272 -> begin
(let _158_200 = (let _158_199 = (let _158_198 = (let _158_197 = (fv_qual_of_se se)
in (FStar_Syntax_Syntax.fvar lid dd _158_197))
in ((_158_198), (false)))
in Term_name (_158_199))
in Some (_158_200))
end)))
end else begin
None
end
end
| (FStar_Syntax_Syntax.Sig_new_effect_for_free (ne, _)) | (FStar_Syntax_Syntax.Sig_new_effect (ne, _)) -> begin
Some (Eff_name (((se), ((FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname (FStar_Ident.range_of_lid source_lid))))))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (_63_283) -> begin
Some (Eff_name (((se), (source_lid))))
end
| _63_286 -> begin
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
in (FStar_Util.find_map env.recbindings (fun _63_297 -> (match (_63_297) with
| (id, l, dd) -> begin
if (id.FStar_Ident.idText = lid.FStar_Ident.ident.FStar_Ident.idText) then begin
(let _158_204 = (let _158_203 = (let _158_202 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range l (FStar_Ident.range_of_lid lid)) dd None)
in ((_158_202), (false)))
in Term_name (_158_203))
in Some (_158_204))
end else begin
None
end
end))))
end)
end
| _63_299 -> begin
None
end)
in (match (found_id) with
| Some (_63_302) -> begin
found_id
end
| _63_305 -> begin
(resolve_in_open_namespaces env lid find_in_sig)
end)))))


let try_lookup_effect_name' : Prims.bool  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident) Prims.option = (fun exclude_interf env lid -> (match ((try_lookup_name true exclude_interf env lid)) with
| Some (Eff_name (o, l)) -> begin
Some (((o), (l)))
end
| _63_315 -> begin
None
end))


let try_lookup_effect_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env l -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some (o, l) -> begin
Some (l)
end
| _63_323 -> begin
None
end))


let try_lookup_effect_defn : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl Prims.option = (fun env l -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some (FStar_Syntax_Syntax.Sig_new_effect (ne, _63_328), _63_332) -> begin
Some (ne)
end
| Some (FStar_Syntax_Syntax.Sig_new_effect_for_free (ne, _63_337), _63_341) -> begin
Some (ne)
end
| _63_345 -> begin
None
end))


let is_effect_name : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((try_lookup_effect_name env lid)) with
| None -> begin
false
end
| Some (_63_350) -> begin
true
end))


let lookup_letbinding_quals : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.qualifier Prims.list = (fun env lid -> (

let find_in_sig = (fun lid -> (match ((FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str)) with
| Some (FStar_Syntax_Syntax.Sig_declare_typ (lid, _63_358, _63_360, quals, _63_363), _63_367) -> begin
Some (quals)
end
| _63_371 -> begin
None
end))
in (match ((resolve_in_open_namespaces env lid find_in_sig)) with
| Some (quals) -> begin
quals
end
| _63_375 -> begin
[]
end)))


let try_lookup_module : env  ->  Prims.string Prims.list  ->  FStar_Syntax_Syntax.modul Prims.option = (fun env path -> (match ((FStar_List.tryFind (fun _63_380 -> (match (_63_380) with
| (mlid, modul) -> begin
((FStar_Ident.path_of_lid mlid) = path)
end)) env.modules)) with
| Some (_63_382, modul) -> begin
Some (modul)
end
| None -> begin
None
end))


let try_lookup_let : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env lid -> (

let find_in_sig = (fun lid -> (match ((FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str)) with
| Some (FStar_Syntax_Syntax.Sig_let ((_63_392, lbs), _63_396, _63_398, _63_400), _63_404) -> begin
(

let fv = (lb_fv lbs lid)
in (let _158_240 = (FStar_Syntax_Syntax.fvar lid fv.FStar_Syntax_Syntax.fv_delta fv.FStar_Syntax_Syntax.fv_qual)
in Some (_158_240)))
end
| _63_409 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))


let try_lookup_definition : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env lid -> (

let find_in_sig = (fun lid -> (match ((FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str)) with
| Some (FStar_Syntax_Syntax.Sig_let (lbs, _63_416, _63_418, _63_420), _63_424) -> begin
(FStar_Util.find_map (Prims.snd lbs) (fun lb -> (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv lid) -> begin
Some (lb.FStar_Syntax_Syntax.lbdef)
end
| _63_431 -> begin
None
end)))
end
| _63_433 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))


let try_lookup_lid' : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term * Prims.bool) Prims.option = (fun any_val exclude_interf env lid -> (match ((try_lookup_name any_val exclude_interf env lid)) with
| Some (Term_name (e, mut)) -> begin
Some (((e), (mut)))
end
| _63_444 -> begin
None
end))


let try_lookup_lid : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term * Prims.bool) Prims.option = (fun env l -> (try_lookup_lid' env.iface false env l))


let try_lookup_datacon : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.fv Prims.option = (fun env lid -> (

let find_in_sig = (fun lid -> (match ((FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str)) with
| Some (FStar_Syntax_Syntax.Sig_declare_typ (_63_452, _63_454, _63_456, quals, _63_459), _63_463) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _63_7 -> (match (_63_7) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| _63_469 -> begin
false
end)))) then begin
(let _158_267 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant None)
in Some (_158_267))
end else begin
None
end
end
| Some (FStar_Syntax_Syntax.Sig_datacon (_63_471), _63_474) -> begin
(let _158_268 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in Some (_158_268))
end
| _63_478 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))


let find_all_datacons : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.list Prims.option = (fun env lid -> (

let find_in_sig = (fun lid -> (match ((FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str)) with
| Some (FStar_Syntax_Syntax.Sig_inductive_typ (_63_484, _63_486, _63_488, _63_490, _63_492, datas, _63_495, _63_497), _63_501) -> begin
Some (datas)
end
| _63_505 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))


let record_cache_aux : ((Prims.unit  ->  Prims.unit) * (Prims.unit  ->  Prims.unit) * (Prims.unit  ->  record_or_dc Prims.list) * (record_or_dc  ->  Prims.unit) * (Prims.unit  ->  Prims.unit)) = (

let record_cache = (FStar_Util.mk_ref (([])::[]))
in (

let push = (fun _63_508 -> (match (()) with
| () -> begin
(let _158_290 = (let _158_289 = (let _158_287 = (FStar_ST.read record_cache)
in (FStar_List.hd _158_287))
in (let _158_288 = (FStar_ST.read record_cache)
in (_158_289)::_158_288))
in (FStar_ST.op_Colon_Equals record_cache _158_290))
end))
in (

let pop = (fun _63_510 -> (match (()) with
| () -> begin
(let _158_294 = (let _158_293 = (FStar_ST.read record_cache)
in (FStar_List.tl _158_293))
in (FStar_ST.op_Colon_Equals record_cache _158_294))
end))
in (

let peek = (fun _63_512 -> (match (()) with
| () -> begin
(let _158_297 = (FStar_ST.read record_cache)
in (FStar_List.hd _158_297))
end))
in (

let insert = (fun r -> (let _158_304 = (let _158_303 = (let _158_300 = (peek ())
in (r)::_158_300)
in (let _158_302 = (let _158_301 = (FStar_ST.read record_cache)
in (FStar_List.tl _158_301))
in (_158_303)::_158_302))
in (FStar_ST.op_Colon_Equals record_cache _158_304)))
in (

let commit = (fun _63_516 -> (match (()) with
| () -> begin
(match ((FStar_ST.read record_cache)) with
| (hd)::(_63_519)::tl -> begin
(FStar_ST.op_Colon_Equals record_cache ((hd)::tl))
end
| _63_524 -> begin
(FStar_All.failwith "Impossible")
end)
end))
in ((push), (pop), (peek), (insert), (commit))))))))


let push_record_cache : Prims.unit  ->  Prims.unit = (

let _63_534 = record_cache_aux
in (match (_63_534) with
| (push, _63_527, _63_529, _63_531, _63_533) -> begin
push
end))


let pop_record_cache : Prims.unit  ->  Prims.unit = (

let _63_544 = record_cache_aux
in (match (_63_544) with
| (_63_536, pop, _63_539, _63_541, _63_543) -> begin
pop
end))


let peek_record_cache : Prims.unit  ->  record_or_dc Prims.list = (

let _63_554 = record_cache_aux
in (match (_63_554) with
| (_63_546, _63_548, peek, _63_551, _63_553) -> begin
peek
end))


let insert_record_cache : record_or_dc  ->  Prims.unit = (

let _63_564 = record_cache_aux
in (match (_63_564) with
| (_63_556, _63_558, _63_560, insert, _63_563) -> begin
insert
end))


let commit_record_cache : Prims.unit  ->  Prims.unit = (

let _63_574 = record_cache_aux
in (match (_63_574) with
| (_63_566, _63_568, _63_570, _63_572, commit) -> begin
commit
end))


let extract_record : env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun e _63_11 -> (match (_63_11) with
| FStar_Syntax_Syntax.Sig_bundle (sigs, _63_579, _63_581, _63_583) -> begin
(

let is_rec = (FStar_Util.for_some (fun _63_8 -> (match (_63_8) with
| (FStar_Syntax_Syntax.RecordType (_)) | (FStar_Syntax_Syntax.RecordConstructor (_)) -> begin
true
end
| _63_594 -> begin
false
end)))
in (

let find_dc = (fun dc -> (FStar_All.pipe_right sigs (FStar_Util.find_opt (fun _63_9 -> (match (_63_9) with
| FStar_Syntax_Syntax.Sig_datacon (lid, _63_601, _63_603, _63_605, _63_607, _63_609, _63_611, _63_613) -> begin
(FStar_Ident.lid_equals dc lid)
end
| _63_617 -> begin
false
end)))))
in (FStar_All.pipe_right sigs (FStar_List.iter (fun _63_10 -> (match (_63_10) with
| FStar_Syntax_Syntax.Sig_inductive_typ (typename, univs, parms, _63_623, _63_625, (dc)::[], tags, _63_630) -> begin
(match ((let _158_407 = (find_dc dc)
in (FStar_All.pipe_left FStar_Util.must _158_407))) with
| FStar_Syntax_Syntax.Sig_datacon (constrname, _63_635, t, _63_638, _63_640, _63_642, _63_644, _63_646) -> begin
(

let _63_652 = (FStar_Syntax_Util.arrow_formals t)
in (match (_63_652) with
| (formals, _63_651) -> begin
(

let is_rec = (is_rec tags)
in (

let fields = (FStar_All.pipe_right formals (FStar_List.collect (fun _63_656 -> (match (_63_656) with
| (x, q) -> begin
if ((FStar_Syntax_Syntax.is_null_bv x) || (is_rec && (FStar_Syntax_Syntax.is_implicit q))) then begin
[]
end else begin
(let _158_411 = (let _158_410 = (let _158_409 = if is_rec then begin
(FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname)
end else begin
x.FStar_Syntax_Syntax.ppname
end
in (FStar_Syntax_Util.mk_field_projector_name_from_ident constrname _158_409))
in ((_158_410), (x.FStar_Syntax_Syntax.sort)))
in (_158_411)::[])
end
end))))
in (

let record = {typename = typename; constrname = constrname; parms = parms; fields = fields; is_record = is_rec}
in (insert_record_cache record))))
end))
end
| _63_660 -> begin
()
end)
end
| _63_662 -> begin
()
end))))))
end
| _63_664 -> begin
()
end))


let try_lookup_record_or_dc_by_field_name : env  ->  FStar_Ident.lident  ->  (record_or_dc * FStar_Ident.lident) Prims.option = (fun env fieldname -> (

let needs_constrname = (not ((FStar_Syntax_Util.field_projector_contains_constructor fieldname.FStar_Ident.ident.FStar_Ident.idText)))
in (

let find_in_cache = (fun fieldname -> (

let _63_672 = ((fieldname.FStar_Ident.ns), (fieldname.FStar_Ident.ident))
in (match (_63_672) with
| (ns, id) -> begin
(let _158_421 = (peek_record_cache ())
in (FStar_Util.find_map _158_421 (fun record -> (

let constrname = record.constrname.FStar_Ident.ident
in (

let fname = if needs_constrname then begin
(let _158_419 = (FStar_Ident.lid_of_ids (FStar_List.append ns ((constrname)::[])))
in (FStar_Syntax_Util.mk_field_projector_name_from_ident _158_419 id))
end else begin
fieldname
end
in (FStar_Util.find_map record.fields (fun _63_679 -> (match (_63_679) with
| (f, _63_678) -> begin
if (FStar_Ident.lid_equals fname f) then begin
Some (((record), (fname)))
end else begin
None
end
end))))))))
end)))
in (resolve_in_open_namespaces env fieldname find_in_cache))))


let try_lookup_record_by_field_name : env  ->  FStar_Ident.lident  ->  (record_or_dc * FStar_Ident.lident) Prims.option = (fun env fieldname -> (match ((try_lookup_record_or_dc_by_field_name env fieldname)) with
| Some (r, f) when r.is_record -> begin
Some (((r), (f)))
end
| _63_687 -> begin
None
end))


let try_lookup_projector_by_field_name : env  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * Prims.bool) Prims.option = (fun env fieldname -> (match ((try_lookup_record_or_dc_by_field_name env fieldname)) with
| Some (r, f) -> begin
Some (((f), (r.is_record)))
end
| _63_695 -> begin
None
end))


let qualify_field_to_record : env  ->  record_or_dc  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env recd f -> (

let qualify = (fun fieldname -> (

let _63_703 = ((fieldname.FStar_Ident.ns), (fieldname.FStar_Ident.ident))
in (match (_63_703) with
| (ns, fieldname) -> begin
(

let constrname = recd.constrname.FStar_Ident.ident
in (

let fname = (let _158_438 = (FStar_Ident.lid_of_ids (FStar_List.append ns ((constrname)::[])))
in (FStar_Syntax_Util.mk_field_projector_name_from_ident _158_438 fieldname))
in (FStar_Util.find_map recd.fields (fun _63_709 -> (match (_63_709) with
| (f, _63_708) -> begin
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

let _63_714 = env
in {curmodule = _63_714.curmodule; curmonad = _63_714.curmonad; modules = _63_714.modules; open_namespaces = []; modul_abbrevs = _63_714.modul_abbrevs; sigaccum = _63_714.sigaccum; localbindings = _63_714.localbindings; recbindings = _63_714.recbindings; sigmap = _63_714.sigmap; default_result_effect = _63_714.default_result_effect; iface = _63_714.iface; admitted_iface = _63_714.admitted_iface; expect_typ = _63_714.expect_typ})
in (match ((try_lookup_lid' any_val exclude_if env lid)) with
| None -> begin
true
end
| Some (_63_719) -> begin
false
end)))


let push_bv' : env  ->  FStar_Ident.ident  ->  Prims.bool  ->  (env * FStar_Syntax_Syntax.bv) = (fun env x is_mutable -> (

let bv = (FStar_Syntax_Syntax.gen_bv x.FStar_Ident.idText (Some (x.FStar_Ident.idRange)) FStar_Syntax_Syntax.tun)
in (((

let _63_725 = env
in {curmodule = _63_725.curmodule; curmonad = _63_725.curmonad; modules = _63_725.modules; open_namespaces = _63_725.open_namespaces; modul_abbrevs = _63_725.modul_abbrevs; sigaccum = _63_725.sigaccum; localbindings = (((x), (bv), (is_mutable)))::env.localbindings; recbindings = _63_725.recbindings; sigmap = _63_725.sigmap; default_result_effect = _63_725.default_result_effect; iface = _63_725.iface; admitted_iface = _63_725.admitted_iface; expect_typ = _63_725.expect_typ})), (bv))))


let push_bv_mutable : env  ->  FStar_Ident.ident  ->  (env * FStar_Syntax_Syntax.bv) = (fun env x -> (push_bv' env x true))


let push_bv : env  ->  FStar_Ident.ident  ->  (env * FStar_Syntax_Syntax.bv) = (fun env x -> (push_bv' env x false))


let push_top_level_rec_binding : env  ->  FStar_Ident.ident  ->  FStar_Syntax_Syntax.delta_depth  ->  env = (fun env x dd -> (

let l = (qualify env x)
in if (unique false true env l) then begin
(

let _63_735 = env
in {curmodule = _63_735.curmodule; curmonad = _63_735.curmonad; modules = _63_735.modules; open_namespaces = _63_735.open_namespaces; modul_abbrevs = _63_735.modul_abbrevs; sigaccum = _63_735.sigaccum; localbindings = _63_735.localbindings; recbindings = (((x), (l), (dd)))::env.recbindings; sigmap = _63_735.sigmap; default_result_effect = _63_735.default_result_effect; iface = _63_735.iface; admitted_iface = _63_735.admitted_iface; expect_typ = _63_735.expect_typ})
end else begin
(Prims.raise (FStar_Syntax_Syntax.Error ((((Prims.strcat "Duplicate top-level names " l.FStar_Ident.str)), ((FStar_Ident.range_of_lid l))))))
end))


let push_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env s -> (

let err = (fun l -> (

let sopt = (FStar_Util.smap_try_find (sigmap env) l.FStar_Ident.str)
in (

let r = (match (sopt) with
| Some (se, _63_744) -> begin
(match ((let _158_474 = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_Util.find_opt (FStar_Ident.lid_equals l) _158_474))) with
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
in (let _158_477 = (let _158_476 = (let _158_475 = (FStar_Util.format2 "Duplicate top-level names [%s]; previously declared at %s" (FStar_Ident.text_of_lid l) r)
in ((_158_475), ((FStar_Ident.range_of_lid l))))
in FStar_Syntax_Syntax.Error (_158_476))
in (Prims.raise _158_477)))))
in (

let env = (

let _63_762 = (match (s) with
| FStar_Syntax_Syntax.Sig_let (_63_753) -> begin
((false), (true))
end
| FStar_Syntax_Syntax.Sig_bundle (_63_756) -> begin
((true), (true))
end
| _63_759 -> begin
((false), (false))
end)
in (match (_63_762) with
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

let _63_766 = (extract_record env s)
in (

let _63_768 = env
in {curmodule = _63_768.curmodule; curmonad = _63_768.curmonad; modules = _63_768.modules; open_namespaces = _63_768.open_namespaces; modul_abbrevs = _63_768.modul_abbrevs; sigaccum = (s)::env.sigaccum; localbindings = _63_768.localbindings; recbindings = _63_768.recbindings; sigmap = _63_768.sigmap; default_result_effect = _63_768.default_result_effect; iface = _63_768.iface; admitted_iface = _63_768.admitted_iface; expect_typ = _63_768.expect_typ}))
end
| Some (l) -> begin
(err l)
end))
end))
in (

let _63_787 = (match (s) with
| FStar_Syntax_Syntax.Sig_bundle (ses, _63_775, _63_777, _63_779) -> begin
(let _158_481 = (FStar_List.map (fun se -> (let _158_480 = (FStar_Syntax_Util.lids_of_sigelt se)
in ((_158_480), (se)))) ses)
in ((env), (_158_481)))
end
| _63_784 -> begin
(let _158_484 = (let _158_483 = (let _158_482 = (FStar_Syntax_Util.lids_of_sigelt s)
in ((_158_482), (s)))
in (_158_483)::[])
in ((env), (_158_484)))
end)
in (match (_63_787) with
| (env, lss) -> begin
(

let _63_792 = (FStar_All.pipe_right lss (FStar_List.iter (fun _63_790 -> (match (_63_790) with
| (lids, se) -> begin
(FStar_All.pipe_right lids (FStar_List.iter (fun lid -> (FStar_Util.smap_add (sigmap env) lid.FStar_Ident.str ((se), ((env.iface && (not (env.admitted_iface)))))))))
end))))
in env)
end)))))


let push_namespace : env  ->  FStar_Ident.lident  ->  env = (fun env ns -> (

let modules = env.modules
in if (FStar_All.pipe_right modules (FStar_Util.for_some (fun _63_800 -> (match (_63_800) with
| (m, _63_799) -> begin
(FStar_Util.starts_with (FStar_Ident.text_of_lid m) (FStar_Ident.text_of_lid ns))
end)))) then begin
(

let _63_801 = env
in {curmodule = _63_801.curmodule; curmonad = _63_801.curmonad; modules = _63_801.modules; open_namespaces = (ns)::env.open_namespaces; modul_abbrevs = _63_801.modul_abbrevs; sigaccum = _63_801.sigaccum; localbindings = _63_801.localbindings; recbindings = _63_801.recbindings; sigmap = _63_801.sigmap; default_result_effect = _63_801.default_result_effect; iface = _63_801.iface; admitted_iface = _63_801.admitted_iface; expect_typ = _63_801.expect_typ})
end else begin
(let _158_494 = (let _158_493 = (let _158_492 = (FStar_Util.format1 "Namespace %s cannot be found" (FStar_Ident.text_of_lid ns))
in ((_158_492), ((FStar_Ident.range_of_lid ns))))
in FStar_Syntax_Syntax.Error (_158_493))
in (Prims.raise _158_494))
end))


let push_module_abbrev : env  ->  FStar_Ident.ident  ->  FStar_Ident.lident  ->  env = (fun env x l -> if (FStar_All.pipe_right env.modul_abbrevs (FStar_Util.for_some (fun _63_809 -> (match (_63_809) with
| (y, _63_808) -> begin
(x.FStar_Ident.idText = y.FStar_Ident.idText)
end)))) then begin
(let _158_504 = (let _158_503 = (let _158_502 = (FStar_Util.format1 "Module %s is already defined" x.FStar_Ident.idText)
in ((_158_502), (x.FStar_Ident.idRange)))
in FStar_Syntax_Syntax.Error (_158_503))
in (Prims.raise _158_504))
end else begin
(

let modules = env.modules
in if (FStar_All.pipe_right modules (FStar_Util.for_some (fun _63_814 -> (match (_63_814) with
| (m, _63_813) -> begin
(FStar_Ident.lid_equals m l)
end)))) then begin
(

let _63_815 = env
in {curmodule = _63_815.curmodule; curmonad = _63_815.curmonad; modules = _63_815.modules; open_namespaces = _63_815.open_namespaces; modul_abbrevs = (((x), (l)))::env.modul_abbrevs; sigaccum = _63_815.sigaccum; localbindings = _63_815.localbindings; recbindings = _63_815.recbindings; sigmap = _63_815.sigmap; default_result_effect = _63_815.default_result_effect; iface = _63_815.iface; admitted_iface = _63_815.admitted_iface; expect_typ = _63_815.expect_typ})
end else begin
(let _158_508 = (let _158_507 = (let _158_506 = (FStar_Util.format1 "Module %s cannot be found" (FStar_Ident.text_of_lid l))
in ((_158_506), ((FStar_Ident.range_of_lid l))))
in FStar_Syntax_Syntax.Error (_158_507))
in (Prims.raise _158_508))
end)
end)


let check_admits : env  ->  Prims.unit = (fun env -> (FStar_All.pipe_right env.sigaccum (FStar_List.iter (fun se -> (match (se) with
| FStar_Syntax_Syntax.Sig_declare_typ (l, u, t, quals, r) -> begin
(match ((try_lookup_lid env l)) with
| None -> begin
(

let _63_827 = (let _158_514 = (let _158_513 = (FStar_Range.string_of_range (FStar_Ident.range_of_lid l))
in (let _158_512 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format2 "%s: Warning: Admitting %s without a definition\n" _158_513 _158_512)))
in (FStar_Util.print_string _158_514))
in (FStar_Util.smap_add (sigmap env) l.FStar_Ident.str ((FStar_Syntax_Syntax.Sig_declare_typ (((l), (u), (t), ((FStar_Syntax_Syntax.Assumption)::quals), (r)))), (false))))
end
| Some (_63_830) -> begin
()
end)
end
| _63_833 -> begin
()
end)))))


let finish : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env modul -> (

let _63_893 = (FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations (FStar_List.iter (fun _63_13 -> (match (_63_13) with
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _63_840, _63_842) -> begin
if ((FStar_List.contains FStar_Syntax_Syntax.Private quals) || (FStar_List.contains FStar_Syntax_Syntax.Abstract quals)) then begin
(FStar_All.pipe_right ses (FStar_List.iter (fun _63_12 -> (match (_63_12) with
| FStar_Syntax_Syntax.Sig_datacon (lid, _63_848, _63_850, _63_852, _63_854, _63_856, _63_858, _63_860) -> begin
(FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str)
end
| _63_864 -> begin
()
end))))
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _63_867, _63_869, quals, _63_872) -> begin
if (FStar_List.contains FStar_Syntax_Syntax.Private quals) then begin
(FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str)
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_let ((_63_876, lbs), r, _63_881, quals) -> begin
(

let _63_886 = if ((FStar_List.contains FStar_Syntax_Syntax.Private quals) || (FStar_List.contains FStar_Syntax_Syntax.Abstract quals)) then begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (let _158_525 = (let _158_524 = (let _158_523 = (let _158_522 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _158_522.FStar_Syntax_Syntax.fv_name)
in _158_523.FStar_Syntax_Syntax.v)
in _158_524.FStar_Ident.str)
in (FStar_Util.smap_remove (sigmap env) _158_525)))))
end else begin
()
end
in if ((FStar_List.contains FStar_Syntax_Syntax.Abstract quals) && (not ((FStar_List.contains FStar_Syntax_Syntax.Private quals)))) then begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (

let lid = (let _158_528 = (let _158_527 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _158_527.FStar_Syntax_Syntax.fv_name)
in _158_528.FStar_Syntax_Syntax.v)
in (

let decl = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), ((FStar_Syntax_Syntax.Assumption)::quals), (r)))
in (FStar_Util.smap_add (sigmap env) lid.FStar_Ident.str ((decl), (false))))))))
end else begin
()
end)
end
| _63_892 -> begin
()
end))))
in (

let _63_895 = env
in {curmodule = None; curmonad = _63_895.curmonad; modules = (((modul.FStar_Syntax_Syntax.name), (modul)))::env.modules; open_namespaces = []; modul_abbrevs = []; sigaccum = []; localbindings = []; recbindings = []; sigmap = _63_895.sigmap; default_result_effect = _63_895.default_result_effect; iface = _63_895.iface; admitted_iface = _63_895.admitted_iface; expect_typ = _63_895.expect_typ})))


type env_stack_ops =
{push : env  ->  env; mark : env  ->  env; reset_mark : env  ->  env; commit_mark : env  ->  env; pop : env  ->  env}


let is_Mkenv_stack_ops : env_stack_ops  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv_stack_ops"))))


let stack_ops : env_stack_ops = (

let stack = (FStar_Util.mk_ref [])
in (

let push = (fun env -> (

let _63_906 = (push_record_cache ())
in (

let _63_908 = (let _158_578 = (let _158_577 = (FStar_ST.read stack)
in (env)::_158_577)
in (FStar_ST.op_Colon_Equals stack _158_578))
in (

let _63_910 = env
in (let _158_579 = (FStar_Util.smap_copy (sigmap env))
in {curmodule = _63_910.curmodule; curmonad = _63_910.curmonad; modules = _63_910.modules; open_namespaces = _63_910.open_namespaces; modul_abbrevs = _63_910.modul_abbrevs; sigaccum = _63_910.sigaccum; localbindings = _63_910.localbindings; recbindings = _63_910.recbindings; sigmap = _158_579; default_result_effect = _63_910.default_result_effect; iface = _63_910.iface; admitted_iface = _63_910.admitted_iface; expect_typ = _63_910.expect_typ})))))
in (

let pop = (fun env -> (match ((FStar_ST.read stack)) with
| (env)::tl -> begin
(

let _63_917 = (pop_record_cache ())
in (

let _63_919 = (FStar_ST.op_Colon_Equals stack tl)
in env))
end
| _63_922 -> begin
(FStar_All.failwith "Impossible: Too many pops")
end))
in (

let commit_mark = (fun env -> (

let _63_925 = (commit_record_cache ())
in (match ((FStar_ST.read stack)) with
| (_63_929)::tl -> begin
(

let _63_931 = (FStar_ST.op_Colon_Equals stack tl)
in env)
end
| _63_934 -> begin
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
| (l)::_63_945 -> begin
(l.FStar_Ident.nsstr = m.FStar_Ident.str)
end
| _63_949 -> begin
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

let _63_973 = (FStar_All.pipe_right keys (FStar_List.iter (fun k -> (match ((FStar_Util.smap_try_find sm' k)) with
| Some (se, true) when (sigelt_in_m se) -> begin
(

let _63_959 = (FStar_Util.smap_remove sm' k)
in (

let se = (match (se) with
| FStar_Syntax_Syntax.Sig_declare_typ (l, u, t, q, r) -> begin
FStar_Syntax_Syntax.Sig_declare_typ (((l), (u), (t), ((FStar_Syntax_Syntax.Assumption)::q), (r)))
end
| _63_969 -> begin
se
end)
in (FStar_Util.smap_add sm' k ((se), (false)))))
end
| _63_972 -> begin
()
end))))
in env)))))))


let finish_module_or_interface : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env modul -> (

let _63_977 = if (not (modul.FStar_Syntax_Syntax.is_interface)) then begin
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

let _63_988 = env
in {curmodule = Some (mname); curmonad = _63_988.curmonad; modules = _63_988.modules; open_namespaces = open_ns; modul_abbrevs = _63_988.modul_abbrevs; sigaccum = _63_988.sigaccum; localbindings = _63_988.localbindings; recbindings = _63_988.recbindings; sigmap = env.sigmap; default_result_effect = if ((FStar_Ident.lid_equals mname FStar_Syntax_Const.all_lid) || (has_all_in_scope env)) then begin
FStar_Syntax_Const.effect_ML_lid
end else begin
FStar_Syntax_Const.effect_Tot_lid
end; iface = intf; admitted_iface = admitted; expect_typ = _63_988.expect_typ}))))
in (match ((FStar_All.pipe_right env.modules (FStar_Util.find_opt (fun _63_993 -> (match (_63_993) with
| (l, _63_992) -> begin
(FStar_Ident.lid_equals l mname)
end))))) with
| None -> begin
(let _158_616 = (prep env)
in ((_158_616), (false)))
end
| Some (_63_996, m) -> begin
(

let _63_1000 = if ((not (m.FStar_Syntax_Syntax.is_interface)) || intf) then begin
(let _158_619 = (let _158_618 = (let _158_617 = (FStar_Util.format1 "Duplicate module or interface name: %s" mname.FStar_Ident.str)
in ((_158_617), ((FStar_Ident.range_of_lid mname))))
in FStar_Syntax_Syntax.Error (_158_618))
in (Prims.raise _158_619))
end else begin
()
end
in (let _158_621 = (let _158_620 = (push env)
in (prep _158_620))
in ((_158_621), (true))))
end)))


let enter_monad_scope : env  ->  FStar_Ident.ident  ->  env = (fun env mname -> (match (env.curmonad) with
| Some (mname') -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((((Prims.strcat "Trying to define monad " (Prims.strcat mname.FStar_Ident.idText (Prims.strcat ", but already in monad scope " mname'.FStar_Ident.idText)))), (mname.FStar_Ident.idRange)))))
end
| None -> begin
(

let _63_1007 = env
in {curmodule = _63_1007.curmodule; curmonad = Some (mname); modules = _63_1007.modules; open_namespaces = _63_1007.open_namespaces; modul_abbrevs = _63_1007.modul_abbrevs; sigaccum = _63_1007.sigaccum; localbindings = _63_1007.localbindings; recbindings = _63_1007.recbindings; sigmap = _63_1007.sigmap; default_result_effect = _63_1007.default_result_effect; iface = _63_1007.iface; admitted_iface = _63_1007.admitted_iface; expect_typ = _63_1007.expect_typ})
end))


let fail_or = (fun env lookup lid -> (match ((lookup lid)) with
| None -> begin
(

let opened_modules = (FStar_List.map (fun _63_1016 -> (match (_63_1016) with
| (lid, _63_1015) -> begin
(FStar_Ident.text_of_lid lid)
end)) env.modules)
in (

let module_of_the_lid = (let _158_633 = (FStar_Ident.path_of_ns lid.FStar_Ident.ns)
in (FStar_Ident.text_of_path _158_633))
in (

let msg = (FStar_Util.format1 "Identifier not found: [%s]" (FStar_Ident.text_of_lid lid))
in (

let msg = (match (env.curmodule) with
| Some (m) when (((FStar_Ident.text_of_lid m) = module_of_the_lid) || (module_of_the_lid = "")) -> begin
msg
end
| _63_1023 when (FStar_List.existsb (fun m -> (m = module_of_the_lid)) opened_modules) -> begin
msg
end
| _63_1026 -> begin
(let _158_638 = (let _158_637 = (let _158_636 = (let _158_635 = (FStar_Ident.path_of_ns lid.FStar_Ident.ns)
in (FStar_Ident.text_of_path _158_635))
in (FStar_Util.format3 "Hint: %s belongs to module %s, which does not belong to the list of modules in scope, namely %s" (FStar_Ident.text_of_lid lid) _158_636 (FStar_String.concat ", " opened_modules)))
in (Prims.strcat "\n" _158_637))
in (Prims.strcat msg _158_638))
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




