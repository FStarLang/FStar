
open Prims
type env =
{curmodule : FStar_Ident.lident Prims.option; modules : (FStar_Ident.lident * FStar_Syntax_Syntax.modul) Prims.list; open_namespaces : FStar_Ident.lident Prims.list; sigaccum : FStar_Syntax_Syntax.sigelts; localbindings : (FStar_Ident.ident * FStar_Syntax_Syntax.bv) Prims.list; recbindings : (FStar_Ident.ident * FStar_Ident.lident) Prims.list; sigmap : (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap Prims.list; default_result_effect : FStar_Ident.lident; iface : Prims.bool; admitted_iface : Prims.bool; expect_typ : Prims.bool}

let is_Mkenv : env  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv"))))

let open_modules : env  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.modul) Prims.list = (fun e -> e.modules)

let current_module : env  ->  FStar_Ident.lident = (fun env -> (match (env.curmodule) with
| None -> begin
(FStar_All.failwith "Unset current module")
end
| Some (m) -> begin
m
end))

let qual : FStar_Ident.lident  ->  FStar_Ident.ident  ->  FStar_Ident.lident = (fun lid id -> (let _169_43 = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns ((lid.FStar_Ident.ident)::(id)::[])))
in (FStar_Ident.set_lid_range _169_43 id.FStar_Ident.idRange)))

let qualify : env  ->  FStar_Ident.ident  ->  FStar_Ident.lident = (fun env id -> (let _169_48 = (current_module env)
in (qual _169_48 id)))

let qualify_lid : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (let cur = (current_module env)
in (let _169_53 = (FStar_Ident.lid_of_ids (FStar_List.append (FStar_List.append (FStar_List.append cur.FStar_Ident.ns ((cur.FStar_Ident.ident)::[])) lid.FStar_Ident.ns) ((lid.FStar_Ident.ident)::[])))
in (FStar_Ident.set_lid_range _169_53 (FStar_Ident.range_of_lid lid)))))

let new_sigmap = (fun _66_36 -> (match (()) with
| () -> begin
(FStar_Util.smap_create 100)
end))

let empty_env : Prims.unit  ->  env = (fun _66_37 -> (match (()) with
| () -> begin
(let _169_58 = (let _169_57 = (new_sigmap ())
in (_169_57)::[])
in {curmodule = None; modules = []; open_namespaces = []; sigaccum = []; localbindings = []; recbindings = []; sigmap = _169_58; default_result_effect = FStar_Syntax_Const.effect_ML_lid; iface = false; admitted_iface = false; expect_typ = false})
end))

let sigmap : env  ->  (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap = (fun env -> (FStar_List.hd env.sigmap))

let default_total : env  ->  env = (fun env -> (let _66_40 = env
in {curmodule = _66_40.curmodule; modules = _66_40.modules; open_namespaces = _66_40.open_namespaces; sigaccum = _66_40.sigaccum; localbindings = _66_40.localbindings; recbindings = _66_40.recbindings; sigmap = _66_40.sigmap; default_result_effect = FStar_Syntax_Const.effect_Tot_lid; iface = _66_40.iface; admitted_iface = _66_40.admitted_iface; expect_typ = _66_40.expect_typ}))

let default_ml : env  ->  env = (fun env -> (let _66_43 = env
in {curmodule = _66_43.curmodule; modules = _66_43.modules; open_namespaces = _66_43.open_namespaces; sigaccum = _66_43.sigaccum; localbindings = _66_43.localbindings; recbindings = _66_43.recbindings; sigmap = _66_43.sigmap; default_result_effect = FStar_Syntax_Const.effect_ML_lid; iface = _66_43.iface; admitted_iface = _66_43.admitted_iface; expect_typ = _66_43.expect_typ}))

let set_bv_range : FStar_Syntax_Syntax.bv  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.bv = (fun bv r -> (let id = (let _66_47 = bv.FStar_Syntax_Syntax.ppname
in {FStar_Ident.idText = _66_47.FStar_Ident.idText; FStar_Ident.idRange = r})
in (let _66_50 = bv
in {FStar_Syntax_Syntax.ppname = id; FStar_Syntax_Syntax.index = _66_50.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _66_50.FStar_Syntax_Syntax.sort})))

let bv_to_name : FStar_Syntax_Syntax.bv  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.term = (fun bv r -> (FStar_Syntax_Syntax.bv_to_name (set_bv_range bv r)))

let unmangleMap : (Prims.string * Prims.string) Prims.list = (("op_ColonColon", "Cons"))::(("not", "op_Negation"))::[]

let unmangleOpName : FStar_Ident.ident  ->  FStar_Ident.lident Prims.option = (fun id -> (FStar_Util.find_map unmangleMap (fun _66_57 -> (match (_66_57) with
| (x, y) -> begin
if (id.FStar_Ident.idText = x) then begin
(let _169_76 = (FStar_Ident.lid_of_path (("Prims")::(y)::[]) id.FStar_Ident.idRange)
in Some (_169_76))
end else begin
None
end
end))))

let try_lookup_id : env  ->  FStar_Ident.ident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env id -> (match ((unmangleOpName id)) with
| Some (l) -> begin
(let _169_81 = (FStar_Syntax_Syntax.fvar None l id.FStar_Ident.idRange)
in Some (_169_81))
end
| _66_63 -> begin
(FStar_Util.find_map env.localbindings (fun _66_1 -> (match (_66_1) with
| (id', x) when (id'.FStar_Ident.idText = id.FStar_Ident.idText) -> begin
(let _169_83 = (bv_to_name x id.FStar_Ident.idRange)
in Some (_169_83))
end
| _66_69 -> begin
None
end)))
end))

let resolve_in_open_namespaces = (fun env lid finder -> (let aux = (fun namespaces -> (match ((finder lid)) with
| Some (r) -> begin
Some (r)
end
| _66_79 -> begin
(let ids = (FStar_Ident.ids_of_lid lid)
in (FStar_Util.find_map namespaces (fun ns -> (let full_name = (FStar_Ident.lid_of_ids (FStar_List.append (FStar_Ident.ids_of_lid ns) ids))
in (finder full_name)))))
end))
in (let _169_98 = (let _169_97 = (current_module env)
in (_169_97)::env.open_namespaces)
in (aux _169_98))))

type foundname =
| Term_name of FStar_Syntax_Syntax.typ
| Eff_name of (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident)

let is_Term_name : foundname  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Term_name (_) -> begin
true
end
| _ -> begin
false
end))

let is_Eff_name : foundname  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Eff_name (_) -> begin
true
end
| _ -> begin
false
end))

let ___Term_name____0 : foundname  ->  FStar_Syntax_Syntax.typ = (fun projectee -> (match (projectee) with
| Term_name (_66_85) -> begin
_66_85
end))

let ___Eff_name____0 : foundname  ->  (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident) = (fun projectee -> (match (projectee) with
| Eff_name (_66_88) -> begin
_66_88
end))

let fv_qual_of_se : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.fv_qual Prims.option = (fun _66_3 -> (match (_66_3) with
| FStar_Syntax_Syntax.Sig_datacon (_66_91, _66_93, _66_95, l, _66_98, quals, _66_101, _66_103) -> begin
(let qopt = (FStar_Util.find_map quals (fun _66_2 -> (match (_66_2) with
| FStar_Syntax_Syntax.RecordConstructor (fs) -> begin
Some (FStar_Syntax_Syntax.Record_ctor ((l, fs)))
end
| _66_110 -> begin
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
| FStar_Syntax_Syntax.Sig_declare_typ (_66_115, _66_117, _66_119, quals, _66_122) -> begin
None
end
| _66_126 -> begin
None
end))

let try_lookup_name : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  foundname Prims.option = (fun any_val exclude_interf env lid -> (let find_in_sig = (fun lid -> (match ((let _169_140 = (sigmap env)
in (FStar_Util.smap_try_find _169_140 lid.FStar_Ident.str))) with
| Some (_66_134, true) when exclude_interf -> begin
None
end
| None -> begin
None
end
| Some (se, _66_141) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_66_145) -> begin
(let _169_142 = (let _169_141 = (FStar_Syntax_Syntax.fvar None lid (FStar_Ident.range_of_lid lid))
in Term_name (_169_141))
in Some (_169_142))
end
| FStar_Syntax_Syntax.Sig_datacon (_66_148) -> begin
(let _169_145 = (let _169_144 = (let _169_143 = (fv_qual_of_se se)
in (FStar_Syntax_Syntax.fvar _169_143 lid (FStar_Ident.range_of_lid lid)))
in Term_name (_169_144))
in Some (_169_145))
end
| FStar_Syntax_Syntax.Sig_let (_66_151) -> begin
(let _169_147 = (let _169_146 = (FStar_Syntax_Syntax.fvar None lid (FStar_Ident.range_of_lid lid))
in Term_name (_169_146))
in Some (_169_147))
end
| FStar_Syntax_Syntax.Sig_declare_typ (_66_154, _66_156, _66_158, quals, _66_161) -> begin
if (any_val || (FStar_All.pipe_right quals (FStar_Util.for_some (fun _66_4 -> (match (_66_4) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| _66_167 -> begin
false
end))))) then begin
(let _169_151 = (let _169_150 = (let _169_149 = (fv_qual_of_se se)
in (FStar_Syntax_Syntax.fvar _169_149 lid (FStar_Ident.range_of_lid lid)))
in Term_name (_169_150))
in Some (_169_151))
end else begin
None
end
end
| FStar_Syntax_Syntax.Sig_new_effect (ne, _66_170) -> begin
(let _169_154 = (let _169_153 = (let _169_152 = (FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname (FStar_Ident.range_of_lid lid))
in (se, _169_152))
in Eff_name (_169_153))
in Some (_169_154))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (_66_174) -> begin
Some (Eff_name ((se, lid)))
end
| _66_177 -> begin
None
end)
end))
in (let found_id = (match (lid.FStar_Ident.ns) with
| [] -> begin
(match ((try_lookup_id env lid.FStar_Ident.ident)) with
| Some (e) -> begin
Some (Term_name (e))
end
| None -> begin
(let recname = (qualify env lid.FStar_Ident.ident)
in (FStar_Util.find_map env.recbindings (fun _66_185 -> (match (_66_185) with
| (id, l) -> begin
if (id.FStar_Ident.idText = lid.FStar_Ident.ident.FStar_Ident.idText) then begin
(let _169_158 = (let _169_157 = (let _169_156 = (FStar_Ident.set_lid_range l (FStar_Ident.range_of_lid lid))
in (FStar_Syntax_Syntax.fvar None _169_156 (FStar_Ident.range_of_lid lid)))
in Term_name (_169_157))
in Some (_169_158))
end else begin
None
end
end))))
end)
end
| _66_187 -> begin
None
end)
in (match (found_id) with
| Some (_66_190) -> begin
found_id
end
| _66_193 -> begin
(resolve_in_open_namespaces env lid find_in_sig)
end))))

let try_lookup_effect_name' : Prims.bool  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident) Prims.option = (fun exclude_interf env lid -> (match ((try_lookup_name true exclude_interf env lid)) with
| Some (Eff_name (o, l)) -> begin
Some ((o, l))
end
| _66_203 -> begin
None
end))

let try_lookup_effect_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env l -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some (o, l) -> begin
Some (l)
end
| _66_211 -> begin
None
end))

let try_lookup_effect_defn : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl Prims.option = (fun env l -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some (FStar_Syntax_Syntax.Sig_new_effect (ne, _66_216), _66_220) -> begin
Some (ne)
end
| _66_224 -> begin
None
end))

let is_effect_name : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((try_lookup_effect_name env lid)) with
| None -> begin
false
end
| Some (_66_229) -> begin
true
end))

let lookup_letbinding_quals : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.qualifier Prims.list = (fun env lid -> (let find_in_sig = (fun lid -> (match ((let _169_183 = (sigmap env)
in (FStar_Util.smap_try_find _169_183 lid.FStar_Ident.str))) with
| Some (FStar_Syntax_Syntax.Sig_declare_typ (lid, _66_237, _66_239, quals, _66_242), _66_246) -> begin
Some (quals)
end
| _66_250 -> begin
None
end))
in (match ((resolve_in_open_namespaces env lid find_in_sig)) with
| Some (quals) -> begin
quals
end
| _66_254 -> begin
[]
end)))

let try_lookup_module : env  ->  Prims.string Prims.list  ->  FStar_Syntax_Syntax.modul Prims.option = (fun env path -> (match ((FStar_List.tryFind (fun _66_259 -> (match (_66_259) with
| (mlid, modul) -> begin
((FStar_Ident.path_of_lid mlid) = path)
end)) env.modules)) with
| Some (_66_261, modul) -> begin
Some (modul)
end
| None -> begin
None
end))

let try_lookup_let : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env lid -> (let find_in_sig = (fun lid -> (match ((let _169_195 = (sigmap env)
in (FStar_Util.smap_try_find _169_195 lid.FStar_Ident.str))) with
| Some (FStar_Syntax_Syntax.Sig_let (_66_271), _66_274) -> begin
(let _169_196 = (FStar_Syntax_Syntax.fvar None lid (FStar_Ident.range_of_lid lid))
in Some (_169_196))
end
| _66_278 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))

let try_lookup_definition : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env lid -> (let find_in_sig = (fun lid -> (match ((let _169_203 = (sigmap env)
in (FStar_Util.smap_try_find _169_203 lid.FStar_Ident.str))) with
| Some (FStar_Syntax_Syntax.Sig_let (lbs, _66_285, _66_287, _66_289), _66_293) -> begin
(FStar_Util.find_map (Prims.snd lbs) (fun lb -> (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (lid') when (FStar_Ident.lid_equals lid lid') -> begin
Some (lb.FStar_Syntax_Syntax.lbdef)
end
| _66_300 -> begin
None
end)))
end
| _66_302 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))

let try_lookup_lid' : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun any_val exclude_interf env lid -> (match ((try_lookup_name any_val exclude_interf env lid)) with
| Some (Term_name (e)) -> begin
Some (e)
end
| _66_311 -> begin
None
end))

let try_lookup_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env l -> (try_lookup_lid' env.iface false env l))

let try_lookup_datacon : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.fv Prims.option = (fun env lid -> (let find_in_sig = (fun lid -> (match ((let _169_223 = (sigmap env)
in (FStar_Util.smap_try_find _169_223 lid.FStar_Ident.str))) with
| Some (FStar_Syntax_Syntax.Sig_declare_typ (_66_319, _66_321, _66_323, quals, _66_326), _66_330) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _66_5 -> (match (_66_5) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| _66_336 -> begin
false
end)))) then begin
(let _169_225 = (FStar_Syntax_Syntax.lid_as_fv lid None)
in Some (_169_225))
end else begin
None
end
end
| Some (FStar_Syntax_Syntax.Sig_datacon (_66_338), _66_341) -> begin
(let _169_226 = (FStar_Syntax_Syntax.lid_as_fv lid (Some (FStar_Syntax_Syntax.Data_ctor)))
in Some (_169_226))
end
| _66_345 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))

let find_all_datacons : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.list Prims.option = (fun env lid -> (let find_in_sig = (fun lid -> (match ((let _169_233 = (sigmap env)
in (FStar_Util.smap_try_find _169_233 lid.FStar_Ident.str))) with
| Some (FStar_Syntax_Syntax.Sig_inductive_typ (_66_351, _66_353, _66_355, _66_357, _66_359, datas, _66_362, _66_364), _66_368) -> begin
Some (datas)
end
| _66_372 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))

type record_or_dc =
{typename : FStar_Ident.lident; constrname : FStar_Ident.lident; parms : FStar_Syntax_Syntax.binders; fields : (FStar_Syntax_Syntax.fieldname * FStar_Syntax_Syntax.typ) Prims.list; is_record : Prims.bool}

let is_Mkrecord_or_dc : record_or_dc  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkrecord_or_dc"))))

let record_cache_aux : ((Prims.unit  ->  Prims.unit) * (Prims.unit  ->  Prims.unit) * (Prims.unit  ->  record_or_dc Prims.list) * (record_or_dc  ->  Prims.unit)) = (let record_cache = (FStar_Util.mk_ref (([])::[]))
in (let push = (fun _66_381 -> (match (()) with
| () -> begin
(let _169_263 = (let _169_262 = (let _169_260 = (FStar_ST.read record_cache)
in (FStar_List.hd _169_260))
in (let _169_261 = (FStar_ST.read record_cache)
in (_169_262)::_169_261))
in (FStar_ST.op_Colon_Equals record_cache _169_263))
end))
in (let pop = (fun _66_383 -> (match (()) with
| () -> begin
(let _169_267 = (let _169_266 = (FStar_ST.read record_cache)
in (FStar_List.tl _169_266))
in (FStar_ST.op_Colon_Equals record_cache _169_267))
end))
in (let peek = (fun _66_385 -> (match (()) with
| () -> begin
(let _169_270 = (FStar_ST.read record_cache)
in (FStar_List.hd _169_270))
end))
in (let insert = (fun r -> (let _169_277 = (let _169_276 = (let _169_273 = (peek ())
in (r)::_169_273)
in (let _169_275 = (let _169_274 = (FStar_ST.read record_cache)
in (FStar_List.tl _169_274))
in (_169_276)::_169_275))
in (FStar_ST.op_Colon_Equals record_cache _169_277)))
in (push, pop, peek, insert))))))

let push_record_cache : Prims.unit  ->  Prims.unit = (let _66_395 = record_cache_aux
in (match (_66_395) with
| (push, _66_390, _66_392, _66_394) -> begin
push
end))

let pop_record_cache : Prims.unit  ->  Prims.unit = (let _66_403 = record_cache_aux
in (match (_66_403) with
| (_66_397, pop, _66_400, _66_402) -> begin
pop
end))

let peek_record_cache : Prims.unit  ->  record_or_dc Prims.list = (let _66_411 = record_cache_aux
in (match (_66_411) with
| (_66_405, _66_407, peek, _66_410) -> begin
peek
end))

let insert_record_cache : record_or_dc  ->  Prims.unit = (let _66_419 = record_cache_aux
in (match (_66_419) with
| (_66_413, _66_415, _66_417, insert) -> begin
insert
end))

let extract_record : env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun e _66_9 -> (match (_66_9) with
| FStar_Syntax_Syntax.Sig_bundle (sigs, _66_424, _66_426, _66_428) -> begin
(let is_rec = (FStar_Util.for_some (fun _66_6 -> (match (_66_6) with
| (FStar_Syntax_Syntax.RecordType (_)) | (FStar_Syntax_Syntax.RecordConstructor (_)) -> begin
true
end
| _66_439 -> begin
false
end)))
in (let find_dc = (fun dc -> (FStar_All.pipe_right sigs (FStar_Util.find_opt (fun _66_7 -> (match (_66_7) with
| FStar_Syntax_Syntax.Sig_datacon (lid, _66_446, _66_448, _66_450, _66_452, _66_454, _66_456, _66_458) -> begin
(FStar_Ident.lid_equals dc lid)
end
| _66_462 -> begin
false
end)))))
in (FStar_All.pipe_right sigs (FStar_List.iter (fun _66_8 -> (match (_66_8) with
| FStar_Syntax_Syntax.Sig_inductive_typ (typename, univs, parms, _66_468, _66_470, dc::[], tags, _66_475) -> begin
(match ((let _169_348 = (find_dc dc)
in (FStar_All.pipe_left FStar_Util.must _169_348))) with
| FStar_Syntax_Syntax.Sig_datacon (constrname, _66_480, t, _66_483, _66_485, _66_487, _66_489, _66_491) -> begin
(let _66_497 = (FStar_Syntax_Util.arrow_formals t)
in (match (_66_497) with
| (formals, _66_496) -> begin
(let is_rec = (is_rec tags)
in (let fields = (FStar_All.pipe_right formals (FStar_List.collect (fun _66_501 -> (match (_66_501) with
| (x, q) -> begin
if ((FStar_Syntax_Syntax.is_null_bv x) || (is_rec && (q = Some (FStar_Syntax_Syntax.Implicit)))) then begin
[]
end else begin
(let _169_352 = (let _169_351 = (let _169_350 = if is_rec then begin
(FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname)
end else begin
x.FStar_Syntax_Syntax.ppname
end
in (qual constrname _169_350))
in (_169_351, x.FStar_Syntax_Syntax.sort))
in (_169_352)::[])
end
end))))
in (let record = {typename = typename; constrname = constrname; parms = parms; fields = fields; is_record = is_rec}
in (insert_record_cache record))))
end))
end
| _66_505 -> begin
()
end)
end
| _66_507 -> begin
()
end))))))
end
| _66_509 -> begin
()
end))

let try_lookup_record_or_dc_by_field_name : env  ->  FStar_Ident.lident  ->  (record_or_dc * FStar_Ident.lident) Prims.option = (fun env fieldname -> (let maybe_add_constrname = (fun ns c -> (let rec aux = (fun ns -> (match (ns) with
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
(let _169_363 = (aux tl)
in (hd)::_169_363)
end))
in (aux ns)))
in (let find_in_cache = (fun fieldname -> (let _66_527 = (fieldname.FStar_Ident.ns, fieldname.FStar_Ident.ident)
in (match (_66_527) with
| (ns, fieldname) -> begin
(let _169_368 = (peek_record_cache ())
in (FStar_Util.find_map _169_368 (fun record -> (let constrname = record.constrname.FStar_Ident.ident
in (let ns = (maybe_add_constrname ns constrname)
in (let fname = (FStar_Ident.lid_of_ids (FStar_List.append ns ((fieldname)::[])))
in (FStar_Util.find_map record.fields (fun _66_535 -> (match (_66_535) with
| (f, _66_534) -> begin
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
| _66_543 -> begin
None
end))

let try_lookup_projector_by_field_name : env  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * Prims.bool) Prims.option = (fun env fieldname -> (match ((try_lookup_record_or_dc_by_field_name env fieldname)) with
| Some (r, f) -> begin
Some ((f, r.is_record))
end
| _66_551 -> begin
None
end))

let qualify_field_to_record : env  ->  record_or_dc  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env recd f -> (let qualify = (fun fieldname -> (let _66_559 = (fieldname.FStar_Ident.ns, fieldname.FStar_Ident.ident)
in (match (_66_559) with
| (ns, fieldname) -> begin
(let constrname = recd.constrname.FStar_Ident.ident
in (let fname = (FStar_Ident.lid_of_ids (FStar_List.append (FStar_List.append ns ((constrname)::[])) ((fieldname)::[])))
in (FStar_Util.find_map recd.fields (fun _66_565 -> (match (_66_565) with
| (f, _66_564) -> begin
if (FStar_Ident.lid_equals fname f) then begin
Some (fname)
end else begin
None
end
end)))))
end)))
in (resolve_in_open_namespaces env f qualify)))

let unique : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  Prims.bool = (fun any_val exclude_if env lid -> (let this_env = (let _66_570 = env
in {curmodule = _66_570.curmodule; modules = _66_570.modules; open_namespaces = []; sigaccum = _66_570.sigaccum; localbindings = _66_570.localbindings; recbindings = _66_570.recbindings; sigmap = _66_570.sigmap; default_result_effect = _66_570.default_result_effect; iface = _66_570.iface; admitted_iface = _66_570.admitted_iface; expect_typ = _66_570.expect_typ})
in (match ((try_lookup_lid' any_val exclude_if env lid)) with
| None -> begin
true
end
| Some (_66_575) -> begin
false
end)))

let push_bv : env  ->  FStar_Ident.ident  ->  (env * FStar_Syntax_Syntax.bv) = (fun env x -> (let bv = (FStar_Syntax_Syntax.gen_bv x.FStar_Ident.idText (Some (x.FStar_Ident.idRange)) FStar_Syntax_Syntax.tun)
in ((let _66_580 = env
in {curmodule = _66_580.curmodule; modules = _66_580.modules; open_namespaces = _66_580.open_namespaces; sigaccum = _66_580.sigaccum; localbindings = ((x, bv))::env.localbindings; recbindings = _66_580.recbindings; sigmap = _66_580.sigmap; default_result_effect = _66_580.default_result_effect; iface = _66_580.iface; admitted_iface = _66_580.admitted_iface; expect_typ = _66_580.expect_typ}), bv)))

let push_top_level_rec_binding : env  ->  FStar_Ident.ident  ->  env = (fun env x -> (let l = (qualify env x)
in if (unique false true env l) then begin
(let _66_585 = env
in {curmodule = _66_585.curmodule; modules = _66_585.modules; open_namespaces = _66_585.open_namespaces; sigaccum = _66_585.sigaccum; localbindings = _66_585.localbindings; recbindings = ((x, l))::env.recbindings; sigmap = _66_585.sigmap; default_result_effect = _66_585.default_result_effect; iface = _66_585.iface; admitted_iface = _66_585.admitted_iface; expect_typ = _66_585.expect_typ})
end else begin
(Prims.raise (FStar_Syntax_Syntax.Error (((Prims.strcat "Duplicate top-level names " l.FStar_Ident.str), (FStar_Ident.range_of_lid l)))))
end))

let push_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env s -> (let err = (fun l -> (let sopt = (let _169_408 = (sigmap env)
in (FStar_Util.smap_try_find _169_408 l.FStar_Ident.str))
in (let r = (match (sopt) with
| Some (se, _66_594) -> begin
(match ((let _169_409 = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_Util.find_opt (FStar_Ident.lid_equals l) _169_409))) with
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
in (let _169_412 = (let _169_411 = (let _169_410 = (FStar_Util.format2 "Duplicate top-level names [%s]; previously declared at %s" (FStar_Ident.text_of_lid l) r)
in (_169_410, (FStar_Ident.range_of_lid l)))
in FStar_Syntax_Syntax.Error (_169_411))
in (Prims.raise _169_412)))))
in (let env = (let _66_612 = (match (s) with
| FStar_Syntax_Syntax.Sig_let (_66_603) -> begin
(false, true)
end
| FStar_Syntax_Syntax.Sig_bundle (_66_606) -> begin
(true, true)
end
| _66_609 -> begin
(false, false)
end)
in (match (_66_612) with
| (any_val, exclude_if) -> begin
(let lids = (FStar_Syntax_Util.lids_of_sigelt s)
in (match ((FStar_Util.find_map lids (fun l -> if (not ((unique any_val exclude_if env l))) then begin
Some (l)
end else begin
None
end))) with
| None -> begin
(let _66_616 = (extract_record env s)
in (let _66_618 = env
in {curmodule = _66_618.curmodule; modules = _66_618.modules; open_namespaces = _66_618.open_namespaces; sigaccum = (s)::env.sigaccum; localbindings = _66_618.localbindings; recbindings = _66_618.recbindings; sigmap = _66_618.sigmap; default_result_effect = _66_618.default_result_effect; iface = _66_618.iface; admitted_iface = _66_618.admitted_iface; expect_typ = _66_618.expect_typ}))
end
| Some (l) -> begin
(err l)
end))
end))
in (let _66_637 = (match (s) with
| FStar_Syntax_Syntax.Sig_bundle (ses, _66_625, _66_627, _66_629) -> begin
(let _169_416 = (FStar_List.map (fun se -> (let _169_415 = (FStar_Syntax_Util.lids_of_sigelt se)
in (_169_415, se))) ses)
in (env, _169_416))
end
| _66_634 -> begin
(let _169_419 = (let _169_418 = (let _169_417 = (FStar_Syntax_Util.lids_of_sigelt s)
in (_169_417, s))
in (_169_418)::[])
in (env, _169_419))
end)
in (match (_66_637) with
| (env, lss) -> begin
(let _66_642 = (FStar_All.pipe_right lss (FStar_List.iter (fun _66_640 -> (match (_66_640) with
| (lids, se) -> begin
(FStar_All.pipe_right lids (FStar_List.iter (fun lid -> (let _169_422 = (sigmap env)
in (FStar_Util.smap_add _169_422 lid.FStar_Ident.str (se, (env.iface && (not (env.admitted_iface)))))))))
end))))
in env)
end)))))

let push_namespace : env  ->  FStar_Ident.lident  ->  env = (fun env lid -> (let _66_646 = env
in {curmodule = _66_646.curmodule; modules = _66_646.modules; open_namespaces = (lid)::env.open_namespaces; sigaccum = _66_646.sigaccum; localbindings = _66_646.localbindings; recbindings = _66_646.recbindings; sigmap = _66_646.sigmap; default_result_effect = _66_646.default_result_effect; iface = _66_646.iface; admitted_iface = _66_646.admitted_iface; expect_typ = _66_646.expect_typ}))

let check_admits : FStar_Ident.lident  ->  env  ->  Prims.unit = (fun nm env -> (let warn = (not ((let _169_432 = (FStar_ST.read FStar_Options.admit_fsi)
in (FStar_All.pipe_right _169_432 (FStar_Util.for_some (fun l -> (nm.FStar_Ident.str = l)))))))
in (FStar_All.pipe_right env.sigaccum (FStar_List.iter (fun se -> (match (se) with
| FStar_Syntax_Syntax.Sig_declare_typ (l, u, t, quals, r) -> begin
(match ((try_lookup_lid env l)) with
| None -> begin
(let _66_661 = if warn then begin
(let _169_436 = (let _169_435 = (FStar_Range.string_of_range (FStar_Ident.range_of_lid l))
in (let _169_434 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format2 "%s: Warning: Admitting %s without a definition\n" _169_435 _169_434)))
in (FStar_Util.print_string _169_436))
end else begin
()
end
in (let _169_437 = (sigmap env)
in (FStar_Util.smap_add _169_437 l.FStar_Ident.str (FStar_Syntax_Syntax.Sig_declare_typ ((l, u, t, (FStar_Syntax_Syntax.Assumption)::quals, r)), false))))
end
| Some (_66_664) -> begin
()
end)
end
| _66_667 -> begin
()
end))))))

let finish : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env modul -> (let _66_711 = (FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations (FStar_List.iter (fun _66_11 -> (match (_66_11) with
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _66_674, _66_676) -> begin
if (FStar_List.contains FStar_Syntax_Syntax.Private quals) then begin
(FStar_All.pipe_right ses (FStar_List.iter (fun _66_10 -> (match (_66_10) with
| FStar_Syntax_Syntax.Sig_datacon (lid, _66_682, _66_684, _66_686, _66_688, _66_690, _66_692, _66_694) -> begin
(let _169_444 = (sigmap env)
in (FStar_Util.smap_remove _169_444 lid.FStar_Ident.str))
end
| _66_698 -> begin
()
end))))
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _66_701, _66_703, quals, _66_706) -> begin
if (FStar_List.contains FStar_Syntax_Syntax.Private quals) then begin
(let _169_445 = (sigmap env)
in (FStar_Util.smap_remove _169_445 lid.FStar_Ident.str))
end else begin
()
end
end
| _66_710 -> begin
()
end))))
in (let _66_713 = env
in {curmodule = None; modules = ((modul.FStar_Syntax_Syntax.name, modul))::env.modules; open_namespaces = []; sigaccum = []; localbindings = []; recbindings = []; sigmap = _66_713.sigmap; default_result_effect = _66_713.default_result_effect; iface = _66_713.iface; admitted_iface = _66_713.admitted_iface; expect_typ = _66_713.expect_typ})))

let push : env  ->  env = (fun env -> (let _66_716 = (push_record_cache ())
in (let _66_718 = env
in (let _169_450 = (let _169_449 = (let _169_448 = (sigmap env)
in (FStar_Util.smap_copy _169_448))
in (_169_449)::env.sigmap)
in {curmodule = _66_718.curmodule; modules = _66_718.modules; open_namespaces = _66_718.open_namespaces; sigaccum = _66_718.sigaccum; localbindings = _66_718.localbindings; recbindings = _66_718.recbindings; sigmap = _169_450; default_result_effect = _66_718.default_result_effect; iface = _66_718.iface; admitted_iface = _66_718.admitted_iface; expect_typ = _66_718.expect_typ}))))

let mark : env  ->  env = (fun env -> (push env))

let reset_mark : env  ->  env = (fun env -> (let _66_722 = env
in (let _169_455 = (FStar_List.tl env.sigmap)
in {curmodule = _66_722.curmodule; modules = _66_722.modules; open_namespaces = _66_722.open_namespaces; sigaccum = _66_722.sigaccum; localbindings = _66_722.localbindings; recbindings = _66_722.recbindings; sigmap = _169_455; default_result_effect = _66_722.default_result_effect; iface = _66_722.iface; admitted_iface = _66_722.admitted_iface; expect_typ = _66_722.expect_typ})))

let commit_mark : env  ->  env = (fun env -> (match (env.sigmap) with
| hd::_66_727::tl -> begin
(let _66_731 = env
in {curmodule = _66_731.curmodule; modules = _66_731.modules; open_namespaces = _66_731.open_namespaces; sigaccum = _66_731.sigaccum; localbindings = _66_731.localbindings; recbindings = _66_731.recbindings; sigmap = (hd)::tl; default_result_effect = _66_731.default_result_effect; iface = _66_731.iface; admitted_iface = _66_731.admitted_iface; expect_typ = _66_731.expect_typ})
end
| _66_734 -> begin
(FStar_All.failwith "Impossible")
end))

let pop : env  ->  env = (fun env -> (match (env.sigmap) with
| _66_738::maps -> begin
(let _66_740 = (pop_record_cache ())
in (let _66_742 = env
in {curmodule = _66_742.curmodule; modules = _66_742.modules; open_namespaces = _66_742.open_namespaces; sigaccum = _66_742.sigaccum; localbindings = _66_742.localbindings; recbindings = _66_742.recbindings; sigmap = maps; default_result_effect = _66_742.default_result_effect; iface = _66_742.iface; admitted_iface = _66_742.admitted_iface; expect_typ = _66_742.expect_typ}))
end
| _66_745 -> begin
(FStar_All.failwith "No more modules to pop")
end))

let export_interface : FStar_Ident.lident  ->  env  ->  env = (fun m env -> (let sigelt_in_m = (fun se -> (match ((FStar_Syntax_Util.lids_of_sigelt se)) with
| l::_66_751 -> begin
(l.FStar_Ident.nsstr = m.FStar_Ident.str)
end
| _66_755 -> begin
false
end))
in (let sm = (sigmap env)
in (let env = (pop env)
in (let keys = (FStar_Util.smap_keys sm)
in (let sm' = (sigmap env)
in (let _66_779 = (FStar_All.pipe_right keys (FStar_List.iter (fun k -> (match ((FStar_Util.smap_try_find sm' k)) with
| Some (se, true) when (sigelt_in_m se) -> begin
(let _66_765 = (FStar_Util.smap_remove sm' k)
in (let se = (match (se) with
| FStar_Syntax_Syntax.Sig_declare_typ (l, u, t, q, r) -> begin
FStar_Syntax_Syntax.Sig_declare_typ ((l, u, t, (FStar_Syntax_Syntax.Assumption)::q, r))
end
| _66_775 -> begin
se
end)
in (FStar_Util.smap_add sm' k (se, false))))
end
| _66_778 -> begin
()
end))))
in env)))))))

let finish_module_or_interface : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env modul -> (let _66_783 = if (not (modul.FStar_Syntax_Syntax.is_interface)) then begin
(check_admits modul.FStar_Syntax_Syntax.name env)
end else begin
()
end
in (finish env modul)))

let prepare_module_or_interface : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  (env * Prims.bool) = (fun intf admitted env mname -> (let prep = (fun env -> (let open_ns = if (FStar_Ident.lid_equals mname FStar_Syntax_Const.prims_lid) then begin
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
in (let _66_792 = env
in {curmodule = Some (mname); modules = _66_792.modules; open_namespaces = open_ns; sigaccum = _66_792.sigaccum; localbindings = _66_792.localbindings; recbindings = _66_792.recbindings; sigmap = env.sigmap; default_result_effect = _66_792.default_result_effect; iface = intf; admitted_iface = admitted; expect_typ = _66_792.expect_typ})))
in (match ((FStar_All.pipe_right env.modules (FStar_Util.find_opt (fun _66_797 -> (match (_66_797) with
| (l, _66_796) -> begin
(FStar_Ident.lid_equals l mname)
end))))) with
| None -> begin
((prep env), false)
end
| Some (_66_800, m) -> begin
(let _66_804 = if ((not (m.FStar_Syntax_Syntax.is_interface)) || intf) then begin
(let _169_484 = (let _169_483 = (let _169_482 = (FStar_Util.format1 "Duplicate module or interface name: %s" mname.FStar_Ident.str)
in (_169_482, (FStar_Ident.range_of_lid mname)))
in FStar_Syntax_Syntax.Error (_169_483))
in (Prims.raise _169_484))
end else begin
()
end
in (let _169_486 = (let _169_485 = (push env)
in (prep _169_485))
in (_169_486, true)))
end)))

let enter_monad_scope : env  ->  FStar_Ident.ident  ->  env = (fun env mname -> (let curmod = (current_module env)
in (let mscope = (FStar_Ident.lid_of_ids (FStar_List.append curmod.FStar_Ident.ns ((curmod.FStar_Ident.ident)::(mname)::[])))
in (let _66_810 = env
in {curmodule = Some (mscope); modules = _66_810.modules; open_namespaces = (curmod)::env.open_namespaces; sigaccum = _66_810.sigaccum; localbindings = _66_810.localbindings; recbindings = _66_810.recbindings; sigmap = _66_810.sigmap; default_result_effect = _66_810.default_result_effect; iface = _66_810.iface; admitted_iface = _66_810.admitted_iface; expect_typ = _66_810.expect_typ}))))

let exit_monad_scope : env  ->  env  ->  env = (fun env0 env -> (let _66_814 = env
in {curmodule = env0.curmodule; modules = _66_814.modules; open_namespaces = env0.open_namespaces; sigaccum = _66_814.sigaccum; localbindings = _66_814.localbindings; recbindings = _66_814.recbindings; sigmap = _66_814.sigmap; default_result_effect = _66_814.default_result_effect; iface = _66_814.iface; admitted_iface = _66_814.admitted_iface; expect_typ = _66_814.expect_typ}))

let fail_or = (fun lookup lid -> (match ((lookup lid)) with
| None -> begin
(let _169_502 = (let _169_501 = (let _169_500 = (FStar_Util.format1 "Identifier not found: [%s]" (FStar_Ident.text_of_lid lid))
in (_169_500, (FStar_Ident.range_of_lid lid)))
in FStar_Syntax_Syntax.Error (_169_501))
in (Prims.raise _169_502))
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




