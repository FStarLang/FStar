
open Prims

type env =
{curmodule : FStar_Ident.lident Prims.option; modules : (FStar_Ident.lident * FStar_Syntax_Syntax.modul) Prims.list; open_namespaces : FStar_Ident.lident Prims.list; modul_abbrevs : (FStar_Ident.ident * FStar_Ident.lident) Prims.list; sigaccum : FStar_Syntax_Syntax.sigelts; localbindings : (FStar_Ident.ident * FStar_Syntax_Syntax.bv) Prims.list; recbindings : (FStar_Ident.ident * FStar_Ident.lid * FStar_Syntax_Syntax.delta_depth) Prims.list; sigmap : (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap; default_result_effect : FStar_Ident.lident; iface : Prims.bool; admitted_iface : Prims.bool; expect_typ : Prims.bool}


let is_Mkenv : env  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv"))))


type foundname =
| Term_name of FStar_Syntax_Syntax.typ
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


let qual : FStar_Ident.lident  ->  FStar_Ident.ident  ->  FStar_Ident.lident = (fun lid id -> (let _150_90 = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns ((lid.FStar_Ident.ident)::(id)::[])))
in (FStar_Ident.set_lid_range _150_90 id.FStar_Ident.idRange)))


let qualify : env  ->  FStar_Ident.ident  ->  FStar_Ident.lident = (fun env id -> (let _150_95 = (current_module env)
in (qual _150_95 id)))


let qualify_lid : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (

let cur = (current_module env)
in (let _150_100 = (FStar_Ident.lid_of_ids (FStar_List.append (FStar_List.append (FStar_List.append cur.FStar_Ident.ns ((cur.FStar_Ident.ident)::[])) lid.FStar_Ident.ns) ((lid.FStar_Ident.ident)::[])))
in (FStar_Ident.set_lid_range _150_100 (FStar_Ident.range_of_lid lid)))))


let new_sigmap = (fun _61_52 -> (match (()) with
| () -> begin
(FStar_Util.smap_create 100)
end))


let empty_env : Prims.unit  ->  env = (fun _61_53 -> (match (()) with
| () -> begin
(let _150_104 = (new_sigmap ())
in {curmodule = None; modules = []; open_namespaces = []; modul_abbrevs = []; sigaccum = []; localbindings = []; recbindings = []; sigmap = _150_104; default_result_effect = FStar_Syntax_Const.effect_ML_lid; iface = false; admitted_iface = false; expect_typ = false})
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
(let _150_123 = (let _150_122 = (FStar_Ident.lid_of_path (("Prims")::(y)::[]) id.FStar_Ident.idRange)
in (FStar_Syntax_Syntax.fvar _150_122 dd dq))
in Some (_150_123))
end else begin
None
end
end))))


let try_lookup_id : env  ->  FStar_Ident.ident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env id -> (match ((unmangleOpName id)) with
| Some (f) -> begin
Some (f)
end
| _61_81 -> begin
(FStar_Util.find_map env.localbindings (fun _61_1 -> (match (_61_1) with
| (id', x) when (id'.FStar_Ident.idText = id.FStar_Ident.idText) -> begin
(let _150_129 = (bv_to_name x id.FStar_Ident.idRange)
in Some (_150_129))
end
| _61_87 -> begin
None
end)))
end))


let resolve_in_open_namespaces' = (fun env lid finder -> (

let aux = (fun namespaces -> (match ((finder lid)) with
| Some (r) -> begin
Some (r)
end
| _61_97 -> begin
(

let ids = (FStar_Ident.ids_of_lid lid)
in (FStar_Util.find_map namespaces (fun ns -> (

let full_name = (FStar_Ident.lid_of_ids (FStar_List.append (FStar_Ident.ids_of_lid ns) ids))
in (finder full_name)))))
end))
in (let _150_140 = (let _150_139 = (current_module env)
in (_150_139)::env.open_namespaces)
in (aux _150_140))))


let expand_module_abbrevs : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (match (lid.FStar_Ident.ns) with
| (id)::rest -> begin
(match ((FStar_All.pipe_right env.modul_abbrevs (FStar_List.tryFind (fun _61_109 -> (match (_61_109) with
| (id', _61_108) -> begin
(id.FStar_Ident.idText = id'.FStar_Ident.idText)
end))))) with
| None -> begin
lid
end
| Some (_61_112, lid') -> begin
(FStar_Ident.lid_of_ids (FStar_List.append (FStar_List.append (FStar_Ident.ids_of_lid lid') rest) ((lid.FStar_Ident.ident)::[])))
end)
end
| _61_117 -> begin
lid
end))


let resolve_in_open_namespaces = (fun env lid finder -> (let _150_152 = (expand_module_abbrevs env lid)
in (resolve_in_open_namespaces' env _150_152 finder)))


let fv_qual_of_se : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.fv_qual Prims.option = (fun _61_3 -> (match (_61_3) with
| FStar_Syntax_Syntax.Sig_datacon (_61_124, _61_126, _61_128, l, _61_131, quals, _61_134, _61_136) -> begin
(

let qopt = (FStar_Util.find_map quals (fun _61_2 -> (match (_61_2) with
| FStar_Syntax_Syntax.RecordConstructor (fs) -> begin
Some (FStar_Syntax_Syntax.Record_ctor ((l, fs)))
end
| _61_143 -> begin
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
| FStar_Syntax_Syntax.Sig_declare_typ (_61_148, _61_150, _61_152, quals, _61_155) -> begin
None
end
| _61_159 -> begin
None
end))


let lb_fv : FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.fv = (fun lbs lid -> (let _150_161 = (FStar_Util.find_map lbs (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in if (FStar_Syntax_Syntax.fv_eq_lid fv lid) then begin
Some (fv)
end else begin
None
end)))
in (FStar_All.pipe_right _150_161 FStar_Util.must)))


let try_lookup_name : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  foundname Prims.option = (fun any_val exclude_interf env lid -> (

let find_in_sig = (fun lid -> (match ((FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str)) with
| Some (_61_171, true) when exclude_interf -> begin
None
end
| None -> begin
None
end
| Some (se, _61_178) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_61_182) -> begin
(let _150_173 = (let _150_172 = (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.Delta_constant None)
in Term_name (_150_172))
in Some (_150_173))
end
| FStar_Syntax_Syntax.Sig_datacon (_61_185) -> begin
(let _150_176 = (let _150_175 = (let _150_174 = (fv_qual_of_se se)
in (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.Delta_constant _150_174))
in Term_name (_150_175))
in Some (_150_176))
end
| FStar_Syntax_Syntax.Sig_let ((_61_188, lbs), _61_192, _61_194, _61_196) -> begin
(

let fv = (lb_fv lbs lid)
in (let _150_178 = (let _150_177 = (FStar_Syntax_Syntax.fvar lid fv.FStar_Syntax_Syntax.fv_delta fv.FStar_Syntax_Syntax.fv_qual)
in Term_name (_150_177))
in Some (_150_178)))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _61_202, _61_204, quals, _61_207) -> begin
if (any_val || (FStar_All.pipe_right quals (FStar_Util.for_some (fun _61_4 -> (match (_61_4) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| _61_213 -> begin
false
end))))) then begin
(

let dd = if ((FStar_Syntax_Util.is_primop_lid lid) || ((FStar_Util.starts_with lid.FStar_Ident.nsstr "Prims.") && (FStar_All.pipe_right quals (FStar_Util.for_some (fun _61_5 -> (match (_61_5) with
| (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) -> begin
true
end
| _61_222 -> begin
false
end)))))) then begin
FStar_Syntax_Syntax.Delta_equational
end else begin
FStar_Syntax_Syntax.Delta_constant
end
in (let _150_183 = (let _150_182 = (let _150_181 = (fv_qual_of_se se)
in (FStar_Syntax_Syntax.fvar lid dd _150_181))
in Term_name (_150_182))
in Some (_150_183)))
end else begin
None
end
end
| FStar_Syntax_Syntax.Sig_new_effect (ne, _61_226) -> begin
(let _150_186 = (let _150_185 = (let _150_184 = (FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname (FStar_Ident.range_of_lid lid))
in (se, _150_184))
in Eff_name (_150_185))
in Some (_150_186))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (_61_230) -> begin
Some (Eff_name ((se, lid)))
end
| _61_233 -> begin
None
end)
end))
in (

let found_id = (match (lid.FStar_Ident.ns) with
| [] -> begin
(match ((try_lookup_id env lid.FStar_Ident.ident)) with
| Some (e) -> begin
Some (Term_name (e))
end
| None -> begin
(

let recname = (qualify env lid.FStar_Ident.ident)
in (FStar_Util.find_map env.recbindings (fun _61_242 -> (match (_61_242) with
| (id, l, dd) -> begin
if (id.FStar_Ident.idText = lid.FStar_Ident.ident.FStar_Ident.idText) then begin
(let _150_190 = (let _150_189 = (let _150_188 = (FStar_Ident.set_lid_range l (FStar_Ident.range_of_lid lid))
in (FStar_Syntax_Syntax.fvar _150_188 dd None))
in Term_name (_150_189))
in Some (_150_190))
end else begin
None
end
end))))
end)
end
| _61_244 -> begin
None
end)
in (match (found_id) with
| Some (_61_247) -> begin
found_id
end
| _61_250 -> begin
(resolve_in_open_namespaces env lid find_in_sig)
end))))


let try_lookup_effect_name' : Prims.bool  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident) Prims.option = (fun exclude_interf env lid -> (match ((try_lookup_name true exclude_interf env lid)) with
| Some (Eff_name (o, l)) -> begin
Some ((o, l))
end
| _61_260 -> begin
None
end))


let try_lookup_effect_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env l -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some (o, l) -> begin
Some (l)
end
| _61_268 -> begin
None
end))


let try_lookup_effect_defn : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl Prims.option = (fun env l -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some (FStar_Syntax_Syntax.Sig_new_effect (ne, _61_273), _61_277) -> begin
Some (ne)
end
| _61_281 -> begin
None
end))


let is_effect_name : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((try_lookup_effect_name env lid)) with
| None -> begin
false
end
| Some (_61_286) -> begin
true
end))


let lookup_letbinding_quals : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.qualifier Prims.list = (fun env lid -> (

let find_in_sig = (fun lid -> (match ((FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str)) with
| Some (FStar_Syntax_Syntax.Sig_declare_typ (lid, _61_294, _61_296, quals, _61_299), _61_303) -> begin
Some (quals)
end
| _61_307 -> begin
None
end))
in (match ((resolve_in_open_namespaces env lid find_in_sig)) with
| Some (quals) -> begin
quals
end
| _61_311 -> begin
[]
end)))


let try_lookup_module : env  ->  Prims.string Prims.list  ->  FStar_Syntax_Syntax.modul Prims.option = (fun env path -> (match ((FStar_List.tryFind (fun _61_316 -> (match (_61_316) with
| (mlid, modul) -> begin
((FStar_Ident.path_of_lid mlid) = path)
end)) env.modules)) with
| Some (_61_318, modul) -> begin
Some (modul)
end
| None -> begin
None
end))


let try_lookup_let : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env lid -> (

let find_in_sig = (fun lid -> (match ((FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str)) with
| Some (FStar_Syntax_Syntax.Sig_let ((_61_328, lbs), _61_332, _61_334, _61_336), _61_340) -> begin
(

let fv = (lb_fv lbs lid)
in (let _150_226 = (FStar_Syntax_Syntax.fvar lid fv.FStar_Syntax_Syntax.fv_delta fv.FStar_Syntax_Syntax.fv_qual)
in Some (_150_226)))
end
| _61_345 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))


let try_lookup_definition : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env lid -> (

let find_in_sig = (fun lid -> (match ((FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str)) with
| Some (FStar_Syntax_Syntax.Sig_let (lbs, _61_352, _61_354, _61_356), _61_360) -> begin
(FStar_Util.find_map (Prims.snd lbs) (fun lb -> (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv lid) -> begin
Some (lb.FStar_Syntax_Syntax.lbdef)
end
| _61_367 -> begin
None
end)))
end
| _61_369 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))


let try_lookup_lid' : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun any_val exclude_interf env lid -> (match ((try_lookup_name any_val exclude_interf env lid)) with
| Some (Term_name (e)) -> begin
Some (e)
end
| _61_378 -> begin
None
end))


let try_lookup_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env l -> (try_lookup_lid' env.iface false env l))


let try_lookup_datacon : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.fv Prims.option = (fun env lid -> (

let find_in_sig = (fun lid -> (match ((FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str)) with
| Some (FStar_Syntax_Syntax.Sig_declare_typ (_61_386, _61_388, _61_390, quals, _61_393), _61_397) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _61_6 -> (match (_61_6) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| _61_403 -> begin
false
end)))) then begin
(let _150_253 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant None)
in Some (_150_253))
end else begin
None
end
end
| Some (FStar_Syntax_Syntax.Sig_datacon (_61_405), _61_408) -> begin
(let _150_254 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in Some (_150_254))
end
| _61_412 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))


let find_all_datacons : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.list Prims.option = (fun env lid -> (

let find_in_sig = (fun lid -> (match ((FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str)) with
| Some (FStar_Syntax_Syntax.Sig_inductive_typ (_61_418, _61_420, _61_422, _61_424, _61_426, datas, _61_429, _61_431), _61_435) -> begin
Some (datas)
end
| _61_439 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))


let record_cache_aux : ((Prims.unit  ->  Prims.unit) * (Prims.unit  ->  Prims.unit) * (Prims.unit  ->  record_or_dc Prims.list) * (record_or_dc  ->  Prims.unit) * (Prims.unit  ->  Prims.unit)) = (

let record_cache = (FStar_Util.mk_ref (([])::[]))
in (

let push = (fun _61_442 -> (match (()) with
| () -> begin
(let _150_276 = (let _150_275 = (let _150_273 = (FStar_ST.read record_cache)
in (FStar_List.hd _150_273))
in (let _150_274 = (FStar_ST.read record_cache)
in (_150_275)::_150_274))
in (FStar_ST.op_Colon_Equals record_cache _150_276))
end))
in (

let pop = (fun _61_444 -> (match (()) with
| () -> begin
(let _150_280 = (let _150_279 = (FStar_ST.read record_cache)
in (FStar_List.tl _150_279))
in (FStar_ST.op_Colon_Equals record_cache _150_280))
end))
in (

let peek = (fun _61_446 -> (match (()) with
| () -> begin
(let _150_283 = (FStar_ST.read record_cache)
in (FStar_List.hd _150_283))
end))
in (

let insert = (fun r -> (let _150_290 = (let _150_289 = (let _150_286 = (peek ())
in (r)::_150_286)
in (let _150_288 = (let _150_287 = (FStar_ST.read record_cache)
in (FStar_List.tl _150_287))
in (_150_289)::_150_288))
in (FStar_ST.op_Colon_Equals record_cache _150_290)))
in (

let commit = (fun _61_450 -> (match (()) with
| () -> begin
(match ((FStar_ST.read record_cache)) with
| (hd)::(_61_453)::tl -> begin
(FStar_ST.op_Colon_Equals record_cache ((hd)::tl))
end
| _61_458 -> begin
(FStar_All.failwith "Impossible")
end)
end))
in (push, pop, peek, insert, commit)))))))


let push_record_cache : Prims.unit  ->  Prims.unit = (

let _61_468 = record_cache_aux
in (match (_61_468) with
| (push, _61_461, _61_463, _61_465, _61_467) -> begin
push
end))


let pop_record_cache : Prims.unit  ->  Prims.unit = (

let _61_478 = record_cache_aux
in (match (_61_478) with
| (_61_470, pop, _61_473, _61_475, _61_477) -> begin
pop
end))


let peek_record_cache : Prims.unit  ->  record_or_dc Prims.list = (

let _61_488 = record_cache_aux
in (match (_61_488) with
| (_61_480, _61_482, peek, _61_485, _61_487) -> begin
peek
end))


let insert_record_cache : record_or_dc  ->  Prims.unit = (

let _61_498 = record_cache_aux
in (match (_61_498) with
| (_61_490, _61_492, _61_494, insert, _61_497) -> begin
insert
end))


let commit_record_cache : Prims.unit  ->  Prims.unit = (

let _61_508 = record_cache_aux
in (match (_61_508) with
| (_61_500, _61_502, _61_504, _61_506, commit) -> begin
commit
end))


let extract_record : env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun e _61_10 -> (match (_61_10) with
| FStar_Syntax_Syntax.Sig_bundle (sigs, _61_513, _61_515, _61_517) -> begin
(

let is_rec = (FStar_Util.for_some (fun _61_7 -> (match (_61_7) with
| (FStar_Syntax_Syntax.RecordType (_)) | (FStar_Syntax_Syntax.RecordConstructor (_)) -> begin
true
end
| _61_528 -> begin
false
end)))
in (

let find_dc = (fun dc -> (FStar_All.pipe_right sigs (FStar_Util.find_opt (fun _61_8 -> (match (_61_8) with
| FStar_Syntax_Syntax.Sig_datacon (lid, _61_535, _61_537, _61_539, _61_541, _61_543, _61_545, _61_547) -> begin
(FStar_Ident.lid_equals dc lid)
end
| _61_551 -> begin
false
end)))))
in (FStar_All.pipe_right sigs (FStar_List.iter (fun _61_9 -> (match (_61_9) with
| FStar_Syntax_Syntax.Sig_inductive_typ (typename, univs, parms, _61_557, _61_559, (dc)::[], tags, _61_564) -> begin
(match ((let _150_393 = (find_dc dc)
in (FStar_All.pipe_left FStar_Util.must _150_393))) with
| FStar_Syntax_Syntax.Sig_datacon (constrname, _61_569, t, _61_572, _61_574, _61_576, _61_578, _61_580) -> begin
(

let _61_586 = (FStar_Syntax_Util.arrow_formals t)
in (match (_61_586) with
| (formals, _61_585) -> begin
(

let is_rec = (is_rec tags)
in (

let fields = (FStar_All.pipe_right formals (FStar_List.collect (fun _61_590 -> (match (_61_590) with
| (x, q) -> begin
if ((FStar_Syntax_Syntax.is_null_bv x) || (is_rec && (FStar_Syntax_Syntax.is_implicit q))) then begin
[]
end else begin
(let _150_397 = (let _150_396 = (let _150_395 = if is_rec then begin
(FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname)
end else begin
x.FStar_Syntax_Syntax.ppname
end
in (qual constrname _150_395))
in (_150_396, x.FStar_Syntax_Syntax.sort))
in (_150_397)::[])
end
end))))
in (

let record = {typename = typename; constrname = constrname; parms = parms; fields = fields; is_record = is_rec}
in (insert_record_cache record))))
end))
end
| _61_594 -> begin
()
end)
end
| _61_596 -> begin
()
end))))))
end
| _61_598 -> begin
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
(let _150_408 = (aux tl)
in (hd)::_150_408)
end))
in (aux ns)))
in (

let find_in_cache = (fun fieldname -> (

let _61_616 = (fieldname.FStar_Ident.ns, fieldname.FStar_Ident.ident)
in (match (_61_616) with
| (ns, fieldname) -> begin
(let _150_413 = (peek_record_cache ())
in (FStar_Util.find_map _150_413 (fun record -> (

let constrname = record.constrname.FStar_Ident.ident
in (

let ns = (maybe_add_constrname ns constrname)
in (

let fname = (FStar_Ident.lid_of_ids (FStar_List.append ns ((fieldname)::[])))
in (FStar_Util.find_map record.fields (fun _61_624 -> (match (_61_624) with
| (f, _61_623) -> begin
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
| _61_632 -> begin
None
end))


let try_lookup_projector_by_field_name : env  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * Prims.bool) Prims.option = (fun env fieldname -> (match ((try_lookup_record_or_dc_by_field_name env fieldname)) with
| Some (r, f) -> begin
Some ((f, r.is_record))
end
| _61_640 -> begin
None
end))


let qualify_field_to_record : env  ->  record_or_dc  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env recd f -> (

let qualify = (fun fieldname -> (

let _61_648 = (fieldname.FStar_Ident.ns, fieldname.FStar_Ident.ident)
in (match (_61_648) with
| (ns, fieldname) -> begin
(

let constrname = recd.constrname.FStar_Ident.ident
in (

let fname = (FStar_Ident.lid_of_ids (FStar_List.append (FStar_List.append ns ((constrname)::[])) ((fieldname)::[])))
in (FStar_Util.find_map recd.fields (fun _61_654 -> (match (_61_654) with
| (f, _61_653) -> begin
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

let _61_659 = env
in {curmodule = _61_659.curmodule; modules = _61_659.modules; open_namespaces = []; modul_abbrevs = _61_659.modul_abbrevs; sigaccum = _61_659.sigaccum; localbindings = _61_659.localbindings; recbindings = _61_659.recbindings; sigmap = _61_659.sigmap; default_result_effect = _61_659.default_result_effect; iface = _61_659.iface; admitted_iface = _61_659.admitted_iface; expect_typ = _61_659.expect_typ})
in (match ((try_lookup_lid' any_val exclude_if env lid)) with
| None -> begin
true
end
| Some (_61_664) -> begin
false
end)))


let push_bv : env  ->  FStar_Ident.ident  ->  (env * FStar_Syntax_Syntax.bv) = (fun env x -> (

let bv = (FStar_Syntax_Syntax.gen_bv x.FStar_Ident.idText (Some (x.FStar_Ident.idRange)) FStar_Syntax_Syntax.tun)
in ((

let _61_669 = env
in {curmodule = _61_669.curmodule; modules = _61_669.modules; open_namespaces = _61_669.open_namespaces; modul_abbrevs = _61_669.modul_abbrevs; sigaccum = _61_669.sigaccum; localbindings = ((x, bv))::env.localbindings; recbindings = _61_669.recbindings; sigmap = _61_669.sigmap; default_result_effect = _61_669.default_result_effect; iface = _61_669.iface; admitted_iface = _61_669.admitted_iface; expect_typ = _61_669.expect_typ}), bv)))


let push_top_level_rec_binding : env  ->  FStar_Ident.ident  ->  FStar_Syntax_Syntax.delta_depth  ->  env = (fun env x dd -> (

let l = (qualify env x)
in if (unique false true env l) then begin
(

let _61_675 = env
in {curmodule = _61_675.curmodule; modules = _61_675.modules; open_namespaces = _61_675.open_namespaces; modul_abbrevs = _61_675.modul_abbrevs; sigaccum = _61_675.sigaccum; localbindings = _61_675.localbindings; recbindings = ((x, l, dd))::env.recbindings; sigmap = _61_675.sigmap; default_result_effect = _61_675.default_result_effect; iface = _61_675.iface; admitted_iface = _61_675.admitted_iface; expect_typ = _61_675.expect_typ})
end else begin
(Prims.raise (FStar_Syntax_Syntax.Error (((Prims.strcat "Duplicate top-level names " l.FStar_Ident.str), (FStar_Ident.range_of_lid l)))))
end))


let push_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env s -> (

let err = (fun l -> (

let sopt = (FStar_Util.smap_try_find (sigmap env) l.FStar_Ident.str)
in (

let r = (match (sopt) with
| Some (se, _61_684) -> begin
(match ((let _150_455 = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_Util.find_opt (FStar_Ident.lid_equals l) _150_455))) with
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
in (let _150_458 = (let _150_457 = (let _150_456 = (FStar_Util.format2 "Duplicate top-level names [%s]; previously declared at %s" (FStar_Ident.text_of_lid l) r)
in (_150_456, (FStar_Ident.range_of_lid l)))
in FStar_Syntax_Syntax.Error (_150_457))
in (Prims.raise _150_458)))))
in (

let env = (

let _61_702 = (match (s) with
| FStar_Syntax_Syntax.Sig_let (_61_693) -> begin
(false, true)
end
| FStar_Syntax_Syntax.Sig_bundle (_61_696) -> begin
(true, true)
end
| _61_699 -> begin
(false, false)
end)
in (match (_61_702) with
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

let _61_706 = (extract_record env s)
in (

let _61_708 = env
in {curmodule = _61_708.curmodule; modules = _61_708.modules; open_namespaces = _61_708.open_namespaces; modul_abbrevs = _61_708.modul_abbrevs; sigaccum = (s)::env.sigaccum; localbindings = _61_708.localbindings; recbindings = _61_708.recbindings; sigmap = _61_708.sigmap; default_result_effect = _61_708.default_result_effect; iface = _61_708.iface; admitted_iface = _61_708.admitted_iface; expect_typ = _61_708.expect_typ}))
end
| Some (l) -> begin
(err l)
end))
end))
in (

let _61_727 = (match (s) with
| FStar_Syntax_Syntax.Sig_bundle (ses, _61_715, _61_717, _61_719) -> begin
(let _150_462 = (FStar_List.map (fun se -> (let _150_461 = (FStar_Syntax_Util.lids_of_sigelt se)
in (_150_461, se))) ses)
in (env, _150_462))
end
| _61_724 -> begin
(let _150_465 = (let _150_464 = (let _150_463 = (FStar_Syntax_Util.lids_of_sigelt s)
in (_150_463, s))
in (_150_464)::[])
in (env, _150_465))
end)
in (match (_61_727) with
| (env, lss) -> begin
(

let _61_732 = (FStar_All.pipe_right lss (FStar_List.iter (fun _61_730 -> (match (_61_730) with
| (lids, se) -> begin
(FStar_All.pipe_right lids (FStar_List.iter (fun lid -> (FStar_Util.smap_add (sigmap env) lid.FStar_Ident.str (se, (env.iface && (not (env.admitted_iface))))))))
end))))
in env)
end)))))


let push_namespace : env  ->  FStar_Ident.lident  ->  env = (fun env ns -> (

let modules = env.modules
in if (FStar_All.pipe_right modules (FStar_Util.for_some (fun _61_740 -> (match (_61_740) with
| (m, _61_739) -> begin
(FStar_Util.starts_with (FStar_Ident.text_of_lid m) (FStar_Ident.text_of_lid ns))
end)))) then begin
(

let _61_741 = env
in {curmodule = _61_741.curmodule; modules = _61_741.modules; open_namespaces = (ns)::env.open_namespaces; modul_abbrevs = _61_741.modul_abbrevs; sigaccum = _61_741.sigaccum; localbindings = _61_741.localbindings; recbindings = _61_741.recbindings; sigmap = _61_741.sigmap; default_result_effect = _61_741.default_result_effect; iface = _61_741.iface; admitted_iface = _61_741.admitted_iface; expect_typ = _61_741.expect_typ})
end else begin
(let _150_475 = (let _150_474 = (let _150_473 = (FStar_Util.format1 "Namespace %s cannot be found" (FStar_Ident.text_of_lid ns))
in (_150_473, (FStar_Ident.range_of_lid ns)))
in FStar_Syntax_Syntax.Error (_150_474))
in (Prims.raise _150_475))
end))


let push_module_abbrev : env  ->  FStar_Ident.ident  ->  FStar_Ident.lident  ->  env = (fun env x l -> if (FStar_All.pipe_right env.modul_abbrevs (FStar_Util.for_some (fun _61_749 -> (match (_61_749) with
| (y, _61_748) -> begin
(x.FStar_Ident.idText = y.FStar_Ident.idText)
end)))) then begin
(let _150_485 = (let _150_484 = (let _150_483 = (FStar_Util.format1 "Module %s is already defined" x.FStar_Ident.idText)
in (_150_483, x.FStar_Ident.idRange))
in FStar_Syntax_Syntax.Error (_150_484))
in (Prims.raise _150_485))
end else begin
(

let modules = env.modules
in if (FStar_All.pipe_right modules (FStar_Util.for_some (fun _61_754 -> (match (_61_754) with
| (m, _61_753) -> begin
(FStar_Ident.lid_equals m l)
end)))) then begin
(

let _61_755 = env
in {curmodule = _61_755.curmodule; modules = _61_755.modules; open_namespaces = _61_755.open_namespaces; modul_abbrevs = ((x, l))::env.modul_abbrevs; sigaccum = _61_755.sigaccum; localbindings = _61_755.localbindings; recbindings = _61_755.recbindings; sigmap = _61_755.sigmap; default_result_effect = _61_755.default_result_effect; iface = _61_755.iface; admitted_iface = _61_755.admitted_iface; expect_typ = _61_755.expect_typ})
end else begin
(let _150_489 = (let _150_488 = (let _150_487 = (FStar_Util.format1 "Module %s cannot be found" (FStar_Ident.text_of_lid l))
in (_150_487, (FStar_Ident.range_of_lid l)))
in FStar_Syntax_Syntax.Error (_150_488))
in (Prims.raise _150_489))
end)
end)


let check_admits : env  ->  Prims.unit = (fun env -> (FStar_All.pipe_right env.sigaccum (FStar_List.iter (fun se -> (match (se) with
| FStar_Syntax_Syntax.Sig_declare_typ (l, u, t, quals, r) -> begin
(match ((try_lookup_lid env l)) with
| None -> begin
(

let _61_767 = (let _150_495 = (let _150_494 = (FStar_Range.string_of_range (FStar_Ident.range_of_lid l))
in (let _150_493 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format2 "%s: Warning: Admitting %s without a definition\n" _150_494 _150_493)))
in (FStar_Util.print_string _150_495))
in (FStar_Util.smap_add (sigmap env) l.FStar_Ident.str (FStar_Syntax_Syntax.Sig_declare_typ ((l, u, t, (FStar_Syntax_Syntax.Assumption)::quals, r)), false)))
end
| Some (_61_770) -> begin
()
end)
end
| _61_773 -> begin
()
end)))))


let finish : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env modul -> (

let _61_833 = (FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations (FStar_List.iter (fun _61_12 -> (match (_61_12) with
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _61_780, _61_782) -> begin
if ((FStar_List.contains FStar_Syntax_Syntax.Private quals) || (FStar_List.contains FStar_Syntax_Syntax.Abstract quals)) then begin
(FStar_All.pipe_right ses (FStar_List.iter (fun _61_11 -> (match (_61_11) with
| FStar_Syntax_Syntax.Sig_datacon (lid, _61_788, _61_790, _61_792, _61_794, _61_796, _61_798, _61_800) -> begin
(FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str)
end
| _61_804 -> begin
()
end))))
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _61_807, _61_809, quals, _61_812) -> begin
if (FStar_List.contains FStar_Syntax_Syntax.Private quals) then begin
(FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str)
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_let ((_61_816, lbs), r, _61_821, quals) -> begin
(

let _61_826 = if ((FStar_List.contains FStar_Syntax_Syntax.Private quals) || (FStar_List.contains FStar_Syntax_Syntax.Abstract quals)) then begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (let _150_506 = (let _150_505 = (let _150_504 = (let _150_503 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _150_503.FStar_Syntax_Syntax.fv_name)
in _150_504.FStar_Syntax_Syntax.v)
in _150_505.FStar_Ident.str)
in (FStar_Util.smap_remove (sigmap env) _150_506)))))
end else begin
()
end
in if ((FStar_List.contains FStar_Syntax_Syntax.Abstract quals) && (not ((FStar_List.contains FStar_Syntax_Syntax.Private quals)))) then begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (

let lid = (let _150_509 = (let _150_508 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _150_508.FStar_Syntax_Syntax.fv_name)
in _150_509.FStar_Syntax_Syntax.v)
in (

let decl = FStar_Syntax_Syntax.Sig_declare_typ ((lid, lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp, (FStar_Syntax_Syntax.Assumption)::quals, r))
in (FStar_Util.smap_add (sigmap env) lid.FStar_Ident.str (decl, false)))))))
end else begin
()
end)
end
| _61_832 -> begin
()
end))))
in (

let _61_835 = env
in {curmodule = None; modules = ((modul.FStar_Syntax_Syntax.name, modul))::env.modules; open_namespaces = []; modul_abbrevs = []; sigaccum = []; localbindings = []; recbindings = []; sigmap = _61_835.sigmap; default_result_effect = _61_835.default_result_effect; iface = _61_835.iface; admitted_iface = _61_835.admitted_iface; expect_typ = _61_835.expect_typ})))


type env_stack_ops =
{push : env  ->  env; mark : env  ->  env; reset_mark : env  ->  env; commit_mark : env  ->  env; pop : env  ->  env}


let is_Mkenv_stack_ops : env_stack_ops  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv_stack_ops"))))


let stack_ops : env_stack_ops = (

let stack = (FStar_Util.mk_ref [])
in (

let push = (fun env -> (

let _61_846 = (push_record_cache ())
in (

let _61_848 = (let _150_559 = (let _150_558 = (FStar_ST.read stack)
in (env)::_150_558)
in (FStar_ST.op_Colon_Equals stack _150_559))
in (

let _61_850 = env
in (let _150_560 = (FStar_Util.smap_copy (sigmap env))
in {curmodule = _61_850.curmodule; modules = _61_850.modules; open_namespaces = _61_850.open_namespaces; modul_abbrevs = _61_850.modul_abbrevs; sigaccum = _61_850.sigaccum; localbindings = _61_850.localbindings; recbindings = _61_850.recbindings; sigmap = _150_560; default_result_effect = _61_850.default_result_effect; iface = _61_850.iface; admitted_iface = _61_850.admitted_iface; expect_typ = _61_850.expect_typ})))))
in (

let pop = (fun env -> (match ((FStar_ST.read stack)) with
| (env)::tl -> begin
(

let _61_857 = (pop_record_cache ())
in (

let _61_859 = (FStar_ST.op_Colon_Equals stack tl)
in env))
end
| _61_862 -> begin
(FStar_All.failwith "Impossible: Too many pops")
end))
in (

let commit_mark = (fun env -> (

let _61_865 = (commit_record_cache ())
in (match ((FStar_ST.read stack)) with
| (_61_869)::tl -> begin
(

let _61_871 = (FStar_ST.op_Colon_Equals stack tl)
in env)
end
| _61_874 -> begin
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
| (l)::_61_885 -> begin
(l.FStar_Ident.nsstr = m.FStar_Ident.str)
end
| _61_889 -> begin
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

let _61_913 = (FStar_All.pipe_right keys (FStar_List.iter (fun k -> (match ((FStar_Util.smap_try_find sm' k)) with
| Some (se, true) when (sigelt_in_m se) -> begin
(

let _61_899 = (FStar_Util.smap_remove sm' k)
in (

let se = (match (se) with
| FStar_Syntax_Syntax.Sig_declare_typ (l, u, t, q, r) -> begin
FStar_Syntax_Syntax.Sig_declare_typ ((l, u, t, (FStar_Syntax_Syntax.Assumption)::q, r))
end
| _61_909 -> begin
se
end)
in (FStar_Util.smap_add sm' k (se, false))))
end
| _61_912 -> begin
()
end))))
in env)))))))


let finish_module_or_interface : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env modul -> (

let _61_917 = if (not (modul.FStar_Syntax_Syntax.is_interface)) then begin
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

let open_ns = if ((FStar_List.length mname.FStar_Ident.ns) <> 0) then begin
(

let ns = (FStar_Ident.lid_of_ids mname.FStar_Ident.ns)
in (ns)::open_ns)
end else begin
open_ns
end
in (

let _61_928 = env
in {curmodule = Some (mname); modules = _61_928.modules; open_namespaces = open_ns; modul_abbrevs = _61_928.modul_abbrevs; sigaccum = _61_928.sigaccum; localbindings = _61_928.localbindings; recbindings = _61_928.recbindings; sigmap = env.sigmap; default_result_effect = _61_928.default_result_effect; iface = intf; admitted_iface = admitted; expect_typ = _61_928.expect_typ}))))
in (match ((FStar_All.pipe_right env.modules (FStar_Util.find_opt (fun _61_933 -> (match (_61_933) with
| (l, _61_932) -> begin
(FStar_Ident.lid_equals l mname)
end))))) with
| None -> begin
(let _150_597 = (prep env)
in (_150_597, false))
end
| Some (_61_936, m) -> begin
(

let _61_940 = if ((not (m.FStar_Syntax_Syntax.is_interface)) || intf) then begin
(let _150_600 = (let _150_599 = (let _150_598 = (FStar_Util.format1 "Duplicate module or interface name: %s" mname.FStar_Ident.str)
in (_150_598, (FStar_Ident.range_of_lid mname)))
in FStar_Syntax_Syntax.Error (_150_599))
in (Prims.raise _150_600))
end else begin
()
end
in (let _150_602 = (let _150_601 = (push env)
in (prep _150_601))
in (_150_602, true)))
end)))


let enter_monad_scope : env  ->  FStar_Ident.ident  ->  env = (fun env mname -> (

let curmod = (current_module env)
in (

let mscope = (FStar_Ident.lid_of_ids (FStar_List.append curmod.FStar_Ident.ns ((curmod.FStar_Ident.ident)::(mname)::[])))
in (

let _61_946 = env
in {curmodule = Some (mscope); modules = _61_946.modules; open_namespaces = (curmod)::env.open_namespaces; modul_abbrevs = _61_946.modul_abbrevs; sigaccum = _61_946.sigaccum; localbindings = _61_946.localbindings; recbindings = _61_946.recbindings; sigmap = _61_946.sigmap; default_result_effect = _61_946.default_result_effect; iface = _61_946.iface; admitted_iface = _61_946.admitted_iface; expect_typ = _61_946.expect_typ}))))


let exit_monad_scope : env  ->  env  ->  env = (fun env0 env -> (

let _61_950 = env
in {curmodule = env0.curmodule; modules = _61_950.modules; open_namespaces = env0.open_namespaces; modul_abbrevs = _61_950.modul_abbrevs; sigaccum = _61_950.sigaccum; localbindings = _61_950.localbindings; recbindings = _61_950.recbindings; sigmap = _61_950.sigmap; default_result_effect = _61_950.default_result_effect; iface = _61_950.iface; admitted_iface = _61_950.admitted_iface; expect_typ = _61_950.expect_typ}))


let fail_or = (fun env lookup lid -> (match ((lookup lid)) with
| None -> begin
(

let opened_modules = (FStar_List.map (fun _61_959 -> (match (_61_959) with
| (lid, _61_958) -> begin
(FStar_Ident.text_of_lid lid)
end)) env.modules)
in (

let module_of_the_lid = (let _150_618 = (FStar_Ident.path_of_ns lid.FStar_Ident.ns)
in (FStar_Ident.text_of_path _150_618))
in (

let msg = (FStar_Util.format1 "Identifier not found: [%s]" (FStar_Ident.text_of_lid lid))
in (

let msg = (match (env.curmodule) with
| Some (m) when (((FStar_Ident.text_of_lid m) = module_of_the_lid) || (module_of_the_lid = "")) -> begin
msg
end
| _61_966 when (FStar_List.existsb (fun m -> (m = module_of_the_lid)) opened_modules) -> begin
msg
end
| _61_969 -> begin
(let _150_622 = (let _150_621 = (let _150_620 = (FStar_Ident.path_of_ns lid.FStar_Ident.ns)
in (FStar_Ident.text_of_path _150_620))
in (FStar_Util.format3 "Hint: %s belongs to module %s, which does not belong to the list of modules in scope, namely %s" (FStar_Ident.text_of_lid lid) _150_621 (FStar_String.concat ", " opened_modules)))
in (Prims.strcat (Prims.strcat msg "\n") _150_622))
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




