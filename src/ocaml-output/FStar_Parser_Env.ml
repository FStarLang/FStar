
open Prims

type env =
{curmodule : FStar_Ident.lident Prims.option; modules : (FStar_Ident.lident * FStar_Syntax_Syntax.modul) Prims.list; open_namespaces : FStar_Ident.lident Prims.list; sigaccum : FStar_Syntax_Syntax.sigelts; localbindings : (FStar_Ident.ident * FStar_Syntax_Syntax.bv) Prims.list; recbindings : (FStar_Ident.ident * FStar_Ident.lid * FStar_Syntax_Syntax.delta_depth) Prims.list; sigmap : (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap Prims.list; default_result_effect : FStar_Ident.lident; iface : Prims.bool; admitted_iface : Prims.bool; expect_typ : Prims.bool}


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
| Term_name (_54_26) -> begin
_54_26
end))


let ___Eff_name____0 = (fun projectee -> (match (projectee) with
| Eff_name (_54_29) -> begin
_54_29
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


let qual : FStar_Ident.lident  ->  FStar_Ident.ident  ->  FStar_Ident.lident = (fun lid id -> (let _143_87 = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns ((lid.FStar_Ident.ident)::(id)::[])))
in (FStar_Ident.set_lid_range _143_87 id.FStar_Ident.idRange)))


let qualify : env  ->  FStar_Ident.ident  ->  FStar_Ident.lident = (fun env id -> (let _143_92 = (current_module env)
in (qual _143_92 id)))


let qualify_lid : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (

let cur = (current_module env)
in (let _143_97 = (FStar_Ident.lid_of_ids (FStar_List.append (FStar_List.append (FStar_List.append cur.FStar_Ident.ns ((cur.FStar_Ident.ident)::[])) lid.FStar_Ident.ns) ((lid.FStar_Ident.ident)::[])))
in (FStar_Ident.set_lid_range _143_97 (FStar_Ident.range_of_lid lid)))))


let new_sigmap = (fun _54_50 -> (match (()) with
| () -> begin
(FStar_Util.smap_create 100)
end))


let empty_env : Prims.unit  ->  env = (fun _54_51 -> (match (()) with
| () -> begin
(let _143_102 = (let _143_101 = (new_sigmap ())
in (_143_101)::[])
in {curmodule = None; modules = []; open_namespaces = []; sigaccum = []; localbindings = []; recbindings = []; sigmap = _143_102; default_result_effect = FStar_Syntax_Const.effect_ML_lid; iface = false; admitted_iface = false; expect_typ = false})
end))


let sigmap : env  ->  (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap = (fun env -> (FStar_List.hd env.sigmap))


let default_total : env  ->  env = (fun env -> (

let _54_54 = env
in {curmodule = _54_54.curmodule; modules = _54_54.modules; open_namespaces = _54_54.open_namespaces; sigaccum = _54_54.sigaccum; localbindings = _54_54.localbindings; recbindings = _54_54.recbindings; sigmap = _54_54.sigmap; default_result_effect = FStar_Syntax_Const.effect_Tot_lid; iface = _54_54.iface; admitted_iface = _54_54.admitted_iface; expect_typ = _54_54.expect_typ}))


let default_ml : env  ->  env = (fun env -> (

let _54_57 = env
in {curmodule = _54_57.curmodule; modules = _54_57.modules; open_namespaces = _54_57.open_namespaces; sigaccum = _54_57.sigaccum; localbindings = _54_57.localbindings; recbindings = _54_57.recbindings; sigmap = _54_57.sigmap; default_result_effect = FStar_Syntax_Const.effect_ML_lid; iface = _54_57.iface; admitted_iface = _54_57.admitted_iface; expect_typ = _54_57.expect_typ}))


let set_bv_range : FStar_Syntax_Syntax.bv  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.bv = (fun bv r -> (

let id = (

let _54_61 = bv.FStar_Syntax_Syntax.ppname
in {FStar_Ident.idText = _54_61.FStar_Ident.idText; FStar_Ident.idRange = r})
in (

let _54_64 = bv
in {FStar_Syntax_Syntax.ppname = id; FStar_Syntax_Syntax.index = _54_64.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _54_64.FStar_Syntax_Syntax.sort})))


let bv_to_name : FStar_Syntax_Syntax.bv  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.term = (fun bv r -> (FStar_Syntax_Syntax.bv_to_name (set_bv_range bv r)))


let unmangleMap : (Prims.string * Prims.string * FStar_Syntax_Syntax.delta_depth * FStar_Syntax_Syntax.fv_qual Prims.option) Prims.list = (("op_ColonColon", "Cons", FStar_Syntax_Syntax.Delta_constant, Some (FStar_Syntax_Syntax.Data_ctor)))::(("not", "op_Negation", FStar_Syntax_Syntax.Delta_equational, None))::[]


let unmangleOpName : FStar_Ident.ident  ->  FStar_Syntax_Syntax.term Prims.option = (fun id -> (FStar_Util.find_map unmangleMap (fun _54_73 -> (match (_54_73) with
| (x, y, dd, dq) -> begin
if (id.FStar_Ident.idText = x) then begin
(let _143_121 = (let _143_120 = (FStar_Ident.lid_of_path (("Prims")::(y)::[]) id.FStar_Ident.idRange)
in (FStar_Syntax_Syntax.fvar _143_120 dd dq))
in Some (_143_121))
end else begin
None
end
end))))


let try_lookup_id : env  ->  FStar_Ident.ident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env id -> (match ((unmangleOpName id)) with
| Some (f) -> begin
Some (f)
end
| _54_79 -> begin
(FStar_Util.find_map env.localbindings (fun _54_1 -> (match (_54_1) with
| (id', x) when (id'.FStar_Ident.idText = id.FStar_Ident.idText) -> begin
(let _143_127 = (bv_to_name x id.FStar_Ident.idRange)
in Some (_143_127))
end
| _54_85 -> begin
None
end)))
end))


let resolve_in_open_namespaces = (fun env lid finder -> (

let aux = (fun namespaces -> (match ((finder lid)) with
| Some (r) -> begin
Some (r)
end
| _54_95 -> begin
(

let ids = (FStar_Ident.ids_of_lid lid)
in (FStar_Util.find_map namespaces (fun ns -> (

let full_name = (FStar_Ident.lid_of_ids (FStar_List.append (FStar_Ident.ids_of_lid ns) ids))
in (finder full_name)))))
end))
in (let _143_138 = (let _143_137 = (current_module env)
in (_143_137)::env.open_namespaces)
in (aux _143_138))))


let fv_qual_of_se : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.fv_qual Prims.option = (fun _54_3 -> (match (_54_3) with
| FStar_Syntax_Syntax.Sig_datacon (_54_101, _54_103, _54_105, l, _54_108, quals, _54_111, _54_113) -> begin
(

let qopt = (FStar_Util.find_map quals (fun _54_2 -> (match (_54_2) with
| FStar_Syntax_Syntax.RecordConstructor (fs) -> begin
Some (FStar_Syntax_Syntax.Record_ctor ((l, fs)))
end
| _54_120 -> begin
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
| FStar_Syntax_Syntax.Sig_declare_typ (_54_125, _54_127, _54_129, quals, _54_132) -> begin
None
end
| _54_136 -> begin
None
end))


let lb_fv : FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.fv = (fun lbs lid -> (let _143_147 = (FStar_Util.find_map lbs (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in if (FStar_Syntax_Syntax.fv_eq_lid fv lid) then begin
Some (fv)
end else begin
None
end)))
in (FStar_All.pipe_right _143_147 FStar_Util.must)))


let try_lookup_name : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  foundname Prims.option = (fun any_val exclude_interf env lid -> (

let find_in_sig = (fun lid -> (match ((let _143_158 = (sigmap env)
in (FStar_Util.smap_try_find _143_158 lid.FStar_Ident.str))) with
| Some (_54_148, true) when exclude_interf -> begin
None
end
| None -> begin
None
end
| Some (se, _54_155) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_54_159) -> begin
(let _143_160 = (let _143_159 = (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.Delta_constant None)
in Term_name (_143_159))
in Some (_143_160))
end
| FStar_Syntax_Syntax.Sig_datacon (_54_162) -> begin
(let _143_163 = (let _143_162 = (let _143_161 = (fv_qual_of_se se)
in (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.Delta_constant _143_161))
in Term_name (_143_162))
in Some (_143_163))
end
| FStar_Syntax_Syntax.Sig_let ((_54_165, lbs), _54_169, _54_171, _54_173) -> begin
(

let fv = (lb_fv lbs lid)
in (let _143_165 = (let _143_164 = (FStar_Syntax_Syntax.fvar lid fv.FStar_Syntax_Syntax.fv_delta fv.FStar_Syntax_Syntax.fv_qual)
in Term_name (_143_164))
in Some (_143_165)))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _54_179, _54_181, quals, _54_184) -> begin
if (any_val || (FStar_All.pipe_right quals (FStar_Util.for_some (fun _54_4 -> (match (_54_4) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| _54_190 -> begin
false
end))))) then begin
(

let dd = if (FStar_Syntax_Util.is_primop_lid lid) then begin
FStar_Syntax_Syntax.Delta_equational
end else begin
FStar_Syntax_Syntax.Delta_constant
end
in (let _143_169 = (let _143_168 = (let _143_167 = (fv_qual_of_se se)
in (FStar_Syntax_Syntax.fvar lid dd _143_167))
in Term_name (_143_168))
in Some (_143_169)))
end else begin
None
end
end
| FStar_Syntax_Syntax.Sig_new_effect (ne, _54_194) -> begin
(let _143_172 = (let _143_171 = (let _143_170 = (FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname (FStar_Ident.range_of_lid lid))
in (se, _143_170))
in Eff_name (_143_171))
in Some (_143_172))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (_54_198) -> begin
Some (Eff_name ((se, lid)))
end
| _54_201 -> begin
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
in (FStar_Util.find_map env.recbindings (fun _54_210 -> (match (_54_210) with
| (id, l, dd) -> begin
if (id.FStar_Ident.idText = lid.FStar_Ident.ident.FStar_Ident.idText) then begin
(let _143_176 = (let _143_175 = (let _143_174 = (FStar_Ident.set_lid_range l (FStar_Ident.range_of_lid lid))
in (FStar_Syntax_Syntax.fvar _143_174 dd None))
in Term_name (_143_175))
in Some (_143_176))
end else begin
None
end
end))))
end)
end
| _54_212 -> begin
None
end)
in (match (found_id) with
| Some (_54_215) -> begin
found_id
end
| _54_218 -> begin
(resolve_in_open_namespaces env lid find_in_sig)
end))))


let try_lookup_effect_name' : Prims.bool  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident) Prims.option = (fun exclude_interf env lid -> (match ((try_lookup_name true exclude_interf env lid)) with
| Some (Eff_name (o, l)) -> begin
Some ((o, l))
end
| _54_228 -> begin
None
end))


let try_lookup_effect_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env l -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some (o, l) -> begin
Some (l)
end
| _54_236 -> begin
None
end))


let try_lookup_effect_defn : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl Prims.option = (fun env l -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some (FStar_Syntax_Syntax.Sig_new_effect (ne, _54_241), _54_245) -> begin
Some (ne)
end
| _54_249 -> begin
None
end))


let is_effect_name : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((try_lookup_effect_name env lid)) with
| None -> begin
false
end
| Some (_54_254) -> begin
true
end))


let lookup_letbinding_quals : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.qualifier Prims.list = (fun env lid -> (

let find_in_sig = (fun lid -> (match ((let _143_201 = (sigmap env)
in (FStar_Util.smap_try_find _143_201 lid.FStar_Ident.str))) with
| Some (FStar_Syntax_Syntax.Sig_declare_typ (lid, _54_262, _54_264, quals, _54_267), _54_271) -> begin
Some (quals)
end
| _54_275 -> begin
None
end))
in (match ((resolve_in_open_namespaces env lid find_in_sig)) with
| Some (quals) -> begin
quals
end
| _54_279 -> begin
[]
end)))


let try_lookup_module : env  ->  Prims.string Prims.list  ->  FStar_Syntax_Syntax.modul Prims.option = (fun env path -> (match ((FStar_List.tryFind (fun _54_284 -> (match (_54_284) with
| (mlid, modul) -> begin
((FStar_Ident.path_of_lid mlid) = path)
end)) env.modules)) with
| Some (_54_286, modul) -> begin
Some (modul)
end
| None -> begin
None
end))


let try_lookup_let : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env lid -> (

let find_in_sig = (fun lid -> (match ((let _143_213 = (sigmap env)
in (FStar_Util.smap_try_find _143_213 lid.FStar_Ident.str))) with
| Some (FStar_Syntax_Syntax.Sig_let ((_54_296, lbs), _54_300, _54_302, _54_304), _54_308) -> begin
(

let fv = (lb_fv lbs lid)
in (let _143_214 = (FStar_Syntax_Syntax.fvar lid fv.FStar_Syntax_Syntax.fv_delta fv.FStar_Syntax_Syntax.fv_qual)
in Some (_143_214)))
end
| _54_313 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))


let try_lookup_definition : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env lid -> (

let find_in_sig = (fun lid -> (match ((let _143_221 = (sigmap env)
in (FStar_Util.smap_try_find _143_221 lid.FStar_Ident.str))) with
| Some (FStar_Syntax_Syntax.Sig_let (lbs, _54_320, _54_322, _54_324), _54_328) -> begin
(FStar_Util.find_map (Prims.snd lbs) (fun lb -> (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv lid) -> begin
Some (lb.FStar_Syntax_Syntax.lbdef)
end
| _54_335 -> begin
None
end)))
end
| _54_337 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))


let try_lookup_lid' : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun any_val exclude_interf env lid -> (match ((try_lookup_name any_val exclude_interf env lid)) with
| Some (Term_name (e)) -> begin
Some (e)
end
| _54_346 -> begin
None
end))


let try_lookup_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env l -> (try_lookup_lid' env.iface false env l))


let try_lookup_datacon : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.fv Prims.option = (fun env lid -> (

let find_in_sig = (fun lid -> (match ((let _143_241 = (sigmap env)
in (FStar_Util.smap_try_find _143_241 lid.FStar_Ident.str))) with
| Some (FStar_Syntax_Syntax.Sig_declare_typ (_54_354, _54_356, _54_358, quals, _54_361), _54_365) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _54_5 -> (match (_54_5) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| _54_371 -> begin
false
end)))) then begin
(let _143_243 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant None)
in Some (_143_243))
end else begin
None
end
end
| Some (FStar_Syntax_Syntax.Sig_datacon (_54_373), _54_376) -> begin
(let _143_244 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in Some (_143_244))
end
| _54_380 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))


let find_all_datacons : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.list Prims.option = (fun env lid -> (

let find_in_sig = (fun lid -> (match ((let _143_251 = (sigmap env)
in (FStar_Util.smap_try_find _143_251 lid.FStar_Ident.str))) with
| Some (FStar_Syntax_Syntax.Sig_inductive_typ (_54_386, _54_388, _54_390, _54_392, _54_394, datas, _54_397, _54_399), _54_403) -> begin
Some (datas)
end
| _54_407 -> begin
None
end))
in (resolve_in_open_namespaces env lid find_in_sig)))


let record_cache_aux : ((Prims.unit  ->  Prims.unit) * (Prims.unit  ->  Prims.unit) * (Prims.unit  ->  record_or_dc Prims.list) * (record_or_dc  ->  Prims.unit)) = (

let record_cache = (FStar_Util.mk_ref (([])::[]))
in (

let push = (fun _54_410 -> (match (()) with
| () -> begin
(let _143_265 = (let _143_264 = (let _143_262 = (FStar_ST.read record_cache)
in (FStar_List.hd _143_262))
in (let _143_263 = (FStar_ST.read record_cache)
in (_143_264)::_143_263))
in (FStar_ST.op_Colon_Equals record_cache _143_265))
end))
in (

let pop = (fun _54_412 -> (match (()) with
| () -> begin
(let _143_269 = (let _143_268 = (FStar_ST.read record_cache)
in (FStar_List.tl _143_268))
in (FStar_ST.op_Colon_Equals record_cache _143_269))
end))
in (

let peek = (fun _54_414 -> (match (()) with
| () -> begin
(let _143_272 = (FStar_ST.read record_cache)
in (FStar_List.hd _143_272))
end))
in (

let insert = (fun r -> (let _143_279 = (let _143_278 = (let _143_275 = (peek ())
in (r)::_143_275)
in (let _143_277 = (let _143_276 = (FStar_ST.read record_cache)
in (FStar_List.tl _143_276))
in (_143_278)::_143_277))
in (FStar_ST.op_Colon_Equals record_cache _143_279)))
in (push, pop, peek, insert))))))


let push_record_cache : Prims.unit  ->  Prims.unit = (

let _54_424 = record_cache_aux
in (match (_54_424) with
| (push, _54_419, _54_421, _54_423) -> begin
push
end))


let pop_record_cache : Prims.unit  ->  Prims.unit = (

let _54_432 = record_cache_aux
in (match (_54_432) with
| (_54_426, pop, _54_429, _54_431) -> begin
pop
end))


let peek_record_cache : Prims.unit  ->  record_or_dc Prims.list = (

let _54_440 = record_cache_aux
in (match (_54_440) with
| (_54_434, _54_436, peek, _54_439) -> begin
peek
end))


let insert_record_cache : record_or_dc  ->  Prims.unit = (

let _54_448 = record_cache_aux
in (match (_54_448) with
| (_54_442, _54_444, _54_446, insert) -> begin
insert
end))


let extract_record : env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun e _54_9 -> (match (_54_9) with
| FStar_Syntax_Syntax.Sig_bundle (sigs, _54_453, _54_455, _54_457) -> begin
(

let is_rec = (FStar_Util.for_some (fun _54_6 -> (match (_54_6) with
| (FStar_Syntax_Syntax.RecordType (_)) | (FStar_Syntax_Syntax.RecordConstructor (_)) -> begin
true
end
| _54_468 -> begin
false
end)))
in (

let find_dc = (fun dc -> (FStar_All.pipe_right sigs (FStar_Util.find_opt (fun _54_7 -> (match (_54_7) with
| FStar_Syntax_Syntax.Sig_datacon (lid, _54_475, _54_477, _54_479, _54_481, _54_483, _54_485, _54_487) -> begin
(FStar_Ident.lid_equals dc lid)
end
| _54_491 -> begin
false
end)))))
in (FStar_All.pipe_right sigs (FStar_List.iter (fun _54_8 -> (match (_54_8) with
| FStar_Syntax_Syntax.Sig_inductive_typ (typename, univs, parms, _54_497, _54_499, dc::[], tags, _54_504) -> begin
(match ((let _143_350 = (find_dc dc)
in (FStar_All.pipe_left FStar_Util.must _143_350))) with
| FStar_Syntax_Syntax.Sig_datacon (constrname, _54_509, t, _54_512, _54_514, _54_516, _54_518, _54_520) -> begin
(

let _54_526 = (FStar_Syntax_Util.arrow_formals t)
in (match (_54_526) with
| (formals, _54_525) -> begin
(

let is_rec = (is_rec tags)
in (

let fields = (FStar_All.pipe_right formals (FStar_List.collect (fun _54_530 -> (match (_54_530) with
| (x, q) -> begin
if ((FStar_Syntax_Syntax.is_null_bv x) || (is_rec && (FStar_Syntax_Syntax.is_implicit q))) then begin
[]
end else begin
(let _143_354 = (let _143_353 = (let _143_352 = if is_rec then begin
(FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname)
end else begin
x.FStar_Syntax_Syntax.ppname
end
in (qual constrname _143_352))
in (_143_353, x.FStar_Syntax_Syntax.sort))
in (_143_354)::[])
end
end))))
in (

let record = {typename = typename; constrname = constrname; parms = parms; fields = fields; is_record = is_rec}
in (insert_record_cache record))))
end))
end
| _54_534 -> begin
()
end)
end
| _54_536 -> begin
()
end))))))
end
| _54_538 -> begin
()
end))


let try_lookup_record_or_dc_by_field_name : env  ->  FStar_Ident.lident  ->  (record_or_dc * FStar_Ident.lident) Prims.option = (fun env fieldname -> (

let maybe_add_constrname = (fun ns c -> (

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
(let _143_365 = (aux tl)
in (hd)::_143_365)
end))
in (aux ns)))
in (

let find_in_cache = (fun fieldname -> (

let _54_556 = (fieldname.FStar_Ident.ns, fieldname.FStar_Ident.ident)
in (match (_54_556) with
| (ns, fieldname) -> begin
(let _143_370 = (peek_record_cache ())
in (FStar_Util.find_map _143_370 (fun record -> (

let constrname = record.constrname.FStar_Ident.ident
in (

let ns = (maybe_add_constrname ns constrname)
in (

let fname = (FStar_Ident.lid_of_ids (FStar_List.append ns ((fieldname)::[])))
in (FStar_Util.find_map record.fields (fun _54_564 -> (match (_54_564) with
| (f, _54_563) -> begin
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
| _54_572 -> begin
None
end))


let try_lookup_projector_by_field_name : env  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * Prims.bool) Prims.option = (fun env fieldname -> (match ((try_lookup_record_or_dc_by_field_name env fieldname)) with
| Some (r, f) -> begin
Some ((f, r.is_record))
end
| _54_580 -> begin
None
end))


let qualify_field_to_record : env  ->  record_or_dc  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env recd f -> (

let qualify = (fun fieldname -> (

let _54_588 = (fieldname.FStar_Ident.ns, fieldname.FStar_Ident.ident)
in (match (_54_588) with
| (ns, fieldname) -> begin
(

let constrname = recd.constrname.FStar_Ident.ident
in (

let fname = (FStar_Ident.lid_of_ids (FStar_List.append (FStar_List.append ns ((constrname)::[])) ((fieldname)::[])))
in (FStar_Util.find_map recd.fields (fun _54_594 -> (match (_54_594) with
| (f, _54_593) -> begin
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

let _54_599 = env
in {curmodule = _54_599.curmodule; modules = _54_599.modules; open_namespaces = []; sigaccum = _54_599.sigaccum; localbindings = _54_599.localbindings; recbindings = _54_599.recbindings; sigmap = _54_599.sigmap; default_result_effect = _54_599.default_result_effect; iface = _54_599.iface; admitted_iface = _54_599.admitted_iface; expect_typ = _54_599.expect_typ})
in (match ((try_lookup_lid' any_val exclude_if env lid)) with
| None -> begin
true
end
| Some (_54_604) -> begin
false
end)))


let push_bv : env  ->  FStar_Ident.ident  ->  (env * FStar_Syntax_Syntax.bv) = (fun env x -> (

let bv = (FStar_Syntax_Syntax.gen_bv x.FStar_Ident.idText (Some (x.FStar_Ident.idRange)) FStar_Syntax_Syntax.tun)
in ((

let _54_609 = env
in {curmodule = _54_609.curmodule; modules = _54_609.modules; open_namespaces = _54_609.open_namespaces; sigaccum = _54_609.sigaccum; localbindings = ((x, bv))::env.localbindings; recbindings = _54_609.recbindings; sigmap = _54_609.sigmap; default_result_effect = _54_609.default_result_effect; iface = _54_609.iface; admitted_iface = _54_609.admitted_iface; expect_typ = _54_609.expect_typ}), bv)))


let push_top_level_rec_binding : env  ->  FStar_Ident.ident  ->  FStar_Syntax_Syntax.delta_depth  ->  env = (fun env x dd -> (

let l = (qualify env x)
in if (unique false true env l) then begin
(

let _54_615 = env
in {curmodule = _54_615.curmodule; modules = _54_615.modules; open_namespaces = _54_615.open_namespaces; sigaccum = _54_615.sigaccum; localbindings = _54_615.localbindings; recbindings = ((x, l, dd))::env.recbindings; sigmap = _54_615.sigmap; default_result_effect = _54_615.default_result_effect; iface = _54_615.iface; admitted_iface = _54_615.admitted_iface; expect_typ = _54_615.expect_typ})
end else begin
(Prims.raise (FStar_Syntax_Syntax.Error (((Prims.strcat "Duplicate top-level names " l.FStar_Ident.str), (FStar_Ident.range_of_lid l)))))
end))


let push_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env s -> (

let err = (fun l -> (

let sopt = (let _143_412 = (sigmap env)
in (FStar_Util.smap_try_find _143_412 l.FStar_Ident.str))
in (

let r = (match (sopt) with
| Some (se, _54_624) -> begin
(match ((let _143_413 = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_Util.find_opt (FStar_Ident.lid_equals l) _143_413))) with
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
in (let _143_416 = (let _143_415 = (let _143_414 = (FStar_Util.format2 "Duplicate top-level names [%s]; previously declared at %s" (FStar_Ident.text_of_lid l) r)
in (_143_414, (FStar_Ident.range_of_lid l)))
in FStar_Syntax_Syntax.Error (_143_415))
in (Prims.raise _143_416)))))
in (

let env = (

let _54_642 = (match (s) with
| FStar_Syntax_Syntax.Sig_let (_54_633) -> begin
(false, true)
end
| FStar_Syntax_Syntax.Sig_bundle (_54_636) -> begin
(true, true)
end
| _54_639 -> begin
(false, false)
end)
in (match (_54_642) with
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

let _54_646 = (extract_record env s)
in (

let _54_648 = env
in {curmodule = _54_648.curmodule; modules = _54_648.modules; open_namespaces = _54_648.open_namespaces; sigaccum = (s)::env.sigaccum; localbindings = _54_648.localbindings; recbindings = _54_648.recbindings; sigmap = _54_648.sigmap; default_result_effect = _54_648.default_result_effect; iface = _54_648.iface; admitted_iface = _54_648.admitted_iface; expect_typ = _54_648.expect_typ}))
end
| Some (l) -> begin
(err l)
end))
end))
in (

let _54_667 = (match (s) with
| FStar_Syntax_Syntax.Sig_bundle (ses, _54_655, _54_657, _54_659) -> begin
(let _143_420 = (FStar_List.map (fun se -> (let _143_419 = (FStar_Syntax_Util.lids_of_sigelt se)
in (_143_419, se))) ses)
in (env, _143_420))
end
| _54_664 -> begin
(let _143_423 = (let _143_422 = (let _143_421 = (FStar_Syntax_Util.lids_of_sigelt s)
in (_143_421, s))
in (_143_422)::[])
in (env, _143_423))
end)
in (match (_54_667) with
| (env, lss) -> begin
(

let _54_672 = (FStar_All.pipe_right lss (FStar_List.iter (fun _54_670 -> (match (_54_670) with
| (lids, se) -> begin
(FStar_All.pipe_right lids (FStar_List.iter (fun lid -> (let _143_426 = (sigmap env)
in (FStar_Util.smap_add _143_426 lid.FStar_Ident.str (se, (env.iface && (not (env.admitted_iface)))))))))
end))))
in env)
end)))))


let push_namespace : env  ->  FStar_Ident.lident  ->  env = (fun env lid -> (

let _54_676 = env
in {curmodule = _54_676.curmodule; modules = _54_676.modules; open_namespaces = (lid)::env.open_namespaces; sigaccum = _54_676.sigaccum; localbindings = _54_676.localbindings; recbindings = _54_676.recbindings; sigmap = _54_676.sigmap; default_result_effect = _54_676.default_result_effect; iface = _54_676.iface; admitted_iface = _54_676.admitted_iface; expect_typ = _54_676.expect_typ}))


let check_admits : env  ->  Prims.unit = (fun env -> (FStar_All.pipe_right env.sigaccum (FStar_List.iter (fun se -> (match (se) with
| FStar_Syntax_Syntax.Sig_declare_typ (l, u, t, quals, r) -> begin
(match ((try_lookup_lid env l)) with
| None -> begin
(

let _54_688 = (let _143_436 = (let _143_435 = (FStar_Range.string_of_range (FStar_Ident.range_of_lid l))
in (let _143_434 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format2 "%s: Warning: Admitting %s without a definition\n" _143_435 _143_434)))
in (FStar_Util.print_string _143_436))
in (let _143_437 = (sigmap env)
in (FStar_Util.smap_add _143_437 l.FStar_Ident.str (FStar_Syntax_Syntax.Sig_declare_typ ((l, u, t, (FStar_Syntax_Syntax.Assumption)::quals, r)), false))))
end
| Some (_54_691) -> begin
()
end)
end
| _54_694 -> begin
()
end)))))


let finish : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env modul -> (

let _54_754 = (FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations (FStar_List.iter (fun _54_11 -> (match (_54_11) with
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _54_701, _54_703) -> begin
if ((FStar_List.contains FStar_Syntax_Syntax.Private quals) || (FStar_List.contains FStar_Syntax_Syntax.Abstract quals)) then begin
(FStar_All.pipe_right ses (FStar_List.iter (fun _54_10 -> (match (_54_10) with
| FStar_Syntax_Syntax.Sig_datacon (lid, _54_709, _54_711, _54_713, _54_715, _54_717, _54_719, _54_721) -> begin
(let _143_444 = (sigmap env)
in (FStar_Util.smap_remove _143_444 lid.FStar_Ident.str))
end
| _54_725 -> begin
()
end))))
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _54_728, _54_730, quals, _54_733) -> begin
if (FStar_List.contains FStar_Syntax_Syntax.Private quals) then begin
(let _143_445 = (sigmap env)
in (FStar_Util.smap_remove _143_445 lid.FStar_Ident.str))
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_let ((_54_737, lbs), r, _54_742, quals) -> begin
(

let _54_747 = if ((FStar_List.contains FStar_Syntax_Syntax.Private quals) || (FStar_List.contains FStar_Syntax_Syntax.Abstract quals)) then begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (let _143_451 = (sigmap env)
in (let _143_450 = (let _143_449 = (let _143_448 = (let _143_447 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _143_447.FStar_Syntax_Syntax.fv_name)
in _143_448.FStar_Syntax_Syntax.v)
in _143_449.FStar_Ident.str)
in (FStar_Util.smap_remove _143_451 _143_450))))))
end else begin
()
end
in if ((FStar_List.contains FStar_Syntax_Syntax.Abstract quals) && (not ((FStar_List.contains FStar_Syntax_Syntax.Private quals)))) then begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (

let lid = (let _143_454 = (let _143_453 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _143_453.FStar_Syntax_Syntax.fv_name)
in _143_454.FStar_Syntax_Syntax.v)
in (

let decl = FStar_Syntax_Syntax.Sig_declare_typ ((lid, lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp, (FStar_Syntax_Syntax.Assumption)::quals, r))
in (let _143_455 = (sigmap env)
in (FStar_Util.smap_add _143_455 lid.FStar_Ident.str (decl, false))))))))
end else begin
()
end)
end
| _54_753 -> begin
()
end))))
in (

let _54_756 = env
in {curmodule = None; modules = ((modul.FStar_Syntax_Syntax.name, modul))::env.modules; open_namespaces = []; sigaccum = []; localbindings = []; recbindings = []; sigmap = _54_756.sigmap; default_result_effect = _54_756.default_result_effect; iface = _54_756.iface; admitted_iface = _54_756.admitted_iface; expect_typ = _54_756.expect_typ})))


let push : env  ->  env = (fun env -> (

let _54_759 = (push_record_cache ())
in (

let _54_761 = env
in (let _143_460 = (let _143_459 = (let _143_458 = (sigmap env)
in (FStar_Util.smap_copy _143_458))
in (_143_459)::env.sigmap)
in {curmodule = _54_761.curmodule; modules = _54_761.modules; open_namespaces = _54_761.open_namespaces; sigaccum = _54_761.sigaccum; localbindings = _54_761.localbindings; recbindings = _54_761.recbindings; sigmap = _143_460; default_result_effect = _54_761.default_result_effect; iface = _54_761.iface; admitted_iface = _54_761.admitted_iface; expect_typ = _54_761.expect_typ}))))


let mark : env  ->  env = (fun env -> (push env))


let reset_mark : env  ->  env = (fun env -> (

let _54_765 = env
in (let _143_465 = (FStar_List.tl env.sigmap)
in {curmodule = _54_765.curmodule; modules = _54_765.modules; open_namespaces = _54_765.open_namespaces; sigaccum = _54_765.sigaccum; localbindings = _54_765.localbindings; recbindings = _54_765.recbindings; sigmap = _143_465; default_result_effect = _54_765.default_result_effect; iface = _54_765.iface; admitted_iface = _54_765.admitted_iface; expect_typ = _54_765.expect_typ})))


let commit_mark : env  ->  env = (fun env -> (match (env.sigmap) with
| hd::_54_770::tl -> begin
(

let _54_774 = env
in {curmodule = _54_774.curmodule; modules = _54_774.modules; open_namespaces = _54_774.open_namespaces; sigaccum = _54_774.sigaccum; localbindings = _54_774.localbindings; recbindings = _54_774.recbindings; sigmap = (hd)::tl; default_result_effect = _54_774.default_result_effect; iface = _54_774.iface; admitted_iface = _54_774.admitted_iface; expect_typ = _54_774.expect_typ})
end
| _54_777 -> begin
(FStar_All.failwith "Impossible")
end))


let pop : env  ->  env = (fun env -> (match (env.sigmap) with
| _54_781::maps -> begin
(

let _54_783 = (pop_record_cache ())
in (

let _54_785 = env
in {curmodule = _54_785.curmodule; modules = _54_785.modules; open_namespaces = _54_785.open_namespaces; sigaccum = _54_785.sigaccum; localbindings = _54_785.localbindings; recbindings = _54_785.recbindings; sigmap = maps; default_result_effect = _54_785.default_result_effect; iface = _54_785.iface; admitted_iface = _54_785.admitted_iface; expect_typ = _54_785.expect_typ}))
end
| _54_788 -> begin
(FStar_All.failwith "No more modules to pop")
end))


let export_interface : FStar_Ident.lident  ->  env  ->  env = (fun m env -> (

let sigelt_in_m = (fun se -> (match ((FStar_Syntax_Util.lids_of_sigelt se)) with
| l::_54_794 -> begin
(l.FStar_Ident.nsstr = m.FStar_Ident.str)
end
| _54_798 -> begin
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

let _54_822 = (FStar_All.pipe_right keys (FStar_List.iter (fun k -> (match ((FStar_Util.smap_try_find sm' k)) with
| Some (se, true) when (sigelt_in_m se) -> begin
(

let _54_808 = (FStar_Util.smap_remove sm' k)
in (

let se = (match (se) with
| FStar_Syntax_Syntax.Sig_declare_typ (l, u, t, q, r) -> begin
FStar_Syntax_Syntax.Sig_declare_typ ((l, u, t, (FStar_Syntax_Syntax.Assumption)::q, r))
end
| _54_818 -> begin
se
end)
in (FStar_Util.smap_add sm' k (se, false))))
end
| _54_821 -> begin
()
end))))
in env)))))))


let finish_module_or_interface : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env modul -> (

let _54_826 = if (not (modul.FStar_Syntax_Syntax.is_interface)) then begin
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

let _54_835 = env
in {curmodule = Some (mname); modules = _54_835.modules; open_namespaces = open_ns; sigaccum = _54_835.sigaccum; localbindings = _54_835.localbindings; recbindings = _54_835.recbindings; sigmap = env.sigmap; default_result_effect = _54_835.default_result_effect; iface = intf; admitted_iface = admitted; expect_typ = _54_835.expect_typ})))
in (match ((FStar_All.pipe_right env.modules (FStar_Util.find_opt (fun _54_840 -> (match (_54_840) with
| (l, _54_839) -> begin
(FStar_Ident.lid_equals l mname)
end))))) with
| None -> begin
((prep env), false)
end
| Some (_54_843, m) -> begin
(

let _54_847 = if ((not (m.FStar_Syntax_Syntax.is_interface)) || intf) then begin
(let _143_494 = (let _143_493 = (let _143_492 = (FStar_Util.format1 "Duplicate module or interface name: %s" mname.FStar_Ident.str)
in (_143_492, (FStar_Ident.range_of_lid mname)))
in FStar_Syntax_Syntax.Error (_143_493))
in (Prims.raise _143_494))
end else begin
()
end
in (let _143_496 = (let _143_495 = (push env)
in (prep _143_495))
in (_143_496, true)))
end)))


let enter_monad_scope : env  ->  FStar_Ident.ident  ->  env = (fun env mname -> (

let curmod = (current_module env)
in (

let mscope = (FStar_Ident.lid_of_ids (FStar_List.append curmod.FStar_Ident.ns ((curmod.FStar_Ident.ident)::(mname)::[])))
in (

let _54_853 = env
in {curmodule = Some (mscope); modules = _54_853.modules; open_namespaces = (curmod)::env.open_namespaces; sigaccum = _54_853.sigaccum; localbindings = _54_853.localbindings; recbindings = _54_853.recbindings; sigmap = _54_853.sigmap; default_result_effect = _54_853.default_result_effect; iface = _54_853.iface; admitted_iface = _54_853.admitted_iface; expect_typ = _54_853.expect_typ}))))


let exit_monad_scope : env  ->  env  ->  env = (fun env0 env -> (

let _54_857 = env
in {curmodule = env0.curmodule; modules = _54_857.modules; open_namespaces = env0.open_namespaces; sigaccum = _54_857.sigaccum; localbindings = _54_857.localbindings; recbindings = _54_857.recbindings; sigmap = _54_857.sigmap; default_result_effect = _54_857.default_result_effect; iface = _54_857.iface; admitted_iface = _54_857.admitted_iface; expect_typ = _54_857.expect_typ}))


let fail_or = (fun lookup lid -> (match ((lookup lid)) with
| None -> begin
(let _143_512 = (let _143_511 = (let _143_510 = (FStar_Util.format1 "Identifier not found: [%s]" (FStar_Ident.text_of_lid lid))
in (_143_510, (FStar_Ident.range_of_lid lid)))
in FStar_Syntax_Syntax.Error (_143_511))
in (Prims.raise _143_512))
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




