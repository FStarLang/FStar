
open Prims

type local_binding =
(FStar_Ident.ident * FStar_Syntax_Syntax.bv * Prims.bool)


type rec_binding =
(FStar_Ident.ident * FStar_Ident.lid * FStar_Syntax_Syntax.delta_depth)


type module_abbrev =
(FStar_Ident.ident * FStar_Ident.lident)


type open_kind =
| Open_module
| Open_namespace


let is_Open_module = (fun _discr_ -> (match (_discr_) with
| Open_module (_) -> begin
true
end
| _ -> begin
false
end))


let is_Open_namespace = (fun _discr_ -> (match (_discr_) with
| Open_namespace (_) -> begin
true
end
| _ -> begin
false
end))


type open_module_or_namespace =
(FStar_Ident.lident * open_kind)


type record_or_dc =
{typename : FStar_Ident.lident; constrname : FStar_Ident.ident; parms : FStar_Syntax_Syntax.binders; fields : (FStar_Ident.ident * FStar_Syntax_Syntax.typ) Prims.list; is_private_or_abstract : Prims.bool; is_record : Prims.bool}


let is_Mkrecord_or_dc : record_or_dc  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkrecord_or_dc"))))


type scope_mod =
| Local_binding of local_binding
| Rec_binding of rec_binding
| Module_abbrev of module_abbrev
| Open_module_or_namespace of open_module_or_namespace
| Top_level_def of FStar_Ident.ident
| Record_or_dc of record_or_dc


let is_Local_binding = (fun _discr_ -> (match (_discr_) with
| Local_binding (_) -> begin
true
end
| _ -> begin
false
end))


let is_Rec_binding = (fun _discr_ -> (match (_discr_) with
| Rec_binding (_) -> begin
true
end
| _ -> begin
false
end))


let is_Module_abbrev = (fun _discr_ -> (match (_discr_) with
| Module_abbrev (_) -> begin
true
end
| _ -> begin
false
end))


let is_Open_module_or_namespace = (fun _discr_ -> (match (_discr_) with
| Open_module_or_namespace (_) -> begin
true
end
| _ -> begin
false
end))


let is_Top_level_def = (fun _discr_ -> (match (_discr_) with
| Top_level_def (_) -> begin
true
end
| _ -> begin
false
end))


let is_Record_or_dc = (fun _discr_ -> (match (_discr_) with
| Record_or_dc (_) -> begin
true
end
| _ -> begin
false
end))


let ___Local_binding____0 = (fun projectee -> (match (projectee) with
| Local_binding (_65_35) -> begin
_65_35
end))


let ___Rec_binding____0 = (fun projectee -> (match (projectee) with
| Rec_binding (_65_38) -> begin
_65_38
end))


let ___Module_abbrev____0 = (fun projectee -> (match (projectee) with
| Module_abbrev (_65_41) -> begin
_65_41
end))


let ___Open_module_or_namespace____0 = (fun projectee -> (match (projectee) with
| Open_module_or_namespace (_65_44) -> begin
_65_44
end))


let ___Top_level_def____0 = (fun projectee -> (match (projectee) with
| Top_level_def (_65_47) -> begin
_65_47
end))


let ___Record_or_dc____0 = (fun projectee -> (match (projectee) with
| Record_or_dc (_65_50) -> begin
_65_50
end))


type env =
{curmodule : FStar_Ident.lident Prims.option; curmonad : FStar_Ident.ident Prims.option; modules : (FStar_Ident.lident * FStar_Syntax_Syntax.modul) Prims.list; scope_mods : scope_mod Prims.list; sigaccum : FStar_Syntax_Syntax.sigelts; sigmap : (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap; default_result_effect : FStar_Ident.lident; iface : Prims.bool; admitted_iface : Prims.bool; expect_typ : Prims.bool}


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
| Term_name (_65_64) -> begin
_65_64
end))


let ___Eff_name____0 = (fun projectee -> (match (projectee) with
| Eff_name (_65_67) -> begin
_65_67
end))


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
(let _163_175 = (current_module env)
in (qual _163_175 id))
end
| Some (monad) -> begin
(let _163_177 = (let _163_176 = (current_module env)
in (qual _163_176 monad))
in (FStar_Syntax_Util.mk_field_projector_name_from_ident _163_177 id))
end))


let new_sigmap = (fun _65_80 -> (match (()) with
| () -> begin
(FStar_Util.smap_create (Prims.parse_int "100"))
end))


let empty_env : Prims.unit  ->  env = (fun _65_81 -> (match (()) with
| () -> begin
(let _163_181 = (new_sigmap ())
in {curmodule = None; curmonad = None; modules = []; scope_mods = []; sigaccum = []; sigmap = _163_181; default_result_effect = FStar_Syntax_Const.effect_Tot_lid; iface = false; admitted_iface = false; expect_typ = false})
end))


let sigmap : env  ->  (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap = (fun env -> env.sigmap)


let has_all_in_scope : env  ->  Prims.bool = (fun env -> (FStar_List.existsb (fun _65_87 -> (match (_65_87) with
| (m, _65_86) -> begin
(FStar_Ident.lid_equals m FStar_Syntax_Const.all_lid)
end)) env.modules))


let default_total : env  ->  env = (fun env -> (

let _65_89 = env
in {curmodule = _65_89.curmodule; curmonad = _65_89.curmonad; modules = _65_89.modules; scope_mods = _65_89.scope_mods; sigaccum = _65_89.sigaccum; sigmap = _65_89.sigmap; default_result_effect = FStar_Syntax_Const.effect_Tot_lid; iface = _65_89.iface; admitted_iface = _65_89.admitted_iface; expect_typ = _65_89.expect_typ}))


let default_ml : env  ->  env = (fun env -> if (has_all_in_scope env) then begin
(

let _65_92 = env
in {curmodule = _65_92.curmodule; curmonad = _65_92.curmonad; modules = _65_92.modules; scope_mods = _65_92.scope_mods; sigaccum = _65_92.sigaccum; sigmap = _65_92.sigmap; default_result_effect = FStar_Syntax_Const.effect_ML_lid; iface = _65_92.iface; admitted_iface = _65_92.admitted_iface; expect_typ = _65_92.expect_typ})
end else begin
env
end)


let set_bv_range : FStar_Syntax_Syntax.bv  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.bv = (fun bv r -> (

let id = (

let _65_96 = bv.FStar_Syntax_Syntax.ppname
in {FStar_Ident.idText = _65_96.FStar_Ident.idText; FStar_Ident.idRange = r})
in (

let _65_99 = bv
in {FStar_Syntax_Syntax.ppname = id; FStar_Syntax_Syntax.index = _65_99.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _65_99.FStar_Syntax_Syntax.sort})))


let bv_to_name : FStar_Syntax_Syntax.bv  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.term = (fun bv r -> (FStar_Syntax_Syntax.bv_to_name (set_bv_range bv r)))


let unmangleMap : (Prims.string * Prims.string * FStar_Syntax_Syntax.delta_depth * FStar_Syntax_Syntax.fv_qual Prims.option) Prims.list = ((("op_ColonColon"), ("Cons"), (FStar_Syntax_Syntax.Delta_constant), (Some (FStar_Syntax_Syntax.Data_ctor))))::((("not"), ("op_Negation"), (FStar_Syntax_Syntax.Delta_equational), (None)))::[]


let unmangleOpName : FStar_Ident.ident  ->  (FStar_Syntax_Syntax.term * Prims.bool) Prims.option = (fun id -> (

let t = (FStar_Util.find_map unmangleMap (fun _65_108 -> (match (_65_108) with
| (x, y, dd, dq) -> begin
if (id.FStar_Ident.idText = x) then begin
(let _163_203 = (let _163_202 = (FStar_Ident.lid_of_path (("Prims")::(y)::[]) id.FStar_Ident.idRange)
in (FStar_Syntax_Syntax.fvar _163_202 dd dq))
in Some (_163_203))
end else begin
None
end
end)))
in (match (t) with
| Some (v) -> begin
Some (((v), (false)))
end
| None -> begin
None
end)))


type 'a cont_t =
| Cont_ok of 'a
| Cont_fail
| Cont_ignore


let is_Cont_ok = (fun _ _discr_ -> (match (_discr_) with
| Cont_ok (_) -> begin
true
end
| _ -> begin
false
end))


let is_Cont_fail = (fun _ _discr_ -> (match (_discr_) with
| Cont_fail (_) -> begin
true
end
| _ -> begin
false
end))


let is_Cont_ignore = (fun _ _discr_ -> (match (_discr_) with
| Cont_ignore (_) -> begin
true
end
| _ -> begin
false
end))


let ___Cont_ok____0 = (fun projectee -> (match (projectee) with
| Cont_ok (_65_116) -> begin
_65_116
end))


let option_of_cont = (fun k_ignore _65_1 -> (match (_65_1) with
| Cont_ok (a) -> begin
Some (a)
end
| Cont_fail -> begin
None
end
| Cont_ignore -> begin
(k_ignore ())
end))


let find_in_record = (fun ns id record cont -> (

let typename' = (FStar_Ident.lid_of_ids (FStar_List.append ns ((record.typename.FStar_Ident.ident)::[])))
in if (FStar_Ident.lid_equals typename' record.typename) then begin
(

let fname = (FStar_Ident.lid_of_ids (FStar_List.append record.typename.FStar_Ident.ns ((id)::[])))
in (

let find = (FStar_Util.find_map record.fields (fun _65_133 -> (match (_65_133) with
| (f, _65_132) -> begin
if (id.FStar_Ident.idText = f.FStar_Ident.idText) then begin
Some (record)
end else begin
None
end
end)))
in (match (find) with
| Some (r) -> begin
(cont r)
end
| None -> begin
Cont_ignore
end)))
end else begin
Cont_ignore
end))


let try_lookup_id'' = (fun env id k_local_binding k_rec_binding k_record find_in_module lookup_default_id -> (

let check_local_binding_id = (fun _65_2 -> (match (_65_2) with
| (id', _65_149, _65_151) -> begin
(id'.FStar_Ident.idText = id.FStar_Ident.idText)
end))
in (

let check_rec_binding_id = (fun _65_3 -> (match (_65_3) with
| (id', _65_157, _65_159) -> begin
(id'.FStar_Ident.idText = id.FStar_Ident.idText)
end))
in (

let curmod_ns = (let _163_264 = (current_module env)
in (FStar_Ident.ids_of_lid _163_264))
in (

let proc = (fun _65_4 -> (match (_65_4) with
| Local_binding (l) when (check_local_binding_id l) -> begin
(k_local_binding l)
end
| Rec_binding (r) when (check_rec_binding_id r) -> begin
(k_rec_binding r)
end
| Open_module_or_namespace (ns, _65_170) -> begin
(

let lid = (qual ns id)
in (find_in_module lid))
end
| Top_level_def (id') when (id'.FStar_Ident.idText = id.FStar_Ident.idText) -> begin
(lookup_default_id Cont_ignore id)
end
| Record_or_dc (r) -> begin
(find_in_record curmod_ns id r k_record)
end
| _65_179 -> begin
Cont_ignore
end))
in (

let rec aux = (fun _65_5 -> (match (_65_5) with
| (a)::q -> begin
(let _163_270 = (proc a)
in (option_of_cont (fun _65_186 -> (aux q)) _163_270))
end
| [] -> begin
(let _163_272 = (lookup_default_id Cont_fail id)
in (option_of_cont (fun _65_189 -> None) _163_272))
end))
in (aux env.scope_mods)))))))


let found_local_binding = (fun r _65_195 -> (match (_65_195) with
| (id', x, mut) -> begin
(let _163_275 = (bv_to_name x r)
in ((_163_275), (mut)))
end))


let find_in_module = (fun env lid k_global_def k_not_found -> (match ((FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str)) with
| Some (sb) -> begin
(k_global_def lid sb)
end
| None -> begin
k_not_found
end))


let try_lookup_id : env  ->  FStar_Ident.ident  ->  (FStar_Syntax_Syntax.term * Prims.bool) Prims.option = (fun env id -> (match ((unmangleOpName id)) with
| Some (f) -> begin
Some (f)
end
| _65_208 -> begin
(try_lookup_id'' env id (fun r -> (let _163_291 = (found_local_binding id.FStar_Ident.idRange r)
in Cont_ok (_163_291))) (fun _65_220 -> Cont_fail) (fun _65_218 -> Cont_ignore) (fun i -> (find_in_module env i (fun _65_214 _65_216 -> Cont_fail) Cont_ignore)) (fun _65_209 _65_211 -> Cont_fail))
end))


let lookup_default_id = (fun env id k_global_def k_not_found -> (

let find_in_monad = (match (env.curmonad) with
| Some (_65_229) -> begin
(

let lid = (qualify env id)
in (match ((FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str)) with
| Some (r) -> begin
(let _163_309 = (k_global_def lid r)
in Some (_163_309))
end
| None -> begin
None
end))
end
| None -> begin
None
end)
in (match (find_in_monad) with
| Some (v) -> begin
v
end
| None -> begin
(

let lid = (let _163_310 = (current_module env)
in (qual _163_310 id))
in (find_in_module env lid k_global_def k_not_found))
end)))


let module_is_defined : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> ((let _163_315 = (current_module env)
in (FStar_Ident.lid_equals lid _163_315)) || (FStar_List.existsb (fun x -> (FStar_Ident.lid_equals lid (Prims.fst x))) env.modules)))


let resolve_module_name : env  ->  FStar_Ident.lident  ->  Prims.bool  ->  FStar_Ident.lident Prims.option = (fun env lid honor_ns -> (

let nslen = (FStar_List.length lid.FStar_Ident.ns)
in (

let rec aux = (fun _65_6 -> (match (_65_6) with
| [] -> begin
if (module_is_defined env lid) then begin
Some (lid)
end else begin
None
end
end
| (Open_module_or_namespace (ns, Open_namespace))::q when honor_ns -> begin
(

let new_lid = (let _163_327 = (let _163_326 = (FStar_Ident.path_of_lid ns)
in (let _163_325 = (FStar_Ident.path_of_lid lid)
in (FStar_List.append _163_326 _163_325)))
in (FStar_Ident.lid_of_path _163_327 (FStar_Ident.range_of_lid lid)))
in if (module_is_defined env new_lid) then begin
Some (new_lid)
end else begin
(aux q)
end)
end
| (Module_abbrev (name, modul))::_65_259 when ((nslen = (Prims.parse_int "0")) && (name.FStar_Ident.idText = lid.FStar_Ident.ident.FStar_Ident.idText)) -> begin
Some (modul)
end
| (_65_267)::q -> begin
(aux q)
end))
in (aux env.scope_mods))))


let resolve_in_open_namespaces'' = (fun env lid k_local_binding k_rec_binding k_record f_module l_default -> (match (lid.FStar_Ident.ns) with
| (_65_280)::_65_278 -> begin
(match ((let _163_357 = (let _163_356 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in (FStar_Ident.set_lid_range _163_356 (FStar_Ident.range_of_lid lid)))
in (resolve_module_name env _163_357 true))) with
| None -> begin
None
end
| Some (modul) -> begin
(

let lid' = (qual modul lid.FStar_Ident.ident)
in (let _163_359 = (f_module Cont_fail lid')
in (option_of_cont (fun _65_286 -> None) _163_359)))
end)
end
| [] -> begin
(try_lookup_id'' env lid.FStar_Ident.ident k_local_binding k_rec_binding k_record (f_module Cont_ignore) l_default)
end))


let cont_of_option = (fun k_none _65_7 -> (match (_65_7) with
| Some (v) -> begin
Cont_ok (v)
end
| None -> begin
k_none
end))


let resolve_in_open_namespaces' = (fun env lid k_local_binding k_rec_binding k_global_def -> (

let k_global_def' = (fun k lid def -> (let _163_385 = (k_global_def lid def)
in (cont_of_option k _163_385)))
in (

let f_module = (fun k lid' -> (find_in_module env lid' (k_global_def' k) k))
in (

let l_default = (fun k i -> (lookup_default_id env i (k_global_def' k) k))
in (resolve_in_open_namespaces'' env lid (fun l -> (let _163_395 = (k_local_binding l)
in (cont_of_option Cont_fail _163_395))) (fun r -> (let _163_397 = (k_rec_binding r)
in (cont_of_option Cont_fail _163_397))) (fun _65_311 -> Cont_ignore) f_module l_default)))))


let fv_qual_of_se : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.fv_qual Prims.option = (fun _65_9 -> (match (_65_9) with
| FStar_Syntax_Syntax.Sig_datacon (_65_317, _65_319, _65_321, l, _65_324, quals, _65_327, _65_329) -> begin
(

let qopt = (FStar_Util.find_map quals (fun _65_8 -> (match (_65_8) with
| FStar_Syntax_Syntax.RecordConstructor (_65_334, fs) -> begin
Some (FStar_Syntax_Syntax.Record_ctor (((l), (fs))))
end
| _65_339 -> begin
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
| FStar_Syntax_Syntax.Sig_declare_typ (_65_344, _65_346, _65_348, quals, _65_351) -> begin
None
end
| _65_355 -> begin
None
end))


let lb_fv : FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.fv = (fun lbs lid -> (let _163_407 = (FStar_Util.find_map lbs (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in if (FStar_Syntax_Syntax.fv_eq_lid fv lid) then begin
Some (fv)
end else begin
None
end)))
in (FStar_All.pipe_right _163_407 FStar_Util.must)))


let ns_of_lid_equals : FStar_Ident.lident  ->  FStar_Ident.lident  ->  Prims.bool = (fun lid ns -> (((FStar_List.length lid.FStar_Ident.ns) = (FStar_List.length (FStar_Ident.ids_of_lid ns))) && (let _163_412 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in (FStar_Ident.lid_equals _163_412 ns))))


let try_lookup_name : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  foundname Prims.option = (fun any_val exclude_interf env lid -> (

let occurrence_range = (FStar_Ident.range_of_lid lid)
in (

let k_global_def = (fun source_lid _65_13 -> (match (_65_13) with
| (_65_371, true) when exclude_interf -> begin
None
end
| (se, _65_376) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_65_379) -> begin
(let _163_427 = (let _163_426 = (let _163_425 = (FStar_Syntax_Syntax.fvar source_lid FStar_Syntax_Syntax.Delta_constant None)
in ((_163_425), (false)))
in Term_name (_163_426))
in Some (_163_427))
end
| FStar_Syntax_Syntax.Sig_datacon (_65_382) -> begin
(let _163_431 = (let _163_430 = (let _163_429 = (let _163_428 = (fv_qual_of_se se)
in (FStar_Syntax_Syntax.fvar source_lid FStar_Syntax_Syntax.Delta_constant _163_428))
in ((_163_429), (false)))
in Term_name (_163_430))
in Some (_163_431))
end
| FStar_Syntax_Syntax.Sig_let ((_65_385, lbs), _65_389, _65_391, _65_393, _65_395) -> begin
(

let fv = (lb_fv lbs source_lid)
in (let _163_434 = (let _163_433 = (let _163_432 = (FStar_Syntax_Syntax.fvar source_lid fv.FStar_Syntax_Syntax.fv_delta fv.FStar_Syntax_Syntax.fv_qual)
in ((_163_432), (false)))
in Term_name (_163_433))
in Some (_163_434)))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _65_401, _65_403, quals, _65_406) -> begin
if (any_val || (FStar_All.pipe_right quals (FStar_Util.for_some (fun _65_10 -> (match (_65_10) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| _65_412 -> begin
false
end))))) then begin
(

let lid = (FStar_Ident.set_lid_range lid (FStar_Ident.range_of_lid source_lid))
in (

let dd = if ((FStar_Syntax_Util.is_primop_lid lid) || ((ns_of_lid_equals lid FStar_Syntax_Const.prims_lid) && (FStar_All.pipe_right quals (FStar_Util.for_some (fun _65_11 -> (match (_65_11) with
| (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) -> begin
true
end
| _65_422 -> begin
false
end)))))) then begin
FStar_Syntax_Syntax.Delta_equational
end else begin
FStar_Syntax_Syntax.Delta_constant
end
in (match ((FStar_Util.find_map quals (fun _65_12 -> (match (_65_12) with
| FStar_Syntax_Syntax.Reflectable (refl_monad) -> begin
Some (refl_monad)
end
| _65_428 -> begin
None
end)))) with
| Some (refl_monad) -> begin
(

let refl_const = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (refl_monad))) None occurrence_range)
in Some (Term_name (((refl_const), (false)))))
end
| _65_433 -> begin
(let _163_441 = (let _163_440 = (let _163_439 = (let _163_438 = (fv_qual_of_se se)
in (FStar_Syntax_Syntax.fvar lid dd _163_438))
in ((_163_439), (false)))
in Term_name (_163_440))
in Some (_163_441))
end)))
end else begin
None
end
end
| (FStar_Syntax_Syntax.Sig_new_effect_for_free (ne, _)) | (FStar_Syntax_Syntax.Sig_new_effect (ne, _)) -> begin
Some (Eff_name (((se), ((FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname (FStar_Ident.range_of_lid source_lid))))))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (_65_444) -> begin
Some (Eff_name (((se), (source_lid))))
end
| _65_447 -> begin
None
end)
end))
in (

let k_local_binding = (fun r -> (let _163_445 = (let _163_444 = (found_local_binding (FStar_Ident.range_of_lid lid) r)
in Term_name (_163_444))
in Some (_163_445)))
in (

let k_rec_binding = (fun _65_454 -> (match (_65_454) with
| (id, l, dd) -> begin
(let _163_450 = (let _163_449 = (let _163_448 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range l (FStar_Ident.range_of_lid lid)) dd None)
in ((_163_448), (false)))
in Term_name (_163_449))
in Some (_163_450))
end))
in (

let found_unmangled = (match (lid.FStar_Ident.ns) with
| [] -> begin
(match ((unmangleOpName lid.FStar_Ident.ident)) with
| Some (f) -> begin
Some (Term_name (f))
end
| _65_459 -> begin
None
end)
end
| _65_461 -> begin
None
end)
in (match (found_unmangled) with
| None -> begin
(resolve_in_open_namespaces' env lid k_local_binding k_rec_binding k_global_def)
end
| x -> begin
x
end)))))))


let try_lookup_effect_name' : Prims.bool  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident) Prims.option = (fun exclude_interf env lid -> (match ((try_lookup_name true exclude_interf env lid)) with
| Some (Eff_name (o, l)) -> begin
Some (((o), (l)))
end
| _65_474 -> begin
None
end))


let try_lookup_effect_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env l -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some (o, l) -> begin
Some (l)
end
| _65_482 -> begin
None
end))


let try_lookup_effect_name_and_attributes : env  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.cflags Prims.list) Prims.option = (fun env l -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some (FStar_Syntax_Syntax.Sig_new_effect (ne, _65_487), l) -> begin
Some (((l), (ne.FStar_Syntax_Syntax.cattributes)))
end
| Some (FStar_Syntax_Syntax.Sig_new_effect_for_free (ne, _65_495), l) -> begin
Some (((l), (ne.FStar_Syntax_Syntax.cattributes)))
end
| Some (FStar_Syntax_Syntax.Sig_effect_abbrev (_65_502, _65_504, _65_506, _65_508, _65_510, cattributes, _65_513), l) -> begin
Some (((l), (cattributes)))
end
| _65_520 -> begin
None
end))


let try_lookup_effect_defn : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl Prims.option = (fun env l -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some (FStar_Syntax_Syntax.Sig_new_effect (ne, _65_525), _65_529) -> begin
Some (ne)
end
| Some (FStar_Syntax_Syntax.Sig_new_effect_for_free (ne, _65_534), _65_538) -> begin
Some (ne)
end
| _65_542 -> begin
None
end))


let is_effect_name : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((try_lookup_effect_name env lid)) with
| None -> begin
false
end
| Some (_65_547) -> begin
true
end))


let lookup_letbinding_quals : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.qualifier Prims.list = (fun env lid -> (

let k_global_def = (fun lid _65_14 -> (match (_65_14) with
| (FStar_Syntax_Syntax.Sig_declare_typ (lid, _65_556, _65_558, quals, _65_561), _65_565) -> begin
Some (quals)
end
| _65_568 -> begin
None
end))
in (match ((resolve_in_open_namespaces' env lid (fun _65_571 -> None) (fun _65_569 -> None) k_global_def)) with
| Some (quals) -> begin
quals
end
| _65_576 -> begin
[]
end)))


let try_lookup_module : env  ->  Prims.string Prims.list  ->  FStar_Syntax_Syntax.modul Prims.option = (fun env path -> (match ((FStar_List.tryFind (fun _65_581 -> (match (_65_581) with
| (mlid, modul) -> begin
((FStar_Ident.path_of_lid mlid) = path)
end)) env.modules)) with
| Some (_65_583, modul) -> begin
Some (modul)
end
| None -> begin
None
end))


let try_lookup_let : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env lid -> (

let k_global_def = (fun lid _65_15 -> (match (_65_15) with
| (FStar_Syntax_Syntax.Sig_let ((_65_594, lbs), _65_598, _65_600, _65_602, _65_604), _65_608) -> begin
(

let fv = (lb_fv lbs lid)
in (let _163_496 = (FStar_Syntax_Syntax.fvar lid fv.FStar_Syntax_Syntax.fv_delta fv.FStar_Syntax_Syntax.fv_qual)
in Some (_163_496)))
end
| _65_612 -> begin
None
end))
in (resolve_in_open_namespaces' env lid (fun _65_615 -> None) (fun _65_613 -> None) k_global_def)))


let try_lookup_definition : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env lid -> (

let k_global_def = (fun lid _65_16 -> (match (_65_16) with
| (FStar_Syntax_Syntax.Sig_let (lbs, _65_624, _65_626, _65_628, _65_630), _65_634) -> begin
(FStar_Util.find_map (Prims.snd lbs) (fun lb -> (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv lid) -> begin
Some (lb.FStar_Syntax_Syntax.lbdef)
end
| _65_640 -> begin
None
end)))
end
| _65_642 -> begin
None
end))
in (resolve_in_open_namespaces' env lid (fun _65_645 -> None) (fun _65_643 -> None) k_global_def)))


let try_lookup_lid' : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term * Prims.bool) Prims.option = (fun any_val exclude_interf env lid -> (match ((try_lookup_name any_val exclude_interf env lid)) with
| Some (Term_name (e, mut)) -> begin
Some (((e), (mut)))
end
| _65_657 -> begin
None
end))


let try_lookup_lid : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term * Prims.bool) Prims.option = (fun env l -> (try_lookup_lid' env.iface false env l))


let try_lookup_datacon : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.fv Prims.option = (fun env lid -> (

let k_global_def = (fun lid _65_18 -> (match (_65_18) with
| (FStar_Syntax_Syntax.Sig_declare_typ (_65_666, _65_668, _65_670, quals, _65_673), _65_677) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _65_17 -> (match (_65_17) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| _65_682 -> begin
false
end)))) then begin
(let _163_531 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant None)
in Some (_163_531))
end else begin
None
end
end
| (FStar_Syntax_Syntax.Sig_datacon (_65_684), _65_687) -> begin
(let _163_532 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in Some (_163_532))
end
| _65_690 -> begin
None
end))
in (resolve_in_open_namespaces' env lid (fun _65_693 -> None) (fun _65_691 -> None) k_global_def)))


let find_all_datacons : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.list Prims.option = (fun env lid -> (

let k_global_def = (fun lid _65_19 -> (match (_65_19) with
| (FStar_Syntax_Syntax.Sig_inductive_typ (_65_701, _65_703, _65_705, _65_707, _65_709, datas, _65_712, _65_714), _65_718) -> begin
Some (datas)
end
| _65_721 -> begin
None
end))
in (resolve_in_open_namespaces' env lid (fun _65_724 -> None) (fun _65_722 -> None) k_global_def)))


let record_cache_aux_with_filter : (((Prims.unit  ->  Prims.unit) * (Prims.unit  ->  Prims.unit) * (Prims.unit  ->  record_or_dc Prims.list) * (record_or_dc  ->  Prims.unit) * (Prims.unit  ->  Prims.unit)) * (Prims.unit  ->  Prims.unit)) = (

let record_cache = (FStar_Util.mk_ref (([])::[]))
in (

let push = (fun _65_728 -> (match (()) with
| () -> begin
(let _163_567 = (let _163_566 = (let _163_564 = (FStar_ST.read record_cache)
in (FStar_List.hd _163_564))
in (let _163_565 = (FStar_ST.read record_cache)
in (_163_566)::_163_565))
in (FStar_ST.op_Colon_Equals record_cache _163_567))
end))
in (

let pop = (fun _65_730 -> (match (()) with
| () -> begin
(let _163_571 = (let _163_570 = (FStar_ST.read record_cache)
in (FStar_List.tl _163_570))
in (FStar_ST.op_Colon_Equals record_cache _163_571))
end))
in (

let peek = (fun _65_732 -> (match (()) with
| () -> begin
(let _163_574 = (FStar_ST.read record_cache)
in (FStar_List.hd _163_574))
end))
in (

let insert = (fun r -> (let _163_581 = (let _163_580 = (let _163_577 = (peek ())
in (r)::_163_577)
in (let _163_579 = (let _163_578 = (FStar_ST.read record_cache)
in (FStar_List.tl _163_578))
in (_163_580)::_163_579))
in (FStar_ST.op_Colon_Equals record_cache _163_581)))
in (

let commit = (fun _65_736 -> (match (()) with
| () -> begin
(match ((FStar_ST.read record_cache)) with
| (hd)::(_65_739)::tl -> begin
(FStar_ST.op_Colon_Equals record_cache ((hd)::tl))
end
| _65_744 -> begin
(FStar_All.failwith "Impossible")
end)
end))
in (

let filter = (fun _65_746 -> (match (()) with
| () -> begin
(

let rc = (peek ())
in (

let _65_748 = (pop ())
in (match (()) with
| () -> begin
(

let filtered = (FStar_List.filter (fun r -> (not (r.is_private_or_abstract))) rc)
in (let _163_588 = (let _163_587 = (FStar_ST.read record_cache)
in (filtered)::_163_587)
in (FStar_ST.op_Colon_Equals record_cache _163_588)))
end)))
end))
in (

let aux = ((push), (pop), (peek), (insert), (commit))
in ((aux), (filter))))))))))


let record_cache_aux : ((Prims.unit  ->  Prims.unit) * (Prims.unit  ->  Prims.unit) * (Prims.unit  ->  record_or_dc Prims.list) * (record_or_dc  ->  Prims.unit) * (Prims.unit  ->  Prims.unit)) = (

let _65_755 = record_cache_aux_with_filter
in (match (_65_755) with
| (aux, _65_754) -> begin
aux
end))


let filter_record_cache : Prims.unit  ->  Prims.unit = (

let _65_759 = record_cache_aux_with_filter
in (match (_65_759) with
| (_65_757, filter) -> begin
filter
end))


let push_record_cache : Prims.unit  ->  Prims.unit = (

let _65_769 = record_cache_aux
in (match (_65_769) with
| (push, _65_762, _65_764, _65_766, _65_768) -> begin
push
end))


let pop_record_cache : Prims.unit  ->  Prims.unit = (

let _65_779 = record_cache_aux
in (match (_65_779) with
| (_65_771, pop, _65_774, _65_776, _65_778) -> begin
pop
end))


let peek_record_cache : Prims.unit  ->  record_or_dc Prims.list = (

let _65_789 = record_cache_aux
in (match (_65_789) with
| (_65_781, _65_783, peek, _65_786, _65_788) -> begin
peek
end))


let insert_record_cache : record_or_dc  ->  Prims.unit = (

let _65_799 = record_cache_aux
in (match (_65_799) with
| (_65_791, _65_793, _65_795, insert, _65_798) -> begin
insert
end))


let commit_record_cache : Prims.unit  ->  Prims.unit = (

let _65_809 = record_cache_aux
in (match (_65_809) with
| (_65_801, _65_803, _65_805, _65_807, commit) -> begin
commit
end))


let extract_record : env  ->  scope_mod Prims.list FStar_ST.ref  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun e new_globs _65_23 -> (match (_65_23) with
| FStar_Syntax_Syntax.Sig_bundle (sigs, _65_815, _65_817, _65_819) -> begin
(

let is_rec = (FStar_Util.for_some (fun _65_20 -> (match (_65_20) with
| (FStar_Syntax_Syntax.RecordType (_)) | (FStar_Syntax_Syntax.RecordConstructor (_)) -> begin
true
end
| _65_830 -> begin
false
end)))
in (

let find_dc = (fun dc -> (FStar_All.pipe_right sigs (FStar_Util.find_opt (fun _65_21 -> (match (_65_21) with
| FStar_Syntax_Syntax.Sig_datacon (lid, _65_837, _65_839, _65_841, _65_843, _65_845, _65_847, _65_849) -> begin
(FStar_Ident.lid_equals dc lid)
end
| _65_853 -> begin
false
end)))))
in (FStar_All.pipe_right sigs (FStar_List.iter (fun _65_22 -> (match (_65_22) with
| FStar_Syntax_Syntax.Sig_inductive_typ (typename, univs, parms, _65_859, _65_861, (dc)::[], tags, _65_866) -> begin
(match ((let _163_790 = (find_dc dc)
in (FStar_All.pipe_left FStar_Util.must _163_790))) with
| FStar_Syntax_Syntax.Sig_datacon (constrname, _65_871, t, _65_874, _65_876, _65_878, _65_880, _65_882) -> begin
(

let _65_888 = (FStar_Syntax_Util.arrow_formals t)
in (match (_65_888) with
| (formals, _65_887) -> begin
(

let is_rec = (is_rec tags)
in (

let fields = (FStar_All.pipe_right formals (FStar_List.collect (fun _65_892 -> (match (_65_892) with
| (x, q) -> begin
if ((FStar_Syntax_Syntax.is_null_bv x) || (is_rec && (FStar_Syntax_Syntax.is_implicit q))) then begin
[]
end else begin
(let _163_793 = (let _163_792 = if is_rec then begin
(FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname)
end else begin
x.FStar_Syntax_Syntax.ppname
end
in ((_163_792), (x.FStar_Syntax_Syntax.sort)))
in (_163_793)::[])
end
end))))
in (

let record = {typename = typename; constrname = constrname.FStar_Ident.ident; parms = parms; fields = fields; is_private_or_abstract = ((FStar_List.contains FStar_Syntax_Syntax.Private tags) || (FStar_List.contains FStar_Syntax_Syntax.Abstract tags)); is_record = is_rec}
in (

let _65_895 = (let _163_795 = (let _163_794 = (FStar_ST.read new_globs)
in (Record_or_dc (record))::_163_794)
in (FStar_ST.op_Colon_Equals new_globs _163_795))
in (match (()) with
| () -> begin
(insert_record_cache record)
end)))))
end))
end
| _65_897 -> begin
()
end)
end
| _65_899 -> begin
()
end))))))
end
| _65_901 -> begin
()
end))


let try_lookup_record_or_dc_by_field_name : env  ->  FStar_Ident.lident  ->  record_or_dc Prims.option = (fun env fieldname -> (

let find_in_cache = (fun fieldname -> (

let _65_908 = ((fieldname.FStar_Ident.ns), (fieldname.FStar_Ident.ident))
in (match (_65_908) with
| (ns, id) -> begin
(let _163_806 = (peek_record_cache ())
in (FStar_Util.find_map _163_806 (fun record -> (let _163_805 = (find_in_record ns id record (fun r -> Cont_ok (r)))
in (option_of_cont (fun _65_911 -> None) _163_805)))))
end)))
in (resolve_in_open_namespaces'' env fieldname (fun _65_921 -> Cont_ignore) (fun _65_919 -> Cont_ignore) (fun r -> Cont_ok (r)) (fun k fn -> (let _163_812 = (find_in_cache fn)
in (cont_of_option k _163_812))) (fun k _65_914 -> k))))


let try_lookup_record_by_field_name : env  ->  FStar_Ident.lident  ->  record_or_dc Prims.option = (fun env fieldname -> (match ((try_lookup_record_or_dc_by_field_name env fieldname)) with
| Some (r) when r.is_record -> begin
Some (r)
end
| _65_928 -> begin
None
end))


let belongs_to_record : env  ->  FStar_Ident.lident  ->  record_or_dc  ->  Prims.bool = (fun env lid record -> (match ((try_lookup_record_by_field_name env lid)) with
| Some (record') when ((let _163_825 = (FStar_Ident.path_of_ns record.typename.FStar_Ident.ns)
in (FStar_Ident.text_of_path _163_825)) = (let _163_826 = (FStar_Ident.path_of_ns record'.typename.FStar_Ident.ns)
in (FStar_Ident.text_of_path _163_826))) -> begin
(match ((find_in_record record.typename.FStar_Ident.ns lid.FStar_Ident.ident record (fun _65_934 -> Cont_ok (())))) with
| Cont_ok (_65_937) -> begin
true
end
| _65_940 -> begin
false
end)
end
| _65_942 -> begin
false
end))


let try_lookup_dc_by_field_name : env  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * Prims.bool) Prims.option = (fun env fieldname -> (match ((try_lookup_record_or_dc_by_field_name env fieldname)) with
| Some (r) -> begin
(let _163_834 = (let _163_833 = (let _163_832 = (FStar_Ident.lid_of_ids (FStar_List.append r.typename.FStar_Ident.ns ((r.constrname)::[])))
in (FStar_Ident.set_lid_range _163_832 (FStar_Ident.range_of_lid fieldname)))
in ((_163_833), (r.is_record)))
in Some (_163_834))
end
| _65_948 -> begin
None
end))


let unique : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  Prims.bool = (fun any_val exclude_if env lid -> (

let this_env = (

let _65_953 = env
in {curmodule = _65_953.curmodule; curmonad = _65_953.curmonad; modules = _65_953.modules; scope_mods = []; sigaccum = _65_953.sigaccum; sigmap = _65_953.sigmap; default_result_effect = _65_953.default_result_effect; iface = _65_953.iface; admitted_iface = _65_953.admitted_iface; expect_typ = _65_953.expect_typ})
in (match ((try_lookup_lid' any_val exclude_if env lid)) with
| None -> begin
true
end
| Some (_65_958) -> begin
false
end)))


let push_scope_mod : env  ->  scope_mod  ->  env = (fun env scope_mod -> (

let _65_962 = env
in {curmodule = _65_962.curmodule; curmonad = _65_962.curmonad; modules = _65_962.modules; scope_mods = (scope_mod)::env.scope_mods; sigaccum = _65_962.sigaccum; sigmap = _65_962.sigmap; default_result_effect = _65_962.default_result_effect; iface = _65_962.iface; admitted_iface = _65_962.admitted_iface; expect_typ = _65_962.expect_typ}))


let push_bv' : env  ->  FStar_Ident.ident  ->  Prims.bool  ->  (env * FStar_Syntax_Syntax.bv) = (fun env x is_mutable -> (

let bv = (FStar_Syntax_Syntax.gen_bv x.FStar_Ident.idText (Some (x.FStar_Ident.idRange)) FStar_Syntax_Syntax.tun)
in (((push_scope_mod env (Local_binding (((x), (bv), (is_mutable)))))), (bv))))


let push_bv_mutable : env  ->  FStar_Ident.ident  ->  (env * FStar_Syntax_Syntax.bv) = (fun env x -> (push_bv' env x true))


let push_bv : env  ->  FStar_Ident.ident  ->  (env * FStar_Syntax_Syntax.bv) = (fun env x -> (push_bv' env x false))


let push_top_level_rec_binding : env  ->  FStar_Ident.ident  ->  FStar_Syntax_Syntax.delta_depth  ->  env = (fun env x dd -> (

let l = (qualify env x)
in if (unique false true env l) then begin
(push_scope_mod env (Rec_binding (((x), (l), (dd)))))
end else begin
(Prims.raise (FStar_Syntax_Syntax.Error ((((Prims.strcat "Duplicate top-level names " l.FStar_Ident.str)), ((FStar_Ident.range_of_lid l))))))
end))


let push_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env s -> (

let err = (fun l -> (

let sopt = (FStar_Util.smap_try_find (sigmap env) l.FStar_Ident.str)
in (

let r = (match (sopt) with
| Some (se, _65_983) -> begin
(match ((FStar_Util.find_opt (FStar_Ident.lid_equals l) (FStar_Syntax_Util.lids_of_sigelt se))) with
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
in (let _163_875 = (let _163_874 = (let _163_873 = (FStar_Util.format2 "Duplicate top-level names [%s]; previously declared at %s" (FStar_Ident.text_of_lid l) r)
in ((_163_873), ((FStar_Ident.range_of_lid l))))
in FStar_Syntax_Syntax.Error (_163_874))
in (Prims.raise _163_875)))))
in (

let globals = (FStar_ST.alloc env.scope_mods)
in (

let env = (

let _65_1002 = (match (s) with
| FStar_Syntax_Syntax.Sig_let (_65_993) -> begin
((false), (true))
end
| FStar_Syntax_Syntax.Sig_bundle (_65_996) -> begin
((true), (true))
end
| _65_999 -> begin
((false), (false))
end)
in (match (_65_1002) with
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

let _65_1006 = (extract_record env globals s)
in (

let _65_1008 = env
in {curmodule = _65_1008.curmodule; curmonad = _65_1008.curmonad; modules = _65_1008.modules; scope_mods = _65_1008.scope_mods; sigaccum = (s)::env.sigaccum; sigmap = _65_1008.sigmap; default_result_effect = _65_1008.default_result_effect; iface = _65_1008.iface; admitted_iface = _65_1008.admitted_iface; expect_typ = _65_1008.expect_typ}))
end
| Some (l) -> begin
(err l)
end))
end))
in (

let env = (

let _65_1013 = env
in (let _163_877 = (FStar_ST.read globals)
in {curmodule = _65_1013.curmodule; curmonad = _65_1013.curmonad; modules = _65_1013.modules; scope_mods = _163_877; sigaccum = _65_1013.sigaccum; sigmap = _65_1013.sigmap; default_result_effect = _65_1013.default_result_effect; iface = _65_1013.iface; admitted_iface = _65_1013.admitted_iface; expect_typ = _65_1013.expect_typ}))
in (

let _65_1030 = (match (s) with
| FStar_Syntax_Syntax.Sig_bundle (ses, _65_1018, _65_1020, _65_1022) -> begin
(let _163_879 = (FStar_List.map (fun se -> (((FStar_Syntax_Util.lids_of_sigelt se)), (se))) ses)
in ((env), (_163_879)))
end
| _65_1027 -> begin
((env), (((((FStar_Syntax_Util.lids_of_sigelt s)), (s)))::[]))
end)
in (match (_65_1030) with
| (env, lss) -> begin
(

let _65_1036 = (FStar_All.pipe_right lss (FStar_List.iter (fun _65_1033 -> (match (_65_1033) with
| (lids, se) -> begin
(FStar_All.pipe_right lids (FStar_List.iter (fun lid -> (

let _65_1035 = (let _163_883 = (let _163_882 = (FStar_ST.read globals)
in (Top_level_def (lid.FStar_Ident.ident))::_163_882)
in (FStar_ST.op_Colon_Equals globals _163_883))
in (match (()) with
| () -> begin
(FStar_Util.smap_add (sigmap env) lid.FStar_Ident.str ((se), ((env.iface && (not (env.admitted_iface))))))
end)))))
end))))
in (

let env = (

let _65_1038 = env
in (let _163_884 = (FStar_ST.read globals)
in {curmodule = _65_1038.curmodule; curmonad = _65_1038.curmonad; modules = _65_1038.modules; scope_mods = _163_884; sigaccum = _65_1038.sigaccum; sigmap = _65_1038.sigmap; default_result_effect = _65_1038.default_result_effect; iface = _65_1038.iface; admitted_iface = _65_1038.admitted_iface; expect_typ = _65_1038.expect_typ}))
in env))
end)))))))


let push_namespace : env  ->  FStar_Ident.lident  ->  env = (fun env ns -> (

let _65_1053 = (match ((resolve_module_name env ns false)) with
| None -> begin
(

let modules = env.modules
in if (FStar_All.pipe_right modules (FStar_Util.for_some (fun _65_1048 -> (match (_65_1048) with
| (m, _65_1047) -> begin
(FStar_Util.starts_with (Prims.strcat (FStar_Ident.text_of_lid m) ".") (Prims.strcat (FStar_Ident.text_of_lid ns) "."))
end)))) then begin
((ns), (Open_namespace))
end else begin
(let _163_892 = (let _163_891 = (let _163_890 = (FStar_Util.format1 "Namespace %s cannot be found" (FStar_Ident.text_of_lid ns))
in ((_163_890), ((FStar_Ident.range_of_lid ns))))
in FStar_Syntax_Syntax.Error (_163_891))
in (Prims.raise _163_892))
end)
end
| Some (ns') -> begin
((ns'), (Open_module))
end)
in (match (_65_1053) with
| (ns', kd) -> begin
(push_scope_mod env (Open_module_or_namespace (((ns'), (kd)))))
end)))


let push_module_abbrev : env  ->  FStar_Ident.ident  ->  FStar_Ident.lident  ->  env = (fun env x l -> if (module_is_defined env l) then begin
(push_scope_mod env (Module_abbrev (((x), (l)))))
end else begin
(let _163_901 = (let _163_900 = (let _163_899 = (FStar_Util.format1 "Module %s cannot be found" (FStar_Ident.text_of_lid l))
in ((_163_899), ((FStar_Ident.range_of_lid l))))
in FStar_Syntax_Syntax.Error (_163_900))
in (Prims.raise _163_901))
end)


let check_admits : env  ->  Prims.unit = (fun env -> (FStar_All.pipe_right env.sigaccum (FStar_List.iter (fun se -> (match (se) with
| FStar_Syntax_Syntax.Sig_declare_typ (l, u, t, quals, r) -> begin
(match ((try_lookup_lid env l)) with
| None -> begin
(

let _65_1067 = (let _163_907 = (let _163_906 = (FStar_Range.string_of_range (FStar_Ident.range_of_lid l))
in (let _163_905 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format2 "%s: Warning: Admitting %s without a definition\n" _163_906 _163_905)))
in (FStar_Util.print_string _163_907))
in (FStar_Util.smap_add (sigmap env) l.FStar_Ident.str ((FStar_Syntax_Syntax.Sig_declare_typ (((l), (u), (t), ((FStar_Syntax_Syntax.Assumption)::quals), (r)))), (false))))
end
| Some (_65_1070) -> begin
()
end)
end
| _65_1073 -> begin
()
end)))))


let finish : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env modul -> (

let _65_1135 = (FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations (FStar_List.iter (fun _65_25 -> (match (_65_25) with
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _65_1080, _65_1082) -> begin
if ((FStar_List.contains FStar_Syntax_Syntax.Private quals) || (FStar_List.contains FStar_Syntax_Syntax.Abstract quals)) then begin
(FStar_All.pipe_right ses (FStar_List.iter (fun _65_24 -> (match (_65_24) with
| FStar_Syntax_Syntax.Sig_datacon (lid, _65_1088, _65_1090, _65_1092, _65_1094, _65_1096, _65_1098, _65_1100) -> begin
(FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str)
end
| _65_1104 -> begin
()
end))))
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _65_1107, _65_1109, quals, _65_1112) -> begin
if (FStar_List.contains FStar_Syntax_Syntax.Private quals) then begin
(FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str)
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_let ((_65_1116, lbs), r, _65_1121, quals, _65_1124) -> begin
(

let _65_1128 = if ((FStar_List.contains FStar_Syntax_Syntax.Private quals) || (FStar_List.contains FStar_Syntax_Syntax.Abstract quals)) then begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (let _163_918 = (let _163_917 = (let _163_916 = (let _163_915 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _163_915.FStar_Syntax_Syntax.fv_name)
in _163_916.FStar_Syntax_Syntax.v)
in _163_917.FStar_Ident.str)
in (FStar_Util.smap_remove (sigmap env) _163_918)))))
end else begin
()
end
in if ((FStar_List.contains FStar_Syntax_Syntax.Abstract quals) && (not ((FStar_List.contains FStar_Syntax_Syntax.Private quals)))) then begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (

let lid = (let _163_921 = (let _163_920 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _163_920.FStar_Syntax_Syntax.fv_name)
in _163_921.FStar_Syntax_Syntax.v)
in (

let decl = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), ((FStar_Syntax_Syntax.Assumption)::quals), (r)))
in (FStar_Util.smap_add (sigmap env) lid.FStar_Ident.str ((decl), (false))))))))
end else begin
()
end)
end
| _65_1134 -> begin
()
end))))
in (

let _65_1137 = (filter_record_cache ())
in (match (()) with
| () -> begin
(

let _65_1138 = env
in {curmodule = None; curmonad = _65_1138.curmonad; modules = (((modul.FStar_Syntax_Syntax.name), (modul)))::env.modules; scope_mods = []; sigaccum = []; sigmap = _65_1138.sigmap; default_result_effect = _65_1138.default_result_effect; iface = _65_1138.iface; admitted_iface = _65_1138.admitted_iface; expect_typ = _65_1138.expect_typ})
end))))


type env_stack_ops =
{push : env  ->  env; mark : env  ->  env; reset_mark : env  ->  env; commit_mark : env  ->  env; pop : env  ->  env}


let is_Mkenv_stack_ops : env_stack_ops  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv_stack_ops"))))


let stack_ops : env_stack_ops = (

let stack = (FStar_Util.mk_ref [])
in (

let push = (fun env -> (

let _65_1149 = (push_record_cache ())
in (

let _65_1151 = (let _163_971 = (let _163_970 = (FStar_ST.read stack)
in (env)::_163_970)
in (FStar_ST.op_Colon_Equals stack _163_971))
in (

let _65_1153 = env
in (let _163_972 = (FStar_Util.smap_copy (sigmap env))
in {curmodule = _65_1153.curmodule; curmonad = _65_1153.curmonad; modules = _65_1153.modules; scope_mods = _65_1153.scope_mods; sigaccum = _65_1153.sigaccum; sigmap = _163_972; default_result_effect = _65_1153.default_result_effect; iface = _65_1153.iface; admitted_iface = _65_1153.admitted_iface; expect_typ = _65_1153.expect_typ})))))
in (

let pop = (fun env -> (match ((FStar_ST.read stack)) with
| (env)::tl -> begin
(

let _65_1160 = (pop_record_cache ())
in (

let _65_1162 = (FStar_ST.op_Colon_Equals stack tl)
in env))
end
| _65_1165 -> begin
(FStar_All.failwith "Impossible: Too many pops")
end))
in (

let commit_mark = (fun env -> (

let _65_1168 = (commit_record_cache ())
in (match ((FStar_ST.read stack)) with
| (_65_1172)::tl -> begin
(

let _65_1174 = (FStar_ST.op_Colon_Equals stack tl)
in env)
end
| _65_1177 -> begin
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
| (l)::_65_1188 -> begin
(l.FStar_Ident.nsstr = m.FStar_Ident.str)
end
| _65_1192 -> begin
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

let _65_1216 = (FStar_All.pipe_right keys (FStar_List.iter (fun k -> (match ((FStar_Util.smap_try_find sm' k)) with
| Some (se, true) when (sigelt_in_m se) -> begin
(

let _65_1202 = (FStar_Util.smap_remove sm' k)
in (

let se = (match (se) with
| FStar_Syntax_Syntax.Sig_declare_typ (l, u, t, q, r) -> begin
FStar_Syntax_Syntax.Sig_declare_typ (((l), (u), (t), ((FStar_Syntax_Syntax.Assumption)::q), (r)))
end
| _65_1212 -> begin
se
end)
in (FStar_Util.smap_add sm' k ((se), (false)))))
end
| _65_1215 -> begin
()
end))))
in env)))))))


let finish_module_or_interface : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env modul -> (

let _65_1220 = if (not (modul.FStar_Syntax_Syntax.is_interface)) then begin
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

let _65_1231 = env
in (let _163_1009 = (FStar_List.map (fun lid -> Open_module_or_namespace (((lid), (Open_namespace)))) open_ns)
in {curmodule = Some (mname); curmonad = _65_1231.curmonad; modules = _65_1231.modules; scope_mods = _163_1009; sigaccum = _65_1231.sigaccum; sigmap = env.sigmap; default_result_effect = if ((FStar_Ident.lid_equals mname FStar_Syntax_Const.all_lid) || (has_all_in_scope env)) then begin
FStar_Syntax_Const.effect_ML_lid
end else begin
FStar_Syntax_Const.effect_Tot_lid
end; iface = intf; admitted_iface = admitted; expect_typ = _65_1231.expect_typ})))))
in (match ((FStar_All.pipe_right env.modules (FStar_Util.find_opt (fun _65_1237 -> (match (_65_1237) with
| (l, _65_1236) -> begin
(FStar_Ident.lid_equals l mname)
end))))) with
| None -> begin
(let _163_1011 = (prep env)
in ((_163_1011), (false)))
end
| Some (_65_1240, m) -> begin
(

let _65_1244 = if ((not (m.FStar_Syntax_Syntax.is_interface)) || intf) then begin
(let _163_1014 = (let _163_1013 = (let _163_1012 = (FStar_Util.format1 "Duplicate module or interface name: %s" mname.FStar_Ident.str)
in ((_163_1012), ((FStar_Ident.range_of_lid mname))))
in FStar_Syntax_Syntax.Error (_163_1013))
in (Prims.raise _163_1014))
end else begin
()
end
in (let _163_1016 = (let _163_1015 = (push env)
in (prep _163_1015))
in ((_163_1016), (true))))
end)))


let enter_monad_scope : env  ->  FStar_Ident.ident  ->  env = (fun env mname -> (match (env.curmonad) with
| Some (mname') -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((((Prims.strcat "Trying to define monad " (Prims.strcat mname.FStar_Ident.idText (Prims.strcat ", but already in monad scope " mname'.FStar_Ident.idText)))), (mname.FStar_Ident.idRange)))))
end
| None -> begin
(

let _65_1251 = env
in {curmodule = _65_1251.curmodule; curmonad = Some (mname); modules = _65_1251.modules; scope_mods = _65_1251.scope_mods; sigaccum = _65_1251.sigaccum; sigmap = _65_1251.sigmap; default_result_effect = _65_1251.default_result_effect; iface = _65_1251.iface; admitted_iface = _65_1251.admitted_iface; expect_typ = _65_1251.expect_typ})
end))


let fail_or = (fun env lookup lid -> (match ((lookup lid)) with
| None -> begin
(

let opened_modules = (FStar_List.map (fun _65_1260 -> (match (_65_1260) with
| (lid, _65_1259) -> begin
(FStar_Ident.text_of_lid lid)
end)) env.modules)
in (

let msg = (FStar_Util.format1 "Identifier not found: [%s]" (FStar_Ident.text_of_lid lid))
in (

let msg = if ((FStar_List.length lid.FStar_Ident.ns) = (Prims.parse_int "0")) then begin
msg
end else begin
(

let modul = (let _163_1028 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in (FStar_Ident.set_lid_range _163_1028 (FStar_Ident.range_of_lid lid)))
in (match ((resolve_module_name env modul true)) with
| None -> begin
(

let opened_modules = (FStar_String.concat ", " opened_modules)
in (FStar_Util.format3 "%s\nModule %s does not belong to the list of modules in scope, namely %s" msg modul.FStar_Ident.str opened_modules))
end
| Some (modul') when (not ((FStar_List.existsb (fun m -> (m = modul'.FStar_Ident.str)) opened_modules))) -> begin
(

let opened_modules = (FStar_String.concat ", " opened_modules)
in (FStar_Util.format4 "%s\nModule %s resolved into %s, which does not belong to the list of modules in scope, namely %s" msg modul.FStar_Ident.str modul'.FStar_Ident.str opened_modules))
end
| Some (modul') -> begin
(FStar_Util.format4 "%s\nModule %s resolved into %s, definition %s not found" msg modul.FStar_Ident.str modul'.FStar_Ident.str lid.FStar_Ident.ident.FStar_Ident.idText)
end))
end
in (Prims.raise (FStar_Syntax_Syntax.Error (((msg), ((FStar_Ident.range_of_lid lid)))))))))
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




