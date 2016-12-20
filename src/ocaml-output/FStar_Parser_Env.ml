
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
| Local_binding (_64_35) -> begin
_64_35
end))


let ___Rec_binding____0 = (fun projectee -> (match (projectee) with
| Rec_binding (_64_38) -> begin
_64_38
end))


let ___Module_abbrev____0 = (fun projectee -> (match (projectee) with
| Module_abbrev (_64_41) -> begin
_64_41
end))


let ___Open_module_or_namespace____0 = (fun projectee -> (match (projectee) with
| Open_module_or_namespace (_64_44) -> begin
_64_44
end))


let ___Top_level_def____0 = (fun projectee -> (match (projectee) with
| Top_level_def (_64_47) -> begin
_64_47
end))


let ___Record_or_dc____0 = (fun projectee -> (match (projectee) with
| Record_or_dc (_64_50) -> begin
_64_50
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
| Term_name (_64_64) -> begin
_64_64
end))


let ___Eff_name____0 = (fun projectee -> (match (projectee) with
| Eff_name (_64_67) -> begin
_64_67
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
(let _161_175 = (current_module env)
in (qual _161_175 id))
end
| Some (monad) -> begin
(let _161_177 = (let _161_176 = (current_module env)
in (qual _161_176 monad))
in (FStar_Syntax_Util.mk_field_projector_name_from_ident _161_177 id))
end))


let new_sigmap = (fun _64_80 -> (match (()) with
| () -> begin
(FStar_Util.smap_create (Prims.parse_int "100"))
end))


let empty_env : Prims.unit  ->  env = (fun _64_81 -> (match (()) with
| () -> begin
(let _161_181 = (new_sigmap ())
in {curmodule = None; curmonad = None; modules = []; scope_mods = []; sigaccum = []; sigmap = _161_181; default_result_effect = FStar_Syntax_Const.effect_Tot_lid; iface = false; admitted_iface = false; expect_typ = false})
end))


let sigmap : env  ->  (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap = (fun env -> env.sigmap)


let has_all_in_scope : env  ->  Prims.bool = (fun env -> (FStar_List.existsb (fun _64_87 -> (match (_64_87) with
| (m, _64_86) -> begin
(FStar_Ident.lid_equals m FStar_Syntax_Const.all_lid)
end)) env.modules))


let default_total : env  ->  env = (fun env -> (

let _64_89 = env
in {curmodule = _64_89.curmodule; curmonad = _64_89.curmonad; modules = _64_89.modules; scope_mods = _64_89.scope_mods; sigaccum = _64_89.sigaccum; sigmap = _64_89.sigmap; default_result_effect = FStar_Syntax_Const.effect_Tot_lid; iface = _64_89.iface; admitted_iface = _64_89.admitted_iface; expect_typ = _64_89.expect_typ}))


let default_ml : env  ->  env = (fun env -> if (has_all_in_scope env) then begin
(

let _64_92 = env
in {curmodule = _64_92.curmodule; curmonad = _64_92.curmonad; modules = _64_92.modules; scope_mods = _64_92.scope_mods; sigaccum = _64_92.sigaccum; sigmap = _64_92.sigmap; default_result_effect = FStar_Syntax_Const.effect_ML_lid; iface = _64_92.iface; admitted_iface = _64_92.admitted_iface; expect_typ = _64_92.expect_typ})
end else begin
env
end)


let set_bv_range : FStar_Syntax_Syntax.bv  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.bv = (fun bv r -> (

let id = (

let _64_96 = bv.FStar_Syntax_Syntax.ppname
in {FStar_Ident.idText = _64_96.FStar_Ident.idText; FStar_Ident.idRange = r})
in (

let _64_99 = bv
in {FStar_Syntax_Syntax.ppname = id; FStar_Syntax_Syntax.index = _64_99.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _64_99.FStar_Syntax_Syntax.sort})))


let bv_to_name : FStar_Syntax_Syntax.bv  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.term = (fun bv r -> (FStar_Syntax_Syntax.bv_to_name (set_bv_range bv r)))


let unmangleMap : (Prims.string * Prims.string * FStar_Syntax_Syntax.delta_depth * FStar_Syntax_Syntax.fv_qual Prims.option) Prims.list = ((("op_ColonColon"), ("Cons"), (FStar_Syntax_Syntax.Delta_constant), (Some (FStar_Syntax_Syntax.Data_ctor))))::((("not"), ("op_Negation"), (FStar_Syntax_Syntax.Delta_equational), (None)))::[]


let unmangleOpName : FStar_Ident.ident  ->  (FStar_Syntax_Syntax.term * Prims.bool) Prims.option = (fun id -> (

let t = (FStar_Util.find_map unmangleMap (fun _64_108 -> (match (_64_108) with
| (x, y, dd, dq) -> begin
if (id.FStar_Ident.idText = x) then begin
(let _161_203 = (let _161_202 = (FStar_Ident.lid_of_path (("Prims")::(y)::[]) id.FStar_Ident.idRange)
in (FStar_Syntax_Syntax.fvar _161_202 dd dq))
in Some (_161_203))
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
| Cont_ok (_64_116) -> begin
_64_116
end))


let option_of_cont = (fun k_ignore _64_1 -> (match (_64_1) with
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

let find = (FStar_Util.find_map record.fields (fun _64_133 -> (match (_64_133) with
| (f, _64_132) -> begin
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

let check_local_binding_id = (fun _64_2 -> (match (_64_2) with
| (id', _64_149, _64_151) -> begin
(id'.FStar_Ident.idText = id.FStar_Ident.idText)
end))
in (

let check_rec_binding_id = (fun _64_3 -> (match (_64_3) with
| (id', _64_157, _64_159) -> begin
(id'.FStar_Ident.idText = id.FStar_Ident.idText)
end))
in (

let curmod_ns = (let _161_264 = (current_module env)
in (FStar_Ident.ids_of_lid _161_264))
in (

let proc = (fun _64_4 -> (match (_64_4) with
| Local_binding (l) when (check_local_binding_id l) -> begin
(k_local_binding l)
end
| Rec_binding (r) when (check_rec_binding_id r) -> begin
(k_rec_binding r)
end
| Open_module_or_namespace (ns, _64_170) -> begin
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
| _64_179 -> begin
Cont_ignore
end))
in (

let rec aux = (fun _64_5 -> (match (_64_5) with
| (a)::q -> begin
(let _161_270 = (proc a)
in (option_of_cont (fun _64_186 -> (aux q)) _161_270))
end
| [] -> begin
(let _161_272 = (lookup_default_id Cont_fail id)
in (option_of_cont (fun _64_189 -> None) _161_272))
end))
in (aux env.scope_mods)))))))


let found_local_binding = (fun r _64_195 -> (match (_64_195) with
| (id', x, mut) -> begin
(let _161_275 = (bv_to_name x r)
in ((_161_275), (mut)))
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
| _64_208 -> begin
(try_lookup_id'' env id (fun r -> (let _161_291 = (found_local_binding id.FStar_Ident.idRange r)
in Cont_ok (_161_291))) (fun _64_220 -> Cont_fail) (fun _64_218 -> Cont_ignore) (fun i -> (find_in_module env i (fun _64_214 _64_216 -> Cont_fail) Cont_ignore)) (fun _64_209 _64_211 -> Cont_fail))
end))


let lookup_default_id = (fun env id k_global_def k_not_found -> (

let find_in_monad = (match (env.curmonad) with
| Some (_64_229) -> begin
(

let lid = (qualify env id)
in (match ((FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str)) with
| Some (r) -> begin
(let _161_309 = (k_global_def lid r)
in Some (_161_309))
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

let lid = (let _161_310 = (current_module env)
in (qual _161_310 id))
in (find_in_module env lid k_global_def k_not_found))
end)))


let module_is_defined : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> ((let _161_315 = (current_module env)
in (FStar_Ident.lid_equals lid _161_315)) || (FStar_List.existsb (fun x -> (FStar_Ident.lid_equals lid (Prims.fst x))) env.modules)))


let resolve_module_name : env  ->  FStar_Ident.lident  ->  Prims.bool  ->  FStar_Ident.lident Prims.option = (fun env lid honor_ns -> (

let nslen = (FStar_List.length lid.FStar_Ident.ns)
in (

let rec aux = (fun _64_6 -> (match (_64_6) with
| [] -> begin
if (module_is_defined env lid) then begin
Some (lid)
end else begin
None
end
end
| (Open_module_or_namespace (ns, Open_namespace))::q when honor_ns -> begin
(

let new_lid = (let _161_327 = (let _161_326 = (FStar_Ident.path_of_lid ns)
in (let _161_325 = (FStar_Ident.path_of_lid lid)
in (FStar_List.append _161_326 _161_325)))
in (FStar_Ident.lid_of_path _161_327 (FStar_Ident.range_of_lid lid)))
in if (module_is_defined env new_lid) then begin
Some (new_lid)
end else begin
(aux q)
end)
end
| (Module_abbrev (name, modul))::_64_259 when ((nslen = (Prims.parse_int "0")) && (name.FStar_Ident.idText = lid.FStar_Ident.ident.FStar_Ident.idText)) -> begin
Some (modul)
end
| (_64_267)::q -> begin
(aux q)
end))
in (aux env.scope_mods))))


let resolve_in_open_namespaces'' = (fun env lid k_local_binding k_rec_binding k_record f_module l_default -> (match (lid.FStar_Ident.ns) with
| (_64_280)::_64_278 -> begin
(match ((let _161_357 = (let _161_356 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in (FStar_Ident.set_lid_range _161_356 (FStar_Ident.range_of_lid lid)))
in (resolve_module_name env _161_357 true))) with
| None -> begin
None
end
| Some (modul) -> begin
(

let lid' = (qual modul lid.FStar_Ident.ident)
in (let _161_359 = (f_module Cont_fail lid')
in (option_of_cont (fun _64_286 -> None) _161_359)))
end)
end
| [] -> begin
(try_lookup_id'' env lid.FStar_Ident.ident k_local_binding k_rec_binding k_record (f_module Cont_ignore) l_default)
end))


let cont_of_option = (fun k_none _64_7 -> (match (_64_7) with
| Some (v) -> begin
Cont_ok (v)
end
| None -> begin
k_none
end))


let resolve_in_open_namespaces' = (fun env lid k_local_binding k_rec_binding k_global_def -> (

let k_global_def' = (fun k lid def -> (let _161_385 = (k_global_def lid def)
in (cont_of_option k _161_385)))
in (

let f_module = (fun k lid' -> (find_in_module env lid' (k_global_def' k) k))
in (

let l_default = (fun k i -> (lookup_default_id env i (k_global_def' k) k))
in (resolve_in_open_namespaces'' env lid (fun l -> (let _161_395 = (k_local_binding l)
in (cont_of_option Cont_fail _161_395))) (fun r -> (let _161_397 = (k_rec_binding r)
in (cont_of_option Cont_fail _161_397))) (fun _64_311 -> Cont_ignore) f_module l_default)))))


let fv_qual_of_se : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.fv_qual Prims.option = (fun _64_9 -> (match (_64_9) with
| FStar_Syntax_Syntax.Sig_datacon (_64_317, _64_319, _64_321, l, _64_324, quals, _64_327, _64_329) -> begin
(

let qopt = (FStar_Util.find_map quals (fun _64_8 -> (match (_64_8) with
| FStar_Syntax_Syntax.RecordConstructor (_64_334, fs) -> begin
Some (FStar_Syntax_Syntax.Record_ctor (((l), (fs))))
end
| _64_339 -> begin
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
| FStar_Syntax_Syntax.Sig_declare_typ (_64_344, _64_346, _64_348, quals, _64_351) -> begin
None
end
| _64_355 -> begin
None
end))


let lb_fv : FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.fv = (fun lbs lid -> (let _161_407 = (FStar_Util.find_map lbs (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in if (FStar_Syntax_Syntax.fv_eq_lid fv lid) then begin
Some (fv)
end else begin
None
end)))
in (FStar_All.pipe_right _161_407 FStar_Util.must)))


let ns_of_lid_equals : FStar_Ident.lident  ->  FStar_Ident.lident  ->  Prims.bool = (fun lid ns -> (((FStar_List.length lid.FStar_Ident.ns) = (FStar_List.length (FStar_Ident.ids_of_lid ns))) && (let _161_412 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in (FStar_Ident.lid_equals _161_412 ns))))


let try_lookup_name : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  foundname Prims.option = (fun any_val exclude_interf env lid -> (

let occurrence_range = (FStar_Ident.range_of_lid lid)
in (

let k_global_def = (fun source_lid _64_13 -> (match (_64_13) with
| (_64_371, true) when exclude_interf -> begin
None
end
| (se, _64_376) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_64_379) -> begin
(let _161_427 = (let _161_426 = (let _161_425 = (FStar_Syntax_Syntax.fvar source_lid FStar_Syntax_Syntax.Delta_constant None)
in ((_161_425), (false)))
in Term_name (_161_426))
in Some (_161_427))
end
| FStar_Syntax_Syntax.Sig_datacon (_64_382) -> begin
(let _161_431 = (let _161_430 = (let _161_429 = (let _161_428 = (fv_qual_of_se se)
in (FStar_Syntax_Syntax.fvar source_lid FStar_Syntax_Syntax.Delta_constant _161_428))
in ((_161_429), (false)))
in Term_name (_161_430))
in Some (_161_431))
end
| FStar_Syntax_Syntax.Sig_let ((_64_385, lbs), _64_389, _64_391, _64_393) -> begin
(

let fv = (lb_fv lbs source_lid)
in (let _161_434 = (let _161_433 = (let _161_432 = (FStar_Syntax_Syntax.fvar source_lid fv.FStar_Syntax_Syntax.fv_delta fv.FStar_Syntax_Syntax.fv_qual)
in ((_161_432), (false)))
in Term_name (_161_433))
in Some (_161_434)))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _64_399, _64_401, quals, _64_404) -> begin
if (any_val || (FStar_All.pipe_right quals (FStar_Util.for_some (fun _64_10 -> (match (_64_10) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| _64_410 -> begin
false
end))))) then begin
(

let lid = (FStar_Ident.set_lid_range lid (FStar_Ident.range_of_lid source_lid))
in (

let dd = if ((FStar_Syntax_Util.is_primop_lid lid) || ((ns_of_lid_equals lid FStar_Syntax_Const.prims_lid) && (FStar_All.pipe_right quals (FStar_Util.for_some (fun _64_11 -> (match (_64_11) with
| (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) -> begin
true
end
| _64_420 -> begin
false
end)))))) then begin
FStar_Syntax_Syntax.Delta_equational
end else begin
FStar_Syntax_Syntax.Delta_constant
end
in (match ((FStar_Util.find_map quals (fun _64_12 -> (match (_64_12) with
| FStar_Syntax_Syntax.Reflectable (refl_monad) -> begin
Some (refl_monad)
end
| _64_426 -> begin
None
end)))) with
| Some (refl_monad) -> begin
(

let refl_const = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (refl_monad))) None occurrence_range)
in Some (Term_name (((refl_const), (false)))))
end
| _64_431 -> begin
(let _161_441 = (let _161_440 = (let _161_439 = (let _161_438 = (fv_qual_of_se se)
in (FStar_Syntax_Syntax.fvar lid dd _161_438))
in ((_161_439), (false)))
in Term_name (_161_440))
in Some (_161_441))
end)))
end else begin
None
end
end
| (FStar_Syntax_Syntax.Sig_new_effect_for_free (ne, _)) | (FStar_Syntax_Syntax.Sig_new_effect (ne, _)) -> begin
Some (Eff_name (((se), ((FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname (FStar_Ident.range_of_lid source_lid))))))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (_64_442) -> begin
Some (Eff_name (((se), (source_lid))))
end
| _64_445 -> begin
None
end)
end))
in (

let k_local_binding = (fun r -> (let _161_445 = (let _161_444 = (found_local_binding (FStar_Ident.range_of_lid lid) r)
in Term_name (_161_444))
in Some (_161_445)))
in (

let k_rec_binding = (fun _64_452 -> (match (_64_452) with
| (id, l, dd) -> begin
(let _161_450 = (let _161_449 = (let _161_448 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range l (FStar_Ident.range_of_lid lid)) dd None)
in ((_161_448), (false)))
in Term_name (_161_449))
in Some (_161_450))
end))
in (

let found_unmangled = (match (lid.FStar_Ident.ns) with
| [] -> begin
(match ((unmangleOpName lid.FStar_Ident.ident)) with
| Some (f) -> begin
Some (Term_name (f))
end
| _64_457 -> begin
None
end)
end
| _64_459 -> begin
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
| _64_472 -> begin
None
end))


let try_lookup_effect_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env l -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some (o, l) -> begin
Some (l)
end
| _64_480 -> begin
None
end))


let try_lookup_effect_name_and_attributes : env  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.cflags Prims.list) Prims.option = (fun env l -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some (FStar_Syntax_Syntax.Sig_new_effect (ne, _64_485), l) -> begin
Some (((l), (ne.FStar_Syntax_Syntax.cattributes)))
end
| Some (FStar_Syntax_Syntax.Sig_new_effect_for_free (ne, _64_493), l) -> begin
Some (((l), (ne.FStar_Syntax_Syntax.cattributes)))
end
| Some (FStar_Syntax_Syntax.Sig_effect_abbrev (_64_500, _64_502, _64_504, _64_506, _64_508, cattributes, _64_511), l) -> begin
Some (((l), (cattributes)))
end
| _64_518 -> begin
None
end))


let try_lookup_effect_defn : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl Prims.option = (fun env l -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some (FStar_Syntax_Syntax.Sig_new_effect (ne, _64_523), _64_527) -> begin
Some (ne)
end
| Some (FStar_Syntax_Syntax.Sig_new_effect_for_free (ne, _64_532), _64_536) -> begin
Some (ne)
end
| _64_540 -> begin
None
end))


let is_effect_name : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((try_lookup_effect_name env lid)) with
| None -> begin
false
end
| Some (_64_545) -> begin
true
end))


let lookup_letbinding_quals : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.qualifier Prims.list = (fun env lid -> (

let k_global_def = (fun lid _64_14 -> (match (_64_14) with
| (FStar_Syntax_Syntax.Sig_declare_typ (lid, _64_554, _64_556, quals, _64_559), _64_563) -> begin
Some (quals)
end
| _64_566 -> begin
None
end))
in (match ((resolve_in_open_namespaces' env lid (fun _64_569 -> None) (fun _64_567 -> None) k_global_def)) with
| Some (quals) -> begin
quals
end
| _64_574 -> begin
[]
end)))


let try_lookup_module : env  ->  Prims.string Prims.list  ->  FStar_Syntax_Syntax.modul Prims.option = (fun env path -> (match ((FStar_List.tryFind (fun _64_579 -> (match (_64_579) with
| (mlid, modul) -> begin
((FStar_Ident.path_of_lid mlid) = path)
end)) env.modules)) with
| Some (_64_581, modul) -> begin
Some (modul)
end
| None -> begin
None
end))


let try_lookup_let : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env lid -> (

let k_global_def = (fun lid _64_15 -> (match (_64_15) with
| (FStar_Syntax_Syntax.Sig_let ((_64_592, lbs), _64_596, _64_598, _64_600), _64_604) -> begin
(

let fv = (lb_fv lbs lid)
in (let _161_496 = (FStar_Syntax_Syntax.fvar lid fv.FStar_Syntax_Syntax.fv_delta fv.FStar_Syntax_Syntax.fv_qual)
in Some (_161_496)))
end
| _64_608 -> begin
None
end))
in (resolve_in_open_namespaces' env lid (fun _64_611 -> None) (fun _64_609 -> None) k_global_def)))


let try_lookup_definition : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env lid -> (

let k_global_def = (fun lid _64_16 -> (match (_64_16) with
| (FStar_Syntax_Syntax.Sig_let (lbs, _64_620, _64_622, _64_624), _64_628) -> begin
(FStar_Util.find_map (Prims.snd lbs) (fun lb -> (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv lid) -> begin
Some (lb.FStar_Syntax_Syntax.lbdef)
end
| _64_634 -> begin
None
end)))
end
| _64_636 -> begin
None
end))
in (resolve_in_open_namespaces' env lid (fun _64_639 -> None) (fun _64_637 -> None) k_global_def)))


let try_lookup_lid' : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term * Prims.bool) Prims.option = (fun any_val exclude_interf env lid -> (match ((try_lookup_name any_val exclude_interf env lid)) with
| Some (Term_name (e, mut)) -> begin
Some (((e), (mut)))
end
| _64_651 -> begin
None
end))


let try_lookup_lid : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term * Prims.bool) Prims.option = (fun env l -> (try_lookup_lid' env.iface false env l))


let try_lookup_datacon : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.fv Prims.option = (fun env lid -> (

let k_global_def = (fun lid _64_18 -> (match (_64_18) with
| (FStar_Syntax_Syntax.Sig_declare_typ (_64_660, _64_662, _64_664, quals, _64_667), _64_671) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _64_17 -> (match (_64_17) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| _64_676 -> begin
false
end)))) then begin
(let _161_531 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant None)
in Some (_161_531))
end else begin
None
end
end
| (FStar_Syntax_Syntax.Sig_datacon (_64_678), _64_681) -> begin
(let _161_532 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in Some (_161_532))
end
| _64_684 -> begin
None
end))
in (resolve_in_open_namespaces' env lid (fun _64_687 -> None) (fun _64_685 -> None) k_global_def)))


let find_all_datacons : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.list Prims.option = (fun env lid -> (

let k_global_def = (fun lid _64_19 -> (match (_64_19) with
| (FStar_Syntax_Syntax.Sig_inductive_typ (_64_695, _64_697, _64_699, _64_701, _64_703, datas, _64_706, _64_708), _64_712) -> begin
Some (datas)
end
| _64_715 -> begin
None
end))
in (resolve_in_open_namespaces' env lid (fun _64_718 -> None) (fun _64_716 -> None) k_global_def)))


let record_cache_aux_with_filter : (((Prims.unit  ->  Prims.unit) * (Prims.unit  ->  Prims.unit) * (Prims.unit  ->  record_or_dc Prims.list) * (record_or_dc  ->  Prims.unit) * (Prims.unit  ->  Prims.unit)) * (Prims.unit  ->  Prims.unit)) = (

let record_cache = (FStar_Util.mk_ref (([])::[]))
in (

let push = (fun _64_722 -> (match (()) with
| () -> begin
(let _161_567 = (let _161_566 = (let _161_564 = (FStar_ST.read record_cache)
in (FStar_List.hd _161_564))
in (let _161_565 = (FStar_ST.read record_cache)
in (_161_566)::_161_565))
in (FStar_ST.op_Colon_Equals record_cache _161_567))
end))
in (

let pop = (fun _64_724 -> (match (()) with
| () -> begin
(let _161_571 = (let _161_570 = (FStar_ST.read record_cache)
in (FStar_List.tl _161_570))
in (FStar_ST.op_Colon_Equals record_cache _161_571))
end))
in (

let peek = (fun _64_726 -> (match (()) with
| () -> begin
(let _161_574 = (FStar_ST.read record_cache)
in (FStar_List.hd _161_574))
end))
in (

let insert = (fun r -> (let _161_581 = (let _161_580 = (let _161_577 = (peek ())
in (r)::_161_577)
in (let _161_579 = (let _161_578 = (FStar_ST.read record_cache)
in (FStar_List.tl _161_578))
in (_161_580)::_161_579))
in (FStar_ST.op_Colon_Equals record_cache _161_581)))
in (

let commit = (fun _64_730 -> (match (()) with
| () -> begin
(match ((FStar_ST.read record_cache)) with
| (hd)::(_64_733)::tl -> begin
(FStar_ST.op_Colon_Equals record_cache ((hd)::tl))
end
| _64_738 -> begin
(FStar_All.failwith "Impossible")
end)
end))
in (

let filter = (fun _64_740 -> (match (()) with
| () -> begin
(

let rc = (peek ())
in (

let _64_742 = (pop ())
in (match (()) with
| () -> begin
(

let filtered = (FStar_List.filter (fun r -> (not (r.is_private_or_abstract))) rc)
in (let _161_588 = (let _161_587 = (FStar_ST.read record_cache)
in (filtered)::_161_587)
in (FStar_ST.op_Colon_Equals record_cache _161_588)))
end)))
end))
in (

let aux = ((push), (pop), (peek), (insert), (commit))
in ((aux), (filter))))))))))


let record_cache_aux : ((Prims.unit  ->  Prims.unit) * (Prims.unit  ->  Prims.unit) * (Prims.unit  ->  record_or_dc Prims.list) * (record_or_dc  ->  Prims.unit) * (Prims.unit  ->  Prims.unit)) = (

let _64_749 = record_cache_aux_with_filter
in (match (_64_749) with
| (aux, _64_748) -> begin
aux
end))


let filter_record_cache : Prims.unit  ->  Prims.unit = (

let _64_753 = record_cache_aux_with_filter
in (match (_64_753) with
| (_64_751, filter) -> begin
filter
end))


let push_record_cache : Prims.unit  ->  Prims.unit = (

let _64_763 = record_cache_aux
in (match (_64_763) with
| (push, _64_756, _64_758, _64_760, _64_762) -> begin
push
end))


let pop_record_cache : Prims.unit  ->  Prims.unit = (

let _64_773 = record_cache_aux
in (match (_64_773) with
| (_64_765, pop, _64_768, _64_770, _64_772) -> begin
pop
end))


let peek_record_cache : Prims.unit  ->  record_or_dc Prims.list = (

let _64_783 = record_cache_aux
in (match (_64_783) with
| (_64_775, _64_777, peek, _64_780, _64_782) -> begin
peek
end))


let insert_record_cache : record_or_dc  ->  Prims.unit = (

let _64_793 = record_cache_aux
in (match (_64_793) with
| (_64_785, _64_787, _64_789, insert, _64_792) -> begin
insert
end))


let commit_record_cache : Prims.unit  ->  Prims.unit = (

let _64_803 = record_cache_aux
in (match (_64_803) with
| (_64_795, _64_797, _64_799, _64_801, commit) -> begin
commit
end))


let extract_record : env  ->  scope_mod Prims.list FStar_ST.ref  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun e new_globs _64_23 -> (match (_64_23) with
| FStar_Syntax_Syntax.Sig_bundle (sigs, _64_809, _64_811, _64_813) -> begin
(

let is_rec = (FStar_Util.for_some (fun _64_20 -> (match (_64_20) with
| (FStar_Syntax_Syntax.RecordType (_)) | (FStar_Syntax_Syntax.RecordConstructor (_)) -> begin
true
end
| _64_824 -> begin
false
end)))
in (

let find_dc = (fun dc -> (FStar_All.pipe_right sigs (FStar_Util.find_opt (fun _64_21 -> (match (_64_21) with
| FStar_Syntax_Syntax.Sig_datacon (lid, _64_831, _64_833, _64_835, _64_837, _64_839, _64_841, _64_843) -> begin
(FStar_Ident.lid_equals dc lid)
end
| _64_847 -> begin
false
end)))))
in (FStar_All.pipe_right sigs (FStar_List.iter (fun _64_22 -> (match (_64_22) with
| FStar_Syntax_Syntax.Sig_inductive_typ (typename, univs, parms, _64_853, _64_855, (dc)::[], tags, _64_860) -> begin
(match ((let _161_790 = (find_dc dc)
in (FStar_All.pipe_left FStar_Util.must _161_790))) with
| FStar_Syntax_Syntax.Sig_datacon (constrname, _64_865, t, _64_868, _64_870, _64_872, _64_874, _64_876) -> begin
(

let _64_882 = (FStar_Syntax_Util.arrow_formals t)
in (match (_64_882) with
| (formals, _64_881) -> begin
(

let is_rec = (is_rec tags)
in (

let fields = (FStar_All.pipe_right formals (FStar_List.collect (fun _64_886 -> (match (_64_886) with
| (x, q) -> begin
if ((FStar_Syntax_Syntax.is_null_bv x) || (is_rec && (FStar_Syntax_Syntax.is_implicit q))) then begin
[]
end else begin
(let _161_793 = (let _161_792 = if is_rec then begin
(FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname)
end else begin
x.FStar_Syntax_Syntax.ppname
end
in ((_161_792), (x.FStar_Syntax_Syntax.sort)))
in (_161_793)::[])
end
end))))
in (

let record = {typename = typename; constrname = constrname.FStar_Ident.ident; parms = parms; fields = fields; is_private_or_abstract = ((FStar_List.contains FStar_Syntax_Syntax.Private tags) || (FStar_List.contains FStar_Syntax_Syntax.Abstract tags)); is_record = is_rec}
in (

let _64_889 = (let _161_795 = (let _161_794 = (FStar_ST.read new_globs)
in (Record_or_dc (record))::_161_794)
in (FStar_ST.op_Colon_Equals new_globs _161_795))
in (match (()) with
| () -> begin
(insert_record_cache record)
end)))))
end))
end
| _64_891 -> begin
()
end)
end
| _64_893 -> begin
()
end))))))
end
| _64_895 -> begin
()
end))


let try_lookup_record_or_dc_by_field_name : env  ->  FStar_Ident.lident  ->  record_or_dc Prims.option = (fun env fieldname -> (

let find_in_cache = (fun fieldname -> (

let _64_902 = ((fieldname.FStar_Ident.ns), (fieldname.FStar_Ident.ident))
in (match (_64_902) with
| (ns, id) -> begin
(let _161_806 = (peek_record_cache ())
in (FStar_Util.find_map _161_806 (fun record -> (let _161_805 = (find_in_record ns id record (fun r -> Cont_ok (r)))
in (option_of_cont (fun _64_905 -> None) _161_805)))))
end)))
in (resolve_in_open_namespaces'' env fieldname (fun _64_915 -> Cont_ignore) (fun _64_913 -> Cont_ignore) (fun r -> Cont_ok (r)) (fun k fn -> (let _161_812 = (find_in_cache fn)
in (cont_of_option k _161_812))) (fun k _64_908 -> k))))


let try_lookup_record_by_field_name : env  ->  FStar_Ident.lident  ->  record_or_dc Prims.option = (fun env fieldname -> (match ((try_lookup_record_or_dc_by_field_name env fieldname)) with
| Some (r) when r.is_record -> begin
Some (r)
end
| _64_922 -> begin
None
end))


let belongs_to_record : env  ->  FStar_Ident.lident  ->  record_or_dc  ->  Prims.bool = (fun env lid record -> (match ((try_lookup_record_by_field_name env lid)) with
| Some (record') when ((let _161_825 = (FStar_Ident.path_of_ns record.typename.FStar_Ident.ns)
in (FStar_Ident.text_of_path _161_825)) = (let _161_826 = (FStar_Ident.path_of_ns record'.typename.FStar_Ident.ns)
in (FStar_Ident.text_of_path _161_826))) -> begin
(match ((find_in_record record.typename.FStar_Ident.ns lid.FStar_Ident.ident record (fun _64_928 -> Cont_ok (())))) with
| Cont_ok (_64_931) -> begin
true
end
| _64_934 -> begin
false
end)
end
| _64_936 -> begin
false
end))


let try_lookup_dc_by_field_name : env  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * Prims.bool) Prims.option = (fun env fieldname -> (match ((try_lookup_record_or_dc_by_field_name env fieldname)) with
| Some (r) -> begin
(let _161_834 = (let _161_833 = (let _161_832 = (FStar_Ident.lid_of_ids (FStar_List.append r.typename.FStar_Ident.ns ((r.constrname)::[])))
in (FStar_Ident.set_lid_range _161_832 (FStar_Ident.range_of_lid fieldname)))
in ((_161_833), (r.is_record)))
in Some (_161_834))
end
| _64_942 -> begin
None
end))


let unique : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  Prims.bool = (fun any_val exclude_if env lid -> (

let this_env = (

let _64_947 = env
in {curmodule = _64_947.curmodule; curmonad = _64_947.curmonad; modules = _64_947.modules; scope_mods = []; sigaccum = _64_947.sigaccum; sigmap = _64_947.sigmap; default_result_effect = _64_947.default_result_effect; iface = _64_947.iface; admitted_iface = _64_947.admitted_iface; expect_typ = _64_947.expect_typ})
in (match ((try_lookup_lid' any_val exclude_if env lid)) with
| None -> begin
true
end
| Some (_64_952) -> begin
false
end)))


let push_scope_mod : env  ->  scope_mod  ->  env = (fun env scope_mod -> (

let _64_956 = env
in {curmodule = _64_956.curmodule; curmonad = _64_956.curmonad; modules = _64_956.modules; scope_mods = (scope_mod)::env.scope_mods; sigaccum = _64_956.sigaccum; sigmap = _64_956.sigmap; default_result_effect = _64_956.default_result_effect; iface = _64_956.iface; admitted_iface = _64_956.admitted_iface; expect_typ = _64_956.expect_typ}))


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
| Some (se, _64_977) -> begin
(match ((let _161_873 = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_Util.find_opt (FStar_Ident.lid_equals l) _161_873))) with
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
in (let _161_876 = (let _161_875 = (let _161_874 = (FStar_Util.format2 "Duplicate top-level names [%s]; previously declared at %s" (FStar_Ident.text_of_lid l) r)
in ((_161_874), ((FStar_Ident.range_of_lid l))))
in FStar_Syntax_Syntax.Error (_161_875))
in (Prims.raise _161_876)))))
in (

let globals = (FStar_ST.alloc env.scope_mods)
in (

let env = (

let _64_996 = (match (s) with
| FStar_Syntax_Syntax.Sig_let (_64_987) -> begin
((false), (true))
end
| FStar_Syntax_Syntax.Sig_bundle (_64_990) -> begin
((true), (true))
end
| _64_993 -> begin
((false), (false))
end)
in (match (_64_996) with
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

let _64_1000 = (extract_record env globals s)
in (

let _64_1002 = env
in {curmodule = _64_1002.curmodule; curmonad = _64_1002.curmonad; modules = _64_1002.modules; scope_mods = _64_1002.scope_mods; sigaccum = (s)::env.sigaccum; sigmap = _64_1002.sigmap; default_result_effect = _64_1002.default_result_effect; iface = _64_1002.iface; admitted_iface = _64_1002.admitted_iface; expect_typ = _64_1002.expect_typ}))
end
| Some (l) -> begin
(err l)
end))
end))
in (

let env = (

let _64_1007 = env
in (let _161_878 = (FStar_ST.read globals)
in {curmodule = _64_1007.curmodule; curmonad = _64_1007.curmonad; modules = _64_1007.modules; scope_mods = _161_878; sigaccum = _64_1007.sigaccum; sigmap = _64_1007.sigmap; default_result_effect = _64_1007.default_result_effect; iface = _64_1007.iface; admitted_iface = _64_1007.admitted_iface; expect_typ = _64_1007.expect_typ}))
in (

let _64_1024 = (match (s) with
| FStar_Syntax_Syntax.Sig_bundle (ses, _64_1012, _64_1014, _64_1016) -> begin
(let _161_881 = (FStar_List.map (fun se -> (let _161_880 = (FStar_Syntax_Util.lids_of_sigelt se)
in ((_161_880), (se)))) ses)
in ((env), (_161_881)))
end
| _64_1021 -> begin
(let _161_884 = (let _161_883 = (let _161_882 = (FStar_Syntax_Util.lids_of_sigelt s)
in ((_161_882), (s)))
in (_161_883)::[])
in ((env), (_161_884)))
end)
in (match (_64_1024) with
| (env, lss) -> begin
(

let _64_1030 = (FStar_All.pipe_right lss (FStar_List.iter (fun _64_1027 -> (match (_64_1027) with
| (lids, se) -> begin
(FStar_All.pipe_right lids (FStar_List.iter (fun lid -> (

let _64_1029 = (let _161_888 = (let _161_887 = (FStar_ST.read globals)
in (Top_level_def (lid.FStar_Ident.ident))::_161_887)
in (FStar_ST.op_Colon_Equals globals _161_888))
in (match (()) with
| () -> begin
(FStar_Util.smap_add (sigmap env) lid.FStar_Ident.str ((se), ((env.iface && (not (env.admitted_iface))))))
end)))))
end))))
in (

let env = (

let _64_1032 = env
in (let _161_889 = (FStar_ST.read globals)
in {curmodule = _64_1032.curmodule; curmonad = _64_1032.curmonad; modules = _64_1032.modules; scope_mods = _161_889; sigaccum = _64_1032.sigaccum; sigmap = _64_1032.sigmap; default_result_effect = _64_1032.default_result_effect; iface = _64_1032.iface; admitted_iface = _64_1032.admitted_iface; expect_typ = _64_1032.expect_typ}))
in env))
end)))))))


let push_namespace : env  ->  FStar_Ident.lident  ->  env = (fun env ns -> (

let _64_1047 = (match ((resolve_module_name env ns false)) with
| None -> begin
(

let modules = env.modules
in if (FStar_All.pipe_right modules (FStar_Util.for_some (fun _64_1042 -> (match (_64_1042) with
| (m, _64_1041) -> begin
(FStar_Util.starts_with (Prims.strcat (FStar_Ident.text_of_lid m) ".") (Prims.strcat (FStar_Ident.text_of_lid ns) "."))
end)))) then begin
((ns), (Open_namespace))
end else begin
(let _161_897 = (let _161_896 = (let _161_895 = (FStar_Util.format1 "Namespace %s cannot be found" (FStar_Ident.text_of_lid ns))
in ((_161_895), ((FStar_Ident.range_of_lid ns))))
in FStar_Syntax_Syntax.Error (_161_896))
in (Prims.raise _161_897))
end)
end
| Some (ns') -> begin
((ns'), (Open_module))
end)
in (match (_64_1047) with
| (ns', kd) -> begin
(push_scope_mod env (Open_module_or_namespace (((ns'), (kd)))))
end)))


let push_module_abbrev : env  ->  FStar_Ident.ident  ->  FStar_Ident.lident  ->  env = (fun env x l -> if (module_is_defined env l) then begin
(push_scope_mod env (Module_abbrev (((x), (l)))))
end else begin
(let _161_906 = (let _161_905 = (let _161_904 = (FStar_Util.format1 "Module %s cannot be found" (FStar_Ident.text_of_lid l))
in ((_161_904), ((FStar_Ident.range_of_lid l))))
in FStar_Syntax_Syntax.Error (_161_905))
in (Prims.raise _161_906))
end)


let check_admits : env  ->  Prims.unit = (fun env -> (FStar_All.pipe_right env.sigaccum (FStar_List.iter (fun se -> (match (se) with
| FStar_Syntax_Syntax.Sig_declare_typ (l, u, t, quals, r) -> begin
(match ((try_lookup_lid env l)) with
| None -> begin
(

let _64_1061 = (let _161_912 = (let _161_911 = (FStar_Range.string_of_range (FStar_Ident.range_of_lid l))
in (let _161_910 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format2 "%s: Warning: Admitting %s without a definition\n" _161_911 _161_910)))
in (FStar_Util.print_string _161_912))
in (FStar_Util.smap_add (sigmap env) l.FStar_Ident.str ((FStar_Syntax_Syntax.Sig_declare_typ (((l), (u), (t), ((FStar_Syntax_Syntax.Assumption)::quals), (r)))), (false))))
end
| Some (_64_1064) -> begin
()
end)
end
| _64_1067 -> begin
()
end)))))


let finish : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env modul -> (

let _64_1127 = (FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations (FStar_List.iter (fun _64_25 -> (match (_64_25) with
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _64_1074, _64_1076) -> begin
if ((FStar_List.contains FStar_Syntax_Syntax.Private quals) || (FStar_List.contains FStar_Syntax_Syntax.Abstract quals)) then begin
(FStar_All.pipe_right ses (FStar_List.iter (fun _64_24 -> (match (_64_24) with
| FStar_Syntax_Syntax.Sig_datacon (lid, _64_1082, _64_1084, _64_1086, _64_1088, _64_1090, _64_1092, _64_1094) -> begin
(FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str)
end
| _64_1098 -> begin
()
end))))
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _64_1101, _64_1103, quals, _64_1106) -> begin
if (FStar_List.contains FStar_Syntax_Syntax.Private quals) then begin
(FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str)
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_let ((_64_1110, lbs), r, _64_1115, quals) -> begin
(

let _64_1120 = if ((FStar_List.contains FStar_Syntax_Syntax.Private quals) || (FStar_List.contains FStar_Syntax_Syntax.Abstract quals)) then begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (let _161_923 = (let _161_922 = (let _161_921 = (let _161_920 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _161_920.FStar_Syntax_Syntax.fv_name)
in _161_921.FStar_Syntax_Syntax.v)
in _161_922.FStar_Ident.str)
in (FStar_Util.smap_remove (sigmap env) _161_923)))))
end else begin
()
end
in if ((FStar_List.contains FStar_Syntax_Syntax.Abstract quals) && (not ((FStar_List.contains FStar_Syntax_Syntax.Private quals)))) then begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (

let lid = (let _161_926 = (let _161_925 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _161_925.FStar_Syntax_Syntax.fv_name)
in _161_926.FStar_Syntax_Syntax.v)
in (

let decl = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), ((FStar_Syntax_Syntax.Assumption)::quals), (r)))
in (FStar_Util.smap_add (sigmap env) lid.FStar_Ident.str ((decl), (false))))))))
end else begin
()
end)
end
| _64_1126 -> begin
()
end))))
in (

let _64_1129 = (filter_record_cache ())
in (match (()) with
| () -> begin
(

let _64_1130 = env
in {curmodule = None; curmonad = _64_1130.curmonad; modules = (((modul.FStar_Syntax_Syntax.name), (modul)))::env.modules; scope_mods = []; sigaccum = []; sigmap = _64_1130.sigmap; default_result_effect = _64_1130.default_result_effect; iface = _64_1130.iface; admitted_iface = _64_1130.admitted_iface; expect_typ = _64_1130.expect_typ})
end))))


type env_stack_ops =
{push : env  ->  env; mark : env  ->  env; reset_mark : env  ->  env; commit_mark : env  ->  env; pop : env  ->  env}


let is_Mkenv_stack_ops : env_stack_ops  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv_stack_ops"))))


let stack_ops : env_stack_ops = (

let stack = (FStar_Util.mk_ref [])
in (

let push = (fun env -> (

let _64_1141 = (push_record_cache ())
in (

let _64_1143 = (let _161_976 = (let _161_975 = (FStar_ST.read stack)
in (env)::_161_975)
in (FStar_ST.op_Colon_Equals stack _161_976))
in (

let _64_1145 = env
in (let _161_977 = (FStar_Util.smap_copy (sigmap env))
in {curmodule = _64_1145.curmodule; curmonad = _64_1145.curmonad; modules = _64_1145.modules; scope_mods = _64_1145.scope_mods; sigaccum = _64_1145.sigaccum; sigmap = _161_977; default_result_effect = _64_1145.default_result_effect; iface = _64_1145.iface; admitted_iface = _64_1145.admitted_iface; expect_typ = _64_1145.expect_typ})))))
in (

let pop = (fun env -> (match ((FStar_ST.read stack)) with
| (env)::tl -> begin
(

let _64_1152 = (pop_record_cache ())
in (

let _64_1154 = (FStar_ST.op_Colon_Equals stack tl)
in env))
end
| _64_1157 -> begin
(FStar_All.failwith "Impossible: Too many pops")
end))
in (

let commit_mark = (fun env -> (

let _64_1160 = (commit_record_cache ())
in (match ((FStar_ST.read stack)) with
| (_64_1164)::tl -> begin
(

let _64_1166 = (FStar_ST.op_Colon_Equals stack tl)
in env)
end
| _64_1169 -> begin
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
| (l)::_64_1180 -> begin
(l.FStar_Ident.nsstr = m.FStar_Ident.str)
end
| _64_1184 -> begin
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

let _64_1208 = (FStar_All.pipe_right keys (FStar_List.iter (fun k -> (match ((FStar_Util.smap_try_find sm' k)) with
| Some (se, true) when (sigelt_in_m se) -> begin
(

let _64_1194 = (FStar_Util.smap_remove sm' k)
in (

let se = (match (se) with
| FStar_Syntax_Syntax.Sig_declare_typ (l, u, t, q, r) -> begin
FStar_Syntax_Syntax.Sig_declare_typ (((l), (u), (t), ((FStar_Syntax_Syntax.Assumption)::q), (r)))
end
| _64_1204 -> begin
se
end)
in (FStar_Util.smap_add sm' k ((se), (false)))))
end
| _64_1207 -> begin
()
end))))
in env)))))))


let finish_module_or_interface : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env modul -> (

let _64_1212 = if (not (modul.FStar_Syntax_Syntax.is_interface)) then begin
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

let _64_1223 = env
in (let _161_1014 = (FStar_List.map (fun lid -> Open_module_or_namespace (((lid), (Open_namespace)))) open_ns)
in {curmodule = Some (mname); curmonad = _64_1223.curmonad; modules = _64_1223.modules; scope_mods = _161_1014; sigaccum = _64_1223.sigaccum; sigmap = env.sigmap; default_result_effect = if ((FStar_Ident.lid_equals mname FStar_Syntax_Const.all_lid) || (has_all_in_scope env)) then begin
FStar_Syntax_Const.effect_ML_lid
end else begin
FStar_Syntax_Const.effect_Tot_lid
end; iface = intf; admitted_iface = admitted; expect_typ = _64_1223.expect_typ})))))
in (match ((FStar_All.pipe_right env.modules (FStar_Util.find_opt (fun _64_1229 -> (match (_64_1229) with
| (l, _64_1228) -> begin
(FStar_Ident.lid_equals l mname)
end))))) with
| None -> begin
(let _161_1016 = (prep env)
in ((_161_1016), (false)))
end
| Some (_64_1232, m) -> begin
(

let _64_1236 = if ((not (m.FStar_Syntax_Syntax.is_interface)) || intf) then begin
(let _161_1019 = (let _161_1018 = (let _161_1017 = (FStar_Util.format1 "Duplicate module or interface name: %s" mname.FStar_Ident.str)
in ((_161_1017), ((FStar_Ident.range_of_lid mname))))
in FStar_Syntax_Syntax.Error (_161_1018))
in (Prims.raise _161_1019))
end else begin
()
end
in (let _161_1021 = (let _161_1020 = (push env)
in (prep _161_1020))
in ((_161_1021), (true))))
end)))


let enter_monad_scope : env  ->  FStar_Ident.ident  ->  env = (fun env mname -> (match (env.curmonad) with
| Some (mname') -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((((Prims.strcat "Trying to define monad " (Prims.strcat mname.FStar_Ident.idText (Prims.strcat ", but already in monad scope " mname'.FStar_Ident.idText)))), (mname.FStar_Ident.idRange)))))
end
| None -> begin
(

let _64_1243 = env
in {curmodule = _64_1243.curmodule; curmonad = Some (mname); modules = _64_1243.modules; scope_mods = _64_1243.scope_mods; sigaccum = _64_1243.sigaccum; sigmap = _64_1243.sigmap; default_result_effect = _64_1243.default_result_effect; iface = _64_1243.iface; admitted_iface = _64_1243.admitted_iface; expect_typ = _64_1243.expect_typ})
end))


let fail_or = (fun env lookup lid -> (match ((lookup lid)) with
| None -> begin
(

let opened_modules = (FStar_List.map (fun _64_1252 -> (match (_64_1252) with
| (lid, _64_1251) -> begin
(FStar_Ident.text_of_lid lid)
end)) env.modules)
in (

let msg = (FStar_Util.format1 "Identifier not found: [%s]" (FStar_Ident.text_of_lid lid))
in (

let msg = if ((FStar_List.length lid.FStar_Ident.ns) = (Prims.parse_int "0")) then begin
msg
end else begin
(

let modul = (let _161_1033 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in (FStar_Ident.set_lid_range _161_1033 (FStar_Ident.range_of_lid lid)))
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




