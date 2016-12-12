
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
| Local_binding (_63_35) -> begin
_63_35
end))


let ___Rec_binding____0 = (fun projectee -> (match (projectee) with
| Rec_binding (_63_38) -> begin
_63_38
end))


let ___Module_abbrev____0 = (fun projectee -> (match (projectee) with
| Module_abbrev (_63_41) -> begin
_63_41
end))


let ___Open_module_or_namespace____0 = (fun projectee -> (match (projectee) with
| Open_module_or_namespace (_63_44) -> begin
_63_44
end))


let ___Top_level_def____0 = (fun projectee -> (match (projectee) with
| Top_level_def (_63_47) -> begin
_63_47
end))


let ___Record_or_dc____0 = (fun projectee -> (match (projectee) with
| Record_or_dc (_63_50) -> begin
_63_50
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
| Term_name (_63_64) -> begin
_63_64
end))


let ___Eff_name____0 = (fun projectee -> (match (projectee) with
| Eff_name (_63_67) -> begin
_63_67
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
(let _158_175 = (current_module env)
in (qual _158_175 id))
end
| Some (monad) -> begin
(let _158_177 = (let _158_176 = (current_module env)
in (qual _158_176 monad))
in (FStar_Syntax_Util.mk_field_projector_name_from_ident _158_177 id))
end))


let new_sigmap = (fun _63_80 -> (match (()) with
| () -> begin
(FStar_Util.smap_create (Prims.parse_int "100"))
end))


let empty_env : Prims.unit  ->  env = (fun _63_81 -> (match (()) with
| () -> begin
(let _158_181 = (new_sigmap ())
in {curmodule = None; curmonad = None; modules = []; scope_mods = []; sigaccum = []; sigmap = _158_181; default_result_effect = FStar_Syntax_Const.effect_Tot_lid; iface = false; admitted_iface = false; expect_typ = false})
end))


let sigmap : env  ->  (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap = (fun env -> env.sigmap)


let has_all_in_scope : env  ->  Prims.bool = (fun env -> (FStar_List.existsb (fun _63_87 -> (match (_63_87) with
| (m, _63_86) -> begin
(FStar_Ident.lid_equals m FStar_Syntax_Const.all_lid)
end)) env.modules))


let default_total : env  ->  env = (fun env -> (

let _63_89 = env
in {curmodule = _63_89.curmodule; curmonad = _63_89.curmonad; modules = _63_89.modules; scope_mods = _63_89.scope_mods; sigaccum = _63_89.sigaccum; sigmap = _63_89.sigmap; default_result_effect = FStar_Syntax_Const.effect_Tot_lid; iface = _63_89.iface; admitted_iface = _63_89.admitted_iface; expect_typ = _63_89.expect_typ}))


let default_ml : env  ->  env = (fun env -> if (has_all_in_scope env) then begin
(

let _63_92 = env
in {curmodule = _63_92.curmodule; curmonad = _63_92.curmonad; modules = _63_92.modules; scope_mods = _63_92.scope_mods; sigaccum = _63_92.sigaccum; sigmap = _63_92.sigmap; default_result_effect = FStar_Syntax_Const.effect_ML_lid; iface = _63_92.iface; admitted_iface = _63_92.admitted_iface; expect_typ = _63_92.expect_typ})
end else begin
env
end)


let set_bv_range : FStar_Syntax_Syntax.bv  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.bv = (fun bv r -> (

let id = (

let _63_96 = bv.FStar_Syntax_Syntax.ppname
in {FStar_Ident.idText = _63_96.FStar_Ident.idText; FStar_Ident.idRange = r})
in (

let _63_99 = bv
in {FStar_Syntax_Syntax.ppname = id; FStar_Syntax_Syntax.index = _63_99.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _63_99.FStar_Syntax_Syntax.sort})))


let bv_to_name : FStar_Syntax_Syntax.bv  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.term = (fun bv r -> (FStar_Syntax_Syntax.bv_to_name (set_bv_range bv r)))


let unmangleMap : (Prims.string * Prims.string * FStar_Syntax_Syntax.delta_depth * FStar_Syntax_Syntax.fv_qual Prims.option) Prims.list = ((("op_ColonColon"), ("Cons"), (FStar_Syntax_Syntax.Delta_constant), (Some (FStar_Syntax_Syntax.Data_ctor))))::((("not"), ("op_Negation"), (FStar_Syntax_Syntax.Delta_equational), (None)))::[]


let unmangleOpName : FStar_Ident.ident  ->  (FStar_Syntax_Syntax.term * Prims.bool) Prims.option = (fun id -> (

let t = (FStar_Util.find_map unmangleMap (fun _63_108 -> (match (_63_108) with
| (x, y, dd, dq) -> begin
if (id.FStar_Ident.idText = x) then begin
(let _158_203 = (let _158_202 = (FStar_Ident.lid_of_path (("Prims")::(y)::[]) id.FStar_Ident.idRange)
in (FStar_Syntax_Syntax.fvar _158_202 dd dq))
in Some (_158_203))
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
| Cont_ok (_63_116) -> begin
_63_116
end))


let option_of_cont = (fun k_ignore _63_1 -> (match (_63_1) with
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

let find = (FStar_Util.find_map record.fields (fun _63_133 -> (match (_63_133) with
| (f, _63_132) -> begin
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

let check_local_binding_id = (fun _63_2 -> (match (_63_2) with
| (id', _63_149, _63_151) -> begin
(id'.FStar_Ident.idText = id.FStar_Ident.idText)
end))
in (

let check_rec_binding_id = (fun _63_3 -> (match (_63_3) with
| (id', _63_157, _63_159) -> begin
(id'.FStar_Ident.idText = id.FStar_Ident.idText)
end))
in (

let curmod_ns = (let _158_264 = (current_module env)
in (FStar_Ident.ids_of_lid _158_264))
in (

let proc = (fun _63_4 -> (match (_63_4) with
| Local_binding (l) when (check_local_binding_id l) -> begin
(k_local_binding l)
end
| Rec_binding (r) when (check_rec_binding_id r) -> begin
(k_rec_binding r)
end
| Open_module_or_namespace (ns, _63_170) -> begin
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
| _63_179 -> begin
Cont_ignore
end))
in (

let rec aux = (fun _63_5 -> (match (_63_5) with
| (a)::q -> begin
(let _158_270 = (proc a)
in (option_of_cont (fun _63_186 -> (aux q)) _158_270))
end
| [] -> begin
(let _158_272 = (lookup_default_id Cont_fail id)
in (option_of_cont (fun _63_189 -> None) _158_272))
end))
in (aux env.scope_mods)))))))


let found_local_binding = (fun r _63_195 -> (match (_63_195) with
| (id', x, mut) -> begin
(let _158_275 = (bv_to_name x r)
in ((_158_275), (mut)))
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
| _63_208 -> begin
(try_lookup_id'' env id (fun r -> (let _158_291 = (found_local_binding id.FStar_Ident.idRange r)
in Cont_ok (_158_291))) (fun _63_220 -> Cont_fail) (fun _63_218 -> Cont_ignore) (fun i -> (find_in_module env i (fun _63_214 _63_216 -> Cont_fail) Cont_ignore)) (fun _63_209 _63_211 -> Cont_fail))
end))


let lookup_default_id = (fun env id k_global_def k_not_found -> (

let find_in_monad = (match (env.curmonad) with
| Some (_63_229) -> begin
(

let lid = (qualify env id)
in (match ((FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str)) with
| Some (r) -> begin
(let _158_309 = (k_global_def lid r)
in Some (_158_309))
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

let lid = (let _158_310 = (current_module env)
in (qual _158_310 id))
in (find_in_module env lid k_global_def k_not_found))
end)))


let module_is_defined : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> ((let _158_315 = (current_module env)
in (FStar_Ident.lid_equals lid _158_315)) || (FStar_List.existsb (fun x -> (FStar_Ident.lid_equals lid (Prims.fst x))) env.modules)))


let resolve_module_name : env  ->  FStar_Ident.lident  ->  Prims.bool  ->  FStar_Ident.lident Prims.option = (fun env lid honor_ns -> (

let nslen = (FStar_List.length lid.FStar_Ident.ns)
in (

let rec aux = (fun _63_6 -> (match (_63_6) with
| [] -> begin
if (module_is_defined env lid) then begin
Some (lid)
end else begin
None
end
end
| (Open_module_or_namespace (ns, Open_namespace))::q when honor_ns -> begin
(

let new_lid = (let _158_327 = (let _158_326 = (FStar_Ident.path_of_lid ns)
in (let _158_325 = (FStar_Ident.path_of_lid lid)
in (FStar_List.append _158_326 _158_325)))
in (FStar_Ident.lid_of_path _158_327 (FStar_Ident.range_of_lid lid)))
in if (module_is_defined env new_lid) then begin
Some (new_lid)
end else begin
(aux q)
end)
end
| (Module_abbrev (name, modul))::_63_259 when ((nslen = (Prims.parse_int "0")) && (name.FStar_Ident.idText = lid.FStar_Ident.ident.FStar_Ident.idText)) -> begin
Some (modul)
end
| (_63_267)::q -> begin
(aux q)
end))
in (aux env.scope_mods))))


let resolve_in_open_namespaces'' = (fun env lid k_local_binding k_rec_binding k_record f_module l_default -> (match (lid.FStar_Ident.ns) with
| (_63_280)::_63_278 -> begin
(match ((let _158_357 = (let _158_356 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in (FStar_Ident.set_lid_range _158_356 (FStar_Ident.range_of_lid lid)))
in (resolve_module_name env _158_357 true))) with
| None -> begin
None
end
| Some (modul) -> begin
(

let lid' = (qual modul lid.FStar_Ident.ident)
in (let _158_359 = (f_module Cont_fail lid')
in (option_of_cont (fun _63_286 -> None) _158_359)))
end)
end
| [] -> begin
(try_lookup_id'' env lid.FStar_Ident.ident k_local_binding k_rec_binding k_record (f_module Cont_ignore) l_default)
end))


let cont_of_option = (fun k_none _63_7 -> (match (_63_7) with
| Some (v) -> begin
Cont_ok (v)
end
| None -> begin
k_none
end))


let resolve_in_open_namespaces' = (fun env lid k_local_binding k_rec_binding k_global_def -> (

let k_global_def' = (fun k lid def -> (let _158_385 = (k_global_def lid def)
in (cont_of_option k _158_385)))
in (

let f_module = (fun k lid' -> (find_in_module env lid' (k_global_def' k) k))
in (

let l_default = (fun k i -> (lookup_default_id env i (k_global_def' k) k))
in (resolve_in_open_namespaces'' env lid (fun l -> (let _158_395 = (k_local_binding l)
in (cont_of_option Cont_fail _158_395))) (fun r -> (let _158_397 = (k_rec_binding r)
in (cont_of_option Cont_fail _158_397))) (fun _63_311 -> Cont_ignore) f_module l_default)))))


let fv_qual_of_se : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.fv_qual Prims.option = (fun _63_9 -> (match (_63_9) with
| FStar_Syntax_Syntax.Sig_datacon (_63_317, _63_319, _63_321, l, _63_324, quals, _63_327, _63_329) -> begin
(

let qopt = (FStar_Util.find_map quals (fun _63_8 -> (match (_63_8) with
| FStar_Syntax_Syntax.RecordConstructor (_63_334, fs) -> begin
Some (FStar_Syntax_Syntax.Record_ctor (((l), (fs))))
end
| _63_339 -> begin
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
| FStar_Syntax_Syntax.Sig_declare_typ (_63_344, _63_346, _63_348, quals, _63_351) -> begin
None
end
| _63_355 -> begin
None
end))


let lb_fv : FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.fv = (fun lbs lid -> (let _158_407 = (FStar_Util.find_map lbs (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in if (FStar_Syntax_Syntax.fv_eq_lid fv lid) then begin
Some (fv)
end else begin
None
end)))
in (FStar_All.pipe_right _158_407 FStar_Util.must)))


let ns_of_lid_equals : FStar_Ident.lident  ->  FStar_Ident.lident  ->  Prims.bool = (fun lid ns -> (((FStar_List.length lid.FStar_Ident.ns) = (FStar_List.length (FStar_Ident.ids_of_lid ns))) && (let _158_412 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in (FStar_Ident.lid_equals _158_412 ns))))


let try_lookup_name : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  foundname Prims.option = (fun any_val exclude_interf env lid -> (

let occurrence_range = (FStar_Ident.range_of_lid lid)
in (

let k_global_def = (fun source_lid _63_13 -> (match (_63_13) with
| (_63_371, true) when exclude_interf -> begin
None
end
| (se, _63_376) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_63_379) -> begin
(let _158_427 = (let _158_426 = (let _158_425 = (FStar_Syntax_Syntax.fvar source_lid FStar_Syntax_Syntax.Delta_constant None)
in ((_158_425), (false)))
in Term_name (_158_426))
in Some (_158_427))
end
| FStar_Syntax_Syntax.Sig_datacon (_63_382) -> begin
(let _158_431 = (let _158_430 = (let _158_429 = (let _158_428 = (fv_qual_of_se se)
in (FStar_Syntax_Syntax.fvar source_lid FStar_Syntax_Syntax.Delta_constant _158_428))
in ((_158_429), (false)))
in Term_name (_158_430))
in Some (_158_431))
end
| FStar_Syntax_Syntax.Sig_let ((_63_385, lbs), _63_389, _63_391, _63_393) -> begin
(

let fv = (lb_fv lbs source_lid)
in (let _158_434 = (let _158_433 = (let _158_432 = (FStar_Syntax_Syntax.fvar source_lid fv.FStar_Syntax_Syntax.fv_delta fv.FStar_Syntax_Syntax.fv_qual)
in ((_158_432), (false)))
in Term_name (_158_433))
in Some (_158_434)))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _63_399, _63_401, quals, _63_404) -> begin
if (any_val || (FStar_All.pipe_right quals (FStar_Util.for_some (fun _63_10 -> (match (_63_10) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| _63_410 -> begin
false
end))))) then begin
(

let lid = (FStar_Ident.set_lid_range lid (FStar_Ident.range_of_lid source_lid))
in (

let dd = if ((FStar_Syntax_Util.is_primop_lid lid) || ((ns_of_lid_equals lid FStar_Syntax_Const.prims_lid) && (FStar_All.pipe_right quals (FStar_Util.for_some (fun _63_11 -> (match (_63_11) with
| (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) -> begin
true
end
| _63_420 -> begin
false
end)))))) then begin
FStar_Syntax_Syntax.Delta_equational
end else begin
FStar_Syntax_Syntax.Delta_constant
end
in (match ((FStar_Util.find_map quals (fun _63_12 -> (match (_63_12) with
| FStar_Syntax_Syntax.Reflectable (refl_monad) -> begin
Some (refl_monad)
end
| _63_426 -> begin
None
end)))) with
| Some (refl_monad) -> begin
(

let refl_const = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (refl_monad))) None occurrence_range)
in Some (Term_name (((refl_const), (false)))))
end
| _63_431 -> begin
(let _158_441 = (let _158_440 = (let _158_439 = (let _158_438 = (fv_qual_of_se se)
in (FStar_Syntax_Syntax.fvar lid dd _158_438))
in ((_158_439), (false)))
in Term_name (_158_440))
in Some (_158_441))
end)))
end else begin
None
end
end
| (FStar_Syntax_Syntax.Sig_new_effect_for_free (ne, _)) | (FStar_Syntax_Syntax.Sig_new_effect (ne, _)) -> begin
Some (Eff_name (((se), ((FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname (FStar_Ident.range_of_lid source_lid))))))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (_63_442) -> begin
Some (Eff_name (((se), (source_lid))))
end
| _63_445 -> begin
None
end)
end))
in (

let k_local_binding = (fun r -> (let _158_445 = (let _158_444 = (found_local_binding (FStar_Ident.range_of_lid lid) r)
in Term_name (_158_444))
in Some (_158_445)))
in (

let k_rec_binding = (fun _63_452 -> (match (_63_452) with
| (id, l, dd) -> begin
(let _158_450 = (let _158_449 = (let _158_448 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range l (FStar_Ident.range_of_lid lid)) dd None)
in ((_158_448), (false)))
in Term_name (_158_449))
in Some (_158_450))
end))
in (

let found_unmangled = (match (lid.FStar_Ident.ns) with
| [] -> begin
(match ((unmangleOpName lid.FStar_Ident.ident)) with
| Some (f) -> begin
Some (Term_name (f))
end
| _63_457 -> begin
None
end)
end
| _63_459 -> begin
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
| _63_472 -> begin
None
end))


let try_lookup_effect_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env l -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some (o, l) -> begin
Some (l)
end
| _63_480 -> begin
None
end))


let try_lookup_effect_name_and_attributes : env  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.cflags Prims.list) Prims.option = (fun env l -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some (FStar_Syntax_Syntax.Sig_new_effect (ne, _63_485), l) -> begin
Some (((l), (ne.FStar_Syntax_Syntax.cattributes)))
end
| Some (FStar_Syntax_Syntax.Sig_new_effect_for_free (ne, _63_493), l) -> begin
Some (((l), (ne.FStar_Syntax_Syntax.cattributes)))
end
| Some (FStar_Syntax_Syntax.Sig_effect_abbrev (_63_500, _63_502, _63_504, _63_506, _63_508, cattributes, _63_511), l) -> begin
Some (((l), (cattributes)))
end
| _63_518 -> begin
None
end))


let try_lookup_effect_defn : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl Prims.option = (fun env l -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some (FStar_Syntax_Syntax.Sig_new_effect (ne, _63_523), _63_527) -> begin
Some (ne)
end
| Some (FStar_Syntax_Syntax.Sig_new_effect_for_free (ne, _63_532), _63_536) -> begin
Some (ne)
end
| _63_540 -> begin
None
end))


let is_effect_name : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((try_lookup_effect_name env lid)) with
| None -> begin
false
end
| Some (_63_545) -> begin
true
end))


let lookup_letbinding_quals : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.qualifier Prims.list = (fun env lid -> (

let k_global_def = (fun lid _63_14 -> (match (_63_14) with
| (FStar_Syntax_Syntax.Sig_declare_typ (lid, _63_554, _63_556, quals, _63_559), _63_563) -> begin
Some (quals)
end
| _63_566 -> begin
None
end))
in (match ((resolve_in_open_namespaces' env lid (fun _63_569 -> None) (fun _63_567 -> None) k_global_def)) with
| Some (quals) -> begin
quals
end
| _63_574 -> begin
[]
end)))


let try_lookup_module : env  ->  Prims.string Prims.list  ->  FStar_Syntax_Syntax.modul Prims.option = (fun env path -> (match ((FStar_List.tryFind (fun _63_579 -> (match (_63_579) with
| (mlid, modul) -> begin
((FStar_Ident.path_of_lid mlid) = path)
end)) env.modules)) with
| Some (_63_581, modul) -> begin
Some (modul)
end
| None -> begin
None
end))


let try_lookup_let : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env lid -> (

let k_global_def = (fun lid _63_15 -> (match (_63_15) with
| (FStar_Syntax_Syntax.Sig_let ((_63_592, lbs), _63_596, _63_598, _63_600), _63_604) -> begin
(

let fv = (lb_fv lbs lid)
in (let _158_496 = (FStar_Syntax_Syntax.fvar lid fv.FStar_Syntax_Syntax.fv_delta fv.FStar_Syntax_Syntax.fv_qual)
in Some (_158_496)))
end
| _63_608 -> begin
None
end))
in (resolve_in_open_namespaces' env lid (fun _63_611 -> None) (fun _63_609 -> None) k_global_def)))


let try_lookup_definition : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env lid -> (

let k_global_def = (fun lid _63_16 -> (match (_63_16) with
| (FStar_Syntax_Syntax.Sig_let (lbs, _63_620, _63_622, _63_624), _63_628) -> begin
(FStar_Util.find_map (Prims.snd lbs) (fun lb -> (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv lid) -> begin
Some (lb.FStar_Syntax_Syntax.lbdef)
end
| _63_634 -> begin
None
end)))
end
| _63_636 -> begin
None
end))
in (resolve_in_open_namespaces' env lid (fun _63_639 -> None) (fun _63_637 -> None) k_global_def)))


let try_lookup_lid' : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term * Prims.bool) Prims.option = (fun any_val exclude_interf env lid -> (match ((try_lookup_name any_val exclude_interf env lid)) with
| Some (Term_name (e, mut)) -> begin
Some (((e), (mut)))
end
| _63_651 -> begin
None
end))


let try_lookup_lid : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term * Prims.bool) Prims.option = (fun env l -> (try_lookup_lid' env.iface false env l))


let try_lookup_datacon : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.fv Prims.option = (fun env lid -> (

let k_global_def = (fun lid _63_18 -> (match (_63_18) with
| (FStar_Syntax_Syntax.Sig_declare_typ (_63_660, _63_662, _63_664, quals, _63_667), _63_671) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _63_17 -> (match (_63_17) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| _63_676 -> begin
false
end)))) then begin
(let _158_531 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant None)
in Some (_158_531))
end else begin
None
end
end
| (FStar_Syntax_Syntax.Sig_datacon (_63_678), _63_681) -> begin
(let _158_532 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in Some (_158_532))
end
| _63_684 -> begin
None
end))
in (resolve_in_open_namespaces' env lid (fun _63_687 -> None) (fun _63_685 -> None) k_global_def)))


let find_all_datacons : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.list Prims.option = (fun env lid -> (

let k_global_def = (fun lid _63_19 -> (match (_63_19) with
| (FStar_Syntax_Syntax.Sig_inductive_typ (_63_695, _63_697, _63_699, _63_701, _63_703, datas, _63_706, _63_708), _63_712) -> begin
Some (datas)
end
| _63_715 -> begin
None
end))
in (resolve_in_open_namespaces' env lid (fun _63_718 -> None) (fun _63_716 -> None) k_global_def)))


let record_cache_aux_with_filter : (((Prims.unit  ->  Prims.unit) * (Prims.unit  ->  Prims.unit) * (Prims.unit  ->  record_or_dc Prims.list) * (record_or_dc  ->  Prims.unit) * (Prims.unit  ->  Prims.unit)) * (Prims.unit  ->  Prims.unit)) = (

let record_cache = (FStar_Util.mk_ref (([])::[]))
in (

let push = (fun _63_722 -> (match (()) with
| () -> begin
(let _158_567 = (let _158_566 = (let _158_564 = (FStar_ST.read record_cache)
in (FStar_List.hd _158_564))
in (let _158_565 = (FStar_ST.read record_cache)
in (_158_566)::_158_565))
in (FStar_ST.op_Colon_Equals record_cache _158_567))
end))
in (

let pop = (fun _63_724 -> (match (()) with
| () -> begin
(let _158_571 = (let _158_570 = (FStar_ST.read record_cache)
in (FStar_List.tl _158_570))
in (FStar_ST.op_Colon_Equals record_cache _158_571))
end))
in (

let peek = (fun _63_726 -> (match (()) with
| () -> begin
(let _158_574 = (FStar_ST.read record_cache)
in (FStar_List.hd _158_574))
end))
in (

let insert = (fun r -> (let _158_581 = (let _158_580 = (let _158_577 = (peek ())
in (r)::_158_577)
in (let _158_579 = (let _158_578 = (FStar_ST.read record_cache)
in (FStar_List.tl _158_578))
in (_158_580)::_158_579))
in (FStar_ST.op_Colon_Equals record_cache _158_581)))
in (

let commit = (fun _63_730 -> (match (()) with
| () -> begin
(match ((FStar_ST.read record_cache)) with
| (hd)::(_63_733)::tl -> begin
(FStar_ST.op_Colon_Equals record_cache ((hd)::tl))
end
| _63_738 -> begin
(FStar_All.failwith "Impossible")
end)
end))
in (

let filter = (fun _63_740 -> (match (()) with
| () -> begin
(

let rc = (peek ())
in (

let _63_742 = (pop ())
in (match (()) with
| () -> begin
(

let filtered = (FStar_List.filter (fun r -> (not (r.is_private_or_abstract))) rc)
in (let _158_588 = (let _158_587 = (FStar_ST.read record_cache)
in (filtered)::_158_587)
in (FStar_ST.op_Colon_Equals record_cache _158_588)))
end)))
end))
in (

let aux = ((push), (pop), (peek), (insert), (commit))
in ((aux), (filter))))))))))


let record_cache_aux : ((Prims.unit  ->  Prims.unit) * (Prims.unit  ->  Prims.unit) * (Prims.unit  ->  record_or_dc Prims.list) * (record_or_dc  ->  Prims.unit) * (Prims.unit  ->  Prims.unit)) = (

let _63_749 = record_cache_aux_with_filter
in (match (_63_749) with
| (aux, _63_748) -> begin
aux
end))


let filter_record_cache : Prims.unit  ->  Prims.unit = (

let _63_753 = record_cache_aux_with_filter
in (match (_63_753) with
| (_63_751, filter) -> begin
filter
end))


let push_record_cache : Prims.unit  ->  Prims.unit = (

let _63_763 = record_cache_aux
in (match (_63_763) with
| (push, _63_756, _63_758, _63_760, _63_762) -> begin
push
end))


let pop_record_cache : Prims.unit  ->  Prims.unit = (

let _63_773 = record_cache_aux
in (match (_63_773) with
| (_63_765, pop, _63_768, _63_770, _63_772) -> begin
pop
end))


let peek_record_cache : Prims.unit  ->  record_or_dc Prims.list = (

let _63_783 = record_cache_aux
in (match (_63_783) with
| (_63_775, _63_777, peek, _63_780, _63_782) -> begin
peek
end))


let insert_record_cache : record_or_dc  ->  Prims.unit = (

let _63_793 = record_cache_aux
in (match (_63_793) with
| (_63_785, _63_787, _63_789, insert, _63_792) -> begin
insert
end))


let commit_record_cache : Prims.unit  ->  Prims.unit = (

let _63_803 = record_cache_aux
in (match (_63_803) with
| (_63_795, _63_797, _63_799, _63_801, commit) -> begin
commit
end))


let extract_record : env  ->  scope_mod Prims.list FStar_ST.ref  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun e new_globs _63_23 -> (match (_63_23) with
| FStar_Syntax_Syntax.Sig_bundle (sigs, _63_809, _63_811, _63_813) -> begin
(

let is_rec = (FStar_Util.for_some (fun _63_20 -> (match (_63_20) with
| (FStar_Syntax_Syntax.RecordType (_)) | (FStar_Syntax_Syntax.RecordConstructor (_)) -> begin
true
end
| _63_824 -> begin
false
end)))
in (

let find_dc = (fun dc -> (FStar_All.pipe_right sigs (FStar_Util.find_opt (fun _63_21 -> (match (_63_21) with
| FStar_Syntax_Syntax.Sig_datacon (lid, _63_831, _63_833, _63_835, _63_837, _63_839, _63_841, _63_843) -> begin
(FStar_Ident.lid_equals dc lid)
end
| _63_847 -> begin
false
end)))))
in (FStar_All.pipe_right sigs (FStar_List.iter (fun _63_22 -> (match (_63_22) with
| FStar_Syntax_Syntax.Sig_inductive_typ (typename, univs, parms, _63_853, _63_855, (dc)::[], tags, _63_860) -> begin
(match ((let _158_790 = (find_dc dc)
in (FStar_All.pipe_left FStar_Util.must _158_790))) with
| FStar_Syntax_Syntax.Sig_datacon (constrname, _63_865, t, _63_868, _63_870, _63_872, _63_874, _63_876) -> begin
(

let _63_882 = (FStar_Syntax_Util.arrow_formals t)
in (match (_63_882) with
| (formals, _63_881) -> begin
(

let is_rec = (is_rec tags)
in (

let fields = (FStar_All.pipe_right formals (FStar_List.collect (fun _63_886 -> (match (_63_886) with
| (x, q) -> begin
if ((FStar_Syntax_Syntax.is_null_bv x) || (is_rec && (FStar_Syntax_Syntax.is_implicit q))) then begin
[]
end else begin
(let _158_793 = (let _158_792 = if is_rec then begin
(FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname)
end else begin
x.FStar_Syntax_Syntax.ppname
end
in ((_158_792), (x.FStar_Syntax_Syntax.sort)))
in (_158_793)::[])
end
end))))
in (

let record = {typename = typename; constrname = constrname.FStar_Ident.ident; parms = parms; fields = fields; is_private_or_abstract = ((FStar_List.contains FStar_Syntax_Syntax.Private tags) || (FStar_List.contains FStar_Syntax_Syntax.Abstract tags)); is_record = is_rec}
in (

let _63_889 = (let _158_795 = (let _158_794 = (FStar_ST.read new_globs)
in (Record_or_dc (record))::_158_794)
in (FStar_ST.op_Colon_Equals new_globs _158_795))
in (match (()) with
| () -> begin
(insert_record_cache record)
end)))))
end))
end
| _63_891 -> begin
()
end)
end
| _63_893 -> begin
()
end))))))
end
| _63_895 -> begin
()
end))


let try_lookup_record_or_dc_by_field_name : env  ->  FStar_Ident.lident  ->  record_or_dc Prims.option = (fun env fieldname -> (

let find_in_cache = (fun fieldname -> (

let _63_902 = ((fieldname.FStar_Ident.ns), (fieldname.FStar_Ident.ident))
in (match (_63_902) with
| (ns, id) -> begin
(let _158_806 = (peek_record_cache ())
in (FStar_Util.find_map _158_806 (fun record -> (let _158_805 = (find_in_record ns id record (fun r -> Cont_ok (r)))
in (option_of_cont (fun _63_905 -> None) _158_805)))))
end)))
in (resolve_in_open_namespaces'' env fieldname (fun _63_915 -> Cont_ignore) (fun _63_913 -> Cont_ignore) (fun r -> Cont_ok (r)) (fun k fn -> (let _158_812 = (find_in_cache fn)
in (cont_of_option k _158_812))) (fun k _63_908 -> k))))


let try_lookup_record_by_field_name : env  ->  FStar_Ident.lident  ->  record_or_dc Prims.option = (fun env fieldname -> (match ((try_lookup_record_or_dc_by_field_name env fieldname)) with
| Some (r) when r.is_record -> begin
Some (r)
end
| _63_922 -> begin
None
end))


let belongs_to_record : env  ->  FStar_Ident.lident  ->  record_or_dc  ->  Prims.bool = (fun env lid record -> (match ((try_lookup_record_by_field_name env lid)) with
| Some (record') when ((let _158_825 = (FStar_Ident.path_of_ns record.typename.FStar_Ident.ns)
in (FStar_Ident.text_of_path _158_825)) = (let _158_826 = (FStar_Ident.path_of_ns record'.typename.FStar_Ident.ns)
in (FStar_Ident.text_of_path _158_826))) -> begin
(match ((find_in_record record.typename.FStar_Ident.ns lid.FStar_Ident.ident record (fun _63_928 -> Cont_ok (())))) with
| Cont_ok (_63_931) -> begin
true
end
| _63_934 -> begin
false
end)
end
| _63_936 -> begin
false
end))


let try_lookup_dc_by_field_name : env  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * Prims.bool) Prims.option = (fun env fieldname -> (match ((try_lookup_record_or_dc_by_field_name env fieldname)) with
| Some (r) -> begin
(let _158_834 = (let _158_833 = (let _158_832 = (FStar_Ident.lid_of_ids (FStar_List.append r.typename.FStar_Ident.ns ((r.constrname)::[])))
in (FStar_Ident.set_lid_range _158_832 (FStar_Ident.range_of_lid fieldname)))
in ((_158_833), (r.is_record)))
in Some (_158_834))
end
| _63_942 -> begin
None
end))


let unique : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  Prims.bool = (fun any_val exclude_if env lid -> (

let this_env = (

let _63_947 = env
in {curmodule = _63_947.curmodule; curmonad = _63_947.curmonad; modules = _63_947.modules; scope_mods = []; sigaccum = _63_947.sigaccum; sigmap = _63_947.sigmap; default_result_effect = _63_947.default_result_effect; iface = _63_947.iface; admitted_iface = _63_947.admitted_iface; expect_typ = _63_947.expect_typ})
in (match ((try_lookup_lid' any_val exclude_if env lid)) with
| None -> begin
true
end
| Some (_63_952) -> begin
false
end)))


let push_scope_mod : env  ->  scope_mod  ->  env = (fun env scope_mod -> (

let _63_956 = env
in {curmodule = _63_956.curmodule; curmonad = _63_956.curmonad; modules = _63_956.modules; scope_mods = (scope_mod)::env.scope_mods; sigaccum = _63_956.sigaccum; sigmap = _63_956.sigmap; default_result_effect = _63_956.default_result_effect; iface = _63_956.iface; admitted_iface = _63_956.admitted_iface; expect_typ = _63_956.expect_typ}))


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
| Some (se, _63_977) -> begin
(match ((let _158_873 = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_Util.find_opt (FStar_Ident.lid_equals l) _158_873))) with
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
in (let _158_876 = (let _158_875 = (let _158_874 = (FStar_Util.format2 "Duplicate top-level names [%s]; previously declared at %s" (FStar_Ident.text_of_lid l) r)
in ((_158_874), ((FStar_Ident.range_of_lid l))))
in FStar_Syntax_Syntax.Error (_158_875))
in (Prims.raise _158_876)))))
in (

let globals = (FStar_ST.alloc env.scope_mods)
in (

let env = (

let _63_996 = (match (s) with
| FStar_Syntax_Syntax.Sig_let (_63_987) -> begin
((false), (true))
end
| FStar_Syntax_Syntax.Sig_bundle (_63_990) -> begin
((true), (true))
end
| _63_993 -> begin
((false), (false))
end)
in (match (_63_996) with
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

let _63_1000 = (extract_record env globals s)
in (

let _63_1002 = env
in {curmodule = _63_1002.curmodule; curmonad = _63_1002.curmonad; modules = _63_1002.modules; scope_mods = _63_1002.scope_mods; sigaccum = (s)::env.sigaccum; sigmap = _63_1002.sigmap; default_result_effect = _63_1002.default_result_effect; iface = _63_1002.iface; admitted_iface = _63_1002.admitted_iface; expect_typ = _63_1002.expect_typ}))
end
| Some (l) -> begin
(err l)
end))
end))
in (

let env = (

let _63_1007 = env
in (let _158_878 = (FStar_ST.read globals)
in {curmodule = _63_1007.curmodule; curmonad = _63_1007.curmonad; modules = _63_1007.modules; scope_mods = _158_878; sigaccum = _63_1007.sigaccum; sigmap = _63_1007.sigmap; default_result_effect = _63_1007.default_result_effect; iface = _63_1007.iface; admitted_iface = _63_1007.admitted_iface; expect_typ = _63_1007.expect_typ}))
in (

let _63_1024 = (match (s) with
| FStar_Syntax_Syntax.Sig_bundle (ses, _63_1012, _63_1014, _63_1016) -> begin
(let _158_881 = (FStar_List.map (fun se -> (let _158_880 = (FStar_Syntax_Util.lids_of_sigelt se)
in ((_158_880), (se)))) ses)
in ((env), (_158_881)))
end
| _63_1021 -> begin
(let _158_884 = (let _158_883 = (let _158_882 = (FStar_Syntax_Util.lids_of_sigelt s)
in ((_158_882), (s)))
in (_158_883)::[])
in ((env), (_158_884)))
end)
in (match (_63_1024) with
| (env, lss) -> begin
(

let _63_1030 = (FStar_All.pipe_right lss (FStar_List.iter (fun _63_1027 -> (match (_63_1027) with
| (lids, se) -> begin
(FStar_All.pipe_right lids (FStar_List.iter (fun lid -> (

let _63_1029 = (let _158_888 = (let _158_887 = (FStar_ST.read globals)
in (Top_level_def (lid.FStar_Ident.ident))::_158_887)
in (FStar_ST.op_Colon_Equals globals _158_888))
in (match (()) with
| () -> begin
(FStar_Util.smap_add (sigmap env) lid.FStar_Ident.str ((se), ((env.iface && (not (env.admitted_iface))))))
end)))))
end))))
in (

let env = (

let _63_1032 = env
in (let _158_889 = (FStar_ST.read globals)
in {curmodule = _63_1032.curmodule; curmonad = _63_1032.curmonad; modules = _63_1032.modules; scope_mods = _158_889; sigaccum = _63_1032.sigaccum; sigmap = _63_1032.sigmap; default_result_effect = _63_1032.default_result_effect; iface = _63_1032.iface; admitted_iface = _63_1032.admitted_iface; expect_typ = _63_1032.expect_typ}))
in env))
end)))))))


let push_namespace : env  ->  FStar_Ident.lident  ->  env = (fun env ns -> (

let _63_1047 = (match ((resolve_module_name env ns false)) with
| None -> begin
(

let modules = env.modules
in if (FStar_All.pipe_right modules (FStar_Util.for_some (fun _63_1042 -> (match (_63_1042) with
| (m, _63_1041) -> begin
(FStar_Util.starts_with (Prims.strcat (FStar_Ident.text_of_lid m) ".") (Prims.strcat (FStar_Ident.text_of_lid ns) "."))
end)))) then begin
((ns), (Open_namespace))
end else begin
(let _158_897 = (let _158_896 = (let _158_895 = (FStar_Util.format1 "Namespace %s cannot be found" (FStar_Ident.text_of_lid ns))
in ((_158_895), ((FStar_Ident.range_of_lid ns))))
in FStar_Syntax_Syntax.Error (_158_896))
in (Prims.raise _158_897))
end)
end
| Some (ns') -> begin
((ns'), (Open_module))
end)
in (match (_63_1047) with
| (ns', kd) -> begin
(push_scope_mod env (Open_module_or_namespace (((ns'), (kd)))))
end)))


let push_module_abbrev : env  ->  FStar_Ident.ident  ->  FStar_Ident.lident  ->  env = (fun env x l -> if (module_is_defined env l) then begin
(push_scope_mod env (Module_abbrev (((x), (l)))))
end else begin
(let _158_906 = (let _158_905 = (let _158_904 = (FStar_Util.format1 "Module %s cannot be found" (FStar_Ident.text_of_lid l))
in ((_158_904), ((FStar_Ident.range_of_lid l))))
in FStar_Syntax_Syntax.Error (_158_905))
in (Prims.raise _158_906))
end)


let check_admits : env  ->  Prims.unit = (fun env -> (FStar_All.pipe_right env.sigaccum (FStar_List.iter (fun se -> (match (se) with
| FStar_Syntax_Syntax.Sig_declare_typ (l, u, t, quals, r) -> begin
(match ((try_lookup_lid env l)) with
| None -> begin
(

let _63_1061 = (let _158_912 = (let _158_911 = (FStar_Range.string_of_range (FStar_Ident.range_of_lid l))
in (let _158_910 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format2 "%s: Warning: Admitting %s without a definition\n" _158_911 _158_910)))
in (FStar_Util.print_string _158_912))
in (FStar_Util.smap_add (sigmap env) l.FStar_Ident.str ((FStar_Syntax_Syntax.Sig_declare_typ (((l), (u), (t), ((FStar_Syntax_Syntax.Assumption)::quals), (r)))), (false))))
end
| Some (_63_1064) -> begin
()
end)
end
| _63_1067 -> begin
()
end)))))


let finish : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env modul -> (

let _63_1127 = (FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations (FStar_List.iter (fun _63_25 -> (match (_63_25) with
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _63_1074, _63_1076) -> begin
if ((FStar_List.contains FStar_Syntax_Syntax.Private quals) || (FStar_List.contains FStar_Syntax_Syntax.Abstract quals)) then begin
(FStar_All.pipe_right ses (FStar_List.iter (fun _63_24 -> (match (_63_24) with
| FStar_Syntax_Syntax.Sig_datacon (lid, _63_1082, _63_1084, _63_1086, _63_1088, _63_1090, _63_1092, _63_1094) -> begin
(FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str)
end
| _63_1098 -> begin
()
end))))
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _63_1101, _63_1103, quals, _63_1106) -> begin
if (FStar_List.contains FStar_Syntax_Syntax.Private quals) then begin
(FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str)
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_let ((_63_1110, lbs), r, _63_1115, quals) -> begin
(

let _63_1120 = if ((FStar_List.contains FStar_Syntax_Syntax.Private quals) || (FStar_List.contains FStar_Syntax_Syntax.Abstract quals)) then begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (let _158_923 = (let _158_922 = (let _158_921 = (let _158_920 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _158_920.FStar_Syntax_Syntax.fv_name)
in _158_921.FStar_Syntax_Syntax.v)
in _158_922.FStar_Ident.str)
in (FStar_Util.smap_remove (sigmap env) _158_923)))))
end else begin
()
end
in if ((FStar_List.contains FStar_Syntax_Syntax.Abstract quals) && (not ((FStar_List.contains FStar_Syntax_Syntax.Private quals)))) then begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (

let lid = (let _158_926 = (let _158_925 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _158_925.FStar_Syntax_Syntax.fv_name)
in _158_926.FStar_Syntax_Syntax.v)
in (

let decl = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), ((FStar_Syntax_Syntax.Assumption)::quals), (r)))
in (FStar_Util.smap_add (sigmap env) lid.FStar_Ident.str ((decl), (false))))))))
end else begin
()
end)
end
| _63_1126 -> begin
()
end))))
in (

let _63_1129 = (filter_record_cache ())
in (match (()) with
| () -> begin
(

let _63_1130 = env
in {curmodule = None; curmonad = _63_1130.curmonad; modules = (((modul.FStar_Syntax_Syntax.name), (modul)))::env.modules; scope_mods = []; sigaccum = []; sigmap = _63_1130.sigmap; default_result_effect = _63_1130.default_result_effect; iface = _63_1130.iface; admitted_iface = _63_1130.admitted_iface; expect_typ = _63_1130.expect_typ})
end))))


type env_stack_ops =
{push : env  ->  env; mark : env  ->  env; reset_mark : env  ->  env; commit_mark : env  ->  env; pop : env  ->  env}


let is_Mkenv_stack_ops : env_stack_ops  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv_stack_ops"))))


let stack_ops : env_stack_ops = (

let stack = (FStar_Util.mk_ref [])
in (

let push = (fun env -> (

let _63_1141 = (push_record_cache ())
in (

let _63_1143 = (let _158_976 = (let _158_975 = (FStar_ST.read stack)
in (env)::_158_975)
in (FStar_ST.op_Colon_Equals stack _158_976))
in (

let _63_1145 = env
in (let _158_977 = (FStar_Util.smap_copy (sigmap env))
in {curmodule = _63_1145.curmodule; curmonad = _63_1145.curmonad; modules = _63_1145.modules; scope_mods = _63_1145.scope_mods; sigaccum = _63_1145.sigaccum; sigmap = _158_977; default_result_effect = _63_1145.default_result_effect; iface = _63_1145.iface; admitted_iface = _63_1145.admitted_iface; expect_typ = _63_1145.expect_typ})))))
in (

let pop = (fun env -> (match ((FStar_ST.read stack)) with
| (env)::tl -> begin
(

let _63_1152 = (pop_record_cache ())
in (

let _63_1154 = (FStar_ST.op_Colon_Equals stack tl)
in env))
end
| _63_1157 -> begin
(FStar_All.failwith "Impossible: Too many pops")
end))
in (

let commit_mark = (fun env -> (

let _63_1160 = (commit_record_cache ())
in (match ((FStar_ST.read stack)) with
| (_63_1164)::tl -> begin
(

let _63_1166 = (FStar_ST.op_Colon_Equals stack tl)
in env)
end
| _63_1169 -> begin
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
| (l)::_63_1180 -> begin
(l.FStar_Ident.nsstr = m.FStar_Ident.str)
end
| _63_1184 -> begin
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

let _63_1208 = (FStar_All.pipe_right keys (FStar_List.iter (fun k -> (match ((FStar_Util.smap_try_find sm' k)) with
| Some (se, true) when (sigelt_in_m se) -> begin
(

let _63_1194 = (FStar_Util.smap_remove sm' k)
in (

let se = (match (se) with
| FStar_Syntax_Syntax.Sig_declare_typ (l, u, t, q, r) -> begin
FStar_Syntax_Syntax.Sig_declare_typ (((l), (u), (t), ((FStar_Syntax_Syntax.Assumption)::q), (r)))
end
| _63_1204 -> begin
se
end)
in (FStar_Util.smap_add sm' k ((se), (false)))))
end
| _63_1207 -> begin
()
end))))
in env)))))))


let finish_module_or_interface : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env modul -> (

let _63_1212 = if (not (modul.FStar_Syntax_Syntax.is_interface)) then begin
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

let _63_1223 = env
in (let _158_1014 = (FStar_List.map (fun lid -> Open_module_or_namespace (((lid), (Open_namespace)))) open_ns)
in {curmodule = Some (mname); curmonad = _63_1223.curmonad; modules = _63_1223.modules; scope_mods = _158_1014; sigaccum = _63_1223.sigaccum; sigmap = env.sigmap; default_result_effect = if ((FStar_Ident.lid_equals mname FStar_Syntax_Const.all_lid) || (has_all_in_scope env)) then begin
FStar_Syntax_Const.effect_ML_lid
end else begin
FStar_Syntax_Const.effect_Tot_lid
end; iface = intf; admitted_iface = admitted; expect_typ = _63_1223.expect_typ})))))
in (match ((FStar_All.pipe_right env.modules (FStar_Util.find_opt (fun _63_1229 -> (match (_63_1229) with
| (l, _63_1228) -> begin
(FStar_Ident.lid_equals l mname)
end))))) with
| None -> begin
(let _158_1016 = (prep env)
in ((_158_1016), (false)))
end
| Some (_63_1232, m) -> begin
(

let _63_1236 = if ((not (m.FStar_Syntax_Syntax.is_interface)) || intf) then begin
(let _158_1019 = (let _158_1018 = (let _158_1017 = (FStar_Util.format1 "Duplicate module or interface name: %s" mname.FStar_Ident.str)
in ((_158_1017), ((FStar_Ident.range_of_lid mname))))
in FStar_Syntax_Syntax.Error (_158_1018))
in (Prims.raise _158_1019))
end else begin
()
end
in (let _158_1021 = (let _158_1020 = (push env)
in (prep _158_1020))
in ((_158_1021), (true))))
end)))


let enter_monad_scope : env  ->  FStar_Ident.ident  ->  env = (fun env mname -> (match (env.curmonad) with
| Some (mname') -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((((Prims.strcat "Trying to define monad " (Prims.strcat mname.FStar_Ident.idText (Prims.strcat ", but already in monad scope " mname'.FStar_Ident.idText)))), (mname.FStar_Ident.idRange)))))
end
| None -> begin
(

let _63_1243 = env
in {curmodule = _63_1243.curmodule; curmonad = Some (mname); modules = _63_1243.modules; scope_mods = _63_1243.scope_mods; sigaccum = _63_1243.sigaccum; sigmap = _63_1243.sigmap; default_result_effect = _63_1243.default_result_effect; iface = _63_1243.iface; admitted_iface = _63_1243.admitted_iface; expect_typ = _63_1243.expect_typ})
end))


let fail_or = (fun env lookup lid -> (match ((lookup lid)) with
| None -> begin
(

let opened_modules = (FStar_List.map (fun _63_1252 -> (match (_63_1252) with
| (lid, _63_1251) -> begin
(FStar_Ident.text_of_lid lid)
end)) env.modules)
in (

let msg = (FStar_Util.format1 "Identifier not found: [%s]" (FStar_Ident.text_of_lid lid))
in (

let msg = if ((FStar_List.length lid.FStar_Ident.ns) = (Prims.parse_int "0")) then begin
msg
end else begin
(

let modul = (let _158_1033 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in (FStar_Ident.set_lid_range _158_1033 (FStar_Ident.range_of_lid lid)))
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




