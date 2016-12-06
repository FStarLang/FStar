
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
{typename : FStar_Ident.lident; constrname : FStar_Ident.lident; parms : FStar_Syntax_Syntax.binders; fields : (FStar_Syntax_Syntax.fieldname * FStar_Syntax_Syntax.typ) Prims.list; is_record : Prims.bool}


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
| Local_binding (_63_34) -> begin
_63_34
end))


let ___Rec_binding____0 = (fun projectee -> (match (projectee) with
| Rec_binding (_63_37) -> begin
_63_37
end))


let ___Module_abbrev____0 = (fun projectee -> (match (projectee) with
| Module_abbrev (_63_40) -> begin
_63_40
end))


let ___Open_module_or_namespace____0 = (fun projectee -> (match (projectee) with
| Open_module_or_namespace (_63_43) -> begin
_63_43
end))


let ___Top_level_def____0 = (fun projectee -> (match (projectee) with
| Top_level_def (_63_46) -> begin
_63_46
end))


let ___Record_or_dc____0 = (fun projectee -> (match (projectee) with
| Record_or_dc (_63_49) -> begin
_63_49
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
| Term_name (_63_63) -> begin
_63_63
end))


let ___Eff_name____0 = (fun projectee -> (match (projectee) with
| Eff_name (_63_66) -> begin
_63_66
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
(let _158_172 = (current_module env)
in (qual _158_172 id))
end
| Some (monad) -> begin
(let _158_174 = (let _158_173 = (current_module env)
in (qual _158_173 monad))
in (FStar_Syntax_Util.mk_field_projector_name_from_ident _158_174 id))
end))


let new_sigmap = (fun _63_79 -> (match (()) with
| () -> begin
(FStar_Util.smap_create (Prims.parse_int "100"))
end))


let empty_env : Prims.unit  ->  env = (fun _63_80 -> (match (()) with
| () -> begin
(let _158_178 = (new_sigmap ())
in {curmodule = None; curmonad = None; modules = []; scope_mods = []; sigaccum = []; sigmap = _158_178; default_result_effect = FStar_Syntax_Const.effect_Tot_lid; iface = false; admitted_iface = false; expect_typ = false})
end))


let sigmap : env  ->  (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap = (fun env -> env.sigmap)


let has_all_in_scope : env  ->  Prims.bool = (fun env -> (FStar_List.existsb (fun _63_86 -> (match (_63_86) with
| (m, _63_85) -> begin
(FStar_Ident.lid_equals m FStar_Syntax_Const.all_lid)
end)) env.modules))


let default_total : env  ->  env = (fun env -> (

let _63_88 = env
in {curmodule = _63_88.curmodule; curmonad = _63_88.curmonad; modules = _63_88.modules; scope_mods = _63_88.scope_mods; sigaccum = _63_88.sigaccum; sigmap = _63_88.sigmap; default_result_effect = FStar_Syntax_Const.effect_Tot_lid; iface = _63_88.iface; admitted_iface = _63_88.admitted_iface; expect_typ = _63_88.expect_typ}))


let default_ml : env  ->  env = (fun env -> if (has_all_in_scope env) then begin
(

let _63_91 = env
in {curmodule = _63_91.curmodule; curmonad = _63_91.curmonad; modules = _63_91.modules; scope_mods = _63_91.scope_mods; sigaccum = _63_91.sigaccum; sigmap = _63_91.sigmap; default_result_effect = FStar_Syntax_Const.effect_ML_lid; iface = _63_91.iface; admitted_iface = _63_91.admitted_iface; expect_typ = _63_91.expect_typ})
end else begin
env
end)


let set_bv_range : FStar_Syntax_Syntax.bv  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.bv = (fun bv r -> (

let id = (

let _63_95 = bv.FStar_Syntax_Syntax.ppname
in {FStar_Ident.idText = _63_95.FStar_Ident.idText; FStar_Ident.idRange = r})
in (

let _63_98 = bv
in {FStar_Syntax_Syntax.ppname = id; FStar_Syntax_Syntax.index = _63_98.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _63_98.FStar_Syntax_Syntax.sort})))


let bv_to_name : FStar_Syntax_Syntax.bv  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.term = (fun bv r -> (FStar_Syntax_Syntax.bv_to_name (set_bv_range bv r)))


let unmangleMap : (Prims.string * Prims.string * FStar_Syntax_Syntax.delta_depth * FStar_Syntax_Syntax.fv_qual Prims.option) Prims.list = ((("op_ColonColon"), ("Cons"), (FStar_Syntax_Syntax.Delta_constant), (Some (FStar_Syntax_Syntax.Data_ctor))))::((("not"), ("op_Negation"), (FStar_Syntax_Syntax.Delta_equational), (None)))::[]


let unmangleOpName : FStar_Ident.ident  ->  (FStar_Syntax_Syntax.term * Prims.bool) Prims.option = (fun id -> (

let t = (FStar_Util.find_map unmangleMap (fun _63_107 -> (match (_63_107) with
| (x, y, dd, dq) -> begin
if (id.FStar_Ident.idText = x) then begin
(let _158_200 = (let _158_199 = (FStar_Ident.lid_of_path (("Prims")::(y)::[]) id.FStar_Ident.idRange)
in (FStar_Syntax_Syntax.fvar _158_199 dd dq))
in Some (_158_200))
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
| Cont_ok (_63_115) -> begin
_63_115
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

let needs_constrname = (not ((FStar_Syntax_Util.field_projector_contains_constructor id.FStar_Ident.idText)))
in (

let constrname = record.constrname.FStar_Ident.ident
in (

let fname = if needs_constrname then begin
(let _158_231 = (FStar_Ident.lid_of_ids (FStar_List.append ns ((constrname)::[])))
in (FStar_Syntax_Util.mk_field_projector_name_from_ident _158_231 id))
end else begin
(FStar_Ident.lid_of_ids (FStar_List.append ns ((id)::[])))
end
in (

let fname = (FStar_Ident.set_lid_range fname id.FStar_Ident.idRange)
in (

let find = (FStar_Util.find_map record.fields (fun _63_134 -> (match (_63_134) with
| (f, _63_133) -> begin
if (FStar_Ident.lid_equals fname f) then begin
Some (((record), (fname)))
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
end)))))))


let try_lookup_id'' = (fun env id k_local_binding k_rec_binding k_record find_in_module lookup_default_id -> (

let check_local_binding_id = (fun _63_2 -> (match (_63_2) with
| (id', _63_150, _63_152) -> begin
(id'.FStar_Ident.idText = id.FStar_Ident.idText)
end))
in (

let check_rec_binding_id = (fun _63_3 -> (match (_63_3) with
| (id', _63_158, _63_160) -> begin
(id'.FStar_Ident.idText = id.FStar_Ident.idText)
end))
in (

let curmod_ns = (let _158_262 = (current_module env)
in (FStar_Ident.ids_of_lid _158_262))
in (

let proc = (fun _63_4 -> (match (_63_4) with
| Local_binding (l) when (check_local_binding_id l) -> begin
(k_local_binding l)
end
| Rec_binding (r) when (check_rec_binding_id r) -> begin
(k_rec_binding r)
end
| Open_module_or_namespace (ns, _63_171) -> begin
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
| _63_180 -> begin
Cont_ignore
end))
in (

let rec aux = (fun _63_5 -> (match (_63_5) with
| (a)::q -> begin
(let _158_268 = (proc a)
in (option_of_cont (fun _63_187 -> (aux q)) _158_268))
end
| [] -> begin
(let _158_270 = (lookup_default_id Cont_fail id)
in (option_of_cont (fun _63_190 -> None) _158_270))
end))
in (aux env.scope_mods)))))))


let found_local_binding = (fun _63_195 -> (match (_63_195) with
| (id', x, mut) -> begin
(let _158_272 = (bv_to_name x id'.FStar_Ident.idRange)
in ((_158_272), (mut)))
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
(try_lookup_id'' env id (fun r -> (let _158_288 = (found_local_binding r)
in Cont_ok (_158_288))) (fun _63_220 -> Cont_fail) (fun _63_218 -> Cont_ignore) (fun i -> (find_in_module env i (fun _63_214 _63_216 -> Cont_fail) Cont_ignore)) (fun _63_209 _63_211 -> Cont_fail))
end))


let lookup_default_id = (fun env id k_global_def k_not_found -> (

let find_in_monad = (match (env.curmonad) with
| Some (_63_229) -> begin
(

let lid = (qualify env id)
in (match ((FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str)) with
| Some (r) -> begin
(let _158_306 = (k_global_def lid r)
in Some (_158_306))
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

let lid = (let _158_307 = (current_module env)
in (qual _158_307 id))
in (find_in_module env lid k_global_def k_not_found))
end)))


let module_is_defined : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> ((let _158_312 = (current_module env)
in (FStar_Ident.lid_equals lid _158_312)) || (FStar_List.existsb (fun x -> (FStar_Ident.lid_equals lid (Prims.fst x))) env.modules)))


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

let new_lid = (let _158_324 = (let _158_323 = (FStar_Ident.path_of_lid ns)
in (let _158_322 = (FStar_Ident.path_of_lid lid)
in (FStar_List.append _158_323 _158_322)))
in (FStar_Ident.lid_of_path _158_324 (FStar_Ident.range_of_lid lid)))
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
(match ((let _158_354 = (let _158_353 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in (FStar_Ident.set_lid_range _158_353 (FStar_Ident.range_of_lid lid)))
in (resolve_module_name env _158_354 true))) with
| None -> begin
None
end
| Some (modul) -> begin
(

let lid' = (qual modul lid.FStar_Ident.ident)
in (let _158_356 = (f_module Cont_fail lid')
in (option_of_cont (fun _63_286 -> None) _158_356)))
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

let k_global_def' = (fun k lid def -> (let _158_382 = (k_global_def lid def)
in (cont_of_option k _158_382)))
in (

let f_module = (fun k lid' -> (find_in_module env lid' (k_global_def' k) k))
in (

let l_default = (fun k i -> (lookup_default_id env i (k_global_def' k) k))
in (resolve_in_open_namespaces'' env lid (fun l -> (let _158_392 = (k_local_binding l)
in (cont_of_option Cont_fail _158_392))) (fun r -> (let _158_394 = (k_rec_binding r)
in (cont_of_option Cont_fail _158_394))) (fun _63_311 -> Cont_ignore) f_module l_default)))))


let fv_qual_of_se : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.fv_qual Prims.option = (fun _63_9 -> (match (_63_9) with
| FStar_Syntax_Syntax.Sig_datacon (_63_317, _63_319, _63_321, l, _63_324, quals, _63_327, _63_329) -> begin
(

let qopt = (FStar_Util.find_map quals (fun _63_8 -> (match (_63_8) with
| FStar_Syntax_Syntax.RecordConstructor (fs) -> begin
Some (FStar_Syntax_Syntax.Record_ctor (((l), (fs))))
end
| _63_336 -> begin
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
| FStar_Syntax_Syntax.Sig_declare_typ (_63_341, _63_343, _63_345, quals, _63_348) -> begin
None
end
| _63_352 -> begin
None
end))


let lb_fv : FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.fv = (fun lbs lid -> (let _158_404 = (FStar_Util.find_map lbs (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in if (FStar_Syntax_Syntax.fv_eq_lid fv lid) then begin
Some (fv)
end else begin
None
end)))
in (FStar_All.pipe_right _158_404 FStar_Util.must)))


let ns_of_lid_equals : FStar_Ident.lident  ->  FStar_Ident.lident  ->  Prims.bool = (fun lid ns -> (((FStar_List.length lid.FStar_Ident.ns) = (FStar_List.length (FStar_Ident.ids_of_lid ns))) && (let _158_409 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in (FStar_Ident.lid_equals _158_409 ns))))


let try_lookup_name : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  foundname Prims.option = (fun any_val exclude_interf env lid -> (

let occurrence_range = (FStar_Ident.range_of_lid lid)
in (

let k_global_def = (fun source_lid _63_13 -> (match (_63_13) with
| (_63_368, true) when exclude_interf -> begin
None
end
| (se, _63_373) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_63_376) -> begin
(let _158_424 = (let _158_423 = (let _158_422 = (FStar_Syntax_Syntax.fvar source_lid FStar_Syntax_Syntax.Delta_constant None)
in ((_158_422), (false)))
in Term_name (_158_423))
in Some (_158_424))
end
| FStar_Syntax_Syntax.Sig_datacon (_63_379) -> begin
(let _158_428 = (let _158_427 = (let _158_426 = (let _158_425 = (fv_qual_of_se se)
in (FStar_Syntax_Syntax.fvar source_lid FStar_Syntax_Syntax.Delta_constant _158_425))
in ((_158_426), (false)))
in Term_name (_158_427))
in Some (_158_428))
end
| FStar_Syntax_Syntax.Sig_let ((_63_382, lbs), _63_386, _63_388, _63_390) -> begin
(

let fv = (lb_fv lbs source_lid)
in (let _158_431 = (let _158_430 = (let _158_429 = (FStar_Syntax_Syntax.fvar source_lid fv.FStar_Syntax_Syntax.fv_delta fv.FStar_Syntax_Syntax.fv_qual)
in ((_158_429), (false)))
in Term_name (_158_430))
in Some (_158_431)))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _63_396, _63_398, quals, _63_401) -> begin
if (any_val || (FStar_All.pipe_right quals (FStar_Util.for_some (fun _63_10 -> (match (_63_10) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| _63_407 -> begin
false
end))))) then begin
(

let lid = (FStar_Ident.set_lid_range lid (FStar_Ident.range_of_lid source_lid))
in (

let dd = if ((FStar_Syntax_Util.is_primop_lid lid) || ((ns_of_lid_equals lid FStar_Syntax_Const.prims_lid) && (FStar_All.pipe_right quals (FStar_Util.for_some (fun _63_11 -> (match (_63_11) with
| (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) -> begin
true
end
| _63_417 -> begin
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
| _63_423 -> begin
None
end)))) with
| Some (refl_monad) -> begin
(

let refl_const = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (refl_monad))) None occurrence_range)
in Some (Term_name (((refl_const), (false)))))
end
| _63_428 -> begin
(let _158_438 = (let _158_437 = (let _158_436 = (let _158_435 = (fv_qual_of_se se)
in (FStar_Syntax_Syntax.fvar lid dd _158_435))
in ((_158_436), (false)))
in Term_name (_158_437))
in Some (_158_438))
end)))
end else begin
None
end
end
| (FStar_Syntax_Syntax.Sig_new_effect_for_free (ne, _)) | (FStar_Syntax_Syntax.Sig_new_effect (ne, _)) -> begin
Some (Eff_name (((se), ((FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname (FStar_Ident.range_of_lid source_lid))))))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (_63_439) -> begin
Some (Eff_name (((se), (source_lid))))
end
| _63_442 -> begin
None
end)
end))
in (

let k_local_binding = (fun r -> (let _158_442 = (let _158_441 = (found_local_binding r)
in Term_name (_158_441))
in Some (_158_442)))
in (

let k_rec_binding = (fun _63_449 -> (match (_63_449) with
| (id, l, dd) -> begin
(let _158_447 = (let _158_446 = (let _158_445 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range l (FStar_Ident.range_of_lid lid)) dd None)
in ((_158_445), (false)))
in Term_name (_158_446))
in Some (_158_447))
end))
in (

let found_unmangled = (match (lid.FStar_Ident.ns) with
| [] -> begin
(match ((unmangleOpName lid.FStar_Ident.ident)) with
| Some (f) -> begin
Some (Term_name (f))
end
| _63_454 -> begin
None
end)
end
| _63_456 -> begin
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
| _63_469 -> begin
None
end))


let try_lookup_effect_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env l -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some (o, l) -> begin
Some (l)
end
| _63_477 -> begin
None
end))


let try_lookup_effect_name_and_attributes : env  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.cflags Prims.list) Prims.option = (fun env l -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some (FStar_Syntax_Syntax.Sig_new_effect (ne, _63_482), l) -> begin
Some (((l), (ne.FStar_Syntax_Syntax.cattributes)))
end
| Some (FStar_Syntax_Syntax.Sig_new_effect_for_free (ne, _63_490), l) -> begin
Some (((l), (ne.FStar_Syntax_Syntax.cattributes)))
end
| Some (FStar_Syntax_Syntax.Sig_effect_abbrev (_63_497, _63_499, _63_501, _63_503, _63_505, cattributes, _63_508), l) -> begin
Some (((l), (cattributes)))
end
| _63_515 -> begin
None
end))


let try_lookup_effect_defn : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl Prims.option = (fun env l -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some (FStar_Syntax_Syntax.Sig_new_effect (ne, _63_520), _63_524) -> begin
Some (ne)
end
| Some (FStar_Syntax_Syntax.Sig_new_effect_for_free (ne, _63_529), _63_533) -> begin
Some (ne)
end
| _63_537 -> begin
None
end))


let is_effect_name : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((try_lookup_effect_name env lid)) with
| None -> begin
false
end
| Some (_63_542) -> begin
true
end))


let lookup_letbinding_quals : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.qualifier Prims.list = (fun env lid -> (

let k_global_def = (fun lid _63_14 -> (match (_63_14) with
| (FStar_Syntax_Syntax.Sig_declare_typ (lid, _63_551, _63_553, quals, _63_556), _63_560) -> begin
Some (quals)
end
| _63_563 -> begin
None
end))
in (match ((resolve_in_open_namespaces' env lid (fun _63_566 -> None) (fun _63_564 -> None) k_global_def)) with
| Some (quals) -> begin
quals
end
| _63_571 -> begin
[]
end)))


let try_lookup_module : env  ->  Prims.string Prims.list  ->  FStar_Syntax_Syntax.modul Prims.option = (fun env path -> (match ((FStar_List.tryFind (fun _63_576 -> (match (_63_576) with
| (mlid, modul) -> begin
((FStar_Ident.path_of_lid mlid) = path)
end)) env.modules)) with
| Some (_63_578, modul) -> begin
Some (modul)
end
| None -> begin
None
end))


let try_lookup_let : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env lid -> (

let k_global_def = (fun lid _63_15 -> (match (_63_15) with
| (FStar_Syntax_Syntax.Sig_let ((_63_589, lbs), _63_593, _63_595, _63_597), _63_601) -> begin
(

let fv = (lb_fv lbs lid)
in (let _158_493 = (FStar_Syntax_Syntax.fvar lid fv.FStar_Syntax_Syntax.fv_delta fv.FStar_Syntax_Syntax.fv_qual)
in Some (_158_493)))
end
| _63_605 -> begin
None
end))
in (resolve_in_open_namespaces' env lid (fun _63_608 -> None) (fun _63_606 -> None) k_global_def)))


let try_lookup_definition : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env lid -> (

let k_global_def = (fun lid _63_16 -> (match (_63_16) with
| (FStar_Syntax_Syntax.Sig_let (lbs, _63_617, _63_619, _63_621), _63_625) -> begin
(FStar_Util.find_map (Prims.snd lbs) (fun lb -> (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv lid) -> begin
Some (lb.FStar_Syntax_Syntax.lbdef)
end
| _63_631 -> begin
None
end)))
end
| _63_633 -> begin
None
end))
in (resolve_in_open_namespaces' env lid (fun _63_636 -> None) (fun _63_634 -> None) k_global_def)))


let try_lookup_lid' : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term * Prims.bool) Prims.option = (fun any_val exclude_interf env lid -> (match ((try_lookup_name any_val exclude_interf env lid)) with
| Some (Term_name (e, mut)) -> begin
Some (((e), (mut)))
end
| _63_648 -> begin
None
end))


let try_lookup_lid : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term * Prims.bool) Prims.option = (fun env l -> (try_lookup_lid' env.iface false env l))


let try_lookup_datacon : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.fv Prims.option = (fun env lid -> (

let k_global_def = (fun lid _63_18 -> (match (_63_18) with
| (FStar_Syntax_Syntax.Sig_declare_typ (_63_657, _63_659, _63_661, quals, _63_664), _63_668) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _63_17 -> (match (_63_17) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| _63_673 -> begin
false
end)))) then begin
(let _158_528 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant None)
in Some (_158_528))
end else begin
None
end
end
| (FStar_Syntax_Syntax.Sig_datacon (_63_675), _63_678) -> begin
(let _158_529 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in Some (_158_529))
end
| _63_681 -> begin
None
end))
in (resolve_in_open_namespaces' env lid (fun _63_684 -> None) (fun _63_682 -> None) k_global_def)))


let find_all_datacons : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.list Prims.option = (fun env lid -> (

let k_global_def = (fun lid _63_19 -> (match (_63_19) with
| (FStar_Syntax_Syntax.Sig_inductive_typ (_63_692, _63_694, _63_696, _63_698, _63_700, datas, _63_703, _63_705), _63_709) -> begin
Some (datas)
end
| _63_712 -> begin
None
end))
in (resolve_in_open_namespaces' env lid (fun _63_715 -> None) (fun _63_713 -> None) k_global_def)))


let record_cache_aux : ((Prims.unit  ->  Prims.unit) * (Prims.unit  ->  Prims.unit) * (Prims.unit  ->  record_or_dc Prims.list) * (record_or_dc  ->  Prims.unit) * (Prims.unit  ->  Prims.unit)) = (

let record_cache = (FStar_Util.mk_ref (([])::[]))
in (

let push = (fun _63_719 -> (match (()) with
| () -> begin
(let _158_557 = (let _158_556 = (let _158_554 = (FStar_ST.read record_cache)
in (FStar_List.hd _158_554))
in (let _158_555 = (FStar_ST.read record_cache)
in (_158_556)::_158_555))
in (FStar_ST.op_Colon_Equals record_cache _158_557))
end))
in (

let pop = (fun _63_721 -> (match (()) with
| () -> begin
(let _158_561 = (let _158_560 = (FStar_ST.read record_cache)
in (FStar_List.tl _158_560))
in (FStar_ST.op_Colon_Equals record_cache _158_561))
end))
in (

let peek = (fun _63_723 -> (match (()) with
| () -> begin
(let _158_564 = (FStar_ST.read record_cache)
in (FStar_List.hd _158_564))
end))
in (

let insert = (fun r -> (let _158_571 = (let _158_570 = (let _158_567 = (peek ())
in (r)::_158_567)
in (let _158_569 = (let _158_568 = (FStar_ST.read record_cache)
in (FStar_List.tl _158_568))
in (_158_570)::_158_569))
in (FStar_ST.op_Colon_Equals record_cache _158_571)))
in (

let commit = (fun _63_727 -> (match (()) with
| () -> begin
(match ((FStar_ST.read record_cache)) with
| (hd)::(_63_730)::tl -> begin
(FStar_ST.op_Colon_Equals record_cache ((hd)::tl))
end
| _63_735 -> begin
(FStar_All.failwith "Impossible")
end)
end))
in ((push), (pop), (peek), (insert), (commit))))))))


let push_record_cache : Prims.unit  ->  Prims.unit = (

let _63_745 = record_cache_aux
in (match (_63_745) with
| (push, _63_738, _63_740, _63_742, _63_744) -> begin
push
end))


let pop_record_cache : Prims.unit  ->  Prims.unit = (

let _63_755 = record_cache_aux
in (match (_63_755) with
| (_63_747, pop, _63_750, _63_752, _63_754) -> begin
pop
end))


let peek_record_cache : Prims.unit  ->  record_or_dc Prims.list = (

let _63_765 = record_cache_aux
in (match (_63_765) with
| (_63_757, _63_759, peek, _63_762, _63_764) -> begin
peek
end))


let insert_record_cache : record_or_dc  ->  Prims.unit = (

let _63_775 = record_cache_aux
in (match (_63_775) with
| (_63_767, _63_769, _63_771, insert, _63_774) -> begin
insert
end))


let commit_record_cache : Prims.unit  ->  Prims.unit = (

let _63_785 = record_cache_aux
in (match (_63_785) with
| (_63_777, _63_779, _63_781, _63_783, commit) -> begin
commit
end))


let extract_record : env  ->  scope_mod Prims.list FStar_ST.ref  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun e new_globs _63_23 -> (match (_63_23) with
| FStar_Syntax_Syntax.Sig_bundle (sigs, _63_791, _63_793, _63_795) -> begin
(

let is_rec = (FStar_Util.for_some (fun _63_20 -> (match (_63_20) with
| (FStar_Syntax_Syntax.RecordType (_)) | (FStar_Syntax_Syntax.RecordConstructor (_)) -> begin
true
end
| _63_806 -> begin
false
end)))
in (

let find_dc = (fun dc -> (FStar_All.pipe_right sigs (FStar_Util.find_opt (fun _63_21 -> (match (_63_21) with
| FStar_Syntax_Syntax.Sig_datacon (lid, _63_813, _63_815, _63_817, _63_819, _63_821, _63_823, _63_825) -> begin
(FStar_Ident.lid_equals dc lid)
end
| _63_829 -> begin
false
end)))))
in (FStar_All.pipe_right sigs (FStar_List.iter (fun _63_22 -> (match (_63_22) with
| FStar_Syntax_Syntax.Sig_inductive_typ (typename, univs, parms, _63_835, _63_837, (dc)::[], tags, _63_842) -> begin
(match ((let _158_676 = (find_dc dc)
in (FStar_All.pipe_left FStar_Util.must _158_676))) with
| FStar_Syntax_Syntax.Sig_datacon (constrname, _63_847, t, _63_850, _63_852, _63_854, _63_856, _63_858) -> begin
(

let _63_864 = (FStar_Syntax_Util.arrow_formals t)
in (match (_63_864) with
| (formals, _63_863) -> begin
(

let is_rec = (is_rec tags)
in (

let fields = (FStar_All.pipe_right formals (FStar_List.collect (fun _63_868 -> (match (_63_868) with
| (x, q) -> begin
if ((FStar_Syntax_Syntax.is_null_bv x) || (is_rec && (FStar_Syntax_Syntax.is_implicit q))) then begin
[]
end else begin
(let _158_680 = (let _158_679 = (let _158_678 = if is_rec then begin
(FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname)
end else begin
x.FStar_Syntax_Syntax.ppname
end
in (FStar_Syntax_Util.mk_field_projector_name_from_ident constrname _158_678))
in ((_158_679), (x.FStar_Syntax_Syntax.sort)))
in (_158_680)::[])
end
end))))
in (

let record = {typename = typename; constrname = constrname; parms = parms; fields = fields; is_record = is_rec}
in (

let _63_871 = (let _158_682 = (let _158_681 = (FStar_ST.read new_globs)
in (Record_or_dc (record))::_158_681)
in (FStar_ST.op_Colon_Equals new_globs _158_682))
in (match (()) with
| () -> begin
(insert_record_cache record)
end)))))
end))
end
| _63_873 -> begin
()
end)
end
| _63_875 -> begin
()
end))))))
end
| _63_877 -> begin
()
end))


let try_lookup_record_or_dc_by_field_name : env  ->  FStar_Ident.lident  ->  (record_or_dc * FStar_Syntax_Syntax.fieldname) Prims.option = (fun env fieldname -> (

let needs_constrname = (not ((FStar_Syntax_Util.field_projector_contains_constructor fieldname.FStar_Ident.ident.FStar_Ident.idText)))
in (

let find_in_cache = (fun fieldname -> (

let _63_885 = ((fieldname.FStar_Ident.ns), (fieldname.FStar_Ident.ident))
in (match (_63_885) with
| (ns, id) -> begin
(let _158_693 = (peek_record_cache ())
in (FStar_Util.find_map _158_693 (fun record -> (let _158_692 = (find_in_record ns id record (fun r -> Cont_ok (r)))
in (option_of_cont (fun _63_888 -> None) _158_692)))))
end)))
in (resolve_in_open_namespaces'' env fieldname (fun _63_898 -> Cont_ignore) (fun _63_896 -> Cont_ignore) (fun r -> Cont_ok (r)) (fun k fn -> (let _158_699 = (find_in_cache fn)
in (cont_of_option k _158_699))) (fun k _63_891 -> k)))))


let try_lookup_record_by_field_name : env  ->  FStar_Ident.lident  ->  (record_or_dc * FStar_Ident.lident) Prims.option = (fun env fieldname -> (match ((try_lookup_record_or_dc_by_field_name env fieldname)) with
| Some (r, f) when r.is_record -> begin
Some (((r), (f)))
end
| _63_907 -> begin
None
end))


let try_lookup_projector_by_field_name : env  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * Prims.bool) Prims.option = (fun env fieldname -> (match ((try_lookup_record_or_dc_by_field_name env fieldname)) with
| Some (r, f) -> begin
Some (((f), (r.is_record)))
end
| _63_915 -> begin
None
end))


let qualify_field_to_record : env  ->  record_or_dc  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env recd f -> (

let qualify = (fun fieldname -> (

let _63_923 = ((fieldname.FStar_Ident.ns), (fieldname.FStar_Ident.ident))
in (match (_63_923) with
| (ns, fieldname) -> begin
(

let constrname = recd.constrname.FStar_Ident.ident
in (

let fname = (let _158_718 = (FStar_Ident.lid_of_ids (FStar_List.append ns ((constrname)::[])))
in (FStar_Syntax_Util.mk_field_projector_name_from_ident _158_718 fieldname))
in (FStar_Util.find_map recd.fields (fun _63_929 -> (match (_63_929) with
| (f, _63_928) -> begin
if (FStar_Ident.lid_equals fname f) then begin
Some (fname)
end else begin
None
end
end)))))
end)))
in (resolve_in_open_namespaces'' env f (fun _63_938 -> Cont_ignore) (fun _63_936 -> Cont_ignore) (fun r -> Cont_ok ((Prims.snd r))) (fun k fn -> (let _158_725 = (qualify fn)
in (cont_of_option k _158_725))) (fun k _63_931 -> k))))


let unique : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  Prims.bool = (fun any_val exclude_if env lid -> (

let this_env = (

let _63_944 = env
in {curmodule = _63_944.curmodule; curmonad = _63_944.curmonad; modules = _63_944.modules; scope_mods = []; sigaccum = _63_944.sigaccum; sigmap = _63_944.sigmap; default_result_effect = _63_944.default_result_effect; iface = _63_944.iface; admitted_iface = _63_944.admitted_iface; expect_typ = _63_944.expect_typ})
in (match ((try_lookup_lid' any_val exclude_if env lid)) with
| None -> begin
true
end
| Some (_63_949) -> begin
false
end)))


let push_scope_mod : env  ->  scope_mod  ->  env = (fun env scope_mod -> (

let _63_953 = env
in {curmodule = _63_953.curmodule; curmonad = _63_953.curmonad; modules = _63_953.modules; scope_mods = (scope_mod)::env.scope_mods; sigaccum = _63_953.sigaccum; sigmap = _63_953.sigmap; default_result_effect = _63_953.default_result_effect; iface = _63_953.iface; admitted_iface = _63_953.admitted_iface; expect_typ = _63_953.expect_typ}))


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
| Some (se, _63_974) -> begin
(match ((let _158_766 = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_Util.find_opt (FStar_Ident.lid_equals l) _158_766))) with
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
in (let _158_769 = (let _158_768 = (let _158_767 = (FStar_Util.format2 "Duplicate top-level names [%s]; previously declared at %s" (FStar_Ident.text_of_lid l) r)
in ((_158_767), ((FStar_Ident.range_of_lid l))))
in FStar_Syntax_Syntax.Error (_158_768))
in (Prims.raise _158_769)))))
in (

let globals = (FStar_ST.alloc env.scope_mods)
in (

let env = (

let _63_993 = (match (s) with
| FStar_Syntax_Syntax.Sig_let (_63_984) -> begin
((false), (true))
end
| FStar_Syntax_Syntax.Sig_bundle (_63_987) -> begin
((true), (true))
end
| _63_990 -> begin
((false), (false))
end)
in (match (_63_993) with
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

let _63_997 = (extract_record env globals s)
in (

let _63_999 = env
in {curmodule = _63_999.curmodule; curmonad = _63_999.curmonad; modules = _63_999.modules; scope_mods = _63_999.scope_mods; sigaccum = (s)::env.sigaccum; sigmap = _63_999.sigmap; default_result_effect = _63_999.default_result_effect; iface = _63_999.iface; admitted_iface = _63_999.admitted_iface; expect_typ = _63_999.expect_typ}))
end
| Some (l) -> begin
(err l)
end))
end))
in (

let env = (

let _63_1004 = env
in (let _158_771 = (FStar_ST.read globals)
in {curmodule = _63_1004.curmodule; curmonad = _63_1004.curmonad; modules = _63_1004.modules; scope_mods = _158_771; sigaccum = _63_1004.sigaccum; sigmap = _63_1004.sigmap; default_result_effect = _63_1004.default_result_effect; iface = _63_1004.iface; admitted_iface = _63_1004.admitted_iface; expect_typ = _63_1004.expect_typ}))
in (

let _63_1021 = (match (s) with
| FStar_Syntax_Syntax.Sig_bundle (ses, _63_1009, _63_1011, _63_1013) -> begin
(let _158_774 = (FStar_List.map (fun se -> (let _158_773 = (FStar_Syntax_Util.lids_of_sigelt se)
in ((_158_773), (se)))) ses)
in ((env), (_158_774)))
end
| _63_1018 -> begin
(let _158_777 = (let _158_776 = (let _158_775 = (FStar_Syntax_Util.lids_of_sigelt s)
in ((_158_775), (s)))
in (_158_776)::[])
in ((env), (_158_777)))
end)
in (match (_63_1021) with
| (env, lss) -> begin
(

let _63_1027 = (FStar_All.pipe_right lss (FStar_List.iter (fun _63_1024 -> (match (_63_1024) with
| (lids, se) -> begin
(FStar_All.pipe_right lids (FStar_List.iter (fun lid -> (

let _63_1026 = (let _158_781 = (let _158_780 = (FStar_ST.read globals)
in (Top_level_def (lid.FStar_Ident.ident))::_158_780)
in (FStar_ST.op_Colon_Equals globals _158_781))
in (match (()) with
| () -> begin
(FStar_Util.smap_add (sigmap env) lid.FStar_Ident.str ((se), ((env.iface && (not (env.admitted_iface))))))
end)))))
end))))
in (

let env = (

let _63_1029 = env
in (let _158_782 = (FStar_ST.read globals)
in {curmodule = _63_1029.curmodule; curmonad = _63_1029.curmonad; modules = _63_1029.modules; scope_mods = _158_782; sigaccum = _63_1029.sigaccum; sigmap = _63_1029.sigmap; default_result_effect = _63_1029.default_result_effect; iface = _63_1029.iface; admitted_iface = _63_1029.admitted_iface; expect_typ = _63_1029.expect_typ}))
in env))
end)))))))


let push_namespace : env  ->  FStar_Ident.lident  ->  env = (fun env ns -> (

let _63_1044 = (match ((resolve_module_name env ns false)) with
| None -> begin
(

let modules = env.modules
in if (FStar_All.pipe_right modules (FStar_Util.for_some (fun _63_1039 -> (match (_63_1039) with
| (m, _63_1038) -> begin
(FStar_Util.starts_with (Prims.strcat (FStar_Ident.text_of_lid m) ".") (Prims.strcat (FStar_Ident.text_of_lid ns) "."))
end)))) then begin
((ns), (Open_namespace))
end else begin
(let _158_790 = (let _158_789 = (let _158_788 = (FStar_Util.format1 "Namespace %s cannot be found" (FStar_Ident.text_of_lid ns))
in ((_158_788), ((FStar_Ident.range_of_lid ns))))
in FStar_Syntax_Syntax.Error (_158_789))
in (Prims.raise _158_790))
end)
end
| Some (ns') -> begin
((ns'), (Open_module))
end)
in (match (_63_1044) with
| (ns', kd) -> begin
(push_scope_mod env (Open_module_or_namespace (((ns'), (kd)))))
end)))


let push_module_abbrev : env  ->  FStar_Ident.ident  ->  FStar_Ident.lident  ->  env = (fun env x l -> if (module_is_defined env l) then begin
(push_scope_mod env (Module_abbrev (((x), (l)))))
end else begin
(let _158_799 = (let _158_798 = (let _158_797 = (FStar_Util.format1 "Module %s cannot be found" (FStar_Ident.text_of_lid l))
in ((_158_797), ((FStar_Ident.range_of_lid l))))
in FStar_Syntax_Syntax.Error (_158_798))
in (Prims.raise _158_799))
end)


let check_admits : env  ->  Prims.unit = (fun env -> (FStar_All.pipe_right env.sigaccum (FStar_List.iter (fun se -> (match (se) with
| FStar_Syntax_Syntax.Sig_declare_typ (l, u, t, quals, r) -> begin
(match ((try_lookup_lid env l)) with
| None -> begin
(

let _63_1058 = (let _158_805 = (let _158_804 = (FStar_Range.string_of_range (FStar_Ident.range_of_lid l))
in (let _158_803 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format2 "%s: Warning: Admitting %s without a definition\n" _158_804 _158_803)))
in (FStar_Util.print_string _158_805))
in (FStar_Util.smap_add (sigmap env) l.FStar_Ident.str ((FStar_Syntax_Syntax.Sig_declare_typ (((l), (u), (t), ((FStar_Syntax_Syntax.Assumption)::quals), (r)))), (false))))
end
| Some (_63_1061) -> begin
()
end)
end
| _63_1064 -> begin
()
end)))))


let finish : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env modul -> (

let _63_1124 = (FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations (FStar_List.iter (fun _63_25 -> (match (_63_25) with
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _63_1071, _63_1073) -> begin
if ((FStar_List.contains FStar_Syntax_Syntax.Private quals) || (FStar_List.contains FStar_Syntax_Syntax.Abstract quals)) then begin
(FStar_All.pipe_right ses (FStar_List.iter (fun _63_24 -> (match (_63_24) with
| FStar_Syntax_Syntax.Sig_datacon (lid, _63_1079, _63_1081, _63_1083, _63_1085, _63_1087, _63_1089, _63_1091) -> begin
(FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str)
end
| _63_1095 -> begin
()
end))))
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _63_1098, _63_1100, quals, _63_1103) -> begin
if (FStar_List.contains FStar_Syntax_Syntax.Private quals) then begin
(FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str)
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_let ((_63_1107, lbs), r, _63_1112, quals) -> begin
(

let _63_1117 = if ((FStar_List.contains FStar_Syntax_Syntax.Private quals) || (FStar_List.contains FStar_Syntax_Syntax.Abstract quals)) then begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (let _158_816 = (let _158_815 = (let _158_814 = (let _158_813 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _158_813.FStar_Syntax_Syntax.fv_name)
in _158_814.FStar_Syntax_Syntax.v)
in _158_815.FStar_Ident.str)
in (FStar_Util.smap_remove (sigmap env) _158_816)))))
end else begin
()
end
in if ((FStar_List.contains FStar_Syntax_Syntax.Abstract quals) && (not ((FStar_List.contains FStar_Syntax_Syntax.Private quals)))) then begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (

let lid = (let _158_819 = (let _158_818 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _158_818.FStar_Syntax_Syntax.fv_name)
in _158_819.FStar_Syntax_Syntax.v)
in (

let decl = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), ((FStar_Syntax_Syntax.Assumption)::quals), (r)))
in (FStar_Util.smap_add (sigmap env) lid.FStar_Ident.str ((decl), (false))))))))
end else begin
()
end)
end
| _63_1123 -> begin
()
end))))
in (

let _63_1126 = env
in {curmodule = None; curmonad = _63_1126.curmonad; modules = (((modul.FStar_Syntax_Syntax.name), (modul)))::env.modules; scope_mods = []; sigaccum = []; sigmap = _63_1126.sigmap; default_result_effect = _63_1126.default_result_effect; iface = _63_1126.iface; admitted_iface = _63_1126.admitted_iface; expect_typ = _63_1126.expect_typ})))


type env_stack_ops =
{push : env  ->  env; mark : env  ->  env; reset_mark : env  ->  env; commit_mark : env  ->  env; pop : env  ->  env}


let is_Mkenv_stack_ops : env_stack_ops  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv_stack_ops"))))


let stack_ops : env_stack_ops = (

let stack = (FStar_Util.mk_ref [])
in (

let push = (fun env -> (

let _63_1137 = (push_record_cache ())
in (

let _63_1139 = (let _158_869 = (let _158_868 = (FStar_ST.read stack)
in (env)::_158_868)
in (FStar_ST.op_Colon_Equals stack _158_869))
in (

let _63_1141 = env
in (let _158_870 = (FStar_Util.smap_copy (sigmap env))
in {curmodule = _63_1141.curmodule; curmonad = _63_1141.curmonad; modules = _63_1141.modules; scope_mods = _63_1141.scope_mods; sigaccum = _63_1141.sigaccum; sigmap = _158_870; default_result_effect = _63_1141.default_result_effect; iface = _63_1141.iface; admitted_iface = _63_1141.admitted_iface; expect_typ = _63_1141.expect_typ})))))
in (

let pop = (fun env -> (match ((FStar_ST.read stack)) with
| (env)::tl -> begin
(

let _63_1148 = (pop_record_cache ())
in (

let _63_1150 = (FStar_ST.op_Colon_Equals stack tl)
in env))
end
| _63_1153 -> begin
(FStar_All.failwith "Impossible: Too many pops")
end))
in (

let commit_mark = (fun env -> (

let _63_1156 = (commit_record_cache ())
in (match ((FStar_ST.read stack)) with
| (_63_1160)::tl -> begin
(

let _63_1162 = (FStar_ST.op_Colon_Equals stack tl)
in env)
end
| _63_1165 -> begin
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
| (l)::_63_1176 -> begin
(l.FStar_Ident.nsstr = m.FStar_Ident.str)
end
| _63_1180 -> begin
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

let _63_1204 = (FStar_All.pipe_right keys (FStar_List.iter (fun k -> (match ((FStar_Util.smap_try_find sm' k)) with
| Some (se, true) when (sigelt_in_m se) -> begin
(

let _63_1190 = (FStar_Util.smap_remove sm' k)
in (

let se = (match (se) with
| FStar_Syntax_Syntax.Sig_declare_typ (l, u, t, q, r) -> begin
FStar_Syntax_Syntax.Sig_declare_typ (((l), (u), (t), ((FStar_Syntax_Syntax.Assumption)::q), (r)))
end
| _63_1200 -> begin
se
end)
in (FStar_Util.smap_add sm' k ((se), (false)))))
end
| _63_1203 -> begin
()
end))))
in env)))))))


let finish_module_or_interface : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env modul -> (

let _63_1208 = if (not (modul.FStar_Syntax_Syntax.is_interface)) then begin
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

let _63_1219 = env
in (let _158_907 = (FStar_List.map (fun lid -> Open_module_or_namespace (((lid), (Open_namespace)))) open_ns)
in {curmodule = Some (mname); curmonad = _63_1219.curmonad; modules = _63_1219.modules; scope_mods = _158_907; sigaccum = _63_1219.sigaccum; sigmap = env.sigmap; default_result_effect = if ((FStar_Ident.lid_equals mname FStar_Syntax_Const.all_lid) || (has_all_in_scope env)) then begin
FStar_Syntax_Const.effect_ML_lid
end else begin
FStar_Syntax_Const.effect_Tot_lid
end; iface = intf; admitted_iface = admitted; expect_typ = _63_1219.expect_typ})))))
in (match ((FStar_All.pipe_right env.modules (FStar_Util.find_opt (fun _63_1225 -> (match (_63_1225) with
| (l, _63_1224) -> begin
(FStar_Ident.lid_equals l mname)
end))))) with
| None -> begin
(let _158_909 = (prep env)
in ((_158_909), (false)))
end
| Some (_63_1228, m) -> begin
(

let _63_1232 = if ((not (m.FStar_Syntax_Syntax.is_interface)) || intf) then begin
(let _158_912 = (let _158_911 = (let _158_910 = (FStar_Util.format1 "Duplicate module or interface name: %s" mname.FStar_Ident.str)
in ((_158_910), ((FStar_Ident.range_of_lid mname))))
in FStar_Syntax_Syntax.Error (_158_911))
in (Prims.raise _158_912))
end else begin
()
end
in (let _158_914 = (let _158_913 = (push env)
in (prep _158_913))
in ((_158_914), (true))))
end)))


let enter_monad_scope : env  ->  FStar_Ident.ident  ->  env = (fun env mname -> (match (env.curmonad) with
| Some (mname') -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((((Prims.strcat "Trying to define monad " (Prims.strcat mname.FStar_Ident.idText (Prims.strcat ", but already in monad scope " mname'.FStar_Ident.idText)))), (mname.FStar_Ident.idRange)))))
end
| None -> begin
(

let _63_1239 = env
in {curmodule = _63_1239.curmodule; curmonad = Some (mname); modules = _63_1239.modules; scope_mods = _63_1239.scope_mods; sigaccum = _63_1239.sigaccum; sigmap = _63_1239.sigmap; default_result_effect = _63_1239.default_result_effect; iface = _63_1239.iface; admitted_iface = _63_1239.admitted_iface; expect_typ = _63_1239.expect_typ})
end))


let fail_or = (fun env lookup lid -> (match ((lookup lid)) with
| None -> begin
(

let opened_modules = (FStar_List.map (fun _63_1248 -> (match (_63_1248) with
| (lid, _63_1247) -> begin
(FStar_Ident.text_of_lid lid)
end)) env.modules)
in (

let msg = (FStar_Util.format1 "Identifier not found: [%s]" (FStar_Ident.text_of_lid lid))
in (

let msg = if ((FStar_List.length lid.FStar_Ident.ns) = (Prims.parse_int "0")) then begin
msg
end else begin
(

let modul = (let _158_926 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in (FStar_Ident.set_lid_range _158_926 (FStar_Ident.range_of_lid lid)))
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




