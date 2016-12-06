
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
| Local_binding (_63_39) -> begin
_63_39
end))


let ___Rec_binding____0 = (fun projectee -> (match (projectee) with
| Rec_binding (_63_42) -> begin
_63_42
end))


let ___Module_abbrev____0 = (fun projectee -> (match (projectee) with
| Module_abbrev (_63_45) -> begin
_63_45
end))


let ___Open_module_or_namespace____0 = (fun projectee -> (match (projectee) with
| Open_module_or_namespace (_63_48) -> begin
_63_48
end))


let ___Top_level_def____0 = (fun projectee -> (match (projectee) with
| Top_level_def (_63_51) -> begin
_63_51
end))


let ___Record_or_dc____0 = (fun projectee -> (match (projectee) with
| Record_or_dc (_63_54) -> begin
_63_54
end))


type string_set =
Prims.string FStar_Util.set


type exported_id_kind =
| Exported_id_term_type
| Exported_id_field


let is_Exported_id_term_type = (fun _discr_ -> (match (_discr_) with
| Exported_id_term_type (_) -> begin
true
end
| _ -> begin
false
end))


let is_Exported_id_field = (fun _discr_ -> (match (_discr_) with
| Exported_id_field (_) -> begin
true
end
| _ -> begin
false
end))


type exported_id_set =
exported_id_kind  ->  string_set FStar_ST.ref


type env =
{curmodule : FStar_Ident.lident Prims.option; curmonad : FStar_Ident.ident Prims.option; modules : (FStar_Ident.lident * FStar_Syntax_Syntax.modul) Prims.list; scope_mods : scope_mod Prims.list; exported_ids : exported_id_set FStar_Util.smap; trans_exported_ids : exported_id_set FStar_Util.smap; includes : FStar_Ident.lident Prims.list FStar_ST.ref FStar_Util.smap; sigaccum : FStar_Syntax_Syntax.sigelts; sigmap : (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap; default_result_effect : FStar_Ident.lident; iface : Prims.bool; admitted_iface : Prims.bool; expect_typ : Prims.bool}


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
| Term_name (_63_71) -> begin
_63_71
end))


let ___Eff_name____0 = (fun projectee -> (match (projectee) with
| Eff_name (_63_74) -> begin
_63_74
end))


let all_exported_id_kinds : exported_id_kind Prims.list = (Exported_id_field)::(Exported_id_term_type)::[]


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
(let _158_185 = (current_module env)
in (qual _158_185 id))
end
| Some (monad) -> begin
(let _158_187 = (let _158_186 = (current_module env)
in (qual _158_186 monad))
in (FStar_Syntax_Util.mk_field_projector_name_from_ident _158_187 id))
end))


let new_sigmap = (fun _63_87 -> (match (()) with
| () -> begin
(FStar_Util.smap_create (Prims.parse_int "100"))
end))


let empty_env : Prims.unit  ->  env = (fun _63_88 -> (match (()) with
| () -> begin
(let _158_194 = (new_sigmap ())
in (let _158_193 = (new_sigmap ())
in (let _158_192 = (new_sigmap ())
in (let _158_191 = (new_sigmap ())
in {curmodule = None; curmonad = None; modules = []; scope_mods = []; exported_ids = _158_194; trans_exported_ids = _158_193; includes = _158_192; sigaccum = []; sigmap = _158_191; default_result_effect = FStar_Syntax_Const.effect_Tot_lid; iface = false; admitted_iface = false; expect_typ = false}))))
end))


let sigmap : env  ->  (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap = (fun env -> env.sigmap)


let has_all_in_scope : env  ->  Prims.bool = (fun env -> (FStar_List.existsb (fun _63_94 -> (match (_63_94) with
| (m, _63_93) -> begin
(FStar_Ident.lid_equals m FStar_Syntax_Const.all_lid)
end)) env.modules))


let default_total : env  ->  env = (fun env -> (

let _63_96 = env
in {curmodule = _63_96.curmodule; curmonad = _63_96.curmonad; modules = _63_96.modules; scope_mods = _63_96.scope_mods; exported_ids = _63_96.exported_ids; trans_exported_ids = _63_96.trans_exported_ids; includes = _63_96.includes; sigaccum = _63_96.sigaccum; sigmap = _63_96.sigmap; default_result_effect = FStar_Syntax_Const.effect_Tot_lid; iface = _63_96.iface; admitted_iface = _63_96.admitted_iface; expect_typ = _63_96.expect_typ}))


let default_ml : env  ->  env = (fun env -> if (has_all_in_scope env) then begin
(

let _63_99 = env
in {curmodule = _63_99.curmodule; curmonad = _63_99.curmonad; modules = _63_99.modules; scope_mods = _63_99.scope_mods; exported_ids = _63_99.exported_ids; trans_exported_ids = _63_99.trans_exported_ids; includes = _63_99.includes; sigaccum = _63_99.sigaccum; sigmap = _63_99.sigmap; default_result_effect = FStar_Syntax_Const.effect_ML_lid; iface = _63_99.iface; admitted_iface = _63_99.admitted_iface; expect_typ = _63_99.expect_typ})
end else begin
env
end)


let set_bv_range : FStar_Syntax_Syntax.bv  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.bv = (fun bv r -> (

let id = (

let _63_103 = bv.FStar_Syntax_Syntax.ppname
in {FStar_Ident.idText = _63_103.FStar_Ident.idText; FStar_Ident.idRange = r})
in (

let _63_106 = bv
in {FStar_Syntax_Syntax.ppname = id; FStar_Syntax_Syntax.index = _63_106.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _63_106.FStar_Syntax_Syntax.sort})))


let bv_to_name : FStar_Syntax_Syntax.bv  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.term = (fun bv r -> (FStar_Syntax_Syntax.bv_to_name (set_bv_range bv r)))


let unmangleMap : (Prims.string * Prims.string * FStar_Syntax_Syntax.delta_depth * FStar_Syntax_Syntax.fv_qual Prims.option) Prims.list = ((("op_ColonColon"), ("Cons"), (FStar_Syntax_Syntax.Delta_constant), (Some (FStar_Syntax_Syntax.Data_ctor))))::((("not"), ("op_Negation"), (FStar_Syntax_Syntax.Delta_equational), (None)))::[]


let unmangleOpName : FStar_Ident.ident  ->  (FStar_Syntax_Syntax.term * Prims.bool) Prims.option = (fun id -> (

let t = (FStar_Util.find_map unmangleMap (fun _63_115 -> (match (_63_115) with
| (x, y, dd, dq) -> begin
if (id.FStar_Ident.idText = x) then begin
(let _158_216 = (let _158_215 = (FStar_Ident.lid_of_path (("Prims")::(y)::[]) id.FStar_Ident.idRange)
in (FStar_Syntax_Syntax.fvar _158_215 dd dq))
in Some (_158_216))
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
| Cont_ok (_63_123) -> begin
_63_123
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
(let _158_247 = (FStar_Ident.lid_of_ids (FStar_List.append ns ((constrname)::[])))
in (FStar_Syntax_Util.mk_field_projector_name_from_ident _158_247 id))
end else begin
(FStar_Ident.lid_of_ids (FStar_List.append ns ((id)::[])))
end
in (

let fname = (FStar_Ident.set_lid_range fname id.FStar_Ident.idRange)
in (

let find = (FStar_Util.find_map record.fields (fun _63_142 -> (match (_63_142) with
| (f, _63_141) -> begin
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


let get_exported_id_set : env  ->  Prims.string  ->  (exported_id_kind  ->  string_set FStar_ST.ref) Prims.option = (fun e mname -> (FStar_Util.smap_try_find e.exported_ids mname))


let get_trans_exported_id_set : env  ->  Prims.string  ->  (exported_id_kind  ->  string_set FStar_ST.ref) Prims.option = (fun e mname -> (FStar_Util.smap_try_find e.trans_exported_ids mname))


let string_of_exported_id_kind : exported_id_kind  ->  Prims.string = (fun _63_2 -> (match (_63_2) with
| Exported_id_field -> begin
"field"
end
| Exported_id_term_type -> begin
"term/type"
end))


let find_in_module_with_includes = (fun eikind find_in_module find_in_module_default env ns id -> (

let idstr = id.FStar_Ident.idText
in (

let rec aux = (fun _63_3 -> (match (_63_3) with
| [] -> begin
find_in_module_default
end
| (modul)::q -> begin
(

let mname = modul.FStar_Ident.str
in (

let not_shadowed = (match ((get_exported_id_set env mname)) with
| None -> begin
true
end
| Some (mex) -> begin
(

let mexports = (let _158_287 = (mex eikind)
in (FStar_ST.read _158_287))
in (FStar_Util.set_mem idstr mexports))
end)
in (

let mincludes = (match ((FStar_Util.smap_try_find env.includes mname)) with
| None -> begin
[]
end
| Some (minc) -> begin
(FStar_ST.read minc)
end)
in (

let look_into = if not_shadowed then begin
(let _158_288 = (qual modul id)
in (find_in_module _158_288))
end else begin
Cont_ignore
end
in (match (look_into) with
| Cont_ignore -> begin
(aux (FStar_List.append mincludes q))
end
| _63_181 -> begin
look_into
end)))))
end))
in (aux ((ns)::[])))))


let is_exported_id_field : exported_id_kind  ->  Prims.bool = (fun _63_4 -> (match (_63_4) with
| Exported_id_field -> begin
true
end
| _63_185 -> begin
false
end))


let try_lookup_id'' = (fun env id eikind k_local_binding k_rec_binding k_record find_in_module lookup_default_id -> (

let check_local_binding_id = (fun _63_5 -> (match (_63_5) with
| (id', _63_198, _63_200) -> begin
(id'.FStar_Ident.idText = id.FStar_Ident.idText)
end))
in (

let check_rec_binding_id = (fun _63_6 -> (match (_63_6) with
| (id', _63_206, _63_208) -> begin
(id'.FStar_Ident.idText = id.FStar_Ident.idText)
end))
in (

let curmod_ns = (let _158_321 = (current_module env)
in (FStar_Ident.ids_of_lid _158_321))
in (

let proc = (fun _63_7 -> (match (_63_7) with
| Local_binding (l) when (check_local_binding_id l) -> begin
(k_local_binding l)
end
| Rec_binding (r) when (check_rec_binding_id r) -> begin
(k_rec_binding r)
end
| Open_module_or_namespace (ns, _63_219) -> begin
(find_in_module_with_includes eikind find_in_module Cont_ignore env ns id)
end
| Top_level_def (id') when (id'.FStar_Ident.idText = id.FStar_Ident.idText) -> begin
(lookup_default_id Cont_ignore id)
end
| Record_or_dc (r) when (is_exported_id_field eikind) -> begin
(let _158_325 = (FStar_Ident.lid_of_ids curmod_ns)
in (find_in_module_with_includes Exported_id_field (fun lid -> (

let id = lid.FStar_Ident.ident
in (find_in_record lid.FStar_Ident.ns id r k_record))) Cont_ignore env _158_325 id))
end
| _63_229 -> begin
Cont_ignore
end))
in (

let rec aux = (fun _63_8 -> (match (_63_8) with
| (a)::q -> begin
(let _158_329 = (proc a)
in (option_of_cont (fun _63_236 -> (aux q)) _158_329))
end
| [] -> begin
(let _158_331 = (lookup_default_id Cont_fail id)
in (option_of_cont (fun _63_239 -> None) _158_331))
end))
in (aux env.scope_mods)))))))


let found_local_binding = (fun _63_244 -> (match (_63_244) with
| (id', x, mut) -> begin
(let _158_333 = (bv_to_name x id'.FStar_Ident.idRange)
in ((_158_333), (mut)))
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
| _63_257 -> begin
(try_lookup_id'' env id Exported_id_term_type (fun r -> (let _158_349 = (found_local_binding r)
in Cont_ok (_158_349))) (fun _63_269 -> Cont_fail) (fun _63_267 -> Cont_ignore) (fun i -> (find_in_module env i (fun _63_263 _63_265 -> Cont_fail) Cont_ignore)) (fun _63_258 _63_260 -> Cont_fail))
end))


let lookup_default_id = (fun env id k_global_def k_not_found -> (

let find_in_monad = (match (env.curmonad) with
| Some (_63_278) -> begin
(

let lid = (qualify env id)
in (match ((FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str)) with
| Some (r) -> begin
(let _158_367 = (k_global_def lid r)
in Some (_158_367))
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

let lid = (let _158_368 = (current_module env)
in (qual _158_368 id))
in (find_in_module env lid k_global_def k_not_found))
end)))


let module_is_defined : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> ((let _158_373 = (current_module env)
in (FStar_Ident.lid_equals lid _158_373)) || (FStar_List.existsb (fun x -> (FStar_Ident.lid_equals lid (Prims.fst x))) env.modules)))


let resolve_module_name : env  ->  FStar_Ident.lident  ->  Prims.bool  ->  FStar_Ident.lident Prims.option = (fun env lid honor_ns -> (

let nslen = (FStar_List.length lid.FStar_Ident.ns)
in (

let rec aux = (fun _63_9 -> (match (_63_9) with
| [] -> begin
if (module_is_defined env lid) then begin
Some (lid)
end else begin
None
end
end
| (Open_module_or_namespace (ns, Open_namespace))::q when honor_ns -> begin
(

let new_lid = (let _158_385 = (let _158_384 = (FStar_Ident.path_of_lid ns)
in (let _158_383 = (FStar_Ident.path_of_lid lid)
in (FStar_List.append _158_384 _158_383)))
in (FStar_Ident.lid_of_path _158_385 (FStar_Ident.range_of_lid lid)))
in if (module_is_defined env new_lid) then begin
Some (new_lid)
end else begin
(aux q)
end)
end
| (Module_abbrev (name, modul))::_63_308 when ((nslen = (Prims.parse_int "0")) && (name.FStar_Ident.idText = lid.FStar_Ident.ident.FStar_Ident.idText)) -> begin
Some (modul)
end
| (_63_316)::q -> begin
(aux q)
end))
in (aux env.scope_mods))))


let resolve_in_open_namespaces'' = (fun env lid eikind k_local_binding k_rec_binding k_record f_module l_default -> (match (lid.FStar_Ident.ns) with
| (_63_330)::_63_328 -> begin
(match ((let _158_413 = (let _158_412 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in (FStar_Ident.set_lid_range _158_412 (FStar_Ident.range_of_lid lid)))
in (resolve_module_name env _158_413 true))) with
| None -> begin
None
end
| Some (modul) -> begin
(let _158_415 = (find_in_module_with_includes eikind f_module Cont_fail env modul lid.FStar_Ident.ident)
in (option_of_cont (fun _63_335 -> None) _158_415))
end)
end
| [] -> begin
(try_lookup_id'' env lid.FStar_Ident.ident eikind k_local_binding k_rec_binding k_record f_module l_default)
end))


let cont_of_option = (fun k_none _63_10 -> (match (_63_10) with
| Some (v) -> begin
Cont_ok (v)
end
| None -> begin
k_none
end))


let resolve_in_open_namespaces' = (fun env lid k_local_binding k_rec_binding k_global_def -> (

let k_global_def' = (fun k lid def -> (let _158_441 = (k_global_def lid def)
in (cont_of_option k _158_441)))
in (

let f_module = (fun lid' -> (

let k = Cont_ignore
in (find_in_module env lid' (k_global_def' k) k)))
in (

let l_default = (fun k i -> (lookup_default_id env i (k_global_def' k) k))
in (resolve_in_open_namespaces'' env lid Exported_id_term_type (fun l -> (let _158_449 = (k_local_binding l)
in (cont_of_option Cont_fail _158_449))) (fun r -> (let _158_451 = (k_rec_binding r)
in (cont_of_option Cont_fail _158_451))) (fun _63_360 -> Cont_ignore) f_module l_default)))))


let fv_qual_of_se : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.fv_qual Prims.option = (fun _63_12 -> (match (_63_12) with
| FStar_Syntax_Syntax.Sig_datacon (_63_366, _63_368, _63_370, l, _63_373, quals, _63_376, _63_378) -> begin
(

let qopt = (FStar_Util.find_map quals (fun _63_11 -> (match (_63_11) with
| FStar_Syntax_Syntax.RecordConstructor (fs) -> begin
Some (FStar_Syntax_Syntax.Record_ctor (((l), (fs))))
end
| _63_385 -> begin
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
| FStar_Syntax_Syntax.Sig_declare_typ (_63_390, _63_392, _63_394, quals, _63_397) -> begin
None
end
| _63_401 -> begin
None
end))


let lb_fv : FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.fv = (fun lbs lid -> (let _158_461 = (FStar_Util.find_map lbs (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in if (FStar_Syntax_Syntax.fv_eq_lid fv lid) then begin
Some (fv)
end else begin
None
end)))
in (FStar_All.pipe_right _158_461 FStar_Util.must)))


let ns_of_lid_equals : FStar_Ident.lident  ->  FStar_Ident.lident  ->  Prims.bool = (fun lid ns -> (((FStar_List.length lid.FStar_Ident.ns) = (FStar_List.length (FStar_Ident.ids_of_lid ns))) && (let _158_466 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in (FStar_Ident.lid_equals _158_466 ns))))


let try_lookup_name : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  foundname Prims.option = (fun any_val exclude_interf env lid -> (

let occurrence_range = (FStar_Ident.range_of_lid lid)
in (

let k_global_def = (fun source_lid _63_16 -> (match (_63_16) with
| (_63_417, true) when exclude_interf -> begin
None
end
| (se, _63_422) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_63_425) -> begin
(let _158_481 = (let _158_480 = (let _158_479 = (FStar_Syntax_Syntax.fvar source_lid FStar_Syntax_Syntax.Delta_constant None)
in ((_158_479), (false)))
in Term_name (_158_480))
in Some (_158_481))
end
| FStar_Syntax_Syntax.Sig_datacon (_63_428) -> begin
(let _158_485 = (let _158_484 = (let _158_483 = (let _158_482 = (fv_qual_of_se se)
in (FStar_Syntax_Syntax.fvar source_lid FStar_Syntax_Syntax.Delta_constant _158_482))
in ((_158_483), (false)))
in Term_name (_158_484))
in Some (_158_485))
end
| FStar_Syntax_Syntax.Sig_let ((_63_431, lbs), _63_435, _63_437, _63_439) -> begin
(

let fv = (lb_fv lbs source_lid)
in (let _158_488 = (let _158_487 = (let _158_486 = (FStar_Syntax_Syntax.fvar source_lid fv.FStar_Syntax_Syntax.fv_delta fv.FStar_Syntax_Syntax.fv_qual)
in ((_158_486), (false)))
in Term_name (_158_487))
in Some (_158_488)))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _63_445, _63_447, quals, _63_450) -> begin
if (any_val || (FStar_All.pipe_right quals (FStar_Util.for_some (fun _63_13 -> (match (_63_13) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| _63_456 -> begin
false
end))))) then begin
(

let lid = (FStar_Ident.set_lid_range lid (FStar_Ident.range_of_lid source_lid))
in (

let dd = if ((FStar_Syntax_Util.is_primop_lid lid) || ((ns_of_lid_equals lid FStar_Syntax_Const.prims_lid) && (FStar_All.pipe_right quals (FStar_Util.for_some (fun _63_14 -> (match (_63_14) with
| (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) -> begin
true
end
| _63_466 -> begin
false
end)))))) then begin
FStar_Syntax_Syntax.Delta_equational
end else begin
FStar_Syntax_Syntax.Delta_constant
end
in (match ((FStar_Util.find_map quals (fun _63_15 -> (match (_63_15) with
| FStar_Syntax_Syntax.Reflectable (refl_monad) -> begin
Some (refl_monad)
end
| _63_472 -> begin
None
end)))) with
| Some (refl_monad) -> begin
(

let refl_const = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (refl_monad))) None occurrence_range)
in Some (Term_name (((refl_const), (false)))))
end
| _63_477 -> begin
(let _158_495 = (let _158_494 = (let _158_493 = (let _158_492 = (fv_qual_of_se se)
in (FStar_Syntax_Syntax.fvar lid dd _158_492))
in ((_158_493), (false)))
in Term_name (_158_494))
in Some (_158_495))
end)))
end else begin
None
end
end
| (FStar_Syntax_Syntax.Sig_new_effect_for_free (ne, _)) | (FStar_Syntax_Syntax.Sig_new_effect (ne, _)) -> begin
Some (Eff_name (((se), ((FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname (FStar_Ident.range_of_lid source_lid))))))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (_63_488) -> begin
Some (Eff_name (((se), (source_lid))))
end
| _63_491 -> begin
None
end)
end))
in (

let k_local_binding = (fun r -> (let _158_499 = (let _158_498 = (found_local_binding r)
in Term_name (_158_498))
in Some (_158_499)))
in (

let k_rec_binding = (fun _63_498 -> (match (_63_498) with
| (id, l, dd) -> begin
(let _158_504 = (let _158_503 = (let _158_502 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range l (FStar_Ident.range_of_lid lid)) dd None)
in ((_158_502), (false)))
in Term_name (_158_503))
in Some (_158_504))
end))
in (

let found_unmangled = (match (lid.FStar_Ident.ns) with
| [] -> begin
(match ((unmangleOpName lid.FStar_Ident.ident)) with
| Some (f) -> begin
Some (Term_name (f))
end
| _63_503 -> begin
None
end)
end
| _63_505 -> begin
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
| _63_518 -> begin
None
end))


let try_lookup_effect_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env l -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some (o, l) -> begin
Some (l)
end
| _63_526 -> begin
None
end))


let try_lookup_effect_defn : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl Prims.option = (fun env l -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some (FStar_Syntax_Syntax.Sig_new_effect (ne, _63_531), _63_535) -> begin
Some (ne)
end
| Some (FStar_Syntax_Syntax.Sig_new_effect_for_free (ne, _63_540), _63_544) -> begin
Some (ne)
end
| _63_548 -> begin
None
end))


let is_effect_name : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((try_lookup_effect_name env lid)) with
| None -> begin
false
end
| Some (_63_553) -> begin
true
end))


let lookup_letbinding_quals : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.qualifier Prims.list = (fun env lid -> (

let k_global_def = (fun lid _63_17 -> (match (_63_17) with
| (FStar_Syntax_Syntax.Sig_declare_typ (lid, _63_562, _63_564, quals, _63_567), _63_571) -> begin
Some (quals)
end
| _63_574 -> begin
None
end))
in (match ((resolve_in_open_namespaces' env lid (fun _63_577 -> None) (fun _63_575 -> None) k_global_def)) with
| Some (quals) -> begin
quals
end
| _63_582 -> begin
[]
end)))


let try_lookup_module : env  ->  Prims.string Prims.list  ->  FStar_Syntax_Syntax.modul Prims.option = (fun env path -> (match ((FStar_List.tryFind (fun _63_587 -> (match (_63_587) with
| (mlid, modul) -> begin
((FStar_Ident.path_of_lid mlid) = path)
end)) env.modules)) with
| Some (_63_589, modul) -> begin
Some (modul)
end
| None -> begin
None
end))


let try_lookup_let : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env lid -> (

let k_global_def = (fun lid _63_18 -> (match (_63_18) with
| (FStar_Syntax_Syntax.Sig_let ((_63_600, lbs), _63_604, _63_606, _63_608), _63_612) -> begin
(

let fv = (lb_fv lbs lid)
in (let _158_546 = (FStar_Syntax_Syntax.fvar lid fv.FStar_Syntax_Syntax.fv_delta fv.FStar_Syntax_Syntax.fv_qual)
in Some (_158_546)))
end
| _63_616 -> begin
None
end))
in (resolve_in_open_namespaces' env lid (fun _63_619 -> None) (fun _63_617 -> None) k_global_def)))


let try_lookup_definition : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env lid -> (

let k_global_def = (fun lid _63_19 -> (match (_63_19) with
| (FStar_Syntax_Syntax.Sig_let (lbs, _63_628, _63_630, _63_632), _63_636) -> begin
(FStar_Util.find_map (Prims.snd lbs) (fun lb -> (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv lid) -> begin
Some (lb.FStar_Syntax_Syntax.lbdef)
end
| _63_642 -> begin
None
end)))
end
| _63_644 -> begin
None
end))
in (resolve_in_open_namespaces' env lid (fun _63_647 -> None) (fun _63_645 -> None) k_global_def)))


let try_lookup_lid' : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term * Prims.bool) Prims.option = (fun any_val exclude_interf env lid -> (match ((try_lookup_name any_val exclude_interf env lid)) with
| Some (Term_name (e, mut)) -> begin
Some (((e), (mut)))
end
| _63_659 -> begin
None
end))


let try_lookup_lid : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term * Prims.bool) Prims.option = (fun env l -> (try_lookup_lid' env.iface false env l))


let try_lookup_datacon : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.fv Prims.option = (fun env lid -> (

let k_global_def = (fun lid _63_21 -> (match (_63_21) with
| (FStar_Syntax_Syntax.Sig_declare_typ (_63_668, _63_670, _63_672, quals, _63_675), _63_679) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _63_20 -> (match (_63_20) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| _63_684 -> begin
false
end)))) then begin
(let _158_581 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant None)
in Some (_158_581))
end else begin
None
end
end
| (FStar_Syntax_Syntax.Sig_datacon (_63_686), _63_689) -> begin
(let _158_582 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in Some (_158_582))
end
| _63_692 -> begin
None
end))
in (resolve_in_open_namespaces' env lid (fun _63_695 -> None) (fun _63_693 -> None) k_global_def)))


let find_all_datacons : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.list Prims.option = (fun env lid -> (

let k_global_def = (fun lid _63_22 -> (match (_63_22) with
| (FStar_Syntax_Syntax.Sig_inductive_typ (_63_703, _63_705, _63_707, _63_709, _63_711, datas, _63_714, _63_716), _63_720) -> begin
Some (datas)
end
| _63_723 -> begin
None
end))
in (resolve_in_open_namespaces' env lid (fun _63_726 -> None) (fun _63_724 -> None) k_global_def)))


let record_cache_aux : ((Prims.unit  ->  Prims.unit) * (Prims.unit  ->  Prims.unit) * (Prims.unit  ->  record_or_dc Prims.list) * (record_or_dc  ->  Prims.unit) * (Prims.unit  ->  Prims.unit)) = (

let record_cache = (FStar_Util.mk_ref (([])::[]))
in (

let push = (fun _63_730 -> (match (()) with
| () -> begin
(let _158_610 = (let _158_609 = (let _158_607 = (FStar_ST.read record_cache)
in (FStar_List.hd _158_607))
in (let _158_608 = (FStar_ST.read record_cache)
in (_158_609)::_158_608))
in (FStar_ST.op_Colon_Equals record_cache _158_610))
end))
in (

let pop = (fun _63_732 -> (match (()) with
| () -> begin
(let _158_614 = (let _158_613 = (FStar_ST.read record_cache)
in (FStar_List.tl _158_613))
in (FStar_ST.op_Colon_Equals record_cache _158_614))
end))
in (

let peek = (fun _63_734 -> (match (()) with
| () -> begin
(let _158_617 = (FStar_ST.read record_cache)
in (FStar_List.hd _158_617))
end))
in (

let insert = (fun r -> (let _158_624 = (let _158_623 = (let _158_620 = (peek ())
in (r)::_158_620)
in (let _158_622 = (let _158_621 = (FStar_ST.read record_cache)
in (FStar_List.tl _158_621))
in (_158_623)::_158_622))
in (FStar_ST.op_Colon_Equals record_cache _158_624)))
in (

let commit = (fun _63_738 -> (match (()) with
| () -> begin
(match ((FStar_ST.read record_cache)) with
| (hd)::(_63_741)::tl -> begin
(FStar_ST.op_Colon_Equals record_cache ((hd)::tl))
end
| _63_746 -> begin
(FStar_All.failwith "Impossible")
end)
end))
in ((push), (pop), (peek), (insert), (commit))))))))


let push_record_cache : Prims.unit  ->  Prims.unit = (

let _63_756 = record_cache_aux
in (match (_63_756) with
| (push, _63_749, _63_751, _63_753, _63_755) -> begin
push
end))


let pop_record_cache : Prims.unit  ->  Prims.unit = (

let _63_766 = record_cache_aux
in (match (_63_766) with
| (_63_758, pop, _63_761, _63_763, _63_765) -> begin
pop
end))


let peek_record_cache : Prims.unit  ->  record_or_dc Prims.list = (

let _63_776 = record_cache_aux
in (match (_63_776) with
| (_63_768, _63_770, peek, _63_773, _63_775) -> begin
peek
end))


let insert_record_cache : record_or_dc  ->  Prims.unit = (

let _63_786 = record_cache_aux
in (match (_63_786) with
| (_63_778, _63_780, _63_782, insert, _63_785) -> begin
insert
end))


let commit_record_cache : Prims.unit  ->  Prims.unit = (

let _63_796 = record_cache_aux
in (match (_63_796) with
| (_63_788, _63_790, _63_792, _63_794, commit) -> begin
commit
end))


let extract_record : env  ->  scope_mod Prims.list FStar_ST.ref  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun e new_globs _63_26 -> (match (_63_26) with
| FStar_Syntax_Syntax.Sig_bundle (sigs, _63_802, _63_804, _63_806) -> begin
(

let is_rec = (FStar_Util.for_some (fun _63_23 -> (match (_63_23) with
| (FStar_Syntax_Syntax.RecordType (_)) | (FStar_Syntax_Syntax.RecordConstructor (_)) -> begin
true
end
| _63_817 -> begin
false
end)))
in (

let find_dc = (fun dc -> (FStar_All.pipe_right sigs (FStar_Util.find_opt (fun _63_24 -> (match (_63_24) with
| FStar_Syntax_Syntax.Sig_datacon (lid, _63_824, _63_826, _63_828, _63_830, _63_832, _63_834, _63_836) -> begin
(FStar_Ident.lid_equals dc lid)
end
| _63_840 -> begin
false
end)))))
in (FStar_All.pipe_right sigs (FStar_List.iter (fun _63_25 -> (match (_63_25) with
| FStar_Syntax_Syntax.Sig_inductive_typ (typename, univs, parms, _63_846, _63_848, (dc)::[], tags, _63_853) -> begin
(match ((let _158_729 = (find_dc dc)
in (FStar_All.pipe_left FStar_Util.must _158_729))) with
| FStar_Syntax_Syntax.Sig_datacon (constrname, _63_858, t, _63_861, _63_863, _63_865, _63_867, _63_869) -> begin
(

let _63_875 = (FStar_Syntax_Util.arrow_formals t)
in (match (_63_875) with
| (formals, _63_874) -> begin
(

let is_rec = (is_rec tags)
in (

let formals' = (FStar_All.pipe_right formals (FStar_List.collect (fun _63_879 -> (match (_63_879) with
| (x, q) -> begin
if ((FStar_Syntax_Syntax.is_null_bv x) || (is_rec && (FStar_Syntax_Syntax.is_implicit q))) then begin
[]
end else begin
(((x), (q)))::[]
end
end))))
in (

let fields' = (FStar_All.pipe_right formals' (FStar_List.map (fun _63_883 -> (match (_63_883) with
| (x, q) -> begin
(let _158_732 = if is_rec then begin
(FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname)
end else begin
x.FStar_Syntax_Syntax.ppname
end
in ((_158_732), (x.FStar_Syntax_Syntax.sort)))
end))))
in (

let fields = (FStar_All.pipe_right fields' (FStar_List.map (fun _63_887 -> (match (_63_887) with
| (xid, xsort) -> begin
(let _158_734 = (FStar_Syntax_Util.mk_field_projector_name_from_ident constrname xid)
in ((_158_734), (xsort)))
end))))
in (

let record = {typename = typename; constrname = constrname; parms = parms; fields = fields; is_record = is_rec}
in (

let _63_890 = (let _158_736 = (let _158_735 = (FStar_ST.read new_globs)
in (Record_or_dc (record))::_158_735)
in (FStar_ST.op_Colon_Equals new_globs _158_736))
in (match (()) with
| () -> begin
(

let _63_904 = (

let add_field = (fun _63_895 -> (match (_63_895) with
| (id, _63_894) -> begin
(

let modul = (let _158_739 = (FStar_Ident.lid_of_ids constrname.FStar_Ident.ns)
in _158_739.FStar_Ident.str)
in (match ((get_exported_id_set e modul)) with
| Some (my_ex) -> begin
(

let my_exported_ids = (my_ex Exported_id_field)
in (

let _63_900 = (let _158_742 = (let _158_741 = (FStar_ST.read my_exported_ids)
in (FStar_Util.set_add id.FStar_Ident.idText _158_741))
in (FStar_ST.op_Colon_Equals my_exported_ids _158_742))
in (match (()) with
| () -> begin
(

let projname = (let _158_744 = (let _158_743 = (FStar_Syntax_Util.mk_field_projector_name_from_ident constrname id)
in _158_743.FStar_Ident.ident)
in _158_744.FStar_Ident.idText)
in (

let _63_902 = (let _158_746 = (let _158_745 = (FStar_ST.read my_exported_ids)
in (FStar_Util.set_add projname _158_745))
in (FStar_ST.op_Colon_Equals my_exported_ids _158_746))
in ()))
end)))
end
| None -> begin
()
end))
end))
in (FStar_List.iter add_field fields'))
in (match (()) with
| () -> begin
(insert_record_cache record)
end))
end)))))))
end))
end
| _63_906 -> begin
()
end)
end
| _63_908 -> begin
()
end))))))
end
| _63_910 -> begin
()
end))


let try_lookup_record_or_dc_by_field_name : env  ->  FStar_Ident.lident  ->  (record_or_dc * FStar_Syntax_Syntax.fieldname) Prims.option = (fun env fieldname -> (

let needs_constrname = (not ((FStar_Syntax_Util.field_projector_contains_constructor fieldname.FStar_Ident.ident.FStar_Ident.idText)))
in (

let find_in_cache = (fun fieldname -> (

let _63_918 = ((fieldname.FStar_Ident.ns), (fieldname.FStar_Ident.ident))
in (match (_63_918) with
| (ns, id) -> begin
(let _158_757 = (peek_record_cache ())
in (FStar_Util.find_map _158_757 (fun record -> (let _158_756 = (find_in_record ns id record (fun r -> Cont_ok (r)))
in (option_of_cont (fun _63_921 -> None) _158_756)))))
end)))
in (resolve_in_open_namespaces'' env fieldname Exported_id_field (fun _63_930 -> Cont_ignore) (fun _63_928 -> Cont_ignore) (fun r -> Cont_ok (r)) (fun fn -> (let _158_762 = (find_in_cache fn)
in (cont_of_option Cont_ignore _158_762))) (fun k _63_924 -> k)))))


let try_lookup_record_by_field_name : env  ->  FStar_Ident.lident  ->  (record_or_dc * FStar_Ident.lident) Prims.option = (fun env fieldname -> (match ((try_lookup_record_or_dc_by_field_name env fieldname)) with
| Some (r, f) when r.is_record -> begin
Some (((r), (f)))
end
| _63_939 -> begin
None
end))


let try_lookup_projector_by_field_name : env  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * Prims.bool) Prims.option = (fun env fieldname -> (match ((try_lookup_record_or_dc_by_field_name env fieldname)) with
| Some (r, f) -> begin
Some (((f), (r.is_record)))
end
| _63_947 -> begin
None
end))


let qualify_field_to_record : env  ->  record_or_dc  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env recd f -> (

let qualify = (fun fieldname -> (

let _63_955 = ((fieldname.FStar_Ident.ns), (fieldname.FStar_Ident.ident))
in (match (_63_955) with
| (ns, fieldname) -> begin
(

let constrname = recd.constrname.FStar_Ident.ident
in (

let fname = (let _158_781 = (FStar_Ident.lid_of_ids (FStar_List.append ns ((constrname)::[])))
in (FStar_Syntax_Util.mk_field_projector_name_from_ident _158_781 fieldname))
in (FStar_Util.find_map recd.fields (fun _63_961 -> (match (_63_961) with
| (f, _63_960) -> begin
if (FStar_Ident.lid_equals fname f) then begin
Some (fname)
end else begin
None
end
end)))))
end)))
in (resolve_in_open_namespaces'' env f Exported_id_field (fun _63_969 -> Cont_ignore) (fun _63_967 -> Cont_ignore) (fun r -> Cont_ok ((Prims.snd r))) (fun fn -> (let _158_787 = (qualify fn)
in (cont_of_option Cont_ignore _158_787))) (fun k _63_963 -> k))))


let string_set_ref_new : Prims.unit  ->  Prims.string FStar_Util.set FStar_ST.ref = (fun _63_971 -> (match (()) with
| () -> begin
(let _158_792 = (FStar_Util.new_set FStar_Util.compare FStar_Util.hashcode)
in (FStar_Util.mk_ref _158_792))
end))


let exported_id_set_new : Prims.unit  ->  exported_id_kind  ->  Prims.string FStar_Util.set FStar_ST.ref = (fun _63_972 -> (match (()) with
| () -> begin
(

let term_type_set = (string_set_ref_new ())
in (

let field_set = (string_set_ref_new ())
in (fun _63_27 -> (match (_63_27) with
| Exported_id_term_type -> begin
term_type_set
end
| Exported_id_field -> begin
field_set
end))))
end))


let empty_include_smap : FStar_Ident.lident Prims.list FStar_ST.ref FStar_Util.smap = (new_sigmap ())


let empty_exported_id_smap : exported_id_set FStar_Util.smap = (new_sigmap ())


let unique : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  Prims.bool = (fun any_val exclude_if env lid -> (

let filter_scope_mods = (fun _63_28 -> (match (_63_28) with
| Rec_binding (_63_984) -> begin
true
end
| _63_987 -> begin
false
end))
in (

let this_env = (

let _63_989 = env
in (let _158_812 = (FStar_List.filter filter_scope_mods env.scope_mods)
in {curmodule = _63_989.curmodule; curmonad = _63_989.curmonad; modules = _63_989.modules; scope_mods = _158_812; exported_ids = empty_exported_id_smap; trans_exported_ids = _63_989.trans_exported_ids; includes = empty_include_smap; sigaccum = _63_989.sigaccum; sigmap = _63_989.sigmap; default_result_effect = _63_989.default_result_effect; iface = _63_989.iface; admitted_iface = _63_989.admitted_iface; expect_typ = _63_989.expect_typ}))
in (match ((try_lookup_lid' any_val exclude_if this_env lid)) with
| None -> begin
true
end
| Some (_63_994) -> begin
false
end))))


let push_scope_mod : env  ->  scope_mod  ->  env = (fun env scope_mod -> (

let _63_998 = env
in {curmodule = _63_998.curmodule; curmonad = _63_998.curmonad; modules = _63_998.modules; scope_mods = (scope_mod)::env.scope_mods; exported_ids = _63_998.exported_ids; trans_exported_ids = _63_998.trans_exported_ids; includes = _63_998.includes; sigaccum = _63_998.sigaccum; sigmap = _63_998.sigmap; default_result_effect = _63_998.default_result_effect; iface = _63_998.iface; admitted_iface = _63_998.admitted_iface; expect_typ = _63_998.expect_typ}))


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
| Some (se, _63_1019) -> begin
(match ((let _158_843 = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_Util.find_opt (FStar_Ident.lid_equals l) _158_843))) with
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
in (let _158_846 = (let _158_845 = (let _158_844 = (FStar_Util.format2 "Duplicate top-level names [%s]; previously declared at %s" (FStar_Ident.text_of_lid l) r)
in ((_158_844), ((FStar_Ident.range_of_lid l))))
in FStar_Syntax_Syntax.Error (_158_845))
in (Prims.raise _158_846)))))
in (

let globals = (FStar_ST.alloc env.scope_mods)
in (

let env = (

let _63_1038 = (match (s) with
| FStar_Syntax_Syntax.Sig_let (_63_1029) -> begin
((false), (true))
end
| FStar_Syntax_Syntax.Sig_bundle (_63_1032) -> begin
((true), (true))
end
| _63_1035 -> begin
((false), (false))
end)
in (match (_63_1038) with
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

let _63_1042 = (extract_record env globals s)
in (

let _63_1044 = env
in {curmodule = _63_1044.curmodule; curmonad = _63_1044.curmonad; modules = _63_1044.modules; scope_mods = _63_1044.scope_mods; exported_ids = _63_1044.exported_ids; trans_exported_ids = _63_1044.trans_exported_ids; includes = _63_1044.includes; sigaccum = (s)::env.sigaccum; sigmap = _63_1044.sigmap; default_result_effect = _63_1044.default_result_effect; iface = _63_1044.iface; admitted_iface = _63_1044.admitted_iface; expect_typ = _63_1044.expect_typ}))
end
| Some (l) -> begin
(err l)
end))
end))
in (

let env = (

let _63_1049 = env
in (let _158_848 = (FStar_ST.read globals)
in {curmodule = _63_1049.curmodule; curmonad = _63_1049.curmonad; modules = _63_1049.modules; scope_mods = _158_848; exported_ids = _63_1049.exported_ids; trans_exported_ids = _63_1049.trans_exported_ids; includes = _63_1049.includes; sigaccum = _63_1049.sigaccum; sigmap = _63_1049.sigmap; default_result_effect = _63_1049.default_result_effect; iface = _63_1049.iface; admitted_iface = _63_1049.admitted_iface; expect_typ = _63_1049.expect_typ}))
in (

let _63_1066 = (match (s) with
| FStar_Syntax_Syntax.Sig_bundle (ses, _63_1054, _63_1056, _63_1058) -> begin
(let _158_851 = (FStar_List.map (fun se -> (let _158_850 = (FStar_Syntax_Util.lids_of_sigelt se)
in ((_158_850), (se)))) ses)
in ((env), (_158_851)))
end
| _63_1063 -> begin
(let _158_854 = (let _158_853 = (let _158_852 = (FStar_Syntax_Util.lids_of_sigelt s)
in ((_158_852), (s)))
in (_158_853)::[])
in ((env), (_158_854)))
end)
in (match (_63_1066) with
| (env, lss) -> begin
(

let _63_1078 = (FStar_All.pipe_right lss (FStar_List.iter (fun _63_1069 -> (match (_63_1069) with
| (lids, se) -> begin
(FStar_All.pipe_right lids (FStar_List.iter (fun lid -> (

let _63_1071 = (let _158_858 = (let _158_857 = (FStar_ST.read globals)
in (Top_level_def (lid.FStar_Ident.ident))::_158_857)
in (FStar_ST.op_Colon_Equals globals _158_858))
in (match (()) with
| () -> begin
(

let modul = (let _158_859 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in _158_859.FStar_Ident.str)
in (

let _63_1077 = (match ((get_exported_id_set env modul)) with
| Some (f) -> begin
(

let my_exported_ids = (f Exported_id_term_type)
in (let _158_862 = (let _158_861 = (FStar_ST.read my_exported_ids)
in (FStar_Util.set_add lid.FStar_Ident.ident.FStar_Ident.idText _158_861))
in (FStar_ST.op_Colon_Equals my_exported_ids _158_862)))
end
| None -> begin
()
end)
in (match (()) with
| () -> begin
(FStar_Util.smap_add (sigmap env) lid.FStar_Ident.str ((se), ((env.iface && (not (env.admitted_iface))))))
end)))
end)))))
end))))
in (

let env = (

let _63_1080 = env
in (let _158_863 = (FStar_ST.read globals)
in {curmodule = _63_1080.curmodule; curmonad = _63_1080.curmonad; modules = _63_1080.modules; scope_mods = _158_863; exported_ids = _63_1080.exported_ids; trans_exported_ids = _63_1080.trans_exported_ids; includes = _63_1080.includes; sigaccum = _63_1080.sigaccum; sigmap = _63_1080.sigmap; default_result_effect = _63_1080.default_result_effect; iface = _63_1080.iface; admitted_iface = _63_1080.admitted_iface; expect_typ = _63_1080.expect_typ}))
in env))
end)))))))


let push_namespace : env  ->  FStar_Ident.lident  ->  env = (fun env ns -> (

let _63_1095 = (match ((resolve_module_name env ns false)) with
| None -> begin
(

let modules = env.modules
in if (FStar_All.pipe_right modules (FStar_Util.for_some (fun _63_1090 -> (match (_63_1090) with
| (m, _63_1089) -> begin
(FStar_Util.starts_with (Prims.strcat (FStar_Ident.text_of_lid m) ".") (Prims.strcat (FStar_Ident.text_of_lid ns) "."))
end)))) then begin
((ns), (Open_namespace))
end else begin
(let _158_871 = (let _158_870 = (let _158_869 = (FStar_Util.format1 "Namespace %s cannot be found" (FStar_Ident.text_of_lid ns))
in ((_158_869), ((FStar_Ident.range_of_lid ns))))
in FStar_Syntax_Syntax.Error (_158_870))
in (Prims.raise _158_871))
end)
end
| Some (ns') -> begin
((ns'), (Open_module))
end)
in (match (_63_1095) with
| (ns', kd) -> begin
(push_scope_mod env (Open_module_or_namespace (((ns'), (kd)))))
end)))


let push_include : env  ->  FStar_Ident.lident  ->  env = (fun env ns -> (match ((resolve_module_name env ns false)) with
| Some (ns) -> begin
(

let env = (push_scope_mod env (Open_module_or_namespace (((ns), (Open_module)))))
in (

let curmod = (let _158_876 = (current_module env)
in _158_876.FStar_Ident.str)
in (

let _63_1105 = (match ((FStar_Util.smap_try_find env.includes curmod)) with
| None -> begin
()
end
| Some (incl) -> begin
(let _158_878 = (let _158_877 = (FStar_ST.read incl)
in (ns)::_158_877)
in (FStar_ST.op_Colon_Equals incl _158_878))
end)
in (match (()) with
| () -> begin
(match ((get_trans_exported_id_set env ns.FStar_Ident.str)) with
| Some (ns_trans_exports) -> begin
(

let _63_1122 = (match ((let _158_885 = (get_exported_id_set env curmod)
in (let _158_884 = (get_trans_exported_id_set env curmod)
in ((_158_885), (_158_884))))) with
| (Some (cur_exports), Some (cur_trans_exports)) -> begin
(

let update_exports = (fun k -> (

let ns_ex = (let _158_890 = (ns_trans_exports k)
in (FStar_ST.read _158_890))
in (

let ex = (cur_exports k)
in (

let _63_1117 = (let _158_892 = (let _158_891 = (FStar_ST.read ex)
in (FStar_Util.set_difference _158_891 ns_ex))
in (FStar_ST.op_Colon_Equals ex _158_892))
in (match (()) with
| () -> begin
(

let trans_ex = (cur_trans_exports k)
in (

let _63_1119 = (let _158_894 = (let _158_893 = (FStar_ST.read ex)
in (FStar_Util.set_union _158_893 ns_ex))
in (FStar_ST.op_Colon_Equals trans_ex _158_894))
in ()))
end)))))
in (FStar_List.iter update_exports all_exported_id_kinds))
end
| _63_1121 -> begin
()
end)
in (match (()) with
| () -> begin
env
end))
end
| None -> begin
(let _158_903 = (let _158_902 = (let _158_901 = (FStar_Util.format1 "include: Module %s was not prepared" ns.FStar_Ident.str)
in ((_158_901), ((FStar_Ident.range_of_lid ns))))
in FStar_Syntax_Syntax.Error (_158_902))
in (Prims.raise _158_903))
end)
end))))
end
| _63_1125 -> begin
(let _158_906 = (let _158_905 = (let _158_904 = (FStar_Util.format1 "include: Module %s cannot be found" ns.FStar_Ident.str)
in ((_158_904), ((FStar_Ident.range_of_lid ns))))
in FStar_Syntax_Syntax.Error (_158_905))
in (Prims.raise _158_906))
end))


let push_module_abbrev : env  ->  FStar_Ident.ident  ->  FStar_Ident.lident  ->  env = (fun env x l -> if (module_is_defined env l) then begin
(push_scope_mod env (Module_abbrev (((x), (l)))))
end else begin
(let _158_915 = (let _158_914 = (let _158_913 = (FStar_Util.format1 "Module %s cannot be found" (FStar_Ident.text_of_lid l))
in ((_158_913), ((FStar_Ident.range_of_lid l))))
in FStar_Syntax_Syntax.Error (_158_914))
in (Prims.raise _158_915))
end)


let check_admits : env  ->  Prims.unit = (fun env -> (FStar_All.pipe_right env.sigaccum (FStar_List.iter (fun se -> (match (se) with
| FStar_Syntax_Syntax.Sig_declare_typ (l, u, t, quals, r) -> begin
(match ((try_lookup_lid env l)) with
| None -> begin
(

let _63_1139 = (let _158_921 = (let _158_920 = (FStar_Range.string_of_range (FStar_Ident.range_of_lid l))
in (let _158_919 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format2 "%s: Warning: Admitting %s without a definition\n" _158_920 _158_919)))
in (FStar_Util.print_string _158_921))
in (FStar_Util.smap_add (sigmap env) l.FStar_Ident.str ((FStar_Syntax_Syntax.Sig_declare_typ (((l), (u), (t), ((FStar_Syntax_Syntax.Assumption)::quals), (r)))), (false))))
end
| Some (_63_1142) -> begin
()
end)
end
| _63_1145 -> begin
()
end)))))


let finish : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env modul -> (

let _63_1205 = (FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations (FStar_List.iter (fun _63_30 -> (match (_63_30) with
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _63_1152, _63_1154) -> begin
if ((FStar_List.contains FStar_Syntax_Syntax.Private quals) || (FStar_List.contains FStar_Syntax_Syntax.Abstract quals)) then begin
(FStar_All.pipe_right ses (FStar_List.iter (fun _63_29 -> (match (_63_29) with
| FStar_Syntax_Syntax.Sig_datacon (lid, _63_1160, _63_1162, _63_1164, _63_1166, _63_1168, _63_1170, _63_1172) -> begin
(FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str)
end
| _63_1176 -> begin
()
end))))
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _63_1179, _63_1181, quals, _63_1184) -> begin
if (FStar_List.contains FStar_Syntax_Syntax.Private quals) then begin
(FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str)
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_let ((_63_1188, lbs), r, _63_1193, quals) -> begin
(

let _63_1198 = if ((FStar_List.contains FStar_Syntax_Syntax.Private quals) || (FStar_List.contains FStar_Syntax_Syntax.Abstract quals)) then begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (let _158_932 = (let _158_931 = (let _158_930 = (let _158_929 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _158_929.FStar_Syntax_Syntax.fv_name)
in _158_930.FStar_Syntax_Syntax.v)
in _158_931.FStar_Ident.str)
in (FStar_Util.smap_remove (sigmap env) _158_932)))))
end else begin
()
end
in if ((FStar_List.contains FStar_Syntax_Syntax.Abstract quals) && (not ((FStar_List.contains FStar_Syntax_Syntax.Private quals)))) then begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (

let lid = (let _158_935 = (let _158_934 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _158_934.FStar_Syntax_Syntax.fv_name)
in _158_935.FStar_Syntax_Syntax.v)
in (

let decl = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), ((FStar_Syntax_Syntax.Assumption)::quals), (r)))
in (FStar_Util.smap_add (sigmap env) lid.FStar_Ident.str ((decl), (false))))))))
end else begin
()
end)
end
| _63_1204 -> begin
()
end))))
in (

let curmod = (let _158_936 = (current_module env)
in _158_936.FStar_Ident.str)
in (

let _63_1219 = (match ((let _158_942 = (get_exported_id_set env curmod)
in (let _158_941 = (get_trans_exported_id_set env curmod)
in ((_158_942), (_158_941))))) with
| (Some (cur_ex), Some (cur_trans_ex)) -> begin
(

let update_exports = (fun eikind -> (

let cur_ex_set = (let _158_947 = (cur_ex eikind)
in (FStar_ST.read _158_947))
in (

let cur_trans_ex_set_ref = (cur_trans_ex eikind)
in (let _158_949 = (let _158_948 = (FStar_ST.read cur_trans_ex_set_ref)
in (FStar_Util.set_union cur_ex_set _158_948))
in (FStar_ST.op_Colon_Equals cur_trans_ex_set_ref _158_949)))))
in (FStar_List.iter update_exports all_exported_id_kinds))
end
| _63_1218 -> begin
()
end)
in (match (()) with
| () -> begin
(

let _63_1220 = env
in {curmodule = None; curmonad = _63_1220.curmonad; modules = (((modul.FStar_Syntax_Syntax.name), (modul)))::env.modules; scope_mods = []; exported_ids = _63_1220.exported_ids; trans_exported_ids = _63_1220.trans_exported_ids; includes = _63_1220.includes; sigaccum = []; sigmap = _63_1220.sigmap; default_result_effect = _63_1220.default_result_effect; iface = _63_1220.iface; admitted_iface = _63_1220.admitted_iface; expect_typ = _63_1220.expect_typ})
end)))))


type env_stack_ops =
{push : env  ->  env; mark : env  ->  env; reset_mark : env  ->  env; commit_mark : env  ->  env; pop : env  ->  env}


let is_Mkenv_stack_ops : env_stack_ops  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv_stack_ops"))))


let stack_ops : env_stack_ops = (

let stack = (FStar_Util.mk_ref [])
in (

let push = (fun env -> (

let _63_1231 = (push_record_cache ())
in (

let _63_1233 = (let _158_1005 = (let _158_1004 = (FStar_ST.read stack)
in (env)::_158_1004)
in (FStar_ST.op_Colon_Equals stack _158_1005))
in (

let _63_1235 = env
in (let _158_1006 = (FStar_Util.smap_copy (sigmap env))
in {curmodule = _63_1235.curmodule; curmonad = _63_1235.curmonad; modules = _63_1235.modules; scope_mods = _63_1235.scope_mods; exported_ids = _63_1235.exported_ids; trans_exported_ids = _63_1235.trans_exported_ids; includes = _63_1235.includes; sigaccum = _63_1235.sigaccum; sigmap = _158_1006; default_result_effect = _63_1235.default_result_effect; iface = _63_1235.iface; admitted_iface = _63_1235.admitted_iface; expect_typ = _63_1235.expect_typ})))))
in (

let pop = (fun env -> (match ((FStar_ST.read stack)) with
| (env)::tl -> begin
(

let _63_1242 = (pop_record_cache ())
in (

let _63_1244 = (FStar_ST.op_Colon_Equals stack tl)
in env))
end
| _63_1247 -> begin
(FStar_All.failwith "Impossible: Too many pops")
end))
in (

let commit_mark = (fun env -> (

let _63_1250 = (commit_record_cache ())
in (match ((FStar_ST.read stack)) with
| (_63_1254)::tl -> begin
(

let _63_1256 = (FStar_ST.op_Colon_Equals stack tl)
in env)
end
| _63_1259 -> begin
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
| (l)::_63_1270 -> begin
(l.FStar_Ident.nsstr = m.FStar_Ident.str)
end
| _63_1274 -> begin
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

let _63_1298 = (FStar_All.pipe_right keys (FStar_List.iter (fun k -> (match ((FStar_Util.smap_try_find sm' k)) with
| Some (se, true) when (sigelt_in_m se) -> begin
(

let _63_1284 = (FStar_Util.smap_remove sm' k)
in (

let se = (match (se) with
| FStar_Syntax_Syntax.Sig_declare_typ (l, u, t, q, r) -> begin
FStar_Syntax_Syntax.Sig_declare_typ (((l), (u), (t), ((FStar_Syntax_Syntax.Assumption)::q), (r)))
end
| _63_1294 -> begin
se
end)
in (FStar_Util.smap_add sm' k ((se), (false)))))
end
| _63_1297 -> begin
()
end))))
in env)))))))


let finish_module_or_interface : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env modul -> (

let _63_1302 = if (not (modul.FStar_Syntax_Syntax.is_interface)) then begin
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

let _63_1313 = (let _158_1042 = (exported_id_set_new ())
in (FStar_Util.smap_add env.exported_ids mname.FStar_Ident.str _158_1042))
in (match (()) with
| () -> begin
(

let _63_1314 = (let _158_1043 = (exported_id_set_new ())
in (FStar_Util.smap_add env.trans_exported_ids mname.FStar_Ident.str _158_1043))
in (match (()) with
| () -> begin
(

let _63_1315 = (let _158_1044 = (FStar_Util.mk_ref [])
in (FStar_Util.smap_add env.includes mname.FStar_Ident.str _158_1044))
in (match (()) with
| () -> begin
(

let _63_1316 = env
in (let _158_1046 = (FStar_List.map (fun lid -> Open_module_or_namespace (((lid), (Open_namespace)))) open_ns)
in {curmodule = Some (mname); curmonad = _63_1316.curmonad; modules = _63_1316.modules; scope_mods = _158_1046; exported_ids = _63_1316.exported_ids; trans_exported_ids = _63_1316.trans_exported_ids; includes = _63_1316.includes; sigaccum = _63_1316.sigaccum; sigmap = env.sigmap; default_result_effect = if ((FStar_Ident.lid_equals mname FStar_Syntax_Const.all_lid) || (has_all_in_scope env)) then begin
FStar_Syntax_Const.effect_ML_lid
end else begin
FStar_Syntax_Const.effect_Tot_lid
end; iface = intf; admitted_iface = admitted; expect_typ = _63_1316.expect_typ}))
end))
end))
end)))))
in (match ((FStar_All.pipe_right env.modules (FStar_Util.find_opt (fun _63_1322 -> (match (_63_1322) with
| (l, _63_1321) -> begin
(FStar_Ident.lid_equals l mname)
end))))) with
| None -> begin
(let _158_1048 = (prep env)
in ((_158_1048), (false)))
end
| Some (_63_1325, m) -> begin
(

let _63_1329 = if ((not (m.FStar_Syntax_Syntax.is_interface)) || intf) then begin
(let _158_1051 = (let _158_1050 = (let _158_1049 = (FStar_Util.format1 "Duplicate module or interface name: %s" mname.FStar_Ident.str)
in ((_158_1049), ((FStar_Ident.range_of_lid mname))))
in FStar_Syntax_Syntax.Error (_158_1050))
in (Prims.raise _158_1051))
end else begin
()
end
in (let _158_1053 = (let _158_1052 = (push env)
in (prep _158_1052))
in ((_158_1053), (true))))
end)))


let enter_monad_scope : env  ->  FStar_Ident.ident  ->  env = (fun env mname -> (match (env.curmonad) with
| Some (mname') -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((((Prims.strcat "Trying to define monad " (Prims.strcat mname.FStar_Ident.idText (Prims.strcat ", but already in monad scope " mname'.FStar_Ident.idText)))), (mname.FStar_Ident.idRange)))))
end
| None -> begin
(

let _63_1336 = env
in {curmodule = _63_1336.curmodule; curmonad = Some (mname); modules = _63_1336.modules; scope_mods = _63_1336.scope_mods; exported_ids = _63_1336.exported_ids; trans_exported_ids = _63_1336.trans_exported_ids; includes = _63_1336.includes; sigaccum = _63_1336.sigaccum; sigmap = _63_1336.sigmap; default_result_effect = _63_1336.default_result_effect; iface = _63_1336.iface; admitted_iface = _63_1336.admitted_iface; expect_typ = _63_1336.expect_typ})
end))


let fail_or = (fun env lookup lid -> (match ((lookup lid)) with
| None -> begin
(

let opened_modules = (FStar_List.map (fun _63_1345 -> (match (_63_1345) with
| (lid, _63_1344) -> begin
(FStar_Ident.text_of_lid lid)
end)) env.modules)
in (

let msg = (FStar_Util.format1 "Identifier not found: [%s]" (FStar_Ident.text_of_lid lid))
in (

let msg = if ((FStar_List.length lid.FStar_Ident.ns) = (Prims.parse_int "0")) then begin
msg
end else begin
(

let modul = (let _158_1065 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in (FStar_Ident.set_lid_range _158_1065 (FStar_Ident.range_of_lid lid)))
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




