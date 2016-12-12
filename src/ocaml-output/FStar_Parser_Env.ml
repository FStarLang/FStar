
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
| Local_binding (_63_40) -> begin
_63_40
end))


let ___Rec_binding____0 = (fun projectee -> (match (projectee) with
| Rec_binding (_63_43) -> begin
_63_43
end))


let ___Module_abbrev____0 = (fun projectee -> (match (projectee) with
| Module_abbrev (_63_46) -> begin
_63_46
end))


let ___Open_module_or_namespace____0 = (fun projectee -> (match (projectee) with
| Open_module_or_namespace (_63_49) -> begin
_63_49
end))


let ___Top_level_def____0 = (fun projectee -> (match (projectee) with
| Top_level_def (_63_52) -> begin
_63_52
end))


let ___Record_or_dc____0 = (fun projectee -> (match (projectee) with
| Record_or_dc (_63_55) -> begin
_63_55
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
| Term_name (_63_72) -> begin
_63_72
end))


let ___Eff_name____0 = (fun projectee -> (match (projectee) with
| Eff_name (_63_75) -> begin
_63_75
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
(let _158_188 = (current_module env)
in (qual _158_188 id))
end
| Some (monad) -> begin
(let _158_190 = (let _158_189 = (current_module env)
in (qual _158_189 monad))
in (FStar_Syntax_Util.mk_field_projector_name_from_ident _158_190 id))
end))


let new_sigmap = (fun _63_88 -> (match (()) with
| () -> begin
(FStar_Util.smap_create (Prims.parse_int "100"))
end))


let empty_env : Prims.unit  ->  env = (fun _63_89 -> (match (()) with
| () -> begin
(let _158_197 = (new_sigmap ())
in (let _158_196 = (new_sigmap ())
in (let _158_195 = (new_sigmap ())
in (let _158_194 = (new_sigmap ())
in {curmodule = None; curmonad = None; modules = []; scope_mods = []; exported_ids = _158_197; trans_exported_ids = _158_196; includes = _158_195; sigaccum = []; sigmap = _158_194; default_result_effect = FStar_Syntax_Const.effect_Tot_lid; iface = false; admitted_iface = false; expect_typ = false}))))
end))


let sigmap : env  ->  (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap = (fun env -> env.sigmap)


let has_all_in_scope : env  ->  Prims.bool = (fun env -> (FStar_List.existsb (fun _63_95 -> (match (_63_95) with
| (m, _63_94) -> begin
(FStar_Ident.lid_equals m FStar_Syntax_Const.all_lid)
end)) env.modules))


let default_total : env  ->  env = (fun env -> (

let _63_97 = env
in {curmodule = _63_97.curmodule; curmonad = _63_97.curmonad; modules = _63_97.modules; scope_mods = _63_97.scope_mods; exported_ids = _63_97.exported_ids; trans_exported_ids = _63_97.trans_exported_ids; includes = _63_97.includes; sigaccum = _63_97.sigaccum; sigmap = _63_97.sigmap; default_result_effect = FStar_Syntax_Const.effect_Tot_lid; iface = _63_97.iface; admitted_iface = _63_97.admitted_iface; expect_typ = _63_97.expect_typ}))


let default_ml : env  ->  env = (fun env -> if (has_all_in_scope env) then begin
(

let _63_100 = env
in {curmodule = _63_100.curmodule; curmonad = _63_100.curmonad; modules = _63_100.modules; scope_mods = _63_100.scope_mods; exported_ids = _63_100.exported_ids; trans_exported_ids = _63_100.trans_exported_ids; includes = _63_100.includes; sigaccum = _63_100.sigaccum; sigmap = _63_100.sigmap; default_result_effect = FStar_Syntax_Const.effect_ML_lid; iface = _63_100.iface; admitted_iface = _63_100.admitted_iface; expect_typ = _63_100.expect_typ})
end else begin
env
end)


let set_bv_range : FStar_Syntax_Syntax.bv  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.bv = (fun bv r -> (

let id = (

let _63_104 = bv.FStar_Syntax_Syntax.ppname
in {FStar_Ident.idText = _63_104.FStar_Ident.idText; FStar_Ident.idRange = r})
in (

let _63_107 = bv
in {FStar_Syntax_Syntax.ppname = id; FStar_Syntax_Syntax.index = _63_107.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _63_107.FStar_Syntax_Syntax.sort})))


let bv_to_name : FStar_Syntax_Syntax.bv  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.term = (fun bv r -> (FStar_Syntax_Syntax.bv_to_name (set_bv_range bv r)))


let unmangleMap : (Prims.string * Prims.string * FStar_Syntax_Syntax.delta_depth * FStar_Syntax_Syntax.fv_qual Prims.option) Prims.list = ((("op_ColonColon"), ("Cons"), (FStar_Syntax_Syntax.Delta_constant), (Some (FStar_Syntax_Syntax.Data_ctor))))::((("not"), ("op_Negation"), (FStar_Syntax_Syntax.Delta_equational), (None)))::[]


let unmangleOpName : FStar_Ident.ident  ->  (FStar_Syntax_Syntax.term * Prims.bool) Prims.option = (fun id -> (

let t = (FStar_Util.find_map unmangleMap (fun _63_116 -> (match (_63_116) with
| (x, y, dd, dq) -> begin
if (id.FStar_Ident.idText = x) then begin
(let _158_219 = (let _158_218 = (FStar_Ident.lid_of_path (("Prims")::(y)::[]) id.FStar_Ident.idRange)
in (FStar_Syntax_Syntax.fvar _158_218 dd dq))
in Some (_158_219))
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
| Cont_ok (_63_124) -> begin
_63_124
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

let find = (FStar_Util.find_map record.fields (fun _63_141 -> (match (_63_141) with
| (f, _63_140) -> begin
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

let mexports = (let _158_289 = (mex eikind)
in (FStar_ST.read _158_289))
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
(let _158_290 = (qual modul id)
in (find_in_module _158_290))
end else begin
Cont_ignore
end
in (match (look_into) with
| Cont_ignore -> begin
(aux (FStar_List.append mincludes q))
end
| _63_180 -> begin
look_into
end)))))
end))
in (aux ((ns)::[])))))


let is_exported_id_field : exported_id_kind  ->  Prims.bool = (fun _63_4 -> (match (_63_4) with
| Exported_id_field -> begin
true
end
| _63_184 -> begin
false
end))


let try_lookup_id'' = (fun env id eikind k_local_binding k_rec_binding k_record find_in_module lookup_default_id -> (

let check_local_binding_id = (fun _63_5 -> (match (_63_5) with
| (id', _63_197, _63_199) -> begin
(id'.FStar_Ident.idText = id.FStar_Ident.idText)
end))
in (

let check_rec_binding_id = (fun _63_6 -> (match (_63_6) with
| (id', _63_205, _63_207) -> begin
(id'.FStar_Ident.idText = id.FStar_Ident.idText)
end))
in (

let curmod_ns = (let _158_323 = (current_module env)
in (FStar_Ident.ids_of_lid _158_323))
in (

let proc = (fun _63_7 -> (match (_63_7) with
| Local_binding (l) when (check_local_binding_id l) -> begin
(k_local_binding l)
end
| Rec_binding (r) when (check_rec_binding_id r) -> begin
(k_rec_binding r)
end
| Open_module_or_namespace (ns, _63_218) -> begin
(find_in_module_with_includes eikind find_in_module Cont_ignore env ns id)
end
| Top_level_def (id') when (id'.FStar_Ident.idText = id.FStar_Ident.idText) -> begin
(lookup_default_id Cont_ignore id)
end
| Record_or_dc (r) when (is_exported_id_field eikind) -> begin
(let _158_327 = (FStar_Ident.lid_of_ids curmod_ns)
in (find_in_module_with_includes Exported_id_field (fun lid -> (

let id = lid.FStar_Ident.ident
in (find_in_record lid.FStar_Ident.ns id r k_record))) Cont_ignore env _158_327 id))
end
| _63_228 -> begin
Cont_ignore
end))
in (

let rec aux = (fun _63_8 -> (match (_63_8) with
| (a)::q -> begin
(let _158_331 = (proc a)
in (option_of_cont (fun _63_235 -> (aux q)) _158_331))
end
| [] -> begin
(let _158_333 = (lookup_default_id Cont_fail id)
in (option_of_cont (fun _63_238 -> None) _158_333))
end))
in (aux env.scope_mods)))))))


let found_local_binding = (fun r _63_244 -> (match (_63_244) with
| (id', x, mut) -> begin
(let _158_336 = (bv_to_name x r)
in ((_158_336), (mut)))
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
(try_lookup_id'' env id Exported_id_term_type (fun r -> (let _158_352 = (found_local_binding id.FStar_Ident.idRange r)
in Cont_ok (_158_352))) (fun _63_269 -> Cont_fail) (fun _63_267 -> Cont_ignore) (fun i -> (find_in_module env i (fun _63_263 _63_265 -> Cont_fail) Cont_ignore)) (fun _63_258 _63_260 -> Cont_fail))
end))


let lookup_default_id = (fun env id k_global_def k_not_found -> (

let find_in_monad = (match (env.curmonad) with
| Some (_63_278) -> begin
(

let lid = (qualify env id)
in (match ((FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str)) with
| Some (r) -> begin
(let _158_370 = (k_global_def lid r)
in Some (_158_370))
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

let lid = (let _158_371 = (current_module env)
in (qual _158_371 id))
in (find_in_module env lid k_global_def k_not_found))
end)))


let module_is_defined : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> ((let _158_376 = (current_module env)
in (FStar_Ident.lid_equals lid _158_376)) || (FStar_List.existsb (fun x -> (FStar_Ident.lid_equals lid (Prims.fst x))) env.modules)))


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

let new_lid = (let _158_388 = (let _158_387 = (FStar_Ident.path_of_lid ns)
in (let _158_386 = (FStar_Ident.path_of_lid lid)
in (FStar_List.append _158_387 _158_386)))
in (FStar_Ident.lid_of_path _158_388 (FStar_Ident.range_of_lid lid)))
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
(match ((let _158_416 = (let _158_415 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in (FStar_Ident.set_lid_range _158_415 (FStar_Ident.range_of_lid lid)))
in (resolve_module_name env _158_416 true))) with
| None -> begin
None
end
| Some (modul) -> begin
(let _158_418 = (find_in_module_with_includes eikind f_module Cont_fail env modul lid.FStar_Ident.ident)
in (option_of_cont (fun _63_335 -> None) _158_418))
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

let k_global_def' = (fun k lid def -> (let _158_444 = (k_global_def lid def)
in (cont_of_option k _158_444)))
in (

let f_module = (fun lid' -> (

let k = Cont_ignore
in (find_in_module env lid' (k_global_def' k) k)))
in (

let l_default = (fun k i -> (lookup_default_id env i (k_global_def' k) k))
in (resolve_in_open_namespaces'' env lid Exported_id_term_type (fun l -> (let _158_452 = (k_local_binding l)
in (cont_of_option Cont_fail _158_452))) (fun r -> (let _158_454 = (k_rec_binding r)
in (cont_of_option Cont_fail _158_454))) (fun _63_360 -> Cont_ignore) f_module l_default)))))


let fv_qual_of_se : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.fv_qual Prims.option = (fun _63_12 -> (match (_63_12) with
| FStar_Syntax_Syntax.Sig_datacon (_63_366, _63_368, _63_370, l, _63_373, quals, _63_376, _63_378) -> begin
(

let qopt = (FStar_Util.find_map quals (fun _63_11 -> (match (_63_11) with
| FStar_Syntax_Syntax.RecordConstructor (_63_383, fs) -> begin
Some (FStar_Syntax_Syntax.Record_ctor (((l), (fs))))
end
| _63_388 -> begin
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
| FStar_Syntax_Syntax.Sig_declare_typ (_63_393, _63_395, _63_397, quals, _63_400) -> begin
None
end
| _63_404 -> begin
None
end))


let lb_fv : FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.fv = (fun lbs lid -> (let _158_464 = (FStar_Util.find_map lbs (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in if (FStar_Syntax_Syntax.fv_eq_lid fv lid) then begin
Some (fv)
end else begin
None
end)))
in (FStar_All.pipe_right _158_464 FStar_Util.must)))


let ns_of_lid_equals : FStar_Ident.lident  ->  FStar_Ident.lident  ->  Prims.bool = (fun lid ns -> (((FStar_List.length lid.FStar_Ident.ns) = (FStar_List.length (FStar_Ident.ids_of_lid ns))) && (let _158_469 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in (FStar_Ident.lid_equals _158_469 ns))))


let try_lookup_name : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  foundname Prims.option = (fun any_val exclude_interf env lid -> (

let occurrence_range = (FStar_Ident.range_of_lid lid)
in (

let k_global_def = (fun source_lid _63_16 -> (match (_63_16) with
| (_63_420, true) when exclude_interf -> begin
None
end
| (se, _63_425) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_63_428) -> begin
(let _158_484 = (let _158_483 = (let _158_482 = (FStar_Syntax_Syntax.fvar source_lid FStar_Syntax_Syntax.Delta_constant None)
in ((_158_482), (false)))
in Term_name (_158_483))
in Some (_158_484))
end
| FStar_Syntax_Syntax.Sig_datacon (_63_431) -> begin
(let _158_488 = (let _158_487 = (let _158_486 = (let _158_485 = (fv_qual_of_se se)
in (FStar_Syntax_Syntax.fvar source_lid FStar_Syntax_Syntax.Delta_constant _158_485))
in ((_158_486), (false)))
in Term_name (_158_487))
in Some (_158_488))
end
| FStar_Syntax_Syntax.Sig_let ((_63_434, lbs), _63_438, _63_440, _63_442) -> begin
(

let fv = (lb_fv lbs source_lid)
in (let _158_491 = (let _158_490 = (let _158_489 = (FStar_Syntax_Syntax.fvar source_lid fv.FStar_Syntax_Syntax.fv_delta fv.FStar_Syntax_Syntax.fv_qual)
in ((_158_489), (false)))
in Term_name (_158_490))
in Some (_158_491)))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _63_448, _63_450, quals, _63_453) -> begin
if (any_val || (FStar_All.pipe_right quals (FStar_Util.for_some (fun _63_13 -> (match (_63_13) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| _63_459 -> begin
false
end))))) then begin
(

let lid = (FStar_Ident.set_lid_range lid (FStar_Ident.range_of_lid source_lid))
in (

let dd = if ((FStar_Syntax_Util.is_primop_lid lid) || ((ns_of_lid_equals lid FStar_Syntax_Const.prims_lid) && (FStar_All.pipe_right quals (FStar_Util.for_some (fun _63_14 -> (match (_63_14) with
| (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) -> begin
true
end
| _63_469 -> begin
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
| _63_475 -> begin
None
end)))) with
| Some (refl_monad) -> begin
(

let refl_const = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (refl_monad))) None occurrence_range)
in Some (Term_name (((refl_const), (false)))))
end
| _63_480 -> begin
(let _158_498 = (let _158_497 = (let _158_496 = (let _158_495 = (fv_qual_of_se se)
in (FStar_Syntax_Syntax.fvar lid dd _158_495))
in ((_158_496), (false)))
in Term_name (_158_497))
in Some (_158_498))
end)))
end else begin
None
end
end
| (FStar_Syntax_Syntax.Sig_new_effect_for_free (ne, _)) | (FStar_Syntax_Syntax.Sig_new_effect (ne, _)) -> begin
Some (Eff_name (((se), ((FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname (FStar_Ident.range_of_lid source_lid))))))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (_63_491) -> begin
Some (Eff_name (((se), (source_lid))))
end
| _63_494 -> begin
None
end)
end))
in (

let k_local_binding = (fun r -> (let _158_502 = (let _158_501 = (found_local_binding (FStar_Ident.range_of_lid lid) r)
in Term_name (_158_501))
in Some (_158_502)))
in (

let k_rec_binding = (fun _63_501 -> (match (_63_501) with
| (id, l, dd) -> begin
(let _158_507 = (let _158_506 = (let _158_505 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range l (FStar_Ident.range_of_lid lid)) dd None)
in ((_158_505), (false)))
in Term_name (_158_506))
in Some (_158_507))
end))
in (

let found_unmangled = (match (lid.FStar_Ident.ns) with
| [] -> begin
(match ((unmangleOpName lid.FStar_Ident.ident)) with
| Some (f) -> begin
Some (Term_name (f))
end
| _63_506 -> begin
None
end)
end
| _63_508 -> begin
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
| _63_521 -> begin
None
end))


let try_lookup_effect_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env l -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some (o, l) -> begin
Some (l)
end
| _63_529 -> begin
None
end))


let try_lookup_effect_name_and_attributes : env  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.cflags Prims.list) Prims.option = (fun env l -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some (FStar_Syntax_Syntax.Sig_new_effect (ne, _63_534), l) -> begin
Some (((l), (ne.FStar_Syntax_Syntax.cattributes)))
end
| Some (FStar_Syntax_Syntax.Sig_new_effect_for_free (ne, _63_542), l) -> begin
Some (((l), (ne.FStar_Syntax_Syntax.cattributes)))
end
| Some (FStar_Syntax_Syntax.Sig_effect_abbrev (_63_549, _63_551, _63_553, _63_555, _63_557, cattributes, _63_560), l) -> begin
Some (((l), (cattributes)))
end
| _63_567 -> begin
None
end))


let try_lookup_effect_defn : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl Prims.option = (fun env l -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some (FStar_Syntax_Syntax.Sig_new_effect (ne, _63_572), _63_576) -> begin
Some (ne)
end
| Some (FStar_Syntax_Syntax.Sig_new_effect_for_free (ne, _63_581), _63_585) -> begin
Some (ne)
end
| _63_589 -> begin
None
end))


let is_effect_name : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((try_lookup_effect_name env lid)) with
| None -> begin
false
end
| Some (_63_594) -> begin
true
end))


let lookup_letbinding_quals : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.qualifier Prims.list = (fun env lid -> (

let k_global_def = (fun lid _63_17 -> (match (_63_17) with
| (FStar_Syntax_Syntax.Sig_declare_typ (lid, _63_603, _63_605, quals, _63_608), _63_612) -> begin
Some (quals)
end
| _63_615 -> begin
None
end))
in (match ((resolve_in_open_namespaces' env lid (fun _63_618 -> None) (fun _63_616 -> None) k_global_def)) with
| Some (quals) -> begin
quals
end
| _63_623 -> begin
[]
end)))


let try_lookup_module : env  ->  Prims.string Prims.list  ->  FStar_Syntax_Syntax.modul Prims.option = (fun env path -> (match ((FStar_List.tryFind (fun _63_628 -> (match (_63_628) with
| (mlid, modul) -> begin
((FStar_Ident.path_of_lid mlid) = path)
end)) env.modules)) with
| Some (_63_630, modul) -> begin
Some (modul)
end
| None -> begin
None
end))


let try_lookup_let : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env lid -> (

let k_global_def = (fun lid _63_18 -> (match (_63_18) with
| (FStar_Syntax_Syntax.Sig_let ((_63_641, lbs), _63_645, _63_647, _63_649), _63_653) -> begin
(

let fv = (lb_fv lbs lid)
in (let _158_553 = (FStar_Syntax_Syntax.fvar lid fv.FStar_Syntax_Syntax.fv_delta fv.FStar_Syntax_Syntax.fv_qual)
in Some (_158_553)))
end
| _63_657 -> begin
None
end))
in (resolve_in_open_namespaces' env lid (fun _63_660 -> None) (fun _63_658 -> None) k_global_def)))


let try_lookup_definition : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env lid -> (

let k_global_def = (fun lid _63_19 -> (match (_63_19) with
| (FStar_Syntax_Syntax.Sig_let (lbs, _63_669, _63_671, _63_673), _63_677) -> begin
(FStar_Util.find_map (Prims.snd lbs) (fun lb -> (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv lid) -> begin
Some (lb.FStar_Syntax_Syntax.lbdef)
end
| _63_683 -> begin
None
end)))
end
| _63_685 -> begin
None
end))
in (resolve_in_open_namespaces' env lid (fun _63_688 -> None) (fun _63_686 -> None) k_global_def)))


let try_lookup_lid' : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term * Prims.bool) Prims.option = (fun any_val exclude_interf env lid -> (match ((try_lookup_name any_val exclude_interf env lid)) with
| Some (Term_name (e, mut)) -> begin
Some (((e), (mut)))
end
| _63_700 -> begin
None
end))


let try_lookup_lid : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term * Prims.bool) Prims.option = (fun env l -> (try_lookup_lid' env.iface false env l))


let try_lookup_datacon : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.fv Prims.option = (fun env lid -> (

let k_global_def = (fun lid _63_21 -> (match (_63_21) with
| (FStar_Syntax_Syntax.Sig_declare_typ (_63_709, _63_711, _63_713, quals, _63_716), _63_720) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _63_20 -> (match (_63_20) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| _63_725 -> begin
false
end)))) then begin
(let _158_588 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant None)
in Some (_158_588))
end else begin
None
end
end
| (FStar_Syntax_Syntax.Sig_datacon (_63_727), _63_730) -> begin
(let _158_589 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in Some (_158_589))
end
| _63_733 -> begin
None
end))
in (resolve_in_open_namespaces' env lid (fun _63_736 -> None) (fun _63_734 -> None) k_global_def)))


let find_all_datacons : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.list Prims.option = (fun env lid -> (

let k_global_def = (fun lid _63_22 -> (match (_63_22) with
| (FStar_Syntax_Syntax.Sig_inductive_typ (_63_744, _63_746, _63_748, _63_750, _63_752, datas, _63_755, _63_757), _63_761) -> begin
Some (datas)
end
| _63_764 -> begin
None
end))
in (resolve_in_open_namespaces' env lid (fun _63_767 -> None) (fun _63_765 -> None) k_global_def)))


let record_cache_aux_with_filter : (((Prims.unit  ->  Prims.unit) * (Prims.unit  ->  Prims.unit) * (Prims.unit  ->  record_or_dc Prims.list) * (record_or_dc  ->  Prims.unit) * (Prims.unit  ->  Prims.unit)) * (Prims.unit  ->  Prims.unit)) = (

let record_cache = (FStar_Util.mk_ref (([])::[]))
in (

let push = (fun _63_771 -> (match (()) with
| () -> begin
(let _158_624 = (let _158_623 = (let _158_621 = (FStar_ST.read record_cache)
in (FStar_List.hd _158_621))
in (let _158_622 = (FStar_ST.read record_cache)
in (_158_623)::_158_622))
in (FStar_ST.op_Colon_Equals record_cache _158_624))
end))
in (

let pop = (fun _63_773 -> (match (()) with
| () -> begin
(let _158_628 = (let _158_627 = (FStar_ST.read record_cache)
in (FStar_List.tl _158_627))
in (FStar_ST.op_Colon_Equals record_cache _158_628))
end))
in (

let peek = (fun _63_775 -> (match (()) with
| () -> begin
(let _158_631 = (FStar_ST.read record_cache)
in (FStar_List.hd _158_631))
end))
in (

let insert = (fun r -> (let _158_638 = (let _158_637 = (let _158_634 = (peek ())
in (r)::_158_634)
in (let _158_636 = (let _158_635 = (FStar_ST.read record_cache)
in (FStar_List.tl _158_635))
in (_158_637)::_158_636))
in (FStar_ST.op_Colon_Equals record_cache _158_638)))
in (

let commit = (fun _63_779 -> (match (()) with
| () -> begin
(match ((FStar_ST.read record_cache)) with
| (hd)::(_63_782)::tl -> begin
(FStar_ST.op_Colon_Equals record_cache ((hd)::tl))
end
| _63_787 -> begin
(FStar_All.failwith "Impossible")
end)
end))
in (

let filter = (fun _63_789 -> (match (()) with
| () -> begin
(

let rc = (peek ())
in (

let _63_791 = (pop ())
in (match (()) with
| () -> begin
(

let filtered = (FStar_List.filter (fun r -> (not (r.is_private_or_abstract))) rc)
in (let _158_645 = (let _158_644 = (FStar_ST.read record_cache)
in (filtered)::_158_644)
in (FStar_ST.op_Colon_Equals record_cache _158_645)))
end)))
end))
in (

let aux = ((push), (pop), (peek), (insert), (commit))
in ((aux), (filter))))))))))


let record_cache_aux : ((Prims.unit  ->  Prims.unit) * (Prims.unit  ->  Prims.unit) * (Prims.unit  ->  record_or_dc Prims.list) * (record_or_dc  ->  Prims.unit) * (Prims.unit  ->  Prims.unit)) = (

let _63_798 = record_cache_aux_with_filter
in (match (_63_798) with
| (aux, _63_797) -> begin
aux
end))


let filter_record_cache : Prims.unit  ->  Prims.unit = (

let _63_802 = record_cache_aux_with_filter
in (match (_63_802) with
| (_63_800, filter) -> begin
filter
end))


let push_record_cache : Prims.unit  ->  Prims.unit = (

let _63_812 = record_cache_aux
in (match (_63_812) with
| (push, _63_805, _63_807, _63_809, _63_811) -> begin
push
end))


let pop_record_cache : Prims.unit  ->  Prims.unit = (

let _63_822 = record_cache_aux
in (match (_63_822) with
| (_63_814, pop, _63_817, _63_819, _63_821) -> begin
pop
end))


let peek_record_cache : Prims.unit  ->  record_or_dc Prims.list = (

let _63_832 = record_cache_aux
in (match (_63_832) with
| (_63_824, _63_826, peek, _63_829, _63_831) -> begin
peek
end))


let insert_record_cache : record_or_dc  ->  Prims.unit = (

let _63_842 = record_cache_aux
in (match (_63_842) with
| (_63_834, _63_836, _63_838, insert, _63_841) -> begin
insert
end))


let commit_record_cache : Prims.unit  ->  Prims.unit = (

let _63_852 = record_cache_aux
in (match (_63_852) with
| (_63_844, _63_846, _63_848, _63_850, commit) -> begin
commit
end))


let extract_record : env  ->  scope_mod Prims.list FStar_ST.ref  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun e new_globs _63_26 -> (match (_63_26) with
| FStar_Syntax_Syntax.Sig_bundle (sigs, _63_858, _63_860, _63_862) -> begin
(

let is_rec = (FStar_Util.for_some (fun _63_23 -> (match (_63_23) with
| (FStar_Syntax_Syntax.RecordType (_)) | (FStar_Syntax_Syntax.RecordConstructor (_)) -> begin
true
end
| _63_873 -> begin
false
end)))
in (

let find_dc = (fun dc -> (FStar_All.pipe_right sigs (FStar_Util.find_opt (fun _63_24 -> (match (_63_24) with
| FStar_Syntax_Syntax.Sig_datacon (lid, _63_880, _63_882, _63_884, _63_886, _63_888, _63_890, _63_892) -> begin
(FStar_Ident.lid_equals dc lid)
end
| _63_896 -> begin
false
end)))))
in (FStar_All.pipe_right sigs (FStar_List.iter (fun _63_25 -> (match (_63_25) with
| FStar_Syntax_Syntax.Sig_inductive_typ (typename, univs, parms, _63_902, _63_904, (dc)::[], tags, _63_909) -> begin
(match ((let _158_847 = (find_dc dc)
in (FStar_All.pipe_left FStar_Util.must _158_847))) with
| FStar_Syntax_Syntax.Sig_datacon (constrname, _63_914, t, _63_917, _63_919, _63_921, _63_923, _63_925) -> begin
(

let _63_931 = (FStar_Syntax_Util.arrow_formals t)
in (match (_63_931) with
| (formals, _63_930) -> begin
(

let is_rec = (is_rec tags)
in (

let formals' = (FStar_All.pipe_right formals (FStar_List.collect (fun _63_935 -> (match (_63_935) with
| (x, q) -> begin
if ((FStar_Syntax_Syntax.is_null_bv x) || (is_rec && (FStar_Syntax_Syntax.is_implicit q))) then begin
[]
end else begin
(((x), (q)))::[]
end
end))))
in (

let fields' = (FStar_All.pipe_right formals' (FStar_List.map (fun _63_939 -> (match (_63_939) with
| (x, q) -> begin
(let _158_850 = if is_rec then begin
(FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname)
end else begin
x.FStar_Syntax_Syntax.ppname
end
in ((_158_850), (x.FStar_Syntax_Syntax.sort)))
end))))
in (

let fields = fields'
in (

let record = {typename = typename; constrname = constrname.FStar_Ident.ident; parms = parms; fields = fields; is_private_or_abstract = ((FStar_List.contains FStar_Syntax_Syntax.Private tags) || (FStar_List.contains FStar_Syntax_Syntax.Abstract tags)); is_record = is_rec}
in (

let _63_943 = (let _158_852 = (let _158_851 = (FStar_ST.read new_globs)
in (Record_or_dc (record))::_158_851)
in (FStar_ST.op_Colon_Equals new_globs _158_852))
in (match (()) with
| () -> begin
(

let _63_957 = (

let add_field = (fun _63_948 -> (match (_63_948) with
| (id, _63_947) -> begin
(

let modul = (let _158_855 = (FStar_Ident.lid_of_ids constrname.FStar_Ident.ns)
in _158_855.FStar_Ident.str)
in (match ((get_exported_id_set e modul)) with
| Some (my_ex) -> begin
(

let my_exported_ids = (my_ex Exported_id_field)
in (

let _63_953 = (let _158_858 = (let _158_857 = (FStar_ST.read my_exported_ids)
in (FStar_Util.set_add id.FStar_Ident.idText _158_857))
in (FStar_ST.op_Colon_Equals my_exported_ids _158_858))
in (match (()) with
| () -> begin
(

let projname = (let _158_860 = (let _158_859 = (FStar_Syntax_Util.mk_field_projector_name_from_ident constrname id)
in _158_859.FStar_Ident.ident)
in _158_860.FStar_Ident.idText)
in (

let _63_955 = (let _158_862 = (let _158_861 = (FStar_ST.read my_exported_ids)
in (FStar_Util.set_add projname _158_861))
in (FStar_ST.op_Colon_Equals my_exported_ids _158_862))
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
| _63_959 -> begin
()
end)
end
| _63_961 -> begin
()
end))))))
end
| _63_963 -> begin
()
end))


let try_lookup_record_or_dc_by_field_name : env  ->  FStar_Ident.lident  ->  record_or_dc Prims.option = (fun env fieldname -> (

let find_in_cache = (fun fieldname -> (

let _63_970 = ((fieldname.FStar_Ident.ns), (fieldname.FStar_Ident.ident))
in (match (_63_970) with
| (ns, id) -> begin
(let _158_873 = (peek_record_cache ())
in (FStar_Util.find_map _158_873 (fun record -> (let _158_872 = (find_in_record ns id record (fun r -> Cont_ok (r)))
in (option_of_cont (fun _63_973 -> None) _158_872)))))
end)))
in (resolve_in_open_namespaces'' env fieldname Exported_id_field (fun _63_982 -> Cont_ignore) (fun _63_980 -> Cont_ignore) (fun r -> Cont_ok (r)) (fun fn -> (let _158_878 = (find_in_cache fn)
in (cont_of_option Cont_ignore _158_878))) (fun k _63_976 -> k))))


let try_lookup_record_by_field_name : env  ->  FStar_Ident.lident  ->  record_or_dc Prims.option = (fun env fieldname -> (match ((try_lookup_record_or_dc_by_field_name env fieldname)) with
| Some (r) when r.is_record -> begin
Some (r)
end
| _63_989 -> begin
None
end))


let belongs_to_record : env  ->  FStar_Ident.lident  ->  record_or_dc  ->  Prims.bool = (fun env lid record -> (match ((try_lookup_record_by_field_name env lid)) with
| Some (record') when ((let _158_891 = (FStar_Ident.path_of_ns record.typename.FStar_Ident.ns)
in (FStar_Ident.text_of_path _158_891)) = (let _158_892 = (FStar_Ident.path_of_ns record'.typename.FStar_Ident.ns)
in (FStar_Ident.text_of_path _158_892))) -> begin
(match ((find_in_record record.typename.FStar_Ident.ns lid.FStar_Ident.ident record (fun _63_995 -> Cont_ok (())))) with
| Cont_ok (_63_998) -> begin
true
end
| _63_1001 -> begin
false
end)
end
| _63_1003 -> begin
false
end))


let try_lookup_dc_by_field_name : env  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * Prims.bool) Prims.option = (fun env fieldname -> (match ((try_lookup_record_or_dc_by_field_name env fieldname)) with
| Some (r) -> begin
(let _158_900 = (let _158_899 = (let _158_898 = (FStar_Ident.lid_of_ids (FStar_List.append r.typename.FStar_Ident.ns ((r.constrname)::[])))
in (FStar_Ident.set_lid_range _158_898 (FStar_Ident.range_of_lid fieldname)))
in ((_158_899), (r.is_record)))
in Some (_158_900))
end
| _63_1009 -> begin
None
end))


let string_set_ref_new : Prims.unit  ->  Prims.string FStar_Util.set FStar_ST.ref = (fun _63_1010 -> (match (()) with
| () -> begin
(let _158_903 = (FStar_Util.new_set FStar_Util.compare FStar_Util.hashcode)
in (FStar_Util.mk_ref _158_903))
end))


let exported_id_set_new : Prims.unit  ->  exported_id_kind  ->  Prims.string FStar_Util.set FStar_ST.ref = (fun _63_1011 -> (match (()) with
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
| Rec_binding (_63_1023) -> begin
true
end
| _63_1026 -> begin
false
end))
in (

let this_env = (

let _63_1028 = env
in (let _158_923 = (FStar_List.filter filter_scope_mods env.scope_mods)
in {curmodule = _63_1028.curmodule; curmonad = _63_1028.curmonad; modules = _63_1028.modules; scope_mods = _158_923; exported_ids = empty_exported_id_smap; trans_exported_ids = _63_1028.trans_exported_ids; includes = empty_include_smap; sigaccum = _63_1028.sigaccum; sigmap = _63_1028.sigmap; default_result_effect = _63_1028.default_result_effect; iface = _63_1028.iface; admitted_iface = _63_1028.admitted_iface; expect_typ = _63_1028.expect_typ}))
in (match ((try_lookup_lid' any_val exclude_if this_env lid)) with
| None -> begin
true
end
| Some (_63_1033) -> begin
false
end))))


let push_scope_mod : env  ->  scope_mod  ->  env = (fun env scope_mod -> (

let _63_1037 = env
in {curmodule = _63_1037.curmodule; curmonad = _63_1037.curmonad; modules = _63_1037.modules; scope_mods = (scope_mod)::env.scope_mods; exported_ids = _63_1037.exported_ids; trans_exported_ids = _63_1037.trans_exported_ids; includes = _63_1037.includes; sigaccum = _63_1037.sigaccum; sigmap = _63_1037.sigmap; default_result_effect = _63_1037.default_result_effect; iface = _63_1037.iface; admitted_iface = _63_1037.admitted_iface; expect_typ = _63_1037.expect_typ}))


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
| Some (se, _63_1058) -> begin
(match ((let _158_954 = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_Util.find_opt (FStar_Ident.lid_equals l) _158_954))) with
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
in (let _158_957 = (let _158_956 = (let _158_955 = (FStar_Util.format2 "Duplicate top-level names [%s]; previously declared at %s" (FStar_Ident.text_of_lid l) r)
in ((_158_955), ((FStar_Ident.range_of_lid l))))
in FStar_Syntax_Syntax.Error (_158_956))
in (Prims.raise _158_957)))))
in (

let globals = (FStar_ST.alloc env.scope_mods)
in (

let env = (

let _63_1077 = (match (s) with
| FStar_Syntax_Syntax.Sig_let (_63_1068) -> begin
((false), (true))
end
| FStar_Syntax_Syntax.Sig_bundle (_63_1071) -> begin
((true), (true))
end
| _63_1074 -> begin
((false), (false))
end)
in (match (_63_1077) with
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

let _63_1081 = (extract_record env globals s)
in (

let _63_1083 = env
in {curmodule = _63_1083.curmodule; curmonad = _63_1083.curmonad; modules = _63_1083.modules; scope_mods = _63_1083.scope_mods; exported_ids = _63_1083.exported_ids; trans_exported_ids = _63_1083.trans_exported_ids; includes = _63_1083.includes; sigaccum = (s)::env.sigaccum; sigmap = _63_1083.sigmap; default_result_effect = _63_1083.default_result_effect; iface = _63_1083.iface; admitted_iface = _63_1083.admitted_iface; expect_typ = _63_1083.expect_typ}))
end
| Some (l) -> begin
(err l)
end))
end))
in (

let env = (

let _63_1088 = env
in (let _158_959 = (FStar_ST.read globals)
in {curmodule = _63_1088.curmodule; curmonad = _63_1088.curmonad; modules = _63_1088.modules; scope_mods = _158_959; exported_ids = _63_1088.exported_ids; trans_exported_ids = _63_1088.trans_exported_ids; includes = _63_1088.includes; sigaccum = _63_1088.sigaccum; sigmap = _63_1088.sigmap; default_result_effect = _63_1088.default_result_effect; iface = _63_1088.iface; admitted_iface = _63_1088.admitted_iface; expect_typ = _63_1088.expect_typ}))
in (

let _63_1105 = (match (s) with
| FStar_Syntax_Syntax.Sig_bundle (ses, _63_1093, _63_1095, _63_1097) -> begin
(let _158_962 = (FStar_List.map (fun se -> (let _158_961 = (FStar_Syntax_Util.lids_of_sigelt se)
in ((_158_961), (se)))) ses)
in ((env), (_158_962)))
end
| _63_1102 -> begin
(let _158_965 = (let _158_964 = (let _158_963 = (FStar_Syntax_Util.lids_of_sigelt s)
in ((_158_963), (s)))
in (_158_964)::[])
in ((env), (_158_965)))
end)
in (match (_63_1105) with
| (env, lss) -> begin
(

let _63_1117 = (FStar_All.pipe_right lss (FStar_List.iter (fun _63_1108 -> (match (_63_1108) with
| (lids, se) -> begin
(FStar_All.pipe_right lids (FStar_List.iter (fun lid -> (

let _63_1110 = (let _158_969 = (let _158_968 = (FStar_ST.read globals)
in (Top_level_def (lid.FStar_Ident.ident))::_158_968)
in (FStar_ST.op_Colon_Equals globals _158_969))
in (match (()) with
| () -> begin
(

let modul = (let _158_970 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in _158_970.FStar_Ident.str)
in (

let _63_1116 = (match ((get_exported_id_set env modul)) with
| Some (f) -> begin
(

let my_exported_ids = (f Exported_id_term_type)
in (let _158_973 = (let _158_972 = (FStar_ST.read my_exported_ids)
in (FStar_Util.set_add lid.FStar_Ident.ident.FStar_Ident.idText _158_972))
in (FStar_ST.op_Colon_Equals my_exported_ids _158_973)))
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

let _63_1119 = env
in (let _158_974 = (FStar_ST.read globals)
in {curmodule = _63_1119.curmodule; curmonad = _63_1119.curmonad; modules = _63_1119.modules; scope_mods = _158_974; exported_ids = _63_1119.exported_ids; trans_exported_ids = _63_1119.trans_exported_ids; includes = _63_1119.includes; sigaccum = _63_1119.sigaccum; sigmap = _63_1119.sigmap; default_result_effect = _63_1119.default_result_effect; iface = _63_1119.iface; admitted_iface = _63_1119.admitted_iface; expect_typ = _63_1119.expect_typ}))
in env))
end)))))))


let push_namespace : env  ->  FStar_Ident.lident  ->  env = (fun env ns -> (

let _63_1134 = (match ((resolve_module_name env ns false)) with
| None -> begin
(

let modules = env.modules
in if (FStar_All.pipe_right modules (FStar_Util.for_some (fun _63_1129 -> (match (_63_1129) with
| (m, _63_1128) -> begin
(FStar_Util.starts_with (Prims.strcat (FStar_Ident.text_of_lid m) ".") (Prims.strcat (FStar_Ident.text_of_lid ns) "."))
end)))) then begin
((ns), (Open_namespace))
end else begin
(let _158_982 = (let _158_981 = (let _158_980 = (FStar_Util.format1 "Namespace %s cannot be found" (FStar_Ident.text_of_lid ns))
in ((_158_980), ((FStar_Ident.range_of_lid ns))))
in FStar_Syntax_Syntax.Error (_158_981))
in (Prims.raise _158_982))
end)
end
| Some (ns') -> begin
((ns'), (Open_module))
end)
in (match (_63_1134) with
| (ns', kd) -> begin
(push_scope_mod env (Open_module_or_namespace (((ns'), (kd)))))
end)))


let push_include : env  ->  FStar_Ident.lident  ->  env = (fun env ns -> (match ((resolve_module_name env ns false)) with
| Some (ns) -> begin
(

let env = (push_scope_mod env (Open_module_or_namespace (((ns), (Open_module)))))
in (

let curmod = (let _158_987 = (current_module env)
in _158_987.FStar_Ident.str)
in (

let _63_1144 = (match ((FStar_Util.smap_try_find env.includes curmod)) with
| None -> begin
()
end
| Some (incl) -> begin
(let _158_989 = (let _158_988 = (FStar_ST.read incl)
in (ns)::_158_988)
in (FStar_ST.op_Colon_Equals incl _158_989))
end)
in (match (()) with
| () -> begin
(match ((get_trans_exported_id_set env ns.FStar_Ident.str)) with
| Some (ns_trans_exports) -> begin
(

let _63_1161 = (match ((let _158_996 = (get_exported_id_set env curmod)
in (let _158_995 = (get_trans_exported_id_set env curmod)
in ((_158_996), (_158_995))))) with
| (Some (cur_exports), Some (cur_trans_exports)) -> begin
(

let update_exports = (fun k -> (

let ns_ex = (let _158_1001 = (ns_trans_exports k)
in (FStar_ST.read _158_1001))
in (

let ex = (cur_exports k)
in (

let _63_1156 = (let _158_1003 = (let _158_1002 = (FStar_ST.read ex)
in (FStar_Util.set_difference _158_1002 ns_ex))
in (FStar_ST.op_Colon_Equals ex _158_1003))
in (match (()) with
| () -> begin
(

let trans_ex = (cur_trans_exports k)
in (

let _63_1158 = (let _158_1005 = (let _158_1004 = (FStar_ST.read ex)
in (FStar_Util.set_union _158_1004 ns_ex))
in (FStar_ST.op_Colon_Equals trans_ex _158_1005))
in ()))
end)))))
in (FStar_List.iter update_exports all_exported_id_kinds))
end
| _63_1160 -> begin
()
end)
in (match (()) with
| () -> begin
env
end))
end
| None -> begin
(let _158_1014 = (let _158_1013 = (let _158_1012 = (FStar_Util.format1 "include: Module %s was not prepared" ns.FStar_Ident.str)
in ((_158_1012), ((FStar_Ident.range_of_lid ns))))
in FStar_Syntax_Syntax.Error (_158_1013))
in (Prims.raise _158_1014))
end)
end))))
end
| _63_1164 -> begin
(let _158_1017 = (let _158_1016 = (let _158_1015 = (FStar_Util.format1 "include: Module %s cannot be found" ns.FStar_Ident.str)
in ((_158_1015), ((FStar_Ident.range_of_lid ns))))
in FStar_Syntax_Syntax.Error (_158_1016))
in (Prims.raise _158_1017))
end))


let push_module_abbrev : env  ->  FStar_Ident.ident  ->  FStar_Ident.lident  ->  env = (fun env x l -> if (module_is_defined env l) then begin
(push_scope_mod env (Module_abbrev (((x), (l)))))
end else begin
(let _158_1026 = (let _158_1025 = (let _158_1024 = (FStar_Util.format1 "Module %s cannot be found" (FStar_Ident.text_of_lid l))
in ((_158_1024), ((FStar_Ident.range_of_lid l))))
in FStar_Syntax_Syntax.Error (_158_1025))
in (Prims.raise _158_1026))
end)


let check_admits : env  ->  Prims.unit = (fun env -> (FStar_All.pipe_right env.sigaccum (FStar_List.iter (fun se -> (match (se) with
| FStar_Syntax_Syntax.Sig_declare_typ (l, u, t, quals, r) -> begin
(match ((try_lookup_lid env l)) with
| None -> begin
(

let _63_1178 = (let _158_1032 = (let _158_1031 = (FStar_Range.string_of_range (FStar_Ident.range_of_lid l))
in (let _158_1030 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format2 "%s: Warning: Admitting %s without a definition\n" _158_1031 _158_1030)))
in (FStar_Util.print_string _158_1032))
in (FStar_Util.smap_add (sigmap env) l.FStar_Ident.str ((FStar_Syntax_Syntax.Sig_declare_typ (((l), (u), (t), ((FStar_Syntax_Syntax.Assumption)::quals), (r)))), (false))))
end
| Some (_63_1181) -> begin
()
end)
end
| _63_1184 -> begin
()
end)))))


let finish : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env modul -> (

let _63_1244 = (FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations (FStar_List.iter (fun _63_30 -> (match (_63_30) with
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _63_1191, _63_1193) -> begin
if ((FStar_List.contains FStar_Syntax_Syntax.Private quals) || (FStar_List.contains FStar_Syntax_Syntax.Abstract quals)) then begin
(FStar_All.pipe_right ses (FStar_List.iter (fun _63_29 -> (match (_63_29) with
| FStar_Syntax_Syntax.Sig_datacon (lid, _63_1199, _63_1201, _63_1203, _63_1205, _63_1207, _63_1209, _63_1211) -> begin
(FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str)
end
| _63_1215 -> begin
()
end))))
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _63_1218, _63_1220, quals, _63_1223) -> begin
if (FStar_List.contains FStar_Syntax_Syntax.Private quals) then begin
(FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str)
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_let ((_63_1227, lbs), r, _63_1232, quals) -> begin
(

let _63_1237 = if ((FStar_List.contains FStar_Syntax_Syntax.Private quals) || (FStar_List.contains FStar_Syntax_Syntax.Abstract quals)) then begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (let _158_1043 = (let _158_1042 = (let _158_1041 = (let _158_1040 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _158_1040.FStar_Syntax_Syntax.fv_name)
in _158_1041.FStar_Syntax_Syntax.v)
in _158_1042.FStar_Ident.str)
in (FStar_Util.smap_remove (sigmap env) _158_1043)))))
end else begin
()
end
in if ((FStar_List.contains FStar_Syntax_Syntax.Abstract quals) && (not ((FStar_List.contains FStar_Syntax_Syntax.Private quals)))) then begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (

let lid = (let _158_1046 = (let _158_1045 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _158_1045.FStar_Syntax_Syntax.fv_name)
in _158_1046.FStar_Syntax_Syntax.v)
in (

let decl = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), ((FStar_Syntax_Syntax.Assumption)::quals), (r)))
in (FStar_Util.smap_add (sigmap env) lid.FStar_Ident.str ((decl), (false))))))))
end else begin
()
end)
end
| _63_1243 -> begin
()
end))))
in (

let curmod = (let _158_1047 = (current_module env)
in _158_1047.FStar_Ident.str)
in (

let _63_1258 = (match ((let _158_1053 = (get_exported_id_set env curmod)
in (let _158_1052 = (get_trans_exported_id_set env curmod)
in ((_158_1053), (_158_1052))))) with
| (Some (cur_ex), Some (cur_trans_ex)) -> begin
(

let update_exports = (fun eikind -> (

let cur_ex_set = (let _158_1058 = (cur_ex eikind)
in (FStar_ST.read _158_1058))
in (

let cur_trans_ex_set_ref = (cur_trans_ex eikind)
in (let _158_1060 = (let _158_1059 = (FStar_ST.read cur_trans_ex_set_ref)
in (FStar_Util.set_union cur_ex_set _158_1059))
in (FStar_ST.op_Colon_Equals cur_trans_ex_set_ref _158_1060)))))
in (FStar_List.iter update_exports all_exported_id_kinds))
end
| _63_1257 -> begin
()
end)
in (match (()) with
| () -> begin
(

let _63_1259 = (filter_record_cache ())
in (match (()) with
| () -> begin
(

let _63_1260 = env
in {curmodule = None; curmonad = _63_1260.curmonad; modules = (((modul.FStar_Syntax_Syntax.name), (modul)))::env.modules; scope_mods = []; exported_ids = _63_1260.exported_ids; trans_exported_ids = _63_1260.trans_exported_ids; includes = _63_1260.includes; sigaccum = []; sigmap = _63_1260.sigmap; default_result_effect = _63_1260.default_result_effect; iface = _63_1260.iface; admitted_iface = _63_1260.admitted_iface; expect_typ = _63_1260.expect_typ})
end))
end)))))


type env_stack_ops =
{push : env  ->  env; mark : env  ->  env; reset_mark : env  ->  env; commit_mark : env  ->  env; pop : env  ->  env}


let is_Mkenv_stack_ops : env_stack_ops  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv_stack_ops"))))


let stack_ops : env_stack_ops = (

let stack = (FStar_Util.mk_ref [])
in (

let push = (fun env -> (

let _63_1271 = (push_record_cache ())
in (

let _63_1273 = (let _158_1116 = (let _158_1115 = (FStar_ST.read stack)
in (env)::_158_1115)
in (FStar_ST.op_Colon_Equals stack _158_1116))
in (

let _63_1275 = env
in (let _158_1117 = (FStar_Util.smap_copy (sigmap env))
in {curmodule = _63_1275.curmodule; curmonad = _63_1275.curmonad; modules = _63_1275.modules; scope_mods = _63_1275.scope_mods; exported_ids = _63_1275.exported_ids; trans_exported_ids = _63_1275.trans_exported_ids; includes = _63_1275.includes; sigaccum = _63_1275.sigaccum; sigmap = _158_1117; default_result_effect = _63_1275.default_result_effect; iface = _63_1275.iface; admitted_iface = _63_1275.admitted_iface; expect_typ = _63_1275.expect_typ})))))
in (

let pop = (fun env -> (match ((FStar_ST.read stack)) with
| (env)::tl -> begin
(

let _63_1282 = (pop_record_cache ())
in (

let _63_1284 = (FStar_ST.op_Colon_Equals stack tl)
in env))
end
| _63_1287 -> begin
(FStar_All.failwith "Impossible: Too many pops")
end))
in (

let commit_mark = (fun env -> (

let _63_1290 = (commit_record_cache ())
in (match ((FStar_ST.read stack)) with
| (_63_1294)::tl -> begin
(

let _63_1296 = (FStar_ST.op_Colon_Equals stack tl)
in env)
end
| _63_1299 -> begin
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
| (l)::_63_1310 -> begin
(l.FStar_Ident.nsstr = m.FStar_Ident.str)
end
| _63_1314 -> begin
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

let _63_1338 = (FStar_All.pipe_right keys (FStar_List.iter (fun k -> (match ((FStar_Util.smap_try_find sm' k)) with
| Some (se, true) when (sigelt_in_m se) -> begin
(

let _63_1324 = (FStar_Util.smap_remove sm' k)
in (

let se = (match (se) with
| FStar_Syntax_Syntax.Sig_declare_typ (l, u, t, q, r) -> begin
FStar_Syntax_Syntax.Sig_declare_typ (((l), (u), (t), ((FStar_Syntax_Syntax.Assumption)::q), (r)))
end
| _63_1334 -> begin
se
end)
in (FStar_Util.smap_add sm' k ((se), (false)))))
end
| _63_1337 -> begin
()
end))))
in env)))))))


let finish_module_or_interface : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env modul -> (

let _63_1342 = if (not (modul.FStar_Syntax_Syntax.is_interface)) then begin
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

let _63_1353 = (let _158_1153 = (exported_id_set_new ())
in (FStar_Util.smap_add env.exported_ids mname.FStar_Ident.str _158_1153))
in (match (()) with
| () -> begin
(

let _63_1354 = (let _158_1154 = (exported_id_set_new ())
in (FStar_Util.smap_add env.trans_exported_ids mname.FStar_Ident.str _158_1154))
in (match (()) with
| () -> begin
(

let _63_1355 = (let _158_1155 = (FStar_Util.mk_ref [])
in (FStar_Util.smap_add env.includes mname.FStar_Ident.str _158_1155))
in (match (()) with
| () -> begin
(

let _63_1356 = env
in (let _158_1157 = (FStar_List.map (fun lid -> Open_module_or_namespace (((lid), (Open_namespace)))) open_ns)
in {curmodule = Some (mname); curmonad = _63_1356.curmonad; modules = _63_1356.modules; scope_mods = _158_1157; exported_ids = _63_1356.exported_ids; trans_exported_ids = _63_1356.trans_exported_ids; includes = _63_1356.includes; sigaccum = _63_1356.sigaccum; sigmap = env.sigmap; default_result_effect = if ((FStar_Ident.lid_equals mname FStar_Syntax_Const.all_lid) || (has_all_in_scope env)) then begin
FStar_Syntax_Const.effect_ML_lid
end else begin
FStar_Syntax_Const.effect_Tot_lid
end; iface = intf; admitted_iface = admitted; expect_typ = _63_1356.expect_typ}))
end))
end))
end)))))
in (match ((FStar_All.pipe_right env.modules (FStar_Util.find_opt (fun _63_1362 -> (match (_63_1362) with
| (l, _63_1361) -> begin
(FStar_Ident.lid_equals l mname)
end))))) with
| None -> begin
(let _158_1159 = (prep env)
in ((_158_1159), (false)))
end
| Some (_63_1365, m) -> begin
(

let _63_1369 = if ((not (m.FStar_Syntax_Syntax.is_interface)) || intf) then begin
(let _158_1162 = (let _158_1161 = (let _158_1160 = (FStar_Util.format1 "Duplicate module or interface name: %s" mname.FStar_Ident.str)
in ((_158_1160), ((FStar_Ident.range_of_lid mname))))
in FStar_Syntax_Syntax.Error (_158_1161))
in (Prims.raise _158_1162))
end else begin
()
end
in (let _158_1164 = (let _158_1163 = (push env)
in (prep _158_1163))
in ((_158_1164), (true))))
end)))


let enter_monad_scope : env  ->  FStar_Ident.ident  ->  env = (fun env mname -> (match (env.curmonad) with
| Some (mname') -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((((Prims.strcat "Trying to define monad " (Prims.strcat mname.FStar_Ident.idText (Prims.strcat ", but already in monad scope " mname'.FStar_Ident.idText)))), (mname.FStar_Ident.idRange)))))
end
| None -> begin
(

let _63_1376 = env
in {curmodule = _63_1376.curmodule; curmonad = Some (mname); modules = _63_1376.modules; scope_mods = _63_1376.scope_mods; exported_ids = _63_1376.exported_ids; trans_exported_ids = _63_1376.trans_exported_ids; includes = _63_1376.includes; sigaccum = _63_1376.sigaccum; sigmap = _63_1376.sigmap; default_result_effect = _63_1376.default_result_effect; iface = _63_1376.iface; admitted_iface = _63_1376.admitted_iface; expect_typ = _63_1376.expect_typ})
end))


let fail_or = (fun env lookup lid -> (match ((lookup lid)) with
| None -> begin
(

let opened_modules = (FStar_List.map (fun _63_1385 -> (match (_63_1385) with
| (lid, _63_1384) -> begin
(FStar_Ident.text_of_lid lid)
end)) env.modules)
in (

let msg = (FStar_Util.format1 "Identifier not found: [%s]" (FStar_Ident.text_of_lid lid))
in (

let msg = if ((FStar_List.length lid.FStar_Ident.ns) = (Prims.parse_int "0")) then begin
msg
end else begin
(

let modul = (let _158_1176 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in (FStar_Ident.set_lid_range _158_1176 (FStar_Ident.range_of_lid lid)))
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




