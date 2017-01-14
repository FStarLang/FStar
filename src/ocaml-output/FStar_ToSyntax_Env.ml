
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


let is_Mkrecord_or_dc : record_or_dc  ->  Prims.bool = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mkrecord_or_dc"))))


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
| Local_binding (_73_10) -> begin
_73_10
end))


let ___Rec_binding____0 = (fun projectee -> (match (projectee) with
| Rec_binding (_73_13) -> begin
_73_13
end))


let ___Module_abbrev____0 = (fun projectee -> (match (projectee) with
| Module_abbrev (_73_16) -> begin
_73_16
end))


let ___Open_module_or_namespace____0 = (fun projectee -> (match (projectee) with
| Open_module_or_namespace (_73_19) -> begin
_73_19
end))


let ___Top_level_def____0 = (fun projectee -> (match (projectee) with
| Top_level_def (_73_22) -> begin
_73_22
end))


let ___Record_or_dc____0 = (fun projectee -> (match (projectee) with
| Record_or_dc (_73_25) -> begin
_73_25
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


let is_Mkenv : env  ->  Prims.bool = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mkenv"))))


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
| Term_name (_73_42) -> begin
_73_42
end))


let ___Eff_name____0 = (fun projectee -> (match (projectee) with
| Eff_name (_73_45) -> begin
_73_45
end))


let all_exported_id_kinds : exported_id_kind Prims.list = (Exported_id_field)::(Exported_id_term_type)::[]


let open_modules : env  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.modul) Prims.list = (fun e -> e.modules)


let current_module : env  ->  FStar_Ident.lident = (fun env -> (match (env.curmodule) with
| None -> begin
(failwith "Unset current module")
end
| Some (m) -> begin
m
end))


let qual : FStar_Ident.lident  ->  FStar_Ident.ident  ->  FStar_Ident.lident = FStar_Syntax_Util.qual_id


let qualify : env  ->  FStar_Ident.ident  ->  FStar_Ident.lident = (fun env id -> (match (env.curmonad) with
| None -> begin
(let _174_188 = (current_module env)
in (qual _174_188 id))
end
| Some (monad) -> begin
(let _174_190 = (let _174_189 = (current_module env)
in (qual _174_189 monad))
in (FStar_Syntax_Util.mk_field_projector_name_from_ident _174_190 id))
end))


let new_sigmap = (fun _73_58 -> (match (()) with
| () -> begin
(FStar_Util.smap_create (Prims.parse_int "100"))
end))


let empty_env : Prims.unit  ->  env = (fun _73_59 -> (match (()) with
| () -> begin
(let _174_197 = (new_sigmap ())
in (let _174_196 = (new_sigmap ())
in (let _174_195 = (new_sigmap ())
in (let _174_194 = (new_sigmap ())
in {curmodule = None; curmonad = None; modules = []; scope_mods = []; exported_ids = _174_197; trans_exported_ids = _174_196; includes = _174_195; sigaccum = []; sigmap = _174_194; default_result_effect = FStar_Syntax_Const.effect_Tot_lid; iface = false; admitted_iface = false; expect_typ = false}))))
end))


let sigmap : env  ->  (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap = (fun env -> env.sigmap)


let has_all_in_scope : env  ->  Prims.bool = (fun env -> (FStar_List.existsb (fun _73_65 -> (match (_73_65) with
| (m, _73_64) -> begin
(FStar_Ident.lid_equals m FStar_Syntax_Const.all_lid)
end)) env.modules))


let default_total : env  ->  env = (fun env -> (

let _73_67 = env
in {curmodule = _73_67.curmodule; curmonad = _73_67.curmonad; modules = _73_67.modules; scope_mods = _73_67.scope_mods; exported_ids = _73_67.exported_ids; trans_exported_ids = _73_67.trans_exported_ids; includes = _73_67.includes; sigaccum = _73_67.sigaccum; sigmap = _73_67.sigmap; default_result_effect = FStar_Syntax_Const.effect_Tot_lid; iface = _73_67.iface; admitted_iface = _73_67.admitted_iface; expect_typ = _73_67.expect_typ}))


let default_ml : env  ->  env = (fun env -> if (has_all_in_scope env) then begin
(

let _73_70 = env
in {curmodule = _73_70.curmodule; curmonad = _73_70.curmonad; modules = _73_70.modules; scope_mods = _73_70.scope_mods; exported_ids = _73_70.exported_ids; trans_exported_ids = _73_70.trans_exported_ids; includes = _73_70.includes; sigaccum = _73_70.sigaccum; sigmap = _73_70.sigmap; default_result_effect = FStar_Syntax_Const.effect_ML_lid; iface = _73_70.iface; admitted_iface = _73_70.admitted_iface; expect_typ = _73_70.expect_typ})
end else begin
env
end)


let set_bv_range : FStar_Syntax_Syntax.bv  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.bv = (fun bv r -> (

let id = (

let _73_74 = bv.FStar_Syntax_Syntax.ppname
in {FStar_Ident.idText = _73_74.FStar_Ident.idText; FStar_Ident.idRange = r})
in (

let _73_77 = bv
in {FStar_Syntax_Syntax.ppname = id; FStar_Syntax_Syntax.index = _73_77.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _73_77.FStar_Syntax_Syntax.sort})))


let bv_to_name : FStar_Syntax_Syntax.bv  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.term = (fun bv r -> (FStar_Syntax_Syntax.bv_to_name (set_bv_range bv r)))


let unmangleMap : (Prims.string * Prims.string * FStar_Syntax_Syntax.delta_depth * FStar_Syntax_Syntax.fv_qual Prims.option) Prims.list = ((("op_ColonColon"), ("Cons"), (FStar_Syntax_Syntax.Delta_constant), (Some (FStar_Syntax_Syntax.Data_ctor))))::((("not"), ("op_Negation"), (FStar_Syntax_Syntax.Delta_equational), (None)))::[]


let unmangleOpName : FStar_Ident.ident  ->  (FStar_Syntax_Syntax.term * Prims.bool) Prims.option = (fun id -> (

let t = (FStar_Util.find_map unmangleMap (fun _73_86 -> (match (_73_86) with
| (x, y, dd, dq) -> begin
if (id.FStar_Ident.idText = x) then begin
(let _174_219 = (let _174_218 = (FStar_Ident.lid_of_path (("Prims")::(y)::[]) id.FStar_Ident.idRange)
in (FStar_Syntax_Syntax.fvar _174_218 dd dq))
in Some (_174_219))
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
| Cont_ok (_73_94) -> begin
_73_94
end))


let option_of_cont = (fun k_ignore uu___439 -> (match (uu___439) with
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

let find = (FStar_Util.find_map record.fields (fun _73_111 -> (match (_73_111) with
| (f, _73_110) -> begin
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


let string_of_exported_id_kind : exported_id_kind  ->  Prims.string = (fun uu___440 -> (match (uu___440) with
| Exported_id_field -> begin
"field"
end
| Exported_id_term_type -> begin
"term/type"
end))


let find_in_module_with_includes = (fun eikind find_in_module find_in_module_default env ns id -> (

let idstr = id.FStar_Ident.idText
in (

let rec aux = (fun uu___441 -> (match (uu___441) with
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

let mexports = (let _174_289 = (mex eikind)
in (FStar_ST.read _174_289))
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
(let _174_290 = (qual modul id)
in (find_in_module _174_290))
end else begin
Cont_ignore
end
in (match (look_into) with
| Cont_ignore -> begin
(aux (FStar_List.append mincludes q))
end
| _73_150 -> begin
look_into
end)))))
end))
in (aux ((ns)::[])))))


let is_exported_id_field : exported_id_kind  ->  Prims.bool = (fun uu___442 -> (match (uu___442) with
| Exported_id_field -> begin
true
end
| _73_154 -> begin
false
end))


let try_lookup_id'' = (fun env id eikind k_local_binding k_rec_binding k_record find_in_module lookup_default_id -> (

let check_local_binding_id = (fun uu___443 -> (match (uu___443) with
| (id', _73_167, _73_169) -> begin
(id'.FStar_Ident.idText = id.FStar_Ident.idText)
end))
in (

let check_rec_binding_id = (fun uu___444 -> (match (uu___444) with
| (id', _73_175, _73_177) -> begin
(id'.FStar_Ident.idText = id.FStar_Ident.idText)
end))
in (

let curmod_ns = (let _174_323 = (current_module env)
in (FStar_Ident.ids_of_lid _174_323))
in (

let proc = (fun uu___445 -> (match (uu___445) with
| Local_binding (l) when (check_local_binding_id l) -> begin
(k_local_binding l)
end
| Rec_binding (r) when (check_rec_binding_id r) -> begin
(k_rec_binding r)
end
| Open_module_or_namespace (ns, _73_188) -> begin
(find_in_module_with_includes eikind find_in_module Cont_ignore env ns id)
end
| Top_level_def (id') when (id'.FStar_Ident.idText = id.FStar_Ident.idText) -> begin
(lookup_default_id Cont_ignore id)
end
| Record_or_dc (r) when (is_exported_id_field eikind) -> begin
(let _174_327 = (FStar_Ident.lid_of_ids curmod_ns)
in (find_in_module_with_includes Exported_id_field (fun lid -> (

let id = lid.FStar_Ident.ident
in (find_in_record lid.FStar_Ident.ns id r k_record))) Cont_ignore env _174_327 id))
end
| _73_198 -> begin
Cont_ignore
end))
in (

let rec aux = (fun uu___446 -> (match (uu___446) with
| (a)::q -> begin
(let _174_331 = (proc a)
in (option_of_cont (fun _73_205 -> (aux q)) _174_331))
end
| [] -> begin
(let _174_333 = (lookup_default_id Cont_fail id)
in (option_of_cont (fun _73_208 -> None) _174_333))
end))
in (aux env.scope_mods)))))))


let found_local_binding = (fun r _73_214 -> (match (_73_214) with
| (id', x, mut) -> begin
(let _174_336 = (bv_to_name x r)
in ((_174_336), (mut)))
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
| _73_227 -> begin
(try_lookup_id'' env id Exported_id_term_type (fun r -> (let _174_352 = (found_local_binding id.FStar_Ident.idRange r)
in Cont_ok (_174_352))) (fun _73_239 -> Cont_fail) (fun _73_237 -> Cont_ignore) (fun i -> (find_in_module env i (fun _73_233 _73_235 -> Cont_fail) Cont_ignore)) (fun _73_228 _73_230 -> Cont_fail))
end))


let lookup_default_id = (fun env id k_global_def k_not_found -> (

let find_in_monad = (match (env.curmonad) with
| Some (_73_248) -> begin
(

let lid = (qualify env id)
in (match ((FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str)) with
| Some (r) -> begin
(let _174_370 = (k_global_def lid r)
in Some (_174_370))
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

let lid = (let _174_371 = (current_module env)
in (qual _174_371 id))
in (find_in_module env lid k_global_def k_not_found))
end)))


let module_is_defined : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> ((let _174_376 = (current_module env)
in (FStar_Ident.lid_equals lid _174_376)) || (FStar_List.existsb (fun x -> (FStar_Ident.lid_equals lid (Prims.fst x))) env.modules)))


let resolve_module_name : env  ->  FStar_Ident.lident  ->  Prims.bool  ->  FStar_Ident.lident Prims.option = (fun env lid honor_ns -> (

let nslen = (FStar_List.length lid.FStar_Ident.ns)
in (

let rec aux = (fun uu___447 -> (match (uu___447) with
| [] -> begin
if (module_is_defined env lid) then begin
Some (lid)
end else begin
None
end
end
| (Open_module_or_namespace (ns, Open_namespace))::q when honor_ns -> begin
(

let new_lid = (let _174_388 = (let _174_387 = (FStar_Ident.path_of_lid ns)
in (let _174_386 = (FStar_Ident.path_of_lid lid)
in (FStar_List.append _174_387 _174_386)))
in (FStar_Ident.lid_of_path _174_388 (FStar_Ident.range_of_lid lid)))
in if (module_is_defined env new_lid) then begin
Some (new_lid)
end else begin
(aux q)
end)
end
| (Module_abbrev (name, modul))::_73_278 when ((nslen = (Prims.parse_int "0")) && (name.FStar_Ident.idText = lid.FStar_Ident.ident.FStar_Ident.idText)) -> begin
Some (modul)
end
| (_73_286)::q -> begin
(aux q)
end))
in (aux env.scope_mods))))


let resolve_in_open_namespaces'' = (fun env lid eikind k_local_binding k_rec_binding k_record f_module l_default -> (match (lid.FStar_Ident.ns) with
| (_73_300)::_73_298 -> begin
(match ((let _174_416 = (let _174_415 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in (FStar_Ident.set_lid_range _174_415 (FStar_Ident.range_of_lid lid)))
in (resolve_module_name env _174_416 true))) with
| None -> begin
None
end
| Some (modul) -> begin
(let _174_418 = (find_in_module_with_includes eikind f_module Cont_fail env modul lid.FStar_Ident.ident)
in (option_of_cont (fun _73_305 -> None) _174_418))
end)
end
| [] -> begin
(try_lookup_id'' env lid.FStar_Ident.ident eikind k_local_binding k_rec_binding k_record f_module l_default)
end))


let cont_of_option = (fun k_none uu___448 -> (match (uu___448) with
| Some (v) -> begin
Cont_ok (v)
end
| None -> begin
k_none
end))


let resolve_in_open_namespaces' = (fun env lid k_local_binding k_rec_binding k_global_def -> (

let k_global_def' = (fun k lid def -> (let _174_444 = (k_global_def lid def)
in (cont_of_option k _174_444)))
in (

let f_module = (fun lid' -> (

let k = Cont_ignore
in (find_in_module env lid' (k_global_def' k) k)))
in (

let l_default = (fun k i -> (lookup_default_id env i (k_global_def' k) k))
in (resolve_in_open_namespaces'' env lid Exported_id_term_type (fun l -> (let _174_452 = (k_local_binding l)
in (cont_of_option Cont_fail _174_452))) (fun r -> (let _174_454 = (k_rec_binding r)
in (cont_of_option Cont_fail _174_454))) (fun _73_330 -> Cont_ignore) f_module l_default)))))


let fv_qual_of_se : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.fv_qual Prims.option = (fun uu___450 -> (match (uu___450) with
| FStar_Syntax_Syntax.Sig_datacon (_73_336, _73_338, _73_340, l, _73_343, quals, _73_346, _73_348) -> begin
(

let qopt = (FStar_Util.find_map quals (fun uu___449 -> (match (uu___449) with
| FStar_Syntax_Syntax.RecordConstructor (_73_353, fs) -> begin
Some (FStar_Syntax_Syntax.Record_ctor (((l), (fs))))
end
| _73_358 -> begin
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
| FStar_Syntax_Syntax.Sig_declare_typ (_73_363, _73_365, _73_367, quals, _73_370) -> begin
None
end
| _73_374 -> begin
None
end))


let lb_fv : FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.fv = (fun lbs lid -> (let _174_464 = (FStar_Util.find_map lbs (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in if (FStar_Syntax_Syntax.fv_eq_lid fv lid) then begin
Some (fv)
end else begin
None
end)))
in (FStar_All.pipe_right _174_464 FStar_Util.must)))


let ns_of_lid_equals : FStar_Ident.lident  ->  FStar_Ident.lident  ->  Prims.bool = (fun lid ns -> (((FStar_List.length lid.FStar_Ident.ns) = (FStar_List.length (FStar_Ident.ids_of_lid ns))) && (let _174_469 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in (FStar_Ident.lid_equals _174_469 ns))))


let try_lookup_name : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  foundname Prims.option = (fun any_val exclude_interf env lid -> (

let occurrence_range = (FStar_Ident.range_of_lid lid)
in (

let k_global_def = (fun source_lid uu___454 -> (match (uu___454) with
| (_73_390, true) when exclude_interf -> begin
None
end
| (se, _73_395) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_73_398) -> begin
(let _174_484 = (let _174_483 = (let _174_482 = (FStar_Syntax_Syntax.fvar source_lid FStar_Syntax_Syntax.Delta_constant None)
in ((_174_482), (false)))
in Term_name (_174_483))
in Some (_174_484))
end
| FStar_Syntax_Syntax.Sig_datacon (_73_401) -> begin
(let _174_488 = (let _174_487 = (let _174_486 = (let _174_485 = (fv_qual_of_se se)
in (FStar_Syntax_Syntax.fvar source_lid FStar_Syntax_Syntax.Delta_constant _174_485))
in ((_174_486), (false)))
in Term_name (_174_487))
in Some (_174_488))
end
| FStar_Syntax_Syntax.Sig_let ((_73_404, lbs), _73_408, _73_410, _73_412, _73_414) -> begin
(

let fv = (lb_fv lbs source_lid)
in (let _174_491 = (let _174_490 = (let _174_489 = (FStar_Syntax_Syntax.fvar source_lid fv.FStar_Syntax_Syntax.fv_delta fv.FStar_Syntax_Syntax.fv_qual)
in ((_174_489), (false)))
in Term_name (_174_490))
in Some (_174_491)))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _73_420, _73_422, quals, _73_425) -> begin
if (any_val || (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___451 -> (match (uu___451) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| _73_431 -> begin
false
end))))) then begin
(

let lid = (FStar_Ident.set_lid_range lid (FStar_Ident.range_of_lid source_lid))
in (

let dd = if ((FStar_Syntax_Util.is_primop_lid lid) || ((ns_of_lid_equals lid FStar_Syntax_Const.prims_lid) && (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___452 -> (match (uu___452) with
| (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) -> begin
true
end
| _73_441 -> begin
false
end)))))) then begin
FStar_Syntax_Syntax.Delta_equational
end else begin
FStar_Syntax_Syntax.Delta_constant
end
in (match ((FStar_Util.find_map quals (fun uu___453 -> (match (uu___453) with
| FStar_Syntax_Syntax.Reflectable (refl_monad) -> begin
Some (refl_monad)
end
| _73_447 -> begin
None
end)))) with
| Some (refl_monad) -> begin
(

let refl_const = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (refl_monad))) None occurrence_range)
in Some (Term_name (((refl_const), (false)))))
end
| _73_452 -> begin
(let _174_498 = (let _174_497 = (let _174_496 = (let _174_495 = (fv_qual_of_se se)
in (FStar_Syntax_Syntax.fvar lid dd _174_495))
in ((_174_496), (false)))
in Term_name (_174_497))
in Some (_174_498))
end)))
end else begin
None
end
end
| (FStar_Syntax_Syntax.Sig_new_effect_for_free (ne, _)) | (FStar_Syntax_Syntax.Sig_new_effect (ne, _)) -> begin
Some (Eff_name (((se), ((FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname (FStar_Ident.range_of_lid source_lid))))))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (_73_463) -> begin
Some (Eff_name (((se), (source_lid))))
end
| _73_466 -> begin
None
end)
end))
in (

let k_local_binding = (fun r -> (let _174_502 = (let _174_501 = (found_local_binding (FStar_Ident.range_of_lid lid) r)
in Term_name (_174_501))
in Some (_174_502)))
in (

let k_rec_binding = (fun _73_473 -> (match (_73_473) with
| (id, l, dd) -> begin
(let _174_507 = (let _174_506 = (let _174_505 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range l (FStar_Ident.range_of_lid lid)) dd None)
in ((_174_505), (false)))
in Term_name (_174_506))
in Some (_174_507))
end))
in (

let found_unmangled = (match (lid.FStar_Ident.ns) with
| [] -> begin
(match ((unmangleOpName lid.FStar_Ident.ident)) with
| Some (f) -> begin
Some (Term_name (f))
end
| _73_478 -> begin
None
end)
end
| _73_480 -> begin
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
| _73_493 -> begin
None
end))


let try_lookup_effect_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env l -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some (o, l) -> begin
Some (l)
end
| _73_501 -> begin
None
end))


let try_lookup_effect_name_and_attributes : env  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.cflags Prims.list) Prims.option = (fun env l -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some (FStar_Syntax_Syntax.Sig_new_effect (ne, _73_506), l) -> begin
Some (((l), (ne.FStar_Syntax_Syntax.cattributes)))
end
| Some (FStar_Syntax_Syntax.Sig_new_effect_for_free (ne, _73_514), l) -> begin
Some (((l), (ne.FStar_Syntax_Syntax.cattributes)))
end
| Some (FStar_Syntax_Syntax.Sig_effect_abbrev (_73_521, _73_523, _73_525, _73_527, _73_529, cattributes, _73_532), l) -> begin
Some (((l), (cattributes)))
end
| _73_539 -> begin
None
end))


let try_lookup_effect_defn : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl Prims.option = (fun env l -> (match ((try_lookup_effect_name' (not (env.iface)) env l)) with
| Some (FStar_Syntax_Syntax.Sig_new_effect (ne, _73_544), _73_548) -> begin
Some (ne)
end
| Some (FStar_Syntax_Syntax.Sig_new_effect_for_free (ne, _73_553), _73_557) -> begin
Some (ne)
end
| _73_561 -> begin
None
end))


let is_effect_name : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((try_lookup_effect_name env lid)) with
| None -> begin
false
end
| Some (_73_566) -> begin
true
end))


let lookup_letbinding_quals : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.qualifier Prims.list = (fun env lid -> (

let k_global_def = (fun lid uu___455 -> (match (uu___455) with
| (FStar_Syntax_Syntax.Sig_declare_typ (lid, _73_575, _73_577, quals, _73_580), _73_584) -> begin
Some (quals)
end
| _73_587 -> begin
None
end))
in (match ((resolve_in_open_namespaces' env lid (fun _73_590 -> None) (fun _73_588 -> None) k_global_def)) with
| Some (quals) -> begin
quals
end
| _73_595 -> begin
[]
end)))


let try_lookup_module : env  ->  Prims.string Prims.list  ->  FStar_Syntax_Syntax.modul Prims.option = (fun env path -> (match ((FStar_List.tryFind (fun _73_600 -> (match (_73_600) with
| (mlid, modul) -> begin
((FStar_Ident.path_of_lid mlid) = path)
end)) env.modules)) with
| Some (_73_602, modul) -> begin
Some (modul)
end
| None -> begin
None
end))


let try_lookup_let : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env lid -> (

let k_global_def = (fun lid uu___456 -> (match (uu___456) with
| (FStar_Syntax_Syntax.Sig_let ((_73_613, lbs), _73_617, _73_619, _73_621, _73_623), _73_627) -> begin
(

let fv = (lb_fv lbs lid)
in (let _174_553 = (FStar_Syntax_Syntax.fvar lid fv.FStar_Syntax_Syntax.fv_delta fv.FStar_Syntax_Syntax.fv_qual)
in Some (_174_553)))
end
| _73_631 -> begin
None
end))
in (resolve_in_open_namespaces' env lid (fun _73_634 -> None) (fun _73_632 -> None) k_global_def)))


let try_lookup_definition : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env lid -> (

let k_global_def = (fun lid uu___457 -> (match (uu___457) with
| (FStar_Syntax_Syntax.Sig_let (lbs, _73_643, _73_645, _73_647, _73_649), _73_653) -> begin
(FStar_Util.find_map (Prims.snd lbs) (fun lb -> (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv lid) -> begin
Some (lb.FStar_Syntax_Syntax.lbdef)
end
| _73_659 -> begin
None
end)))
end
| _73_661 -> begin
None
end))
in (resolve_in_open_namespaces' env lid (fun _73_664 -> None) (fun _73_662 -> None) k_global_def)))


let try_lookup_lid' : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term * Prims.bool) Prims.option = (fun any_val exclude_interf env lid -> (match ((try_lookup_name any_val exclude_interf env lid)) with
| Some (Term_name (e, mut)) -> begin
Some (((e), (mut)))
end
| _73_676 -> begin
None
end))


let try_lookup_lid : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term * Prims.bool) Prims.option = (fun env l -> (try_lookup_lid' env.iface false env l))


let try_lookup_datacon : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.fv Prims.option = (fun env lid -> (

let k_global_def = (fun lid uu___459 -> (match (uu___459) with
| (FStar_Syntax_Syntax.Sig_declare_typ (_73_685, _73_687, _73_689, quals, _73_692), _73_696) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___458 -> (match (uu___458) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| _73_701 -> begin
false
end)))) then begin
(let _174_588 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant None)
in Some (_174_588))
end else begin
None
end
end
| (FStar_Syntax_Syntax.Sig_datacon (_73_703), _73_706) -> begin
(let _174_589 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in Some (_174_589))
end
| _73_709 -> begin
None
end))
in (resolve_in_open_namespaces' env lid (fun _73_712 -> None) (fun _73_710 -> None) k_global_def)))


let find_all_datacons : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.list Prims.option = (fun env lid -> (

let k_global_def = (fun lid uu___460 -> (match (uu___460) with
| (FStar_Syntax_Syntax.Sig_inductive_typ (_73_720, _73_722, _73_724, _73_726, _73_728, datas, _73_731, _73_733), _73_737) -> begin
Some (datas)
end
| _73_740 -> begin
None
end))
in (resolve_in_open_namespaces' env lid (fun _73_743 -> None) (fun _73_741 -> None) k_global_def)))


let record_cache_aux_with_filter : (((Prims.unit  ->  Prims.unit) * (Prims.unit  ->  Prims.unit) * (Prims.unit  ->  record_or_dc Prims.list) * (record_or_dc  ->  Prims.unit) * (Prims.unit  ->  Prims.unit)) * (Prims.unit  ->  Prims.unit)) = (

let record_cache = (FStar_Util.mk_ref (([])::[]))
in (

let push = (fun _73_747 -> (match (()) with
| () -> begin
(let _174_624 = (let _174_623 = (let _174_621 = (FStar_ST.read record_cache)
in (FStar_List.hd _174_621))
in (let _174_622 = (FStar_ST.read record_cache)
in (_174_623)::_174_622))
in (FStar_ST.op_Colon_Equals record_cache _174_624))
end))
in (

let pop = (fun _73_749 -> (match (()) with
| () -> begin
(let _174_628 = (let _174_627 = (FStar_ST.read record_cache)
in (FStar_List.tl _174_627))
in (FStar_ST.op_Colon_Equals record_cache _174_628))
end))
in (

let peek = (fun _73_751 -> (match (()) with
| () -> begin
(let _174_631 = (FStar_ST.read record_cache)
in (FStar_List.hd _174_631))
end))
in (

let insert = (fun r -> (let _174_638 = (let _174_637 = (let _174_634 = (peek ())
in (r)::_174_634)
in (let _174_636 = (let _174_635 = (FStar_ST.read record_cache)
in (FStar_List.tl _174_635))
in (_174_637)::_174_636))
in (FStar_ST.op_Colon_Equals record_cache _174_638)))
in (

let commit = (fun _73_755 -> (match (()) with
| () -> begin
(match ((FStar_ST.read record_cache)) with
| (hd)::(_73_758)::tl -> begin
(FStar_ST.op_Colon_Equals record_cache ((hd)::tl))
end
| _73_763 -> begin
(failwith "Impossible")
end)
end))
in (

let filter = (fun _73_765 -> (match (()) with
| () -> begin
(

let rc = (peek ())
in (

let _73_767 = (pop ())
in (match (()) with
| () -> begin
(

let filtered = (FStar_List.filter (fun r -> (not (r.is_private_or_abstract))) rc)
in (let _174_645 = (let _174_644 = (FStar_ST.read record_cache)
in (filtered)::_174_644)
in (FStar_ST.op_Colon_Equals record_cache _174_645)))
end)))
end))
in (

let aux = ((push), (pop), (peek), (insert), (commit))
in ((aux), (filter))))))))))


let record_cache_aux : ((Prims.unit  ->  Prims.unit) * (Prims.unit  ->  Prims.unit) * (Prims.unit  ->  record_or_dc Prims.list) * (record_or_dc  ->  Prims.unit) * (Prims.unit  ->  Prims.unit)) = (

let _73_774 = record_cache_aux_with_filter
in (match (_73_774) with
| (aux, _73_773) -> begin
aux
end))


let filter_record_cache : Prims.unit  ->  Prims.unit = (

let _73_778 = record_cache_aux_with_filter
in (match (_73_778) with
| (_73_776, filter) -> begin
filter
end))


let push_record_cache : Prims.unit  ->  Prims.unit = (

let _73_788 = record_cache_aux
in (match (_73_788) with
| (push, _73_781, _73_783, _73_785, _73_787) -> begin
push
end))


let pop_record_cache : Prims.unit  ->  Prims.unit = (

let _73_798 = record_cache_aux
in (match (_73_798) with
| (_73_790, pop, _73_793, _73_795, _73_797) -> begin
pop
end))


let peek_record_cache : Prims.unit  ->  record_or_dc Prims.list = (

let _73_808 = record_cache_aux
in (match (_73_808) with
| (_73_800, _73_802, peek, _73_805, _73_807) -> begin
peek
end))


let insert_record_cache : record_or_dc  ->  Prims.unit = (

let _73_818 = record_cache_aux
in (match (_73_818) with
| (_73_810, _73_812, _73_814, insert, _73_817) -> begin
insert
end))


let commit_record_cache : Prims.unit  ->  Prims.unit = (

let _73_828 = record_cache_aux
in (match (_73_828) with
| (_73_820, _73_822, _73_824, _73_826, commit) -> begin
commit
end))


let extract_record : env  ->  scope_mod Prims.list FStar_ST.ref  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun e new_globs uu___464 -> (match (uu___464) with
| FStar_Syntax_Syntax.Sig_bundle (sigs, _73_834, _73_836, _73_838) -> begin
(

let is_rec = (FStar_Util.for_some (fun uu___461 -> (match (uu___461) with
| (FStar_Syntax_Syntax.RecordType (_)) | (FStar_Syntax_Syntax.RecordConstructor (_)) -> begin
true
end
| _73_849 -> begin
false
end)))
in (

let find_dc = (fun dc -> (FStar_All.pipe_right sigs (FStar_Util.find_opt (fun uu___462 -> (match (uu___462) with
| FStar_Syntax_Syntax.Sig_datacon (lid, _73_856, _73_858, _73_860, _73_862, _73_864, _73_866, _73_868) -> begin
(FStar_Ident.lid_equals dc lid)
end
| _73_872 -> begin
false
end)))))
in (FStar_All.pipe_right sigs (FStar_List.iter (fun uu___463 -> (match (uu___463) with
| FStar_Syntax_Syntax.Sig_inductive_typ (typename, univs, parms, _73_878, _73_880, (dc)::[], tags, _73_885) -> begin
(match ((let _174_847 = (find_dc dc)
in (FStar_All.pipe_left FStar_Util.must _174_847))) with
| FStar_Syntax_Syntax.Sig_datacon (constrname, _73_890, t, _73_893, _73_895, _73_897, _73_899, _73_901) -> begin
(

let _73_907 = (FStar_Syntax_Util.arrow_formals t)
in (match (_73_907) with
| (formals, _73_906) -> begin
(

let is_rec = (is_rec tags)
in (

let formals' = (FStar_All.pipe_right formals (FStar_List.collect (fun _73_911 -> (match (_73_911) with
| (x, q) -> begin
if ((FStar_Syntax_Syntax.is_null_bv x) || (is_rec && (FStar_Syntax_Syntax.is_implicit q))) then begin
[]
end else begin
(((x), (q)))::[]
end
end))))
in (

let fields' = (FStar_All.pipe_right formals' (FStar_List.map (fun _73_915 -> (match (_73_915) with
| (x, q) -> begin
(let _174_850 = if is_rec then begin
(FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname)
end else begin
x.FStar_Syntax_Syntax.ppname
end
in ((_174_850), (x.FStar_Syntax_Syntax.sort)))
end))))
in (

let fields = fields'
in (

let record = {typename = typename; constrname = constrname.FStar_Ident.ident; parms = parms; fields = fields; is_private_or_abstract = ((FStar_List.contains FStar_Syntax_Syntax.Private tags) || (FStar_List.contains FStar_Syntax_Syntax.Abstract tags)); is_record = is_rec}
in (

let _73_919 = (let _174_852 = (let _174_851 = (FStar_ST.read new_globs)
in (Record_or_dc (record))::_174_851)
in (FStar_ST.op_Colon_Equals new_globs _174_852))
in (match (()) with
| () -> begin
(

let _73_933 = (

let add_field = (fun _73_924 -> (match (_73_924) with
| (id, _73_923) -> begin
(

let modul = (let _174_855 = (FStar_Ident.lid_of_ids constrname.FStar_Ident.ns)
in _174_855.FStar_Ident.str)
in (match ((get_exported_id_set e modul)) with
| Some (my_ex) -> begin
(

let my_exported_ids = (my_ex Exported_id_field)
in (

let _73_929 = (let _174_858 = (let _174_857 = (FStar_ST.read my_exported_ids)
in (FStar_Util.set_add id.FStar_Ident.idText _174_857))
in (FStar_ST.op_Colon_Equals my_exported_ids _174_858))
in (match (()) with
| () -> begin
(

let projname = (let _174_860 = (let _174_859 = (FStar_Syntax_Util.mk_field_projector_name_from_ident constrname id)
in _174_859.FStar_Ident.ident)
in _174_860.FStar_Ident.idText)
in (

let _73_931 = (let _174_862 = (let _174_861 = (FStar_ST.read my_exported_ids)
in (FStar_Util.set_add projname _174_861))
in (FStar_ST.op_Colon_Equals my_exported_ids _174_862))
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
| _73_935 -> begin
()
end)
end
| _73_937 -> begin
()
end))))))
end
| _73_939 -> begin
()
end))


let try_lookup_record_or_dc_by_field_name : env  ->  FStar_Ident.lident  ->  record_or_dc Prims.option = (fun env fieldname -> (

let find_in_cache = (fun fieldname -> (

let _73_946 = ((fieldname.FStar_Ident.ns), (fieldname.FStar_Ident.ident))
in (match (_73_946) with
| (ns, id) -> begin
(let _174_873 = (peek_record_cache ())
in (FStar_Util.find_map _174_873 (fun record -> (let _174_872 = (find_in_record ns id record (fun r -> Cont_ok (r)))
in (option_of_cont (fun _73_949 -> None) _174_872)))))
end)))
in (resolve_in_open_namespaces'' env fieldname Exported_id_field (fun _73_958 -> Cont_ignore) (fun _73_956 -> Cont_ignore) (fun r -> Cont_ok (r)) (fun fn -> (let _174_878 = (find_in_cache fn)
in (cont_of_option Cont_ignore _174_878))) (fun k _73_952 -> k))))


let try_lookup_record_by_field_name : env  ->  FStar_Ident.lident  ->  record_or_dc Prims.option = (fun env fieldname -> (match ((try_lookup_record_or_dc_by_field_name env fieldname)) with
| Some (r) when r.is_record -> begin
Some (r)
end
| _73_965 -> begin
None
end))


let belongs_to_record : env  ->  FStar_Ident.lident  ->  record_or_dc  ->  Prims.bool = (fun env lid record -> (match ((try_lookup_record_by_field_name env lid)) with
| Some (record') when ((let _174_891 = (FStar_Ident.path_of_ns record.typename.FStar_Ident.ns)
in (FStar_Ident.text_of_path _174_891)) = (let _174_892 = (FStar_Ident.path_of_ns record'.typename.FStar_Ident.ns)
in (FStar_Ident.text_of_path _174_892))) -> begin
(match ((find_in_record record.typename.FStar_Ident.ns lid.FStar_Ident.ident record (fun _73_971 -> Cont_ok (())))) with
| Cont_ok (_73_974) -> begin
true
end
| _73_977 -> begin
false
end)
end
| _73_979 -> begin
false
end))


let try_lookup_dc_by_field_name : env  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * Prims.bool) Prims.option = (fun env fieldname -> (match ((try_lookup_record_or_dc_by_field_name env fieldname)) with
| Some (r) -> begin
(let _174_900 = (let _174_899 = (let _174_898 = (FStar_Ident.lid_of_ids (FStar_List.append r.typename.FStar_Ident.ns ((r.constrname)::[])))
in (FStar_Ident.set_lid_range _174_898 (FStar_Ident.range_of_lid fieldname)))
in ((_174_899), (r.is_record)))
in Some (_174_900))
end
| _73_985 -> begin
None
end))


let string_set_ref_new : Prims.unit  ->  Prims.string FStar_Util.set FStar_ST.ref = (fun _73_986 -> (match (()) with
| () -> begin
(let _174_903 = (FStar_Util.new_set FStar_Util.compare FStar_Util.hashcode)
in (FStar_Util.mk_ref _174_903))
end))


let exported_id_set_new : Prims.unit  ->  exported_id_kind  ->  Prims.string FStar_Util.set FStar_ST.ref = (fun _73_987 -> (match (()) with
| () -> begin
(

let term_type_set = (string_set_ref_new ())
in (

let field_set = (string_set_ref_new ())
in (fun uu___465 -> (match (uu___465) with
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

let filter_scope_mods = (fun uu___466 -> (match (uu___466) with
| Rec_binding (_73_999) -> begin
true
end
| _73_1002 -> begin
false
end))
in (

let this_env = (

let _73_1004 = env
in (let _174_923 = (FStar_List.filter filter_scope_mods env.scope_mods)
in {curmodule = _73_1004.curmodule; curmonad = _73_1004.curmonad; modules = _73_1004.modules; scope_mods = _174_923; exported_ids = empty_exported_id_smap; trans_exported_ids = _73_1004.trans_exported_ids; includes = empty_include_smap; sigaccum = _73_1004.sigaccum; sigmap = _73_1004.sigmap; default_result_effect = _73_1004.default_result_effect; iface = _73_1004.iface; admitted_iface = _73_1004.admitted_iface; expect_typ = _73_1004.expect_typ}))
in (match ((try_lookup_lid' any_val exclude_if this_env lid)) with
| None -> begin
true
end
| Some (_73_1009) -> begin
false
end))))


let push_scope_mod : env  ->  scope_mod  ->  env = (fun env scope_mod -> (

let _73_1013 = env
in {curmodule = _73_1013.curmodule; curmonad = _73_1013.curmonad; modules = _73_1013.modules; scope_mods = (scope_mod)::env.scope_mods; exported_ids = _73_1013.exported_ids; trans_exported_ids = _73_1013.trans_exported_ids; includes = _73_1013.includes; sigaccum = _73_1013.sigaccum; sigmap = _73_1013.sigmap; default_result_effect = _73_1013.default_result_effect; iface = _73_1013.iface; admitted_iface = _73_1013.admitted_iface; expect_typ = _73_1013.expect_typ}))


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
(Prims.raise (FStar_Errors.Error ((((Prims.strcat "Duplicate top-level names " l.FStar_Ident.str)), ((FStar_Ident.range_of_lid l))))))
end))


let push_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env s -> (

let err = (fun l -> (

let sopt = (FStar_Util.smap_try_find (sigmap env) l.FStar_Ident.str)
in (

let r = (match (sopt) with
| Some (se, _73_1034) -> begin
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
in (let _174_956 = (let _174_955 = (let _174_954 = (FStar_Util.format2 "Duplicate top-level names [%s]; previously declared at %s" (FStar_Ident.text_of_lid l) r)
in ((_174_954), ((FStar_Ident.range_of_lid l))))
in FStar_Errors.Error (_174_955))
in (Prims.raise _174_956)))))
in (

let globals = (FStar_Util.mk_ref env.scope_mods)
in (

let env = (

let _73_1053 = (match (s) with
| FStar_Syntax_Syntax.Sig_let (_73_1044) -> begin
((false), (true))
end
| FStar_Syntax_Syntax.Sig_bundle (_73_1047) -> begin
((true), (true))
end
| _73_1050 -> begin
((false), (false))
end)
in (match (_73_1053) with
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

let _73_1057 = (extract_record env globals s)
in (

let _73_1059 = env
in {curmodule = _73_1059.curmodule; curmonad = _73_1059.curmonad; modules = _73_1059.modules; scope_mods = _73_1059.scope_mods; exported_ids = _73_1059.exported_ids; trans_exported_ids = _73_1059.trans_exported_ids; includes = _73_1059.includes; sigaccum = (s)::env.sigaccum; sigmap = _73_1059.sigmap; default_result_effect = _73_1059.default_result_effect; iface = _73_1059.iface; admitted_iface = _73_1059.admitted_iface; expect_typ = _73_1059.expect_typ}))
end
| Some (l) -> begin
(err l)
end))
end))
in (

let env = (

let _73_1064 = env
in (let _174_958 = (FStar_ST.read globals)
in {curmodule = _73_1064.curmodule; curmonad = _73_1064.curmonad; modules = _73_1064.modules; scope_mods = _174_958; exported_ids = _73_1064.exported_ids; trans_exported_ids = _73_1064.trans_exported_ids; includes = _73_1064.includes; sigaccum = _73_1064.sigaccum; sigmap = _73_1064.sigmap; default_result_effect = _73_1064.default_result_effect; iface = _73_1064.iface; admitted_iface = _73_1064.admitted_iface; expect_typ = _73_1064.expect_typ}))
in (

let _73_1081 = (match (s) with
| FStar_Syntax_Syntax.Sig_bundle (ses, _73_1069, _73_1071, _73_1073) -> begin
(let _174_960 = (FStar_List.map (fun se -> (((FStar_Syntax_Util.lids_of_sigelt se)), (se))) ses)
in ((env), (_174_960)))
end
| _73_1078 -> begin
((env), (((((FStar_Syntax_Util.lids_of_sigelt s)), (s)))::[]))
end)
in (match (_73_1081) with
| (env, lss) -> begin
(

let _73_1093 = (FStar_All.pipe_right lss (FStar_List.iter (fun _73_1084 -> (match (_73_1084) with
| (lids, se) -> begin
(FStar_All.pipe_right lids (FStar_List.iter (fun lid -> (

let _73_1086 = (let _174_964 = (let _174_963 = (FStar_ST.read globals)
in (Top_level_def (lid.FStar_Ident.ident))::_174_963)
in (FStar_ST.op_Colon_Equals globals _174_964))
in (match (()) with
| () -> begin
(

let modul = (let _174_965 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in _174_965.FStar_Ident.str)
in (

let _73_1092 = (match ((get_exported_id_set env modul)) with
| Some (f) -> begin
(

let my_exported_ids = (f Exported_id_term_type)
in (let _174_968 = (let _174_967 = (FStar_ST.read my_exported_ids)
in (FStar_Util.set_add lid.FStar_Ident.ident.FStar_Ident.idText _174_967))
in (FStar_ST.op_Colon_Equals my_exported_ids _174_968)))
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

let _73_1095 = env
in (let _174_969 = (FStar_ST.read globals)
in {curmodule = _73_1095.curmodule; curmonad = _73_1095.curmonad; modules = _73_1095.modules; scope_mods = _174_969; exported_ids = _73_1095.exported_ids; trans_exported_ids = _73_1095.trans_exported_ids; includes = _73_1095.includes; sigaccum = _73_1095.sigaccum; sigmap = _73_1095.sigmap; default_result_effect = _73_1095.default_result_effect; iface = _73_1095.iface; admitted_iface = _73_1095.admitted_iface; expect_typ = _73_1095.expect_typ}))
in env))
end)))))))


let push_namespace : env  ->  FStar_Ident.lident  ->  env = (fun env ns -> (

let _73_1110 = (match ((resolve_module_name env ns false)) with
| None -> begin
(

let modules = env.modules
in if (FStar_All.pipe_right modules (FStar_Util.for_some (fun _73_1105 -> (match (_73_1105) with
| (m, _73_1104) -> begin
(FStar_Util.starts_with (Prims.strcat (FStar_Ident.text_of_lid m) ".") (Prims.strcat (FStar_Ident.text_of_lid ns) "."))
end)))) then begin
((ns), (Open_namespace))
end else begin
(let _174_977 = (let _174_976 = (let _174_975 = (FStar_Util.format1 "Namespace %s cannot be found" (FStar_Ident.text_of_lid ns))
in ((_174_975), ((FStar_Ident.range_of_lid ns))))
in FStar_Errors.Error (_174_976))
in (Prims.raise _174_977))
end)
end
| Some (ns') -> begin
((ns'), (Open_module))
end)
in (match (_73_1110) with
| (ns', kd) -> begin
(push_scope_mod env (Open_module_or_namespace (((ns'), (kd)))))
end)))


let push_include : env  ->  FStar_Ident.lident  ->  env = (fun env ns -> (match ((resolve_module_name env ns false)) with
| Some (ns) -> begin
(

let env = (push_scope_mod env (Open_module_or_namespace (((ns), (Open_module)))))
in (

let curmod = (let _174_982 = (current_module env)
in _174_982.FStar_Ident.str)
in (

let _73_1120 = (match ((FStar_Util.smap_try_find env.includes curmod)) with
| None -> begin
()
end
| Some (incl) -> begin
(let _174_984 = (let _174_983 = (FStar_ST.read incl)
in (ns)::_174_983)
in (FStar_ST.op_Colon_Equals incl _174_984))
end)
in (match (()) with
| () -> begin
(match ((get_trans_exported_id_set env ns.FStar_Ident.str)) with
| Some (ns_trans_exports) -> begin
(

let _73_1137 = (match ((let _174_991 = (get_exported_id_set env curmod)
in (let _174_990 = (get_trans_exported_id_set env curmod)
in ((_174_991), (_174_990))))) with
| (Some (cur_exports), Some (cur_trans_exports)) -> begin
(

let update_exports = (fun k -> (

let ns_ex = (let _174_996 = (ns_trans_exports k)
in (FStar_ST.read _174_996))
in (

let ex = (cur_exports k)
in (

let _73_1132 = (let _174_998 = (let _174_997 = (FStar_ST.read ex)
in (FStar_Util.set_difference _174_997 ns_ex))
in (FStar_ST.op_Colon_Equals ex _174_998))
in (match (()) with
| () -> begin
(

let trans_ex = (cur_trans_exports k)
in (

let _73_1134 = (let _174_1000 = (let _174_999 = (FStar_ST.read ex)
in (FStar_Util.set_union _174_999 ns_ex))
in (FStar_ST.op_Colon_Equals trans_ex _174_1000))
in ()))
end)))))
in (FStar_List.iter update_exports all_exported_id_kinds))
end
| _73_1136 -> begin
()
end)
in (match (()) with
| () -> begin
env
end))
end
| None -> begin
(let _174_1009 = (let _174_1008 = (let _174_1007 = (FStar_Util.format1 "include: Module %s was not prepared" ns.FStar_Ident.str)
in ((_174_1007), ((FStar_Ident.range_of_lid ns))))
in FStar_Errors.Error (_174_1008))
in (Prims.raise _174_1009))
end)
end))))
end
| _73_1140 -> begin
(let _174_1012 = (let _174_1011 = (let _174_1010 = (FStar_Util.format1 "include: Module %s cannot be found" ns.FStar_Ident.str)
in ((_174_1010), ((FStar_Ident.range_of_lid ns))))
in FStar_Errors.Error (_174_1011))
in (Prims.raise _174_1012))
end))


let push_module_abbrev : env  ->  FStar_Ident.ident  ->  FStar_Ident.lident  ->  env = (fun env x l -> if (module_is_defined env l) then begin
(push_scope_mod env (Module_abbrev (((x), (l)))))
end else begin
(let _174_1021 = (let _174_1020 = (let _174_1019 = (FStar_Util.format1 "Module %s cannot be found" (FStar_Ident.text_of_lid l))
in ((_174_1019), ((FStar_Ident.range_of_lid l))))
in FStar_Errors.Error (_174_1020))
in (Prims.raise _174_1021))
end)


let check_admits : env  ->  Prims.unit = (fun env -> (FStar_All.pipe_right env.sigaccum (FStar_List.iter (fun se -> (match (se) with
| FStar_Syntax_Syntax.Sig_declare_typ (l, u, t, quals, r) -> begin
(match ((try_lookup_lid env l)) with
| None -> begin
(

let _73_1154 = (let _174_1027 = (let _174_1026 = (FStar_Range.string_of_range (FStar_Ident.range_of_lid l))
in (let _174_1025 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format2 "%s: Warning: Admitting %s without a definition\n" _174_1026 _174_1025)))
in (FStar_Util.print_string _174_1027))
in (FStar_Util.smap_add (sigmap env) l.FStar_Ident.str ((FStar_Syntax_Syntax.Sig_declare_typ (((l), (u), (t), ((FStar_Syntax_Syntax.Assumption)::quals), (r)))), (false))))
end
| Some (_73_1157) -> begin
()
end)
end
| _73_1160 -> begin
()
end)))))


let finish : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env modul -> (

let _73_1222 = (FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations (FStar_List.iter (fun uu___468 -> (match (uu___468) with
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _73_1167, _73_1169) -> begin
if ((FStar_List.contains FStar_Syntax_Syntax.Private quals) || (FStar_List.contains FStar_Syntax_Syntax.Abstract quals)) then begin
(FStar_All.pipe_right ses (FStar_List.iter (fun uu___467 -> (match (uu___467) with
| FStar_Syntax_Syntax.Sig_datacon (lid, _73_1175, _73_1177, _73_1179, _73_1181, _73_1183, _73_1185, _73_1187) -> begin
(FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str)
end
| _73_1191 -> begin
()
end))))
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _73_1194, _73_1196, quals, _73_1199) -> begin
if (FStar_List.contains FStar_Syntax_Syntax.Private quals) then begin
(FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str)
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_let ((_73_1203, lbs), r, _73_1208, quals, _73_1211) -> begin
(

let _73_1215 = if ((FStar_List.contains FStar_Syntax_Syntax.Private quals) || (FStar_List.contains FStar_Syntax_Syntax.Abstract quals)) then begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (let _174_1038 = (let _174_1037 = (let _174_1036 = (let _174_1035 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _174_1035.FStar_Syntax_Syntax.fv_name)
in _174_1036.FStar_Syntax_Syntax.v)
in _174_1037.FStar_Ident.str)
in (FStar_Util.smap_remove (sigmap env) _174_1038)))))
end else begin
()
end
in if ((FStar_List.contains FStar_Syntax_Syntax.Abstract quals) && (not ((FStar_List.contains FStar_Syntax_Syntax.Private quals)))) then begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (

let lid = (let _174_1041 = (let _174_1040 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _174_1040.FStar_Syntax_Syntax.fv_name)
in _174_1041.FStar_Syntax_Syntax.v)
in (

let decl = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), ((FStar_Syntax_Syntax.Assumption)::quals), (r)))
in (FStar_Util.smap_add (sigmap env) lid.FStar_Ident.str ((decl), (false))))))))
end else begin
()
end)
end
| _73_1221 -> begin
()
end))))
in (

let curmod = (let _174_1042 = (current_module env)
in _174_1042.FStar_Ident.str)
in (

let _73_1236 = (match ((let _174_1048 = (get_exported_id_set env curmod)
in (let _174_1047 = (get_trans_exported_id_set env curmod)
in ((_174_1048), (_174_1047))))) with
| (Some (cur_ex), Some (cur_trans_ex)) -> begin
(

let update_exports = (fun eikind -> (

let cur_ex_set = (let _174_1053 = (cur_ex eikind)
in (FStar_ST.read _174_1053))
in (

let cur_trans_ex_set_ref = (cur_trans_ex eikind)
in (let _174_1055 = (let _174_1054 = (FStar_ST.read cur_trans_ex_set_ref)
in (FStar_Util.set_union cur_ex_set _174_1054))
in (FStar_ST.op_Colon_Equals cur_trans_ex_set_ref _174_1055)))))
in (FStar_List.iter update_exports all_exported_id_kinds))
end
| _73_1235 -> begin
()
end)
in (match (()) with
| () -> begin
(

let _73_1237 = (filter_record_cache ())
in (match (()) with
| () -> begin
(

let _73_1238 = env
in {curmodule = None; curmonad = _73_1238.curmonad; modules = (((modul.FStar_Syntax_Syntax.name), (modul)))::env.modules; scope_mods = []; exported_ids = _73_1238.exported_ids; trans_exported_ids = _73_1238.trans_exported_ids; includes = _73_1238.includes; sigaccum = []; sigmap = _73_1238.sigmap; default_result_effect = _73_1238.default_result_effect; iface = _73_1238.iface; admitted_iface = _73_1238.admitted_iface; expect_typ = _73_1238.expect_typ})
end))
end)))))


type env_stack_ops =
{push : env  ->  env; mark : env  ->  env; reset_mark : env  ->  env; commit_mark : env  ->  env; pop : env  ->  env}


let is_Mkenv_stack_ops : env_stack_ops  ->  Prims.bool = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mkenv_stack_ops"))))


let stack_ops : env_stack_ops = (

let stack = (FStar_Util.mk_ref [])
in (

let push = (fun env -> (

let _73_1249 = (push_record_cache ())
in (

let _73_1251 = (let _174_1111 = (let _174_1110 = (FStar_ST.read stack)
in (env)::_174_1110)
in (FStar_ST.op_Colon_Equals stack _174_1111))
in (

let _73_1253 = env
in (let _174_1112 = (FStar_Util.smap_copy (sigmap env))
in {curmodule = _73_1253.curmodule; curmonad = _73_1253.curmonad; modules = _73_1253.modules; scope_mods = _73_1253.scope_mods; exported_ids = _73_1253.exported_ids; trans_exported_ids = _73_1253.trans_exported_ids; includes = _73_1253.includes; sigaccum = _73_1253.sigaccum; sigmap = _174_1112; default_result_effect = _73_1253.default_result_effect; iface = _73_1253.iface; admitted_iface = _73_1253.admitted_iface; expect_typ = _73_1253.expect_typ})))))
in (

let pop = (fun env -> (match ((FStar_ST.read stack)) with
| (env)::tl -> begin
(

let _73_1260 = (pop_record_cache ())
in (

let _73_1262 = (FStar_ST.op_Colon_Equals stack tl)
in env))
end
| _73_1265 -> begin
(failwith "Impossible: Too many pops")
end))
in (

let commit_mark = (fun env -> (

let _73_1268 = (commit_record_cache ())
in (match ((FStar_ST.read stack)) with
| (_73_1272)::tl -> begin
(

let _73_1274 = (FStar_ST.op_Colon_Equals stack tl)
in env)
end
| _73_1277 -> begin
(failwith "Impossible: Too many pops")
end)))
in {push = push; mark = push; reset_mark = pop; commit_mark = commit_mark; pop = pop}))))


let push : env  ->  env = (fun env -> (stack_ops.push env))


let mark : env  ->  env = (fun env -> (stack_ops.mark env))


let reset_mark : env  ->  env = (fun env -> (stack_ops.reset_mark env))


let commit_mark : env  ->  env = (fun env -> (stack_ops.commit_mark env))


let pop : env  ->  env = (fun env -> (stack_ops.pop env))


let export_interface : FStar_Ident.lident  ->  env  ->  env = (fun m env -> (

let sigelt_in_m = (fun se -> (match ((FStar_Syntax_Util.lids_of_sigelt se)) with
| (l)::_73_1288 -> begin
(l.FStar_Ident.nsstr = m.FStar_Ident.str)
end
| _73_1292 -> begin
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

let _73_1316 = (FStar_All.pipe_right keys (FStar_List.iter (fun k -> (match ((FStar_Util.smap_try_find sm' k)) with
| Some (se, true) when (sigelt_in_m se) -> begin
(

let _73_1302 = (FStar_Util.smap_remove sm' k)
in (

let se = (match (se) with
| FStar_Syntax_Syntax.Sig_declare_typ (l, u, t, q, r) -> begin
FStar_Syntax_Syntax.Sig_declare_typ (((l), (u), (t), ((FStar_Syntax_Syntax.Assumption)::q), (r)))
end
| _73_1312 -> begin
se
end)
in (FStar_Util.smap_add sm' k ((se), (false)))))
end
| _73_1315 -> begin
()
end))))
in env)))))))


let finish_module_or_interface : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env modul -> (

let _73_1320 = if (not (modul.FStar_Syntax_Syntax.is_interface)) then begin
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

let _73_1331 = (let _174_1148 = (exported_id_set_new ())
in (FStar_Util.smap_add env.exported_ids mname.FStar_Ident.str _174_1148))
in (match (()) with
| () -> begin
(

let _73_1332 = (let _174_1149 = (exported_id_set_new ())
in (FStar_Util.smap_add env.trans_exported_ids mname.FStar_Ident.str _174_1149))
in (match (()) with
| () -> begin
(

let _73_1333 = (let _174_1150 = (FStar_Util.mk_ref [])
in (FStar_Util.smap_add env.includes mname.FStar_Ident.str _174_1150))
in (match (()) with
| () -> begin
(

let _73_1334 = env
in (let _174_1152 = (FStar_List.map (fun lid -> Open_module_or_namespace (((lid), (Open_namespace)))) open_ns)
in {curmodule = Some (mname); curmonad = _73_1334.curmonad; modules = _73_1334.modules; scope_mods = _174_1152; exported_ids = _73_1334.exported_ids; trans_exported_ids = _73_1334.trans_exported_ids; includes = _73_1334.includes; sigaccum = _73_1334.sigaccum; sigmap = env.sigmap; default_result_effect = if ((FStar_Ident.lid_equals mname FStar_Syntax_Const.all_lid) || (has_all_in_scope env)) then begin
FStar_Syntax_Const.effect_ML_lid
end else begin
FStar_Syntax_Const.effect_Tot_lid
end; iface = intf; admitted_iface = admitted; expect_typ = _73_1334.expect_typ}))
end))
end))
end)))))
in (match ((FStar_All.pipe_right env.modules (FStar_Util.find_opt (fun _73_1340 -> (match (_73_1340) with
| (l, _73_1339) -> begin
(FStar_Ident.lid_equals l mname)
end))))) with
| None -> begin
(let _174_1154 = (prep env)
in ((_174_1154), (false)))
end
| Some (_73_1343, m) -> begin
(

let _73_1347 = if ((not (m.FStar_Syntax_Syntax.is_interface)) || intf) then begin
(let _174_1157 = (let _174_1156 = (let _174_1155 = (FStar_Util.format1 "Duplicate module or interface name: %s" mname.FStar_Ident.str)
in ((_174_1155), ((FStar_Ident.range_of_lid mname))))
in FStar_Errors.Error (_174_1156))
in (Prims.raise _174_1157))
end else begin
()
end
in (let _174_1159 = (let _174_1158 = (push env)
in (prep _174_1158))
in ((_174_1159), (true))))
end)))


let enter_monad_scope : env  ->  FStar_Ident.ident  ->  env = (fun env mname -> (match (env.curmonad) with
| Some (mname') -> begin
(Prims.raise (FStar_Errors.Error ((((Prims.strcat "Trying to define monad " (Prims.strcat mname.FStar_Ident.idText (Prims.strcat ", but already in monad scope " mname'.FStar_Ident.idText)))), (mname.FStar_Ident.idRange)))))
end
| None -> begin
(

let _73_1354 = env
in {curmodule = _73_1354.curmodule; curmonad = Some (mname); modules = _73_1354.modules; scope_mods = _73_1354.scope_mods; exported_ids = _73_1354.exported_ids; trans_exported_ids = _73_1354.trans_exported_ids; includes = _73_1354.includes; sigaccum = _73_1354.sigaccum; sigmap = _73_1354.sigmap; default_result_effect = _73_1354.default_result_effect; iface = _73_1354.iface; admitted_iface = _73_1354.admitted_iface; expect_typ = _73_1354.expect_typ})
end))


let fail_or = (fun env lookup lid -> (match ((lookup lid)) with
| None -> begin
(

let opened_modules = (FStar_List.map (fun _73_1363 -> (match (_73_1363) with
| (lid, _73_1362) -> begin
(FStar_Ident.text_of_lid lid)
end)) env.modules)
in (

let msg = (FStar_Util.format1 "Identifier not found: [%s]" (FStar_Ident.text_of_lid lid))
in (

let msg = if ((FStar_List.length lid.FStar_Ident.ns) = (Prims.parse_int "0")) then begin
msg
end else begin
(

let modul = (let _174_1171 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in (FStar_Ident.set_lid_range _174_1171 (FStar_Ident.range_of_lid lid)))
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
in (Prims.raise (FStar_Errors.Error (((msg), ((FStar_Ident.range_of_lid lid)))))))))
end
| Some (r) -> begin
r
end))


let fail_or2 = (fun lookup id -> (match ((lookup id)) with
| None -> begin
(Prims.raise (FStar_Errors.Error ((((Prims.strcat "Identifier not found [" (Prims.strcat id.FStar_Ident.idText "]"))), (id.FStar_Ident.idRange)))))
end
| Some (r) -> begin
r
end))




