
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


let uu___is_Open_module : open_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Open_module -> begin
true
end
| uu____12 -> begin
false
end))


let uu___is_Open_namespace : open_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Open_namespace -> begin
true
end
| uu____16 -> begin
false
end))


type open_module_or_namespace =
(FStar_Ident.lident * open_kind)

type record_or_dc =
{typename : FStar_Ident.lident; constrname : FStar_Ident.ident; parms : FStar_Syntax_Syntax.binders; fields : (FStar_Ident.ident * FStar_Syntax_Syntax.typ) Prims.list; is_private_or_abstract : Prims.bool; is_record : Prims.bool}

type scope_mod =
| Local_binding of local_binding
| Rec_binding of rec_binding
| Module_abbrev of module_abbrev
| Open_module_or_namespace of open_module_or_namespace
| Top_level_def of FStar_Ident.ident
| Record_or_dc of record_or_dc


let uu___is_Local_binding : scope_mod  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Local_binding (_0) -> begin
true
end
| uu____92 -> begin
false
end))


let __proj__Local_binding__item___0 : scope_mod  ->  local_binding = (fun projectee -> (match (projectee) with
| Local_binding (_0) -> begin
_0
end))


let uu___is_Rec_binding : scope_mod  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Rec_binding (_0) -> begin
true
end
| uu____104 -> begin
false
end))


let __proj__Rec_binding__item___0 : scope_mod  ->  rec_binding = (fun projectee -> (match (projectee) with
| Rec_binding (_0) -> begin
_0
end))


let uu___is_Module_abbrev : scope_mod  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Module_abbrev (_0) -> begin
true
end
| uu____116 -> begin
false
end))


let __proj__Module_abbrev__item___0 : scope_mod  ->  module_abbrev = (fun projectee -> (match (projectee) with
| Module_abbrev (_0) -> begin
_0
end))


let uu___is_Open_module_or_namespace : scope_mod  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Open_module_or_namespace (_0) -> begin
true
end
| uu____128 -> begin
false
end))


let __proj__Open_module_or_namespace__item___0 : scope_mod  ->  open_module_or_namespace = (fun projectee -> (match (projectee) with
| Open_module_or_namespace (_0) -> begin
_0
end))


let uu___is_Top_level_def : scope_mod  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Top_level_def (_0) -> begin
true
end
| uu____140 -> begin
false
end))


let __proj__Top_level_def__item___0 : scope_mod  ->  FStar_Ident.ident = (fun projectee -> (match (projectee) with
| Top_level_def (_0) -> begin
_0
end))


let uu___is_Record_or_dc : scope_mod  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Record_or_dc (_0) -> begin
true
end
| uu____152 -> begin
false
end))


let __proj__Record_or_dc__item___0 : scope_mod  ->  record_or_dc = (fun projectee -> (match (projectee) with
| Record_or_dc (_0) -> begin
_0
end))


type string_set =
Prims.string FStar_Util.set

type exported_id_kind =
| Exported_id_term_type
| Exported_id_field


let uu___is_Exported_id_term_type : exported_id_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Exported_id_term_type -> begin
true
end
| uu____164 -> begin
false
end))


let uu___is_Exported_id_field : exported_id_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Exported_id_field -> begin
true
end
| uu____168 -> begin
false
end))


type exported_id_set =
exported_id_kind  ->  string_set FStar_ST.ref

type env =
{curmodule : FStar_Ident.lident Prims.option; curmonad : FStar_Ident.ident Prims.option; modules : (FStar_Ident.lident * FStar_Syntax_Syntax.modul) Prims.list; scope_mods : scope_mod Prims.list; exported_ids : exported_id_set FStar_Util.smap; trans_exported_ids : exported_id_set FStar_Util.smap; includes : FStar_Ident.lident Prims.list FStar_ST.ref FStar_Util.smap; sigaccum : FStar_Syntax_Syntax.sigelts; sigmap : (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap; iface : Prims.bool; admitted_iface : Prims.bool; expect_typ : Prims.bool}

type foundname =
| Term_name of (FStar_Syntax_Syntax.typ * Prims.bool)
| Eff_name of (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident)


let uu___is_Term_name : foundname  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Term_name (_0) -> begin
true
end
| uu____314 -> begin
false
end))


let __proj__Term_name__item___0 : foundname  ->  (FStar_Syntax_Syntax.typ * Prims.bool) = (fun projectee -> (match (projectee) with
| Term_name (_0) -> begin
_0
end))


let uu___is_Eff_name : foundname  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Eff_name (_0) -> begin
true
end
| uu____334 -> begin
false
end))


let __proj__Eff_name__item___0 : foundname  ->  (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident) = (fun projectee -> (match (projectee) with
| Eff_name (_0) -> begin
_0
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
(let _0_285 = (current_module env)
in (qual _0_285 id))
end
| Some (monad) -> begin
(let _0_287 = (let _0_286 = (current_module env)
in (qual _0_286 monad))
in (FStar_Syntax_Util.mk_field_projector_name_from_ident _0_287 id))
end))


let new_sigmap = (fun uu____377 -> (FStar_Util.smap_create (Prims.parse_int "100")))


let empty_env : Prims.unit  ->  env = (fun uu____380 -> (let _0_291 = (new_sigmap ())
in (let _0_290 = (new_sigmap ())
in (let _0_289 = (new_sigmap ())
in (let _0_288 = (new_sigmap ())
in {curmodule = None; curmonad = None; modules = []; scope_mods = []; exported_ids = _0_291; trans_exported_ids = _0_290; includes = _0_289; sigaccum = []; sigmap = _0_288; iface = false; admitted_iface = false; expect_typ = false})))))


let sigmap : env  ->  (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap = (fun env -> env.sigmap)


let has_all_in_scope : env  ->  Prims.bool = (fun env -> (FStar_List.existsb (fun uu____398 -> (match (uu____398) with
| (m, uu____402) -> begin
(FStar_Ident.lid_equals m FStar_Syntax_Const.all_lid)
end)) env.modules))


let set_bv_range : FStar_Syntax_Syntax.bv  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.bv = (fun bv r -> (

let id = (

let uu___172_410 = bv.FStar_Syntax_Syntax.ppname
in {FStar_Ident.idText = uu___172_410.FStar_Ident.idText; FStar_Ident.idRange = r})
in (

let uu___173_411 = bv
in {FStar_Syntax_Syntax.ppname = id; FStar_Syntax_Syntax.index = uu___173_411.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu___173_411.FStar_Syntax_Syntax.sort})))


let bv_to_name : FStar_Syntax_Syntax.bv  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.term = (fun bv r -> (FStar_Syntax_Syntax.bv_to_name (set_bv_range bv r)))


let unmangleMap : (Prims.string * Prims.string * FStar_Syntax_Syntax.delta_depth * FStar_Syntax_Syntax.fv_qual Prims.option) Prims.list = ((("op_ColonColon"), ("Cons"), (FStar_Syntax_Syntax.Delta_constant), (Some (FStar_Syntax_Syntax.Data_ctor))))::((("not"), ("op_Negation"), (FStar_Syntax_Syntax.Delta_equational), (None)))::[]


let unmangleOpName : FStar_Ident.ident  ->  (FStar_Syntax_Syntax.term * Prims.bool) Prims.option = (fun id -> (

let t = (FStar_Util.find_map unmangleMap (fun uu____457 -> (match (uu____457) with
| (x, y, dd, dq) -> begin
(match ((id.FStar_Ident.idText = x)) with
| true -> begin
Some ((let _0_292 = (FStar_Ident.lid_of_path (("Prims")::(y)::[]) id.FStar_Ident.idRange)
in (FStar_Syntax_Syntax.fvar _0_292 dd dq)))
end
| uu____471 -> begin
None
end)
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


let uu___is_Cont_ok = (fun projectee -> (match (projectee) with
| Cont_ok (_0) -> begin
true
end
| uu____500 -> begin
false
end))


let __proj__Cont_ok__item___0 = (fun projectee -> (match (projectee) with
| Cont_ok (_0) -> begin
_0
end))


let uu___is_Cont_fail = (fun projectee -> (match (projectee) with
| Cont_fail -> begin
true
end
| uu____524 -> begin
false
end))


let uu___is_Cont_ignore = (fun projectee -> (match (projectee) with
| Cont_ignore -> begin
true
end
| uu____535 -> begin
false
end))


let option_of_cont = (fun k_ignore uu___142_554 -> (match (uu___142_554) with
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
in (match ((FStar_Ident.lid_equals typename' record.typename)) with
| true -> begin
(

let fname = (FStar_Ident.lid_of_ids (FStar_List.append record.typename.FStar_Ident.ns ((id)::[])))
in (

let find = (FStar_Util.find_map record.fields (fun uu____599 -> (match (uu____599) with
| (f, uu____604) -> begin
(match ((id.FStar_Ident.idText = f.FStar_Ident.idText)) with
| true -> begin
Some (record)
end
| uu____606 -> begin
None
end)
end)))
in (match (find) with
| Some (r) -> begin
(cont r)
end
| None -> begin
Cont_ignore
end)))
end
| uu____609 -> begin
Cont_ignore
end)))


let get_exported_id_set : env  ->  Prims.string  ->  (exported_id_kind  ->  string_set FStar_ST.ref) Prims.option = (fun e mname -> (FStar_Util.smap_try_find e.exported_ids mname))


let get_trans_exported_id_set : env  ->  Prims.string  ->  (exported_id_kind  ->  string_set FStar_ST.ref) Prims.option = (fun e mname -> (FStar_Util.smap_try_find e.trans_exported_ids mname))


let string_of_exported_id_kind : exported_id_kind  ->  Prims.string = (fun uu___143_640 -> (match (uu___143_640) with
| Exported_id_field -> begin
"field"
end
| Exported_id_term_type -> begin
"term/type"
end))


let find_in_module_with_includes = (fun eikind find_in_module find_in_module_default env ns id -> (

let idstr = id.FStar_Ident.idText
in (

let rec aux = (fun uu___144_689 -> (match (uu___144_689) with
| [] -> begin
find_in_module_default
end
| (modul)::q -> begin
(

let mname = modul.FStar_Ident.str
in (

let not_shadowed = (

let uu____697 = (get_exported_id_set env mname)
in (match (uu____697) with
| None -> begin
true
end
| Some (mex) -> begin
(

let mexports = (FStar_ST.read (mex eikind))
in (FStar_Util.set_mem idstr mexports))
end))
in (

let mincludes = (

let uu____717 = (FStar_Util.smap_try_find env.includes mname)
in (match (uu____717) with
| None -> begin
[]
end
| Some (minc) -> begin
(FStar_ST.read minc)
end))
in (

let look_into = (match (not_shadowed) with
| true -> begin
(find_in_module (qual modul id))
end
| uu____737 -> begin
Cont_ignore
end)
in (match (look_into) with
| Cont_ignore -> begin
(aux (FStar_List.append mincludes q))
end
| uu____739 -> begin
look_into
end)))))
end))
in (aux ((ns)::[])))))


let is_exported_id_field : exported_id_kind  ->  Prims.bool = (fun uu___145_743 -> (match (uu___145_743) with
| Exported_id_field -> begin
true
end
| uu____744 -> begin
false
end))


let try_lookup_id'' = (fun env id eikind k_local_binding k_rec_binding k_record find_in_module lookup_default_id -> (

let check_local_binding_id = (fun uu___146_833 -> (match (uu___146_833) with
| (id', uu____835, uu____836) -> begin
(id'.FStar_Ident.idText = id.FStar_Ident.idText)
end))
in (

let check_rec_binding_id = (fun uu___147_840 -> (match (uu___147_840) with
| (id', uu____842, uu____843) -> begin
(id'.FStar_Ident.idText = id.FStar_Ident.idText)
end))
in (

let curmod_ns = (FStar_Ident.ids_of_lid (current_module env))
in (

let proc = (fun uu___148_850 -> (match (uu___148_850) with
| Local_binding (l) when (check_local_binding_id l) -> begin
(k_local_binding l)
end
| Rec_binding (r) when (check_rec_binding_id r) -> begin
(k_rec_binding r)
end
| Open_module_or_namespace (ns, uu____855) -> begin
(find_in_module_with_includes eikind find_in_module Cont_ignore env ns id)
end
| Top_level_def (id') when (id'.FStar_Ident.idText = id.FStar_Ident.idText) -> begin
(lookup_default_id Cont_ignore id)
end
| Record_or_dc (r) when (is_exported_id_field eikind) -> begin
(let _0_293 = (FStar_Ident.lid_of_ids curmod_ns)
in (find_in_module_with_includes Exported_id_field (fun lid -> (

let id = lid.FStar_Ident.ident
in (find_in_record lid.FStar_Ident.ns id r k_record))) Cont_ignore env _0_293 id))
end
| uu____860 -> begin
Cont_ignore
end))
in (

let rec aux = (fun uu___149_866 -> (match (uu___149_866) with
| (a)::q -> begin
(let _0_294 = (proc a)
in (option_of_cont (fun uu____872 -> (aux q)) _0_294))
end
| [] -> begin
(let _0_295 = (lookup_default_id Cont_fail id)
in (option_of_cont (fun uu____873 -> None) _0_295))
end))
in (aux env.scope_mods)))))))


let found_local_binding = (fun r uu____892 -> (match (uu____892) with
| (id', x, mut) -> begin
(let _0_296 = (bv_to_name x r)
in ((_0_296), (mut)))
end))


let find_in_module = (fun env lid k_global_def k_not_found -> (

let uu____935 = (FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str)
in (match (uu____935) with
| Some (sb) -> begin
(k_global_def lid sb)
end
| None -> begin
k_not_found
end)))


let try_lookup_id : env  ->  FStar_Ident.ident  ->  (FStar_Syntax_Syntax.term * Prims.bool) Prims.option = (fun env id -> (

let uu____957 = (unmangleOpName id)
in (match (uu____957) with
| Some (f) -> begin
Some (f)
end
| uu____971 -> begin
(try_lookup_id'' env id Exported_id_term_type (fun r -> Cont_ok ((found_local_binding id.FStar_Ident.idRange r))) (fun uu____980 -> Cont_fail) (fun uu____983 -> Cont_ignore) (fun i -> (find_in_module env i (fun uu____990 uu____991 -> Cont_fail) Cont_ignore)) (fun uu____998 uu____999 -> Cont_fail))
end)))


let lookup_default_id = (fun env id k_global_def k_not_found -> (

let find_in_monad = (match (env.curmonad) with
| Some (uu____1051) -> begin
(

let lid = (qualify env id)
in (

let uu____1053 = (FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str)
in (match (uu____1053) with
| Some (r) -> begin
Some ((k_global_def lid r))
end
| None -> begin
None
end)))
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

let lid = (let _0_297 = (current_module env)
in (qual _0_297 id))
in (find_in_module env lid k_global_def k_not_found))
end)))


let module_is_defined : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> ((let _0_298 = (current_module env)
in (FStar_Ident.lid_equals lid _0_298)) || (FStar_List.existsb (fun x -> (FStar_Ident.lid_equals lid (Prims.fst x))) env.modules)))


let resolve_module_name : env  ->  FStar_Ident.lident  ->  Prims.bool  ->  FStar_Ident.lident Prims.option = (fun env lid honor_ns -> (

let nslen = (FStar_List.length lid.FStar_Ident.ns)
in (

let rec aux = (fun uu___150_1107 -> (match (uu___150_1107) with
| [] -> begin
(

let uu____1110 = (module_is_defined env lid)
in (match (uu____1110) with
| true -> begin
Some (lid)
end
| uu____1112 -> begin
None
end))
end
| (Open_module_or_namespace (ns, Open_namespace))::q when honor_ns -> begin
(

let new_lid = (let _0_301 = (let _0_300 = (FStar_Ident.path_of_lid ns)
in (let _0_299 = (FStar_Ident.path_of_lid lid)
in (FStar_List.append _0_300 _0_299)))
in (FStar_Ident.lid_of_path _0_301 (FStar_Ident.range_of_lid lid)))
in (

let uu____1117 = (module_is_defined env new_lid)
in (match (uu____1117) with
| true -> begin
Some (new_lid)
end
| uu____1119 -> begin
(aux q)
end)))
end
| (Module_abbrev (name, modul))::uu____1122 when ((nslen = (Prims.parse_int "0")) && (name.FStar_Ident.idText = lid.FStar_Ident.ident.FStar_Ident.idText)) -> begin
Some (modul)
end
| (uu____1126)::q -> begin
(aux q)
end))
in (aux env.scope_mods))))


let resolve_in_open_namespaces'' = (fun env lid eikind k_local_binding k_rec_binding k_record f_module l_default -> (match (lid.FStar_Ident.ns) with
| (uu____1214)::uu____1215 -> begin
(

let uu____1217 = (let _0_303 = (let _0_302 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in (FStar_Ident.set_lid_range _0_302 (FStar_Ident.range_of_lid lid)))
in (resolve_module_name env _0_303 true))
in (match (uu____1217) with
| None -> begin
None
end
| Some (modul) -> begin
(let _0_304 = (find_in_module_with_includes eikind f_module Cont_fail env modul lid.FStar_Ident.ident)
in (option_of_cont (fun uu____1221 -> None) _0_304))
end))
end
| [] -> begin
(try_lookup_id'' env lid.FStar_Ident.ident eikind k_local_binding k_rec_binding k_record f_module l_default)
end))


let cont_of_option = (fun k_none uu___151_1236 -> (match (uu___151_1236) with
| Some (v) -> begin
Cont_ok (v)
end
| None -> begin
k_none
end))


let resolve_in_open_namespaces' = (fun env lid k_local_binding k_rec_binding k_global_def -> (

let k_global_def' = (fun k lid def -> (let _0_305 = (k_global_def lid def)
in (cont_of_option k _0_305)))
in (

let f_module = (fun lid' -> (

let k = Cont_ignore
in (find_in_module env lid' (k_global_def' k) k)))
in (

let l_default = (fun k i -> (lookup_default_id env i (k_global_def' k) k))
in (resolve_in_open_namespaces'' env lid Exported_id_term_type (fun l -> (let _0_306 = (k_local_binding l)
in (cont_of_option Cont_fail _0_306))) (fun r -> (let _0_307 = (k_rec_binding r)
in (cont_of_option Cont_fail _0_307))) (fun uu____1335 -> Cont_ignore) f_module l_default)))))


let fv_qual_of_se : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.fv_qual Prims.option = (fun uu___153_1339 -> (match (uu___153_1339) with
| FStar_Syntax_Syntax.Sig_datacon (uu____1341, uu____1342, uu____1343, l, uu____1345, quals, uu____1347, uu____1348) -> begin
(

let qopt = (FStar_Util.find_map quals (fun uu___152_1355 -> (match (uu___152_1355) with
| FStar_Syntax_Syntax.RecordConstructor (uu____1357, fs) -> begin
Some (FStar_Syntax_Syntax.Record_ctor (((l), (fs))))
end
| uu____1364 -> begin
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
| FStar_Syntax_Syntax.Sig_declare_typ (uu____1368, uu____1369, uu____1370, quals, uu____1372) -> begin
None
end
| uu____1375 -> begin
None
end))


let lb_fv : FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.fv = (fun lbs lid -> (let _0_308 = (FStar_Util.find_map lbs (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let uu____1387 = (FStar_Syntax_Syntax.fv_eq_lid fv lid)
in (match (uu____1387) with
| true -> begin
Some (fv)
end
| uu____1389 -> begin
None
end)))))
in (FStar_All.pipe_right _0_308 FStar_Util.must)))


let ns_of_lid_equals : FStar_Ident.lident  ->  FStar_Ident.lident  ->  Prims.bool = (fun lid ns -> (((FStar_List.length lid.FStar_Ident.ns) = (FStar_List.length (FStar_Ident.ids_of_lid ns))) && (let _0_309 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in (FStar_Ident.lid_equals _0_309 ns))))


let try_lookup_name : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  foundname Prims.option = (fun any_val exclude_interf env lid -> (

let occurrence_range = (FStar_Ident.range_of_lid lid)
in (

let k_global_def = (fun source_lid uu___157_1424 -> (match (uu___157_1424) with
| (uu____1428, true) when exclude_interf -> begin
None
end
| (se, uu____1430) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____1432) -> begin
Some (Term_name ((let _0_310 = (FStar_Syntax_Syntax.fvar source_lid FStar_Syntax_Syntax.Delta_constant None)
in ((_0_310), (false)))))
end
| FStar_Syntax_Syntax.Sig_datacon (uu____1444) -> begin
Some (Term_name ((let _0_312 = (let _0_311 = (fv_qual_of_se se)
in (FStar_Syntax_Syntax.fvar source_lid FStar_Syntax_Syntax.Delta_constant _0_311))
in ((_0_312), (false)))))
end
| FStar_Syntax_Syntax.Sig_let ((uu____1455, lbs), uu____1457, uu____1458, uu____1459, uu____1460) -> begin
(

let fv = (lb_fv lbs source_lid)
in Some (Term_name ((let _0_313 = (FStar_Syntax_Syntax.fvar source_lid fv.FStar_Syntax_Syntax.fv_delta fv.FStar_Syntax_Syntax.fv_qual)
in ((_0_313), (false))))))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____1474, uu____1475, quals, uu____1477) -> begin
(

let uu____1480 = (any_val || (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___154_1482 -> (match (uu___154_1482) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| uu____1483 -> begin
false
end)))))
in (match (uu____1480) with
| true -> begin
(

let lid = (FStar_Ident.set_lid_range lid (FStar_Ident.range_of_lid source_lid))
in (

let dd = (

let uu____1487 = ((FStar_Syntax_Util.is_primop_lid lid) || ((ns_of_lid_equals lid FStar_Syntax_Const.prims_lid) && (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___155_1489 -> (match (uu___155_1489) with
| (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) -> begin
true
end
| uu____1492 -> begin
false
end))))))
in (match (uu____1487) with
| true -> begin
FStar_Syntax_Syntax.Delta_equational
end
| uu____1493 -> begin
FStar_Syntax_Syntax.Delta_constant
end))
in (

let uu____1494 = (FStar_Util.find_map quals (fun uu___156_1496 -> (match (uu___156_1496) with
| FStar_Syntax_Syntax.Reflectable (refl_monad) -> begin
Some (refl_monad)
end
| uu____1499 -> begin
None
end)))
in (match (uu____1494) with
| Some (refl_monad) -> begin
(

let refl_const = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (refl_monad)))) None occurrence_range)
in Some (Term_name (((refl_const), (false)))))
end
| uu____1515 -> begin
Some (Term_name ((let _0_315 = (let _0_314 = (fv_qual_of_se se)
in (FStar_Syntax_Syntax.fvar lid dd _0_314))
in ((_0_315), (false)))))
end))))
end
| uu____1517 -> begin
None
end))
end
| (FStar_Syntax_Syntax.Sig_new_effect_for_free (ne, _)) | (FStar_Syntax_Syntax.Sig_new_effect (ne, _)) -> begin
Some (Eff_name (((se), ((FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname (FStar_Ident.range_of_lid source_lid))))))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (uu____1521) -> begin
Some (Eff_name (((se), (source_lid))))
end
| uu____1531 -> begin
None
end)
end))
in (

let k_local_binding = (fun r -> Some (Term_name ((found_local_binding (FStar_Ident.range_of_lid lid) r))))
in (

let k_rec_binding = (fun uu____1550 -> (match (uu____1550) with
| (id, l, dd) -> begin
Some (Term_name ((let _0_316 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range l (FStar_Ident.range_of_lid lid)) dd None)
in ((_0_316), (false)))))
end))
in (

let found_unmangled = (match (lid.FStar_Ident.ns) with
| [] -> begin
(

let uu____1561 = (unmangleOpName lid.FStar_Ident.ident)
in (match (uu____1561) with
| Some (f) -> begin
Some (Term_name (f))
end
| uu____1571 -> begin
None
end))
end
| uu____1575 -> begin
None
end)
in (match (found_unmangled) with
| None -> begin
(resolve_in_open_namespaces' env lid k_local_binding k_rec_binding k_global_def)
end
| x -> begin
x
end)))))))


let try_lookup_effect_name' : Prims.bool  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident) Prims.option = (fun exclude_interf env lid -> (

let uu____1595 = (try_lookup_name true exclude_interf env lid)
in (match (uu____1595) with
| Some (Eff_name (o, l)) -> begin
Some (((o), (l)))
end
| uu____1604 -> begin
None
end)))


let try_lookup_effect_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env l -> (

let uu____1615 = (try_lookup_effect_name' (not (env.iface)) env l)
in (match (uu____1615) with
| Some (o, l) -> begin
Some (l)
end
| uu____1624 -> begin
None
end)))


let try_lookup_effect_name_and_attributes : env  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.cflags Prims.list) Prims.option = (fun env l -> (

let uu____1638 = (try_lookup_effect_name' (not (env.iface)) env l)
in (match (uu____1638) with
| Some (FStar_Syntax_Syntax.Sig_new_effect (ne, uu____1647), l) -> begin
Some (((l), (ne.FStar_Syntax_Syntax.cattributes)))
end
| Some (FStar_Syntax_Syntax.Sig_new_effect_for_free (ne, uu____1656), l) -> begin
Some (((l), (ne.FStar_Syntax_Syntax.cattributes)))
end
| Some (FStar_Syntax_Syntax.Sig_effect_abbrev (uu____1664, uu____1665, uu____1666, uu____1667, uu____1668, cattributes, uu____1670), l) -> begin
Some (((l), (cattributes)))
end
| uu____1682 -> begin
None
end)))


let try_lookup_effect_defn : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl Prims.option = (fun env l -> (

let uu____1696 = (try_lookup_effect_name' (not (env.iface)) env l)
in (match (uu____1696) with
| Some (FStar_Syntax_Syntax.Sig_new_effect (ne, uu____1702), uu____1703) -> begin
Some (ne)
end
| Some (FStar_Syntax_Syntax.Sig_new_effect_for_free (ne, uu____1707), uu____1708) -> begin
Some (ne)
end
| uu____1711 -> begin
None
end)))


let is_effect_name : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let uu____1721 = (try_lookup_effect_name env lid)
in (match (uu____1721) with
| None -> begin
false
end
| Some (uu____1723) -> begin
true
end)))


let lookup_letbinding_quals : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.qualifier Prims.list = (fun env lid -> (

let k_global_def = (fun lid uu___158_1741 -> (match (uu___158_1741) with
| (FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____1747, uu____1748, quals, uu____1750), uu____1751) -> begin
Some (quals)
end
| uu____1755 -> begin
None
end))
in (

let uu____1759 = (resolve_in_open_namespaces' env lid (fun uu____1763 -> None) (fun uu____1765 -> None) k_global_def)
in (match (uu____1759) with
| Some (quals) -> begin
quals
end
| uu____1771 -> begin
[]
end))))


let try_lookup_module : env  ->  Prims.string Prims.list  ->  FStar_Syntax_Syntax.modul Prims.option = (fun env path -> (

let uu____1783 = (FStar_List.tryFind (fun uu____1789 -> (match (uu____1789) with
| (mlid, modul) -> begin
(let _0_317 = (FStar_Ident.path_of_lid mlid)
in (_0_317 = path))
end)) env.modules)
in (match (uu____1783) with
| Some (uu____1796, modul) -> begin
Some (modul)
end
| None -> begin
None
end)))


let try_lookup_let : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env lid -> (

let k_global_def = (fun lid uu___159_1818 -> (match (uu___159_1818) with
| (FStar_Syntax_Syntax.Sig_let ((uu____1822, lbs), uu____1824, uu____1825, uu____1826, uu____1827), uu____1828) -> begin
(

let fv = (lb_fv lbs lid)
in Some ((FStar_Syntax_Syntax.fvar lid fv.FStar_Syntax_Syntax.fv_delta fv.FStar_Syntax_Syntax.fv_qual)))
end
| uu____1841 -> begin
None
end))
in (resolve_in_open_namespaces' env lid (fun uu____1844 -> None) (fun uu____1845 -> None) k_global_def)))


let try_lookup_definition : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env lid -> (

let k_global_def = (fun lid uu___160_1864 -> (match (uu___160_1864) with
| (FStar_Syntax_Syntax.Sig_let (lbs, uu____1871, uu____1872, uu____1873, uu____1874), uu____1875) -> begin
(FStar_Util.find_map (Prims.snd lbs) (fun lb -> (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv lid) -> begin
Some (lb.FStar_Syntax_Syntax.lbdef)
end
| uu____1892 -> begin
None
end)))
end
| uu____1897 -> begin
None
end))
in (resolve_in_open_namespaces' env lid (fun uu____1904 -> None) (fun uu____1907 -> None) k_global_def)))


let try_lookup_lid' : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term * Prims.bool) Prims.option = (fun any_val exclude_interf env lid -> (

let uu____1928 = (try_lookup_name any_val exclude_interf env lid)
in (match (uu____1928) with
| Some (Term_name (e, mut)) -> begin
Some (((e), (mut)))
end
| uu____1937 -> begin
None
end)))


let try_lookup_lid : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term * Prims.bool) Prims.option = (fun env l -> (try_lookup_lid' env.iface false env l))


let try_lookup_datacon : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.fv Prims.option = (fun env lid -> (

let k_global_def = (fun lid uu___162_1966 -> (match (uu___162_1966) with
| (FStar_Syntax_Syntax.Sig_declare_typ (uu____1970, uu____1971, uu____1972, quals, uu____1974), uu____1975) -> begin
(

let uu____1978 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___161_1980 -> (match (uu___161_1980) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| uu____1981 -> begin
false
end))))
in (match (uu____1978) with
| true -> begin
Some ((FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant None))
end
| uu____1983 -> begin
None
end))
end
| (FStar_Syntax_Syntax.Sig_datacon (uu____1984), uu____1985) -> begin
Some ((FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor))))
end
| uu____1996 -> begin
None
end))
in (resolve_in_open_namespaces' env lid (fun uu____1999 -> None) (fun uu____2000 -> None) k_global_def)))


let find_all_datacons : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.list Prims.option = (fun env lid -> (

let k_global_def = (fun lid uu___163_2019 -> (match (uu___163_2019) with
| (FStar_Syntax_Syntax.Sig_inductive_typ (uu____2024, uu____2025, uu____2026, uu____2027, uu____2028, datas, uu____2030, uu____2031), uu____2032) -> begin
Some (datas)
end
| uu____2040 -> begin
None
end))
in (resolve_in_open_namespaces' env lid (fun uu____2045 -> None) (fun uu____2047 -> None) k_global_def)))


let record_cache_aux_with_filter : (((Prims.unit  ->  Prims.unit) * (Prims.unit  ->  Prims.unit) * (Prims.unit  ->  record_or_dc Prims.list) * (record_or_dc  ->  Prims.unit) * (Prims.unit  ->  Prims.unit)) * (Prims.unit  ->  Prims.unit)) = (

let record_cache = (FStar_Util.mk_ref (([])::[]))
in (

let push = (fun uu____2081 -> (let _0_320 = (let _0_319 = (FStar_List.hd (FStar_ST.read record_cache))
in (let _0_318 = (FStar_ST.read record_cache)
in (_0_319)::_0_318))
in (FStar_ST.write record_cache _0_320)))
in (

let pop = (fun uu____2099 -> (let _0_321 = (FStar_List.tl (FStar_ST.read record_cache))
in (FStar_ST.write record_cache _0_321)))
in (

let peek = (fun uu____2113 -> (FStar_List.hd (FStar_ST.read record_cache)))
in (

let insert = (fun r -> (let _0_325 = (let _0_324 = (let _0_322 = (peek ())
in (r)::_0_322)
in (let _0_323 = (FStar_List.tl (FStar_ST.read record_cache))
in (_0_324)::_0_323))
in (FStar_ST.write record_cache _0_325)))
in (

let commit = (fun uu____2136 -> (

let uu____2137 = (FStar_ST.read record_cache)
in (match (uu____2137) with
| (hd)::(uu____2145)::tl -> begin
(FStar_ST.write record_cache ((hd)::tl))
end
| uu____2158 -> begin
(failwith "Impossible")
end)))
in (

let filter = (fun uu____2164 -> (

let rc = (peek ())
in ((pop ());
(match (()) with
| () -> begin
(

let filtered = (FStar_List.filter (fun r -> (not (r.is_private_or_abstract))) rc)
in (let _0_327 = (let _0_326 = (FStar_ST.read record_cache)
in (filtered)::_0_326)
in (FStar_ST.write record_cache _0_327)))
end);
)))
in (

let aux = ((push), (pop), (peek), (insert), (commit))
in ((aux), (filter))))))))))


let record_cache_aux : ((Prims.unit  ->  Prims.unit) * (Prims.unit  ->  Prims.unit) * (Prims.unit  ->  record_or_dc Prims.list) * (record_or_dc  ->  Prims.unit) * (Prims.unit  ->  Prims.unit)) = (

let uu____2242 = record_cache_aux_with_filter
in (match (uu____2242) with
| (aux, uu____2280) -> begin
aux
end))


let filter_record_cache : Prims.unit  ->  Prims.unit = (

let uu____2319 = record_cache_aux_with_filter
in (match (uu____2319) with
| (uu____2342, filter) -> begin
filter
end))


let push_record_cache : Prims.unit  ->  Prims.unit = (

let uu____2382 = record_cache_aux
in (match (uu____2382) with
| (push, uu____2402, uu____2403, uu____2404, uu____2405) -> begin
push
end))


let pop_record_cache : Prims.unit  ->  Prims.unit = (

let uu____2430 = record_cache_aux
in (match (uu____2430) with
| (uu____2449, pop, uu____2451, uu____2452, uu____2453) -> begin
pop
end))


let peek_record_cache : Prims.unit  ->  record_or_dc Prims.list = (

let uu____2479 = record_cache_aux
in (match (uu____2479) with
| (uu____2499, uu____2500, peek, uu____2502, uu____2503) -> begin
peek
end))


let insert_record_cache : record_or_dc  ->  Prims.unit = (

let uu____2528 = record_cache_aux
in (match (uu____2528) with
| (uu____2547, uu____2548, uu____2549, insert, uu____2551) -> begin
insert
end))


let commit_record_cache : Prims.unit  ->  Prims.unit = (

let uu____2576 = record_cache_aux
in (match (uu____2576) with
| (uu____2595, uu____2596, uu____2597, uu____2598, commit) -> begin
commit
end))


let extract_record : env  ->  scope_mod Prims.list FStar_ST.ref  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun e new_globs uu___167_2633 -> (match (uu___167_2633) with
| FStar_Syntax_Syntax.Sig_bundle (sigs, uu____2638, uu____2639, uu____2640) -> begin
(

let is_rec = (FStar_Util.for_some (fun uu___164_2651 -> (match (uu___164_2651) with
| (FStar_Syntax_Syntax.RecordType (_)) | (FStar_Syntax_Syntax.RecordConstructor (_)) -> begin
true
end
| uu____2654 -> begin
false
end)))
in (

let find_dc = (fun dc -> (FStar_All.pipe_right sigs (FStar_Util.find_opt (fun uu___165_2662 -> (match (uu___165_2662) with
| FStar_Syntax_Syntax.Sig_datacon (lid, uu____2664, uu____2665, uu____2666, uu____2667, uu____2668, uu____2669, uu____2670) -> begin
(FStar_Ident.lid_equals dc lid)
end
| uu____2675 -> begin
false
end)))))
in (FStar_All.pipe_right sigs (FStar_List.iter (fun uu___166_2677 -> (match (uu___166_2677) with
| FStar_Syntax_Syntax.Sig_inductive_typ (typename, univs, parms, uu____2681, uu____2682, (dc)::[], tags, uu____2685) -> begin
(

let uu____2691 = (let _0_328 = (find_dc dc)
in (FStar_All.pipe_left FStar_Util.must _0_328))
in (match (uu____2691) with
| FStar_Syntax_Syntax.Sig_datacon (constrname, uu____2694, t, uu____2696, uu____2697, uu____2698, uu____2699, uu____2700) -> begin
(

let uu____2705 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____2705) with
| (formals, uu____2714) -> begin
(

let is_rec = (is_rec tags)
in (

let formals' = (FStar_All.pipe_right formals (FStar_List.collect (fun uu____2740 -> (match (uu____2740) with
| (x, q) -> begin
(

let uu____2748 = ((FStar_Syntax_Syntax.is_null_bv x) || (is_rec && (FStar_Syntax_Syntax.is_implicit q)))
in (match (uu____2748) with
| true -> begin
[]
end
| uu____2754 -> begin
(((x), (q)))::[]
end))
end))))
in (

let fields' = (FStar_All.pipe_right formals' (FStar_List.map (fun uu____2779 -> (match (uu____2779) with
| (x, q) -> begin
(let _0_329 = (match (is_rec) with
| true -> begin
(FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname)
end
| uu____2790 -> begin
x.FStar_Syntax_Syntax.ppname
end)
in ((_0_329), (x.FStar_Syntax_Syntax.sort)))
end))))
in (

let fields = fields'
in (

let record = {typename = typename; constrname = constrname.FStar_Ident.ident; parms = parms; fields = fields; is_private_or_abstract = ((FStar_List.contains FStar_Syntax_Syntax.Private tags) || (FStar_List.contains FStar_Syntax_Syntax.Abstract tags)); is_record = is_rec}
in ((let _0_331 = (let _0_330 = (FStar_ST.read new_globs)
in (Record_or_dc (record))::_0_330)
in (FStar_ST.write new_globs _0_331));
(match (()) with
| () -> begin
((

let add_field = (fun uu____2813 -> (match (uu____2813) with
| (id, uu____2819) -> begin
(

let modul = (FStar_Ident.lid_of_ids constrname.FStar_Ident.ns).FStar_Ident.str
in (

let uu____2825 = (get_exported_id_set e modul)
in (match (uu____2825) with
| Some (my_ex) -> begin
(

let my_exported_ids = (my_ex Exported_id_field)
in ((let _0_333 = (let _0_332 = (FStar_ST.read my_exported_ids)
in (FStar_Util.set_add id.FStar_Ident.idText _0_332))
in (FStar_ST.write my_exported_ids _0_333));
(match (()) with
| () -> begin
(

let projname = (FStar_Syntax_Util.mk_field_projector_name_from_ident constrname id).FStar_Ident.ident.FStar_Ident.idText
in (

let _0_335 = (let _0_334 = (FStar_ST.read my_exported_ids)
in (FStar_Util.set_add projname _0_334))
in (FStar_ST.write my_exported_ids _0_335)))
end);
))
end
| None -> begin
()
end)))
end))
in (FStar_List.iter add_field fields'));
(match (()) with
| () -> begin
(insert_record_cache record)
end);
)
end);
))))))
end))
end
| uu____2858 -> begin
()
end))
end
| uu____2859 -> begin
()
end))))))
end
| uu____2860 -> begin
()
end))


let try_lookup_record_or_dc_by_field_name : env  ->  FStar_Ident.lident  ->  record_or_dc Prims.option = (fun env fieldname -> (

let find_in_cache = (fun fieldname -> (

let uu____2873 = ((fieldname.FStar_Ident.ns), (fieldname.FStar_Ident.ident))
in (match (uu____2873) with
| (ns, id) -> begin
(let _0_337 = (peek_record_cache ())
in (FStar_Util.find_map _0_337 (fun record -> (let _0_336 = (find_in_record ns id record (fun r -> Cont_ok (r)))
in (option_of_cont (fun uu____2884 -> None) _0_336)))))
end)))
in (resolve_in_open_namespaces'' env fieldname Exported_id_field (fun uu____2886 -> Cont_ignore) (fun uu____2887 -> Cont_ignore) (fun r -> Cont_ok (r)) (fun fn -> (let _0_338 = (find_in_cache fn)
in (cont_of_option Cont_ignore _0_338))) (fun k uu____2891 -> k))))


let try_lookup_record_by_field_name : env  ->  FStar_Ident.lident  ->  record_or_dc Prims.option = (fun env fieldname -> (

let uu____2900 = (try_lookup_record_or_dc_by_field_name env fieldname)
in (match (uu____2900) with
| Some (r) when r.is_record -> begin
Some (r)
end
| uu____2904 -> begin
None
end)))


let belongs_to_record : env  ->  FStar_Ident.lident  ->  record_or_dc  ->  Prims.bool = (fun env lid record -> (

let uu____2915 = (try_lookup_record_by_field_name env lid)
in (match (uu____2915) with
| Some (record') when (let _0_340 = (FStar_Ident.text_of_path (FStar_Ident.path_of_ns record.typename.FStar_Ident.ns))
in (let _0_339 = (FStar_Ident.text_of_path (FStar_Ident.path_of_ns record'.typename.FStar_Ident.ns))
in (_0_340 = _0_339))) -> begin
(

let uu____2918 = (find_in_record record.typename.FStar_Ident.ns lid.FStar_Ident.ident record (fun uu____2920 -> Cont_ok (())))
in (match (uu____2918) with
| Cont_ok (uu____2921) -> begin
true
end
| uu____2922 -> begin
false
end))
end
| uu____2924 -> begin
false
end)))


let try_lookup_dc_by_field_name : env  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * Prims.bool) Prims.option = (fun env fieldname -> (

let uu____2935 = (try_lookup_record_or_dc_by_field_name env fieldname)
in (match (uu____2935) with
| Some (r) -> begin
Some ((let _0_342 = (let _0_341 = (FStar_Ident.lid_of_ids (FStar_List.append r.typename.FStar_Ident.ns ((r.constrname)::[])))
in (FStar_Ident.set_lid_range _0_341 (FStar_Ident.range_of_lid fieldname)))
in ((_0_342), (r.is_record))))
end
| uu____2943 -> begin
None
end)))


let string_set_ref_new : Prims.unit  ->  Prims.string FStar_Util.set FStar_ST.ref = (fun uu____2952 -> (FStar_Util.mk_ref (FStar_Util.new_set FStar_Util.compare FStar_Util.hashcode)))


let exported_id_set_new : Prims.unit  ->  exported_id_kind  ->  Prims.string FStar_Util.set FStar_ST.ref = (fun uu____2962 -> (

let term_type_set = (string_set_ref_new ())
in (

let field_set = (string_set_ref_new ())
in (fun uu___168_2971 -> (match (uu___168_2971) with
| Exported_id_term_type -> begin
term_type_set
end
| Exported_id_field -> begin
field_set
end)))))


let empty_include_smap : FStar_Ident.lident Prims.list FStar_ST.ref FStar_Util.smap = (new_sigmap ())


let empty_exported_id_smap : exported_id_set FStar_Util.smap = (new_sigmap ())


let unique : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  Prims.bool = (fun any_val exclude_if env lid -> (

let filter_scope_mods = (fun uu___169_2997 -> (match (uu___169_2997) with
| Rec_binding (uu____2998) -> begin
true
end
| uu____2999 -> begin
false
end))
in (

let this_env = (

let uu___174_3001 = env
in (let _0_343 = (FStar_List.filter filter_scope_mods env.scope_mods)
in {curmodule = uu___174_3001.curmodule; curmonad = uu___174_3001.curmonad; modules = uu___174_3001.modules; scope_mods = _0_343; exported_ids = empty_exported_id_smap; trans_exported_ids = uu___174_3001.trans_exported_ids; includes = empty_include_smap; sigaccum = uu___174_3001.sigaccum; sigmap = uu___174_3001.sigmap; iface = uu___174_3001.iface; admitted_iface = uu___174_3001.admitted_iface; expect_typ = uu___174_3001.expect_typ}))
in (

let uu____3002 = (try_lookup_lid' any_val exclude_if this_env lid)
in (match (uu____3002) with
| None -> begin
true
end
| Some (uu____3008) -> begin
false
end)))))


let push_scope_mod : env  ->  scope_mod  ->  env = (fun env scope_mod -> (

let uu___175_3019 = env
in {curmodule = uu___175_3019.curmodule; curmonad = uu___175_3019.curmonad; modules = uu___175_3019.modules; scope_mods = (scope_mod)::env.scope_mods; exported_ids = uu___175_3019.exported_ids; trans_exported_ids = uu___175_3019.trans_exported_ids; includes = uu___175_3019.includes; sigaccum = uu___175_3019.sigaccum; sigmap = uu___175_3019.sigmap; iface = uu___175_3019.iface; admitted_iface = uu___175_3019.admitted_iface; expect_typ = uu___175_3019.expect_typ}))


let push_bv' : env  ->  FStar_Ident.ident  ->  Prims.bool  ->  (env * FStar_Syntax_Syntax.bv) = (fun env x is_mutable -> (

let bv = (FStar_Syntax_Syntax.gen_bv x.FStar_Ident.idText (Some (x.FStar_Ident.idRange)) FStar_Syntax_Syntax.tun)
in (((push_scope_mod env (Local_binding (((x), (bv), (is_mutable)))))), (bv))))


let push_bv_mutable : env  ->  FStar_Ident.ident  ->  (env * FStar_Syntax_Syntax.bv) = (fun env x -> (push_bv' env x true))


let push_bv : env  ->  FStar_Ident.ident  ->  (env * FStar_Syntax_Syntax.bv) = (fun env x -> (push_bv' env x false))


let push_top_level_rec_binding : env  ->  FStar_Ident.ident  ->  FStar_Syntax_Syntax.delta_depth  ->  env = (fun env x dd -> (

let l = (qualify env x)
in (

let uu____3058 = ((unique false true env l) || (FStar_Options.interactive ()))
in (match (uu____3058) with
| true -> begin
(push_scope_mod env (Rec_binding (((x), (l), (dd)))))
end
| uu____3059 -> begin
(Prims.raise (FStar_Errors.Error ((((Prims.strcat "Duplicate top-level names " l.FStar_Ident.str)), ((FStar_Ident.range_of_lid l))))))
end))))


let push_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env s -> (

let err = (fun l -> (

let sopt = (FStar_Util.smap_try_find (sigmap env) l.FStar_Ident.str)
in (

let r = (match (sopt) with
| Some (se, uu____3078) -> begin
(

let uu____3081 = (FStar_Util.find_opt (FStar_Ident.lid_equals l) (FStar_Syntax_Util.lids_of_sigelt se))
in (match (uu____3081) with
| Some (l) -> begin
(FStar_All.pipe_left FStar_Range.string_of_range (FStar_Ident.range_of_lid l))
end
| None -> begin
"<unknown>"
end))
end
| None -> begin
"<unknown>"
end)
in (Prims.raise (FStar_Errors.Error ((let _0_344 = (FStar_Util.format2 "Duplicate top-level names [%s]; previously declared at %s" (FStar_Ident.text_of_lid l) r)
in ((_0_344), ((FStar_Ident.range_of_lid l))))))))))
in (

let globals = (FStar_Util.mk_ref env.scope_mods)
in (

let env = (

let uu____3092 = (match (s) with
| FStar_Syntax_Syntax.Sig_let (uu____3097) -> begin
((false), (true))
end
| FStar_Syntax_Syntax.Sig_bundle (uu____3106) -> begin
((true), (true))
end
| uu____3114 -> begin
((false), (false))
end)
in (match (uu____3092) with
| (any_val, exclude_if) -> begin
(

let lids = (FStar_Syntax_Util.lids_of_sigelt s)
in (

let uu____3119 = (FStar_Util.find_map lids (fun l -> (

let uu____3122 = (not ((unique any_val exclude_if env l)))
in (match (uu____3122) with
| true -> begin
Some (l)
end
| uu____3124 -> begin
None
end))))
in (match (uu____3119) with
| Some (l) when (not ((FStar_Options.interactive ()))) -> begin
(err l)
end
| uu____3126 -> begin
((extract_record env globals s);
(

let uu___176_3131 = env
in {curmodule = uu___176_3131.curmodule; curmonad = uu___176_3131.curmonad; modules = uu___176_3131.modules; scope_mods = uu___176_3131.scope_mods; exported_ids = uu___176_3131.exported_ids; trans_exported_ids = uu___176_3131.trans_exported_ids; includes = uu___176_3131.includes; sigaccum = (s)::env.sigaccum; sigmap = uu___176_3131.sigmap; iface = uu___176_3131.iface; admitted_iface = uu___176_3131.admitted_iface; expect_typ = uu___176_3131.expect_typ});
)
end)))
end))
in (

let env = (

let uu___177_3133 = env
in (let _0_345 = (FStar_ST.read globals)
in {curmodule = uu___177_3133.curmodule; curmonad = uu___177_3133.curmonad; modules = uu___177_3133.modules; scope_mods = _0_345; exported_ids = uu___177_3133.exported_ids; trans_exported_ids = uu___177_3133.trans_exported_ids; includes = uu___177_3133.includes; sigaccum = uu___177_3133.sigaccum; sigmap = uu___177_3133.sigmap; iface = uu___177_3133.iface; admitted_iface = uu___177_3133.admitted_iface; expect_typ = uu___177_3133.expect_typ}))
in (

let uu____3137 = (match (s) with
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____3151, uu____3152, uu____3153) -> begin
(let _0_346 = (FStar_List.map (fun se -> (((FStar_Syntax_Util.lids_of_sigelt se)), (se))) ses)
in ((env), (_0_346)))
end
| uu____3169 -> begin
((env), (((((FStar_Syntax_Util.lids_of_sigelt s)), (s)))::[]))
end)
in (match (uu____3137) with
| (env, lss) -> begin
((FStar_All.pipe_right lss (FStar_List.iter (fun uu____3199 -> (match (uu____3199) with
| (lids, se) -> begin
(FStar_All.pipe_right lids (FStar_List.iter (fun lid -> ((let _0_348 = (let _0_347 = (FStar_ST.read globals)
in (Top_level_def (lid.FStar_Ident.ident))::_0_347)
in (FStar_ST.write globals _0_348));
(match (()) with
| () -> begin
(

let modul = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns).FStar_Ident.str
in ((

let uu____3218 = (get_exported_id_set env modul)
in (match (uu____3218) with
| Some (f) -> begin
(

let my_exported_ids = (f Exported_id_term_type)
in (let _0_350 = (let _0_349 = (FStar_ST.read my_exported_ids)
in (FStar_Util.set_add lid.FStar_Ident.ident.FStar_Ident.idText _0_349))
in (FStar_ST.write my_exported_ids _0_350)))
end
| None -> begin
()
end));
(match (()) with
| () -> begin
(FStar_Util.smap_add (sigmap env) lid.FStar_Ident.str ((se), ((env.iface && (not (env.admitted_iface))))))
end);
))
end);
))))
end))));
(

let env = (

let uu___178_3243 = env
in (let _0_351 = (FStar_ST.read globals)
in {curmodule = uu___178_3243.curmodule; curmonad = uu___178_3243.curmonad; modules = uu___178_3243.modules; scope_mods = _0_351; exported_ids = uu___178_3243.exported_ids; trans_exported_ids = uu___178_3243.trans_exported_ids; includes = uu___178_3243.includes; sigaccum = uu___178_3243.sigaccum; sigmap = uu___178_3243.sigmap; iface = uu___178_3243.iface; admitted_iface = uu___178_3243.admitted_iface; expect_typ = uu___178_3243.expect_typ}))
in env);
)
end)))))))


let push_namespace : env  ->  FStar_Ident.lident  ->  env = (fun env ns -> (

let uu____3253 = (

let uu____3256 = (resolve_module_name env ns false)
in (match (uu____3256) with
| None -> begin
(

let modules = env.modules
in (

let uu____3264 = (FStar_All.pipe_right modules (FStar_Util.for_some (fun uu____3270 -> (match (uu____3270) with
| (m, uu____3274) -> begin
(FStar_Util.starts_with (Prims.strcat (FStar_Ident.text_of_lid m) ".") (Prims.strcat (FStar_Ident.text_of_lid ns) "."))
end))))
in (match (uu____3264) with
| true -> begin
((ns), (Open_namespace))
end
| uu____3277 -> begin
(Prims.raise (FStar_Errors.Error ((let _0_352 = (FStar_Util.format1 "Namespace %s cannot be found" (FStar_Ident.text_of_lid ns))
in ((_0_352), ((FStar_Ident.range_of_lid ns)))))))
end)))
end
| Some (ns') -> begin
((ns'), (Open_module))
end))
in (match (uu____3253) with
| (ns', kd) -> begin
(push_scope_mod env (Open_module_or_namespace (((ns'), (kd)))))
end)))


let push_include : env  ->  FStar_Ident.lident  ->  env = (fun env ns -> (

let uu____3289 = (resolve_module_name env ns false)
in (match (uu____3289) with
| Some (ns) -> begin
(

let env = (push_scope_mod env (Open_module_or_namespace (((ns), (Open_module)))))
in (

let curmod = (current_module env).FStar_Ident.str
in ((

let uu____3295 = (FStar_Util.smap_try_find env.includes curmod)
in (match (uu____3295) with
| None -> begin
()
end
| Some (incl) -> begin
(let _0_354 = (let _0_353 = (FStar_ST.read incl)
in (ns)::_0_353)
in (FStar_ST.write incl _0_354))
end));
(match (()) with
| () -> begin
(

let uu____3314 = (get_trans_exported_id_set env ns.FStar_Ident.str)
in (match (uu____3314) with
| Some (ns_trans_exports) -> begin
((

let uu____3327 = (let _0_356 = (get_exported_id_set env curmod)
in (let _0_355 = (get_trans_exported_id_set env curmod)
in ((_0_356), (_0_355))))
in (match (uu____3327) with
| (Some (cur_exports), Some (cur_trans_exports)) -> begin
(

let update_exports = (fun k -> (

let ns_ex = (FStar_ST.read (ns_trans_exports k))
in (

let ex = (cur_exports k)
in ((let _0_358 = (let _0_357 = (FStar_ST.read ex)
in (FStar_Util.set_difference _0_357 ns_ex))
in (FStar_ST.write ex _0_358));
(match (()) with
| () -> begin
(

let trans_ex = (cur_trans_exports k)
in (

let _0_360 = (let _0_359 = (FStar_ST.read ex)
in (FStar_Util.set_union _0_359 ns_ex))
in (FStar_ST.write trans_ex _0_360)))
end);
))))
in (FStar_List.iter update_exports all_exported_id_kinds))
end
| uu____3391 -> begin
()
end));
(match (()) with
| () -> begin
env
end);
)
end
| None -> begin
(Prims.raise (FStar_Errors.Error ((let _0_361 = (FStar_Util.format1 "include: Module %s was not prepared" ns.FStar_Ident.str)
in ((_0_361), ((FStar_Ident.range_of_lid ns)))))))
end))
end);
)))
end
| uu____3405 -> begin
(Prims.raise (FStar_Errors.Error ((let _0_362 = (FStar_Util.format1 "include: Module %s cannot be found" ns.FStar_Ident.str)
in ((_0_362), ((FStar_Ident.range_of_lid ns)))))))
end)))


let push_module_abbrev : env  ->  FStar_Ident.ident  ->  FStar_Ident.lident  ->  env = (fun env x l -> (

let uu____3416 = (module_is_defined env l)
in (match (uu____3416) with
| true -> begin
(push_scope_mod env (Module_abbrev (((x), (l)))))
end
| uu____3417 -> begin
(Prims.raise (FStar_Errors.Error ((let _0_363 = (FStar_Util.format1 "Module %s cannot be found" (FStar_Ident.text_of_lid l))
in ((_0_363), ((FStar_Ident.range_of_lid l)))))))
end)))


let check_admits : env  ->  Prims.unit = (fun env -> (FStar_All.pipe_right env.sigaccum (FStar_List.iter (fun se -> (match (se) with
| FStar_Syntax_Syntax.Sig_declare_typ (l, u, t, quals, r) -> begin
(

let uu____3429 = (try_lookup_lid env l)
in (match (uu____3429) with
| None -> begin
((

let uu____3436 = (not ((FStar_Options.interactive ())))
in (match (uu____3436) with
| true -> begin
(FStar_Util.print_string (let _0_365 = (FStar_Range.string_of_range (FStar_Ident.range_of_lid l))
in (let _0_364 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format2 "%s: Warning: Admitting %s without a definition\n" _0_365 _0_364))))
end
| uu____3437 -> begin
()
end));
(FStar_Util.smap_add (sigmap env) l.FStar_Ident.str ((FStar_Syntax_Syntax.Sig_declare_typ (((l), (u), (t), ((FStar_Syntax_Syntax.Assumption)::quals), (r)))), (false)));
)
end
| Some (uu____3441) -> begin
()
end))
end
| uu____3446 -> begin
()
end)))))


let finish : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env modul -> ((FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations (FStar_List.iter (fun uu___171_3454 -> (match (uu___171_3454) with
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, uu____3457, uu____3458) -> begin
(match (((FStar_List.contains FStar_Syntax_Syntax.Private quals) || (FStar_List.contains FStar_Syntax_Syntax.Abstract quals))) with
| true -> begin
(FStar_All.pipe_right ses (FStar_List.iter (fun uu___170_3466 -> (match (uu___170_3466) with
| FStar_Syntax_Syntax.Sig_datacon (lid, uu____3468, uu____3469, uu____3470, uu____3471, uu____3472, uu____3473, uu____3474) -> begin
(FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str)
end
| uu____3481 -> begin
()
end))))
end
| uu____3482 -> begin
()
end)
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____3484, uu____3485, quals, uu____3487) -> begin
(match ((FStar_List.contains FStar_Syntax_Syntax.Private quals)) with
| true -> begin
(FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str)
end
| uu____3492 -> begin
()
end)
end
| FStar_Syntax_Syntax.Sig_let ((uu____3493, lbs), r, uu____3496, quals, uu____3498) -> begin
((match (((FStar_List.contains FStar_Syntax_Syntax.Private quals) || (FStar_List.contains FStar_Syntax_Syntax.Abstract quals))) with
| true -> begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (let _0_366 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname).FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str
in (FStar_Util.smap_remove (sigmap env) _0_366)))))
end
| uu____3519 -> begin
()
end);
(match (((FStar_List.contains FStar_Syntax_Syntax.Abstract quals) && (not ((FStar_List.contains FStar_Syntax_Syntax.Private quals))))) with
| true -> begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (

let lid = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname).FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let decl = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), ((FStar_Syntax_Syntax.Assumption)::quals), (r)))
in (FStar_Util.smap_add (sigmap env) lid.FStar_Ident.str ((decl), (false))))))))
end
| uu____3534 -> begin
()
end);
)
end
| uu____3535 -> begin
()
end))));
(

let curmod = (current_module env).FStar_Ident.str
in ((

let uu____3538 = (let _0_368 = (get_exported_id_set env curmod)
in (let _0_367 = (get_trans_exported_id_set env curmod)
in ((_0_368), (_0_367))))
in (match (uu____3538) with
| (Some (cur_ex), Some (cur_trans_ex)) -> begin
(

let update_exports = (fun eikind -> (

let cur_ex_set = (FStar_ST.read (cur_ex eikind))
in (

let cur_trans_ex_set_ref = (cur_trans_ex eikind)
in (let _0_370 = (let _0_369 = (FStar_ST.read cur_trans_ex_set_ref)
in (FStar_Util.set_union cur_ex_set _0_369))
in (FStar_ST.write cur_trans_ex_set_ref _0_370)))))
in (FStar_List.iter update_exports all_exported_id_kinds))
end
| uu____3593 -> begin
()
end));
(match (()) with
| () -> begin
((filter_record_cache ());
(match (()) with
| () -> begin
(

let uu___179_3605 = env
in {curmodule = None; curmonad = uu___179_3605.curmonad; modules = (((modul.FStar_Syntax_Syntax.name), (modul)))::env.modules; scope_mods = []; exported_ids = uu___179_3605.exported_ids; trans_exported_ids = uu___179_3605.trans_exported_ids; includes = uu___179_3605.includes; sigaccum = []; sigmap = uu___179_3605.sigmap; iface = uu___179_3605.iface; admitted_iface = uu___179_3605.admitted_iface; expect_typ = uu___179_3605.expect_typ})
end);
)
end);
));
))

type env_stack_ops =
{push : env  ->  env; mark : env  ->  env; reset_mark : env  ->  env; commit_mark : env  ->  env; pop : env  ->  env}


let stack_ops : env_stack_ops = (

let stack = (FStar_Util.mk_ref [])
in (

let push = (fun env -> ((push_record_cache ());
(let _0_372 = (let _0_371 = (FStar_ST.read stack)
in (env)::_0_371)
in (FStar_ST.write stack _0_372));
(let _0_373 = (FStar_Util.string_of_int (FStar_List.length (FStar_ST.read stack)))
in (FStar_Util.print1 "DS/Pushed; size of stack is now: %s\n" _0_373));
(

let uu___180_3702 = env
in (let _0_374 = (FStar_Util.smap_copy (sigmap env))
in {curmodule = uu___180_3702.curmodule; curmonad = uu___180_3702.curmonad; modules = uu___180_3702.modules; scope_mods = uu___180_3702.scope_mods; exported_ids = uu___180_3702.exported_ids; trans_exported_ids = uu___180_3702.trans_exported_ids; includes = uu___180_3702.includes; sigaccum = uu___180_3702.sigaccum; sigmap = _0_374; iface = uu___180_3702.iface; admitted_iface = uu___180_3702.admitted_iface; expect_typ = uu___180_3702.expect_typ}));
))
in (

let pop = (fun env -> (

let uu____3709 = (FStar_ST.read stack)
in (match (uu____3709) with
| (env)::tl -> begin
((pop_record_cache ());
(FStar_ST.write stack tl);
(let _0_375 = (FStar_Util.string_of_int (FStar_List.length (FStar_ST.read stack)))
in (FStar_Util.print1 "DS/Popped; size of stack is now: %s\n" _0_375));
env;
)
end
| uu____3729 -> begin
(failwith "Impossible: Too many pops")
end)))
in (

let commit_mark = (fun env -> ((commit_record_cache ());
(

let uu____3736 = (FStar_ST.read stack)
in (match (uu____3736) with
| (uu____3741)::tl -> begin
((FStar_ST.write stack tl);
env;
)
end
| uu____3748 -> begin
(failwith "Impossible: Too many pops")
end));
))
in {push = push; mark = push; reset_mark = pop; commit_mark = commit_mark; pop = pop}))))


let push : env  ->  env = (fun env -> (stack_ops.push env))


let mark : env  ->  env = (fun env -> (stack_ops.mark env))


let reset_mark : env  ->  env = (fun env -> (stack_ops.reset_mark env))


let commit_mark : env  ->  env = (fun env -> (stack_ops.commit_mark env))


let pop : env  ->  env = (fun env -> (stack_ops.pop env))


let export_interface : FStar_Ident.lident  ->  env  ->  env = (fun m env -> (

let sigelt_in_m = (fun se -> (match ((FStar_Syntax_Util.lids_of_sigelt se)) with
| (l)::uu____3776 -> begin
(l.FStar_Ident.nsstr = m.FStar_Ident.str)
end
| uu____3778 -> begin
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
in ((FStar_All.pipe_right keys (FStar_List.iter (fun k -> (

let uu____3796 = (FStar_Util.smap_try_find sm' k)
in (match (uu____3796) with
| Some (se, true) when (sigelt_in_m se) -> begin
((FStar_Util.smap_remove sm' k);
(

let se = (match (se) with
| FStar_Syntax_Syntax.Sig_declare_typ (l, u, t, q, r) -> begin
FStar_Syntax_Syntax.Sig_declare_typ (((l), (u), (t), ((FStar_Syntax_Syntax.Assumption)::q), (r)))
end
| uu____3817 -> begin
se
end)
in (FStar_Util.smap_add sm' k ((se), (false))));
)
end
| uu____3820 -> begin
()
end)))));
env;
)))))))


let finish_module_or_interface : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env modul -> ((match ((not (modul.FStar_Syntax_Syntax.is_interface))) with
| true -> begin
(check_admits env)
end
| uu____3831 -> begin
()
end);
(finish env modul);
))


let prepare_module_or_interface : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  (env * Prims.bool) = (fun intf admitted env mname -> (

let prep = (fun env -> (

let open_ns = (match ((FStar_Ident.lid_equals mname FStar_Syntax_Const.prims_lid)) with
| true -> begin
[]
end
| uu____3853 -> begin
(match ((FStar_Util.starts_with "FStar." (FStar_Ident.text_of_lid mname))) with
| true -> begin
(FStar_Syntax_Const.prims_lid)::(FStar_Syntax_Const.fstar_ns_lid)::[]
end
| uu____3855 -> begin
(FStar_Syntax_Const.prims_lid)::(FStar_Syntax_Const.st_lid)::(FStar_Syntax_Const.all_lid)::(FStar_Syntax_Const.fstar_ns_lid)::[]
end)
end)
in (

let open_ns = (match (((FStar_List.length mname.FStar_Ident.ns) <> (Prims.parse_int "0"))) with
| true -> begin
(

let ns = (FStar_Ident.lid_of_ids mname.FStar_Ident.ns)
in (ns)::open_ns)
end
| uu____3862 -> begin
open_ns
end)
in ((let _0_376 = (exported_id_set_new ())
in (FStar_Util.smap_add env.exported_ids mname.FStar_Ident.str _0_376));
(match (()) with
| () -> begin
((let _0_377 = (exported_id_set_new ())
in (FStar_Util.smap_add env.trans_exported_ids mname.FStar_Ident.str _0_377));
(match (()) with
| () -> begin
((let _0_378 = (FStar_Util.mk_ref [])
in (FStar_Util.smap_add env.includes mname.FStar_Ident.str _0_378));
(match (()) with
| () -> begin
(

let uu___181_3875 = env
in (let _0_379 = (FStar_List.map (fun lid -> Open_module_or_namespace (((lid), (Open_namespace)))) open_ns)
in {curmodule = Some (mname); curmonad = uu___181_3875.curmonad; modules = uu___181_3875.modules; scope_mods = _0_379; exported_ids = uu___181_3875.exported_ids; trans_exported_ids = uu___181_3875.trans_exported_ids; includes = uu___181_3875.includes; sigaccum = uu___181_3875.sigaccum; sigmap = env.sigmap; iface = intf; admitted_iface = admitted; expect_typ = uu___181_3875.expect_typ}))
end);
)
end);
)
end);
))))
in (

let uu____3877 = (FStar_All.pipe_right env.modules (FStar_Util.find_opt (fun uu____3889 -> (match (uu____3889) with
| (l, uu____3893) -> begin
(FStar_Ident.lid_equals l mname)
end))))
in (match (uu____3877) with
| None -> begin
(let _0_380 = (prep env)
in ((_0_380), (false)))
end
| Some (uu____3898, m) -> begin
((

let uu____3903 = ((not ((FStar_Options.interactive ()))) && ((not (m.FStar_Syntax_Syntax.is_interface)) || intf))
in (match (uu____3903) with
| true -> begin
(Prims.raise (FStar_Errors.Error ((let _0_381 = (FStar_Util.format1 "Duplicate module or interface name: %s" mname.FStar_Ident.str)
in ((_0_381), ((FStar_Ident.range_of_lid mname)))))))
end
| uu____3904 -> begin
()
end));
(let _0_382 = (prep (push env))
in ((_0_382), (true)));
)
end))))


let enter_monad_scope : env  ->  FStar_Ident.ident  ->  env = (fun env mname -> (match (env.curmonad) with
| Some (mname') -> begin
(Prims.raise (FStar_Errors.Error ((((Prims.strcat "Trying to define monad " (Prims.strcat mname.FStar_Ident.idText (Prims.strcat ", but already in monad scope " mname'.FStar_Ident.idText)))), (mname.FStar_Ident.idRange)))))
end
| None -> begin
(

let uu___182_3912 = env
in {curmodule = uu___182_3912.curmodule; curmonad = Some (mname); modules = uu___182_3912.modules; scope_mods = uu___182_3912.scope_mods; exported_ids = uu___182_3912.exported_ids; trans_exported_ids = uu___182_3912.trans_exported_ids; includes = uu___182_3912.includes; sigaccum = uu___182_3912.sigaccum; sigmap = uu___182_3912.sigmap; iface = uu___182_3912.iface; admitted_iface = uu___182_3912.admitted_iface; expect_typ = uu___182_3912.expect_typ})
end))


let fail_or = (fun env lookup lid -> (

let uu____3937 = (lookup lid)
in (match (uu____3937) with
| None -> begin
(

let opened_modules = (FStar_List.map (fun uu____3943 -> (match (uu____3943) with
| (lid, uu____3947) -> begin
(FStar_Ident.text_of_lid lid)
end)) env.modules)
in (

let msg = (FStar_Util.format1 "Identifier not found: [%s]" (FStar_Ident.text_of_lid lid))
in (

let msg = (match (((FStar_List.length lid.FStar_Ident.ns) = (Prims.parse_int "0"))) with
| true -> begin
msg
end
| uu____3952 -> begin
(

let modul = (let _0_383 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in (FStar_Ident.set_lid_range _0_383 (FStar_Ident.range_of_lid lid)))
in (

let uu____3954 = (resolve_module_name env modul true)
in (match (uu____3954) with
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
end)))
end)
in (Prims.raise (FStar_Errors.Error (((msg), ((FStar_Ident.range_of_lid lid)))))))))
end
| Some (r) -> begin
r
end)))


let fail_or2 = (fun lookup id -> (

let uu____3981 = (lookup id)
in (match (uu____3981) with
| None -> begin
(Prims.raise (FStar_Errors.Error ((((Prims.strcat "Identifier not found [" (Prims.strcat id.FStar_Ident.idText "]"))), (id.FStar_Ident.idRange)))))
end
| Some (r) -> begin
r
end)))




