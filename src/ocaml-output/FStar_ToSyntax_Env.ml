
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


let transitive_exported_ids : env  ->  FStar_Ident.lident  ->  Prims.string Prims.list = (fun env lid -> (

let module_name = (FStar_Ident.string_of_lid lid)
in (

let uu____357 = (FStar_Util.smap_try_find env.trans_exported_ids module_name)
in (match (uu____357) with
| None -> begin
[]
end
| Some (exported_id_set) -> begin
(

let uu____361 = (

let uu____362 = (exported_id_set Exported_id_term_type)
in (FStar_ST.read uu____362))
in (FStar_All.pipe_right uu____361 FStar_Util.set_elements))
end))))


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
(

let uu____388 = (current_module env)
in (qual uu____388 id))
end
| Some (monad) -> begin
(

let uu____390 = (

let uu____391 = (current_module env)
in (qual uu____391 monad))
in (FStar_Syntax_Util.mk_field_projector_name_from_ident uu____390 id))
end))


let new_sigmap = (fun uu____399 -> (FStar_Util.smap_create (Prims.parse_int "100")))


let empty_env : Prims.unit  ->  env = (fun uu____402 -> (

let uu____403 = (new_sigmap ())
in (

let uu____405 = (new_sigmap ())
in (

let uu____407 = (new_sigmap ())
in (

let uu____413 = (new_sigmap ())
in {curmodule = None; curmonad = None; modules = []; scope_mods = []; exported_ids = uu____403; trans_exported_ids = uu____405; includes = uu____407; sigaccum = []; sigmap = uu____413; iface = false; admitted_iface = false; expect_typ = false})))))


let sigmap : env  ->  (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap = (fun env -> env.sigmap)


let has_all_in_scope : env  ->  Prims.bool = (fun env -> (FStar_List.existsb (fun uu____432 -> (match (uu____432) with
| (m, uu____436) -> begin
(FStar_Ident.lid_equals m FStar_Syntax_Const.all_lid)
end)) env.modules))


let set_bv_range : FStar_Syntax_Syntax.bv  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.bv = (fun bv r -> (

let id = (

let uu___166_444 = bv.FStar_Syntax_Syntax.ppname
in {FStar_Ident.idText = uu___166_444.FStar_Ident.idText; FStar_Ident.idRange = r})
in (

let uu___167_445 = bv
in {FStar_Syntax_Syntax.ppname = id; FStar_Syntax_Syntax.index = uu___167_445.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu___167_445.FStar_Syntax_Syntax.sort})))


let bv_to_name : FStar_Syntax_Syntax.bv  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.term = (fun bv r -> (FStar_Syntax_Syntax.bv_to_name (set_bv_range bv r)))


let unmangleMap : (Prims.string * Prims.string * FStar_Syntax_Syntax.delta_depth * FStar_Syntax_Syntax.fv_qual Prims.option) Prims.list = ((("op_ColonColon"), ("Cons"), (FStar_Syntax_Syntax.Delta_constant), (Some (FStar_Syntax_Syntax.Data_ctor))))::((("not"), ("op_Negation"), (FStar_Syntax_Syntax.Delta_equational), (None)))::[]


let unmangleOpName : FStar_Ident.ident  ->  (FStar_Syntax_Syntax.term * Prims.bool) Prims.option = (fun id -> (

let t = (FStar_Util.find_map unmangleMap (fun uu____491 -> (match (uu____491) with
| (x, y, dd, dq) -> begin
(match ((id.FStar_Ident.idText = x)) with
| true -> begin
(

let uu____505 = (

let uu____506 = (FStar_Ident.lid_of_path (("Prims")::(y)::[]) id.FStar_Ident.idRange)
in (FStar_Syntax_Syntax.fvar uu____506 dd dq))
in Some (uu____505))
end
| uu____507 -> begin
None
end)
end)))
in (match (t) with
| Some (v1) -> begin
Some (((v1), (false)))
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
| uu____536 -> begin
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
| uu____560 -> begin
false
end))


let uu___is_Cont_ignore = (fun projectee -> (match (projectee) with
| Cont_ignore -> begin
true
end
| uu____571 -> begin
false
end))


let option_of_cont = (fun k_ignore uu___139_590 -> (match (uu___139_590) with
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

let find1 = (FStar_Util.find_map record.fields (fun uu____635 -> (match (uu____635) with
| (f, uu____640) -> begin
(match ((id.FStar_Ident.idText = f.FStar_Ident.idText)) with
| true -> begin
Some (record)
end
| uu____642 -> begin
None
end)
end)))
in (match (find1) with
| Some (r) -> begin
(cont r)
end
| None -> begin
Cont_ignore
end)))
end
| uu____645 -> begin
Cont_ignore
end)))


let get_exported_id_set : env  ->  Prims.string  ->  (exported_id_kind  ->  string_set FStar_ST.ref) Prims.option = (fun e mname -> (FStar_Util.smap_try_find e.exported_ids mname))


let get_trans_exported_id_set : env  ->  Prims.string  ->  (exported_id_kind  ->  string_set FStar_ST.ref) Prims.option = (fun e mname -> (FStar_Util.smap_try_find e.trans_exported_ids mname))


let string_of_exported_id_kind : exported_id_kind  ->  Prims.string = (fun uu___140_676 -> (match (uu___140_676) with
| Exported_id_field -> begin
"field"
end
| Exported_id_term_type -> begin
"term/type"
end))


let find_in_module_with_includes = (fun eikind find_in_module find_in_module_default env ns id -> (

let idstr = id.FStar_Ident.idText
in (

let rec aux = (fun uu___141_725 -> (match (uu___141_725) with
| [] -> begin
find_in_module_default
end
| (modul)::q -> begin
(

let mname = modul.FStar_Ident.str
in (

let not_shadowed = (

let uu____733 = (get_exported_id_set env mname)
in (match (uu____733) with
| None -> begin
true
end
| Some (mex) -> begin
(

let mexports = (

let uu____749 = (mex eikind)
in (FStar_ST.read uu____749))
in (FStar_Util.set_mem idstr mexports))
end))
in (

let mincludes = (

let uu____756 = (FStar_Util.smap_try_find env.includes mname)
in (match (uu____756) with
| None -> begin
[]
end
| Some (minc) -> begin
(FStar_ST.read minc)
end))
in (

let look_into = (match (not_shadowed) with
| true -> begin
(

let uu____776 = (qual modul id)
in (find_in_module uu____776))
end
| uu____777 -> begin
Cont_ignore
end)
in (match (look_into) with
| Cont_ignore -> begin
(aux (FStar_List.append mincludes q))
end
| uu____779 -> begin
look_into
end)))))
end))
in (aux ((ns)::[])))))


let is_exported_id_field : exported_id_kind  ->  Prims.bool = (fun uu___142_783 -> (match (uu___142_783) with
| Exported_id_field -> begin
true
end
| uu____784 -> begin
false
end))


let try_lookup_id'' = (fun env id eikind k_local_binding k_rec_binding k_record find_in_module lookup_default_id -> (

let check_local_binding_id = (fun uu___143_873 -> (match (uu___143_873) with
| (id', uu____875, uu____876) -> begin
(id'.FStar_Ident.idText = id.FStar_Ident.idText)
end))
in (

let check_rec_binding_id = (fun uu___144_880 -> (match (uu___144_880) with
| (id', uu____882, uu____883) -> begin
(id'.FStar_Ident.idText = id.FStar_Ident.idText)
end))
in (

let curmod_ns = (

let uu____886 = (current_module env)
in (FStar_Ident.ids_of_lid uu____886))
in (

let proc = (fun uu___145_891 -> (match (uu___145_891) with
| Local_binding (l) when (check_local_binding_id l) -> begin
(k_local_binding l)
end
| Rec_binding (r) when (check_rec_binding_id r) -> begin
(k_rec_binding r)
end
| Open_module_or_namespace (ns, uu____896) -> begin
(find_in_module_with_includes eikind find_in_module Cont_ignore env ns id)
end
| Top_level_def (id') when (id'.FStar_Ident.idText = id.FStar_Ident.idText) -> begin
(lookup_default_id Cont_ignore id)
end
| Record_or_dc (r) when (is_exported_id_field eikind) -> begin
(

let uu____899 = (FStar_Ident.lid_of_ids curmod_ns)
in (find_in_module_with_includes Exported_id_field (fun lid -> (

let id1 = lid.FStar_Ident.ident
in (find_in_record lid.FStar_Ident.ns id1 r k_record))) Cont_ignore env uu____899 id))
end
| uu____902 -> begin
Cont_ignore
end))
in (

let rec aux = (fun uu___146_908 -> (match (uu___146_908) with
| (a)::q -> begin
(

let uu____914 = (proc a)
in (option_of_cont (fun uu____916 -> (aux q)) uu____914))
end
| [] -> begin
(

let uu____917 = (lookup_default_id Cont_fail id)
in (option_of_cont (fun uu____919 -> None) uu____917))
end))
in (aux env.scope_mods)))))))


let found_local_binding = (fun r uu____938 -> (match (uu____938) with
| (id', x, mut) -> begin
(

let uu____945 = (bv_to_name x r)
in ((uu____945), (mut)))
end))


let find_in_module = (fun env lid k_global_def k_not_found -> (

let uu____982 = (FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str)
in (match (uu____982) with
| Some (sb) -> begin
(k_global_def lid sb)
end
| None -> begin
k_not_found
end)))


let try_lookup_id : env  ->  FStar_Ident.ident  ->  (FStar_Syntax_Syntax.term * Prims.bool) Prims.option = (fun env id -> (

let uu____1004 = (unmangleOpName id)
in (match (uu____1004) with
| Some (f) -> begin
Some (f)
end
| uu____1018 -> begin
(try_lookup_id'' env id Exported_id_term_type (fun r -> (

let uu____1025 = (found_local_binding id.FStar_Ident.idRange r)
in Cont_ok (uu____1025))) (fun uu____1030 -> Cont_fail) (fun uu____1033 -> Cont_ignore) (fun i -> (find_in_module env i (fun uu____1040 uu____1041 -> Cont_fail) Cont_ignore)) (fun uu____1048 uu____1049 -> Cont_fail))
end)))


let lookup_default_id = (fun env id k_global_def k_not_found -> (

let find_in_monad = (match (env.curmonad) with
| Some (uu____1101) -> begin
(

let lid = (qualify env id)
in (

let uu____1103 = (FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str)
in (match (uu____1103) with
| Some (r) -> begin
(

let uu____1116 = (k_global_def lid r)
in Some (uu____1116))
end
| None -> begin
None
end)))
end
| None -> begin
None
end)
in (match (find_in_monad) with
| Some (v1) -> begin
v1
end
| None -> begin
(

let lid = (

let uu____1129 = (current_module env)
in (qual uu____1129 id))
in (find_in_module env lid k_global_def k_not_found))
end)))


let module_is_defined : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> ((match (env.curmodule) with
| None -> begin
false
end
| Some (m) -> begin
(

let uu____1138 = (current_module env)
in (FStar_Ident.lid_equals lid uu____1138))
end) || (FStar_List.existsb (fun x -> (FStar_Ident.lid_equals lid (Prims.fst x))) env.modules)))


let resolve_module_name : env  ->  FStar_Ident.lident  ->  Prims.bool  ->  FStar_Ident.lident Prims.option = (fun env lid honor_ns -> (

let nslen = (FStar_List.length lid.FStar_Ident.ns)
in (

let rec aux = (fun uu___147_1162 -> (match (uu___147_1162) with
| [] -> begin
(

let uu____1165 = (module_is_defined env lid)
in (match (uu____1165) with
| true -> begin
Some (lid)
end
| uu____1167 -> begin
None
end))
end
| (Open_module_or_namespace (ns, Open_namespace))::q when honor_ns -> begin
(

let new_lid = (

let uu____1172 = (

let uu____1174 = (FStar_Ident.path_of_lid ns)
in (

let uu____1176 = (FStar_Ident.path_of_lid lid)
in (FStar_List.append uu____1174 uu____1176)))
in (FStar_Ident.lid_of_path uu____1172 (FStar_Ident.range_of_lid lid)))
in (

let uu____1178 = (module_is_defined env new_lid)
in (match (uu____1178) with
| true -> begin
Some (new_lid)
end
| uu____1180 -> begin
(aux q)
end)))
end
| (Module_abbrev (name, modul))::uu____1183 when ((nslen = (Prims.parse_int "0")) && (name.FStar_Ident.idText = lid.FStar_Ident.ident.FStar_Ident.idText)) -> begin
Some (modul)
end
| (uu____1187)::q -> begin
(aux q)
end))
in (aux env.scope_mods))))


let namespace_is_open : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (FStar_List.existsb (fun uu___148_1196 -> (match (uu___148_1196) with
| Open_module_or_namespace (ns, Open_namespace) -> begin
(FStar_Ident.lid_equals lid ns)
end
| uu____1198 -> begin
false
end)) env.scope_mods))


let shorten_module_path : env  ->  FStar_Ident.ident Prims.list  ->  Prims.bool  ->  (FStar_Ident.ident Prims.list * FStar_Ident.ident Prims.list) = (fun env ids is_full_path -> (

let rec aux = (fun revns id -> (

let lid = (FStar_Ident.lid_of_ns_and_id (FStar_List.rev revns) id)
in (match ((namespace_is_open env lid)) with
| true -> begin
Some ((((FStar_List.rev ((id)::revns))), ([])))
end
| uu____1240 -> begin
(match (revns) with
| [] -> begin
None
end
| (ns_last_id)::rev_ns_prefix -> begin
(

let uu____1253 = (aux rev_ns_prefix ns_last_id)
in (FStar_All.pipe_right uu____1253 (FStar_Util.map_option (fun uu____1277 -> (match (uu____1277) with
| (stripped_ids, rev_kept_ids) -> begin
((stripped_ids), ((id)::rev_kept_ids))
end)))))
end)
end)))
in (

let uu____1294 = (is_full_path && (

let uu____1295 = (FStar_Ident.lid_of_ids ids)
in (module_is_defined env uu____1295)))
in (match (uu____1294) with
| true -> begin
((ids), ([]))
end
| uu____1302 -> begin
(match ((FStar_List.rev ids)) with
| [] -> begin
(([]), ([]))
end
| (ns_last_id)::ns_rev_prefix -> begin
(

let uu____1312 = (aux ns_rev_prefix ns_last_id)
in (match (uu____1312) with
| None -> begin
(([]), (ids))
end
| Some (stripped_ids, rev_kept_ids) -> begin
((stripped_ids), ((FStar_List.rev rev_kept_ids)))
end))
end)
end))))


let resolve_in_open_namespaces'' = (fun env lid eikind k_local_binding k_rec_binding k_record f_module l_default -> (match (lid.FStar_Ident.ns) with
| (uu____1425)::uu____1426 -> begin
(

let uu____1428 = (

let uu____1430 = (

let uu____1431 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in (FStar_Ident.set_lid_range uu____1431 (FStar_Ident.range_of_lid lid)))
in (resolve_module_name env uu____1430 true))
in (match (uu____1428) with
| None -> begin
None
end
| Some (modul) -> begin
(

let uu____1434 = (find_in_module_with_includes eikind f_module Cont_fail env modul lid.FStar_Ident.ident)
in (option_of_cont (fun uu____1436 -> None) uu____1434))
end))
end
| [] -> begin
(try_lookup_id'' env lid.FStar_Ident.ident eikind k_local_binding k_rec_binding k_record f_module l_default)
end))


let cont_of_option = (fun k_none uu___149_1451 -> (match (uu___149_1451) with
| Some (v1) -> begin
Cont_ok (v1)
end
| None -> begin
k_none
end))


let resolve_in_open_namespaces' = (fun env lid k_local_binding k_rec_binding k_global_def -> (

let k_global_def' = (fun k lid1 def -> (

let uu____1530 = (k_global_def lid1 def)
in (cont_of_option k uu____1530)))
in (

let f_module = (fun lid' -> (

let k = Cont_ignore
in (find_in_module env lid' (k_global_def' k) k)))
in (

let l_default = (fun k i -> (lookup_default_id env i (k_global_def' k) k))
in (resolve_in_open_namespaces'' env lid Exported_id_term_type (fun l -> (

let uu____1551 = (k_local_binding l)
in (cont_of_option Cont_fail uu____1551))) (fun r -> (

let uu____1554 = (k_rec_binding r)
in (cont_of_option Cont_fail uu____1554))) (fun uu____1556 -> Cont_ignore) f_module l_default)))))


let fv_qual_of_se : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.fv_qual Prims.option = (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (uu____1562, uu____1563, uu____1564, l, uu____1566, quals, uu____1568) -> begin
(

let qopt = (FStar_Util.find_map quals (fun uu___150_1575 -> (match (uu___150_1575) with
| FStar_Syntax_Syntax.RecordConstructor (uu____1577, fs) -> begin
Some (FStar_Syntax_Syntax.Record_ctor (((l), (fs))))
end
| uu____1584 -> begin
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
| FStar_Syntax_Syntax.Sig_declare_typ (uu____1588, uu____1589, uu____1590, quals) -> begin
None
end
| uu____1594 -> begin
None
end))


let lb_fv : FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.fv = (fun lbs lid -> (

let uu____1603 = (FStar_Util.find_map lbs (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let uu____1607 = (FStar_Syntax_Syntax.fv_eq_lid fv lid)
in (match (uu____1607) with
| true -> begin
Some (fv)
end
| uu____1609 -> begin
None
end)))))
in (FStar_All.pipe_right uu____1603 FStar_Util.must)))


let ns_of_lid_equals : FStar_Ident.lident  ->  FStar_Ident.lident  ->  Prims.bool = (fun lid ns -> (((FStar_List.length lid.FStar_Ident.ns) = (FStar_List.length (FStar_Ident.ids_of_lid ns))) && (

let uu____1621 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in (FStar_Ident.lid_equals uu____1621 ns))))


let try_lookup_name : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  foundname Prims.option = (fun any_val exclude_interf env lid -> (

let occurrence_range = (FStar_Ident.range_of_lid lid)
in (

let k_global_def = (fun source_lid uu___154_1646 -> (match (uu___154_1646) with
| (uu____1650, true) when exclude_interf -> begin
None
end
| (se, uu____1652) -> begin
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____1654) -> begin
(

let uu____1665 = (

let uu____1666 = (

let uu____1669 = (FStar_Syntax_Syntax.fvar source_lid FStar_Syntax_Syntax.Delta_constant None)
in ((uu____1669), (false)))
in Term_name (uu____1666))
in Some (uu____1665))
end
| FStar_Syntax_Syntax.Sig_datacon (uu____1670) -> begin
(

let uu____1680 = (

let uu____1681 = (

let uu____1684 = (

let uu____1685 = (fv_qual_of_se se)
in (FStar_Syntax_Syntax.fvar source_lid FStar_Syntax_Syntax.Delta_constant uu____1685))
in ((uu____1684), (false)))
in Term_name (uu____1681))
in Some (uu____1680))
end
| FStar_Syntax_Syntax.Sig_let ((uu____1687, lbs), uu____1689, uu____1690, uu____1691) -> begin
(

let fv = (lb_fv lbs source_lid)
in (

let uu____1704 = (

let uu____1705 = (

let uu____1708 = (FStar_Syntax_Syntax.fvar source_lid fv.FStar_Syntax_Syntax.fv_delta fv.FStar_Syntax_Syntax.fv_qual)
in ((uu____1708), (false)))
in Term_name (uu____1705))
in Some (uu____1704)))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid1, uu____1710, uu____1711, quals) -> begin
(

let uu____1715 = (any_val || (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___151_1717 -> (match (uu___151_1717) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| uu____1718 -> begin
false
end)))))
in (match (uu____1715) with
| true -> begin
(

let lid2 = (FStar_Ident.set_lid_range lid1 (FStar_Ident.range_of_lid source_lid))
in (

let dd = (

let uu____1722 = ((FStar_Syntax_Util.is_primop_lid lid2) || ((ns_of_lid_equals lid2 FStar_Syntax_Const.prims_lid) && (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___152_1724 -> (match (uu___152_1724) with
| (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) -> begin
true
end
| uu____1727 -> begin
false
end))))))
in (match (uu____1722) with
| true -> begin
FStar_Syntax_Syntax.Delta_equational
end
| uu____1728 -> begin
FStar_Syntax_Syntax.Delta_constant
end))
in (

let uu____1729 = (FStar_Util.find_map quals (fun uu___153_1731 -> (match (uu___153_1731) with
| FStar_Syntax_Syntax.Reflectable (refl_monad) -> begin
Some (refl_monad)
end
| uu____1734 -> begin
None
end)))
in (match (uu____1729) with
| Some (refl_monad) -> begin
(

let refl_const = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (refl_monad)))) None occurrence_range)
in Some (Term_name (((refl_const), (false)))))
end
| uu____1750 -> begin
(

let uu____1752 = (

let uu____1753 = (

let uu____1756 = (

let uu____1757 = (fv_qual_of_se se)
in (FStar_Syntax_Syntax.fvar lid2 dd uu____1757))
in ((uu____1756), (false)))
in Term_name (uu____1753))
in Some (uu____1752))
end))))
end
| uu____1759 -> begin
None
end))
end
| (FStar_Syntax_Syntax.Sig_new_effect_for_free (ne)) | (FStar_Syntax_Syntax.Sig_new_effect (ne)) -> begin
Some (Eff_name (((se), ((FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname (FStar_Ident.range_of_lid source_lid))))))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (uu____1761) -> begin
Some (Eff_name (((se), (source_lid))))
end
| uu____1770 -> begin
None
end)
end))
in (

let k_local_binding = (fun r -> (

let uu____1782 = (

let uu____1783 = (found_local_binding (FStar_Ident.range_of_lid lid) r)
in Term_name (uu____1783))
in Some (uu____1782)))
in (

let k_rec_binding = (fun uu____1793 -> (match (uu____1793) with
| (id, l, dd) -> begin
(

let uu____1801 = (

let uu____1802 = (

let uu____1805 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range l (FStar_Ident.range_of_lid lid)) dd None)
in ((uu____1805), (false)))
in Term_name (uu____1802))
in Some (uu____1801))
end))
in (

let found_unmangled = (match (lid.FStar_Ident.ns) with
| [] -> begin
(

let uu____1809 = (unmangleOpName lid.FStar_Ident.ident)
in (match (uu____1809) with
| Some (f) -> begin
Some (Term_name (f))
end
| uu____1819 -> begin
None
end))
end
| uu____1823 -> begin
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

let uu____1843 = (try_lookup_name true exclude_interf env lid)
in (match (uu____1843) with
| Some (Eff_name (o, l)) -> begin
Some (((o), (l)))
end
| uu____1852 -> begin
None
end)))


let try_lookup_effect_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env l -> (

let uu____1863 = (try_lookup_effect_name' (not (env.iface)) env l)
in (match (uu____1863) with
| Some (o, l1) -> begin
Some (l1)
end
| uu____1872 -> begin
None
end)))


let try_lookup_effect_name_and_attributes : env  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.cflags Prims.list) Prims.option = (fun env l -> (

let uu____1886 = (try_lookup_effect_name' (not (env.iface)) env l)
in (match (uu____1886) with
| Some ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect (ne); FStar_Syntax_Syntax.sigdoc = uu____1895; FStar_Syntax_Syntax.sigrng = uu____1896}, l1) -> begin
Some (((l1), (ne.FStar_Syntax_Syntax.cattributes)))
end
| Some ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect_for_free (ne); FStar_Syntax_Syntax.sigdoc = uu____1906; FStar_Syntax_Syntax.sigrng = uu____1907}, l1) -> begin
Some (((l1), (ne.FStar_Syntax_Syntax.cattributes)))
end
| Some ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_effect_abbrev (uu____1916, uu____1917, uu____1918, uu____1919, uu____1920, cattributes); FStar_Syntax_Syntax.sigdoc = uu____1922; FStar_Syntax_Syntax.sigrng = uu____1923}, l1) -> begin
Some (((l1), (cattributes)))
end
| uu____1936 -> begin
None
end)))


let try_lookup_effect_defn : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl Prims.option = (fun env l -> (

let uu____1950 = (try_lookup_effect_name' (not (env.iface)) env l)
in (match (uu____1950) with
| Some ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect (ne); FStar_Syntax_Syntax.sigdoc = uu____1956; FStar_Syntax_Syntax.sigrng = uu____1957}, uu____1958) -> begin
Some (ne)
end
| Some ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect_for_free (ne); FStar_Syntax_Syntax.sigdoc = uu____1963; FStar_Syntax_Syntax.sigrng = uu____1964}, uu____1965) -> begin
Some (ne)
end
| uu____1969 -> begin
None
end)))


let is_effect_name : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let uu____1979 = (try_lookup_effect_name env lid)
in (match (uu____1979) with
| None -> begin
false
end
| Some (uu____1981) -> begin
true
end)))


let try_lookup_root_effect_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env l -> (

let uu____1989 = (try_lookup_effect_name' (not (env.iface)) env l)
in (match (uu____1989) with
| Some ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_effect_abbrev (l', uu____1995, uu____1996, uu____1997, uu____1998, uu____1999); FStar_Syntax_Syntax.sigdoc = uu____2000; FStar_Syntax_Syntax.sigrng = uu____2001}, uu____2002) -> begin
(

let rec aux = (fun new_name -> (

let uu____2015 = (FStar_Util.smap_try_find (sigmap env) new_name.FStar_Ident.str)
in (match (uu____2015) with
| None -> begin
None
end
| Some (s, uu____2025) -> begin
(match (s.FStar_Syntax_Syntax.sigel) with
| (FStar_Syntax_Syntax.Sig_new_effect_for_free (ne)) | (FStar_Syntax_Syntax.Sig_new_effect (ne)) -> begin
Some ((FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname (FStar_Ident.range_of_lid l)))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (uu____2030, uu____2031, uu____2032, cmp, uu____2034, uu____2035) -> begin
(

let l'' = (FStar_Syntax_Util.comp_effect_name cmp)
in (aux l''))
end
| uu____2041 -> begin
None
end)
end)))
in (aux l'))
end
| Some (uu____2042, l') -> begin
Some (l')
end
| uu____2046 -> begin
None
end)))


let lookup_letbinding_quals : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.qualifier Prims.list = (fun env lid -> (

let k_global_def = (fun lid1 uu___155_2067 -> (match (uu___155_2067) with
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (lid2, uu____2073, uu____2074, quals); FStar_Syntax_Syntax.sigdoc = uu____2076; FStar_Syntax_Syntax.sigrng = uu____2077}, uu____2078) -> begin
Some (quals)
end
| uu____2083 -> begin
None
end))
in (

let uu____2087 = (resolve_in_open_namespaces' env lid (fun uu____2091 -> None) (fun uu____2093 -> None) k_global_def)
in (match (uu____2087) with
| Some (quals) -> begin
quals
end
| uu____2099 -> begin
[]
end))))


let try_lookup_module : env  ->  Prims.string Prims.list  ->  FStar_Syntax_Syntax.modul Prims.option = (fun env path -> (

let uu____2111 = (FStar_List.tryFind (fun uu____2117 -> (match (uu____2117) with
| (mlid, modul) -> begin
(

let uu____2122 = (FStar_Ident.path_of_lid mlid)
in (uu____2122 = path))
end)) env.modules)
in (match (uu____2111) with
| Some (uu____2126, modul) -> begin
Some (modul)
end
| None -> begin
None
end)))


let try_lookup_let : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env lid -> (

let k_global_def = (fun lid1 uu___156_2148 -> (match (uu___156_2148) with
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let ((uu____2152, lbs), uu____2154, uu____2155, uu____2156); FStar_Syntax_Syntax.sigdoc = uu____2157; FStar_Syntax_Syntax.sigrng = uu____2158}, uu____2159) -> begin
(

let fv = (lb_fv lbs lid1)
in (

let uu____2173 = (FStar_Syntax_Syntax.fvar lid1 fv.FStar_Syntax_Syntax.fv_delta fv.FStar_Syntax_Syntax.fv_qual)
in Some (uu____2173)))
end
| uu____2174 -> begin
None
end))
in (resolve_in_open_namespaces' env lid (fun uu____2177 -> None) (fun uu____2178 -> None) k_global_def)))


let try_lookup_definition : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env lid -> (

let k_global_def = (fun lid1 uu___157_2197 -> (match (uu___157_2197) with
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (lbs, uu____2204, uu____2205, uu____2206); FStar_Syntax_Syntax.sigdoc = uu____2207; FStar_Syntax_Syntax.sigrng = uu____2208}, uu____2209) -> begin
(FStar_Util.find_map (Prims.snd lbs) (fun lb -> (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv lid1) -> begin
Some (lb.FStar_Syntax_Syntax.lbdef)
end
| uu____2227 -> begin
None
end)))
end
| uu____2232 -> begin
None
end))
in (resolve_in_open_namespaces' env lid (fun uu____2239 -> None) (fun uu____2242 -> None) k_global_def)))


let empty_include_smap : FStar_Ident.lident Prims.list FStar_ST.ref FStar_Util.smap = (new_sigmap ())


let empty_exported_id_smap : exported_id_set FStar_Util.smap = (new_sigmap ())


let try_lookup_lid' : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term * Prims.bool) Prims.option = (fun any_val exclude_interf env lid -> (

let uu____2269 = (try_lookup_name any_val exclude_interf env lid)
in (match (uu____2269) with
| Some (Term_name (e, mut)) -> begin
Some (((e), (mut)))
end
| uu____2278 -> begin
None
end)))


let try_lookup_lid : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term * Prims.bool) Prims.option = (fun env l -> (try_lookup_lid' env.iface false env l))


let resolve_to_fully_qualified_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env l -> (

let uu____2298 = (try_lookup_lid env l)
in (match (uu____2298) with
| None -> begin
None
end
| Some (e, uu____2306) -> begin
(

let uu____2309 = (

let uu____2310 = (FStar_Syntax_Subst.compress e)
in uu____2310.FStar_Syntax_Syntax.n)
in (match (uu____2309) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
Some (fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end
| uu____2319 -> begin
None
end))
end)))


let try_lookup_lid_no_resolve : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term * Prims.bool) Prims.option = (fun env l -> (

let env' = (

let uu___168_2330 = env
in {curmodule = uu___168_2330.curmodule; curmonad = uu___168_2330.curmonad; modules = uu___168_2330.modules; scope_mods = []; exported_ids = empty_exported_id_smap; trans_exported_ids = uu___168_2330.trans_exported_ids; includes = empty_include_smap; sigaccum = uu___168_2330.sigaccum; sigmap = uu___168_2330.sigmap; iface = uu___168_2330.iface; admitted_iface = uu___168_2330.admitted_iface; expect_typ = uu___168_2330.expect_typ})
in (try_lookup_lid env' l)))


let try_lookup_datacon : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.fv Prims.option = (fun env lid -> (

let k_global_def = (fun lid1 uu___159_2347 -> (match (uu___159_2347) with
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (uu____2351, uu____2352, uu____2353, quals); FStar_Syntax_Syntax.sigdoc = uu____2355; FStar_Syntax_Syntax.sigrng = uu____2356}, uu____2357) -> begin
(

let uu____2361 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___158_2363 -> (match (uu___158_2363) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| uu____2364 -> begin
false
end))))
in (match (uu____2361) with
| true -> begin
(

let uu____2366 = (FStar_Syntax_Syntax.lid_as_fv lid1 FStar_Syntax_Syntax.Delta_constant None)
in Some (uu____2366))
end
| uu____2367 -> begin
None
end))
end
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (uu____2368); FStar_Syntax_Syntax.sigdoc = uu____2369; FStar_Syntax_Syntax.sigrng = uu____2370}, uu____2371) -> begin
(

let uu____2382 = (FStar_Syntax_Syntax.lid_as_fv lid1 FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in Some (uu____2382))
end
| uu____2383 -> begin
None
end))
in (resolve_in_open_namespaces' env lid (fun uu____2386 -> None) (fun uu____2387 -> None) k_global_def)))


let find_all_datacons : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.list Prims.option = (fun env lid -> (

let k_global_def = (fun lid1 uu___160_2406 -> (match (uu___160_2406) with
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (uu____2411, uu____2412, uu____2413, uu____2414, uu____2415, datas, uu____2417); FStar_Syntax_Syntax.sigdoc = uu____2418; FStar_Syntax_Syntax.sigrng = uu____2419}, uu____2420) -> begin
Some (datas)
end
| uu____2429 -> begin
None
end))
in (resolve_in_open_namespaces' env lid (fun uu____2434 -> None) (fun uu____2436 -> None) k_global_def)))


let record_cache_aux_with_filter : (((Prims.unit  ->  Prims.unit) * (Prims.unit  ->  Prims.unit) * (Prims.unit  ->  record_or_dc Prims.list) * (record_or_dc  ->  Prims.unit) * (Prims.unit  ->  Prims.unit)) * (Prims.unit  ->  Prims.unit)) = (

let record_cache = (FStar_Util.mk_ref (([])::[]))
in (

let push1 = (fun uu____2470 -> (

let uu____2471 = (

let uu____2474 = (

let uu____2476 = (FStar_ST.read record_cache)
in (FStar_List.hd uu____2476))
in (

let uu____2484 = (FStar_ST.read record_cache)
in (uu____2474)::uu____2484))
in (FStar_ST.write record_cache uu____2471)))
in (

let pop1 = (fun uu____2499 -> (

let uu____2500 = (

let uu____2503 = (FStar_ST.read record_cache)
in (FStar_List.tl uu____2503))
in (FStar_ST.write record_cache uu____2500)))
in (

let peek = (fun uu____2519 -> (

let uu____2520 = (FStar_ST.read record_cache)
in (FStar_List.hd uu____2520)))
in (

let insert = (fun r -> (

let uu____2532 = (

let uu____2535 = (

let uu____2537 = (peek ())
in (r)::uu____2537)
in (

let uu____2539 = (

let uu____2542 = (FStar_ST.read record_cache)
in (FStar_List.tl uu____2542))
in (uu____2535)::uu____2539))
in (FStar_ST.write record_cache uu____2532)))
in (

let commit1 = (fun uu____2558 -> (

let uu____2559 = (FStar_ST.read record_cache)
in (match (uu____2559) with
| (hd1)::(uu____2567)::tl1 -> begin
(FStar_ST.write record_cache ((hd1)::tl1))
end
| uu____2580 -> begin
(failwith "Impossible")
end)))
in (

let filter1 = (fun uu____2586 -> (

let rc = (peek ())
in ((pop1 ());
(match (()) with
| () -> begin
(

let filtered = (FStar_List.filter (fun r -> (not (r.is_private_or_abstract))) rc)
in (

let uu____2593 = (

let uu____2596 = (FStar_ST.read record_cache)
in (filtered)::uu____2596)
in (FStar_ST.write record_cache uu____2593)))
end);
)))
in (

let aux = ((push1), (pop1), (peek), (insert), (commit1))
in ((aux), (filter1))))))))))


let record_cache_aux : ((Prims.unit  ->  Prims.unit) * (Prims.unit  ->  Prims.unit) * (Prims.unit  ->  record_or_dc Prims.list) * (record_or_dc  ->  Prims.unit) * (Prims.unit  ->  Prims.unit)) = (

let uu____2670 = record_cache_aux_with_filter
in (match (uu____2670) with
| (aux, uu____2708) -> begin
aux
end))


let filter_record_cache : Prims.unit  ->  Prims.unit = (

let uu____2747 = record_cache_aux_with_filter
in (match (uu____2747) with
| (uu____2770, filter1) -> begin
filter1
end))


let push_record_cache : Prims.unit  ->  Prims.unit = (

let uu____2810 = record_cache_aux
in (match (uu____2810) with
| (push1, uu____2830, uu____2831, uu____2832, uu____2833) -> begin
push1
end))


let pop_record_cache : Prims.unit  ->  Prims.unit = (

let uu____2858 = record_cache_aux
in (match (uu____2858) with
| (uu____2877, pop1, uu____2879, uu____2880, uu____2881) -> begin
pop1
end))


let peek_record_cache : Prims.unit  ->  record_or_dc Prims.list = (

let uu____2907 = record_cache_aux
in (match (uu____2907) with
| (uu____2927, uu____2928, peek, uu____2930, uu____2931) -> begin
peek
end))


let insert_record_cache : record_or_dc  ->  Prims.unit = (

let uu____2956 = record_cache_aux
in (match (uu____2956) with
| (uu____2975, uu____2976, uu____2977, insert, uu____2979) -> begin
insert
end))


let commit_record_cache : Prims.unit  ->  Prims.unit = (

let uu____3004 = record_cache_aux
in (match (uu____3004) with
| (uu____3023, uu____3024, uu____3025, uu____3026, commit1) -> begin
commit1
end))


let extract_record : env  ->  scope_mod Prims.list FStar_ST.ref  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun e new_globs se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_bundle (sigs, uu____3066, uu____3067) -> begin
(

let is_rec = (FStar_Util.for_some (fun uu___161_3078 -> (match (uu___161_3078) with
| (FStar_Syntax_Syntax.RecordType (_)) | (FStar_Syntax_Syntax.RecordConstructor (_)) -> begin
true
end
| uu____3081 -> begin
false
end)))
in (

let find_dc = (fun dc -> (FStar_All.pipe_right sigs (FStar_Util.find_opt (fun uu___162_3089 -> (match (uu___162_3089) with
| {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (lid, uu____3091, uu____3092, uu____3093, uu____3094, uu____3095, uu____3096); FStar_Syntax_Syntax.sigdoc = uu____3097; FStar_Syntax_Syntax.sigrng = uu____3098} -> begin
(FStar_Ident.lid_equals dc lid)
end
| uu____3104 -> begin
false
end)))))
in (FStar_All.pipe_right sigs (FStar_List.iter (fun uu___163_3106 -> (match (uu___163_3106) with
| {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (typename, univs, parms, uu____3110, uu____3111, (dc)::[], tags); FStar_Syntax_Syntax.sigdoc = uu____3114; FStar_Syntax_Syntax.sigrng = uu____3115} -> begin
(

let uu____3122 = (

let uu____3123 = (find_dc dc)
in (FStar_All.pipe_left FStar_Util.must uu____3123))
in (match (uu____3122) with
| {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (constrname, uu____3127, t, uu____3129, uu____3130, uu____3131, uu____3132); FStar_Syntax_Syntax.sigdoc = uu____3133; FStar_Syntax_Syntax.sigrng = uu____3134} -> begin
(

let uu____3140 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____3140) with
| (formals, uu____3149) -> begin
(

let is_rec1 = (is_rec tags)
in (

let formals' = (FStar_All.pipe_right formals (FStar_List.collect (fun uu____3175 -> (match (uu____3175) with
| (x, q) -> begin
(

let uu____3183 = ((FStar_Syntax_Syntax.is_null_bv x) || (is_rec1 && (FStar_Syntax_Syntax.is_implicit q)))
in (match (uu____3183) with
| true -> begin
[]
end
| uu____3189 -> begin
(((x), (q)))::[]
end))
end))))
in (

let fields' = (FStar_All.pipe_right formals' (FStar_List.map (fun uu____3214 -> (match (uu____3214) with
| (x, q) -> begin
(

let uu____3223 = (match (is_rec1) with
| true -> begin
(FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname)
end
| uu____3224 -> begin
x.FStar_Syntax_Syntax.ppname
end)
in ((uu____3223), (x.FStar_Syntax_Syntax.sort)))
end))))
in (

let fields = fields'
in (

let record = {typename = typename; constrname = constrname.FStar_Ident.ident; parms = parms; fields = fields; is_private_or_abstract = ((FStar_List.contains FStar_Syntax_Syntax.Private tags) || (FStar_List.contains FStar_Syntax_Syntax.Abstract tags)); is_record = is_rec1}
in ((

let uu____3235 = (

let uu____3237 = (FStar_ST.read new_globs)
in (Record_or_dc (record))::uu____3237)
in (FStar_ST.write new_globs uu____3235));
(match (()) with
| () -> begin
((

let add_field = (fun uu____3253 -> (match (uu____3253) with
| (id, uu____3259) -> begin
(

let modul = (

let uu____3265 = (FStar_Ident.lid_of_ids constrname.FStar_Ident.ns)
in uu____3265.FStar_Ident.str)
in (

let uu____3266 = (get_exported_id_set e modul)
in (match (uu____3266) with
| Some (my_ex) -> begin
(

let my_exported_ids = (my_ex Exported_id_field)
in ((

let uu____3282 = (

let uu____3283 = (FStar_ST.read my_exported_ids)
in (FStar_Util.set_add id.FStar_Ident.idText uu____3283))
in (FStar_ST.write my_exported_ids uu____3282));
(match (()) with
| () -> begin
(

let projname = (

let uu____3290 = (

let uu____3291 = (FStar_Syntax_Util.mk_field_projector_name_from_ident constrname id)
in uu____3291.FStar_Ident.ident)
in uu____3290.FStar_Ident.idText)
in (

let uu____3293 = (

let uu____3294 = (FStar_ST.read my_exported_ids)
in (FStar_Util.set_add projname uu____3294))
in (FStar_ST.write my_exported_ids uu____3293)))
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
| uu____3307 -> begin
()
end))
end
| uu____3308 -> begin
()
end))))))
end
| uu____3309 -> begin
()
end))


let try_lookup_record_or_dc_by_field_name : env  ->  FStar_Ident.lident  ->  record_or_dc Prims.option = (fun env fieldname -> (

let find_in_cache = (fun fieldname1 -> (

let uu____3322 = ((fieldname1.FStar_Ident.ns), (fieldname1.FStar_Ident.ident))
in (match (uu____3322) with
| (ns, id) -> begin
(

let uu____3332 = (peek_record_cache ())
in (FStar_Util.find_map uu____3332 (fun record -> (

let uu____3335 = (find_in_record ns id record (fun r -> Cont_ok (r)))
in (option_of_cont (fun uu____3338 -> None) uu____3335)))))
end)))
in (resolve_in_open_namespaces'' env fieldname Exported_id_field (fun uu____3339 -> Cont_ignore) (fun uu____3340 -> Cont_ignore) (fun r -> Cont_ok (r)) (fun fn -> (

let uu____3343 = (find_in_cache fn)
in (cont_of_option Cont_ignore uu____3343))) (fun k uu____3346 -> k))))


let try_lookup_record_by_field_name : env  ->  FStar_Ident.lident  ->  record_or_dc Prims.option = (fun env fieldname -> (

let uu____3355 = (try_lookup_record_or_dc_by_field_name env fieldname)
in (match (uu____3355) with
| Some (r) when r.is_record -> begin
Some (r)
end
| uu____3359 -> begin
None
end)))


let belongs_to_record : env  ->  FStar_Ident.lident  ->  record_or_dc  ->  Prims.bool = (fun env lid record -> (

let uu____3370 = (try_lookup_record_by_field_name env lid)
in (match (uu____3370) with
| Some (record') when (

let uu____3373 = (

let uu____3374 = (FStar_Ident.path_of_ns record.typename.FStar_Ident.ns)
in (FStar_Ident.text_of_path uu____3374))
in (

let uu____3376 = (

let uu____3377 = (FStar_Ident.path_of_ns record'.typename.FStar_Ident.ns)
in (FStar_Ident.text_of_path uu____3377))
in (uu____3373 = uu____3376))) -> begin
(

let uu____3379 = (find_in_record record.typename.FStar_Ident.ns lid.FStar_Ident.ident record (fun uu____3381 -> Cont_ok (())))
in (match (uu____3379) with
| Cont_ok (uu____3382) -> begin
true
end
| uu____3383 -> begin
false
end))
end
| uu____3385 -> begin
false
end)))


let try_lookup_dc_by_field_name : env  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * Prims.bool) Prims.option = (fun env fieldname -> (

let uu____3396 = (try_lookup_record_or_dc_by_field_name env fieldname)
in (match (uu____3396) with
| Some (r) -> begin
(

let uu____3402 = (

let uu____3405 = (

let uu____3406 = (FStar_Ident.lid_of_ids (FStar_List.append r.typename.FStar_Ident.ns ((r.constrname)::[])))
in (FStar_Ident.set_lid_range uu____3406 (FStar_Ident.range_of_lid fieldname)))
in ((uu____3405), (r.is_record)))
in Some (uu____3402))
end
| uu____3409 -> begin
None
end)))


let string_set_ref_new : Prims.unit  ->  Prims.string FStar_Util.set FStar_ST.ref = (fun uu____3418 -> (

let uu____3419 = (FStar_Util.new_set FStar_Util.compare FStar_Util.hashcode)
in (FStar_Util.mk_ref uu____3419)))


let exported_id_set_new : Prims.unit  ->  exported_id_kind  ->  Prims.string FStar_Util.set FStar_ST.ref = (fun uu____3430 -> (

let term_type_set = (string_set_ref_new ())
in (

let field_set = (string_set_ref_new ())
in (fun uu___164_3439 -> (match (uu___164_3439) with
| Exported_id_term_type -> begin
term_type_set
end
| Exported_id_field -> begin
field_set
end)))))


let unique : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  Prims.bool = (fun any_val exclude_if env lid -> (

let filter_scope_mods = (fun uu___165_3459 -> (match (uu___165_3459) with
| Rec_binding (uu____3460) -> begin
true
end
| uu____3461 -> begin
false
end))
in (

let this_env = (

let uu___169_3463 = env
in (

let uu____3464 = (FStar_List.filter filter_scope_mods env.scope_mods)
in {curmodule = uu___169_3463.curmodule; curmonad = uu___169_3463.curmonad; modules = uu___169_3463.modules; scope_mods = uu____3464; exported_ids = empty_exported_id_smap; trans_exported_ids = uu___169_3463.trans_exported_ids; includes = empty_include_smap; sigaccum = uu___169_3463.sigaccum; sigmap = uu___169_3463.sigmap; iface = uu___169_3463.iface; admitted_iface = uu___169_3463.admitted_iface; expect_typ = uu___169_3463.expect_typ}))
in (

let uu____3466 = (try_lookup_lid' any_val exclude_if this_env lid)
in (match (uu____3466) with
| None -> begin
true
end
| Some (uu____3472) -> begin
false
end)))))


let push_scope_mod : env  ->  scope_mod  ->  env = (fun env scope_mod -> (

let uu___170_3483 = env
in {curmodule = uu___170_3483.curmodule; curmonad = uu___170_3483.curmonad; modules = uu___170_3483.modules; scope_mods = (scope_mod)::env.scope_mods; exported_ids = uu___170_3483.exported_ids; trans_exported_ids = uu___170_3483.trans_exported_ids; includes = uu___170_3483.includes; sigaccum = uu___170_3483.sigaccum; sigmap = uu___170_3483.sigmap; iface = uu___170_3483.iface; admitted_iface = uu___170_3483.admitted_iface; expect_typ = uu___170_3483.expect_typ}))


let push_bv' : env  ->  FStar_Ident.ident  ->  Prims.bool  ->  (env * FStar_Syntax_Syntax.bv) = (fun env x is_mutable -> (

let bv = (FStar_Syntax_Syntax.gen_bv x.FStar_Ident.idText (Some (x.FStar_Ident.idRange)) FStar_Syntax_Syntax.tun)
in (((push_scope_mod env (Local_binding (((x), (bv), (is_mutable)))))), (bv))))


let push_bv_mutable : env  ->  FStar_Ident.ident  ->  (env * FStar_Syntax_Syntax.bv) = (fun env x -> (push_bv' env x true))


let push_bv : env  ->  FStar_Ident.ident  ->  (env * FStar_Syntax_Syntax.bv) = (fun env x -> (push_bv' env x false))


let push_top_level_rec_binding : env  ->  FStar_Ident.ident  ->  FStar_Syntax_Syntax.delta_depth  ->  env = (fun env x dd -> (

let l = (qualify env x)
in (

let uu____3522 = ((unique false true env l) || (FStar_Options.interactive ()))
in (match (uu____3522) with
| true -> begin
(push_scope_mod env (Rec_binding (((x), (l), (dd)))))
end
| uu____3523 -> begin
(Prims.raise (FStar_Errors.Error ((((Prims.strcat "Duplicate top-level names " l.FStar_Ident.str)), ((FStar_Ident.range_of_lid l))))))
end))))


let push_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env s -> (

let err = (fun l -> (

let sopt = (FStar_Util.smap_try_find (sigmap env) l.FStar_Ident.str)
in (

let r = (match (sopt) with
| Some (se, uu____3542) -> begin
(

let uu____3545 = (FStar_Util.find_opt (FStar_Ident.lid_equals l) (FStar_Syntax_Util.lids_of_sigelt se))
in (match (uu____3545) with
| Some (l1) -> begin
(FStar_All.pipe_left FStar_Range.string_of_range (FStar_Ident.range_of_lid l1))
end
| None -> begin
"<unknown>"
end))
end
| None -> begin
"<unknown>"
end)
in (

let uu____3550 = (

let uu____3551 = (

let uu____3554 = (FStar_Util.format2 "Duplicate top-level names [%s]; previously declared at %s" (FStar_Ident.text_of_lid l) r)
in ((uu____3554), ((FStar_Ident.range_of_lid l))))
in FStar_Errors.Error (uu____3551))
in (Prims.raise uu____3550)))))
in (

let globals = (FStar_Util.mk_ref env.scope_mods)
in (

let env1 = (

let uu____3561 = (match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let (uu____3566) -> begin
((false), (true))
end
| FStar_Syntax_Syntax.Sig_bundle (uu____3574) -> begin
((true), (true))
end
| uu____3581 -> begin
((false), (false))
end)
in (match (uu____3561) with
| (any_val, exclude_if) -> begin
(

let lids = (FStar_Syntax_Util.lids_of_sigelt s)
in (

let uu____3586 = (FStar_Util.find_map lids (fun l -> (

let uu____3589 = (

let uu____3590 = (unique any_val exclude_if env l)
in (not (uu____3590)))
in (match (uu____3589) with
| true -> begin
Some (l)
end
| uu____3592 -> begin
None
end))))
in (match (uu____3586) with
| Some (l) when (

let uu____3594 = (FStar_Options.interactive ())
in (not (uu____3594))) -> begin
(err l)
end
| uu____3595 -> begin
((extract_record env globals s);
(

let uu___171_3600 = env
in {curmodule = uu___171_3600.curmodule; curmonad = uu___171_3600.curmonad; modules = uu___171_3600.modules; scope_mods = uu___171_3600.scope_mods; exported_ids = uu___171_3600.exported_ids; trans_exported_ids = uu___171_3600.trans_exported_ids; includes = uu___171_3600.includes; sigaccum = (s)::env.sigaccum; sigmap = uu___171_3600.sigmap; iface = uu___171_3600.iface; admitted_iface = uu___171_3600.admitted_iface; expect_typ = uu___171_3600.expect_typ});
)
end)))
end))
in (

let env2 = (

let uu___172_3602 = env1
in (

let uu____3603 = (FStar_ST.read globals)
in {curmodule = uu___172_3602.curmodule; curmonad = uu___172_3602.curmonad; modules = uu___172_3602.modules; scope_mods = uu____3603; exported_ids = uu___172_3602.exported_ids; trans_exported_ids = uu___172_3602.trans_exported_ids; includes = uu___172_3602.includes; sigaccum = uu___172_3602.sigaccum; sigmap = uu___172_3602.sigmap; iface = uu___172_3602.iface; admitted_iface = uu___172_3602.admitted_iface; expect_typ = uu___172_3602.expect_typ}))
in (

let uu____3608 = (match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____3622, uu____3623) -> begin
(

let uu____3630 = (FStar_List.map (fun se -> (((FStar_Syntax_Util.lids_of_sigelt se)), (se))) ses)
in ((env2), (uu____3630)))
end
| uu____3644 -> begin
((env2), (((((FStar_Syntax_Util.lids_of_sigelt s)), (s)))::[]))
end)
in (match (uu____3608) with
| (env3, lss) -> begin
((FStar_All.pipe_right lss (FStar_List.iter (fun uu____3674 -> (match (uu____3674) with
| (lids, se) -> begin
(FStar_All.pipe_right lids (FStar_List.iter (fun lid -> ((

let uu____3685 = (

let uu____3687 = (FStar_ST.read globals)
in (Top_level_def (lid.FStar_Ident.ident))::uu____3687)
in (FStar_ST.write globals uu____3685));
(match (()) with
| () -> begin
(

let modul = (

let uu____3696 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in uu____3696.FStar_Ident.str)
in ((

let uu____3698 = (get_exported_id_set env3 modul)
in (match (uu____3698) with
| Some (f) -> begin
(

let my_exported_ids = (f Exported_id_term_type)
in (

let uu____3713 = (

let uu____3714 = (FStar_ST.read my_exported_ids)
in (FStar_Util.set_add lid.FStar_Ident.ident.FStar_Ident.idText uu____3714))
in (FStar_ST.write my_exported_ids uu____3713)))
end
| None -> begin
()
end));
(match (()) with
| () -> begin
(FStar_Util.smap_add (sigmap env3) lid.FStar_Ident.str ((se), ((env3.iface && (not (env3.admitted_iface))))))
end);
))
end);
))))
end))));
(

let env4 = (

let uu___173_3726 = env3
in (

let uu____3727 = (FStar_ST.read globals)
in {curmodule = uu___173_3726.curmodule; curmonad = uu___173_3726.curmonad; modules = uu___173_3726.modules; scope_mods = uu____3727; exported_ids = uu___173_3726.exported_ids; trans_exported_ids = uu___173_3726.trans_exported_ids; includes = uu___173_3726.includes; sigaccum = uu___173_3726.sigaccum; sigmap = uu___173_3726.sigmap; iface = uu___173_3726.iface; admitted_iface = uu___173_3726.admitted_iface; expect_typ = uu___173_3726.expect_typ}))
in env4);
)
end)))))))


let push_namespace : env  ->  FStar_Ident.lident  ->  env = (fun env ns -> (

let uu____3738 = (

let uu____3741 = (resolve_module_name env ns false)
in (match (uu____3741) with
| None -> begin
(

let modules = env.modules
in (

let uu____3749 = (FStar_All.pipe_right modules (FStar_Util.for_some (fun uu____3755 -> (match (uu____3755) with
| (m, uu____3759) -> begin
(FStar_Util.starts_with (Prims.strcat (FStar_Ident.text_of_lid m) ".") (Prims.strcat (FStar_Ident.text_of_lid ns) "."))
end))))
in (match (uu____3749) with
| true -> begin
((ns), (Open_namespace))
end
| uu____3762 -> begin
(

let uu____3763 = (

let uu____3764 = (

let uu____3767 = (FStar_Util.format1 "Namespace %s cannot be found" (FStar_Ident.text_of_lid ns))
in ((uu____3767), ((FStar_Ident.range_of_lid ns))))
in FStar_Errors.Error (uu____3764))
in (Prims.raise uu____3763))
end)))
end
| Some (ns') -> begin
((ns'), (Open_module))
end))
in (match (uu____3738) with
| (ns', kd) -> begin
(push_scope_mod env (Open_module_or_namespace (((ns'), (kd)))))
end)))


let push_include : env  ->  FStar_Ident.lident  ->  env = (fun env ns -> (

let uu____3779 = (resolve_module_name env ns false)
in (match (uu____3779) with
| Some (ns1) -> begin
(

let env1 = (push_scope_mod env (Open_module_or_namespace (((ns1), (Open_module)))))
in (

let curmod = (

let uu____3784 = (current_module env1)
in uu____3784.FStar_Ident.str)
in ((

let uu____3786 = (FStar_Util.smap_try_find env1.includes curmod)
in (match (uu____3786) with
| None -> begin
()
end
| Some (incl) -> begin
(

let uu____3799 = (

let uu____3801 = (FStar_ST.read incl)
in (ns1)::uu____3801)
in (FStar_ST.write incl uu____3799))
end));
(match (()) with
| () -> begin
(

let uu____3809 = (get_trans_exported_id_set env1 ns1.FStar_Ident.str)
in (match (uu____3809) with
| Some (ns_trans_exports) -> begin
((

let uu____3822 = (

let uu____3833 = (get_exported_id_set env1 curmod)
in (

let uu____3838 = (get_trans_exported_id_set env1 curmod)
in ((uu____3833), (uu____3838))))
in (match (uu____3822) with
| (Some (cur_exports), Some (cur_trans_exports)) -> begin
(

let update_exports = (fun k -> (

let ns_ex = (

let uu____3878 = (ns_trans_exports k)
in (FStar_ST.read uu____3878))
in (

let ex = (cur_exports k)
in ((

let uu____3887 = (

let uu____3888 = (FStar_ST.read ex)
in (FStar_Util.set_difference uu____3888 ns_ex))
in (FStar_ST.write ex uu____3887));
(match (()) with
| () -> begin
(

let trans_ex = (cur_trans_exports k)
in (

let uu____3898 = (

let uu____3899 = (FStar_ST.read trans_ex)
in (FStar_Util.set_union uu____3899 ns_ex))
in (FStar_ST.write trans_ex uu____3898)))
end);
))))
in (FStar_List.iter update_exports all_exported_id_kinds))
end
| uu____3905 -> begin
()
end));
(match (()) with
| () -> begin
env1
end);
)
end
| None -> begin
(

let uu____3919 = (

let uu____3920 = (

let uu____3923 = (FStar_Util.format1 "include: Module %s was not prepared" ns1.FStar_Ident.str)
in ((uu____3923), ((FStar_Ident.range_of_lid ns1))))
in FStar_Errors.Error (uu____3920))
in (Prims.raise uu____3919))
end))
end);
)))
end
| uu____3924 -> begin
(

let uu____3926 = (

let uu____3927 = (

let uu____3930 = (FStar_Util.format1 "include: Module %s cannot be found" ns.FStar_Ident.str)
in ((uu____3930), ((FStar_Ident.range_of_lid ns))))
in FStar_Errors.Error (uu____3927))
in (Prims.raise uu____3926))
end)))


let push_module_abbrev : env  ->  FStar_Ident.ident  ->  FStar_Ident.lident  ->  env = (fun env x l -> (

let uu____3940 = (module_is_defined env l)
in (match (uu____3940) with
| true -> begin
(push_scope_mod env (Module_abbrev (((x), (l)))))
end
| uu____3941 -> begin
(

let uu____3942 = (

let uu____3943 = (

let uu____3946 = (FStar_Util.format1 "Module %s cannot be found" (FStar_Ident.text_of_lid l))
in ((uu____3946), ((FStar_Ident.range_of_lid l))))
in FStar_Errors.Error (uu____3943))
in (Prims.raise uu____3942))
end)))


let check_admits : env  ->  Prims.unit = (fun env -> (FStar_All.pipe_right env.sigaccum (FStar_List.iter (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_declare_typ (l, u, t, quals) -> begin
(

let uu____3957 = (try_lookup_lid env l)
in (match (uu____3957) with
| None -> begin
((

let uu____3964 = (

let uu____3965 = (FStar_Options.interactive ())
in (not (uu____3965)))
in (match (uu____3964) with
| true -> begin
(

let uu____3966 = (

let uu____3967 = (FStar_Range.string_of_range (FStar_Ident.range_of_lid l))
in (

let uu____3968 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format2 "%s: Warning: Admitting %s without a definition\n" uu____3967 uu____3968)))
in (FStar_Util.print_string uu____3966))
end
| uu____3969 -> begin
()
end));
(FStar_Util.smap_add (sigmap env) l.FStar_Ident.str (((

let uu___174_3972 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((l), (u), (t), ((FStar_Syntax_Syntax.Assumption)::quals))); FStar_Syntax_Syntax.sigdoc = uu___174_3972.FStar_Syntax_Syntax.sigdoc; FStar_Syntax_Syntax.sigrng = uu___174_3972.FStar_Syntax_Syntax.sigrng})), (false)));
)
end
| Some (uu____3974) -> begin
()
end))
end
| uu____3979 -> begin
()
end)))))


let finish : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env modul -> ((FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations (FStar_List.iter (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, uu____3990) -> begin
(match (((FStar_List.contains FStar_Syntax_Syntax.Private quals) || (FStar_List.contains FStar_Syntax_Syntax.Abstract quals))) with
| true -> begin
(FStar_All.pipe_right ses (FStar_List.iter (fun se1 -> (match (se1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (lid, uu____4000, uu____4001, uu____4002, uu____4003, uu____4004, uu____4005) -> begin
(FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str)
end
| uu____4012 -> begin
()
end))))
end
| uu____4013 -> begin
()
end)
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____4015, uu____4016, quals) -> begin
(match ((FStar_List.contains FStar_Syntax_Syntax.Private quals)) with
| true -> begin
(FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str)
end
| uu____4022 -> begin
()
end)
end
| FStar_Syntax_Syntax.Sig_let ((uu____4023, lbs), uu____4025, quals, uu____4027) -> begin
((match (((FStar_List.contains FStar_Syntax_Syntax.Private quals) || (FStar_List.contains FStar_Syntax_Syntax.Abstract quals))) with
| true -> begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (

let uu____4042 = (

let uu____4043 = (

let uu____4044 = (

let uu____4049 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in uu____4049.FStar_Syntax_Syntax.fv_name)
in uu____4044.FStar_Syntax_Syntax.v)
in uu____4043.FStar_Ident.str)
in (FStar_Util.smap_remove (sigmap env) uu____4042)))))
end
| uu____4055 -> begin
()
end);
(match (((FStar_List.contains FStar_Syntax_Syntax.Abstract quals) && (not ((FStar_List.contains FStar_Syntax_Syntax.Private quals))))) with
| true -> begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (

let lid = (

let uu____4059 = (

let uu____4064 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in uu____4064.FStar_Syntax_Syntax.fv_name)
in uu____4059.FStar_Syntax_Syntax.v)
in (

let decl = (

let uu___175_4069 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), ((FStar_Syntax_Syntax.Assumption)::quals))); FStar_Syntax_Syntax.sigdoc = uu___175_4069.FStar_Syntax_Syntax.sigdoc; FStar_Syntax_Syntax.sigrng = uu___175_4069.FStar_Syntax_Syntax.sigrng})
in (FStar_Util.smap_add (sigmap env) lid.FStar_Ident.str ((decl), (false))))))))
end
| uu____4076 -> begin
()
end);
)
end
| uu____4077 -> begin
()
end))));
(

let curmod = (

let uu____4079 = (current_module env)
in uu____4079.FStar_Ident.str)
in ((

let uu____4081 = (

let uu____4092 = (get_exported_id_set env curmod)
in (

let uu____4097 = (get_trans_exported_id_set env curmod)
in ((uu____4092), (uu____4097))))
in (match (uu____4081) with
| (Some (cur_ex), Some (cur_trans_ex)) -> begin
(

let update_exports = (fun eikind -> (

let cur_ex_set = (

let uu____4137 = (cur_ex eikind)
in (FStar_ST.read uu____4137))
in (

let cur_trans_ex_set_ref = (cur_trans_ex eikind)
in (

let uu____4145 = (

let uu____4146 = (FStar_ST.read cur_trans_ex_set_ref)
in (FStar_Util.set_union cur_ex_set uu____4146))
in (FStar_ST.write cur_trans_ex_set_ref uu____4145)))))
in (FStar_List.iter update_exports all_exported_id_kinds))
end
| uu____4152 -> begin
()
end));
(match (()) with
| () -> begin
((filter_record_cache ());
(match (()) with
| () -> begin
(

let uu___176_4164 = env
in {curmodule = None; curmonad = uu___176_4164.curmonad; modules = (((modul.FStar_Syntax_Syntax.name), (modul)))::env.modules; scope_mods = []; exported_ids = uu___176_4164.exported_ids; trans_exported_ids = uu___176_4164.trans_exported_ids; includes = uu___176_4164.includes; sigaccum = []; sigmap = uu___176_4164.sigmap; iface = uu___176_4164.iface; admitted_iface = uu___176_4164.admitted_iface; expect_typ = uu___176_4164.expect_typ})
end);
)
end);
));
))


let stack : env Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let push : env  ->  env = (fun env -> ((push_record_cache ());
(

let uu____4177 = (

let uu____4179 = (FStar_ST.read stack)
in (env)::uu____4179)
in (FStar_ST.write stack uu____4177));
(

let uu___177_4187 = env
in (

let uu____4188 = (FStar_Util.smap_copy (sigmap env))
in {curmodule = uu___177_4187.curmodule; curmonad = uu___177_4187.curmonad; modules = uu___177_4187.modules; scope_mods = uu___177_4187.scope_mods; exported_ids = uu___177_4187.exported_ids; trans_exported_ids = uu___177_4187.trans_exported_ids; includes = uu___177_4187.includes; sigaccum = uu___177_4187.sigaccum; sigmap = uu____4188; iface = uu___177_4187.iface; admitted_iface = uu___177_4187.admitted_iface; expect_typ = uu___177_4187.expect_typ}));
))


let pop : Prims.unit  ->  env = (fun uu____4196 -> (

let uu____4197 = (FStar_ST.read stack)
in (match (uu____4197) with
| (env)::tl1 -> begin
((pop_record_cache ());
(FStar_ST.write stack tl1);
env;
)
end
| uu____4210 -> begin
(failwith "Impossible: Too many pops")
end)))


let commit_mark : env  ->  env = (fun env -> ((commit_record_cache ());
(

let uu____4216 = (FStar_ST.read stack)
in (match (uu____4216) with
| (uu____4221)::tl1 -> begin
((FStar_ST.write stack tl1);
env;
)
end
| uu____4228 -> begin
(failwith "Impossible: Too many pops")
end));
))


let mark : env  ->  env = (fun x -> (push x))


let reset_mark : Prims.unit  ->  env = (fun uu____4235 -> (pop ()))


let export_interface : FStar_Ident.lident  ->  env  ->  env = (fun m env -> (

let sigelt_in_m = (fun se -> (match ((FStar_Syntax_Util.lids_of_sigelt se)) with
| (l)::uu____4247 -> begin
(l.FStar_Ident.nsstr = m.FStar_Ident.str)
end
| uu____4249 -> begin
false
end))
in (

let sm = (sigmap env)
in (

let env1 = (pop ())
in (

let keys = (FStar_Util.smap_keys sm)
in (

let sm' = (sigmap env1)
in ((FStar_All.pipe_right keys (FStar_List.iter (fun k -> (

let uu____4267 = (FStar_Util.smap_try_find sm' k)
in (match (uu____4267) with
| Some (se, true) when (sigelt_in_m se) -> begin
((FStar_Util.smap_remove sm' k);
(

let se1 = (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_declare_typ (l, u, t, q) -> begin
(

let uu___178_4286 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((l), (u), (t), ((FStar_Syntax_Syntax.Assumption)::q))); FStar_Syntax_Syntax.sigdoc = uu___178_4286.FStar_Syntax_Syntax.sigdoc; FStar_Syntax_Syntax.sigrng = uu___178_4286.FStar_Syntax_Syntax.sigrng})
end
| uu____4288 -> begin
se
end)
in (FStar_Util.smap_add sm' k ((se1), (false))));
)
end
| uu____4291 -> begin
()
end)))));
env1;
)))))))


let finish_module_or_interface : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env modul -> ((match ((not (modul.FStar_Syntax_Syntax.is_interface))) with
| true -> begin
(check_admits env)
end
| uu____4302 -> begin
()
end);
(finish env modul);
))


let prepare_module_or_interface : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  (env * Prims.bool) = (fun intf admitted env mname -> (

let prep = (fun env1 -> (

let open_ns = (match ((FStar_Ident.lid_equals mname FStar_Syntax_Const.prims_lid)) with
| true -> begin
[]
end
| uu____4324 -> begin
(match ((FStar_Util.starts_with "FStar." (FStar_Ident.text_of_lid mname))) with
| true -> begin
(FStar_Syntax_Const.prims_lid)::(FStar_Syntax_Const.fstar_ns_lid)::[]
end
| uu____4326 -> begin
(FStar_Syntax_Const.prims_lid)::(FStar_Syntax_Const.st_lid)::(FStar_Syntax_Const.all_lid)::(FStar_Syntax_Const.fstar_ns_lid)::[]
end)
end)
in (

let open_ns1 = (match (((FStar_List.length mname.FStar_Ident.ns) <> (Prims.parse_int "0"))) with
| true -> begin
(

let ns = (FStar_Ident.lid_of_ids mname.FStar_Ident.ns)
in (ns)::open_ns)
end
| uu____4333 -> begin
open_ns
end)
in ((

let uu____4335 = (exported_id_set_new ())
in (FStar_Util.smap_add env1.exported_ids mname.FStar_Ident.str uu____4335));
(match (()) with
| () -> begin
((

let uu____4340 = (exported_id_set_new ())
in (FStar_Util.smap_add env1.trans_exported_ids mname.FStar_Ident.str uu____4340));
(match (()) with
| () -> begin
((

let uu____4345 = (FStar_Util.mk_ref [])
in (FStar_Util.smap_add env1.includes mname.FStar_Ident.str uu____4345));
(match (()) with
| () -> begin
(

let uu___179_4354 = env1
in (

let uu____4355 = (FStar_List.map (fun lid -> Open_module_or_namespace (((lid), (Open_namespace)))) open_ns1)
in {curmodule = Some (mname); curmonad = uu___179_4354.curmonad; modules = uu___179_4354.modules; scope_mods = uu____4355; exported_ids = uu___179_4354.exported_ids; trans_exported_ids = uu___179_4354.trans_exported_ids; includes = uu___179_4354.includes; sigaccum = uu___179_4354.sigaccum; sigmap = env1.sigmap; iface = intf; admitted_iface = admitted; expect_typ = uu___179_4354.expect_typ}))
end);
)
end);
)
end);
))))
in (

let uu____4358 = (FStar_All.pipe_right env.modules (FStar_Util.find_opt (fun uu____4370 -> (match (uu____4370) with
| (l, uu____4374) -> begin
(FStar_Ident.lid_equals l mname)
end))))
in (match (uu____4358) with
| None -> begin
(

let uu____4379 = (prep env)
in ((uu____4379), (false)))
end
| Some (uu____4380, m) -> begin
((

let uu____4385 = ((

let uu____4386 = (FStar_Options.interactive ())
in (not (uu____4386))) && ((not (m.FStar_Syntax_Syntax.is_interface)) || intf))
in (match (uu____4385) with
| true -> begin
(

let uu____4387 = (

let uu____4388 = (

let uu____4391 = (FStar_Util.format1 "Duplicate module or interface name: %s" mname.FStar_Ident.str)
in ((uu____4391), ((FStar_Ident.range_of_lid mname))))
in FStar_Errors.Error (uu____4388))
in (Prims.raise uu____4387))
end
| uu____4392 -> begin
()
end));
(

let uu____4393 = (

let uu____4394 = (push env)
in (prep uu____4394))
in ((uu____4393), (true)));
)
end))))


let enter_monad_scope : env  ->  FStar_Ident.ident  ->  env = (fun env mname -> (match (env.curmonad) with
| Some (mname') -> begin
(Prims.raise (FStar_Errors.Error ((((Prims.strcat "Trying to define monad " (Prims.strcat mname.FStar_Ident.idText (Prims.strcat ", but already in monad scope " mname'.FStar_Ident.idText)))), (mname.FStar_Ident.idRange)))))
end
| None -> begin
(

let uu___180_4402 = env
in {curmodule = uu___180_4402.curmodule; curmonad = Some (mname); modules = uu___180_4402.modules; scope_mods = uu___180_4402.scope_mods; exported_ids = uu___180_4402.exported_ids; trans_exported_ids = uu___180_4402.trans_exported_ids; includes = uu___180_4402.includes; sigaccum = uu___180_4402.sigaccum; sigmap = uu___180_4402.sigmap; iface = uu___180_4402.iface; admitted_iface = uu___180_4402.admitted_iface; expect_typ = uu___180_4402.expect_typ})
end))


let fail_or = (fun env lookup lid -> (

let uu____4427 = (lookup lid)
in (match (uu____4427) with
| None -> begin
(

let opened_modules = (FStar_List.map (fun uu____4433 -> (match (uu____4433) with
| (lid1, uu____4437) -> begin
(FStar_Ident.text_of_lid lid1)
end)) env.modules)
in (

let msg = (FStar_Util.format1 "Identifier not found: [%s]" (FStar_Ident.text_of_lid lid))
in (

let msg1 = (match (((FStar_List.length lid.FStar_Ident.ns) = (Prims.parse_int "0"))) with
| true -> begin
msg
end
| uu____4442 -> begin
(

let modul = (

let uu____4444 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in (FStar_Ident.set_lid_range uu____4444 (FStar_Ident.range_of_lid lid)))
in (

let uu____4445 = (resolve_module_name env modul true)
in (match (uu____4445) with
| None -> begin
(

let opened_modules1 = (FStar_String.concat ", " opened_modules)
in (FStar_Util.format3 "%s\nModule %s does not belong to the list of modules in scope, namely %s" msg modul.FStar_Ident.str opened_modules1))
end
| Some (modul') when (not ((FStar_List.existsb (fun m -> (m = modul'.FStar_Ident.str)) opened_modules))) -> begin
(

let opened_modules1 = (FStar_String.concat ", " opened_modules)
in (FStar_Util.format4 "%s\nModule %s resolved into %s, which does not belong to the list of modules in scope, namely %s" msg modul.FStar_Ident.str modul'.FStar_Ident.str opened_modules1))
end
| Some (modul') -> begin
(FStar_Util.format4 "%s\nModule %s resolved into %s, definition %s not found" msg modul.FStar_Ident.str modul'.FStar_Ident.str lid.FStar_Ident.ident.FStar_Ident.idText)
end)))
end)
in (Prims.raise (FStar_Errors.Error (((msg1), ((FStar_Ident.range_of_lid lid)))))))))
end
| Some (r) -> begin
r
end)))


let fail_or2 = (fun lookup id -> (

let uu____4472 = (lookup id)
in (match (uu____4472) with
| None -> begin
(Prims.raise (FStar_Errors.Error ((((Prims.strcat "Identifier not found [" (Prims.strcat id.FStar_Ident.idText "]"))), (id.FStar_Ident.idRange)))))
end
| Some (r) -> begin
r
end)))




