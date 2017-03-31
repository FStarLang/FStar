
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

let uu___175_444 = bv.FStar_Syntax_Syntax.ppname
in {FStar_Ident.idText = uu___175_444.FStar_Ident.idText; FStar_Ident.idRange = r})
in (

let uu___176_445 = bv
in {FStar_Syntax_Syntax.ppname = id; FStar_Syntax_Syntax.index = uu___176_445.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu___176_445.FStar_Syntax_Syntax.sort})))


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


let option_of_cont = (fun k_ignore uu___144_590 -> (match (uu___144_590) with
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


let string_of_exported_id_kind : exported_id_kind  ->  Prims.string = (fun uu___145_676 -> (match (uu___145_676) with
| Exported_id_field -> begin
"field"
end
| Exported_id_term_type -> begin
"term/type"
end))


let find_in_module_with_includes = (fun eikind find_in_module find_in_module_default env ns id -> (

let idstr = id.FStar_Ident.idText
in (

let rec aux = (fun uu___146_725 -> (match (uu___146_725) with
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


let is_exported_id_field : exported_id_kind  ->  Prims.bool = (fun uu___147_783 -> (match (uu___147_783) with
| Exported_id_field -> begin
true
end
| uu____784 -> begin
false
end))


let try_lookup_id'' = (fun env id eikind k_local_binding k_rec_binding k_record find_in_module lookup_default_id -> (

let check_local_binding_id = (fun uu___148_873 -> (match (uu___148_873) with
| (id', uu____875, uu____876) -> begin
(id'.FStar_Ident.idText = id.FStar_Ident.idText)
end))
in (

let check_rec_binding_id = (fun uu___149_880 -> (match (uu___149_880) with
| (id', uu____882, uu____883) -> begin
(id'.FStar_Ident.idText = id.FStar_Ident.idText)
end))
in (

let curmod_ns = (

let uu____886 = (current_module env)
in (FStar_Ident.ids_of_lid uu____886))
in (

let proc = (fun uu___150_891 -> (match (uu___150_891) with
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

let rec aux = (fun uu___151_908 -> (match (uu___151_908) with
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

let rec aux = (fun uu___152_1162 -> (match (uu___152_1162) with
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


let namespace_is_open : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (FStar_List.existsb (fun uu___153_1196 -> (match (uu___153_1196) with
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


let cont_of_option = (fun k_none uu___154_1451 -> (match (uu___154_1451) with
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


let fv_qual_of_se : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.fv_qual Prims.option = (fun uu___156_1560 -> (match (uu___156_1560) with
| FStar_Syntax_Syntax.Sig_datacon (uu____1562, uu____1563, uu____1564, l, uu____1566, quals, uu____1568, uu____1569) -> begin
(

let qopt = (FStar_Util.find_map quals (fun uu___155_1576 -> (match (uu___155_1576) with
| FStar_Syntax_Syntax.RecordConstructor (uu____1578, fs) -> begin
Some (FStar_Syntax_Syntax.Record_ctor (((l), (fs))))
end
| uu____1585 -> begin
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
| FStar_Syntax_Syntax.Sig_declare_typ (uu____1589, uu____1590, uu____1591, quals, uu____1593) -> begin
None
end
| uu____1596 -> begin
None
end))


let lb_fv : FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.fv = (fun lbs lid -> (

let uu____1605 = (FStar_Util.find_map lbs (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let uu____1609 = (FStar_Syntax_Syntax.fv_eq_lid fv lid)
in (match (uu____1609) with
| true -> begin
Some (fv)
end
| uu____1611 -> begin
None
end)))))
in (FStar_All.pipe_right uu____1605 FStar_Util.must)))


let ns_of_lid_equals : FStar_Ident.lident  ->  FStar_Ident.lident  ->  Prims.bool = (fun lid ns -> (((FStar_List.length lid.FStar_Ident.ns) = (FStar_List.length (FStar_Ident.ids_of_lid ns))) && (

let uu____1623 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in (FStar_Ident.lid_equals uu____1623 ns))))


let try_lookup_name : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  foundname Prims.option = (fun any_val exclude_interf env lid -> (

let occurrence_range = (FStar_Ident.range_of_lid lid)
in (

let k_global_def = (fun source_lid uu___160_1648 -> (match (uu___160_1648) with
| (uu____1652, true) when exclude_interf -> begin
None
end
| (se, uu____1654) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____1656) -> begin
(

let uu____1668 = (

let uu____1669 = (

let uu____1672 = (FStar_Syntax_Syntax.fvar source_lid FStar_Syntax_Syntax.Delta_constant None)
in ((uu____1672), (false)))
in Term_name (uu____1669))
in Some (uu____1668))
end
| FStar_Syntax_Syntax.Sig_datacon (uu____1673) -> begin
(

let uu____1684 = (

let uu____1685 = (

let uu____1688 = (

let uu____1689 = (fv_qual_of_se se)
in (FStar_Syntax_Syntax.fvar source_lid FStar_Syntax_Syntax.Delta_constant uu____1689))
in ((uu____1688), (false)))
in Term_name (uu____1685))
in Some (uu____1684))
end
| FStar_Syntax_Syntax.Sig_let ((uu____1691, lbs), uu____1693, uu____1694, uu____1695, uu____1696) -> begin
(

let fv = (lb_fv lbs source_lid)
in (

let uu____1709 = (

let uu____1710 = (

let uu____1713 = (FStar_Syntax_Syntax.fvar source_lid fv.FStar_Syntax_Syntax.fv_delta fv.FStar_Syntax_Syntax.fv_qual)
in ((uu____1713), (false)))
in Term_name (uu____1710))
in Some (uu____1709)))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid1, uu____1715, uu____1716, quals, uu____1718) -> begin
(

let uu____1721 = (any_val || (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___157_1723 -> (match (uu___157_1723) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| uu____1724 -> begin
false
end)))))
in (match (uu____1721) with
| true -> begin
(

let lid2 = (FStar_Ident.set_lid_range lid1 (FStar_Ident.range_of_lid source_lid))
in (

let dd = (

let uu____1728 = ((FStar_Syntax_Util.is_primop_lid lid2) || ((ns_of_lid_equals lid2 FStar_Syntax_Const.prims_lid) && (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___158_1730 -> (match (uu___158_1730) with
| (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) -> begin
true
end
| uu____1733 -> begin
false
end))))))
in (match (uu____1728) with
| true -> begin
FStar_Syntax_Syntax.Delta_equational
end
| uu____1734 -> begin
FStar_Syntax_Syntax.Delta_constant
end))
in (

let uu____1735 = (FStar_Util.find_map quals (fun uu___159_1737 -> (match (uu___159_1737) with
| FStar_Syntax_Syntax.Reflectable (refl_monad) -> begin
Some (refl_monad)
end
| uu____1740 -> begin
None
end)))
in (match (uu____1735) with
| Some (refl_monad) -> begin
(

let refl_const = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (refl_monad)))) None occurrence_range)
in Some (Term_name (((refl_const), (false)))))
end
| uu____1756 -> begin
(

let uu____1758 = (

let uu____1759 = (

let uu____1762 = (

let uu____1763 = (fv_qual_of_se se)
in (FStar_Syntax_Syntax.fvar lid2 dd uu____1763))
in ((uu____1762), (false)))
in Term_name (uu____1759))
in Some (uu____1758))
end))))
end
| uu____1765 -> begin
None
end))
end
| (FStar_Syntax_Syntax.Sig_new_effect_for_free (ne, _)) | (FStar_Syntax_Syntax.Sig_new_effect (ne, _)) -> begin
Some (Eff_name (((se), ((FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname (FStar_Ident.range_of_lid source_lid))))))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (uu____1769) -> begin
Some (Eff_name (((se), (source_lid))))
end
| uu____1779 -> begin
None
end)
end))
in (

let k_local_binding = (fun r -> (

let uu____1791 = (

let uu____1792 = (found_local_binding (FStar_Ident.range_of_lid lid) r)
in Term_name (uu____1792))
in Some (uu____1791)))
in (

let k_rec_binding = (fun uu____1802 -> (match (uu____1802) with
| (id, l, dd) -> begin
(

let uu____1810 = (

let uu____1811 = (

let uu____1814 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range l (FStar_Ident.range_of_lid lid)) dd None)
in ((uu____1814), (false)))
in Term_name (uu____1811))
in Some (uu____1810))
end))
in (

let found_unmangled = (match (lid.FStar_Ident.ns) with
| [] -> begin
(

let uu____1818 = (unmangleOpName lid.FStar_Ident.ident)
in (match (uu____1818) with
| Some (f) -> begin
Some (Term_name (f))
end
| uu____1828 -> begin
None
end))
end
| uu____1832 -> begin
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

let uu____1852 = (try_lookup_name true exclude_interf env lid)
in (match (uu____1852) with
| Some (Eff_name (o, l)) -> begin
Some (((o), (l)))
end
| uu____1861 -> begin
None
end)))


let try_lookup_effect_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env l -> (

let uu____1872 = (try_lookup_effect_name' (not (env.iface)) env l)
in (match (uu____1872) with
| Some (o, l1) -> begin
Some (l1)
end
| uu____1881 -> begin
None
end)))


let try_lookup_effect_name_and_attributes : env  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.cflags Prims.list) Prims.option = (fun env l -> (

let uu____1895 = (try_lookup_effect_name' (not (env.iface)) env l)
in (match (uu____1895) with
| Some (FStar_Syntax_Syntax.Sig_new_effect (ne, uu____1904), l1) -> begin
Some (((l1), (ne.FStar_Syntax_Syntax.cattributes)))
end
| Some (FStar_Syntax_Syntax.Sig_new_effect_for_free (ne, uu____1913), l1) -> begin
Some (((l1), (ne.FStar_Syntax_Syntax.cattributes)))
end
| Some (FStar_Syntax_Syntax.Sig_effect_abbrev (uu____1921, uu____1922, uu____1923, uu____1924, uu____1925, cattributes, uu____1927), l1) -> begin
Some (((l1), (cattributes)))
end
| uu____1939 -> begin
None
end)))


let try_lookup_effect_defn : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl Prims.option = (fun env l -> (

let uu____1953 = (try_lookup_effect_name' (not (env.iface)) env l)
in (match (uu____1953) with
| Some (FStar_Syntax_Syntax.Sig_new_effect (ne, uu____1959), uu____1960) -> begin
Some (ne)
end
| Some (FStar_Syntax_Syntax.Sig_new_effect_for_free (ne, uu____1964), uu____1965) -> begin
Some (ne)
end
| uu____1968 -> begin
None
end)))


let is_effect_name : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let uu____1978 = (try_lookup_effect_name env lid)
in (match (uu____1978) with
| None -> begin
false
end
| Some (uu____1980) -> begin
true
end)))


let try_lookup_root_effect_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env l -> (

let uu____1988 = (try_lookup_effect_name' (not (env.iface)) env l)
in (match (uu____1988) with
| Some (FStar_Syntax_Syntax.Sig_effect_abbrev (l', uu____1994, uu____1995, uu____1996, uu____1997, uu____1998, uu____1999), uu____2000) -> begin
(

let rec aux = (fun new_name -> (

let uu____2012 = (FStar_Util.smap_try_find (sigmap env) new_name.FStar_Ident.str)
in (match (uu____2012) with
| None -> begin
None
end
| Some (s, uu____2022) -> begin
(match (s) with
| (FStar_Syntax_Syntax.Sig_new_effect_for_free (ne, _)) | (FStar_Syntax_Syntax.Sig_new_effect (ne, _)) -> begin
Some ((FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname (FStar_Ident.range_of_lid l)))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (uu____2029, uu____2030, uu____2031, cmp, uu____2033, uu____2034, uu____2035) -> begin
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

let k_global_def = (fun lid1 uu___161_2067 -> (match (uu___161_2067) with
| (FStar_Syntax_Syntax.Sig_declare_typ (lid2, uu____2073, uu____2074, quals, uu____2076), uu____2077) -> begin
Some (quals)
end
| uu____2081 -> begin
None
end))
in (

let uu____2085 = (resolve_in_open_namespaces' env lid (fun uu____2089 -> None) (fun uu____2091 -> None) k_global_def)
in (match (uu____2085) with
| Some (quals) -> begin
quals
end
| uu____2097 -> begin
[]
end))))


let try_lookup_module : env  ->  Prims.string Prims.list  ->  FStar_Syntax_Syntax.modul Prims.option = (fun env path -> (

let uu____2109 = (FStar_List.tryFind (fun uu____2115 -> (match (uu____2115) with
| (mlid, modul) -> begin
(

let uu____2120 = (FStar_Ident.path_of_lid mlid)
in (uu____2120 = path))
end)) env.modules)
in (match (uu____2109) with
| Some (uu____2124, modul) -> begin
Some (modul)
end
| None -> begin
None
end)))


let try_lookup_let : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env lid -> (

let k_global_def = (fun lid1 uu___162_2146 -> (match (uu___162_2146) with
| (FStar_Syntax_Syntax.Sig_let ((uu____2150, lbs), uu____2152, uu____2153, uu____2154, uu____2155), uu____2156) -> begin
(

let fv = (lb_fv lbs lid1)
in (

let uu____2169 = (FStar_Syntax_Syntax.fvar lid1 fv.FStar_Syntax_Syntax.fv_delta fv.FStar_Syntax_Syntax.fv_qual)
in Some (uu____2169)))
end
| uu____2170 -> begin
None
end))
in (resolve_in_open_namespaces' env lid (fun uu____2173 -> None) (fun uu____2174 -> None) k_global_def)))


let try_lookup_definition : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env lid -> (

let k_global_def = (fun lid1 uu___163_2193 -> (match (uu___163_2193) with
| (FStar_Syntax_Syntax.Sig_let (lbs, uu____2200, uu____2201, uu____2202, uu____2203), uu____2204) -> begin
(FStar_Util.find_map (Prims.snd lbs) (fun lb -> (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv lid1) -> begin
Some (lb.FStar_Syntax_Syntax.lbdef)
end
| uu____2221 -> begin
None
end)))
end
| uu____2226 -> begin
None
end))
in (resolve_in_open_namespaces' env lid (fun uu____2233 -> None) (fun uu____2236 -> None) k_global_def)))


let empty_include_smap : FStar_Ident.lident Prims.list FStar_ST.ref FStar_Util.smap = (new_sigmap ())


let empty_exported_id_smap : exported_id_set FStar_Util.smap = (new_sigmap ())


let try_lookup_lid' : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term * Prims.bool) Prims.option = (fun any_val exclude_interf env lid -> (

let uu____2263 = (try_lookup_name any_val exclude_interf env lid)
in (match (uu____2263) with
| Some (Term_name (e, mut)) -> begin
Some (((e), (mut)))
end
| uu____2272 -> begin
None
end)))


let try_lookup_lid : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term * Prims.bool) Prims.option = (fun env l -> (try_lookup_lid' env.iface false env l))


let resolve_to_fully_qualified_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env l -> (

let uu____2292 = (try_lookup_lid env l)
in (match (uu____2292) with
| None -> begin
None
end
| Some (e, uu____2300) -> begin
(

let uu____2303 = (

let uu____2304 = (FStar_Syntax_Subst.compress e)
in uu____2304.FStar_Syntax_Syntax.n)
in (match (uu____2303) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
Some (fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end
| uu____2313 -> begin
None
end))
end)))


let try_lookup_lid_no_resolve : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term * Prims.bool) Prims.option = (fun env l -> (

let env' = (

let uu___177_2324 = env
in {curmodule = uu___177_2324.curmodule; curmonad = uu___177_2324.curmonad; modules = uu___177_2324.modules; scope_mods = []; exported_ids = empty_exported_id_smap; trans_exported_ids = uu___177_2324.trans_exported_ids; includes = empty_include_smap; sigaccum = uu___177_2324.sigaccum; sigmap = uu___177_2324.sigmap; iface = uu___177_2324.iface; admitted_iface = uu___177_2324.admitted_iface; expect_typ = uu___177_2324.expect_typ})
in (try_lookup_lid env' l)))


let try_lookup_datacon : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.fv Prims.option = (fun env lid -> (

let k_global_def = (fun lid1 uu___165_2341 -> (match (uu___165_2341) with
| (FStar_Syntax_Syntax.Sig_declare_typ (uu____2345, uu____2346, uu____2347, quals, uu____2349), uu____2350) -> begin
(

let uu____2353 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___164_2355 -> (match (uu___164_2355) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| uu____2356 -> begin
false
end))))
in (match (uu____2353) with
| true -> begin
(

let uu____2358 = (FStar_Syntax_Syntax.lid_as_fv lid1 FStar_Syntax_Syntax.Delta_constant None)
in Some (uu____2358))
end
| uu____2359 -> begin
None
end))
end
| (FStar_Syntax_Syntax.Sig_datacon (uu____2360), uu____2361) -> begin
(

let uu____2372 = (FStar_Syntax_Syntax.lid_as_fv lid1 FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in Some (uu____2372))
end
| uu____2373 -> begin
None
end))
in (resolve_in_open_namespaces' env lid (fun uu____2376 -> None) (fun uu____2377 -> None) k_global_def)))


let find_all_datacons : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.list Prims.option = (fun env lid -> (

let k_global_def = (fun lid1 uu___166_2396 -> (match (uu___166_2396) with
| (FStar_Syntax_Syntax.Sig_inductive_typ (uu____2401, uu____2402, uu____2403, uu____2404, uu____2405, datas, uu____2407, uu____2408), uu____2409) -> begin
Some (datas)
end
| uu____2417 -> begin
None
end))
in (resolve_in_open_namespaces' env lid (fun uu____2422 -> None) (fun uu____2424 -> None) k_global_def)))


let record_cache_aux_with_filter : (((Prims.unit  ->  Prims.unit) * (Prims.unit  ->  Prims.unit) * (Prims.unit  ->  record_or_dc Prims.list) * (record_or_dc  ->  Prims.unit) * (Prims.unit  ->  Prims.unit)) * (Prims.unit  ->  Prims.unit)) = (

let record_cache = (FStar_Util.mk_ref (([])::[]))
in (

let push1 = (fun uu____2458 -> (

let uu____2459 = (

let uu____2462 = (

let uu____2464 = (FStar_ST.read record_cache)
in (FStar_List.hd uu____2464))
in (

let uu____2472 = (FStar_ST.read record_cache)
in (uu____2462)::uu____2472))
in (FStar_ST.write record_cache uu____2459)))
in (

let pop1 = (fun uu____2487 -> (

let uu____2488 = (

let uu____2491 = (FStar_ST.read record_cache)
in (FStar_List.tl uu____2491))
in (FStar_ST.write record_cache uu____2488)))
in (

let peek = (fun uu____2507 -> (

let uu____2508 = (FStar_ST.read record_cache)
in (FStar_List.hd uu____2508)))
in (

let insert = (fun r -> (

let uu____2520 = (

let uu____2523 = (

let uu____2525 = (peek ())
in (r)::uu____2525)
in (

let uu____2527 = (

let uu____2530 = (FStar_ST.read record_cache)
in (FStar_List.tl uu____2530))
in (uu____2523)::uu____2527))
in (FStar_ST.write record_cache uu____2520)))
in (

let commit1 = (fun uu____2546 -> (

let uu____2547 = (FStar_ST.read record_cache)
in (match (uu____2547) with
| (hd1)::(uu____2555)::tl1 -> begin
(FStar_ST.write record_cache ((hd1)::tl1))
end
| uu____2568 -> begin
(failwith "Impossible")
end)))
in (

let filter1 = (fun uu____2574 -> (

let rc = (peek ())
in ((pop1 ());
(match (()) with
| () -> begin
(

let filtered = (FStar_List.filter (fun r -> (not (r.is_private_or_abstract))) rc)
in (

let uu____2581 = (

let uu____2584 = (FStar_ST.read record_cache)
in (filtered)::uu____2584)
in (FStar_ST.write record_cache uu____2581)))
end);
)))
in (

let aux = ((push1), (pop1), (peek), (insert), (commit1))
in ((aux), (filter1))))))))))


let record_cache_aux : ((Prims.unit  ->  Prims.unit) * (Prims.unit  ->  Prims.unit) * (Prims.unit  ->  record_or_dc Prims.list) * (record_or_dc  ->  Prims.unit) * (Prims.unit  ->  Prims.unit)) = (

let uu____2658 = record_cache_aux_with_filter
in (match (uu____2658) with
| (aux, uu____2696) -> begin
aux
end))


let filter_record_cache : Prims.unit  ->  Prims.unit = (

let uu____2735 = record_cache_aux_with_filter
in (match (uu____2735) with
| (uu____2758, filter1) -> begin
filter1
end))


let push_record_cache : Prims.unit  ->  Prims.unit = (

let uu____2798 = record_cache_aux
in (match (uu____2798) with
| (push1, uu____2818, uu____2819, uu____2820, uu____2821) -> begin
push1
end))


let pop_record_cache : Prims.unit  ->  Prims.unit = (

let uu____2846 = record_cache_aux
in (match (uu____2846) with
| (uu____2865, pop1, uu____2867, uu____2868, uu____2869) -> begin
pop1
end))


let peek_record_cache : Prims.unit  ->  record_or_dc Prims.list = (

let uu____2895 = record_cache_aux
in (match (uu____2895) with
| (uu____2915, uu____2916, peek, uu____2918, uu____2919) -> begin
peek
end))


let insert_record_cache : record_or_dc  ->  Prims.unit = (

let uu____2944 = record_cache_aux
in (match (uu____2944) with
| (uu____2963, uu____2964, uu____2965, insert, uu____2967) -> begin
insert
end))


let commit_record_cache : Prims.unit  ->  Prims.unit = (

let uu____2992 = record_cache_aux
in (match (uu____2992) with
| (uu____3011, uu____3012, uu____3013, uu____3014, commit1) -> begin
commit1
end))


let extract_record : env  ->  scope_mod Prims.list FStar_ST.ref  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun e new_globs uu___170_3049 -> (match (uu___170_3049) with
| FStar_Syntax_Syntax.Sig_bundle (sigs, uu____3054, uu____3055, uu____3056) -> begin
(

let is_rec = (FStar_Util.for_some (fun uu___167_3067 -> (match (uu___167_3067) with
| (FStar_Syntax_Syntax.RecordType (_)) | (FStar_Syntax_Syntax.RecordConstructor (_)) -> begin
true
end
| uu____3070 -> begin
false
end)))
in (

let find_dc = (fun dc -> (FStar_All.pipe_right sigs (FStar_Util.find_opt (fun uu___168_3078 -> (match (uu___168_3078) with
| FStar_Syntax_Syntax.Sig_datacon (lid, uu____3080, uu____3081, uu____3082, uu____3083, uu____3084, uu____3085, uu____3086) -> begin
(FStar_Ident.lid_equals dc lid)
end
| uu____3091 -> begin
false
end)))))
in (FStar_All.pipe_right sigs (FStar_List.iter (fun uu___169_3093 -> (match (uu___169_3093) with
| FStar_Syntax_Syntax.Sig_inductive_typ (typename, univs, parms, uu____3097, uu____3098, (dc)::[], tags, uu____3101) -> begin
(

let uu____3107 = (

let uu____3108 = (find_dc dc)
in (FStar_All.pipe_left FStar_Util.must uu____3108))
in (match (uu____3107) with
| FStar_Syntax_Syntax.Sig_datacon (constrname, uu____3112, t, uu____3114, uu____3115, uu____3116, uu____3117, uu____3118) -> begin
(

let uu____3123 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____3123) with
| (formals, uu____3132) -> begin
(

let is_rec1 = (is_rec tags)
in (

let formals' = (FStar_All.pipe_right formals (FStar_List.collect (fun uu____3158 -> (match (uu____3158) with
| (x, q) -> begin
(

let uu____3166 = ((FStar_Syntax_Syntax.is_null_bv x) || (is_rec1 && (FStar_Syntax_Syntax.is_implicit q)))
in (match (uu____3166) with
| true -> begin
[]
end
| uu____3172 -> begin
(((x), (q)))::[]
end))
end))))
in (

let fields' = (FStar_All.pipe_right formals' (FStar_List.map (fun uu____3197 -> (match (uu____3197) with
| (x, q) -> begin
(

let uu____3206 = (match (is_rec1) with
| true -> begin
(FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname)
end
| uu____3207 -> begin
x.FStar_Syntax_Syntax.ppname
end)
in ((uu____3206), (x.FStar_Syntax_Syntax.sort)))
end))))
in (

let fields = fields'
in (

let record = {typename = typename; constrname = constrname.FStar_Ident.ident; parms = parms; fields = fields; is_private_or_abstract = ((FStar_List.contains FStar_Syntax_Syntax.Private tags) || (FStar_List.contains FStar_Syntax_Syntax.Abstract tags)); is_record = is_rec1}
in ((

let uu____3218 = (

let uu____3220 = (FStar_ST.read new_globs)
in (Record_or_dc (record))::uu____3220)
in (FStar_ST.write new_globs uu____3218));
(match (()) with
| () -> begin
((

let add_field = (fun uu____3236 -> (match (uu____3236) with
| (id, uu____3242) -> begin
(

let modul = (

let uu____3248 = (FStar_Ident.lid_of_ids constrname.FStar_Ident.ns)
in uu____3248.FStar_Ident.str)
in (

let uu____3249 = (get_exported_id_set e modul)
in (match (uu____3249) with
| Some (my_ex) -> begin
(

let my_exported_ids = (my_ex Exported_id_field)
in ((

let uu____3265 = (

let uu____3266 = (FStar_ST.read my_exported_ids)
in (FStar_Util.set_add id.FStar_Ident.idText uu____3266))
in (FStar_ST.write my_exported_ids uu____3265));
(match (()) with
| () -> begin
(

let projname = (

let uu____3273 = (

let uu____3274 = (FStar_Syntax_Util.mk_field_projector_name_from_ident constrname id)
in uu____3274.FStar_Ident.ident)
in uu____3273.FStar_Ident.idText)
in (

let uu____3276 = (

let uu____3277 = (FStar_ST.read my_exported_ids)
in (FStar_Util.set_add projname uu____3277))
in (FStar_ST.write my_exported_ids uu____3276)))
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
| uu____3290 -> begin
()
end))
end
| uu____3291 -> begin
()
end))))))
end
| uu____3292 -> begin
()
end))


let try_lookup_record_or_dc_by_field_name : env  ->  FStar_Ident.lident  ->  record_or_dc Prims.option = (fun env fieldname -> (

let find_in_cache = (fun fieldname1 -> (

let uu____3305 = ((fieldname1.FStar_Ident.ns), (fieldname1.FStar_Ident.ident))
in (match (uu____3305) with
| (ns, id) -> begin
(

let uu____3315 = (peek_record_cache ())
in (FStar_Util.find_map uu____3315 (fun record -> (

let uu____3318 = (find_in_record ns id record (fun r -> Cont_ok (r)))
in (option_of_cont (fun uu____3321 -> None) uu____3318)))))
end)))
in (resolve_in_open_namespaces'' env fieldname Exported_id_field (fun uu____3322 -> Cont_ignore) (fun uu____3323 -> Cont_ignore) (fun r -> Cont_ok (r)) (fun fn -> (

let uu____3326 = (find_in_cache fn)
in (cont_of_option Cont_ignore uu____3326))) (fun k uu____3329 -> k))))


let try_lookup_record_by_field_name : env  ->  FStar_Ident.lident  ->  record_or_dc Prims.option = (fun env fieldname -> (

let uu____3338 = (try_lookup_record_or_dc_by_field_name env fieldname)
in (match (uu____3338) with
| Some (r) when r.is_record -> begin
Some (r)
end
| uu____3342 -> begin
None
end)))


let belongs_to_record : env  ->  FStar_Ident.lident  ->  record_or_dc  ->  Prims.bool = (fun env lid record -> (

let uu____3353 = (try_lookup_record_by_field_name env lid)
in (match (uu____3353) with
| Some (record') when (

let uu____3356 = (

let uu____3357 = (FStar_Ident.path_of_ns record.typename.FStar_Ident.ns)
in (FStar_Ident.text_of_path uu____3357))
in (

let uu____3359 = (

let uu____3360 = (FStar_Ident.path_of_ns record'.typename.FStar_Ident.ns)
in (FStar_Ident.text_of_path uu____3360))
in (uu____3356 = uu____3359))) -> begin
(

let uu____3362 = (find_in_record record.typename.FStar_Ident.ns lid.FStar_Ident.ident record (fun uu____3364 -> Cont_ok (())))
in (match (uu____3362) with
| Cont_ok (uu____3365) -> begin
true
end
| uu____3366 -> begin
false
end))
end
| uu____3368 -> begin
false
end)))


let try_lookup_dc_by_field_name : env  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * Prims.bool) Prims.option = (fun env fieldname -> (

let uu____3379 = (try_lookup_record_or_dc_by_field_name env fieldname)
in (match (uu____3379) with
| Some (r) -> begin
(

let uu____3385 = (

let uu____3388 = (

let uu____3389 = (FStar_Ident.lid_of_ids (FStar_List.append r.typename.FStar_Ident.ns ((r.constrname)::[])))
in (FStar_Ident.set_lid_range uu____3389 (FStar_Ident.range_of_lid fieldname)))
in ((uu____3388), (r.is_record)))
in Some (uu____3385))
end
| uu____3392 -> begin
None
end)))


let string_set_ref_new : Prims.unit  ->  Prims.string FStar_Util.set FStar_ST.ref = (fun uu____3401 -> (

let uu____3402 = (FStar_Util.new_set FStar_Util.compare FStar_Util.hashcode)
in (FStar_Util.mk_ref uu____3402)))


let exported_id_set_new : Prims.unit  ->  exported_id_kind  ->  Prims.string FStar_Util.set FStar_ST.ref = (fun uu____3413 -> (

let term_type_set = (string_set_ref_new ())
in (

let field_set = (string_set_ref_new ())
in (fun uu___171_3422 -> (match (uu___171_3422) with
| Exported_id_term_type -> begin
term_type_set
end
| Exported_id_field -> begin
field_set
end)))))


let unique : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  Prims.bool = (fun any_val exclude_if env lid -> (

let filter_scope_mods = (fun uu___172_3442 -> (match (uu___172_3442) with
| Rec_binding (uu____3443) -> begin
true
end
| uu____3444 -> begin
false
end))
in (

let this_env = (

let uu___178_3446 = env
in (

let uu____3447 = (FStar_List.filter filter_scope_mods env.scope_mods)
in {curmodule = uu___178_3446.curmodule; curmonad = uu___178_3446.curmonad; modules = uu___178_3446.modules; scope_mods = uu____3447; exported_ids = empty_exported_id_smap; trans_exported_ids = uu___178_3446.trans_exported_ids; includes = empty_include_smap; sigaccum = uu___178_3446.sigaccum; sigmap = uu___178_3446.sigmap; iface = uu___178_3446.iface; admitted_iface = uu___178_3446.admitted_iface; expect_typ = uu___178_3446.expect_typ}))
in (

let uu____3449 = (try_lookup_lid' any_val exclude_if this_env lid)
in (match (uu____3449) with
| None -> begin
true
end
| Some (uu____3455) -> begin
false
end)))))


let push_scope_mod : env  ->  scope_mod  ->  env = (fun env scope_mod -> (

let uu___179_3466 = env
in {curmodule = uu___179_3466.curmodule; curmonad = uu___179_3466.curmonad; modules = uu___179_3466.modules; scope_mods = (scope_mod)::env.scope_mods; exported_ids = uu___179_3466.exported_ids; trans_exported_ids = uu___179_3466.trans_exported_ids; includes = uu___179_3466.includes; sigaccum = uu___179_3466.sigaccum; sigmap = uu___179_3466.sigmap; iface = uu___179_3466.iface; admitted_iface = uu___179_3466.admitted_iface; expect_typ = uu___179_3466.expect_typ}))


let push_bv' : env  ->  FStar_Ident.ident  ->  Prims.bool  ->  (env * FStar_Syntax_Syntax.bv) = (fun env x is_mutable -> (

let bv = (FStar_Syntax_Syntax.gen_bv x.FStar_Ident.idText (Some (x.FStar_Ident.idRange)) FStar_Syntax_Syntax.tun)
in (((push_scope_mod env (Local_binding (((x), (bv), (is_mutable)))))), (bv))))


let push_bv_mutable : env  ->  FStar_Ident.ident  ->  (env * FStar_Syntax_Syntax.bv) = (fun env x -> (push_bv' env x true))


let push_bv : env  ->  FStar_Ident.ident  ->  (env * FStar_Syntax_Syntax.bv) = (fun env x -> (push_bv' env x false))


let push_top_level_rec_binding : env  ->  FStar_Ident.ident  ->  FStar_Syntax_Syntax.delta_depth  ->  env = (fun env x dd -> (

let l = (qualify env x)
in (

let uu____3505 = ((unique false true env l) || (FStar_Options.interactive ()))
in (match (uu____3505) with
| true -> begin
(push_scope_mod env (Rec_binding (((x), (l), (dd)))))
end
| uu____3506 -> begin
(Prims.raise (FStar_Errors.Error ((((Prims.strcat "Duplicate top-level names " l.FStar_Ident.str)), ((FStar_Ident.range_of_lid l))))))
end))))


let push_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env s -> (

let err = (fun l -> (

let sopt = (FStar_Util.smap_try_find (sigmap env) l.FStar_Ident.str)
in (

let r = (match (sopt) with
| Some (se, uu____3525) -> begin
(

let uu____3528 = (FStar_Util.find_opt (FStar_Ident.lid_equals l) (FStar_Syntax_Util.lids_of_sigelt se))
in (match (uu____3528) with
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

let uu____3533 = (

let uu____3534 = (

let uu____3537 = (FStar_Util.format2 "Duplicate top-level names [%s]; previously declared at %s" (FStar_Ident.text_of_lid l) r)
in ((uu____3537), ((FStar_Ident.range_of_lid l))))
in FStar_Errors.Error (uu____3534))
in (Prims.raise uu____3533)))))
in (

let globals = (FStar_Util.mk_ref env.scope_mods)
in (

let env1 = (

let uu____3544 = (match (s) with
| FStar_Syntax_Syntax.Sig_let (uu____3549) -> begin
((false), (true))
end
| FStar_Syntax_Syntax.Sig_bundle (uu____3558) -> begin
((true), (true))
end
| uu____3566 -> begin
((false), (false))
end)
in (match (uu____3544) with
| (any_val, exclude_if) -> begin
(

let lids = (FStar_Syntax_Util.lids_of_sigelt s)
in (

let uu____3571 = (FStar_Util.find_map lids (fun l -> (

let uu____3574 = (

let uu____3575 = (unique any_val exclude_if env l)
in (not (uu____3575)))
in (match (uu____3574) with
| true -> begin
Some (l)
end
| uu____3577 -> begin
None
end))))
in (match (uu____3571) with
| Some (l) when (

let uu____3579 = (FStar_Options.interactive ())
in (not (uu____3579))) -> begin
(err l)
end
| uu____3580 -> begin
((extract_record env globals s);
(

let uu___180_3585 = env
in {curmodule = uu___180_3585.curmodule; curmonad = uu___180_3585.curmonad; modules = uu___180_3585.modules; scope_mods = uu___180_3585.scope_mods; exported_ids = uu___180_3585.exported_ids; trans_exported_ids = uu___180_3585.trans_exported_ids; includes = uu___180_3585.includes; sigaccum = (s)::env.sigaccum; sigmap = uu___180_3585.sigmap; iface = uu___180_3585.iface; admitted_iface = uu___180_3585.admitted_iface; expect_typ = uu___180_3585.expect_typ});
)
end)))
end))
in (

let env2 = (

let uu___181_3587 = env1
in (

let uu____3588 = (FStar_ST.read globals)
in {curmodule = uu___181_3587.curmodule; curmonad = uu___181_3587.curmonad; modules = uu___181_3587.modules; scope_mods = uu____3588; exported_ids = uu___181_3587.exported_ids; trans_exported_ids = uu___181_3587.trans_exported_ids; includes = uu___181_3587.includes; sigaccum = uu___181_3587.sigaccum; sigmap = uu___181_3587.sigmap; iface = uu___181_3587.iface; admitted_iface = uu___181_3587.admitted_iface; expect_typ = uu___181_3587.expect_typ}))
in (

let uu____3593 = (match (s) with
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____3607, uu____3608, uu____3609) -> begin
(

let uu____3616 = (FStar_List.map (fun se -> (((FStar_Syntax_Util.lids_of_sigelt se)), (se))) ses)
in ((env2), (uu____3616)))
end
| uu____3630 -> begin
((env2), (((((FStar_Syntax_Util.lids_of_sigelt s)), (s)))::[]))
end)
in (match (uu____3593) with
| (env3, lss) -> begin
((FStar_All.pipe_right lss (FStar_List.iter (fun uu____3660 -> (match (uu____3660) with
| (lids, se) -> begin
(FStar_All.pipe_right lids (FStar_List.iter (fun lid -> ((

let uu____3671 = (

let uu____3673 = (FStar_ST.read globals)
in (Top_level_def (lid.FStar_Ident.ident))::uu____3673)
in (FStar_ST.write globals uu____3671));
(match (()) with
| () -> begin
(

let modul = (

let uu____3682 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in uu____3682.FStar_Ident.str)
in ((

let uu____3684 = (get_exported_id_set env3 modul)
in (match (uu____3684) with
| Some (f) -> begin
(

let my_exported_ids = (f Exported_id_term_type)
in (

let uu____3699 = (

let uu____3700 = (FStar_ST.read my_exported_ids)
in (FStar_Util.set_add lid.FStar_Ident.ident.FStar_Ident.idText uu____3700))
in (FStar_ST.write my_exported_ids uu____3699)))
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

let uu___182_3712 = env3
in (

let uu____3713 = (FStar_ST.read globals)
in {curmodule = uu___182_3712.curmodule; curmonad = uu___182_3712.curmonad; modules = uu___182_3712.modules; scope_mods = uu____3713; exported_ids = uu___182_3712.exported_ids; trans_exported_ids = uu___182_3712.trans_exported_ids; includes = uu___182_3712.includes; sigaccum = uu___182_3712.sigaccum; sigmap = uu___182_3712.sigmap; iface = uu___182_3712.iface; admitted_iface = uu___182_3712.admitted_iface; expect_typ = uu___182_3712.expect_typ}))
in env4);
)
end)))))))


let push_namespace : env  ->  FStar_Ident.lident  ->  env = (fun env ns -> (

let uu____3724 = (

let uu____3727 = (resolve_module_name env ns false)
in (match (uu____3727) with
| None -> begin
(

let modules = env.modules
in (

let uu____3735 = (FStar_All.pipe_right modules (FStar_Util.for_some (fun uu____3741 -> (match (uu____3741) with
| (m, uu____3745) -> begin
(FStar_Util.starts_with (Prims.strcat (FStar_Ident.text_of_lid m) ".") (Prims.strcat (FStar_Ident.text_of_lid ns) "."))
end))))
in (match (uu____3735) with
| true -> begin
((ns), (Open_namespace))
end
| uu____3748 -> begin
(

let uu____3749 = (

let uu____3750 = (

let uu____3753 = (FStar_Util.format1 "Namespace %s cannot be found" (FStar_Ident.text_of_lid ns))
in ((uu____3753), ((FStar_Ident.range_of_lid ns))))
in FStar_Errors.Error (uu____3750))
in (Prims.raise uu____3749))
end)))
end
| Some (ns') -> begin
((ns'), (Open_module))
end))
in (match (uu____3724) with
| (ns', kd) -> begin
(push_scope_mod env (Open_module_or_namespace (((ns'), (kd)))))
end)))


let push_include : env  ->  FStar_Ident.lident  ->  env = (fun env ns -> (

let uu____3765 = (resolve_module_name env ns false)
in (match (uu____3765) with
| Some (ns1) -> begin
(

let env1 = (push_scope_mod env (Open_module_or_namespace (((ns1), (Open_module)))))
in (

let curmod = (

let uu____3770 = (current_module env1)
in uu____3770.FStar_Ident.str)
in ((

let uu____3772 = (FStar_Util.smap_try_find env1.includes curmod)
in (match (uu____3772) with
| None -> begin
()
end
| Some (incl) -> begin
(

let uu____3785 = (

let uu____3787 = (FStar_ST.read incl)
in (ns1)::uu____3787)
in (FStar_ST.write incl uu____3785))
end));
(match (()) with
| () -> begin
(

let uu____3795 = (get_trans_exported_id_set env1 ns1.FStar_Ident.str)
in (match (uu____3795) with
| Some (ns_trans_exports) -> begin
((

let uu____3808 = (

let uu____3819 = (get_exported_id_set env1 curmod)
in (

let uu____3824 = (get_trans_exported_id_set env1 curmod)
in ((uu____3819), (uu____3824))))
in (match (uu____3808) with
| (Some (cur_exports), Some (cur_trans_exports)) -> begin
(

let update_exports = (fun k -> (

let ns_ex = (

let uu____3864 = (ns_trans_exports k)
in (FStar_ST.read uu____3864))
in (

let ex = (cur_exports k)
in ((

let uu____3873 = (

let uu____3874 = (FStar_ST.read ex)
in (FStar_Util.set_difference uu____3874 ns_ex))
in (FStar_ST.write ex uu____3873));
(match (()) with
| () -> begin
(

let trans_ex = (cur_trans_exports k)
in (

let uu____3884 = (

let uu____3885 = (FStar_ST.read trans_ex)
in (FStar_Util.set_union uu____3885 ns_ex))
in (FStar_ST.write trans_ex uu____3884)))
end);
))))
in (FStar_List.iter update_exports all_exported_id_kinds))
end
| uu____3891 -> begin
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

let uu____3905 = (

let uu____3906 = (

let uu____3909 = (FStar_Util.format1 "include: Module %s was not prepared" ns1.FStar_Ident.str)
in ((uu____3909), ((FStar_Ident.range_of_lid ns1))))
in FStar_Errors.Error (uu____3906))
in (Prims.raise uu____3905))
end))
end);
)))
end
| uu____3910 -> begin
(

let uu____3912 = (

let uu____3913 = (

let uu____3916 = (FStar_Util.format1 "include: Module %s cannot be found" ns.FStar_Ident.str)
in ((uu____3916), ((FStar_Ident.range_of_lid ns))))
in FStar_Errors.Error (uu____3913))
in (Prims.raise uu____3912))
end)))


let push_module_abbrev : env  ->  FStar_Ident.ident  ->  FStar_Ident.lident  ->  env = (fun env x l -> (

let uu____3926 = (module_is_defined env l)
in (match (uu____3926) with
| true -> begin
(push_scope_mod env (Module_abbrev (((x), (l)))))
end
| uu____3927 -> begin
(

let uu____3928 = (

let uu____3929 = (

let uu____3932 = (FStar_Util.format1 "Module %s cannot be found" (FStar_Ident.text_of_lid l))
in ((uu____3932), ((FStar_Ident.range_of_lid l))))
in FStar_Errors.Error (uu____3929))
in (Prims.raise uu____3928))
end)))


let check_admits : env  ->  Prims.unit = (fun env -> (FStar_All.pipe_right env.sigaccum (FStar_List.iter (fun se -> (match (se) with
| FStar_Syntax_Syntax.Sig_declare_typ (l, u, t, quals, r) -> begin
(

let uu____3944 = (try_lookup_lid env l)
in (match (uu____3944) with
| None -> begin
((

let uu____3951 = (

let uu____3952 = (FStar_Options.interactive ())
in (not (uu____3952)))
in (match (uu____3951) with
| true -> begin
(

let uu____3953 = (

let uu____3954 = (FStar_Range.string_of_range (FStar_Ident.range_of_lid l))
in (

let uu____3955 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format2 "%s: Warning: Admitting %s without a definition\n" uu____3954 uu____3955)))
in (FStar_Util.print_string uu____3953))
end
| uu____3956 -> begin
()
end));
(FStar_Util.smap_add (sigmap env) l.FStar_Ident.str ((FStar_Syntax_Syntax.Sig_declare_typ (((l), (u), (t), ((FStar_Syntax_Syntax.Assumption)::quals), (r)))), (false)));
)
end
| Some (uu____3960) -> begin
()
end))
end
| uu____3965 -> begin
()
end)))))


let finish : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env modul -> ((FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations (FStar_List.iter (fun uu___174_3973 -> (match (uu___174_3973) with
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, uu____3976, uu____3977) -> begin
(match (((FStar_List.contains FStar_Syntax_Syntax.Private quals) || (FStar_List.contains FStar_Syntax_Syntax.Abstract quals))) with
| true -> begin
(FStar_All.pipe_right ses (FStar_List.iter (fun uu___173_3985 -> (match (uu___173_3985) with
| FStar_Syntax_Syntax.Sig_datacon (lid, uu____3987, uu____3988, uu____3989, uu____3990, uu____3991, uu____3992, uu____3993) -> begin
(FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str)
end
| uu____4000 -> begin
()
end))))
end
| uu____4001 -> begin
()
end)
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____4003, uu____4004, quals, uu____4006) -> begin
(match ((FStar_List.contains FStar_Syntax_Syntax.Private quals)) with
| true -> begin
(FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str)
end
| uu____4011 -> begin
()
end)
end
| FStar_Syntax_Syntax.Sig_let ((uu____4012, lbs), r, uu____4015, quals, uu____4017) -> begin
((match (((FStar_List.contains FStar_Syntax_Syntax.Private quals) || (FStar_List.contains FStar_Syntax_Syntax.Abstract quals))) with
| true -> begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (

let uu____4032 = (

let uu____4033 = (

let uu____4034 = (

let uu____4039 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in uu____4039.FStar_Syntax_Syntax.fv_name)
in uu____4034.FStar_Syntax_Syntax.v)
in uu____4033.FStar_Ident.str)
in (FStar_Util.smap_remove (sigmap env) uu____4032)))))
end
| uu____4045 -> begin
()
end);
(match (((FStar_List.contains FStar_Syntax_Syntax.Abstract quals) && (not ((FStar_List.contains FStar_Syntax_Syntax.Private quals))))) with
| true -> begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (

let lid = (

let uu____4049 = (

let uu____4054 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in uu____4054.FStar_Syntax_Syntax.fv_name)
in uu____4049.FStar_Syntax_Syntax.v)
in (

let decl = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), ((FStar_Syntax_Syntax.Assumption)::quals), (r)))
in (FStar_Util.smap_add (sigmap env) lid.FStar_Ident.str ((decl), (false))))))))
end
| uu____4065 -> begin
()
end);
)
end
| uu____4066 -> begin
()
end))));
(

let curmod = (

let uu____4068 = (current_module env)
in uu____4068.FStar_Ident.str)
in ((

let uu____4070 = (

let uu____4081 = (get_exported_id_set env curmod)
in (

let uu____4086 = (get_trans_exported_id_set env curmod)
in ((uu____4081), (uu____4086))))
in (match (uu____4070) with
| (Some (cur_ex), Some (cur_trans_ex)) -> begin
(

let update_exports = (fun eikind -> (

let cur_ex_set = (

let uu____4126 = (cur_ex eikind)
in (FStar_ST.read uu____4126))
in (

let cur_trans_ex_set_ref = (cur_trans_ex eikind)
in (

let uu____4134 = (

let uu____4135 = (FStar_ST.read cur_trans_ex_set_ref)
in (FStar_Util.set_union cur_ex_set uu____4135))
in (FStar_ST.write cur_trans_ex_set_ref uu____4134)))))
in (FStar_List.iter update_exports all_exported_id_kinds))
end
| uu____4141 -> begin
()
end));
(match (()) with
| () -> begin
((filter_record_cache ());
(match (()) with
| () -> begin
(

let uu___183_4153 = env
in {curmodule = None; curmonad = uu___183_4153.curmonad; modules = (((modul.FStar_Syntax_Syntax.name), (modul)))::env.modules; scope_mods = []; exported_ids = uu___183_4153.exported_ids; trans_exported_ids = uu___183_4153.trans_exported_ids; includes = uu___183_4153.includes; sigaccum = []; sigmap = uu___183_4153.sigmap; iface = uu___183_4153.iface; admitted_iface = uu___183_4153.admitted_iface; expect_typ = uu___183_4153.expect_typ})
end);
)
end);
));
))


let stack : env Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let push : env  ->  env = (fun env -> ((push_record_cache ());
(

let uu____4166 = (

let uu____4168 = (FStar_ST.read stack)
in (env)::uu____4168)
in (FStar_ST.write stack uu____4166));
(

let uu___184_4176 = env
in (

let uu____4177 = (FStar_Util.smap_copy (sigmap env))
in {curmodule = uu___184_4176.curmodule; curmonad = uu___184_4176.curmonad; modules = uu___184_4176.modules; scope_mods = uu___184_4176.scope_mods; exported_ids = uu___184_4176.exported_ids; trans_exported_ids = uu___184_4176.trans_exported_ids; includes = uu___184_4176.includes; sigaccum = uu___184_4176.sigaccum; sigmap = uu____4177; iface = uu___184_4176.iface; admitted_iface = uu___184_4176.admitted_iface; expect_typ = uu___184_4176.expect_typ}));
))


let pop : Prims.unit  ->  env = (fun uu____4185 -> (

let uu____4186 = (FStar_ST.read stack)
in (match (uu____4186) with
| (env)::tl1 -> begin
((pop_record_cache ());
(FStar_ST.write stack tl1);
env;
)
end
| uu____4199 -> begin
(failwith "Impossible: Too many pops")
end)))


let commit_mark : env  ->  env = (fun env -> ((commit_record_cache ());
(

let uu____4205 = (FStar_ST.read stack)
in (match (uu____4205) with
| (uu____4210)::tl1 -> begin
((FStar_ST.write stack tl1);
env;
)
end
| uu____4217 -> begin
(failwith "Impossible: Too many pops")
end));
))


let mark : env  ->  env = (fun x -> (push x))


let reset_mark : Prims.unit  ->  env = (fun uu____4224 -> (pop ()))


let export_interface : FStar_Ident.lident  ->  env  ->  env = (fun m env -> (

let sigelt_in_m = (fun se -> (match ((FStar_Syntax_Util.lids_of_sigelt se)) with
| (l)::uu____4236 -> begin
(l.FStar_Ident.nsstr = m.FStar_Ident.str)
end
| uu____4238 -> begin
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

let uu____4256 = (FStar_Util.smap_try_find sm' k)
in (match (uu____4256) with
| Some (se, true) when (sigelt_in_m se) -> begin
((FStar_Util.smap_remove sm' k);
(

let se1 = (match (se) with
| FStar_Syntax_Syntax.Sig_declare_typ (l, u, t, q, r) -> begin
FStar_Syntax_Syntax.Sig_declare_typ (((l), (u), (t), ((FStar_Syntax_Syntax.Assumption)::q), (r)))
end
| uu____4277 -> begin
se
end)
in (FStar_Util.smap_add sm' k ((se1), (false))));
)
end
| uu____4280 -> begin
()
end)))));
env1;
)))))))


let finish_module_or_interface : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env modul -> ((match ((not (modul.FStar_Syntax_Syntax.is_interface))) with
| true -> begin
(check_admits env)
end
| uu____4291 -> begin
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
| uu____4313 -> begin
(match ((FStar_Util.starts_with "FStar." (FStar_Ident.text_of_lid mname))) with
| true -> begin
(FStar_Syntax_Const.prims_lid)::(FStar_Syntax_Const.fstar_ns_lid)::[]
end
| uu____4315 -> begin
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
| uu____4322 -> begin
open_ns
end)
in ((

let uu____4324 = (exported_id_set_new ())
in (FStar_Util.smap_add env1.exported_ids mname.FStar_Ident.str uu____4324));
(match (()) with
| () -> begin
((

let uu____4329 = (exported_id_set_new ())
in (FStar_Util.smap_add env1.trans_exported_ids mname.FStar_Ident.str uu____4329));
(match (()) with
| () -> begin
((

let uu____4334 = (FStar_Util.mk_ref [])
in (FStar_Util.smap_add env1.includes mname.FStar_Ident.str uu____4334));
(match (()) with
| () -> begin
(

let uu___185_4343 = env1
in (

let uu____4344 = (FStar_List.map (fun lid -> Open_module_or_namespace (((lid), (Open_namespace)))) open_ns1)
in {curmodule = Some (mname); curmonad = uu___185_4343.curmonad; modules = uu___185_4343.modules; scope_mods = uu____4344; exported_ids = uu___185_4343.exported_ids; trans_exported_ids = uu___185_4343.trans_exported_ids; includes = uu___185_4343.includes; sigaccum = uu___185_4343.sigaccum; sigmap = env1.sigmap; iface = intf; admitted_iface = admitted; expect_typ = uu___185_4343.expect_typ}))
end);
)
end);
)
end);
))))
in (

let uu____4347 = (FStar_All.pipe_right env.modules (FStar_Util.find_opt (fun uu____4359 -> (match (uu____4359) with
| (l, uu____4363) -> begin
(FStar_Ident.lid_equals l mname)
end))))
in (match (uu____4347) with
| None -> begin
(

let uu____4368 = (prep env)
in ((uu____4368), (false)))
end
| Some (uu____4369, m) -> begin
((

let uu____4374 = ((

let uu____4375 = (FStar_Options.interactive ())
in (not (uu____4375))) && ((not (m.FStar_Syntax_Syntax.is_interface)) || intf))
in (match (uu____4374) with
| true -> begin
(

let uu____4376 = (

let uu____4377 = (

let uu____4380 = (FStar_Util.format1 "Duplicate module or interface name: %s" mname.FStar_Ident.str)
in ((uu____4380), ((FStar_Ident.range_of_lid mname))))
in FStar_Errors.Error (uu____4377))
in (Prims.raise uu____4376))
end
| uu____4381 -> begin
()
end));
(

let uu____4382 = (

let uu____4383 = (push env)
in (prep uu____4383))
in ((uu____4382), (true)));
)
end))))


let enter_monad_scope : env  ->  FStar_Ident.ident  ->  env = (fun env mname -> (match (env.curmonad) with
| Some (mname') -> begin
(Prims.raise (FStar_Errors.Error ((((Prims.strcat "Trying to define monad " (Prims.strcat mname.FStar_Ident.idText (Prims.strcat ", but already in monad scope " mname'.FStar_Ident.idText)))), (mname.FStar_Ident.idRange)))))
end
| None -> begin
(

let uu___186_4391 = env
in {curmodule = uu___186_4391.curmodule; curmonad = Some (mname); modules = uu___186_4391.modules; scope_mods = uu___186_4391.scope_mods; exported_ids = uu___186_4391.exported_ids; trans_exported_ids = uu___186_4391.trans_exported_ids; includes = uu___186_4391.includes; sigaccum = uu___186_4391.sigaccum; sigmap = uu___186_4391.sigmap; iface = uu___186_4391.iface; admitted_iface = uu___186_4391.admitted_iface; expect_typ = uu___186_4391.expect_typ})
end))


let fail_or = (fun env lookup lid -> (

let uu____4416 = (lookup lid)
in (match (uu____4416) with
| None -> begin
(

let opened_modules = (FStar_List.map (fun uu____4422 -> (match (uu____4422) with
| (lid1, uu____4426) -> begin
(FStar_Ident.text_of_lid lid1)
end)) env.modules)
in (

let msg = (FStar_Util.format1 "Identifier not found: [%s]" (FStar_Ident.text_of_lid lid))
in (

let msg1 = (match (((FStar_List.length lid.FStar_Ident.ns) = (Prims.parse_int "0"))) with
| true -> begin
msg
end
| uu____4431 -> begin
(

let modul = (

let uu____4433 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in (FStar_Ident.set_lid_range uu____4433 (FStar_Ident.range_of_lid lid)))
in (

let uu____4434 = (resolve_module_name env modul true)
in (match (uu____4434) with
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

let uu____4461 = (lookup id)
in (match (uu____4461) with
| None -> begin
(Prims.raise (FStar_Errors.Error ((((Prims.strcat "Identifier not found [" (Prims.strcat id.FStar_Ident.idText "]"))), (id.FStar_Ident.idRange)))))
end
| Some (r) -> begin
r
end)))




