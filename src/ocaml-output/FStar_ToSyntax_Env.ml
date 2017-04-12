
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
{curmodule : FStar_Ident.lident Prims.option; curmonad : FStar_Ident.ident Prims.option; modules : (FStar_Ident.lident * FStar_Syntax_Syntax.modul) Prims.list; scope_mods : scope_mod Prims.list; exported_ids : exported_id_set FStar_Util.smap; trans_exported_ids : exported_id_set FStar_Util.smap; includes : FStar_Ident.lident Prims.list FStar_ST.ref FStar_Util.smap; sigaccum : FStar_Syntax_Syntax.sigelts; sigmap : (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap; iface : Prims.bool; admitted_iface : Prims.bool; expect_typ : Prims.bool; docs : FStar_Parser_AST.fsdoc FStar_Util.smap}

type foundname =
| Term_name of (FStar_Syntax_Syntax.typ * Prims.bool)
| Eff_name of (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident)


let uu___is_Term_name : foundname  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Term_name (_0) -> begin
true
end
| uu____324 -> begin
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
| uu____344 -> begin
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

let uu____367 = (FStar_Util.smap_try_find env.trans_exported_ids module_name)
in (match (uu____367) with
| None -> begin
[]
end
| Some (exported_id_set) -> begin
(

let uu____371 = (

let uu____372 = (exported_id_set Exported_id_term_type)
in (FStar_ST.read uu____372))
in (FStar_All.pipe_right uu____371 FStar_Util.set_elements))
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

let uu____398 = (current_module env)
in (qual uu____398 id))
end
| Some (monad) -> begin
(

let uu____400 = (

let uu____401 = (current_module env)
in (qual uu____401 monad))
in (FStar_Syntax_Util.mk_field_projector_name_from_ident uu____400 id))
end))


let new_sigmap = (fun uu____409 -> (FStar_Util.smap_create (Prims.parse_int "100")))


let empty_env : Prims.unit  ->  env = (fun uu____412 -> (

let uu____413 = (new_sigmap ())
in (

let uu____415 = (new_sigmap ())
in (

let uu____417 = (new_sigmap ())
in (

let uu____423 = (new_sigmap ())
in (

let uu____429 = (new_sigmap ())
in {curmodule = None; curmonad = None; modules = []; scope_mods = []; exported_ids = uu____413; trans_exported_ids = uu____415; includes = uu____417; sigaccum = []; sigmap = uu____423; iface = false; admitted_iface = false; expect_typ = false; docs = uu____429}))))))


let sigmap : env  ->  (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap = (fun env -> env.sigmap)


let has_all_in_scope : env  ->  Prims.bool = (fun env -> (FStar_List.existsb (fun uu____444 -> (match (uu____444) with
| (m, uu____448) -> begin
(FStar_Ident.lid_equals m FStar_Syntax_Const.all_lid)
end)) env.modules))


let set_bv_range : FStar_Syntax_Syntax.bv  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.bv = (fun bv r -> (

let id = (

let uu___166_456 = bv.FStar_Syntax_Syntax.ppname
in {FStar_Ident.idText = uu___166_456.FStar_Ident.idText; FStar_Ident.idRange = r})
in (

let uu___167_457 = bv
in {FStar_Syntax_Syntax.ppname = id; FStar_Syntax_Syntax.index = uu___167_457.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu___167_457.FStar_Syntax_Syntax.sort})))


let bv_to_name : FStar_Syntax_Syntax.bv  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.term = (fun bv r -> (FStar_Syntax_Syntax.bv_to_name (set_bv_range bv r)))


let unmangleMap : (Prims.string * Prims.string * FStar_Syntax_Syntax.delta_depth * FStar_Syntax_Syntax.fv_qual Prims.option) Prims.list = ((("op_ColonColon"), ("Cons"), (FStar_Syntax_Syntax.Delta_constant), (Some (FStar_Syntax_Syntax.Data_ctor))))::((("not"), ("op_Negation"), (FStar_Syntax_Syntax.Delta_equational), (None)))::[]


let unmangleOpName : FStar_Ident.ident  ->  (FStar_Syntax_Syntax.term * Prims.bool) Prims.option = (fun id -> (

let t = (FStar_Util.find_map unmangleMap (fun uu____503 -> (match (uu____503) with
| (x, y, dd, dq) -> begin
(match ((id.FStar_Ident.idText = x)) with
| true -> begin
(

let uu____517 = (

let uu____518 = (FStar_Ident.lid_of_path (("Prims")::(y)::[]) id.FStar_Ident.idRange)
in (FStar_Syntax_Syntax.fvar uu____518 dd dq))
in Some (uu____517))
end
| uu____519 -> begin
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
| uu____548 -> begin
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
| uu____572 -> begin
false
end))


let uu___is_Cont_ignore = (fun projectee -> (match (projectee) with
| Cont_ignore -> begin
true
end
| uu____583 -> begin
false
end))


let option_of_cont = (fun k_ignore uu___139_602 -> (match (uu___139_602) with
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

let find1 = (FStar_Util.find_map record.fields (fun uu____647 -> (match (uu____647) with
| (f, uu____652) -> begin
(match ((id.FStar_Ident.idText = f.FStar_Ident.idText)) with
| true -> begin
Some (record)
end
| uu____654 -> begin
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
| uu____657 -> begin
Cont_ignore
end)))


let get_exported_id_set : env  ->  Prims.string  ->  (exported_id_kind  ->  string_set FStar_ST.ref) Prims.option = (fun e mname -> (FStar_Util.smap_try_find e.exported_ids mname))


let get_trans_exported_id_set : env  ->  Prims.string  ->  (exported_id_kind  ->  string_set FStar_ST.ref) Prims.option = (fun e mname -> (FStar_Util.smap_try_find e.trans_exported_ids mname))


let string_of_exported_id_kind : exported_id_kind  ->  Prims.string = (fun uu___140_688 -> (match (uu___140_688) with
| Exported_id_field -> begin
"field"
end
| Exported_id_term_type -> begin
"term/type"
end))


let find_in_module_with_includes = (fun eikind find_in_module find_in_module_default env ns id -> (

let idstr = id.FStar_Ident.idText
in (

let rec aux = (fun uu___141_737 -> (match (uu___141_737) with
| [] -> begin
find_in_module_default
end
| (modul)::q -> begin
(

let mname = modul.FStar_Ident.str
in (

let not_shadowed = (

let uu____745 = (get_exported_id_set env mname)
in (match (uu____745) with
| None -> begin
true
end
| Some (mex) -> begin
(

let mexports = (

let uu____761 = (mex eikind)
in (FStar_ST.read uu____761))
in (FStar_Util.set_mem idstr mexports))
end))
in (

let mincludes = (

let uu____768 = (FStar_Util.smap_try_find env.includes mname)
in (match (uu____768) with
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

let uu____788 = (qual modul id)
in (find_in_module uu____788))
end
| uu____789 -> begin
Cont_ignore
end)
in (match (look_into) with
| Cont_ignore -> begin
(aux (FStar_List.append mincludes q))
end
| uu____791 -> begin
look_into
end)))))
end))
in (aux ((ns)::[])))))


let is_exported_id_field : exported_id_kind  ->  Prims.bool = (fun uu___142_795 -> (match (uu___142_795) with
| Exported_id_field -> begin
true
end
| uu____796 -> begin
false
end))


let try_lookup_id'' = (fun env id eikind k_local_binding k_rec_binding k_record find_in_module lookup_default_id -> (

let check_local_binding_id = (fun uu___143_885 -> (match (uu___143_885) with
| (id', uu____887, uu____888) -> begin
(id'.FStar_Ident.idText = id.FStar_Ident.idText)
end))
in (

let check_rec_binding_id = (fun uu___144_892 -> (match (uu___144_892) with
| (id', uu____894, uu____895) -> begin
(id'.FStar_Ident.idText = id.FStar_Ident.idText)
end))
in (

let curmod_ns = (

let uu____898 = (current_module env)
in (FStar_Ident.ids_of_lid uu____898))
in (

let proc = (fun uu___145_903 -> (match (uu___145_903) with
| Local_binding (l) when (check_local_binding_id l) -> begin
(k_local_binding l)
end
| Rec_binding (r) when (check_rec_binding_id r) -> begin
(k_rec_binding r)
end
| Open_module_or_namespace (ns, uu____908) -> begin
(find_in_module_with_includes eikind find_in_module Cont_ignore env ns id)
end
| Top_level_def (id') when (id'.FStar_Ident.idText = id.FStar_Ident.idText) -> begin
(lookup_default_id Cont_ignore id)
end
| Record_or_dc (r) when (is_exported_id_field eikind) -> begin
(

let uu____911 = (FStar_Ident.lid_of_ids curmod_ns)
in (find_in_module_with_includes Exported_id_field (fun lid -> (

let id1 = lid.FStar_Ident.ident
in (find_in_record lid.FStar_Ident.ns id1 r k_record))) Cont_ignore env uu____911 id))
end
| uu____914 -> begin
Cont_ignore
end))
in (

let rec aux = (fun uu___146_920 -> (match (uu___146_920) with
| (a)::q -> begin
(

let uu____926 = (proc a)
in (option_of_cont (fun uu____928 -> (aux q)) uu____926))
end
| [] -> begin
(

let uu____929 = (lookup_default_id Cont_fail id)
in (option_of_cont (fun uu____931 -> None) uu____929))
end))
in (aux env.scope_mods)))))))


let found_local_binding = (fun r uu____950 -> (match (uu____950) with
| (id', x, mut) -> begin
(

let uu____957 = (bv_to_name x r)
in ((uu____957), (mut)))
end))


let find_in_module = (fun env lid k_global_def k_not_found -> (

let uu____994 = (FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str)
in (match (uu____994) with
| Some (sb) -> begin
(k_global_def lid sb)
end
| None -> begin
k_not_found
end)))


let try_lookup_id : env  ->  FStar_Ident.ident  ->  (FStar_Syntax_Syntax.term * Prims.bool) Prims.option = (fun env id -> (

let uu____1016 = (unmangleOpName id)
in (match (uu____1016) with
| Some (f) -> begin
Some (f)
end
| uu____1030 -> begin
(try_lookup_id'' env id Exported_id_term_type (fun r -> (

let uu____1037 = (found_local_binding id.FStar_Ident.idRange r)
in Cont_ok (uu____1037))) (fun uu____1042 -> Cont_fail) (fun uu____1045 -> Cont_ignore) (fun i -> (find_in_module env i (fun uu____1052 uu____1053 -> Cont_fail) Cont_ignore)) (fun uu____1060 uu____1061 -> Cont_fail))
end)))


let lookup_default_id = (fun env id k_global_def k_not_found -> (

let find_in_monad = (match (env.curmonad) with
| Some (uu____1113) -> begin
(

let lid = (qualify env id)
in (

let uu____1115 = (FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str)
in (match (uu____1115) with
| Some (r) -> begin
(

let uu____1128 = (k_global_def lid r)
in Some (uu____1128))
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

let uu____1141 = (current_module env)
in (qual uu____1141 id))
in (find_in_module env lid k_global_def k_not_found))
end)))


let module_is_defined : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> ((match (env.curmodule) with
| None -> begin
false
end
| Some (m) -> begin
(

let uu____1150 = (current_module env)
in (FStar_Ident.lid_equals lid uu____1150))
end) || (FStar_List.existsb (fun x -> (FStar_Ident.lid_equals lid (Prims.fst x))) env.modules)))


let resolve_module_name : env  ->  FStar_Ident.lident  ->  Prims.bool  ->  FStar_Ident.lident Prims.option = (fun env lid honor_ns -> (

let nslen = (FStar_List.length lid.FStar_Ident.ns)
in (

let rec aux = (fun uu___147_1174 -> (match (uu___147_1174) with
| [] -> begin
(

let uu____1177 = (module_is_defined env lid)
in (match (uu____1177) with
| true -> begin
Some (lid)
end
| uu____1179 -> begin
None
end))
end
| (Open_module_or_namespace (ns, Open_namespace))::q when honor_ns -> begin
(

let new_lid = (

let uu____1184 = (

let uu____1186 = (FStar_Ident.path_of_lid ns)
in (

let uu____1188 = (FStar_Ident.path_of_lid lid)
in (FStar_List.append uu____1186 uu____1188)))
in (FStar_Ident.lid_of_path uu____1184 (FStar_Ident.range_of_lid lid)))
in (

let uu____1190 = (module_is_defined env new_lid)
in (match (uu____1190) with
| true -> begin
Some (new_lid)
end
| uu____1192 -> begin
(aux q)
end)))
end
| (Module_abbrev (name, modul))::uu____1195 when ((nslen = (Prims.parse_int "0")) && (name.FStar_Ident.idText = lid.FStar_Ident.ident.FStar_Ident.idText)) -> begin
Some (modul)
end
| (uu____1199)::q -> begin
(aux q)
end))
in (aux env.scope_mods))))


let fail_if_curmodule : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  Prims.unit = (fun env ns_original ns_resolved -> (

let uu____1211 = (

let uu____1212 = (current_module env)
in (FStar_Ident.lid_equals ns_resolved uu____1212))
in (match (uu____1211) with
| true -> begin
(match ((FStar_Ident.lid_equals ns_resolved FStar_Syntax_Const.prims_lid)) with
| true -> begin
()
end
| uu____1213 -> begin
(

let uu____1214 = (

let uu____1215 = (

let uu____1218 = (FStar_Util.format1 "Reference %s to current module is forbidden (see GitHub issue #451)" ns_original.FStar_Ident.str)
in ((uu____1218), ((FStar_Ident.range_of_lid ns_original))))
in FStar_Errors.Error (uu____1215))
in (Prims.raise uu____1214))
end)
end
| uu____1219 -> begin
()
end)))


let fail_if_qualified_by_curmodule : env  ->  FStar_Ident.lident  ->  Prims.unit = (fun env lid -> (match (lid.FStar_Ident.ns) with
| [] -> begin
()
end
| uu____1226 -> begin
(

let modul_orig = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in (

let uu____1229 = (resolve_module_name env modul_orig true)
in (match (uu____1229) with
| Some (modul_res) -> begin
(fail_if_curmodule env modul_orig modul_res)
end
| uu____1232 -> begin
()
end)))
end))


let namespace_is_open : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (FStar_List.existsb (fun uu___148_1240 -> (match (uu___148_1240) with
| Open_module_or_namespace (ns, Open_namespace) -> begin
(FStar_Ident.lid_equals lid ns)
end
| uu____1242 -> begin
false
end)) env.scope_mods))


let shorten_module_path : env  ->  FStar_Ident.ident Prims.list  ->  Prims.bool  ->  (FStar_Ident.ident Prims.list * FStar_Ident.ident Prims.list) = (fun env ids is_full_path -> (

let rec aux = (fun revns id -> (

let lid = (FStar_Ident.lid_of_ns_and_id (FStar_List.rev revns) id)
in (match ((namespace_is_open env lid)) with
| true -> begin
Some ((((FStar_List.rev ((id)::revns))), ([])))
end
| uu____1284 -> begin
(match (revns) with
| [] -> begin
None
end
| (ns_last_id)::rev_ns_prefix -> begin
(

let uu____1297 = (aux rev_ns_prefix ns_last_id)
in (FStar_All.pipe_right uu____1297 (FStar_Util.map_option (fun uu____1321 -> (match (uu____1321) with
| (stripped_ids, rev_kept_ids) -> begin
((stripped_ids), ((id)::rev_kept_ids))
end)))))
end)
end)))
in (

let uu____1338 = (is_full_path && (

let uu____1339 = (FStar_Ident.lid_of_ids ids)
in (module_is_defined env uu____1339)))
in (match (uu____1338) with
| true -> begin
((ids), ([]))
end
| uu____1346 -> begin
(match ((FStar_List.rev ids)) with
| [] -> begin
(([]), ([]))
end
| (ns_last_id)::ns_rev_prefix -> begin
(

let uu____1356 = (aux ns_rev_prefix ns_last_id)
in (match (uu____1356) with
| None -> begin
(([]), (ids))
end
| Some (stripped_ids, rev_kept_ids) -> begin
((stripped_ids), ((FStar_List.rev rev_kept_ids)))
end))
end)
end))))


let resolve_in_open_namespaces'' = (fun env lid eikind k_local_binding k_rec_binding k_record f_module l_default -> (match (lid.FStar_Ident.ns) with
| (uu____1469)::uu____1470 -> begin
(

let uu____1472 = (

let uu____1474 = (

let uu____1475 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in (FStar_Ident.set_lid_range uu____1475 (FStar_Ident.range_of_lid lid)))
in (resolve_module_name env uu____1474 true))
in (match (uu____1472) with
| None -> begin
None
end
| Some (modul) -> begin
(

let uu____1478 = (find_in_module_with_includes eikind f_module Cont_fail env modul lid.FStar_Ident.ident)
in (option_of_cont (fun uu____1480 -> None) uu____1478))
end))
end
| [] -> begin
(try_lookup_id'' env lid.FStar_Ident.ident eikind k_local_binding k_rec_binding k_record f_module l_default)
end))


let cont_of_option = (fun k_none uu___149_1495 -> (match (uu___149_1495) with
| Some (v1) -> begin
Cont_ok (v1)
end
| None -> begin
k_none
end))


let resolve_in_open_namespaces' = (fun env lid k_local_binding k_rec_binding k_global_def -> (

let k_global_def' = (fun k lid1 def -> (

let uu____1574 = (k_global_def lid1 def)
in (cont_of_option k uu____1574)))
in (

let f_module = (fun lid' -> (

let k = Cont_ignore
in (find_in_module env lid' (k_global_def' k) k)))
in (

let l_default = (fun k i -> (lookup_default_id env i (k_global_def' k) k))
in (resolve_in_open_namespaces'' env lid Exported_id_term_type (fun l -> (

let uu____1595 = (k_local_binding l)
in (cont_of_option Cont_fail uu____1595))) (fun r -> (

let uu____1598 = (k_rec_binding r)
in (cont_of_option Cont_fail uu____1598))) (fun uu____1600 -> Cont_ignore) f_module l_default)))))


let fv_qual_of_se : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.fv_qual Prims.option = (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (uu____1606, uu____1607, uu____1608, l, uu____1610, quals, uu____1612) -> begin
(

let qopt = (FStar_Util.find_map quals (fun uu___150_1619 -> (match (uu___150_1619) with
| FStar_Syntax_Syntax.RecordConstructor (uu____1621, fs) -> begin
Some (FStar_Syntax_Syntax.Record_ctor (((l), (fs))))
end
| uu____1628 -> begin
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
| FStar_Syntax_Syntax.Sig_declare_typ (uu____1632, uu____1633, uu____1634, quals) -> begin
None
end
| uu____1638 -> begin
None
end))


let lb_fv : FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.fv = (fun lbs lid -> (

let uu____1647 = (FStar_Util.find_map lbs (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let uu____1651 = (FStar_Syntax_Syntax.fv_eq_lid fv lid)
in (match (uu____1651) with
| true -> begin
Some (fv)
end
| uu____1653 -> begin
None
end)))))
in (FStar_All.pipe_right uu____1647 FStar_Util.must)))


let ns_of_lid_equals : FStar_Ident.lident  ->  FStar_Ident.lident  ->  Prims.bool = (fun lid ns -> (((FStar_List.length lid.FStar_Ident.ns) = (FStar_List.length (FStar_Ident.ids_of_lid ns))) && (

let uu____1665 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in (FStar_Ident.lid_equals uu____1665 ns))))


let try_lookup_name : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  foundname Prims.option = (fun any_val exclude_interf env lid -> (

let occurrence_range = (FStar_Ident.range_of_lid lid)
in (

let k_global_def = (fun source_lid uu___154_1690 -> (match (uu___154_1690) with
| (uu____1694, true) when exclude_interf -> begin
None
end
| (se, uu____1696) -> begin
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____1698) -> begin
(

let uu____1709 = (

let uu____1710 = (

let uu____1713 = (FStar_Syntax_Syntax.fvar source_lid FStar_Syntax_Syntax.Delta_constant None)
in ((uu____1713), (false)))
in Term_name (uu____1710))
in Some (uu____1709))
end
| FStar_Syntax_Syntax.Sig_datacon (uu____1714) -> begin
(

let uu____1724 = (

let uu____1725 = (

let uu____1728 = (

let uu____1729 = (fv_qual_of_se se)
in (FStar_Syntax_Syntax.fvar source_lid FStar_Syntax_Syntax.Delta_constant uu____1729))
in ((uu____1728), (false)))
in Term_name (uu____1725))
in Some (uu____1724))
end
| FStar_Syntax_Syntax.Sig_let ((uu____1731, lbs), uu____1733, uu____1734, uu____1735) -> begin
(

let fv = (lb_fv lbs source_lid)
in (

let uu____1748 = (

let uu____1749 = (

let uu____1752 = (FStar_Syntax_Syntax.fvar source_lid fv.FStar_Syntax_Syntax.fv_delta fv.FStar_Syntax_Syntax.fv_qual)
in ((uu____1752), (false)))
in Term_name (uu____1749))
in Some (uu____1748)))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid1, uu____1754, uu____1755, quals) -> begin
(

let uu____1759 = (any_val || (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___151_1761 -> (match (uu___151_1761) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| uu____1762 -> begin
false
end)))))
in (match (uu____1759) with
| true -> begin
(

let lid2 = (FStar_Ident.set_lid_range lid1 (FStar_Ident.range_of_lid source_lid))
in (

let dd = (

let uu____1766 = ((FStar_Syntax_Util.is_primop_lid lid2) || ((ns_of_lid_equals lid2 FStar_Syntax_Const.prims_lid) && (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___152_1768 -> (match (uu___152_1768) with
| (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) -> begin
true
end
| uu____1771 -> begin
false
end))))))
in (match (uu____1766) with
| true -> begin
FStar_Syntax_Syntax.Delta_equational
end
| uu____1772 -> begin
FStar_Syntax_Syntax.Delta_constant
end))
in (

let uu____1773 = (FStar_Util.find_map quals (fun uu___153_1775 -> (match (uu___153_1775) with
| FStar_Syntax_Syntax.Reflectable (refl_monad) -> begin
Some (refl_monad)
end
| uu____1778 -> begin
None
end)))
in (match (uu____1773) with
| Some (refl_monad) -> begin
(

let refl_const = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (refl_monad)))) None occurrence_range)
in Some (Term_name (((refl_const), (false)))))
end
| uu____1794 -> begin
(

let uu____1796 = (

let uu____1797 = (

let uu____1800 = (

let uu____1801 = (fv_qual_of_se se)
in (FStar_Syntax_Syntax.fvar lid2 dd uu____1801))
in ((uu____1800), (false)))
in Term_name (uu____1797))
in Some (uu____1796))
end))))
end
| uu____1803 -> begin
None
end))
end
| (FStar_Syntax_Syntax.Sig_new_effect_for_free (ne)) | (FStar_Syntax_Syntax.Sig_new_effect (ne)) -> begin
Some (Eff_name (((se), ((FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname (FStar_Ident.range_of_lid source_lid))))))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (uu____1805) -> begin
Some (Eff_name (((se), (source_lid))))
end
| uu____1814 -> begin
None
end)
end))
in (

let k_local_binding = (fun r -> (

let uu____1826 = (

let uu____1827 = (found_local_binding (FStar_Ident.range_of_lid lid) r)
in Term_name (uu____1827))
in Some (uu____1826)))
in (

let k_rec_binding = (fun uu____1837 -> (match (uu____1837) with
| (id, l, dd) -> begin
(

let uu____1845 = (

let uu____1846 = (

let uu____1849 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range l (FStar_Ident.range_of_lid lid)) dd None)
in ((uu____1849), (false)))
in Term_name (uu____1846))
in Some (uu____1845))
end))
in (

let found_unmangled = (match (lid.FStar_Ident.ns) with
| [] -> begin
(

let uu____1853 = (unmangleOpName lid.FStar_Ident.ident)
in (match (uu____1853) with
| Some (f) -> begin
Some (Term_name (f))
end
| uu____1863 -> begin
None
end))
end
| uu____1867 -> begin
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

let uu____1887 = (try_lookup_name true exclude_interf env lid)
in (match (uu____1887) with
| Some (Eff_name (o, l)) -> begin
Some (((o), (l)))
end
| uu____1896 -> begin
None
end)))


let try_lookup_effect_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env l -> (

let uu____1907 = (try_lookup_effect_name' (not (env.iface)) env l)
in (match (uu____1907) with
| Some (o, l1) -> begin
Some (l1)
end
| uu____1916 -> begin
None
end)))


let try_lookup_effect_name_and_attributes : env  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.cflags Prims.list) Prims.option = (fun env l -> (

let uu____1930 = (try_lookup_effect_name' (not (env.iface)) env l)
in (match (uu____1930) with
| Some ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect (ne); FStar_Syntax_Syntax.sigrng = uu____1939}, l1) -> begin
Some (((l1), (ne.FStar_Syntax_Syntax.cattributes)))
end
| Some ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect_for_free (ne); FStar_Syntax_Syntax.sigrng = uu____1948}, l1) -> begin
Some (((l1), (ne.FStar_Syntax_Syntax.cattributes)))
end
| Some ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_effect_abbrev (uu____1956, uu____1957, uu____1958, uu____1959, uu____1960, cattributes); FStar_Syntax_Syntax.sigrng = uu____1962}, l1) -> begin
Some (((l1), (cattributes)))
end
| uu____1974 -> begin
None
end)))


let try_lookup_effect_defn : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl Prims.option = (fun env l -> (

let uu____1988 = (try_lookup_effect_name' (not (env.iface)) env l)
in (match (uu____1988) with
| Some ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect (ne); FStar_Syntax_Syntax.sigrng = uu____1994}, uu____1995) -> begin
Some (ne)
end
| Some ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect_for_free (ne); FStar_Syntax_Syntax.sigrng = uu____1999}, uu____2000) -> begin
Some (ne)
end
| uu____2003 -> begin
None
end)))


let is_effect_name : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let uu____2013 = (try_lookup_effect_name env lid)
in (match (uu____2013) with
| None -> begin
false
end
| Some (uu____2015) -> begin
true
end)))


let try_lookup_root_effect_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env l -> (

let uu____2023 = (try_lookup_effect_name' (not (env.iface)) env l)
in (match (uu____2023) with
| Some ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_effect_abbrev (l', uu____2029, uu____2030, uu____2031, uu____2032, uu____2033); FStar_Syntax_Syntax.sigrng = uu____2034}, uu____2035) -> begin
(

let rec aux = (fun new_name -> (

let uu____2047 = (FStar_Util.smap_try_find (sigmap env) new_name.FStar_Ident.str)
in (match (uu____2047) with
| None -> begin
None
end
| Some (s, uu____2057) -> begin
(match (s.FStar_Syntax_Syntax.sigel) with
| (FStar_Syntax_Syntax.Sig_new_effect_for_free (ne)) | (FStar_Syntax_Syntax.Sig_new_effect (ne)) -> begin
Some ((FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname (FStar_Ident.range_of_lid l)))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (uu____2062, uu____2063, uu____2064, cmp, uu____2066, uu____2067) -> begin
(

let l'' = (FStar_Syntax_Util.comp_effect_name cmp)
in (aux l''))
end
| uu____2073 -> begin
None
end)
end)))
in (aux l'))
end
| Some (uu____2074, l') -> begin
Some (l')
end
| uu____2078 -> begin
None
end)))


let lookup_letbinding_quals : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.qualifier Prims.list = (fun env lid -> (

let k_global_def = (fun lid1 uu___155_2099 -> (match (uu___155_2099) with
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (lid2, uu____2105, uu____2106, quals); FStar_Syntax_Syntax.sigrng = uu____2108}, uu____2109) -> begin
Some (quals)
end
| uu____2113 -> begin
None
end))
in (

let uu____2117 = (resolve_in_open_namespaces' env lid (fun uu____2121 -> None) (fun uu____2123 -> None) k_global_def)
in (match (uu____2117) with
| Some (quals) -> begin
quals
end
| uu____2129 -> begin
[]
end))))


let try_lookup_module : env  ->  Prims.string Prims.list  ->  FStar_Syntax_Syntax.modul Prims.option = (fun env path -> (

let uu____2141 = (FStar_List.tryFind (fun uu____2147 -> (match (uu____2147) with
| (mlid, modul) -> begin
(

let uu____2152 = (FStar_Ident.path_of_lid mlid)
in (uu____2152 = path))
end)) env.modules)
in (match (uu____2141) with
| Some (uu____2156, modul) -> begin
Some (modul)
end
| None -> begin
None
end)))


let try_lookup_let : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env lid -> (

let k_global_def = (fun lid1 uu___156_2178 -> (match (uu___156_2178) with
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let ((uu____2182, lbs), uu____2184, uu____2185, uu____2186); FStar_Syntax_Syntax.sigrng = uu____2187}, uu____2188) -> begin
(

let fv = (lb_fv lbs lid1)
in (

let uu____2201 = (FStar_Syntax_Syntax.fvar lid1 fv.FStar_Syntax_Syntax.fv_delta fv.FStar_Syntax_Syntax.fv_qual)
in Some (uu____2201)))
end
| uu____2202 -> begin
None
end))
in (resolve_in_open_namespaces' env lid (fun uu____2205 -> None) (fun uu____2206 -> None) k_global_def)))


let try_lookup_definition : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env lid -> (

let k_global_def = (fun lid1 uu___157_2225 -> (match (uu___157_2225) with
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (lbs, uu____2232, uu____2233, uu____2234); FStar_Syntax_Syntax.sigrng = uu____2235}, uu____2236) -> begin
(FStar_Util.find_map (Prims.snd lbs) (fun lb -> (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv lid1) -> begin
Some (lb.FStar_Syntax_Syntax.lbdef)
end
| uu____2253 -> begin
None
end)))
end
| uu____2258 -> begin
None
end))
in (resolve_in_open_namespaces' env lid (fun uu____2265 -> None) (fun uu____2268 -> None) k_global_def)))


let empty_include_smap : FStar_Ident.lident Prims.list FStar_ST.ref FStar_Util.smap = (new_sigmap ())


let empty_exported_id_smap : exported_id_set FStar_Util.smap = (new_sigmap ())


let try_lookup_lid' : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term * Prims.bool) Prims.option = (fun any_val exclude_interf env lid -> (

let uu____2295 = (try_lookup_name any_val exclude_interf env lid)
in (match (uu____2295) with
| Some (Term_name (e, mut)) -> begin
Some (((e), (mut)))
end
| uu____2304 -> begin
None
end)))


let try_lookup_lid : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term * Prims.bool) Prims.option = (fun env l -> (try_lookup_lid' env.iface false env l))


let resolve_to_fully_qualified_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env l -> (

let uu____2324 = (try_lookup_lid env l)
in (match (uu____2324) with
| None -> begin
None
end
| Some (e, uu____2332) -> begin
(

let uu____2335 = (

let uu____2336 = (FStar_Syntax_Subst.compress e)
in uu____2336.FStar_Syntax_Syntax.n)
in (match (uu____2335) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
Some (fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end
| uu____2345 -> begin
None
end))
end)))


let try_lookup_lid_no_resolve : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term * Prims.bool) Prims.option = (fun env l -> (

let env' = (

let uu___168_2356 = env
in {curmodule = uu___168_2356.curmodule; curmonad = uu___168_2356.curmonad; modules = uu___168_2356.modules; scope_mods = []; exported_ids = empty_exported_id_smap; trans_exported_ids = uu___168_2356.trans_exported_ids; includes = empty_include_smap; sigaccum = uu___168_2356.sigaccum; sigmap = uu___168_2356.sigmap; iface = uu___168_2356.iface; admitted_iface = uu___168_2356.admitted_iface; expect_typ = uu___168_2356.expect_typ; docs = uu___168_2356.docs})
in (try_lookup_lid env' l)))


let try_lookup_doc : env  ->  FStar_Ident.lid  ->  FStar_Parser_AST.fsdoc Prims.option = (fun env l -> (FStar_Util.smap_try_find env.docs l.FStar_Ident.str))


let try_lookup_datacon : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.fv Prims.option = (fun env lid -> (

let k_global_def = (fun lid1 uu___159_2380 -> (match (uu___159_2380) with
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (uu____2384, uu____2385, uu____2386, quals); FStar_Syntax_Syntax.sigrng = uu____2388}, uu____2389) -> begin
(

let uu____2392 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___158_2394 -> (match (uu___158_2394) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| uu____2395 -> begin
false
end))))
in (match (uu____2392) with
| true -> begin
(

let uu____2397 = (FStar_Syntax_Syntax.lid_as_fv lid1 FStar_Syntax_Syntax.Delta_constant None)
in Some (uu____2397))
end
| uu____2398 -> begin
None
end))
end
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (uu____2399); FStar_Syntax_Syntax.sigrng = uu____2400}, uu____2401) -> begin
(

let uu____2411 = (FStar_Syntax_Syntax.lid_as_fv lid1 FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in Some (uu____2411))
end
| uu____2412 -> begin
None
end))
in (resolve_in_open_namespaces' env lid (fun uu____2415 -> None) (fun uu____2416 -> None) k_global_def)))


let find_all_datacons : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.list Prims.option = (fun env lid -> (

let k_global_def = (fun lid1 uu___160_2435 -> (match (uu___160_2435) with
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (uu____2440, uu____2441, uu____2442, uu____2443, uu____2444, datas, uu____2446); FStar_Syntax_Syntax.sigrng = uu____2447}, uu____2448) -> begin
Some (datas)
end
| uu____2456 -> begin
None
end))
in (resolve_in_open_namespaces' env lid (fun uu____2461 -> None) (fun uu____2463 -> None) k_global_def)))


let record_cache_aux_with_filter : (((Prims.unit  ->  Prims.unit) * (Prims.unit  ->  Prims.unit) * (Prims.unit  ->  record_or_dc Prims.list) * (record_or_dc  ->  Prims.unit) * (Prims.unit  ->  Prims.unit)) * (Prims.unit  ->  Prims.unit)) = (

let record_cache = (FStar_Util.mk_ref (([])::[]))
in (

let push1 = (fun uu____2497 -> (

let uu____2498 = (

let uu____2501 = (

let uu____2503 = (FStar_ST.read record_cache)
in (FStar_List.hd uu____2503))
in (

let uu____2511 = (FStar_ST.read record_cache)
in (uu____2501)::uu____2511))
in (FStar_ST.write record_cache uu____2498)))
in (

let pop1 = (fun uu____2526 -> (

let uu____2527 = (

let uu____2530 = (FStar_ST.read record_cache)
in (FStar_List.tl uu____2530))
in (FStar_ST.write record_cache uu____2527)))
in (

let peek = (fun uu____2546 -> (

let uu____2547 = (FStar_ST.read record_cache)
in (FStar_List.hd uu____2547)))
in (

let insert = (fun r -> (

let uu____2559 = (

let uu____2562 = (

let uu____2564 = (peek ())
in (r)::uu____2564)
in (

let uu____2566 = (

let uu____2569 = (FStar_ST.read record_cache)
in (FStar_List.tl uu____2569))
in (uu____2562)::uu____2566))
in (FStar_ST.write record_cache uu____2559)))
in (

let commit1 = (fun uu____2585 -> (

let uu____2586 = (FStar_ST.read record_cache)
in (match (uu____2586) with
| (hd1)::(uu____2594)::tl1 -> begin
(FStar_ST.write record_cache ((hd1)::tl1))
end
| uu____2607 -> begin
(failwith "Impossible")
end)))
in (

let filter1 = (fun uu____2613 -> (

let rc = (peek ())
in ((pop1 ());
(match (()) with
| () -> begin
(

let filtered = (FStar_List.filter (fun r -> (not (r.is_private_or_abstract))) rc)
in (

let uu____2620 = (

let uu____2623 = (FStar_ST.read record_cache)
in (filtered)::uu____2623)
in (FStar_ST.write record_cache uu____2620)))
end);
)))
in (

let aux = ((push1), (pop1), (peek), (insert), (commit1))
in ((aux), (filter1))))))))))


let record_cache_aux : ((Prims.unit  ->  Prims.unit) * (Prims.unit  ->  Prims.unit) * (Prims.unit  ->  record_or_dc Prims.list) * (record_or_dc  ->  Prims.unit) * (Prims.unit  ->  Prims.unit)) = (

let uu____2697 = record_cache_aux_with_filter
in (match (uu____2697) with
| (aux, uu____2735) -> begin
aux
end))


let filter_record_cache : Prims.unit  ->  Prims.unit = (

let uu____2774 = record_cache_aux_with_filter
in (match (uu____2774) with
| (uu____2797, filter1) -> begin
filter1
end))


let push_record_cache : Prims.unit  ->  Prims.unit = (

let uu____2837 = record_cache_aux
in (match (uu____2837) with
| (push1, uu____2857, uu____2858, uu____2859, uu____2860) -> begin
push1
end))


let pop_record_cache : Prims.unit  ->  Prims.unit = (

let uu____2885 = record_cache_aux
in (match (uu____2885) with
| (uu____2904, pop1, uu____2906, uu____2907, uu____2908) -> begin
pop1
end))


let peek_record_cache : Prims.unit  ->  record_or_dc Prims.list = (

let uu____2934 = record_cache_aux
in (match (uu____2934) with
| (uu____2954, uu____2955, peek, uu____2957, uu____2958) -> begin
peek
end))


let insert_record_cache : record_or_dc  ->  Prims.unit = (

let uu____2983 = record_cache_aux
in (match (uu____2983) with
| (uu____3002, uu____3003, uu____3004, insert, uu____3006) -> begin
insert
end))


let commit_record_cache : Prims.unit  ->  Prims.unit = (

let uu____3031 = record_cache_aux
in (match (uu____3031) with
| (uu____3050, uu____3051, uu____3052, uu____3053, commit1) -> begin
commit1
end))


let extract_record : env  ->  scope_mod Prims.list FStar_ST.ref  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun e new_globs se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_bundle (sigs, uu____3093, uu____3094) -> begin
(

let is_rec = (FStar_Util.for_some (fun uu___161_3105 -> (match (uu___161_3105) with
| (FStar_Syntax_Syntax.RecordType (_)) | (FStar_Syntax_Syntax.RecordConstructor (_)) -> begin
true
end
| uu____3108 -> begin
false
end)))
in (

let find_dc = (fun dc -> (FStar_All.pipe_right sigs (FStar_Util.find_opt (fun uu___162_3116 -> (match (uu___162_3116) with
| {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (lid, uu____3118, uu____3119, uu____3120, uu____3121, uu____3122, uu____3123); FStar_Syntax_Syntax.sigrng = uu____3124} -> begin
(FStar_Ident.lid_equals dc lid)
end
| uu____3129 -> begin
false
end)))))
in (FStar_All.pipe_right sigs (FStar_List.iter (fun uu___163_3131 -> (match (uu___163_3131) with
| {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (typename, univs, parms, uu____3135, uu____3136, (dc)::[], tags); FStar_Syntax_Syntax.sigrng = uu____3139} -> begin
(

let uu____3145 = (

let uu____3146 = (find_dc dc)
in (FStar_All.pipe_left FStar_Util.must uu____3146))
in (match (uu____3145) with
| {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (constrname, uu____3150, t, uu____3152, uu____3153, uu____3154, uu____3155); FStar_Syntax_Syntax.sigrng = uu____3156} -> begin
(

let uu____3161 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____3161) with
| (formals, uu____3170) -> begin
(

let is_rec1 = (is_rec tags)
in (

let formals' = (FStar_All.pipe_right formals (FStar_List.collect (fun uu____3196 -> (match (uu____3196) with
| (x, q) -> begin
(

let uu____3204 = ((FStar_Syntax_Syntax.is_null_bv x) || (is_rec1 && (FStar_Syntax_Syntax.is_implicit q)))
in (match (uu____3204) with
| true -> begin
[]
end
| uu____3210 -> begin
(((x), (q)))::[]
end))
end))))
in (

let fields' = (FStar_All.pipe_right formals' (FStar_List.map (fun uu____3235 -> (match (uu____3235) with
| (x, q) -> begin
(

let uu____3244 = (match (is_rec1) with
| true -> begin
(FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname)
end
| uu____3245 -> begin
x.FStar_Syntax_Syntax.ppname
end)
in ((uu____3244), (x.FStar_Syntax_Syntax.sort)))
end))))
in (

let fields = fields'
in (

let record = {typename = typename; constrname = constrname.FStar_Ident.ident; parms = parms; fields = fields; is_private_or_abstract = ((FStar_List.contains FStar_Syntax_Syntax.Private tags) || (FStar_List.contains FStar_Syntax_Syntax.Abstract tags)); is_record = is_rec1}
in ((

let uu____3256 = (

let uu____3258 = (FStar_ST.read new_globs)
in (Record_or_dc (record))::uu____3258)
in (FStar_ST.write new_globs uu____3256));
(match (()) with
| () -> begin
((

let add_field = (fun uu____3274 -> (match (uu____3274) with
| (id, uu____3280) -> begin
(

let modul = (

let uu____3286 = (FStar_Ident.lid_of_ids constrname.FStar_Ident.ns)
in uu____3286.FStar_Ident.str)
in (

let uu____3287 = (get_exported_id_set e modul)
in (match (uu____3287) with
| Some (my_ex) -> begin
(

let my_exported_ids = (my_ex Exported_id_field)
in ((

let uu____3303 = (

let uu____3304 = (FStar_ST.read my_exported_ids)
in (FStar_Util.set_add id.FStar_Ident.idText uu____3304))
in (FStar_ST.write my_exported_ids uu____3303));
(match (()) with
| () -> begin
(

let projname = (

let uu____3311 = (

let uu____3312 = (FStar_Syntax_Util.mk_field_projector_name_from_ident constrname id)
in uu____3312.FStar_Ident.ident)
in uu____3311.FStar_Ident.idText)
in (

let uu____3314 = (

let uu____3315 = (FStar_ST.read my_exported_ids)
in (FStar_Util.set_add projname uu____3315))
in (FStar_ST.write my_exported_ids uu____3314)))
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
| uu____3328 -> begin
()
end))
end
| uu____3329 -> begin
()
end))))))
end
| uu____3330 -> begin
()
end))


let try_lookup_record_or_dc_by_field_name : env  ->  FStar_Ident.lident  ->  record_or_dc Prims.option = (fun env fieldname -> (

let find_in_cache = (fun fieldname1 -> (

let uu____3343 = ((fieldname1.FStar_Ident.ns), (fieldname1.FStar_Ident.ident))
in (match (uu____3343) with
| (ns, id) -> begin
(

let uu____3353 = (peek_record_cache ())
in (FStar_Util.find_map uu____3353 (fun record -> (

let uu____3356 = (find_in_record ns id record (fun r -> Cont_ok (r)))
in (option_of_cont (fun uu____3359 -> None) uu____3356)))))
end)))
in (resolve_in_open_namespaces'' env fieldname Exported_id_field (fun uu____3360 -> Cont_ignore) (fun uu____3361 -> Cont_ignore) (fun r -> Cont_ok (r)) (fun fn -> (

let uu____3364 = (find_in_cache fn)
in (cont_of_option Cont_ignore uu____3364))) (fun k uu____3367 -> k))))


let try_lookup_record_by_field_name : env  ->  FStar_Ident.lident  ->  record_or_dc Prims.option = (fun env fieldname -> (

let uu____3376 = (try_lookup_record_or_dc_by_field_name env fieldname)
in (match (uu____3376) with
| Some (r) when r.is_record -> begin
Some (r)
end
| uu____3380 -> begin
None
end)))


let belongs_to_record : env  ->  FStar_Ident.lident  ->  record_or_dc  ->  Prims.bool = (fun env lid record -> (

let uu____3391 = (try_lookup_record_by_field_name env lid)
in (match (uu____3391) with
| Some (record') when (

let uu____3394 = (

let uu____3395 = (FStar_Ident.path_of_ns record.typename.FStar_Ident.ns)
in (FStar_Ident.text_of_path uu____3395))
in (

let uu____3397 = (

let uu____3398 = (FStar_Ident.path_of_ns record'.typename.FStar_Ident.ns)
in (FStar_Ident.text_of_path uu____3398))
in (uu____3394 = uu____3397))) -> begin
(

let uu____3400 = (find_in_record record.typename.FStar_Ident.ns lid.FStar_Ident.ident record (fun uu____3402 -> Cont_ok (())))
in (match (uu____3400) with
| Cont_ok (uu____3403) -> begin
true
end
| uu____3404 -> begin
false
end))
end
| uu____3406 -> begin
false
end)))


let try_lookup_dc_by_field_name : env  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * Prims.bool) Prims.option = (fun env fieldname -> (

let uu____3417 = (try_lookup_record_or_dc_by_field_name env fieldname)
in (match (uu____3417) with
| Some (r) -> begin
(

let uu____3423 = (

let uu____3426 = (

let uu____3427 = (FStar_Ident.lid_of_ids (FStar_List.append r.typename.FStar_Ident.ns ((r.constrname)::[])))
in (FStar_Ident.set_lid_range uu____3427 (FStar_Ident.range_of_lid fieldname)))
in ((uu____3426), (r.is_record)))
in Some (uu____3423))
end
| uu____3430 -> begin
None
end)))


let string_set_ref_new : Prims.unit  ->  Prims.string FStar_Util.set FStar_ST.ref = (fun uu____3439 -> (

let uu____3440 = (FStar_Util.new_set FStar_Util.compare FStar_Util.hashcode)
in (FStar_Util.mk_ref uu____3440)))


let exported_id_set_new : Prims.unit  ->  exported_id_kind  ->  Prims.string FStar_Util.set FStar_ST.ref = (fun uu____3451 -> (

let term_type_set = (string_set_ref_new ())
in (

let field_set = (string_set_ref_new ())
in (fun uu___164_3460 -> (match (uu___164_3460) with
| Exported_id_term_type -> begin
term_type_set
end
| Exported_id_field -> begin
field_set
end)))))


let unique : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  Prims.bool = (fun any_val exclude_if env lid -> (

let filter_scope_mods = (fun uu___165_3480 -> (match (uu___165_3480) with
| Rec_binding (uu____3481) -> begin
true
end
| uu____3482 -> begin
false
end))
in (

let this_env = (

let uu___169_3484 = env
in (

let uu____3485 = (FStar_List.filter filter_scope_mods env.scope_mods)
in {curmodule = uu___169_3484.curmodule; curmonad = uu___169_3484.curmonad; modules = uu___169_3484.modules; scope_mods = uu____3485; exported_ids = empty_exported_id_smap; trans_exported_ids = uu___169_3484.trans_exported_ids; includes = empty_include_smap; sigaccum = uu___169_3484.sigaccum; sigmap = uu___169_3484.sigmap; iface = uu___169_3484.iface; admitted_iface = uu___169_3484.admitted_iface; expect_typ = uu___169_3484.expect_typ; docs = uu___169_3484.docs}))
in (

let uu____3487 = (try_lookup_lid' any_val exclude_if this_env lid)
in (match (uu____3487) with
| None -> begin
true
end
| Some (uu____3493) -> begin
false
end)))))


let push_scope_mod : env  ->  scope_mod  ->  env = (fun env scope_mod -> (

let uu___170_3504 = env
in {curmodule = uu___170_3504.curmodule; curmonad = uu___170_3504.curmonad; modules = uu___170_3504.modules; scope_mods = (scope_mod)::env.scope_mods; exported_ids = uu___170_3504.exported_ids; trans_exported_ids = uu___170_3504.trans_exported_ids; includes = uu___170_3504.includes; sigaccum = uu___170_3504.sigaccum; sigmap = uu___170_3504.sigmap; iface = uu___170_3504.iface; admitted_iface = uu___170_3504.admitted_iface; expect_typ = uu___170_3504.expect_typ; docs = uu___170_3504.docs}))


let push_bv' : env  ->  FStar_Ident.ident  ->  Prims.bool  ->  (env * FStar_Syntax_Syntax.bv) = (fun env x is_mutable -> (

let bv = (FStar_Syntax_Syntax.gen_bv x.FStar_Ident.idText (Some (x.FStar_Ident.idRange)) FStar_Syntax_Syntax.tun)
in (((push_scope_mod env (Local_binding (((x), (bv), (is_mutable)))))), (bv))))


let push_bv_mutable : env  ->  FStar_Ident.ident  ->  (env * FStar_Syntax_Syntax.bv) = (fun env x -> (push_bv' env x true))


let push_bv : env  ->  FStar_Ident.ident  ->  (env * FStar_Syntax_Syntax.bv) = (fun env x -> (push_bv' env x false))


let push_top_level_rec_binding : env  ->  FStar_Ident.ident  ->  FStar_Syntax_Syntax.delta_depth  ->  env = (fun env x dd -> (

let l = (qualify env x)
in (

let uu____3543 = ((unique false true env l) || (FStar_Options.interactive ()))
in (match (uu____3543) with
| true -> begin
(push_scope_mod env (Rec_binding (((x), (l), (dd)))))
end
| uu____3544 -> begin
(Prims.raise (FStar_Errors.Error ((((Prims.strcat "Duplicate top-level names " l.FStar_Ident.str)), ((FStar_Ident.range_of_lid l))))))
end))))


let push_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env s -> (

let err = (fun l -> (

let sopt = (FStar_Util.smap_try_find (sigmap env) l.FStar_Ident.str)
in (

let r = (match (sopt) with
| Some (se, uu____3563) -> begin
(

let uu____3566 = (FStar_Util.find_opt (FStar_Ident.lid_equals l) (FStar_Syntax_Util.lids_of_sigelt se))
in (match (uu____3566) with
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

let uu____3571 = (

let uu____3572 = (

let uu____3575 = (FStar_Util.format2 "Duplicate top-level names [%s]; previously declared at %s" (FStar_Ident.text_of_lid l) r)
in ((uu____3575), ((FStar_Ident.range_of_lid l))))
in FStar_Errors.Error (uu____3572))
in (Prims.raise uu____3571)))))
in (

let globals = (FStar_Util.mk_ref env.scope_mods)
in (

let env1 = (

let uu____3582 = (match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let (uu____3587) -> begin
((false), (true))
end
| FStar_Syntax_Syntax.Sig_bundle (uu____3595) -> begin
((true), (true))
end
| uu____3602 -> begin
((false), (false))
end)
in (match (uu____3582) with
| (any_val, exclude_if) -> begin
(

let lids = (FStar_Syntax_Util.lids_of_sigelt s)
in (

let uu____3607 = (FStar_Util.find_map lids (fun l -> (

let uu____3610 = (

let uu____3611 = (unique any_val exclude_if env l)
in (not (uu____3611)))
in (match (uu____3610) with
| true -> begin
Some (l)
end
| uu____3613 -> begin
None
end))))
in (match (uu____3607) with
| Some (l) when (

let uu____3615 = (FStar_Options.interactive ())
in (not (uu____3615))) -> begin
(err l)
end
| uu____3616 -> begin
((extract_record env globals s);
(

let uu___171_3621 = env
in {curmodule = uu___171_3621.curmodule; curmonad = uu___171_3621.curmonad; modules = uu___171_3621.modules; scope_mods = uu___171_3621.scope_mods; exported_ids = uu___171_3621.exported_ids; trans_exported_ids = uu___171_3621.trans_exported_ids; includes = uu___171_3621.includes; sigaccum = (s)::env.sigaccum; sigmap = uu___171_3621.sigmap; iface = uu___171_3621.iface; admitted_iface = uu___171_3621.admitted_iface; expect_typ = uu___171_3621.expect_typ; docs = uu___171_3621.docs});
)
end)))
end))
in (

let env2 = (

let uu___172_3623 = env1
in (

let uu____3624 = (FStar_ST.read globals)
in {curmodule = uu___172_3623.curmodule; curmonad = uu___172_3623.curmonad; modules = uu___172_3623.modules; scope_mods = uu____3624; exported_ids = uu___172_3623.exported_ids; trans_exported_ids = uu___172_3623.trans_exported_ids; includes = uu___172_3623.includes; sigaccum = uu___172_3623.sigaccum; sigmap = uu___172_3623.sigmap; iface = uu___172_3623.iface; admitted_iface = uu___172_3623.admitted_iface; expect_typ = uu___172_3623.expect_typ; docs = uu___172_3623.docs}))
in (

let uu____3629 = (match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____3643, uu____3644) -> begin
(

let uu____3651 = (FStar_List.map (fun se -> (((FStar_Syntax_Util.lids_of_sigelt se)), (se))) ses)
in ((env2), (uu____3651)))
end
| uu____3665 -> begin
((env2), (((((FStar_Syntax_Util.lids_of_sigelt s)), (s)))::[]))
end)
in (match (uu____3629) with
| (env3, lss) -> begin
((FStar_All.pipe_right lss (FStar_List.iter (fun uu____3695 -> (match (uu____3695) with
| (lids, se) -> begin
(FStar_All.pipe_right lids (FStar_List.iter (fun lid -> ((

let uu____3706 = (

let uu____3708 = (FStar_ST.read globals)
in (Top_level_def (lid.FStar_Ident.ident))::uu____3708)
in (FStar_ST.write globals uu____3706));
(match (()) with
| () -> begin
(

let modul = (

let uu____3717 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in uu____3717.FStar_Ident.str)
in ((

let uu____3719 = (get_exported_id_set env3 modul)
in (match (uu____3719) with
| Some (f) -> begin
(

let my_exported_ids = (f Exported_id_term_type)
in (

let uu____3734 = (

let uu____3735 = (FStar_ST.read my_exported_ids)
in (FStar_Util.set_add lid.FStar_Ident.ident.FStar_Ident.idText uu____3735))
in (FStar_ST.write my_exported_ids uu____3734)))
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

let uu___173_3747 = env3
in (

let uu____3748 = (FStar_ST.read globals)
in {curmodule = uu___173_3747.curmodule; curmonad = uu___173_3747.curmonad; modules = uu___173_3747.modules; scope_mods = uu____3748; exported_ids = uu___173_3747.exported_ids; trans_exported_ids = uu___173_3747.trans_exported_ids; includes = uu___173_3747.includes; sigaccum = uu___173_3747.sigaccum; sigmap = uu___173_3747.sigmap; iface = uu___173_3747.iface; admitted_iface = uu___173_3747.admitted_iface; expect_typ = uu___173_3747.expect_typ; docs = uu___173_3747.docs}))
in env4);
)
end)))))))


let push_namespace : env  ->  FStar_Ident.lident  ->  env = (fun env ns -> (

let uu____3759 = (

let uu____3762 = (resolve_module_name env ns false)
in (match (uu____3762) with
| None -> begin
(

let modules = env.modules
in (

let uu____3770 = (FStar_All.pipe_right modules (FStar_Util.for_some (fun uu____3776 -> (match (uu____3776) with
| (m, uu____3780) -> begin
(FStar_Util.starts_with (Prims.strcat (FStar_Ident.text_of_lid m) ".") (Prims.strcat (FStar_Ident.text_of_lid ns) "."))
end))))
in (match (uu____3770) with
| true -> begin
((ns), (Open_namespace))
end
| uu____3783 -> begin
(

let uu____3784 = (

let uu____3785 = (

let uu____3788 = (FStar_Util.format1 "Namespace %s cannot be found" (FStar_Ident.text_of_lid ns))
in ((uu____3788), ((FStar_Ident.range_of_lid ns))))
in FStar_Errors.Error (uu____3785))
in (Prims.raise uu____3784))
end)))
end
| Some (ns') -> begin
((fail_if_curmodule env ns ns');
((ns'), (Open_module));
)
end))
in (match (uu____3759) with
| (ns', kd) -> begin
(push_scope_mod env (Open_module_or_namespace (((ns'), (kd)))))
end)))


let push_include : env  ->  FStar_Ident.lident  ->  env = (fun env ns -> (

let ns0 = ns
in (

let uu____3802 = (resolve_module_name env ns false)
in (match (uu____3802) with
| Some (ns1) -> begin
((fail_if_curmodule env ns0 ns1);
(

let env1 = (push_scope_mod env (Open_module_or_namespace (((ns1), (Open_module)))))
in (

let curmod = (

let uu____3808 = (current_module env1)
in uu____3808.FStar_Ident.str)
in ((

let uu____3810 = (FStar_Util.smap_try_find env1.includes curmod)
in (match (uu____3810) with
| None -> begin
()
end
| Some (incl) -> begin
(

let uu____3823 = (

let uu____3825 = (FStar_ST.read incl)
in (ns1)::uu____3825)
in (FStar_ST.write incl uu____3823))
end));
(match (()) with
| () -> begin
(

let uu____3833 = (get_trans_exported_id_set env1 ns1.FStar_Ident.str)
in (match (uu____3833) with
| Some (ns_trans_exports) -> begin
((

let uu____3846 = (

let uu____3857 = (get_exported_id_set env1 curmod)
in (

let uu____3862 = (get_trans_exported_id_set env1 curmod)
in ((uu____3857), (uu____3862))))
in (match (uu____3846) with
| (Some (cur_exports), Some (cur_trans_exports)) -> begin
(

let update_exports = (fun k -> (

let ns_ex = (

let uu____3902 = (ns_trans_exports k)
in (FStar_ST.read uu____3902))
in (

let ex = (cur_exports k)
in ((

let uu____3911 = (

let uu____3912 = (FStar_ST.read ex)
in (FStar_Util.set_difference uu____3912 ns_ex))
in (FStar_ST.write ex uu____3911));
(match (()) with
| () -> begin
(

let trans_ex = (cur_trans_exports k)
in (

let uu____3922 = (

let uu____3923 = (FStar_ST.read trans_ex)
in (FStar_Util.set_union uu____3923 ns_ex))
in (FStar_ST.write trans_ex uu____3922)))
end);
))))
in (FStar_List.iter update_exports all_exported_id_kinds))
end
| uu____3929 -> begin
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

let uu____3943 = (

let uu____3944 = (

let uu____3947 = (FStar_Util.format1 "include: Module %s was not prepared" ns1.FStar_Ident.str)
in ((uu____3947), ((FStar_Ident.range_of_lid ns1))))
in FStar_Errors.Error (uu____3944))
in (Prims.raise uu____3943))
end))
end);
)));
)
end
| uu____3948 -> begin
(

let uu____3950 = (

let uu____3951 = (

let uu____3954 = (FStar_Util.format1 "include: Module %s cannot be found" ns.FStar_Ident.str)
in ((uu____3954), ((FStar_Ident.range_of_lid ns))))
in FStar_Errors.Error (uu____3951))
in (Prims.raise uu____3950))
end))))


let push_module_abbrev : env  ->  FStar_Ident.ident  ->  FStar_Ident.lident  ->  env = (fun env x l -> (

let uu____3964 = (module_is_defined env l)
in (match (uu____3964) with
| true -> begin
((fail_if_curmodule env l l);
(push_scope_mod env (Module_abbrev (((x), (l)))));
)
end
| uu____3966 -> begin
(

let uu____3967 = (

let uu____3968 = (

let uu____3971 = (FStar_Util.format1 "Module %s cannot be found" (FStar_Ident.text_of_lid l))
in ((uu____3971), ((FStar_Ident.range_of_lid l))))
in FStar_Errors.Error (uu____3968))
in (Prims.raise uu____3967))
end)))


let push_doc : env  ->  FStar_Ident.lident  ->  FStar_Parser_AST.fsdoc Prims.option  ->  env = (fun env l doc_opt -> (match (doc_opt) with
| None -> begin
env
end
| Some (doc1) -> begin
((

let uu____3985 = (FStar_Util.smap_try_find env.docs l.FStar_Ident.str)
in (match (uu____3985) with
| None -> begin
()
end
| Some (old_doc) -> begin
(

let uu____3988 = (

let uu____3989 = (FStar_Ident.string_of_lid l)
in (

let uu____3990 = (FStar_Parser_AST.string_of_fsdoc old_doc)
in (

let uu____3991 = (FStar_Parser_AST.string_of_fsdoc doc1)
in (FStar_Util.format3 "Overwriting doc of %s; old doc was [%s]; new doc are [%s]" uu____3989 uu____3990 uu____3991))))
in (FStar_Errors.warn (FStar_Ident.range_of_lid l) uu____3988))
end));
(FStar_Util.smap_add env.docs l.FStar_Ident.str doc1);
env;
)
end))


let check_admits : env  ->  Prims.unit = (fun env -> (FStar_All.pipe_right env.sigaccum (FStar_List.iter (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_declare_typ (l, u, t, quals) -> begin
(

let uu____4003 = (try_lookup_lid env l)
in (match (uu____4003) with
| None -> begin
((

let uu____4010 = (

let uu____4011 = (FStar_Options.interactive ())
in (not (uu____4011)))
in (match (uu____4010) with
| true -> begin
(

let uu____4012 = (

let uu____4013 = (FStar_Range.string_of_range (FStar_Ident.range_of_lid l))
in (

let uu____4014 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format2 "%s: Warning: Admitting %s without a definition\n" uu____4013 uu____4014)))
in (FStar_Util.print_string uu____4012))
end
| uu____4015 -> begin
()
end));
(FStar_Util.smap_add (sigmap env) l.FStar_Ident.str (((

let uu___174_4018 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((l), (u), (t), ((FStar_Syntax_Syntax.Assumption)::quals))); FStar_Syntax_Syntax.sigrng = uu___174_4018.FStar_Syntax_Syntax.sigrng})), (false)));
)
end
| Some (uu____4020) -> begin
()
end))
end
| uu____4025 -> begin
()
end)))))


let finish : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env modul -> ((FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations (FStar_List.iter (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, uu____4036) -> begin
(match (((FStar_List.contains FStar_Syntax_Syntax.Private quals) || (FStar_List.contains FStar_Syntax_Syntax.Abstract quals))) with
| true -> begin
(FStar_All.pipe_right ses (FStar_List.iter (fun se1 -> (match (se1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (lid, uu____4046, uu____4047, uu____4048, uu____4049, uu____4050, uu____4051) -> begin
(FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str)
end
| uu____4058 -> begin
()
end))))
end
| uu____4059 -> begin
()
end)
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____4061, uu____4062, quals) -> begin
(match ((FStar_List.contains FStar_Syntax_Syntax.Private quals)) with
| true -> begin
(FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str)
end
| uu____4068 -> begin
()
end)
end
| FStar_Syntax_Syntax.Sig_let ((uu____4069, lbs), uu____4071, quals, uu____4073) -> begin
((match (((FStar_List.contains FStar_Syntax_Syntax.Private quals) || (FStar_List.contains FStar_Syntax_Syntax.Abstract quals))) with
| true -> begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (

let uu____4088 = (

let uu____4089 = (

let uu____4090 = (

let uu____4095 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in uu____4095.FStar_Syntax_Syntax.fv_name)
in uu____4090.FStar_Syntax_Syntax.v)
in uu____4089.FStar_Ident.str)
in (FStar_Util.smap_remove (sigmap env) uu____4088)))))
end
| uu____4101 -> begin
()
end);
(match (((FStar_List.contains FStar_Syntax_Syntax.Abstract quals) && (not ((FStar_List.contains FStar_Syntax_Syntax.Private quals))))) with
| true -> begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (

let lid = (

let uu____4105 = (

let uu____4110 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in uu____4110.FStar_Syntax_Syntax.fv_name)
in uu____4105.FStar_Syntax_Syntax.v)
in (

let decl = (

let uu___175_4115 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), ((FStar_Syntax_Syntax.Assumption)::quals))); FStar_Syntax_Syntax.sigrng = uu___175_4115.FStar_Syntax_Syntax.sigrng})
in (FStar_Util.smap_add (sigmap env) lid.FStar_Ident.str ((decl), (false))))))))
end
| uu____4122 -> begin
()
end);
)
end
| uu____4123 -> begin
()
end))));
(

let curmod = (

let uu____4125 = (current_module env)
in uu____4125.FStar_Ident.str)
in ((

let uu____4127 = (

let uu____4138 = (get_exported_id_set env curmod)
in (

let uu____4143 = (get_trans_exported_id_set env curmod)
in ((uu____4138), (uu____4143))))
in (match (uu____4127) with
| (Some (cur_ex), Some (cur_trans_ex)) -> begin
(

let update_exports = (fun eikind -> (

let cur_ex_set = (

let uu____4183 = (cur_ex eikind)
in (FStar_ST.read uu____4183))
in (

let cur_trans_ex_set_ref = (cur_trans_ex eikind)
in (

let uu____4191 = (

let uu____4192 = (FStar_ST.read cur_trans_ex_set_ref)
in (FStar_Util.set_union cur_ex_set uu____4192))
in (FStar_ST.write cur_trans_ex_set_ref uu____4191)))))
in (FStar_List.iter update_exports all_exported_id_kinds))
end
| uu____4198 -> begin
()
end));
(match (()) with
| () -> begin
((filter_record_cache ());
(match (()) with
| () -> begin
(

let uu___176_4210 = env
in {curmodule = None; curmonad = uu___176_4210.curmonad; modules = (((modul.FStar_Syntax_Syntax.name), (modul)))::env.modules; scope_mods = []; exported_ids = uu___176_4210.exported_ids; trans_exported_ids = uu___176_4210.trans_exported_ids; includes = uu___176_4210.includes; sigaccum = []; sigmap = uu___176_4210.sigmap; iface = uu___176_4210.iface; admitted_iface = uu___176_4210.admitted_iface; expect_typ = uu___176_4210.expect_typ; docs = uu___176_4210.docs})
end);
)
end);
));
))


let stack : env Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let push : env  ->  env = (fun env -> ((push_record_cache ());
(

let uu____4223 = (

let uu____4225 = (FStar_ST.read stack)
in (env)::uu____4225)
in (FStar_ST.write stack uu____4223));
(

let uu___177_4233 = env
in (

let uu____4234 = (FStar_Util.smap_copy (sigmap env))
in (

let uu____4240 = (FStar_Util.smap_copy env.docs)
in {curmodule = uu___177_4233.curmodule; curmonad = uu___177_4233.curmonad; modules = uu___177_4233.modules; scope_mods = uu___177_4233.scope_mods; exported_ids = uu___177_4233.exported_ids; trans_exported_ids = uu___177_4233.trans_exported_ids; includes = uu___177_4233.includes; sigaccum = uu___177_4233.sigaccum; sigmap = uu____4234; iface = uu___177_4233.iface; admitted_iface = uu___177_4233.admitted_iface; expect_typ = uu___177_4233.expect_typ; docs = uu____4240})));
))


let pop : Prims.unit  ->  env = (fun uu____4244 -> (

let uu____4245 = (FStar_ST.read stack)
in (match (uu____4245) with
| (env)::tl1 -> begin
((pop_record_cache ());
(FStar_ST.write stack tl1);
env;
)
end
| uu____4258 -> begin
(failwith "Impossible: Too many pops")
end)))


let commit_mark : env  ->  env = (fun env -> ((commit_record_cache ());
(

let uu____4264 = (FStar_ST.read stack)
in (match (uu____4264) with
| (uu____4269)::tl1 -> begin
((FStar_ST.write stack tl1);
env;
)
end
| uu____4276 -> begin
(failwith "Impossible: Too many pops")
end));
))


let mark : env  ->  env = (fun x -> (push x))


let reset_mark : Prims.unit  ->  env = (fun uu____4283 -> (pop ()))


let export_interface : FStar_Ident.lident  ->  env  ->  env = (fun m env -> (

let sigelt_in_m = (fun se -> (match ((FStar_Syntax_Util.lids_of_sigelt se)) with
| (l)::uu____4295 -> begin
(l.FStar_Ident.nsstr = m.FStar_Ident.str)
end
| uu____4297 -> begin
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

let uu____4315 = (FStar_Util.smap_try_find sm' k)
in (match (uu____4315) with
| Some (se, true) when (sigelt_in_m se) -> begin
((FStar_Util.smap_remove sm' k);
(

let se1 = (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_declare_typ (l, u, t, q) -> begin
(

let uu___178_4334 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((l), (u), (t), ((FStar_Syntax_Syntax.Assumption)::q))); FStar_Syntax_Syntax.sigrng = uu___178_4334.FStar_Syntax_Syntax.sigrng})
end
| uu____4336 -> begin
se
end)
in (FStar_Util.smap_add sm' k ((se1), (false))));
)
end
| uu____4339 -> begin
()
end)))));
env1;
)))))))


let finish_module_or_interface : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env modul -> ((match ((not (modul.FStar_Syntax_Syntax.is_interface))) with
| true -> begin
(check_admits env)
end
| uu____4350 -> begin
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
| uu____4372 -> begin
(match ((FStar_Util.starts_with "FStar." (FStar_Ident.text_of_lid mname))) with
| true -> begin
(FStar_Syntax_Const.prims_lid)::(FStar_Syntax_Const.fstar_ns_lid)::[]
end
| uu____4374 -> begin
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
| uu____4381 -> begin
open_ns
end)
in ((

let uu____4383 = (exported_id_set_new ())
in (FStar_Util.smap_add env1.exported_ids mname.FStar_Ident.str uu____4383));
(match (()) with
| () -> begin
((

let uu____4388 = (exported_id_set_new ())
in (FStar_Util.smap_add env1.trans_exported_ids mname.FStar_Ident.str uu____4388));
(match (()) with
| () -> begin
((

let uu____4393 = (FStar_Util.mk_ref [])
in (FStar_Util.smap_add env1.includes mname.FStar_Ident.str uu____4393));
(match (()) with
| () -> begin
(

let uu___179_4402 = env1
in (

let uu____4403 = (FStar_List.map (fun lid -> Open_module_or_namespace (((lid), (Open_namespace)))) open_ns1)
in {curmodule = Some (mname); curmonad = uu___179_4402.curmonad; modules = uu___179_4402.modules; scope_mods = uu____4403; exported_ids = uu___179_4402.exported_ids; trans_exported_ids = uu___179_4402.trans_exported_ids; includes = uu___179_4402.includes; sigaccum = uu___179_4402.sigaccum; sigmap = env1.sigmap; iface = intf; admitted_iface = admitted; expect_typ = uu___179_4402.expect_typ; docs = uu___179_4402.docs}))
end);
)
end);
)
end);
))))
in (

let uu____4406 = (FStar_All.pipe_right env.modules (FStar_Util.find_opt (fun uu____4418 -> (match (uu____4418) with
| (l, uu____4422) -> begin
(FStar_Ident.lid_equals l mname)
end))))
in (match (uu____4406) with
| None -> begin
(

let uu____4427 = (prep env)
in ((uu____4427), (false)))
end
| Some (uu____4428, m) -> begin
((

let uu____4433 = ((

let uu____4434 = (FStar_Options.interactive ())
in (not (uu____4434))) && ((not (m.FStar_Syntax_Syntax.is_interface)) || intf))
in (match (uu____4433) with
| true -> begin
(

let uu____4435 = (

let uu____4436 = (

let uu____4439 = (FStar_Util.format1 "Duplicate module or interface name: %s" mname.FStar_Ident.str)
in ((uu____4439), ((FStar_Ident.range_of_lid mname))))
in FStar_Errors.Error (uu____4436))
in (Prims.raise uu____4435))
end
| uu____4440 -> begin
()
end));
(

let uu____4441 = (

let uu____4442 = (push env)
in (prep uu____4442))
in ((uu____4441), (true)));
)
end))))


let enter_monad_scope : env  ->  FStar_Ident.ident  ->  env = (fun env mname -> (match (env.curmonad) with
| Some (mname') -> begin
(Prims.raise (FStar_Errors.Error ((((Prims.strcat "Trying to define monad " (Prims.strcat mname.FStar_Ident.idText (Prims.strcat ", but already in monad scope " mname'.FStar_Ident.idText)))), (mname.FStar_Ident.idRange)))))
end
| None -> begin
(

let uu___180_4450 = env
in {curmodule = uu___180_4450.curmodule; curmonad = Some (mname); modules = uu___180_4450.modules; scope_mods = uu___180_4450.scope_mods; exported_ids = uu___180_4450.exported_ids; trans_exported_ids = uu___180_4450.trans_exported_ids; includes = uu___180_4450.includes; sigaccum = uu___180_4450.sigaccum; sigmap = uu___180_4450.sigmap; iface = uu___180_4450.iface; admitted_iface = uu___180_4450.admitted_iface; expect_typ = uu___180_4450.expect_typ; docs = uu___180_4450.docs})
end))


let fail_or = (fun env lookup lid -> (

let uu____4475 = (lookup lid)
in (match (uu____4475) with
| None -> begin
(

let opened_modules = (FStar_List.map (fun uu____4481 -> (match (uu____4481) with
| (lid1, uu____4485) -> begin
(FStar_Ident.text_of_lid lid1)
end)) env.modules)
in (

let msg = (FStar_Util.format1 "Identifier not found: [%s]" (FStar_Ident.text_of_lid lid))
in (

let msg1 = (match (((FStar_List.length lid.FStar_Ident.ns) = (Prims.parse_int "0"))) with
| true -> begin
msg
end
| uu____4490 -> begin
(

let modul = (

let uu____4492 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in (FStar_Ident.set_lid_range uu____4492 (FStar_Ident.range_of_lid lid)))
in (

let uu____4493 = (resolve_module_name env modul true)
in (match (uu____4493) with
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

let uu____4520 = (lookup id)
in (match (uu____4520) with
| None -> begin
(Prims.raise (FStar_Errors.Error ((((Prims.strcat "Identifier not found [" (Prims.strcat id.FStar_Ident.idText "]"))), (id.FStar_Ident.idRange)))))
end
| Some (r) -> begin
r
end)))




