
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


let namespace_is_open : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (FStar_List.existsb (fun uu___148_1208 -> (match (uu___148_1208) with
| Open_module_or_namespace (ns, Open_namespace) -> begin
(FStar_Ident.lid_equals lid ns)
end
| uu____1210 -> begin
false
end)) env.scope_mods))


let shorten_module_path : env  ->  FStar_Ident.ident Prims.list  ->  Prims.bool  ->  (FStar_Ident.ident Prims.list * FStar_Ident.ident Prims.list) = (fun env ids is_full_path -> (

let rec aux = (fun revns id -> (

let lid = (FStar_Ident.lid_of_ns_and_id (FStar_List.rev revns) id)
in (match ((namespace_is_open env lid)) with
| true -> begin
Some ((((FStar_List.rev ((id)::revns))), ([])))
end
| uu____1252 -> begin
(match (revns) with
| [] -> begin
None
end
| (ns_last_id)::rev_ns_prefix -> begin
(

let uu____1265 = (aux rev_ns_prefix ns_last_id)
in (FStar_All.pipe_right uu____1265 (FStar_Util.map_option (fun uu____1289 -> (match (uu____1289) with
| (stripped_ids, rev_kept_ids) -> begin
((stripped_ids), ((id)::rev_kept_ids))
end)))))
end)
end)))
in (

let uu____1306 = (is_full_path && (

let uu____1307 = (FStar_Ident.lid_of_ids ids)
in (module_is_defined env uu____1307)))
in (match (uu____1306) with
| true -> begin
((ids), ([]))
end
| uu____1314 -> begin
(match ((FStar_List.rev ids)) with
| [] -> begin
(([]), ([]))
end
| (ns_last_id)::ns_rev_prefix -> begin
(

let uu____1324 = (aux ns_rev_prefix ns_last_id)
in (match (uu____1324) with
| None -> begin
(([]), (ids))
end
| Some (stripped_ids, rev_kept_ids) -> begin
((stripped_ids), ((FStar_List.rev rev_kept_ids)))
end))
end)
end))))


let resolve_in_open_namespaces'' = (fun env lid eikind k_local_binding k_rec_binding k_record f_module l_default -> (match (lid.FStar_Ident.ns) with
| (uu____1437)::uu____1438 -> begin
(

let uu____1440 = (

let uu____1442 = (

let uu____1443 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in (FStar_Ident.set_lid_range uu____1443 (FStar_Ident.range_of_lid lid)))
in (resolve_module_name env uu____1442 true))
in (match (uu____1440) with
| None -> begin
None
end
| Some (modul) -> begin
(

let uu____1446 = (find_in_module_with_includes eikind f_module Cont_fail env modul lid.FStar_Ident.ident)
in (option_of_cont (fun uu____1448 -> None) uu____1446))
end))
end
| [] -> begin
(try_lookup_id'' env lid.FStar_Ident.ident eikind k_local_binding k_rec_binding k_record f_module l_default)
end))


let cont_of_option = (fun k_none uu___149_1463 -> (match (uu___149_1463) with
| Some (v1) -> begin
Cont_ok (v1)
end
| None -> begin
k_none
end))


let resolve_in_open_namespaces' = (fun env lid k_local_binding k_rec_binding k_global_def -> (

let k_global_def' = (fun k lid1 def -> (

let uu____1542 = (k_global_def lid1 def)
in (cont_of_option k uu____1542)))
in (

let f_module = (fun lid' -> (

let k = Cont_ignore
in (find_in_module env lid' (k_global_def' k) k)))
in (

let l_default = (fun k i -> (lookup_default_id env i (k_global_def' k) k))
in (resolve_in_open_namespaces'' env lid Exported_id_term_type (fun l -> (

let uu____1563 = (k_local_binding l)
in (cont_of_option Cont_fail uu____1563))) (fun r -> (

let uu____1566 = (k_rec_binding r)
in (cont_of_option Cont_fail uu____1566))) (fun uu____1568 -> Cont_ignore) f_module l_default)))))


let fv_qual_of_se : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.fv_qual Prims.option = (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (uu____1574, uu____1575, uu____1576, l, uu____1578, quals, uu____1580) -> begin
(

let qopt = (FStar_Util.find_map quals (fun uu___150_1587 -> (match (uu___150_1587) with
| FStar_Syntax_Syntax.RecordConstructor (uu____1589, fs) -> begin
Some (FStar_Syntax_Syntax.Record_ctor (((l), (fs))))
end
| uu____1596 -> begin
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
| FStar_Syntax_Syntax.Sig_declare_typ (uu____1600, uu____1601, uu____1602, quals) -> begin
None
end
| uu____1606 -> begin
None
end))


let lb_fv : FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.fv = (fun lbs lid -> (

let uu____1615 = (FStar_Util.find_map lbs (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let uu____1619 = (FStar_Syntax_Syntax.fv_eq_lid fv lid)
in (match (uu____1619) with
| true -> begin
Some (fv)
end
| uu____1621 -> begin
None
end)))))
in (FStar_All.pipe_right uu____1615 FStar_Util.must)))


let ns_of_lid_equals : FStar_Ident.lident  ->  FStar_Ident.lident  ->  Prims.bool = (fun lid ns -> (((FStar_List.length lid.FStar_Ident.ns) = (FStar_List.length (FStar_Ident.ids_of_lid ns))) && (

let uu____1633 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in (FStar_Ident.lid_equals uu____1633 ns))))


let try_lookup_name : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  foundname Prims.option = (fun any_val exclude_interf env lid -> (

let occurrence_range = (FStar_Ident.range_of_lid lid)
in (

let k_global_def = (fun source_lid uu___154_1658 -> (match (uu___154_1658) with
| (uu____1662, true) when exclude_interf -> begin
None
end
| (se, uu____1664) -> begin
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____1666) -> begin
(

let uu____1677 = (

let uu____1678 = (

let uu____1681 = (FStar_Syntax_Syntax.fvar source_lid FStar_Syntax_Syntax.Delta_constant None)
in ((uu____1681), (false)))
in Term_name (uu____1678))
in Some (uu____1677))
end
| FStar_Syntax_Syntax.Sig_datacon (uu____1682) -> begin
(

let uu____1692 = (

let uu____1693 = (

let uu____1696 = (

let uu____1697 = (fv_qual_of_se se)
in (FStar_Syntax_Syntax.fvar source_lid FStar_Syntax_Syntax.Delta_constant uu____1697))
in ((uu____1696), (false)))
in Term_name (uu____1693))
in Some (uu____1692))
end
| FStar_Syntax_Syntax.Sig_let ((uu____1699, lbs), uu____1701, uu____1702, uu____1703) -> begin
(

let fv = (lb_fv lbs source_lid)
in (

let uu____1716 = (

let uu____1717 = (

let uu____1720 = (FStar_Syntax_Syntax.fvar source_lid fv.FStar_Syntax_Syntax.fv_delta fv.FStar_Syntax_Syntax.fv_qual)
in ((uu____1720), (false)))
in Term_name (uu____1717))
in Some (uu____1716)))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid1, uu____1722, uu____1723, quals) -> begin
(

let uu____1727 = (any_val || (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___151_1729 -> (match (uu___151_1729) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| uu____1730 -> begin
false
end)))))
in (match (uu____1727) with
| true -> begin
(

let lid2 = (FStar_Ident.set_lid_range lid1 (FStar_Ident.range_of_lid source_lid))
in (

let dd = (

let uu____1734 = ((FStar_Syntax_Util.is_primop_lid lid2) || ((ns_of_lid_equals lid2 FStar_Syntax_Const.prims_lid) && (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___152_1736 -> (match (uu___152_1736) with
| (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) -> begin
true
end
| uu____1739 -> begin
false
end))))))
in (match (uu____1734) with
| true -> begin
FStar_Syntax_Syntax.Delta_equational
end
| uu____1740 -> begin
FStar_Syntax_Syntax.Delta_constant
end))
in (

let uu____1741 = (FStar_Util.find_map quals (fun uu___153_1743 -> (match (uu___153_1743) with
| FStar_Syntax_Syntax.Reflectable (refl_monad) -> begin
Some (refl_monad)
end
| uu____1746 -> begin
None
end)))
in (match (uu____1741) with
| Some (refl_monad) -> begin
(

let refl_const = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (refl_monad)))) None occurrence_range)
in Some (Term_name (((refl_const), (false)))))
end
| uu____1762 -> begin
(

let uu____1764 = (

let uu____1765 = (

let uu____1768 = (

let uu____1769 = (fv_qual_of_se se)
in (FStar_Syntax_Syntax.fvar lid2 dd uu____1769))
in ((uu____1768), (false)))
in Term_name (uu____1765))
in Some (uu____1764))
end))))
end
| uu____1771 -> begin
None
end))
end
| (FStar_Syntax_Syntax.Sig_new_effect_for_free (ne)) | (FStar_Syntax_Syntax.Sig_new_effect (ne)) -> begin
Some (Eff_name (((se), ((FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname (FStar_Ident.range_of_lid source_lid))))))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (uu____1773) -> begin
Some (Eff_name (((se), (source_lid))))
end
| uu____1782 -> begin
None
end)
end))
in (

let k_local_binding = (fun r -> (

let uu____1794 = (

let uu____1795 = (found_local_binding (FStar_Ident.range_of_lid lid) r)
in Term_name (uu____1795))
in Some (uu____1794)))
in (

let k_rec_binding = (fun uu____1805 -> (match (uu____1805) with
| (id, l, dd) -> begin
(

let uu____1813 = (

let uu____1814 = (

let uu____1817 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range l (FStar_Ident.range_of_lid lid)) dd None)
in ((uu____1817), (false)))
in Term_name (uu____1814))
in Some (uu____1813))
end))
in (

let found_unmangled = (match (lid.FStar_Ident.ns) with
| [] -> begin
(

let uu____1821 = (unmangleOpName lid.FStar_Ident.ident)
in (match (uu____1821) with
| Some (f) -> begin
Some (Term_name (f))
end
| uu____1831 -> begin
None
end))
end
| uu____1835 -> begin
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

let uu____1855 = (try_lookup_name true exclude_interf env lid)
in (match (uu____1855) with
| Some (Eff_name (o, l)) -> begin
Some (((o), (l)))
end
| uu____1864 -> begin
None
end)))


let try_lookup_effect_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env l -> (

let uu____1875 = (try_lookup_effect_name' (not (env.iface)) env l)
in (match (uu____1875) with
| Some (o, l1) -> begin
Some (l1)
end
| uu____1884 -> begin
None
end)))


let try_lookup_effect_name_and_attributes : env  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.cflags Prims.list) Prims.option = (fun env l -> (

let uu____1898 = (try_lookup_effect_name' (not (env.iface)) env l)
in (match (uu____1898) with
| Some ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect (ne); FStar_Syntax_Syntax.sigrng = uu____1907}, l1) -> begin
Some (((l1), (ne.FStar_Syntax_Syntax.cattributes)))
end
| Some ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect_for_free (ne); FStar_Syntax_Syntax.sigrng = uu____1916}, l1) -> begin
Some (((l1), (ne.FStar_Syntax_Syntax.cattributes)))
end
| Some ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_effect_abbrev (uu____1924, uu____1925, uu____1926, uu____1927, uu____1928, cattributes); FStar_Syntax_Syntax.sigrng = uu____1930}, l1) -> begin
Some (((l1), (cattributes)))
end
| uu____1942 -> begin
None
end)))


let try_lookup_effect_defn : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl Prims.option = (fun env l -> (

let uu____1956 = (try_lookup_effect_name' (not (env.iface)) env l)
in (match (uu____1956) with
| Some ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect (ne); FStar_Syntax_Syntax.sigrng = uu____1962}, uu____1963) -> begin
Some (ne)
end
| Some ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect_for_free (ne); FStar_Syntax_Syntax.sigrng = uu____1967}, uu____1968) -> begin
Some (ne)
end
| uu____1971 -> begin
None
end)))


let is_effect_name : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let uu____1981 = (try_lookup_effect_name env lid)
in (match (uu____1981) with
| None -> begin
false
end
| Some (uu____1983) -> begin
true
end)))


let try_lookup_root_effect_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env l -> (

let uu____1991 = (try_lookup_effect_name' (not (env.iface)) env l)
in (match (uu____1991) with
| Some ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_effect_abbrev (l', uu____1997, uu____1998, uu____1999, uu____2000, uu____2001); FStar_Syntax_Syntax.sigrng = uu____2002}, uu____2003) -> begin
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
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (lid2, uu____2073, uu____2074, quals); FStar_Syntax_Syntax.sigrng = uu____2076}, uu____2077) -> begin
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

let k_global_def = (fun lid1 uu___156_2146 -> (match (uu___156_2146) with
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let ((uu____2150, lbs), uu____2152, uu____2153, uu____2154); FStar_Syntax_Syntax.sigrng = uu____2155}, uu____2156) -> begin
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

let k_global_def = (fun lid1 uu___157_2193 -> (match (uu___157_2193) with
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (lbs, uu____2200, uu____2201, uu____2202); FStar_Syntax_Syntax.sigrng = uu____2203}, uu____2204) -> begin
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

let uu___168_2324 = env
in {curmodule = uu___168_2324.curmodule; curmonad = uu___168_2324.curmonad; modules = uu___168_2324.modules; scope_mods = []; exported_ids = empty_exported_id_smap; trans_exported_ids = uu___168_2324.trans_exported_ids; includes = empty_include_smap; sigaccum = uu___168_2324.sigaccum; sigmap = uu___168_2324.sigmap; iface = uu___168_2324.iface; admitted_iface = uu___168_2324.admitted_iface; expect_typ = uu___168_2324.expect_typ; docs = uu___168_2324.docs})
in (try_lookup_lid env' l)))


let try_lookup_doc : env  ->  FStar_Ident.lid  ->  FStar_Parser_AST.fsdoc Prims.option = (fun env l -> (FStar_Util.smap_try_find env.docs l.FStar_Ident.str))


let try_lookup_datacon : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.fv Prims.option = (fun env lid -> (

let k_global_def = (fun lid1 uu___159_2348 -> (match (uu___159_2348) with
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (uu____2352, uu____2353, uu____2354, quals); FStar_Syntax_Syntax.sigrng = uu____2356}, uu____2357) -> begin
(

let uu____2360 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___158_2362 -> (match (uu___158_2362) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| uu____2363 -> begin
false
end))))
in (match (uu____2360) with
| true -> begin
(

let uu____2365 = (FStar_Syntax_Syntax.lid_as_fv lid1 FStar_Syntax_Syntax.Delta_constant None)
in Some (uu____2365))
end
| uu____2366 -> begin
None
end))
end
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (uu____2367); FStar_Syntax_Syntax.sigrng = uu____2368}, uu____2369) -> begin
(

let uu____2379 = (FStar_Syntax_Syntax.lid_as_fv lid1 FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in Some (uu____2379))
end
| uu____2380 -> begin
None
end))
in (resolve_in_open_namespaces' env lid (fun uu____2383 -> None) (fun uu____2384 -> None) k_global_def)))


let find_all_datacons : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.list Prims.option = (fun env lid -> (

let k_global_def = (fun lid1 uu___160_2403 -> (match (uu___160_2403) with
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (uu____2408, uu____2409, uu____2410, uu____2411, uu____2412, datas, uu____2414); FStar_Syntax_Syntax.sigrng = uu____2415}, uu____2416) -> begin
Some (datas)
end
| uu____2424 -> begin
None
end))
in (resolve_in_open_namespaces' env lid (fun uu____2429 -> None) (fun uu____2431 -> None) k_global_def)))


let record_cache_aux_with_filter : (((Prims.unit  ->  Prims.unit) * (Prims.unit  ->  Prims.unit) * (Prims.unit  ->  record_or_dc Prims.list) * (record_or_dc  ->  Prims.unit) * (Prims.unit  ->  Prims.unit)) * (Prims.unit  ->  Prims.unit)) = (

let record_cache = (FStar_Util.mk_ref (([])::[]))
in (

let push1 = (fun uu____2465 -> (

let uu____2466 = (

let uu____2469 = (

let uu____2471 = (FStar_ST.read record_cache)
in (FStar_List.hd uu____2471))
in (

let uu____2479 = (FStar_ST.read record_cache)
in (uu____2469)::uu____2479))
in (FStar_ST.write record_cache uu____2466)))
in (

let pop1 = (fun uu____2494 -> (

let uu____2495 = (

let uu____2498 = (FStar_ST.read record_cache)
in (FStar_List.tl uu____2498))
in (FStar_ST.write record_cache uu____2495)))
in (

let peek = (fun uu____2514 -> (

let uu____2515 = (FStar_ST.read record_cache)
in (FStar_List.hd uu____2515)))
in (

let insert = (fun r -> (

let uu____2527 = (

let uu____2530 = (

let uu____2532 = (peek ())
in (r)::uu____2532)
in (

let uu____2534 = (

let uu____2537 = (FStar_ST.read record_cache)
in (FStar_List.tl uu____2537))
in (uu____2530)::uu____2534))
in (FStar_ST.write record_cache uu____2527)))
in (

let commit1 = (fun uu____2553 -> (

let uu____2554 = (FStar_ST.read record_cache)
in (match (uu____2554) with
| (hd1)::(uu____2562)::tl1 -> begin
(FStar_ST.write record_cache ((hd1)::tl1))
end
| uu____2575 -> begin
(failwith "Impossible")
end)))
in (

let filter1 = (fun uu____2581 -> (

let rc = (peek ())
in ((pop1 ());
(match (()) with
| () -> begin
(

let filtered = (FStar_List.filter (fun r -> (not (r.is_private_or_abstract))) rc)
in (

let uu____2588 = (

let uu____2591 = (FStar_ST.read record_cache)
in (filtered)::uu____2591)
in (FStar_ST.write record_cache uu____2588)))
end);
)))
in (

let aux = ((push1), (pop1), (peek), (insert), (commit1))
in ((aux), (filter1))))))))))


let record_cache_aux : ((Prims.unit  ->  Prims.unit) * (Prims.unit  ->  Prims.unit) * (Prims.unit  ->  record_or_dc Prims.list) * (record_or_dc  ->  Prims.unit) * (Prims.unit  ->  Prims.unit)) = (

let uu____2665 = record_cache_aux_with_filter
in (match (uu____2665) with
| (aux, uu____2703) -> begin
aux
end))


let filter_record_cache : Prims.unit  ->  Prims.unit = (

let uu____2742 = record_cache_aux_with_filter
in (match (uu____2742) with
| (uu____2765, filter1) -> begin
filter1
end))


let push_record_cache : Prims.unit  ->  Prims.unit = (

let uu____2805 = record_cache_aux
in (match (uu____2805) with
| (push1, uu____2825, uu____2826, uu____2827, uu____2828) -> begin
push1
end))


let pop_record_cache : Prims.unit  ->  Prims.unit = (

let uu____2853 = record_cache_aux
in (match (uu____2853) with
| (uu____2872, pop1, uu____2874, uu____2875, uu____2876) -> begin
pop1
end))


let peek_record_cache : Prims.unit  ->  record_or_dc Prims.list = (

let uu____2902 = record_cache_aux
in (match (uu____2902) with
| (uu____2922, uu____2923, peek, uu____2925, uu____2926) -> begin
peek
end))


let insert_record_cache : record_or_dc  ->  Prims.unit = (

let uu____2951 = record_cache_aux
in (match (uu____2951) with
| (uu____2970, uu____2971, uu____2972, insert, uu____2974) -> begin
insert
end))


let commit_record_cache : Prims.unit  ->  Prims.unit = (

let uu____2999 = record_cache_aux
in (match (uu____2999) with
| (uu____3018, uu____3019, uu____3020, uu____3021, commit1) -> begin
commit1
end))


let extract_record : env  ->  scope_mod Prims.list FStar_ST.ref  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun e new_globs se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_bundle (sigs, uu____3061, uu____3062) -> begin
(

let is_rec = (FStar_Util.for_some (fun uu___161_3073 -> (match (uu___161_3073) with
| (FStar_Syntax_Syntax.RecordType (_)) | (FStar_Syntax_Syntax.RecordConstructor (_)) -> begin
true
end
| uu____3076 -> begin
false
end)))
in (

let find_dc = (fun dc -> (FStar_All.pipe_right sigs (FStar_Util.find_opt (fun uu___162_3084 -> (match (uu___162_3084) with
| {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (lid, uu____3086, uu____3087, uu____3088, uu____3089, uu____3090, uu____3091); FStar_Syntax_Syntax.sigrng = uu____3092} -> begin
(FStar_Ident.lid_equals dc lid)
end
| uu____3097 -> begin
false
end)))))
in (FStar_All.pipe_right sigs (FStar_List.iter (fun uu___163_3099 -> (match (uu___163_3099) with
| {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (typename, univs, parms, uu____3103, uu____3104, (dc)::[], tags); FStar_Syntax_Syntax.sigrng = uu____3107} -> begin
(

let uu____3113 = (

let uu____3114 = (find_dc dc)
in (FStar_All.pipe_left FStar_Util.must uu____3114))
in (match (uu____3113) with
| {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (constrname, uu____3118, t, uu____3120, uu____3121, uu____3122, uu____3123); FStar_Syntax_Syntax.sigrng = uu____3124} -> begin
(

let uu____3129 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____3129) with
| (formals, uu____3138) -> begin
(

let is_rec1 = (is_rec tags)
in (

let formals' = (FStar_All.pipe_right formals (FStar_List.collect (fun uu____3164 -> (match (uu____3164) with
| (x, q) -> begin
(

let uu____3172 = ((FStar_Syntax_Syntax.is_null_bv x) || (is_rec1 && (FStar_Syntax_Syntax.is_implicit q)))
in (match (uu____3172) with
| true -> begin
[]
end
| uu____3178 -> begin
(((x), (q)))::[]
end))
end))))
in (

let fields' = (FStar_All.pipe_right formals' (FStar_List.map (fun uu____3203 -> (match (uu____3203) with
| (x, q) -> begin
(

let uu____3212 = (match (is_rec1) with
| true -> begin
(FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname)
end
| uu____3213 -> begin
x.FStar_Syntax_Syntax.ppname
end)
in ((uu____3212), (x.FStar_Syntax_Syntax.sort)))
end))))
in (

let fields = fields'
in (

let record = {typename = typename; constrname = constrname.FStar_Ident.ident; parms = parms; fields = fields; is_private_or_abstract = ((FStar_List.contains FStar_Syntax_Syntax.Private tags) || (FStar_List.contains FStar_Syntax_Syntax.Abstract tags)); is_record = is_rec1}
in ((

let uu____3224 = (

let uu____3226 = (FStar_ST.read new_globs)
in (Record_or_dc (record))::uu____3226)
in (FStar_ST.write new_globs uu____3224));
(match (()) with
| () -> begin
((

let add_field = (fun uu____3242 -> (match (uu____3242) with
| (id, uu____3248) -> begin
(

let modul = (

let uu____3254 = (FStar_Ident.lid_of_ids constrname.FStar_Ident.ns)
in uu____3254.FStar_Ident.str)
in (

let uu____3255 = (get_exported_id_set e modul)
in (match (uu____3255) with
| Some (my_ex) -> begin
(

let my_exported_ids = (my_ex Exported_id_field)
in ((

let uu____3271 = (

let uu____3272 = (FStar_ST.read my_exported_ids)
in (FStar_Util.set_add id.FStar_Ident.idText uu____3272))
in (FStar_ST.write my_exported_ids uu____3271));
(match (()) with
| () -> begin
(

let projname = (

let uu____3279 = (

let uu____3280 = (FStar_Syntax_Util.mk_field_projector_name_from_ident constrname id)
in uu____3280.FStar_Ident.ident)
in uu____3279.FStar_Ident.idText)
in (

let uu____3282 = (

let uu____3283 = (FStar_ST.read my_exported_ids)
in (FStar_Util.set_add projname uu____3283))
in (FStar_ST.write my_exported_ids uu____3282)))
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
| uu____3296 -> begin
()
end))
end
| uu____3297 -> begin
()
end))))))
end
| uu____3298 -> begin
()
end))


let try_lookup_record_or_dc_by_field_name : env  ->  FStar_Ident.lident  ->  record_or_dc Prims.option = (fun env fieldname -> (

let find_in_cache = (fun fieldname1 -> (

let uu____3311 = ((fieldname1.FStar_Ident.ns), (fieldname1.FStar_Ident.ident))
in (match (uu____3311) with
| (ns, id) -> begin
(

let uu____3321 = (peek_record_cache ())
in (FStar_Util.find_map uu____3321 (fun record -> (

let uu____3324 = (find_in_record ns id record (fun r -> Cont_ok (r)))
in (option_of_cont (fun uu____3327 -> None) uu____3324)))))
end)))
in (resolve_in_open_namespaces'' env fieldname Exported_id_field (fun uu____3328 -> Cont_ignore) (fun uu____3329 -> Cont_ignore) (fun r -> Cont_ok (r)) (fun fn -> (

let uu____3332 = (find_in_cache fn)
in (cont_of_option Cont_ignore uu____3332))) (fun k uu____3335 -> k))))


let try_lookup_record_by_field_name : env  ->  FStar_Ident.lident  ->  record_or_dc Prims.option = (fun env fieldname -> (

let uu____3344 = (try_lookup_record_or_dc_by_field_name env fieldname)
in (match (uu____3344) with
| Some (r) when r.is_record -> begin
Some (r)
end
| uu____3348 -> begin
None
end)))


let belongs_to_record : env  ->  FStar_Ident.lident  ->  record_or_dc  ->  Prims.bool = (fun env lid record -> (

let uu____3359 = (try_lookup_record_by_field_name env lid)
in (match (uu____3359) with
| Some (record') when (

let uu____3362 = (

let uu____3363 = (FStar_Ident.path_of_ns record.typename.FStar_Ident.ns)
in (FStar_Ident.text_of_path uu____3363))
in (

let uu____3365 = (

let uu____3366 = (FStar_Ident.path_of_ns record'.typename.FStar_Ident.ns)
in (FStar_Ident.text_of_path uu____3366))
in (uu____3362 = uu____3365))) -> begin
(

let uu____3368 = (find_in_record record.typename.FStar_Ident.ns lid.FStar_Ident.ident record (fun uu____3370 -> Cont_ok (())))
in (match (uu____3368) with
| Cont_ok (uu____3371) -> begin
true
end
| uu____3372 -> begin
false
end))
end
| uu____3374 -> begin
false
end)))


let try_lookup_dc_by_field_name : env  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * Prims.bool) Prims.option = (fun env fieldname -> (

let uu____3385 = (try_lookup_record_or_dc_by_field_name env fieldname)
in (match (uu____3385) with
| Some (r) -> begin
(

let uu____3391 = (

let uu____3394 = (

let uu____3395 = (FStar_Ident.lid_of_ids (FStar_List.append r.typename.FStar_Ident.ns ((r.constrname)::[])))
in (FStar_Ident.set_lid_range uu____3395 (FStar_Ident.range_of_lid fieldname)))
in ((uu____3394), (r.is_record)))
in Some (uu____3391))
end
| uu____3398 -> begin
None
end)))


let string_set_ref_new : Prims.unit  ->  Prims.string FStar_Util.set FStar_ST.ref = (fun uu____3407 -> (

let uu____3408 = (FStar_Util.new_set FStar_Util.compare FStar_Util.hashcode)
in (FStar_Util.mk_ref uu____3408)))


let exported_id_set_new : Prims.unit  ->  exported_id_kind  ->  Prims.string FStar_Util.set FStar_ST.ref = (fun uu____3419 -> (

let term_type_set = (string_set_ref_new ())
in (

let field_set = (string_set_ref_new ())
in (fun uu___164_3428 -> (match (uu___164_3428) with
| Exported_id_term_type -> begin
term_type_set
end
| Exported_id_field -> begin
field_set
end)))))


let unique : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  Prims.bool = (fun any_val exclude_if env lid -> (

let filter_scope_mods = (fun uu___165_3448 -> (match (uu___165_3448) with
| Rec_binding (uu____3449) -> begin
true
end
| uu____3450 -> begin
false
end))
in (

let this_env = (

let uu___169_3452 = env
in (

let uu____3453 = (FStar_List.filter filter_scope_mods env.scope_mods)
in {curmodule = uu___169_3452.curmodule; curmonad = uu___169_3452.curmonad; modules = uu___169_3452.modules; scope_mods = uu____3453; exported_ids = empty_exported_id_smap; trans_exported_ids = uu___169_3452.trans_exported_ids; includes = empty_include_smap; sigaccum = uu___169_3452.sigaccum; sigmap = uu___169_3452.sigmap; iface = uu___169_3452.iface; admitted_iface = uu___169_3452.admitted_iface; expect_typ = uu___169_3452.expect_typ; docs = uu___169_3452.docs}))
in (

let uu____3455 = (try_lookup_lid' any_val exclude_if this_env lid)
in (match (uu____3455) with
| None -> begin
true
end
| Some (uu____3461) -> begin
false
end)))))


let push_scope_mod : env  ->  scope_mod  ->  env = (fun env scope_mod -> (

let uu___170_3472 = env
in {curmodule = uu___170_3472.curmodule; curmonad = uu___170_3472.curmonad; modules = uu___170_3472.modules; scope_mods = (scope_mod)::env.scope_mods; exported_ids = uu___170_3472.exported_ids; trans_exported_ids = uu___170_3472.trans_exported_ids; includes = uu___170_3472.includes; sigaccum = uu___170_3472.sigaccum; sigmap = uu___170_3472.sigmap; iface = uu___170_3472.iface; admitted_iface = uu___170_3472.admitted_iface; expect_typ = uu___170_3472.expect_typ; docs = uu___170_3472.docs}))


let push_bv' : env  ->  FStar_Ident.ident  ->  Prims.bool  ->  (env * FStar_Syntax_Syntax.bv) = (fun env x is_mutable -> (

let bv = (FStar_Syntax_Syntax.gen_bv x.FStar_Ident.idText (Some (x.FStar_Ident.idRange)) FStar_Syntax_Syntax.tun)
in (((push_scope_mod env (Local_binding (((x), (bv), (is_mutable)))))), (bv))))


let push_bv_mutable : env  ->  FStar_Ident.ident  ->  (env * FStar_Syntax_Syntax.bv) = (fun env x -> (push_bv' env x true))


let push_bv : env  ->  FStar_Ident.ident  ->  (env * FStar_Syntax_Syntax.bv) = (fun env x -> (push_bv' env x false))


let push_top_level_rec_binding : env  ->  FStar_Ident.ident  ->  FStar_Syntax_Syntax.delta_depth  ->  env = (fun env x dd -> (

let l = (qualify env x)
in (

let uu____3511 = ((unique false true env l) || (FStar_Options.interactive ()))
in (match (uu____3511) with
| true -> begin
(push_scope_mod env (Rec_binding (((x), (l), (dd)))))
end
| uu____3512 -> begin
(Prims.raise (FStar_Errors.Error ((((Prims.strcat "Duplicate top-level names " l.FStar_Ident.str)), ((FStar_Ident.range_of_lid l))))))
end))))


let push_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env s -> (

let err = (fun l -> (

let sopt = (FStar_Util.smap_try_find (sigmap env) l.FStar_Ident.str)
in (

let r = (match (sopt) with
| Some (se, uu____3531) -> begin
(

let uu____3534 = (FStar_Util.find_opt (FStar_Ident.lid_equals l) (FStar_Syntax_Util.lids_of_sigelt se))
in (match (uu____3534) with
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

let uu____3539 = (

let uu____3540 = (

let uu____3543 = (FStar_Util.format2 "Duplicate top-level names [%s]; previously declared at %s" (FStar_Ident.text_of_lid l) r)
in ((uu____3543), ((FStar_Ident.range_of_lid l))))
in FStar_Errors.Error (uu____3540))
in (Prims.raise uu____3539)))))
in (

let globals = (FStar_Util.mk_ref env.scope_mods)
in (

let env1 = (

let uu____3550 = (match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let (uu____3555) -> begin
((false), (true))
end
| FStar_Syntax_Syntax.Sig_bundle (uu____3563) -> begin
((true), (true))
end
| uu____3570 -> begin
((false), (false))
end)
in (match (uu____3550) with
| (any_val, exclude_if) -> begin
(

let lids = (FStar_Syntax_Util.lids_of_sigelt s)
in (

let uu____3575 = (FStar_Util.find_map lids (fun l -> (

let uu____3578 = (

let uu____3579 = (unique any_val exclude_if env l)
in (not (uu____3579)))
in (match (uu____3578) with
| true -> begin
Some (l)
end
| uu____3581 -> begin
None
end))))
in (match (uu____3575) with
| Some (l) when (

let uu____3583 = (FStar_Options.interactive ())
in (not (uu____3583))) -> begin
(err l)
end
| uu____3584 -> begin
((extract_record env globals s);
(

let uu___171_3589 = env
in {curmodule = uu___171_3589.curmodule; curmonad = uu___171_3589.curmonad; modules = uu___171_3589.modules; scope_mods = uu___171_3589.scope_mods; exported_ids = uu___171_3589.exported_ids; trans_exported_ids = uu___171_3589.trans_exported_ids; includes = uu___171_3589.includes; sigaccum = (s)::env.sigaccum; sigmap = uu___171_3589.sigmap; iface = uu___171_3589.iface; admitted_iface = uu___171_3589.admitted_iface; expect_typ = uu___171_3589.expect_typ; docs = uu___171_3589.docs});
)
end)))
end))
in (

let env2 = (

let uu___172_3591 = env1
in (

let uu____3592 = (FStar_ST.read globals)
in {curmodule = uu___172_3591.curmodule; curmonad = uu___172_3591.curmonad; modules = uu___172_3591.modules; scope_mods = uu____3592; exported_ids = uu___172_3591.exported_ids; trans_exported_ids = uu___172_3591.trans_exported_ids; includes = uu___172_3591.includes; sigaccum = uu___172_3591.sigaccum; sigmap = uu___172_3591.sigmap; iface = uu___172_3591.iface; admitted_iface = uu___172_3591.admitted_iface; expect_typ = uu___172_3591.expect_typ; docs = uu___172_3591.docs}))
in (

let uu____3597 = (match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____3611, uu____3612) -> begin
(

let uu____3619 = (FStar_List.map (fun se -> (((FStar_Syntax_Util.lids_of_sigelt se)), (se))) ses)
in ((env2), (uu____3619)))
end
| uu____3633 -> begin
((env2), (((((FStar_Syntax_Util.lids_of_sigelt s)), (s)))::[]))
end)
in (match (uu____3597) with
| (env3, lss) -> begin
((FStar_All.pipe_right lss (FStar_List.iter (fun uu____3663 -> (match (uu____3663) with
| (lids, se) -> begin
(FStar_All.pipe_right lids (FStar_List.iter (fun lid -> ((

let uu____3674 = (

let uu____3676 = (FStar_ST.read globals)
in (Top_level_def (lid.FStar_Ident.ident))::uu____3676)
in (FStar_ST.write globals uu____3674));
(match (()) with
| () -> begin
(

let modul = (

let uu____3685 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in uu____3685.FStar_Ident.str)
in ((

let uu____3687 = (get_exported_id_set env3 modul)
in (match (uu____3687) with
| Some (f) -> begin
(

let my_exported_ids = (f Exported_id_term_type)
in (

let uu____3702 = (

let uu____3703 = (FStar_ST.read my_exported_ids)
in (FStar_Util.set_add lid.FStar_Ident.ident.FStar_Ident.idText uu____3703))
in (FStar_ST.write my_exported_ids uu____3702)))
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

let uu___173_3715 = env3
in (

let uu____3716 = (FStar_ST.read globals)
in {curmodule = uu___173_3715.curmodule; curmonad = uu___173_3715.curmonad; modules = uu___173_3715.modules; scope_mods = uu____3716; exported_ids = uu___173_3715.exported_ids; trans_exported_ids = uu___173_3715.trans_exported_ids; includes = uu___173_3715.includes; sigaccum = uu___173_3715.sigaccum; sigmap = uu___173_3715.sigmap; iface = uu___173_3715.iface; admitted_iface = uu___173_3715.admitted_iface; expect_typ = uu___173_3715.expect_typ; docs = uu___173_3715.docs}))
in env4);
)
end)))))))


let push_namespace : env  ->  FStar_Ident.lident  ->  env = (fun env ns -> (

let uu____3727 = (

let uu____3730 = (resolve_module_name env ns false)
in (match (uu____3730) with
| None -> begin
(

let modules = env.modules
in (

let uu____3738 = (FStar_All.pipe_right modules (FStar_Util.for_some (fun uu____3744 -> (match (uu____3744) with
| (m, uu____3748) -> begin
(FStar_Util.starts_with (Prims.strcat (FStar_Ident.text_of_lid m) ".") (Prims.strcat (FStar_Ident.text_of_lid ns) "."))
end))))
in (match (uu____3738) with
| true -> begin
((ns), (Open_namespace))
end
| uu____3751 -> begin
(

let uu____3752 = (

let uu____3753 = (

let uu____3756 = (FStar_Util.format1 "Namespace %s cannot be found" (FStar_Ident.text_of_lid ns))
in ((uu____3756), ((FStar_Ident.range_of_lid ns))))
in FStar_Errors.Error (uu____3753))
in (Prims.raise uu____3752))
end)))
end
| Some (ns') -> begin
((ns'), (Open_module))
end))
in (match (uu____3727) with
| (ns', kd) -> begin
(push_scope_mod env (Open_module_or_namespace (((ns'), (kd)))))
end)))


let push_include : env  ->  FStar_Ident.lident  ->  env = (fun env ns -> (

let uu____3768 = (resolve_module_name env ns false)
in (match (uu____3768) with
| Some (ns1) -> begin
(

let env1 = (push_scope_mod env (Open_module_or_namespace (((ns1), (Open_module)))))
in (

let curmod = (

let uu____3773 = (current_module env1)
in uu____3773.FStar_Ident.str)
in ((

let uu____3775 = (FStar_Util.smap_try_find env1.includes curmod)
in (match (uu____3775) with
| None -> begin
()
end
| Some (incl) -> begin
(

let uu____3788 = (

let uu____3790 = (FStar_ST.read incl)
in (ns1)::uu____3790)
in (FStar_ST.write incl uu____3788))
end));
(match (()) with
| () -> begin
(

let uu____3798 = (get_trans_exported_id_set env1 ns1.FStar_Ident.str)
in (match (uu____3798) with
| Some (ns_trans_exports) -> begin
((

let uu____3811 = (

let uu____3822 = (get_exported_id_set env1 curmod)
in (

let uu____3827 = (get_trans_exported_id_set env1 curmod)
in ((uu____3822), (uu____3827))))
in (match (uu____3811) with
| (Some (cur_exports), Some (cur_trans_exports)) -> begin
(

let update_exports = (fun k -> (

let ns_ex = (

let uu____3867 = (ns_trans_exports k)
in (FStar_ST.read uu____3867))
in (

let ex = (cur_exports k)
in ((

let uu____3876 = (

let uu____3877 = (FStar_ST.read ex)
in (FStar_Util.set_difference uu____3877 ns_ex))
in (FStar_ST.write ex uu____3876));
(match (()) with
| () -> begin
(

let trans_ex = (cur_trans_exports k)
in (

let uu____3887 = (

let uu____3888 = (FStar_ST.read trans_ex)
in (FStar_Util.set_union uu____3888 ns_ex))
in (FStar_ST.write trans_ex uu____3887)))
end);
))))
in (FStar_List.iter update_exports all_exported_id_kinds))
end
| uu____3894 -> begin
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

let uu____3908 = (

let uu____3909 = (

let uu____3912 = (FStar_Util.format1 "include: Module %s was not prepared" ns1.FStar_Ident.str)
in ((uu____3912), ((FStar_Ident.range_of_lid ns1))))
in FStar_Errors.Error (uu____3909))
in (Prims.raise uu____3908))
end))
end);
)))
end
| uu____3913 -> begin
(

let uu____3915 = (

let uu____3916 = (

let uu____3919 = (FStar_Util.format1 "include: Module %s cannot be found" ns.FStar_Ident.str)
in ((uu____3919), ((FStar_Ident.range_of_lid ns))))
in FStar_Errors.Error (uu____3916))
in (Prims.raise uu____3915))
end)))


let push_module_abbrev : env  ->  FStar_Ident.ident  ->  FStar_Ident.lident  ->  env = (fun env x l -> (

let uu____3929 = (module_is_defined env l)
in (match (uu____3929) with
| true -> begin
(push_scope_mod env (Module_abbrev (((x), (l)))))
end
| uu____3930 -> begin
(

let uu____3931 = (

let uu____3932 = (

let uu____3935 = (FStar_Util.format1 "Module %s cannot be found" (FStar_Ident.text_of_lid l))
in ((uu____3935), ((FStar_Ident.range_of_lid l))))
in FStar_Errors.Error (uu____3932))
in (Prims.raise uu____3931))
end)))


let push_doc : env  ->  FStar_Ident.lident  ->  FStar_Parser_AST.fsdoc Prims.option  ->  env = (fun env l doc_opt -> (match (doc_opt) with
| None -> begin
env
end
| Some (doc1) -> begin
((

let uu____3949 = (FStar_Util.smap_try_find env.docs l.FStar_Ident.str)
in (match (uu____3949) with
| None -> begin
()
end
| Some (old_doc) -> begin
(

let uu____3952 = (

let uu____3953 = (FStar_Ident.string_of_lid l)
in (

let uu____3954 = (FStar_Parser_AST.string_of_fsdoc old_doc)
in (

let uu____3955 = (FStar_Parser_AST.string_of_fsdoc doc1)
in (FStar_Util.format3 "Overwriting doc of %s; old doc was [%s]; new doc are [%s]" uu____3953 uu____3954 uu____3955))))
in (FStar_Errors.warn (FStar_Ident.range_of_lid l) uu____3952))
end));
(FStar_Util.smap_add env.docs l.FStar_Ident.str doc1);
env;
)
end))


let check_admits : env  ->  Prims.unit = (fun env -> (FStar_All.pipe_right env.sigaccum (FStar_List.iter (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_declare_typ (l, u, t, quals) -> begin
(

let uu____3967 = (try_lookup_lid env l)
in (match (uu____3967) with
| None -> begin
((

let uu____3974 = (

let uu____3975 = (FStar_Options.interactive ())
in (not (uu____3975)))
in (match (uu____3974) with
| true -> begin
(

let uu____3976 = (

let uu____3977 = (FStar_Range.string_of_range (FStar_Ident.range_of_lid l))
in (

let uu____3978 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format2 "%s: Warning: Admitting %s without a definition\n" uu____3977 uu____3978)))
in (FStar_Util.print_string uu____3976))
end
| uu____3979 -> begin
()
end));
(FStar_Util.smap_add (sigmap env) l.FStar_Ident.str (((

let uu___174_3982 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((l), (u), (t), ((FStar_Syntax_Syntax.Assumption)::quals))); FStar_Syntax_Syntax.sigrng = uu___174_3982.FStar_Syntax_Syntax.sigrng})), (false)));
)
end
| Some (uu____3984) -> begin
()
end))
end
| uu____3989 -> begin
()
end)))))


let finish : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env modul -> ((FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations (FStar_List.iter (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, uu____4000) -> begin
(match (((FStar_List.contains FStar_Syntax_Syntax.Private quals) || (FStar_List.contains FStar_Syntax_Syntax.Abstract quals))) with
| true -> begin
(FStar_All.pipe_right ses (FStar_List.iter (fun se1 -> (match (se1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (lid, uu____4010, uu____4011, uu____4012, uu____4013, uu____4014, uu____4015) -> begin
(FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str)
end
| uu____4022 -> begin
()
end))))
end
| uu____4023 -> begin
()
end)
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____4025, uu____4026, quals) -> begin
(match ((FStar_List.contains FStar_Syntax_Syntax.Private quals)) with
| true -> begin
(FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str)
end
| uu____4032 -> begin
()
end)
end
| FStar_Syntax_Syntax.Sig_let ((uu____4033, lbs), uu____4035, quals, uu____4037) -> begin
((match (((FStar_List.contains FStar_Syntax_Syntax.Private quals) || (FStar_List.contains FStar_Syntax_Syntax.Abstract quals))) with
| true -> begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (

let uu____4052 = (

let uu____4053 = (

let uu____4054 = (

let uu____4059 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in uu____4059.FStar_Syntax_Syntax.fv_name)
in uu____4054.FStar_Syntax_Syntax.v)
in uu____4053.FStar_Ident.str)
in (FStar_Util.smap_remove (sigmap env) uu____4052)))))
end
| uu____4065 -> begin
()
end);
(match (((FStar_List.contains FStar_Syntax_Syntax.Abstract quals) && (not ((FStar_List.contains FStar_Syntax_Syntax.Private quals))))) with
| true -> begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (

let lid = (

let uu____4069 = (

let uu____4074 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in uu____4074.FStar_Syntax_Syntax.fv_name)
in uu____4069.FStar_Syntax_Syntax.v)
in (

let decl = (

let uu___175_4079 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), ((FStar_Syntax_Syntax.Assumption)::quals))); FStar_Syntax_Syntax.sigrng = uu___175_4079.FStar_Syntax_Syntax.sigrng})
in (FStar_Util.smap_add (sigmap env) lid.FStar_Ident.str ((decl), (false))))))))
end
| uu____4086 -> begin
()
end);
)
end
| uu____4087 -> begin
()
end))));
(

let curmod = (

let uu____4089 = (current_module env)
in uu____4089.FStar_Ident.str)
in ((

let uu____4091 = (

let uu____4102 = (get_exported_id_set env curmod)
in (

let uu____4107 = (get_trans_exported_id_set env curmod)
in ((uu____4102), (uu____4107))))
in (match (uu____4091) with
| (Some (cur_ex), Some (cur_trans_ex)) -> begin
(

let update_exports = (fun eikind -> (

let cur_ex_set = (

let uu____4147 = (cur_ex eikind)
in (FStar_ST.read uu____4147))
in (

let cur_trans_ex_set_ref = (cur_trans_ex eikind)
in (

let uu____4155 = (

let uu____4156 = (FStar_ST.read cur_trans_ex_set_ref)
in (FStar_Util.set_union cur_ex_set uu____4156))
in (FStar_ST.write cur_trans_ex_set_ref uu____4155)))))
in (FStar_List.iter update_exports all_exported_id_kinds))
end
| uu____4162 -> begin
()
end));
(match (()) with
| () -> begin
((filter_record_cache ());
(match (()) with
| () -> begin
(

let uu___176_4174 = env
in {curmodule = None; curmonad = uu___176_4174.curmonad; modules = (((modul.FStar_Syntax_Syntax.name), (modul)))::env.modules; scope_mods = []; exported_ids = uu___176_4174.exported_ids; trans_exported_ids = uu___176_4174.trans_exported_ids; includes = uu___176_4174.includes; sigaccum = []; sigmap = uu___176_4174.sigmap; iface = uu___176_4174.iface; admitted_iface = uu___176_4174.admitted_iface; expect_typ = uu___176_4174.expect_typ; docs = uu___176_4174.docs})
end);
)
end);
));
))


let stack : env Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let push : env  ->  env = (fun env -> ((push_record_cache ());
(

let uu____4187 = (

let uu____4189 = (FStar_ST.read stack)
in (env)::uu____4189)
in (FStar_ST.write stack uu____4187));
(

let uu___177_4197 = env
in (

let uu____4198 = (FStar_Util.smap_copy (sigmap env))
in (

let uu____4204 = (FStar_Util.smap_copy env.docs)
in {curmodule = uu___177_4197.curmodule; curmonad = uu___177_4197.curmonad; modules = uu___177_4197.modules; scope_mods = uu___177_4197.scope_mods; exported_ids = uu___177_4197.exported_ids; trans_exported_ids = uu___177_4197.trans_exported_ids; includes = uu___177_4197.includes; sigaccum = uu___177_4197.sigaccum; sigmap = uu____4198; iface = uu___177_4197.iface; admitted_iface = uu___177_4197.admitted_iface; expect_typ = uu___177_4197.expect_typ; docs = uu____4204})));
))


let pop : Prims.unit  ->  env = (fun uu____4208 -> (

let uu____4209 = (FStar_ST.read stack)
in (match (uu____4209) with
| (env)::tl1 -> begin
((pop_record_cache ());
(FStar_ST.write stack tl1);
env;
)
end
| uu____4222 -> begin
(failwith "Impossible: Too many pops")
end)))


let commit_mark : env  ->  env = (fun env -> ((commit_record_cache ());
(

let uu____4228 = (FStar_ST.read stack)
in (match (uu____4228) with
| (uu____4233)::tl1 -> begin
((FStar_ST.write stack tl1);
env;
)
end
| uu____4240 -> begin
(failwith "Impossible: Too many pops")
end));
))


let mark : env  ->  env = (fun x -> (push x))


let reset_mark : Prims.unit  ->  env = (fun uu____4247 -> (pop ()))


let export_interface : FStar_Ident.lident  ->  env  ->  env = (fun m env -> (

let sigelt_in_m = (fun se -> (match ((FStar_Syntax_Util.lids_of_sigelt se)) with
| (l)::uu____4259 -> begin
(l.FStar_Ident.nsstr = m.FStar_Ident.str)
end
| uu____4261 -> begin
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

let uu____4279 = (FStar_Util.smap_try_find sm' k)
in (match (uu____4279) with
| Some (se, true) when (sigelt_in_m se) -> begin
((FStar_Util.smap_remove sm' k);
(

let se1 = (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_declare_typ (l, u, t, q) -> begin
(

let uu___178_4298 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((l), (u), (t), ((FStar_Syntax_Syntax.Assumption)::q))); FStar_Syntax_Syntax.sigrng = uu___178_4298.FStar_Syntax_Syntax.sigrng})
end
| uu____4300 -> begin
se
end)
in (FStar_Util.smap_add sm' k ((se1), (false))));
)
end
| uu____4303 -> begin
()
end)))));
env1;
)))))))


let finish_module_or_interface : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env modul -> ((match ((not (modul.FStar_Syntax_Syntax.is_interface))) with
| true -> begin
(check_admits env)
end
| uu____4314 -> begin
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
| uu____4336 -> begin
(match ((FStar_Util.starts_with "FStar." (FStar_Ident.text_of_lid mname))) with
| true -> begin
(FStar_Syntax_Const.prims_lid)::(FStar_Syntax_Const.fstar_ns_lid)::[]
end
| uu____4338 -> begin
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
| uu____4345 -> begin
open_ns
end)
in ((

let uu____4347 = (exported_id_set_new ())
in (FStar_Util.smap_add env1.exported_ids mname.FStar_Ident.str uu____4347));
(match (()) with
| () -> begin
((

let uu____4352 = (exported_id_set_new ())
in (FStar_Util.smap_add env1.trans_exported_ids mname.FStar_Ident.str uu____4352));
(match (()) with
| () -> begin
((

let uu____4357 = (FStar_Util.mk_ref [])
in (FStar_Util.smap_add env1.includes mname.FStar_Ident.str uu____4357));
(match (()) with
| () -> begin
(

let uu___179_4366 = env1
in (

let uu____4367 = (FStar_List.map (fun lid -> Open_module_or_namespace (((lid), (Open_namespace)))) open_ns1)
in {curmodule = Some (mname); curmonad = uu___179_4366.curmonad; modules = uu___179_4366.modules; scope_mods = uu____4367; exported_ids = uu___179_4366.exported_ids; trans_exported_ids = uu___179_4366.trans_exported_ids; includes = uu___179_4366.includes; sigaccum = uu___179_4366.sigaccum; sigmap = env1.sigmap; iface = intf; admitted_iface = admitted; expect_typ = uu___179_4366.expect_typ; docs = uu___179_4366.docs}))
end);
)
end);
)
end);
))))
in (

let uu____4370 = (FStar_All.pipe_right env.modules (FStar_Util.find_opt (fun uu____4382 -> (match (uu____4382) with
| (l, uu____4386) -> begin
(FStar_Ident.lid_equals l mname)
end))))
in (match (uu____4370) with
| None -> begin
(

let uu____4391 = (prep env)
in ((uu____4391), (false)))
end
| Some (uu____4392, m) -> begin
((

let uu____4397 = ((

let uu____4398 = (FStar_Options.interactive ())
in (not (uu____4398))) && ((not (m.FStar_Syntax_Syntax.is_interface)) || intf))
in (match (uu____4397) with
| true -> begin
(

let uu____4399 = (

let uu____4400 = (

let uu____4403 = (FStar_Util.format1 "Duplicate module or interface name: %s" mname.FStar_Ident.str)
in ((uu____4403), ((FStar_Ident.range_of_lid mname))))
in FStar_Errors.Error (uu____4400))
in (Prims.raise uu____4399))
end
| uu____4404 -> begin
()
end));
(

let uu____4405 = (

let uu____4406 = (push env)
in (prep uu____4406))
in ((uu____4405), (true)));
)
end))))


let enter_monad_scope : env  ->  FStar_Ident.ident  ->  env = (fun env mname -> (match (env.curmonad) with
| Some (mname') -> begin
(Prims.raise (FStar_Errors.Error ((((Prims.strcat "Trying to define monad " (Prims.strcat mname.FStar_Ident.idText (Prims.strcat ", but already in monad scope " mname'.FStar_Ident.idText)))), (mname.FStar_Ident.idRange)))))
end
| None -> begin
(

let uu___180_4414 = env
in {curmodule = uu___180_4414.curmodule; curmonad = Some (mname); modules = uu___180_4414.modules; scope_mods = uu___180_4414.scope_mods; exported_ids = uu___180_4414.exported_ids; trans_exported_ids = uu___180_4414.trans_exported_ids; includes = uu___180_4414.includes; sigaccum = uu___180_4414.sigaccum; sigmap = uu___180_4414.sigmap; iface = uu___180_4414.iface; admitted_iface = uu___180_4414.admitted_iface; expect_typ = uu___180_4414.expect_typ; docs = uu___180_4414.docs})
end))


let fail_or = (fun env lookup lid -> (

let uu____4439 = (lookup lid)
in (match (uu____4439) with
| None -> begin
(

let opened_modules = (FStar_List.map (fun uu____4445 -> (match (uu____4445) with
| (lid1, uu____4449) -> begin
(FStar_Ident.text_of_lid lid1)
end)) env.modules)
in (

let msg = (FStar_Util.format1 "Identifier not found: [%s]" (FStar_Ident.text_of_lid lid))
in (

let msg1 = (match (((FStar_List.length lid.FStar_Ident.ns) = (Prims.parse_int "0"))) with
| true -> begin
msg
end
| uu____4454 -> begin
(

let modul = (

let uu____4456 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in (FStar_Ident.set_lid_range uu____4456 (FStar_Ident.range_of_lid lid)))
in (

let uu____4457 = (resolve_module_name env modul true)
in (match (uu____4457) with
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

let uu____4484 = (lookup id)
in (match (uu____4484) with
| None -> begin
(Prims.raise (FStar_Errors.Error ((((Prims.strcat "Identifier not found [" (Prims.strcat id.FStar_Ident.idText "]"))), (id.FStar_Ident.idRange)))))
end
| Some (r) -> begin
r
end)))




