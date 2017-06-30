
open Prims
open FStar_Pervasives

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
| uu____104 -> begin
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
| uu____116 -> begin
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
| uu____128 -> begin
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
| uu____140 -> begin
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
| uu____152 -> begin
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
| uu____164 -> begin
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
| uu____176 -> begin
false
end))


let uu___is_Exported_id_field : exported_id_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Exported_id_field -> begin
true
end
| uu____180 -> begin
false
end))


type exported_id_set =
exported_id_kind  ->  string_set FStar_ST.ref

type env =
{curmodule : FStar_Ident.lident FStar_Pervasives_Native.option; curmonad : FStar_Ident.ident FStar_Pervasives_Native.option; modules : (FStar_Ident.lident * FStar_Syntax_Syntax.modul) Prims.list; scope_mods : scope_mod Prims.list; exported_ids : exported_id_set FStar_Util.smap; trans_exported_ids : exported_id_set FStar_Util.smap; includes : FStar_Ident.lident Prims.list FStar_ST.ref FStar_Util.smap; sigaccum : FStar_Syntax_Syntax.sigelts; sigmap : (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap; iface : Prims.bool; admitted_iface : Prims.bool; expect_typ : Prims.bool; docs : FStar_Parser_AST.fsdoc FStar_Util.smap; remaining_iface_decls : (FStar_Ident.lident * FStar_Parser_AST.decl Prims.list) Prims.list; syntax_only : Prims.bool}

type foundname =
| Term_name of (FStar_Syntax_Syntax.typ * Prims.bool)
| Eff_name of (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident)


let uu___is_Term_name : foundname  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Term_name (_0) -> begin
true
end
| uu____381 -> begin
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
| uu____401 -> begin
false
end))


let __proj__Eff_name__item___0 : foundname  ->  (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident) = (fun projectee -> (match (projectee) with
| Eff_name (_0) -> begin
_0
end))


let set_iface : env  ->  Prims.bool  ->  env = (fun env b -> (

let uu___174_421 = env
in {curmodule = uu___174_421.curmodule; curmonad = uu___174_421.curmonad; modules = uu___174_421.modules; scope_mods = uu___174_421.scope_mods; exported_ids = uu___174_421.exported_ids; trans_exported_ids = uu___174_421.trans_exported_ids; includes = uu___174_421.includes; sigaccum = uu___174_421.sigaccum; sigmap = uu___174_421.sigmap; iface = b; admitted_iface = uu___174_421.admitted_iface; expect_typ = uu___174_421.expect_typ; docs = uu___174_421.docs; remaining_iface_decls = uu___174_421.remaining_iface_decls; syntax_only = uu___174_421.syntax_only}))


let iface : env  ->  Prims.bool = (fun e -> e.iface)


let set_admitted_iface : env  ->  Prims.bool  ->  env = (fun e b -> (

let uu___175_431 = e
in {curmodule = uu___175_431.curmodule; curmonad = uu___175_431.curmonad; modules = uu___175_431.modules; scope_mods = uu___175_431.scope_mods; exported_ids = uu___175_431.exported_ids; trans_exported_ids = uu___175_431.trans_exported_ids; includes = uu___175_431.includes; sigaccum = uu___175_431.sigaccum; sigmap = uu___175_431.sigmap; iface = uu___175_431.iface; admitted_iface = b; expect_typ = uu___175_431.expect_typ; docs = uu___175_431.docs; remaining_iface_decls = uu___175_431.remaining_iface_decls; syntax_only = uu___175_431.syntax_only}))


let admitted_iface : env  ->  Prims.bool = (fun e -> e.admitted_iface)


let set_expect_typ : env  ->  Prims.bool  ->  env = (fun e b -> (

let uu___176_441 = e
in {curmodule = uu___176_441.curmodule; curmonad = uu___176_441.curmonad; modules = uu___176_441.modules; scope_mods = uu___176_441.scope_mods; exported_ids = uu___176_441.exported_ids; trans_exported_ids = uu___176_441.trans_exported_ids; includes = uu___176_441.includes; sigaccum = uu___176_441.sigaccum; sigmap = uu___176_441.sigmap; iface = uu___176_441.iface; admitted_iface = uu___176_441.admitted_iface; expect_typ = b; docs = uu___176_441.docs; remaining_iface_decls = uu___176_441.remaining_iface_decls; syntax_only = uu___176_441.syntax_only}))


let expect_typ : env  ->  Prims.bool = (fun e -> e.expect_typ)


let all_exported_id_kinds : exported_id_kind Prims.list = (Exported_id_field)::(Exported_id_term_type)::[]


let transitive_exported_ids : env  ->  FStar_Ident.lident  ->  Prims.string Prims.list = (fun env lid -> (

let module_name = (FStar_Ident.string_of_lid lid)
in (

let uu____454 = (FStar_Util.smap_try_find env.trans_exported_ids module_name)
in (match (uu____454) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (exported_id_set) -> begin
(

let uu____458 = (

let uu____459 = (exported_id_set Exported_id_term_type)
in (FStar_ST.read uu____459))
in (FStar_All.pipe_right uu____458 FStar_Util.set_elements))
end))))


let open_modules : env  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.modul) Prims.list = (fun e -> e.modules)


let set_current_module : env  ->  FStar_Ident.lident  ->  env = (fun e l -> (

let uu___177_477 = e
in {curmodule = FStar_Pervasives_Native.Some (l); curmonad = uu___177_477.curmonad; modules = uu___177_477.modules; scope_mods = uu___177_477.scope_mods; exported_ids = uu___177_477.exported_ids; trans_exported_ids = uu___177_477.trans_exported_ids; includes = uu___177_477.includes; sigaccum = uu___177_477.sigaccum; sigmap = uu___177_477.sigmap; iface = uu___177_477.iface; admitted_iface = uu___177_477.admitted_iface; expect_typ = uu___177_477.expect_typ; docs = uu___177_477.docs; remaining_iface_decls = uu___177_477.remaining_iface_decls; syntax_only = uu___177_477.syntax_only}))


let current_module : env  ->  FStar_Ident.lident = (fun env -> (match (env.curmodule) with
| FStar_Pervasives_Native.None -> begin
(failwith "Unset current module")
end
| FStar_Pervasives_Native.Some (m) -> begin
m
end))


let iface_decls : env  ->  FStar_Ident.lident  ->  FStar_Parser_AST.decl Prims.list FStar_Pervasives_Native.option = (fun env l -> (

let uu____490 = (FStar_All.pipe_right env.remaining_iface_decls (FStar_List.tryFind (fun uu____506 -> (match (uu____506) with
| (m, uu____511) -> begin
(FStar_Ident.lid_equals l m)
end))))
in (match (uu____490) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (uu____520, decls) -> begin
FStar_Pervasives_Native.Some (decls)
end)))


let set_iface_decls : env  ->  FStar_Ident.lident  ->  FStar_Parser_AST.decl Prims.list  ->  env = (fun env l ds -> (

let uu____539 = (FStar_List.partition (fun uu____553 -> (match (uu____553) with
| (m, uu____558) -> begin
(FStar_Ident.lid_equals l m)
end)) env.remaining_iface_decls)
in (match (uu____539) with
| (uu____561, rest) -> begin
(

let uu___178_579 = env
in {curmodule = uu___178_579.curmodule; curmonad = uu___178_579.curmonad; modules = uu___178_579.modules; scope_mods = uu___178_579.scope_mods; exported_ids = uu___178_579.exported_ids; trans_exported_ids = uu___178_579.trans_exported_ids; includes = uu___178_579.includes; sigaccum = uu___178_579.sigaccum; sigmap = uu___178_579.sigmap; iface = uu___178_579.iface; admitted_iface = uu___178_579.admitted_iface; expect_typ = uu___178_579.expect_typ; docs = uu___178_579.docs; remaining_iface_decls = (((l), (ds)))::rest; syntax_only = uu___178_579.syntax_only})
end)))


let qual : FStar_Ident.lident  ->  FStar_Ident.ident  ->  FStar_Ident.lident = FStar_Syntax_Util.qual_id


let qualify : env  ->  FStar_Ident.ident  ->  FStar_Ident.lident = (fun env id -> (match (env.curmonad) with
| FStar_Pervasives_Native.None -> begin
(

let uu____594 = (current_module env)
in (qual uu____594 id))
end
| FStar_Pervasives_Native.Some (monad) -> begin
(

let uu____596 = (

let uu____597 = (current_module env)
in (qual uu____597 monad))
in (FStar_Syntax_Util.mk_field_projector_name_from_ident uu____596 id))
end))


let syntax_only : env  ->  Prims.bool = (fun env -> env.syntax_only)


let set_syntax_only : env  ->  Prims.bool  ->  env = (fun env b -> (

let uu___179_607 = env
in {curmodule = uu___179_607.curmodule; curmonad = uu___179_607.curmonad; modules = uu___179_607.modules; scope_mods = uu___179_607.scope_mods; exported_ids = uu___179_607.exported_ids; trans_exported_ids = uu___179_607.trans_exported_ids; includes = uu___179_607.includes; sigaccum = uu___179_607.sigaccum; sigmap = uu___179_607.sigmap; iface = uu___179_607.iface; admitted_iface = uu___179_607.admitted_iface; expect_typ = uu___179_607.expect_typ; docs = uu___179_607.docs; remaining_iface_decls = uu___179_607.remaining_iface_decls; syntax_only = b}))


let new_sigmap = (fun uu____615 -> (FStar_Util.smap_create (Prims.parse_int "100")))


let empty_env : Prims.unit  ->  env = (fun uu____618 -> (

let uu____619 = (new_sigmap ())
in (

let uu____621 = (new_sigmap ())
in (

let uu____623 = (new_sigmap ())
in (

let uu____629 = (new_sigmap ())
in (

let uu____635 = (new_sigmap ())
in {curmodule = FStar_Pervasives_Native.None; curmonad = FStar_Pervasives_Native.None; modules = []; scope_mods = []; exported_ids = uu____619; trans_exported_ids = uu____621; includes = uu____623; sigaccum = []; sigmap = uu____629; iface = false; admitted_iface = false; expect_typ = false; docs = uu____635; remaining_iface_decls = []; syntax_only = false}))))))


let sigmap : env  ->  (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap = (fun env -> env.sigmap)


let has_all_in_scope : env  ->  Prims.bool = (fun env -> (FStar_List.existsb (fun uu____653 -> (match (uu____653) with
| (m, uu____657) -> begin
(FStar_Ident.lid_equals m FStar_Parser_Const.all_lid)
end)) env.modules))


let set_bv_range : FStar_Syntax_Syntax.bv  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.bv = (fun bv r -> (

let id = (

let uu___180_665 = bv.FStar_Syntax_Syntax.ppname
in {FStar_Ident.idText = uu___180_665.FStar_Ident.idText; FStar_Ident.idRange = r})
in (

let uu___181_666 = bv
in {FStar_Syntax_Syntax.ppname = id; FStar_Syntax_Syntax.index = uu___181_666.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu___181_666.FStar_Syntax_Syntax.sort})))


let bv_to_name : FStar_Syntax_Syntax.bv  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.term = (fun bv r -> (FStar_Syntax_Syntax.bv_to_name (set_bv_range bv r)))


let unmangleMap : (Prims.string * Prims.string * FStar_Syntax_Syntax.delta_depth * FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option) Prims.list = ((("op_ColonColon"), ("Cons"), (FStar_Syntax_Syntax.Delta_constant), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor))))::((("not"), ("op_Negation"), (FStar_Syntax_Syntax.Delta_equational), (FStar_Pervasives_Native.None)))::[]


let unmangleOpName : FStar_Ident.ident  ->  (FStar_Syntax_Syntax.term * Prims.bool) FStar_Pervasives_Native.option = (fun id -> (

let t = (FStar_Util.find_map unmangleMap (fun uu____712 -> (match (uu____712) with
| (x, y, dd, dq) -> begin
(match ((id.FStar_Ident.idText = x)) with
| true -> begin
(

let uu____726 = (

let uu____727 = (FStar_Ident.lid_of_path (("Prims")::(y)::[]) id.FStar_Ident.idRange)
in (FStar_Syntax_Syntax.fvar uu____727 dd dq))
in FStar_Pervasives_Native.Some (uu____726))
end
| uu____728 -> begin
FStar_Pervasives_Native.None
end)
end)))
in (match (t) with
| FStar_Pervasives_Native.Some (v1) -> begin
FStar_Pervasives_Native.Some (((v1), (false)))
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end)))

type 'a cont_t =
| Cont_ok of 'a
| Cont_fail
| Cont_ignore


let uu___is_Cont_ok = (fun projectee -> (match (projectee) with
| Cont_ok (_0) -> begin
true
end
| uu____758 -> begin
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
| uu____782 -> begin
false
end))


let uu___is_Cont_ignore = (fun projectee -> (match (projectee) with
| Cont_ignore -> begin
true
end
| uu____793 -> begin
false
end))


let option_of_cont = (fun k_ignore uu___146_812 -> (match (uu___146_812) with
| Cont_ok (a) -> begin
FStar_Pervasives_Native.Some (a)
end
| Cont_fail -> begin
FStar_Pervasives_Native.None
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

let find1 = (FStar_Util.find_map record.fields (fun uu____857 -> (match (uu____857) with
| (f, uu____862) -> begin
(match ((id.FStar_Ident.idText = f.FStar_Ident.idText)) with
| true -> begin
FStar_Pervasives_Native.Some (record)
end
| uu____864 -> begin
FStar_Pervasives_Native.None
end)
end)))
in (match (find1) with
| FStar_Pervasives_Native.Some (r) -> begin
(cont r)
end
| FStar_Pervasives_Native.None -> begin
Cont_ignore
end)))
end
| uu____867 -> begin
Cont_ignore
end)))


let get_exported_id_set : env  ->  Prims.string  ->  (exported_id_kind  ->  string_set FStar_ST.ref) FStar_Pervasives_Native.option = (fun e mname -> (FStar_Util.smap_try_find e.exported_ids mname))


let get_trans_exported_id_set : env  ->  Prims.string  ->  (exported_id_kind  ->  string_set FStar_ST.ref) FStar_Pervasives_Native.option = (fun e mname -> (FStar_Util.smap_try_find e.trans_exported_ids mname))


let string_of_exported_id_kind : exported_id_kind  ->  Prims.string = (fun uu___147_898 -> (match (uu___147_898) with
| Exported_id_field -> begin
"field"
end
| Exported_id_term_type -> begin
"term/type"
end))


let find_in_module_with_includes = (fun eikind find_in_module find_in_module_default env ns id -> (

let idstr = id.FStar_Ident.idText
in (

let rec aux = (fun uu___148_947 -> (match (uu___148_947) with
| [] -> begin
find_in_module_default
end
| (modul)::q -> begin
(

let mname = modul.FStar_Ident.str
in (

let not_shadowed = (

let uu____955 = (get_exported_id_set env mname)
in (match (uu____955) with
| FStar_Pervasives_Native.None -> begin
true
end
| FStar_Pervasives_Native.Some (mex) -> begin
(

let mexports = (

let uu____971 = (mex eikind)
in (FStar_ST.read uu____971))
in (FStar_Util.set_mem idstr mexports))
end))
in (

let mincludes = (

let uu____978 = (FStar_Util.smap_try_find env.includes mname)
in (match (uu____978) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (minc) -> begin
(FStar_ST.read minc)
end))
in (

let look_into = (match (not_shadowed) with
| true -> begin
(

let uu____998 = (qual modul id)
in (find_in_module uu____998))
end
| uu____999 -> begin
Cont_ignore
end)
in (match (look_into) with
| Cont_ignore -> begin
(aux (FStar_List.append mincludes q))
end
| uu____1001 -> begin
look_into
end)))))
end))
in (aux ((ns)::[])))))


let is_exported_id_field : exported_id_kind  ->  Prims.bool = (fun uu___149_1005 -> (match (uu___149_1005) with
| Exported_id_field -> begin
true
end
| uu____1006 -> begin
false
end))


let try_lookup_id'' = (fun env id eikind k_local_binding k_rec_binding k_record find_in_module lookup_default_id -> (

let check_local_binding_id = (fun uu___150_1095 -> (match (uu___150_1095) with
| (id', uu____1097, uu____1098) -> begin
(id'.FStar_Ident.idText = id.FStar_Ident.idText)
end))
in (

let check_rec_binding_id = (fun uu___151_1102 -> (match (uu___151_1102) with
| (id', uu____1104, uu____1105) -> begin
(id'.FStar_Ident.idText = id.FStar_Ident.idText)
end))
in (

let curmod_ns = (

let uu____1108 = (current_module env)
in (FStar_Ident.ids_of_lid uu____1108))
in (

let proc = (fun uu___152_1113 -> (match (uu___152_1113) with
| Local_binding (l) when (check_local_binding_id l) -> begin
(k_local_binding l)
end
| Rec_binding (r) when (check_rec_binding_id r) -> begin
(k_rec_binding r)
end
| Open_module_or_namespace (ns, Open_module) -> begin
(find_in_module_with_includes eikind find_in_module Cont_ignore env ns id)
end
| Top_level_def (id') when (id'.FStar_Ident.idText = id.FStar_Ident.idText) -> begin
(lookup_default_id Cont_ignore id)
end
| Record_or_dc (r) when (is_exported_id_field eikind) -> begin
(

let uu____1120 = (FStar_Ident.lid_of_ids curmod_ns)
in (find_in_module_with_includes Exported_id_field (fun lid -> (

let id1 = lid.FStar_Ident.ident
in (find_in_record lid.FStar_Ident.ns id1 r k_record))) Cont_ignore env uu____1120 id))
end
| uu____1123 -> begin
Cont_ignore
end))
in (

let rec aux = (fun uu___153_1129 -> (match (uu___153_1129) with
| (a)::q -> begin
(

let uu____1135 = (proc a)
in (option_of_cont (fun uu____1137 -> (aux q)) uu____1135))
end
| [] -> begin
(

let uu____1138 = (lookup_default_id Cont_fail id)
in (option_of_cont (fun uu____1140 -> FStar_Pervasives_Native.None) uu____1138))
end))
in (aux env.scope_mods)))))))


let found_local_binding = (fun r uu____1159 -> (match (uu____1159) with
| (id', x, mut) -> begin
(

let uu____1166 = (bv_to_name x r)
in ((uu____1166), (mut)))
end))


let find_in_module = (fun env lid k_global_def k_not_found -> (

let uu____1203 = (FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str)
in (match (uu____1203) with
| FStar_Pervasives_Native.Some (sb) -> begin
(k_global_def lid sb)
end
| FStar_Pervasives_Native.None -> begin
k_not_found
end)))


let try_lookup_id : env  ->  FStar_Ident.ident  ->  (FStar_Syntax_Syntax.term * Prims.bool) FStar_Pervasives_Native.option = (fun env id -> (

let uu____1225 = (unmangleOpName id)
in (match (uu____1225) with
| FStar_Pervasives_Native.Some (f) -> begin
FStar_Pervasives_Native.Some (f)
end
| uu____1239 -> begin
(try_lookup_id'' env id Exported_id_term_type (fun r -> (

let uu____1246 = (found_local_binding id.FStar_Ident.idRange r)
in Cont_ok (uu____1246))) (fun uu____1251 -> Cont_fail) (fun uu____1254 -> Cont_ignore) (fun i -> (find_in_module env i (fun uu____1261 uu____1262 -> Cont_fail) Cont_ignore)) (fun uu____1269 uu____1270 -> Cont_fail))
end)))


let lookup_default_id = (fun env id k_global_def k_not_found -> (

let find_in_monad = (match (env.curmonad) with
| FStar_Pervasives_Native.Some (uu____1322) -> begin
(

let lid = (qualify env id)
in (

let uu____1324 = (FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str)
in (match (uu____1324) with
| FStar_Pervasives_Native.Some (r) -> begin
(

let uu____1337 = (k_global_def lid r)
in FStar_Pervasives_Native.Some (uu____1337))
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end)))
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end)
in (match (find_in_monad) with
| FStar_Pervasives_Native.Some (v1) -> begin
v1
end
| FStar_Pervasives_Native.None -> begin
(

let lid = (

let uu____1350 = (current_module env)
in (qual uu____1350 id))
in (find_in_module env lid k_global_def k_not_found))
end)))


let module_is_defined : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> ((match (env.curmodule) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (m) -> begin
(

let uu____1359 = (current_module env)
in (FStar_Ident.lid_equals lid uu____1359))
end) || (FStar_List.existsb (fun x -> (FStar_Ident.lid_equals lid (FStar_Pervasives_Native.fst x))) env.modules)))


let resolve_module_name : env  ->  FStar_Ident.lident  ->  Prims.bool  ->  FStar_Ident.lident FStar_Pervasives_Native.option = (fun env lid honor_ns -> (

let nslen = (FStar_List.length lid.FStar_Ident.ns)
in (

let rec aux = (fun uu___154_1383 -> (match (uu___154_1383) with
| [] -> begin
(

let uu____1386 = (module_is_defined env lid)
in (match (uu____1386) with
| true -> begin
FStar_Pervasives_Native.Some (lid)
end
| uu____1388 -> begin
FStar_Pervasives_Native.None
end))
end
| (Open_module_or_namespace (ns, Open_namespace))::q when honor_ns -> begin
(

let new_lid = (

let uu____1393 = (

let uu____1395 = (FStar_Ident.path_of_lid ns)
in (

let uu____1397 = (FStar_Ident.path_of_lid lid)
in (FStar_List.append uu____1395 uu____1397)))
in (FStar_Ident.lid_of_path uu____1393 (FStar_Ident.range_of_lid lid)))
in (

let uu____1399 = (module_is_defined env new_lid)
in (match (uu____1399) with
| true -> begin
FStar_Pervasives_Native.Some (new_lid)
end
| uu____1401 -> begin
(aux q)
end)))
end
| (Module_abbrev (name, modul))::uu____1404 when ((nslen = (Prims.parse_int "0")) && (name.FStar_Ident.idText = lid.FStar_Ident.ident.FStar_Ident.idText)) -> begin
FStar_Pervasives_Native.Some (modul)
end
| (uu____1408)::q -> begin
(aux q)
end))
in (aux env.scope_mods))))


let fail_if_curmodule : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  Prims.unit = (fun env ns_original ns_resolved -> (

let uu____1420 = (

let uu____1421 = (current_module env)
in (FStar_Ident.lid_equals ns_resolved uu____1421))
in (match (uu____1420) with
| true -> begin
(match ((FStar_Ident.lid_equals ns_resolved FStar_Parser_Const.prims_lid)) with
| true -> begin
()
end
| uu____1422 -> begin
(

let uu____1423 = (

let uu____1424 = (

let uu____1427 = (FStar_Util.format1 "Reference %s to current module is forbidden (see GitHub issue #451)" ns_original.FStar_Ident.str)
in ((uu____1427), ((FStar_Ident.range_of_lid ns_original))))
in FStar_Errors.Error (uu____1424))
in (FStar_Pervasives.raise uu____1423))
end)
end
| uu____1428 -> begin
()
end)))


let fail_if_qualified_by_curmodule : env  ->  FStar_Ident.lident  ->  Prims.unit = (fun env lid -> (match (lid.FStar_Ident.ns) with
| [] -> begin
()
end
| uu____1435 -> begin
(

let modul_orig = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in (

let uu____1438 = (resolve_module_name env modul_orig true)
in (match (uu____1438) with
| FStar_Pervasives_Native.Some (modul_res) -> begin
(fail_if_curmodule env modul_orig modul_res)
end
| uu____1441 -> begin
()
end)))
end))


let namespace_is_open : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (FStar_List.existsb (fun uu___155_1449 -> (match (uu___155_1449) with
| Open_module_or_namespace (ns, Open_namespace) -> begin
(FStar_Ident.lid_equals lid ns)
end
| uu____1451 -> begin
false
end)) env.scope_mods))


let shorten_module_path : env  ->  FStar_Ident.ident Prims.list  ->  Prims.bool  ->  (FStar_Ident.ident Prims.list * FStar_Ident.ident Prims.list) = (fun env ids is_full_path -> (

let rec aux = (fun revns id -> (

let lid = (FStar_Ident.lid_of_ns_and_id (FStar_List.rev revns) id)
in (match ((namespace_is_open env lid)) with
| true -> begin
FStar_Pervasives_Native.Some ((((FStar_List.rev ((id)::revns))), ([])))
end
| uu____1493 -> begin
(match (revns) with
| [] -> begin
FStar_Pervasives_Native.None
end
| (ns_last_id)::rev_ns_prefix -> begin
(

let uu____1506 = (aux rev_ns_prefix ns_last_id)
in (FStar_All.pipe_right uu____1506 (FStar_Util.map_option (fun uu____1530 -> (match (uu____1530) with
| (stripped_ids, rev_kept_ids) -> begin
((stripped_ids), ((id)::rev_kept_ids))
end)))))
end)
end)))
in (

let uu____1547 = (is_full_path && (

let uu____1548 = (FStar_Ident.lid_of_ids ids)
in (module_is_defined env uu____1548)))
in (match (uu____1547) with
| true -> begin
((ids), ([]))
end
| uu____1555 -> begin
(match ((FStar_List.rev ids)) with
| [] -> begin
(([]), ([]))
end
| (ns_last_id)::ns_rev_prefix -> begin
(

let uu____1565 = (aux ns_rev_prefix ns_last_id)
in (match (uu____1565) with
| FStar_Pervasives_Native.None -> begin
(([]), (ids))
end
| FStar_Pervasives_Native.Some (stripped_ids, rev_kept_ids) -> begin
((stripped_ids), ((FStar_List.rev rev_kept_ids)))
end))
end)
end))))


let shorten_lid : env  ->  FStar_Ident.lid  ->  FStar_Ident.lid = (fun env lid -> (

let uu____1599 = (shorten_module_path env lid.FStar_Ident.ns true)
in (match (uu____1599) with
| (uu____1604, short) -> begin
(FStar_Ident.lid_of_ns_and_id short lid.FStar_Ident.ident)
end)))


let resolve_in_open_namespaces'' = (fun env lid eikind k_local_binding k_rec_binding k_record f_module l_default -> (match (lid.FStar_Ident.ns) with
| (uu____1695)::uu____1696 -> begin
(

let uu____1698 = (

let uu____1700 = (

let uu____1701 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in (FStar_Ident.set_lid_range uu____1701 (FStar_Ident.range_of_lid lid)))
in (resolve_module_name env uu____1700 true))
in (match (uu____1698) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (modul) -> begin
(

let uu____1704 = (find_in_module_with_includes eikind f_module Cont_fail env modul lid.FStar_Ident.ident)
in (option_of_cont (fun uu____1706 -> FStar_Pervasives_Native.None) uu____1704))
end))
end
| [] -> begin
(try_lookup_id'' env lid.FStar_Ident.ident eikind k_local_binding k_rec_binding k_record f_module l_default)
end))


let cont_of_option = (fun k_none uu___156_1721 -> (match (uu___156_1721) with
| FStar_Pervasives_Native.Some (v1) -> begin
Cont_ok (v1)
end
| FStar_Pervasives_Native.None -> begin
k_none
end))


let resolve_in_open_namespaces' = (fun env lid k_local_binding k_rec_binding k_global_def -> (

let k_global_def' = (fun k lid1 def -> (

let uu____1800 = (k_global_def lid1 def)
in (cont_of_option k uu____1800)))
in (

let f_module = (fun lid' -> (

let k = Cont_ignore
in (find_in_module env lid' (k_global_def' k) k)))
in (

let l_default = (fun k i -> (lookup_default_id env i (k_global_def' k) k))
in (resolve_in_open_namespaces'' env lid Exported_id_term_type (fun l -> (

let uu____1821 = (k_local_binding l)
in (cont_of_option Cont_fail uu____1821))) (fun r -> (

let uu____1824 = (k_rec_binding r)
in (cont_of_option Cont_fail uu____1824))) (fun uu____1826 -> Cont_ignore) f_module l_default)))))


let fv_qual_of_se : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option = (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (uu____1832, uu____1833, uu____1834, l, uu____1836, uu____1837) -> begin
(

let qopt = (FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals (fun uu___157_1842 -> (match (uu___157_1842) with
| FStar_Syntax_Syntax.RecordConstructor (uu____1844, fs) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (((l), (fs))))
end
| uu____1851 -> begin
FStar_Pervasives_Native.None
end)))
in (match (qopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)
end
| x -> begin
x
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (uu____1855, uu____1856, uu____1857) -> begin
FStar_Pervasives_Native.None
end
| uu____1858 -> begin
FStar_Pervasives_Native.None
end))


let lb_fv : FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.fv = (fun lbs lid -> (

let uu____1867 = (FStar_Util.find_map lbs (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let uu____1871 = (FStar_Syntax_Syntax.fv_eq_lid fv lid)
in (match (uu____1871) with
| true -> begin
FStar_Pervasives_Native.Some (fv)
end
| uu____1873 -> begin
FStar_Pervasives_Native.None
end)))))
in (FStar_All.pipe_right uu____1867 FStar_Util.must)))


let ns_of_lid_equals : FStar_Ident.lident  ->  FStar_Ident.lident  ->  Prims.bool = (fun lid ns -> (((FStar_List.length lid.FStar_Ident.ns) = (FStar_List.length (FStar_Ident.ids_of_lid ns))) && (

let uu____1885 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in (FStar_Ident.lid_equals uu____1885 ns))))


let try_lookup_name : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  foundname FStar_Pervasives_Native.option = (fun any_val exclude_interf env lid -> (

let occurrence_range = (FStar_Ident.range_of_lid lid)
in (

let k_global_def = (fun source_lid uu___161_1910 -> (match (uu___161_1910) with
| (uu____1914, true) when exclude_interf -> begin
FStar_Pervasives_Native.None
end
| (se, uu____1916) -> begin
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____1918) -> begin
(

let uu____1927 = (

let uu____1928 = (

let uu____1931 = (FStar_Syntax_Syntax.fvar source_lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in ((uu____1931), (false)))
in Term_name (uu____1928))
in FStar_Pervasives_Native.Some (uu____1927))
end
| FStar_Syntax_Syntax.Sig_datacon (uu____1932) -> begin
(

let uu____1940 = (

let uu____1941 = (

let uu____1944 = (

let uu____1945 = (fv_qual_of_se se)
in (FStar_Syntax_Syntax.fvar source_lid FStar_Syntax_Syntax.Delta_constant uu____1945))
in ((uu____1944), (false)))
in Term_name (uu____1941))
in FStar_Pervasives_Native.Some (uu____1940))
end
| FStar_Syntax_Syntax.Sig_let ((uu____1947, lbs), uu____1949, uu____1950) -> begin
(

let fv = (lb_fv lbs source_lid)
in (

let uu____1961 = (

let uu____1962 = (

let uu____1965 = (FStar_Syntax_Syntax.fvar source_lid fv.FStar_Syntax_Syntax.fv_delta fv.FStar_Syntax_Syntax.fv_qual)
in ((uu____1965), (false)))
in Term_name (uu____1962))
in FStar_Pervasives_Native.Some (uu____1961)))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid1, uu____1967, uu____1968) -> begin
(

let quals = se.FStar_Syntax_Syntax.sigquals
in (

let uu____1971 = (any_val || (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___158_1973 -> (match (uu___158_1973) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| uu____1974 -> begin
false
end)))))
in (match (uu____1971) with
| true -> begin
(

let lid2 = (FStar_Ident.set_lid_range lid1 (FStar_Ident.range_of_lid source_lid))
in (

let dd = (

let uu____1978 = ((FStar_Syntax_Util.is_primop_lid lid2) || ((ns_of_lid_equals lid2 FStar_Parser_Const.prims_lid) && (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___159_1980 -> (match (uu___159_1980) with
| FStar_Syntax_Syntax.Projector (uu____1981) -> begin
true
end
| FStar_Syntax_Syntax.Discriminator (uu____1984) -> begin
true
end
| uu____1985 -> begin
false
end))))))
in (match (uu____1978) with
| true -> begin
FStar_Syntax_Syntax.Delta_equational
end
| uu____1986 -> begin
FStar_Syntax_Syntax.Delta_constant
end))
in (

let uu____1987 = (FStar_Util.find_map quals (fun uu___160_1989 -> (match (uu___160_1989) with
| FStar_Syntax_Syntax.Reflectable (refl_monad) -> begin
FStar_Pervasives_Native.Some (refl_monad)
end
| uu____1992 -> begin
FStar_Pervasives_Native.None
end)))
in (match (uu____1987) with
| FStar_Pervasives_Native.Some (refl_monad) -> begin
(

let refl_const = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (refl_monad))) FStar_Pervasives_Native.None occurrence_range)
in FStar_Pervasives_Native.Some (Term_name (((refl_const), (false)))))
end
| uu____2004 -> begin
(

let uu____2006 = (

let uu____2007 = (

let uu____2010 = (

let uu____2011 = (fv_qual_of_se se)
in (FStar_Syntax_Syntax.fvar lid2 dd uu____2011))
in ((uu____2010), (false)))
in Term_name (uu____2007))
in FStar_Pervasives_Native.Some (uu____2006))
end))))
end
| uu____2013 -> begin
FStar_Pervasives_Native.None
end)))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (ne) -> begin
FStar_Pervasives_Native.Some (Eff_name (((se), ((FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname (FStar_Ident.range_of_lid source_lid))))))
end
| FStar_Syntax_Syntax.Sig_new_effect (ne) -> begin
FStar_Pervasives_Native.Some (Eff_name (((se), ((FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname (FStar_Ident.range_of_lid source_lid))))))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (uu____2016) -> begin
FStar_Pervasives_Native.Some (Eff_name (((se), (source_lid))))
end
| uu____2023 -> begin
FStar_Pervasives_Native.None
end)
end))
in (

let k_local_binding = (fun r -> (

let uu____2035 = (

let uu____2036 = (found_local_binding (FStar_Ident.range_of_lid lid) r)
in Term_name (uu____2036))
in FStar_Pervasives_Native.Some (uu____2035)))
in (

let k_rec_binding = (fun uu____2046 -> (match (uu____2046) with
| (id, l, dd) -> begin
(

let uu____2054 = (

let uu____2055 = (

let uu____2058 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range l (FStar_Ident.range_of_lid lid)) dd FStar_Pervasives_Native.None)
in ((uu____2058), (false)))
in Term_name (uu____2055))
in FStar_Pervasives_Native.Some (uu____2054))
end))
in (

let found_unmangled = (match (lid.FStar_Ident.ns) with
| [] -> begin
(

let uu____2062 = (unmangleOpName lid.FStar_Ident.ident)
in (match (uu____2062) with
| FStar_Pervasives_Native.Some (f) -> begin
FStar_Pervasives_Native.Some (Term_name (f))
end
| uu____2072 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____2076 -> begin
FStar_Pervasives_Native.None
end)
in (match (found_unmangled) with
| FStar_Pervasives_Native.None -> begin
(resolve_in_open_namespaces' env lid k_local_binding k_rec_binding k_global_def)
end
| x -> begin
x
end)))))))


let try_lookup_effect_name' : Prims.bool  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident) FStar_Pervasives_Native.option = (fun exclude_interf env lid -> (

let uu____2096 = (try_lookup_name true exclude_interf env lid)
in (match (uu____2096) with
| FStar_Pervasives_Native.Some (Eff_name (o, l)) -> begin
FStar_Pervasives_Native.Some (((o), (l)))
end
| uu____2105 -> begin
FStar_Pervasives_Native.None
end)))


let try_lookup_effect_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident FStar_Pervasives_Native.option = (fun env l -> (

let uu____2116 = (try_lookup_effect_name' (not (env.iface)) env l)
in (match (uu____2116) with
| FStar_Pervasives_Native.Some (o, l1) -> begin
FStar_Pervasives_Native.Some (l1)
end
| uu____2125 -> begin
FStar_Pervasives_Native.None
end)))


let try_lookup_effect_name_and_attributes : env  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.cflags Prims.list) FStar_Pervasives_Native.option = (fun env l -> (

let uu____2139 = (try_lookup_effect_name' (not (env.iface)) env l)
in (match (uu____2139) with
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect (ne); FStar_Syntax_Syntax.sigrng = uu____2148; FStar_Syntax_Syntax.sigquals = uu____2149; FStar_Syntax_Syntax.sigmeta = uu____2150}, l1) -> begin
FStar_Pervasives_Native.Some (((l1), (ne.FStar_Syntax_Syntax.cattributes)))
end
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect_for_free (ne); FStar_Syntax_Syntax.sigrng = uu____2160; FStar_Syntax_Syntax.sigquals = uu____2161; FStar_Syntax_Syntax.sigmeta = uu____2162}, l1) -> begin
FStar_Pervasives_Native.Some (((l1), (ne.FStar_Syntax_Syntax.cattributes)))
end
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_effect_abbrev (uu____2171, uu____2172, uu____2173, uu____2174, cattributes); FStar_Syntax_Syntax.sigrng = uu____2176; FStar_Syntax_Syntax.sigquals = uu____2177; FStar_Syntax_Syntax.sigmeta = uu____2178}, l1) -> begin
FStar_Pervasives_Native.Some (((l1), (cattributes)))
end
| uu____2189 -> begin
FStar_Pervasives_Native.None
end)))


let try_lookup_effect_defn : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl FStar_Pervasives_Native.option = (fun env l -> (

let uu____2203 = (try_lookup_effect_name' (not (env.iface)) env l)
in (match (uu____2203) with
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect (ne); FStar_Syntax_Syntax.sigrng = uu____2209; FStar_Syntax_Syntax.sigquals = uu____2210; FStar_Syntax_Syntax.sigmeta = uu____2211}, uu____2212) -> begin
FStar_Pervasives_Native.Some (ne)
end
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect_for_free (ne); FStar_Syntax_Syntax.sigrng = uu____2217; FStar_Syntax_Syntax.sigquals = uu____2218; FStar_Syntax_Syntax.sigmeta = uu____2219}, uu____2220) -> begin
FStar_Pervasives_Native.Some (ne)
end
| uu____2224 -> begin
FStar_Pervasives_Native.None
end)))


let is_effect_name : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let uu____2234 = (try_lookup_effect_name env lid)
in (match (uu____2234) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (uu____2236) -> begin
true
end)))


let try_lookup_root_effect_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident FStar_Pervasives_Native.option = (fun env l -> (

let uu____2244 = (try_lookup_effect_name' (not (env.iface)) env l)
in (match (uu____2244) with
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_effect_abbrev (l', uu____2250, uu____2251, uu____2252, uu____2253); FStar_Syntax_Syntax.sigrng = uu____2254; FStar_Syntax_Syntax.sigquals = uu____2255; FStar_Syntax_Syntax.sigmeta = uu____2256}, uu____2257) -> begin
(

let rec aux = (fun new_name -> (

let uu____2268 = (FStar_Util.smap_try_find (sigmap env) new_name.FStar_Ident.str)
in (match (uu____2268) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (s, uu____2278) -> begin
(match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_new_effect_for_free (ne) -> begin
FStar_Pervasives_Native.Some ((FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname (FStar_Ident.range_of_lid l)))
end
| FStar_Syntax_Syntax.Sig_new_effect (ne) -> begin
FStar_Pervasives_Native.Some ((FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname (FStar_Ident.range_of_lid l)))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (uu____2284, uu____2285, uu____2286, cmp, uu____2288) -> begin
(

let l'' = (FStar_Syntax_Util.comp_effect_name cmp)
in (aux l''))
end
| uu____2292 -> begin
FStar_Pervasives_Native.None
end)
end)))
in (aux l'))
end
| FStar_Pervasives_Native.Some (uu____2293, l') -> begin
FStar_Pervasives_Native.Some (l')
end
| uu____2297 -> begin
FStar_Pervasives_Native.None
end)))


let lookup_letbinding_quals : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.qualifier Prims.list = (fun env lid -> (

let k_global_def = (fun lid1 uu___162_2318 -> (match (uu___162_2318) with
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (uu____2323, uu____2324, uu____2325); FStar_Syntax_Syntax.sigrng = uu____2326; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = uu____2328}, uu____2329) -> begin
FStar_Pervasives_Native.Some (quals)
end
| uu____2332 -> begin
FStar_Pervasives_Native.None
end))
in (

let uu____2336 = (resolve_in_open_namespaces' env lid (fun uu____2340 -> FStar_Pervasives_Native.None) (fun uu____2342 -> FStar_Pervasives_Native.None) k_global_def)
in (match (uu____2336) with
| FStar_Pervasives_Native.Some (quals) -> begin
quals
end
| uu____2348 -> begin
[]
end))))


let try_lookup_module : env  ->  Prims.string Prims.list  ->  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option = (fun env path -> (

let uu____2360 = (FStar_List.tryFind (fun uu____2366 -> (match (uu____2366) with
| (mlid, modul) -> begin
(

let uu____2371 = (FStar_Ident.path_of_lid mlid)
in (uu____2371 = path))
end)) env.modules)
in (match (uu____2360) with
| FStar_Pervasives_Native.Some (uu____2375, modul) -> begin
FStar_Pervasives_Native.Some (modul)
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end)))


let try_lookup_let : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun env lid -> (

let k_global_def = (fun lid1 uu___163_2397 -> (match (uu___163_2397) with
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let ((uu____2401, lbs), uu____2403, uu____2404); FStar_Syntax_Syntax.sigrng = uu____2405; FStar_Syntax_Syntax.sigquals = uu____2406; FStar_Syntax_Syntax.sigmeta = uu____2407}, uu____2408) -> begin
(

let fv = (lb_fv lbs lid1)
in (

let uu____2420 = (FStar_Syntax_Syntax.fvar lid1 fv.FStar_Syntax_Syntax.fv_delta fv.FStar_Syntax_Syntax.fv_qual)
in FStar_Pervasives_Native.Some (uu____2420)))
end
| uu____2421 -> begin
FStar_Pervasives_Native.None
end))
in (resolve_in_open_namespaces' env lid (fun uu____2424 -> FStar_Pervasives_Native.None) (fun uu____2425 -> FStar_Pervasives_Native.None) k_global_def)))


let try_lookup_definition : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun env lid -> (

let k_global_def = (fun lid1 uu___164_2444 -> (match (uu___164_2444) with
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (lbs, uu____2451, uu____2452); FStar_Syntax_Syntax.sigrng = uu____2453; FStar_Syntax_Syntax.sigquals = uu____2454; FStar_Syntax_Syntax.sigmeta = uu____2455}, uu____2456) -> begin
(FStar_Util.find_map (FStar_Pervasives_Native.snd lbs) (fun lb -> (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv lid1) -> begin
FStar_Pervasives_Native.Some (lb.FStar_Syntax_Syntax.lbdef)
end
| uu____2472 -> begin
FStar_Pervasives_Native.None
end)))
end
| uu____2477 -> begin
FStar_Pervasives_Native.None
end))
in (resolve_in_open_namespaces' env lid (fun uu____2484 -> FStar_Pervasives_Native.None) (fun uu____2487 -> FStar_Pervasives_Native.None) k_global_def)))


let empty_include_smap : FStar_Ident.lident Prims.list FStar_ST.ref FStar_Util.smap = (new_sigmap ())


let empty_exported_id_smap : exported_id_set FStar_Util.smap = (new_sigmap ())


let try_lookup_lid' : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term * Prims.bool) FStar_Pervasives_Native.option = (fun any_val exclude_interf env lid -> (

let uu____2514 = (try_lookup_name any_val exclude_interf env lid)
in (match (uu____2514) with
| FStar_Pervasives_Native.Some (Term_name (e, mut)) -> begin
FStar_Pervasives_Native.Some (((e), (mut)))
end
| uu____2523 -> begin
FStar_Pervasives_Native.None
end)))


let try_lookup_lid : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term * Prims.bool) FStar_Pervasives_Native.option = (fun env l -> (try_lookup_lid' env.iface false env l))


let resolve_to_fully_qualified_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident FStar_Pervasives_Native.option = (fun env l -> (

let uu____2543 = (try_lookup_lid env l)
in (match (uu____2543) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (e, uu____2551) -> begin
(

let uu____2554 = (

let uu____2555 = (FStar_Syntax_Subst.compress e)
in uu____2555.FStar_Syntax_Syntax.n)
in (match (uu____2554) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
FStar_Pervasives_Native.Some (fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end
| uu____2564 -> begin
FStar_Pervasives_Native.None
end))
end)))


let try_lookup_lid_no_resolve : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term * Prims.bool) FStar_Pervasives_Native.option = (fun env l -> (

let env' = (

let uu___182_2575 = env
in {curmodule = uu___182_2575.curmodule; curmonad = uu___182_2575.curmonad; modules = uu___182_2575.modules; scope_mods = []; exported_ids = empty_exported_id_smap; trans_exported_ids = uu___182_2575.trans_exported_ids; includes = empty_include_smap; sigaccum = uu___182_2575.sigaccum; sigmap = uu___182_2575.sigmap; iface = uu___182_2575.iface; admitted_iface = uu___182_2575.admitted_iface; expect_typ = uu___182_2575.expect_typ; docs = uu___182_2575.docs; remaining_iface_decls = uu___182_2575.remaining_iface_decls; syntax_only = uu___182_2575.syntax_only})
in (try_lookup_lid env' l)))


let try_lookup_doc : env  ->  FStar_Ident.lid  ->  FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option = (fun env l -> (FStar_Util.smap_try_find env.docs l.FStar_Ident.str))


let try_lookup_datacon : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.fv FStar_Pervasives_Native.option = (fun env lid -> (

let k_global_def = (fun lid1 uu___166_2599 -> (match (uu___166_2599) with
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (uu____2603, uu____2604, uu____2605); FStar_Syntax_Syntax.sigrng = uu____2606; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = uu____2608}, uu____2609) -> begin
(

let uu____2611 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___165_2613 -> (match (uu___165_2613) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| uu____2614 -> begin
false
end))))
in (match (uu____2611) with
| true -> begin
(

let uu____2616 = (FStar_Syntax_Syntax.lid_as_fv lid1 FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in FStar_Pervasives_Native.Some (uu____2616))
end
| uu____2617 -> begin
FStar_Pervasives_Native.None
end))
end
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (uu____2618); FStar_Syntax_Syntax.sigrng = uu____2619; FStar_Syntax_Syntax.sigquals = uu____2620; FStar_Syntax_Syntax.sigmeta = uu____2621}, uu____2622) -> begin
(

let uu____2631 = (FStar_Syntax_Syntax.lid_as_fv lid1 FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))
in FStar_Pervasives_Native.Some (uu____2631))
end
| uu____2632 -> begin
FStar_Pervasives_Native.None
end))
in (resolve_in_open_namespaces' env lid (fun uu____2635 -> FStar_Pervasives_Native.None) (fun uu____2636 -> FStar_Pervasives_Native.None) k_global_def)))


let find_all_datacons : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.list FStar_Pervasives_Native.option = (fun env lid -> (

let k_global_def = (fun lid1 uu___167_2655 -> (match (uu___167_2655) with
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (uu____2660, uu____2661, uu____2662, uu____2663, datas, uu____2665); FStar_Syntax_Syntax.sigrng = uu____2666; FStar_Syntax_Syntax.sigquals = uu____2667; FStar_Syntax_Syntax.sigmeta = uu____2668}, uu____2669) -> begin
FStar_Pervasives_Native.Some (datas)
end
| uu____2676 -> begin
FStar_Pervasives_Native.None
end))
in (resolve_in_open_namespaces' env lid (fun uu____2681 -> FStar_Pervasives_Native.None) (fun uu____2683 -> FStar_Pervasives_Native.None) k_global_def)))


let record_cache_aux_with_filter : (((Prims.unit  ->  Prims.unit) * (Prims.unit  ->  Prims.unit) * (Prims.unit  ->  record_or_dc Prims.list) * (record_or_dc  ->  Prims.unit) * (Prims.unit  ->  Prims.unit)) * (Prims.unit  ->  Prims.unit)) = (

let record_cache = (FStar_Util.mk_ref (([])::[]))
in (

let push1 = (fun uu____2717 -> (

let uu____2718 = (

let uu____2721 = (

let uu____2723 = (FStar_ST.read record_cache)
in (FStar_List.hd uu____2723))
in (

let uu____2731 = (FStar_ST.read record_cache)
in (uu____2721)::uu____2731))
in (FStar_ST.write record_cache uu____2718)))
in (

let pop1 = (fun uu____2746 -> (

let uu____2747 = (

let uu____2750 = (FStar_ST.read record_cache)
in (FStar_List.tl uu____2750))
in (FStar_ST.write record_cache uu____2747)))
in (

let peek = (fun uu____2766 -> (

let uu____2767 = (FStar_ST.read record_cache)
in (FStar_List.hd uu____2767)))
in (

let insert = (fun r -> (

let uu____2779 = (

let uu____2782 = (

let uu____2784 = (peek ())
in (r)::uu____2784)
in (

let uu____2786 = (

let uu____2789 = (FStar_ST.read record_cache)
in (FStar_List.tl uu____2789))
in (uu____2782)::uu____2786))
in (FStar_ST.write record_cache uu____2779)))
in (

let commit1 = (fun uu____2805 -> (

let uu____2806 = (FStar_ST.read record_cache)
in (match (uu____2806) with
| (hd1)::(uu____2814)::tl1 -> begin
(FStar_ST.write record_cache ((hd1)::tl1))
end
| uu____2827 -> begin
(failwith "Impossible")
end)))
in (

let filter1 = (fun uu____2833 -> (

let rc = (peek ())
in ((pop1 ());
(match (()) with
| () -> begin
(

let filtered = (FStar_List.filter (fun r -> (not (r.is_private_or_abstract))) rc)
in (

let uu____2840 = (

let uu____2843 = (FStar_ST.read record_cache)
in (filtered)::uu____2843)
in (FStar_ST.write record_cache uu____2840)))
end);
)))
in (

let aux = ((push1), (pop1), (peek), (insert), (commit1))
in ((aux), (filter1))))))))))


let record_cache_aux : ((Prims.unit  ->  Prims.unit) * (Prims.unit  ->  Prims.unit) * (Prims.unit  ->  record_or_dc Prims.list) * (record_or_dc  ->  Prims.unit) * (Prims.unit  ->  Prims.unit)) = (

let uu____2917 = record_cache_aux_with_filter
in (match (uu____2917) with
| (aux, uu____2955) -> begin
aux
end))


let filter_record_cache : Prims.unit  ->  Prims.unit = (

let uu____2994 = record_cache_aux_with_filter
in (match (uu____2994) with
| (uu____3017, filter1) -> begin
filter1
end))


let push_record_cache : Prims.unit  ->  Prims.unit = (

let uu____3057 = record_cache_aux
in (match (uu____3057) with
| (push1, uu____3077, uu____3078, uu____3079, uu____3080) -> begin
push1
end))


let pop_record_cache : Prims.unit  ->  Prims.unit = (

let uu____3105 = record_cache_aux
in (match (uu____3105) with
| (uu____3124, pop1, uu____3126, uu____3127, uu____3128) -> begin
pop1
end))


let peek_record_cache : Prims.unit  ->  record_or_dc Prims.list = (

let uu____3154 = record_cache_aux
in (match (uu____3154) with
| (uu____3174, uu____3175, peek, uu____3177, uu____3178) -> begin
peek
end))


let insert_record_cache : record_or_dc  ->  Prims.unit = (

let uu____3203 = record_cache_aux
in (match (uu____3203) with
| (uu____3222, uu____3223, uu____3224, insert, uu____3226) -> begin
insert
end))


let commit_record_cache : Prims.unit  ->  Prims.unit = (

let uu____3251 = record_cache_aux
in (match (uu____3251) with
| (uu____3270, uu____3271, uu____3272, uu____3273, commit1) -> begin
commit1
end))


let extract_record : env  ->  scope_mod Prims.list FStar_ST.ref  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun e new_globs se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_bundle (sigs, uu____3313) -> begin
(

let is_record = (FStar_Util.for_some (fun uu___168_3322 -> (match (uu___168_3322) with
| FStar_Syntax_Syntax.RecordType (uu____3323) -> begin
true
end
| FStar_Syntax_Syntax.RecordConstructor (uu____3328) -> begin
true
end
| uu____3333 -> begin
false
end)))
in (

let find_dc = (fun dc -> (FStar_All.pipe_right sigs (FStar_Util.find_opt (fun uu___169_3341 -> (match (uu___169_3341) with
| {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (lid, uu____3343, uu____3344, uu____3345, uu____3346, uu____3347); FStar_Syntax_Syntax.sigrng = uu____3348; FStar_Syntax_Syntax.sigquals = uu____3349; FStar_Syntax_Syntax.sigmeta = uu____3350} -> begin
(FStar_Ident.lid_equals dc lid)
end
| uu____3354 -> begin
false
end)))))
in (FStar_All.pipe_right sigs (FStar_List.iter (fun uu___170_3356 -> (match (uu___170_3356) with
| {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (typename, univs, parms, uu____3360, uu____3361, (dc)::[]); FStar_Syntax_Syntax.sigrng = uu____3363; FStar_Syntax_Syntax.sigquals = typename_quals; FStar_Syntax_Syntax.sigmeta = uu____3365} -> begin
(

let uu____3370 = (

let uu____3371 = (find_dc dc)
in (FStar_All.pipe_left FStar_Util.must uu____3371))
in (match (uu____3370) with
| {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (constrname, uu____3375, t, uu____3377, uu____3378, uu____3379); FStar_Syntax_Syntax.sigrng = uu____3380; FStar_Syntax_Syntax.sigquals = uu____3381; FStar_Syntax_Syntax.sigmeta = uu____3382} -> begin
(

let uu____3386 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____3386) with
| (formals, uu____3395) -> begin
(

let is_rec = (is_record typename_quals)
in (

let formals' = (FStar_All.pipe_right formals (FStar_List.collect (fun uu____3421 -> (match (uu____3421) with
| (x, q) -> begin
(

let uu____3429 = ((FStar_Syntax_Syntax.is_null_bv x) || (is_rec && (FStar_Syntax_Syntax.is_implicit q)))
in (match (uu____3429) with
| true -> begin
[]
end
| uu____3435 -> begin
(((x), (q)))::[]
end))
end))))
in (

let fields' = (FStar_All.pipe_right formals' (FStar_List.map (fun uu____3460 -> (match (uu____3460) with
| (x, q) -> begin
(

let uu____3469 = (match (is_rec) with
| true -> begin
(FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname)
end
| uu____3470 -> begin
x.FStar_Syntax_Syntax.ppname
end)
in ((uu____3469), (x.FStar_Syntax_Syntax.sort)))
end))))
in (

let fields = fields'
in (

let record = {typename = typename; constrname = constrname.FStar_Ident.ident; parms = parms; fields = fields; is_private_or_abstract = ((FStar_List.contains FStar_Syntax_Syntax.Private typename_quals) || (FStar_List.contains FStar_Syntax_Syntax.Abstract typename_quals)); is_record = is_rec}
in ((

let uu____3481 = (

let uu____3483 = (FStar_ST.read new_globs)
in (Record_or_dc (record))::uu____3483)
in (FStar_ST.write new_globs uu____3481));
(match (()) with
| () -> begin
((

let add_field = (fun uu____3499 -> (match (uu____3499) with
| (id, uu____3505) -> begin
(

let modul = (

let uu____3511 = (FStar_Ident.lid_of_ids constrname.FStar_Ident.ns)
in uu____3511.FStar_Ident.str)
in (

let uu____3512 = (get_exported_id_set e modul)
in (match (uu____3512) with
| FStar_Pervasives_Native.Some (my_ex) -> begin
(

let my_exported_ids = (my_ex Exported_id_field)
in ((

let uu____3528 = (

let uu____3529 = (FStar_ST.read my_exported_ids)
in (FStar_Util.set_add id.FStar_Ident.idText uu____3529))
in (FStar_ST.write my_exported_ids uu____3528));
(match (()) with
| () -> begin
(

let projname = (

let uu____3536 = (

let uu____3537 = (FStar_Syntax_Util.mk_field_projector_name_from_ident constrname id)
in uu____3537.FStar_Ident.ident)
in uu____3536.FStar_Ident.idText)
in (

let uu____3539 = (

let uu____3540 = (FStar_ST.read my_exported_ids)
in (FStar_Util.set_add projname uu____3540))
in (FStar_ST.write my_exported_ids uu____3539)))
end);
))
end
| FStar_Pervasives_Native.None -> begin
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
| uu____3553 -> begin
()
end))
end
| uu____3554 -> begin
()
end))))))
end
| uu____3555 -> begin
()
end))


let try_lookup_record_or_dc_by_field_name : env  ->  FStar_Ident.lident  ->  record_or_dc FStar_Pervasives_Native.option = (fun env fieldname -> (

let find_in_cache = (fun fieldname1 -> (

let uu____3568 = ((fieldname1.FStar_Ident.ns), (fieldname1.FStar_Ident.ident))
in (match (uu____3568) with
| (ns, id) -> begin
(

let uu____3578 = (peek_record_cache ())
in (FStar_Util.find_map uu____3578 (fun record -> (

let uu____3581 = (find_in_record ns id record (fun r -> Cont_ok (r)))
in (option_of_cont (fun uu____3584 -> FStar_Pervasives_Native.None) uu____3581)))))
end)))
in (resolve_in_open_namespaces'' env fieldname Exported_id_field (fun uu____3585 -> Cont_ignore) (fun uu____3586 -> Cont_ignore) (fun r -> Cont_ok (r)) (fun fn -> (

let uu____3589 = (find_in_cache fn)
in (cont_of_option Cont_ignore uu____3589))) (fun k uu____3592 -> k))))


let try_lookup_record_by_field_name : env  ->  FStar_Ident.lident  ->  record_or_dc FStar_Pervasives_Native.option = (fun env fieldname -> (

let uu____3601 = (try_lookup_record_or_dc_by_field_name env fieldname)
in (match (uu____3601) with
| FStar_Pervasives_Native.Some (r) when r.is_record -> begin
FStar_Pervasives_Native.Some (r)
end
| uu____3605 -> begin
FStar_Pervasives_Native.None
end)))


let belongs_to_record : env  ->  FStar_Ident.lident  ->  record_or_dc  ->  Prims.bool = (fun env lid record -> (

let uu____3616 = (try_lookup_record_by_field_name env lid)
in (match (uu____3616) with
| FStar_Pervasives_Native.Some (record') when (

let uu____3619 = (

let uu____3620 = (FStar_Ident.path_of_ns record.typename.FStar_Ident.ns)
in (FStar_Ident.text_of_path uu____3620))
in (

let uu____3622 = (

let uu____3623 = (FStar_Ident.path_of_ns record'.typename.FStar_Ident.ns)
in (FStar_Ident.text_of_path uu____3623))
in (uu____3619 = uu____3622))) -> begin
(

let uu____3625 = (find_in_record record.typename.FStar_Ident.ns lid.FStar_Ident.ident record (fun uu____3627 -> Cont_ok (())))
in (match (uu____3625) with
| Cont_ok (uu____3628) -> begin
true
end
| uu____3629 -> begin
false
end))
end
| uu____3631 -> begin
false
end)))


let try_lookup_dc_by_field_name : env  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * Prims.bool) FStar_Pervasives_Native.option = (fun env fieldname -> (

let uu____3642 = (try_lookup_record_or_dc_by_field_name env fieldname)
in (match (uu____3642) with
| FStar_Pervasives_Native.Some (r) -> begin
(

let uu____3648 = (

let uu____3651 = (

let uu____3652 = (FStar_Ident.lid_of_ids (FStar_List.append r.typename.FStar_Ident.ns ((r.constrname)::[])))
in (FStar_Ident.set_lid_range uu____3652 (FStar_Ident.range_of_lid fieldname)))
in ((uu____3651), (r.is_record)))
in FStar_Pervasives_Native.Some (uu____3648))
end
| uu____3655 -> begin
FStar_Pervasives_Native.None
end)))


let string_set_ref_new : Prims.unit  ->  Prims.string FStar_Util.set FStar_ST.ref = (fun uu____3664 -> (

let uu____3665 = (FStar_Util.new_set FStar_Util.compare FStar_Util.hashcode)
in (FStar_Util.mk_ref uu____3665)))


let exported_id_set_new : Prims.unit  ->  exported_id_kind  ->  Prims.string FStar_Util.set FStar_ST.ref = (fun uu____3676 -> (

let term_type_set = (string_set_ref_new ())
in (

let field_set = (string_set_ref_new ())
in (fun uu___171_3685 -> (match (uu___171_3685) with
| Exported_id_term_type -> begin
term_type_set
end
| Exported_id_field -> begin
field_set
end)))))


let unique : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  Prims.bool = (fun any_val exclude_if env lid -> (

let filter_scope_mods = (fun uu___172_3705 -> (match (uu___172_3705) with
| Rec_binding (uu____3706) -> begin
true
end
| uu____3707 -> begin
false
end))
in (

let this_env = (

let uu___183_3709 = env
in (

let uu____3710 = (FStar_List.filter filter_scope_mods env.scope_mods)
in {curmodule = uu___183_3709.curmodule; curmonad = uu___183_3709.curmonad; modules = uu___183_3709.modules; scope_mods = uu____3710; exported_ids = empty_exported_id_smap; trans_exported_ids = uu___183_3709.trans_exported_ids; includes = empty_include_smap; sigaccum = uu___183_3709.sigaccum; sigmap = uu___183_3709.sigmap; iface = uu___183_3709.iface; admitted_iface = uu___183_3709.admitted_iface; expect_typ = uu___183_3709.expect_typ; docs = uu___183_3709.docs; remaining_iface_decls = uu___183_3709.remaining_iface_decls; syntax_only = uu___183_3709.syntax_only}))
in (

let uu____3712 = (try_lookup_lid' any_val exclude_if this_env lid)
in (match (uu____3712) with
| FStar_Pervasives_Native.None -> begin
true
end
| FStar_Pervasives_Native.Some (uu____3718) -> begin
false
end)))))


let push_scope_mod : env  ->  scope_mod  ->  env = (fun env scope_mod -> (

let uu___184_3729 = env
in {curmodule = uu___184_3729.curmodule; curmonad = uu___184_3729.curmonad; modules = uu___184_3729.modules; scope_mods = (scope_mod)::env.scope_mods; exported_ids = uu___184_3729.exported_ids; trans_exported_ids = uu___184_3729.trans_exported_ids; includes = uu___184_3729.includes; sigaccum = uu___184_3729.sigaccum; sigmap = uu___184_3729.sigmap; iface = uu___184_3729.iface; admitted_iface = uu___184_3729.admitted_iface; expect_typ = uu___184_3729.expect_typ; docs = uu___184_3729.docs; remaining_iface_decls = uu___184_3729.remaining_iface_decls; syntax_only = uu___184_3729.syntax_only}))


let push_bv' : env  ->  FStar_Ident.ident  ->  Prims.bool  ->  (env * FStar_Syntax_Syntax.bv) = (fun env x is_mutable -> (

let bv = (FStar_Syntax_Syntax.gen_bv x.FStar_Ident.idText (FStar_Pervasives_Native.Some (x.FStar_Ident.idRange)) FStar_Syntax_Syntax.tun)
in (((push_scope_mod env (Local_binding (((x), (bv), (is_mutable)))))), (bv))))


let push_bv_mutable : env  ->  FStar_Ident.ident  ->  (env * FStar_Syntax_Syntax.bv) = (fun env x -> (push_bv' env x true))


let push_bv : env  ->  FStar_Ident.ident  ->  (env * FStar_Syntax_Syntax.bv) = (fun env x -> (push_bv' env x false))


let push_top_level_rec_binding : env  ->  FStar_Ident.ident  ->  FStar_Syntax_Syntax.delta_depth  ->  env = (fun env x dd -> (

let l = (qualify env x)
in (

let uu____3768 = ((unique false true env l) || (FStar_Options.interactive ()))
in (match (uu____3768) with
| true -> begin
(push_scope_mod env (Rec_binding (((x), (l), (dd)))))
end
| uu____3769 -> begin
(FStar_Pervasives.raise (FStar_Errors.Error ((((Prims.strcat "Duplicate top-level names " l.FStar_Ident.str)), ((FStar_Ident.range_of_lid l))))))
end))))


let push_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env s -> (

let err1 = (fun l -> (

let sopt = (FStar_Util.smap_try_find (sigmap env) l.FStar_Ident.str)
in (

let r = (match (sopt) with
| FStar_Pervasives_Native.Some (se, uu____3788) -> begin
(

let uu____3791 = (FStar_Util.find_opt (FStar_Ident.lid_equals l) (FStar_Syntax_Util.lids_of_sigelt se))
in (match (uu____3791) with
| FStar_Pervasives_Native.Some (l1) -> begin
(FStar_All.pipe_left FStar_Range.string_of_range (FStar_Ident.range_of_lid l1))
end
| FStar_Pervasives_Native.None -> begin
"<unknown>"
end))
end
| FStar_Pervasives_Native.None -> begin
"<unknown>"
end)
in (

let uu____3796 = (

let uu____3797 = (

let uu____3800 = (FStar_Util.format2 "Duplicate top-level names [%s]; previously declared at %s" (FStar_Ident.text_of_lid l) r)
in ((uu____3800), ((FStar_Ident.range_of_lid l))))
in FStar_Errors.Error (uu____3797))
in (FStar_Pervasives.raise uu____3796)))))
in (

let globals = (FStar_Util.mk_ref env.scope_mods)
in (

let env1 = (

let uu____3807 = (match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let (uu____3812) -> begin
((false), (true))
end
| FStar_Syntax_Syntax.Sig_bundle (uu____3818) -> begin
((true), (true))
end
| uu____3823 -> begin
((false), (false))
end)
in (match (uu____3807) with
| (any_val, exclude_if) -> begin
(

let lids = (FStar_Syntax_Util.lids_of_sigelt s)
in (

let uu____3828 = (FStar_Util.find_map lids (fun l -> (

let uu____3831 = (

let uu____3832 = (unique any_val exclude_if env l)
in (not (uu____3832)))
in (match (uu____3831) with
| true -> begin
FStar_Pervasives_Native.Some (l)
end
| uu____3834 -> begin
FStar_Pervasives_Native.None
end))))
in (match (uu____3828) with
| FStar_Pervasives_Native.Some (l) when (

let uu____3836 = (FStar_Options.interactive ())
in (not (uu____3836))) -> begin
(err1 l)
end
| uu____3837 -> begin
((extract_record env globals s);
(

let uu___185_3842 = env
in {curmodule = uu___185_3842.curmodule; curmonad = uu___185_3842.curmonad; modules = uu___185_3842.modules; scope_mods = uu___185_3842.scope_mods; exported_ids = uu___185_3842.exported_ids; trans_exported_ids = uu___185_3842.trans_exported_ids; includes = uu___185_3842.includes; sigaccum = (s)::env.sigaccum; sigmap = uu___185_3842.sigmap; iface = uu___185_3842.iface; admitted_iface = uu___185_3842.admitted_iface; expect_typ = uu___185_3842.expect_typ; docs = uu___185_3842.docs; remaining_iface_decls = uu___185_3842.remaining_iface_decls; syntax_only = uu___185_3842.syntax_only});
)
end)))
end))
in (

let env2 = (

let uu___186_3844 = env1
in (

let uu____3845 = (FStar_ST.read globals)
in {curmodule = uu___186_3844.curmodule; curmonad = uu___186_3844.curmonad; modules = uu___186_3844.modules; scope_mods = uu____3845; exported_ids = uu___186_3844.exported_ids; trans_exported_ids = uu___186_3844.trans_exported_ids; includes = uu___186_3844.includes; sigaccum = uu___186_3844.sigaccum; sigmap = uu___186_3844.sigmap; iface = uu___186_3844.iface; admitted_iface = uu___186_3844.admitted_iface; expect_typ = uu___186_3844.expect_typ; docs = uu___186_3844.docs; remaining_iface_decls = uu___186_3844.remaining_iface_decls; syntax_only = uu___186_3844.syntax_only}))
in (

let uu____3850 = (match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____3864) -> begin
(

let uu____3869 = (FStar_List.map (fun se -> (((FStar_Syntax_Util.lids_of_sigelt se)), (se))) ses)
in ((env2), (uu____3869)))
end
| uu____3883 -> begin
((env2), (((((FStar_Syntax_Util.lids_of_sigelt s)), (s)))::[]))
end)
in (match (uu____3850) with
| (env3, lss) -> begin
((FStar_All.pipe_right lss (FStar_List.iter (fun uu____3913 -> (match (uu____3913) with
| (lids, se) -> begin
(FStar_All.pipe_right lids (FStar_List.iter (fun lid -> ((

let uu____3924 = (

let uu____3926 = (FStar_ST.read globals)
in (Top_level_def (lid.FStar_Ident.ident))::uu____3926)
in (FStar_ST.write globals uu____3924));
(match (()) with
| () -> begin
(

let modul = (

let uu____3935 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in uu____3935.FStar_Ident.str)
in ((

let uu____3937 = (get_exported_id_set env3 modul)
in (match (uu____3937) with
| FStar_Pervasives_Native.Some (f) -> begin
(

let my_exported_ids = (f Exported_id_term_type)
in (

let uu____3952 = (

let uu____3953 = (FStar_ST.read my_exported_ids)
in (FStar_Util.set_add lid.FStar_Ident.ident.FStar_Ident.idText uu____3953))
in (FStar_ST.write my_exported_ids uu____3952)))
end
| FStar_Pervasives_Native.None -> begin
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

let uu___187_3965 = env3
in (

let uu____3966 = (FStar_ST.read globals)
in {curmodule = uu___187_3965.curmodule; curmonad = uu___187_3965.curmonad; modules = uu___187_3965.modules; scope_mods = uu____3966; exported_ids = uu___187_3965.exported_ids; trans_exported_ids = uu___187_3965.trans_exported_ids; includes = uu___187_3965.includes; sigaccum = uu___187_3965.sigaccum; sigmap = uu___187_3965.sigmap; iface = uu___187_3965.iface; admitted_iface = uu___187_3965.admitted_iface; expect_typ = uu___187_3965.expect_typ; docs = uu___187_3965.docs; remaining_iface_decls = uu___187_3965.remaining_iface_decls; syntax_only = uu___187_3965.syntax_only}))
in env4);
)
end)))))))


let push_namespace : env  ->  FStar_Ident.lident  ->  env = (fun env ns -> (

let uu____3977 = (

let uu____3980 = (resolve_module_name env ns false)
in (match (uu____3980) with
| FStar_Pervasives_Native.None -> begin
(

let modules = env.modules
in (

let uu____3988 = (FStar_All.pipe_right modules (FStar_Util.for_some (fun uu____3994 -> (match (uu____3994) with
| (m, uu____3998) -> begin
(FStar_Util.starts_with (Prims.strcat (FStar_Ident.text_of_lid m) ".") (Prims.strcat (FStar_Ident.text_of_lid ns) "."))
end))))
in (match (uu____3988) with
| true -> begin
((ns), (Open_namespace))
end
| uu____4001 -> begin
(

let uu____4002 = (

let uu____4003 = (

let uu____4006 = (FStar_Util.format1 "Namespace %s cannot be found" (FStar_Ident.text_of_lid ns))
in ((uu____4006), ((FStar_Ident.range_of_lid ns))))
in FStar_Errors.Error (uu____4003))
in (FStar_Pervasives.raise uu____4002))
end)))
end
| FStar_Pervasives_Native.Some (ns') -> begin
((fail_if_curmodule env ns ns');
((ns'), (Open_module));
)
end))
in (match (uu____3977) with
| (ns', kd) -> begin
(push_scope_mod env (Open_module_or_namespace (((ns'), (kd)))))
end)))


let push_include : env  ->  FStar_Ident.lident  ->  env = (fun env ns -> (

let ns0 = ns
in (

let uu____4020 = (resolve_module_name env ns false)
in (match (uu____4020) with
| FStar_Pervasives_Native.Some (ns1) -> begin
((fail_if_curmodule env ns0 ns1);
(

let env1 = (push_scope_mod env (Open_module_or_namespace (((ns1), (Open_module)))))
in (

let curmod = (

let uu____4026 = (current_module env1)
in uu____4026.FStar_Ident.str)
in ((

let uu____4028 = (FStar_Util.smap_try_find env1.includes curmod)
in (match (uu____4028) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (incl) -> begin
(

let uu____4041 = (

let uu____4043 = (FStar_ST.read incl)
in (ns1)::uu____4043)
in (FStar_ST.write incl uu____4041))
end));
(match (()) with
| () -> begin
(

let uu____4051 = (get_trans_exported_id_set env1 ns1.FStar_Ident.str)
in (match (uu____4051) with
| FStar_Pervasives_Native.Some (ns_trans_exports) -> begin
((

let uu____4064 = (

let uu____4075 = (get_exported_id_set env1 curmod)
in (

let uu____4080 = (get_trans_exported_id_set env1 curmod)
in ((uu____4075), (uu____4080))))
in (match (uu____4064) with
| (FStar_Pervasives_Native.Some (cur_exports), FStar_Pervasives_Native.Some (cur_trans_exports)) -> begin
(

let update_exports = (fun k -> (

let ns_ex = (

let uu____4120 = (ns_trans_exports k)
in (FStar_ST.read uu____4120))
in (

let ex = (cur_exports k)
in ((

let uu____4129 = (

let uu____4130 = (FStar_ST.read ex)
in (FStar_Util.set_difference uu____4130 ns_ex))
in (FStar_ST.write ex uu____4129));
(match (()) with
| () -> begin
(

let trans_ex = (cur_trans_exports k)
in (

let uu____4140 = (

let uu____4141 = (FStar_ST.read trans_ex)
in (FStar_Util.set_union uu____4141 ns_ex))
in (FStar_ST.write trans_ex uu____4140)))
end);
))))
in (FStar_List.iter update_exports all_exported_id_kinds))
end
| uu____4147 -> begin
()
end));
(match (()) with
| () -> begin
env1
end);
)
end
| FStar_Pervasives_Native.None -> begin
(

let uu____4161 = (

let uu____4162 = (

let uu____4165 = (FStar_Util.format1 "include: Module %s was not prepared" ns1.FStar_Ident.str)
in ((uu____4165), ((FStar_Ident.range_of_lid ns1))))
in FStar_Errors.Error (uu____4162))
in (FStar_Pervasives.raise uu____4161))
end))
end);
)));
)
end
| uu____4166 -> begin
(

let uu____4168 = (

let uu____4169 = (

let uu____4172 = (FStar_Util.format1 "include: Module %s cannot be found" ns.FStar_Ident.str)
in ((uu____4172), ((FStar_Ident.range_of_lid ns))))
in FStar_Errors.Error (uu____4169))
in (FStar_Pervasives.raise uu____4168))
end))))


let push_module_abbrev : env  ->  FStar_Ident.ident  ->  FStar_Ident.lident  ->  env = (fun env x l -> (

let uu____4182 = (module_is_defined env l)
in (match (uu____4182) with
| true -> begin
((fail_if_curmodule env l l);
(push_scope_mod env (Module_abbrev (((x), (l)))));
)
end
| uu____4184 -> begin
(

let uu____4185 = (

let uu____4186 = (

let uu____4189 = (FStar_Util.format1 "Module %s cannot be found" (FStar_Ident.text_of_lid l))
in ((uu____4189), ((FStar_Ident.range_of_lid l))))
in FStar_Errors.Error (uu____4186))
in (FStar_Pervasives.raise uu____4185))
end)))


let push_doc : env  ->  FStar_Ident.lident  ->  FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option  ->  env = (fun env l doc_opt -> (match (doc_opt) with
| FStar_Pervasives_Native.None -> begin
env
end
| FStar_Pervasives_Native.Some (doc1) -> begin
((

let uu____4203 = (FStar_Util.smap_try_find env.docs l.FStar_Ident.str)
in (match (uu____4203) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (old_doc) -> begin
(

let uu____4206 = (

let uu____4207 = (FStar_Ident.string_of_lid l)
in (

let uu____4208 = (FStar_Parser_AST.string_of_fsdoc old_doc)
in (

let uu____4209 = (FStar_Parser_AST.string_of_fsdoc doc1)
in (FStar_Util.format3 "Overwriting doc of %s; old doc was [%s]; new doc are [%s]" uu____4207 uu____4208 uu____4209))))
in (FStar_Errors.warn (FStar_Ident.range_of_lid l) uu____4206))
end));
(FStar_Util.smap_add env.docs l.FStar_Ident.str doc1);
env;
)
end))


let check_admits : env  ->  Prims.unit = (fun env -> (FStar_All.pipe_right env.sigaccum (FStar_List.iter (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_declare_typ (l, u, t) -> begin
(

let uu____4218 = (try_lookup_lid env l)
in (match (uu____4218) with
| FStar_Pervasives_Native.None -> begin
((

let uu____4225 = (

let uu____4226 = (FStar_Options.interactive ())
in (not (uu____4226)))
in (match (uu____4225) with
| true -> begin
(

let uu____4227 = (

let uu____4228 = (FStar_Range.string_of_range (FStar_Ident.range_of_lid l))
in (

let uu____4229 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format2 "%s: Warning: Admitting %s without a definition\n" uu____4228 uu____4229)))
in (FStar_Util.print_string uu____4227))
end
| uu____4230 -> begin
()
end));
(

let quals = (FStar_Syntax_Syntax.Assumption)::se.FStar_Syntax_Syntax.sigquals
in (FStar_Util.smap_add (sigmap env) l.FStar_Ident.str (((

let uu___188_4235 = se
in {FStar_Syntax_Syntax.sigel = uu___188_4235.FStar_Syntax_Syntax.sigel; FStar_Syntax_Syntax.sigrng = uu___188_4235.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = uu___188_4235.FStar_Syntax_Syntax.sigmeta})), (false))));
)
end
| FStar_Pervasives_Native.Some (uu____4236) -> begin
()
end))
end
| uu____4241 -> begin
()
end)))))


let finish : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env modul -> ((FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations (FStar_List.iter (fun se -> (

let quals = se.FStar_Syntax_Syntax.sigquals
in (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____4253) -> begin
(match (((FStar_List.contains FStar_Syntax_Syntax.Private quals) || (FStar_List.contains FStar_Syntax_Syntax.Abstract quals))) with
| true -> begin
(FStar_All.pipe_right ses (FStar_List.iter (fun se1 -> (match (se1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (lid, uu____4261, uu____4262, uu____4263, uu____4264, uu____4265) -> begin
(FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str)
end
| uu____4270 -> begin
()
end))))
end
| uu____4271 -> begin
()
end)
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____4273, uu____4274) -> begin
(match ((FStar_List.contains FStar_Syntax_Syntax.Private quals)) with
| true -> begin
(FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str)
end
| uu____4277 -> begin
()
end)
end
| FStar_Syntax_Syntax.Sig_let ((uu____4278, lbs), uu____4280, uu____4281) -> begin
((match (((FStar_List.contains FStar_Syntax_Syntax.Private quals) || (FStar_List.contains FStar_Syntax_Syntax.Abstract quals))) with
| true -> begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (

let uu____4294 = (

let uu____4295 = (

let uu____4296 = (

let uu____4301 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in uu____4301.FStar_Syntax_Syntax.fv_name)
in uu____4296.FStar_Syntax_Syntax.v)
in uu____4295.FStar_Ident.str)
in (FStar_Util.smap_remove (sigmap env) uu____4294)))))
end
| uu____4307 -> begin
()
end);
(match (((FStar_List.contains FStar_Syntax_Syntax.Abstract quals) && (not ((FStar_List.contains FStar_Syntax_Syntax.Private quals))))) with
| true -> begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (

let lid = (

let uu____4311 = (

let uu____4316 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in uu____4316.FStar_Syntax_Syntax.fv_name)
in uu____4311.FStar_Syntax_Syntax.v)
in (

let quals1 = (FStar_Syntax_Syntax.Assumption)::quals
in (

let decl = (

let uu___189_4323 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp))); FStar_Syntax_Syntax.sigrng = uu___189_4323.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = uu___189_4323.FStar_Syntax_Syntax.sigmeta})
in (FStar_Util.smap_add (sigmap env) lid.FStar_Ident.str ((decl), (false)))))))))
end
| uu____4329 -> begin
()
end);
)
end
| uu____4330 -> begin
()
end)))));
(

let curmod = (

let uu____4332 = (current_module env)
in uu____4332.FStar_Ident.str)
in ((

let uu____4334 = (

let uu____4345 = (get_exported_id_set env curmod)
in (

let uu____4350 = (get_trans_exported_id_set env curmod)
in ((uu____4345), (uu____4350))))
in (match (uu____4334) with
| (FStar_Pervasives_Native.Some (cur_ex), FStar_Pervasives_Native.Some (cur_trans_ex)) -> begin
(

let update_exports = (fun eikind -> (

let cur_ex_set = (

let uu____4390 = (cur_ex eikind)
in (FStar_ST.read uu____4390))
in (

let cur_trans_ex_set_ref = (cur_trans_ex eikind)
in (

let uu____4398 = (

let uu____4399 = (FStar_ST.read cur_trans_ex_set_ref)
in (FStar_Util.set_union cur_ex_set uu____4399))
in (FStar_ST.write cur_trans_ex_set_ref uu____4398)))))
in (FStar_List.iter update_exports all_exported_id_kinds))
end
| uu____4405 -> begin
()
end));
(match (()) with
| () -> begin
((filter_record_cache ());
(match (()) with
| () -> begin
(

let uu___190_4417 = env
in {curmodule = FStar_Pervasives_Native.None; curmonad = uu___190_4417.curmonad; modules = (((modul.FStar_Syntax_Syntax.name), (modul)))::env.modules; scope_mods = []; exported_ids = uu___190_4417.exported_ids; trans_exported_ids = uu___190_4417.trans_exported_ids; includes = uu___190_4417.includes; sigaccum = []; sigmap = uu___190_4417.sigmap; iface = uu___190_4417.iface; admitted_iface = uu___190_4417.admitted_iface; expect_typ = uu___190_4417.expect_typ; docs = uu___190_4417.docs; remaining_iface_decls = uu___190_4417.remaining_iface_decls; syntax_only = uu___190_4417.syntax_only})
end);
)
end);
));
))


let stack : env Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let push : env  ->  env = (fun env -> ((push_record_cache ());
(

let uu____4430 = (

let uu____4432 = (FStar_ST.read stack)
in (env)::uu____4432)
in (FStar_ST.write stack uu____4430));
(

let uu___191_4440 = env
in (

let uu____4441 = (FStar_Util.smap_copy (sigmap env))
in (

let uu____4447 = (FStar_Util.smap_copy env.docs)
in {curmodule = uu___191_4440.curmodule; curmonad = uu___191_4440.curmonad; modules = uu___191_4440.modules; scope_mods = uu___191_4440.scope_mods; exported_ids = uu___191_4440.exported_ids; trans_exported_ids = uu___191_4440.trans_exported_ids; includes = uu___191_4440.includes; sigaccum = uu___191_4440.sigaccum; sigmap = uu____4441; iface = uu___191_4440.iface; admitted_iface = uu___191_4440.admitted_iface; expect_typ = uu___191_4440.expect_typ; docs = uu____4447; remaining_iface_decls = uu___191_4440.remaining_iface_decls; syntax_only = uu___191_4440.syntax_only})));
))


let pop : Prims.unit  ->  env = (fun uu____4451 -> (

let uu____4452 = (FStar_ST.read stack)
in (match (uu____4452) with
| (env)::tl1 -> begin
((pop_record_cache ());
(FStar_ST.write stack tl1);
env;
)
end
| uu____4465 -> begin
(failwith "Impossible: Too many pops")
end)))


let commit_mark : env  ->  env = (fun env -> ((commit_record_cache ());
(

let uu____4471 = (FStar_ST.read stack)
in (match (uu____4471) with
| (uu____4476)::tl1 -> begin
((FStar_ST.write stack tl1);
env;
)
end
| uu____4483 -> begin
(failwith "Impossible: Too many pops")
end));
))


let mark : env  ->  env = (fun x -> (push x))


let reset_mark : Prims.unit  ->  env = (fun uu____4490 -> (pop ()))


let export_interface : FStar_Ident.lident  ->  env  ->  env = (fun m env -> (

let sigelt_in_m = (fun se -> (match ((FStar_Syntax_Util.lids_of_sigelt se)) with
| (l)::uu____4502 -> begin
(l.FStar_Ident.nsstr = m.FStar_Ident.str)
end
| uu____4504 -> begin
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

let uu____4522 = (FStar_Util.smap_try_find sm' k)
in (match (uu____4522) with
| FStar_Pervasives_Native.Some (se, true) when (sigelt_in_m se) -> begin
((FStar_Util.smap_remove sm' k);
(

let se1 = (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_declare_typ (l, u, t) -> begin
(

let uu___192_4538 = se
in {FStar_Syntax_Syntax.sigel = uu___192_4538.FStar_Syntax_Syntax.sigel; FStar_Syntax_Syntax.sigrng = uu___192_4538.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Assumption)::se.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___192_4538.FStar_Syntax_Syntax.sigmeta})
end
| uu____4539 -> begin
se
end)
in (FStar_Util.smap_add sm' k ((se1), (false))));
)
end
| uu____4542 -> begin
()
end)))));
env1;
)))))))


let finish_module_or_interface : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env modul -> ((match ((not (modul.FStar_Syntax_Syntax.is_interface))) with
| true -> begin
(check_admits env)
end
| uu____4553 -> begin
()
end);
(finish env modul);
))


let prepare_module_or_interface : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  (env * Prims.bool) = (fun intf admitted env mname -> (

let prep = (fun env1 -> (

let filename = (FStar_Util.strcat (FStar_Ident.text_of_lid mname) ".fst")
in (

let auto_open = (FStar_Parser_Dep.hard_coded_dependencies filename)
in (

let auto_open1 = (

let convert_kind = (fun uu___173_4584 -> (match (uu___173_4584) with
| FStar_Parser_Dep.Open_namespace -> begin
Open_namespace
end
| FStar_Parser_Dep.Open_module -> begin
Open_module
end))
in (FStar_List.map (fun uu____4589 -> (match (uu____4589) with
| (lid, kind) -> begin
((lid), ((convert_kind kind)))
end)) auto_open))
in (

let namespace_of_module = (match (((FStar_List.length mname.FStar_Ident.ns) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____4606 = (

let uu____4609 = (FStar_Ident.lid_of_ids mname.FStar_Ident.ns)
in ((uu____4609), (Open_namespace)))
in (uu____4606)::[])
end
| uu____4614 -> begin
[]
end)
in (

let auto_open2 = (FStar_List.rev (FStar_List.append auto_open1 namespace_of_module))
in ((

let uu____4626 = (exported_id_set_new ())
in (FStar_Util.smap_add env1.exported_ids mname.FStar_Ident.str uu____4626));
(match (()) with
| () -> begin
((

let uu____4631 = (exported_id_set_new ())
in (FStar_Util.smap_add env1.trans_exported_ids mname.FStar_Ident.str uu____4631));
(match (()) with
| () -> begin
((

let uu____4636 = (FStar_Util.mk_ref [])
in (FStar_Util.smap_add env1.includes mname.FStar_Ident.str uu____4636));
(match (()) with
| () -> begin
(

let uu___193_4645 = env1
in (

let uu____4646 = (FStar_List.map (fun x -> Open_module_or_namespace (x)) auto_open2)
in {curmodule = FStar_Pervasives_Native.Some (mname); curmonad = uu___193_4645.curmonad; modules = uu___193_4645.modules; scope_mods = uu____4646; exported_ids = uu___193_4645.exported_ids; trans_exported_ids = uu___193_4645.trans_exported_ids; includes = uu___193_4645.includes; sigaccum = uu___193_4645.sigaccum; sigmap = env1.sigmap; iface = intf; admitted_iface = admitted; expect_typ = uu___193_4645.expect_typ; docs = uu___193_4645.docs; remaining_iface_decls = uu___193_4645.remaining_iface_decls; syntax_only = uu___193_4645.syntax_only}))
end);
)
end);
)
end);
)))))))
in (

let uu____4649 = (FStar_All.pipe_right env.modules (FStar_Util.find_opt (fun uu____4661 -> (match (uu____4661) with
| (l, uu____4665) -> begin
(FStar_Ident.lid_equals l mname)
end))))
in (match (uu____4649) with
| FStar_Pervasives_Native.None -> begin
(

let uu____4670 = (prep env)
in ((uu____4670), (false)))
end
| FStar_Pervasives_Native.Some (uu____4671, m) -> begin
((

let uu____4676 = ((

let uu____4677 = (FStar_Options.interactive ())
in (not (uu____4677))) && ((not (m.FStar_Syntax_Syntax.is_interface)) || intf))
in (match (uu____4676) with
| true -> begin
(

let uu____4678 = (

let uu____4679 = (

let uu____4682 = (FStar_Util.format1 "Duplicate module or interface name: %s" mname.FStar_Ident.str)
in ((uu____4682), ((FStar_Ident.range_of_lid mname))))
in FStar_Errors.Error (uu____4679))
in (FStar_Pervasives.raise uu____4678))
end
| uu____4683 -> begin
()
end));
(

let uu____4684 = (

let uu____4685 = (push env)
in (prep uu____4685))
in ((uu____4684), (true)));
)
end))))


let enter_monad_scope : env  ->  FStar_Ident.ident  ->  env = (fun env mname -> (match (env.curmonad) with
| FStar_Pervasives_Native.Some (mname') -> begin
(FStar_Pervasives.raise (FStar_Errors.Error ((((Prims.strcat "Trying to define monad " (Prims.strcat mname.FStar_Ident.idText (Prims.strcat ", but already in monad scope " mname'.FStar_Ident.idText)))), (mname.FStar_Ident.idRange)))))
end
| FStar_Pervasives_Native.None -> begin
(

let uu___194_4693 = env
in {curmodule = uu___194_4693.curmodule; curmonad = FStar_Pervasives_Native.Some (mname); modules = uu___194_4693.modules; scope_mods = uu___194_4693.scope_mods; exported_ids = uu___194_4693.exported_ids; trans_exported_ids = uu___194_4693.trans_exported_ids; includes = uu___194_4693.includes; sigaccum = uu___194_4693.sigaccum; sigmap = uu___194_4693.sigmap; iface = uu___194_4693.iface; admitted_iface = uu___194_4693.admitted_iface; expect_typ = uu___194_4693.expect_typ; docs = uu___194_4693.docs; remaining_iface_decls = uu___194_4693.remaining_iface_decls; syntax_only = uu___194_4693.syntax_only})
end))


let fail_or = (fun env lookup lid -> (

let uu____4718 = (lookup lid)
in (match (uu____4718) with
| FStar_Pervasives_Native.None -> begin
(

let opened_modules = (FStar_List.map (fun uu____4724 -> (match (uu____4724) with
| (lid1, uu____4728) -> begin
(FStar_Ident.text_of_lid lid1)
end)) env.modules)
in (

let msg = (FStar_Util.format1 "Identifier not found: [%s]" (FStar_Ident.text_of_lid lid))
in (

let msg1 = (match (((FStar_List.length lid.FStar_Ident.ns) = (Prims.parse_int "0"))) with
| true -> begin
msg
end
| uu____4733 -> begin
(

let modul = (

let uu____4735 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in (FStar_Ident.set_lid_range uu____4735 (FStar_Ident.range_of_lid lid)))
in (

let uu____4736 = (resolve_module_name env modul true)
in (match (uu____4736) with
| FStar_Pervasives_Native.None -> begin
(

let opened_modules1 = (FStar_String.concat ", " opened_modules)
in (FStar_Util.format3 "%s\nModule %s does not belong to the list of modules in scope, namely %s" msg modul.FStar_Ident.str opened_modules1))
end
| FStar_Pervasives_Native.Some (modul') when (not ((FStar_List.existsb (fun m -> (m = modul'.FStar_Ident.str)) opened_modules))) -> begin
(

let opened_modules1 = (FStar_String.concat ", " opened_modules)
in (FStar_Util.format4 "%s\nModule %s resolved into %s, which does not belong to the list of modules in scope, namely %s" msg modul.FStar_Ident.str modul'.FStar_Ident.str opened_modules1))
end
| FStar_Pervasives_Native.Some (modul') -> begin
(FStar_Util.format4 "%s\nModule %s resolved into %s, definition %s not found" msg modul.FStar_Ident.str modul'.FStar_Ident.str lid.FStar_Ident.ident.FStar_Ident.idText)
end)))
end)
in (FStar_Pervasives.raise (FStar_Errors.Error (((msg1), ((FStar_Ident.range_of_lid lid)))))))))
end
| FStar_Pervasives_Native.Some (r) -> begin
r
end)))


let fail_or2 = (fun lookup id -> (

let uu____4763 = (lookup id)
in (match (uu____4763) with
| FStar_Pervasives_Native.None -> begin
(FStar_Pervasives.raise (FStar_Errors.Error ((((Prims.strcat "Identifier not found [" (Prims.strcat id.FStar_Ident.idText "]"))), (id.FStar_Ident.idRange)))))
end
| FStar_Pervasives_Native.Some (r) -> begin
r
end)))




