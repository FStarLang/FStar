
open Prims
open FStar_Pervasives

type used_marker =
Prims.bool FStar_ST.ref


type local_binding =
(FStar_Ident.ident * FStar_Syntax_Syntax.bv * used_marker)


type rec_binding =
(FStar_Ident.ident * FStar_Ident.lid * FStar_Syntax_Syntax.delta_depth * used_marker)


type module_abbrev =
(FStar_Ident.ident * FStar_Ident.lident)

type open_kind =
| Open_module
| Open_namespace


let uu___is_Open_module : open_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Open_module -> begin
true
end
| uu____60 -> begin
false
end))


let uu___is_Open_namespace : open_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Open_namespace -> begin
true
end
| uu____71 -> begin
false
end))


type open_module_or_namespace =
(FStar_Ident.lident * open_kind)

type record_or_dc =
{typename : FStar_Ident.lident; constrname : FStar_Ident.ident; parms : FStar_Syntax_Syntax.binders; fields : (FStar_Ident.ident * FStar_Syntax_Syntax.typ) Prims.list; is_private_or_abstract : Prims.bool; is_record : Prims.bool}


let __proj__Mkrecord_or_dc__item__typename : record_or_dc  ->  FStar_Ident.lident = (fun projectee -> (match (projectee) with
| {typename = typename; constrname = constrname; parms = parms; fields = fields; is_private_or_abstract = is_private_or_abstract; is_record = is_record} -> begin
typename
end))


let __proj__Mkrecord_or_dc__item__constrname : record_or_dc  ->  FStar_Ident.ident = (fun projectee -> (match (projectee) with
| {typename = typename; constrname = constrname; parms = parms; fields = fields; is_private_or_abstract = is_private_or_abstract; is_record = is_record} -> begin
constrname
end))


let __proj__Mkrecord_or_dc__item__parms : record_or_dc  ->  FStar_Syntax_Syntax.binders = (fun projectee -> (match (projectee) with
| {typename = typename; constrname = constrname; parms = parms; fields = fields; is_private_or_abstract = is_private_or_abstract; is_record = is_record} -> begin
parms
end))


let __proj__Mkrecord_or_dc__item__fields : record_or_dc  ->  (FStar_Ident.ident * FStar_Syntax_Syntax.typ) Prims.list = (fun projectee -> (match (projectee) with
| {typename = typename; constrname = constrname; parms = parms; fields = fields; is_private_or_abstract = is_private_or_abstract; is_record = is_record} -> begin
fields
end))


let __proj__Mkrecord_or_dc__item__is_private_or_abstract : record_or_dc  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {typename = typename; constrname = constrname; parms = parms; fields = fields; is_private_or_abstract = is_private_or_abstract; is_record = is_record} -> begin
is_private_or_abstract
end))


let __proj__Mkrecord_or_dc__item__is_record : record_or_dc  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {typename = typename; constrname = constrname; parms = parms; fields = fields; is_private_or_abstract = is_private_or_abstract; is_record = is_record} -> begin
is_record
end))

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
| uu____311 -> begin
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
| uu____330 -> begin
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
| uu____349 -> begin
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
| uu____368 -> begin
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
| uu____387 -> begin
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
| uu____406 -> begin
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
| uu____427 -> begin
false
end))


let uu___is_Exported_id_field : exported_id_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Exported_id_field -> begin
true
end
| uu____438 -> begin
false
end))


type exported_id_set =
exported_id_kind  ->  string_set FStar_ST.ref

type env =
{curmodule : FStar_Ident.lident FStar_Pervasives_Native.option; curmonad : FStar_Ident.ident FStar_Pervasives_Native.option; modules : (FStar_Ident.lident * FStar_Syntax_Syntax.modul) Prims.list; scope_mods : scope_mod Prims.list; exported_ids : exported_id_set FStar_Util.smap; trans_exported_ids : exported_id_set FStar_Util.smap; includes : FStar_Ident.lident Prims.list FStar_ST.ref FStar_Util.smap; sigaccum : FStar_Syntax_Syntax.sigelts; sigmap : (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap; iface : Prims.bool; admitted_iface : Prims.bool; expect_typ : Prims.bool; docs : FStar_Parser_AST.fsdoc FStar_Util.smap; remaining_iface_decls : (FStar_Ident.lident * FStar_Parser_AST.decl Prims.list) Prims.list; syntax_only : Prims.bool; ds_hooks : dsenv_hooks; dep_graph : FStar_Parser_Dep.deps} 
 and dsenv_hooks =
{ds_push_open_hook : env  ->  open_module_or_namespace  ->  unit; ds_push_include_hook : env  ->  FStar_Ident.lident  ->  unit; ds_push_module_abbrev_hook : env  ->  FStar_Ident.ident  ->  FStar_Ident.lident  ->  unit}


let __proj__Mkenv__item__curmodule : env  ->  FStar_Ident.lident FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {curmodule = curmodule; curmonad = curmonad; modules = modules; scope_mods = scope_mods; exported_ids = exported_ids; trans_exported_ids = trans_exported_ids; includes = includes; sigaccum = sigaccum; sigmap = sigmap; iface = iface; admitted_iface = admitted_iface; expect_typ = expect_typ; docs = docs; remaining_iface_decls = remaining_iface_decls; syntax_only = syntax_only; ds_hooks = ds_hooks; dep_graph = dep_graph} -> begin
curmodule
end))


let __proj__Mkenv__item__curmonad : env  ->  FStar_Ident.ident FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {curmodule = curmodule; curmonad = curmonad; modules = modules; scope_mods = scope_mods; exported_ids = exported_ids; trans_exported_ids = trans_exported_ids; includes = includes; sigaccum = sigaccum; sigmap = sigmap; iface = iface; admitted_iface = admitted_iface; expect_typ = expect_typ; docs = docs; remaining_iface_decls = remaining_iface_decls; syntax_only = syntax_only; ds_hooks = ds_hooks; dep_graph = dep_graph} -> begin
curmonad
end))


let __proj__Mkenv__item__modules : env  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.modul) Prims.list = (fun projectee -> (match (projectee) with
| {curmodule = curmodule; curmonad = curmonad; modules = modules; scope_mods = scope_mods; exported_ids = exported_ids; trans_exported_ids = trans_exported_ids; includes = includes; sigaccum = sigaccum; sigmap = sigmap; iface = iface; admitted_iface = admitted_iface; expect_typ = expect_typ; docs = docs; remaining_iface_decls = remaining_iface_decls; syntax_only = syntax_only; ds_hooks = ds_hooks; dep_graph = dep_graph} -> begin
modules
end))


let __proj__Mkenv__item__scope_mods : env  ->  scope_mod Prims.list = (fun projectee -> (match (projectee) with
| {curmodule = curmodule; curmonad = curmonad; modules = modules; scope_mods = scope_mods; exported_ids = exported_ids; trans_exported_ids = trans_exported_ids; includes = includes; sigaccum = sigaccum; sigmap = sigmap; iface = iface; admitted_iface = admitted_iface; expect_typ = expect_typ; docs = docs; remaining_iface_decls = remaining_iface_decls; syntax_only = syntax_only; ds_hooks = ds_hooks; dep_graph = dep_graph} -> begin
scope_mods
end))


let __proj__Mkenv__item__exported_ids : env  ->  exported_id_set FStar_Util.smap = (fun projectee -> (match (projectee) with
| {curmodule = curmodule; curmonad = curmonad; modules = modules; scope_mods = scope_mods; exported_ids = exported_ids; trans_exported_ids = trans_exported_ids; includes = includes; sigaccum = sigaccum; sigmap = sigmap; iface = iface; admitted_iface = admitted_iface; expect_typ = expect_typ; docs = docs; remaining_iface_decls = remaining_iface_decls; syntax_only = syntax_only; ds_hooks = ds_hooks; dep_graph = dep_graph} -> begin
exported_ids
end))


let __proj__Mkenv__item__trans_exported_ids : env  ->  exported_id_set FStar_Util.smap = (fun projectee -> (match (projectee) with
| {curmodule = curmodule; curmonad = curmonad; modules = modules; scope_mods = scope_mods; exported_ids = exported_ids; trans_exported_ids = trans_exported_ids; includes = includes; sigaccum = sigaccum; sigmap = sigmap; iface = iface; admitted_iface = admitted_iface; expect_typ = expect_typ; docs = docs; remaining_iface_decls = remaining_iface_decls; syntax_only = syntax_only; ds_hooks = ds_hooks; dep_graph = dep_graph} -> begin
trans_exported_ids
end))


let __proj__Mkenv__item__includes : env  ->  FStar_Ident.lident Prims.list FStar_ST.ref FStar_Util.smap = (fun projectee -> (match (projectee) with
| {curmodule = curmodule; curmonad = curmonad; modules = modules; scope_mods = scope_mods; exported_ids = exported_ids; trans_exported_ids = trans_exported_ids; includes = includes; sigaccum = sigaccum; sigmap = sigmap; iface = iface; admitted_iface = admitted_iface; expect_typ = expect_typ; docs = docs; remaining_iface_decls = remaining_iface_decls; syntax_only = syntax_only; ds_hooks = ds_hooks; dep_graph = dep_graph} -> begin
includes
end))


let __proj__Mkenv__item__sigaccum : env  ->  FStar_Syntax_Syntax.sigelts = (fun projectee -> (match (projectee) with
| {curmodule = curmodule; curmonad = curmonad; modules = modules; scope_mods = scope_mods; exported_ids = exported_ids; trans_exported_ids = trans_exported_ids; includes = includes; sigaccum = sigaccum; sigmap = sigmap; iface = iface; admitted_iface = admitted_iface; expect_typ = expect_typ; docs = docs; remaining_iface_decls = remaining_iface_decls; syntax_only = syntax_only; ds_hooks = ds_hooks; dep_graph = dep_graph} -> begin
sigaccum
end))


let __proj__Mkenv__item__sigmap : env  ->  (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap = (fun projectee -> (match (projectee) with
| {curmodule = curmodule; curmonad = curmonad; modules = modules; scope_mods = scope_mods; exported_ids = exported_ids; trans_exported_ids = trans_exported_ids; includes = includes; sigaccum = sigaccum; sigmap = sigmap; iface = iface; admitted_iface = admitted_iface; expect_typ = expect_typ; docs = docs; remaining_iface_decls = remaining_iface_decls; syntax_only = syntax_only; ds_hooks = ds_hooks; dep_graph = dep_graph} -> begin
sigmap
end))


let __proj__Mkenv__item__iface : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {curmodule = curmodule; curmonad = curmonad; modules = modules; scope_mods = scope_mods; exported_ids = exported_ids; trans_exported_ids = trans_exported_ids; includes = includes; sigaccum = sigaccum; sigmap = sigmap; iface = iface; admitted_iface = admitted_iface; expect_typ = expect_typ; docs = docs; remaining_iface_decls = remaining_iface_decls; syntax_only = syntax_only; ds_hooks = ds_hooks; dep_graph = dep_graph} -> begin
iface
end))


let __proj__Mkenv__item__admitted_iface : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {curmodule = curmodule; curmonad = curmonad; modules = modules; scope_mods = scope_mods; exported_ids = exported_ids; trans_exported_ids = trans_exported_ids; includes = includes; sigaccum = sigaccum; sigmap = sigmap; iface = iface; admitted_iface = admitted_iface; expect_typ = expect_typ; docs = docs; remaining_iface_decls = remaining_iface_decls; syntax_only = syntax_only; ds_hooks = ds_hooks; dep_graph = dep_graph} -> begin
admitted_iface
end))


let __proj__Mkenv__item__expect_typ : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {curmodule = curmodule; curmonad = curmonad; modules = modules; scope_mods = scope_mods; exported_ids = exported_ids; trans_exported_ids = trans_exported_ids; includes = includes; sigaccum = sigaccum; sigmap = sigmap; iface = iface; admitted_iface = admitted_iface; expect_typ = expect_typ; docs = docs; remaining_iface_decls = remaining_iface_decls; syntax_only = syntax_only; ds_hooks = ds_hooks; dep_graph = dep_graph} -> begin
expect_typ
end))


let __proj__Mkenv__item__docs : env  ->  FStar_Parser_AST.fsdoc FStar_Util.smap = (fun projectee -> (match (projectee) with
| {curmodule = curmodule; curmonad = curmonad; modules = modules; scope_mods = scope_mods; exported_ids = exported_ids; trans_exported_ids = trans_exported_ids; includes = includes; sigaccum = sigaccum; sigmap = sigmap; iface = iface; admitted_iface = admitted_iface; expect_typ = expect_typ; docs = docs; remaining_iface_decls = remaining_iface_decls; syntax_only = syntax_only; ds_hooks = ds_hooks; dep_graph = dep_graph} -> begin
docs
end))


let __proj__Mkenv__item__remaining_iface_decls : env  ->  (FStar_Ident.lident * FStar_Parser_AST.decl Prims.list) Prims.list = (fun projectee -> (match (projectee) with
| {curmodule = curmodule; curmonad = curmonad; modules = modules; scope_mods = scope_mods; exported_ids = exported_ids; trans_exported_ids = trans_exported_ids; includes = includes; sigaccum = sigaccum; sigmap = sigmap; iface = iface; admitted_iface = admitted_iface; expect_typ = expect_typ; docs = docs; remaining_iface_decls = remaining_iface_decls; syntax_only = syntax_only; ds_hooks = ds_hooks; dep_graph = dep_graph} -> begin
remaining_iface_decls
end))


let __proj__Mkenv__item__syntax_only : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {curmodule = curmodule; curmonad = curmonad; modules = modules; scope_mods = scope_mods; exported_ids = exported_ids; trans_exported_ids = trans_exported_ids; includes = includes; sigaccum = sigaccum; sigmap = sigmap; iface = iface; admitted_iface = admitted_iface; expect_typ = expect_typ; docs = docs; remaining_iface_decls = remaining_iface_decls; syntax_only = syntax_only; ds_hooks = ds_hooks; dep_graph = dep_graph} -> begin
syntax_only
end))


let __proj__Mkenv__item__ds_hooks : env  ->  dsenv_hooks = (fun projectee -> (match (projectee) with
| {curmodule = curmodule; curmonad = curmonad; modules = modules; scope_mods = scope_mods; exported_ids = exported_ids; trans_exported_ids = trans_exported_ids; includes = includes; sigaccum = sigaccum; sigmap = sigmap; iface = iface; admitted_iface = admitted_iface; expect_typ = expect_typ; docs = docs; remaining_iface_decls = remaining_iface_decls; syntax_only = syntax_only; ds_hooks = ds_hooks; dep_graph = dep_graph} -> begin
ds_hooks
end))


let __proj__Mkenv__item__dep_graph : env  ->  FStar_Parser_Dep.deps = (fun projectee -> (match (projectee) with
| {curmodule = curmodule; curmonad = curmonad; modules = modules; scope_mods = scope_mods; exported_ids = exported_ids; trans_exported_ids = trans_exported_ids; includes = includes; sigaccum = sigaccum; sigmap = sigmap; iface = iface; admitted_iface = admitted_iface; expect_typ = expect_typ; docs = docs; remaining_iface_decls = remaining_iface_decls; syntax_only = syntax_only; ds_hooks = ds_hooks; dep_graph = dep_graph} -> begin
dep_graph
end))


let __proj__Mkdsenv_hooks__item__ds_push_open_hook : dsenv_hooks  ->  env  ->  open_module_or_namespace  ->  unit = (fun projectee -> (match (projectee) with
| {ds_push_open_hook = ds_push_open_hook; ds_push_include_hook = ds_push_include_hook; ds_push_module_abbrev_hook = ds_push_module_abbrev_hook} -> begin
ds_push_open_hook
end))


let __proj__Mkdsenv_hooks__item__ds_push_include_hook : dsenv_hooks  ->  env  ->  FStar_Ident.lident  ->  unit = (fun projectee -> (match (projectee) with
| {ds_push_open_hook = ds_push_open_hook; ds_push_include_hook = ds_push_include_hook; ds_push_module_abbrev_hook = ds_push_module_abbrev_hook} -> begin
ds_push_include_hook
end))


let __proj__Mkdsenv_hooks__item__ds_push_module_abbrev_hook : dsenv_hooks  ->  env  ->  FStar_Ident.ident  ->  FStar_Ident.lident  ->  unit = (fun projectee -> (match (projectee) with
| {ds_push_open_hook = ds_push_open_hook; ds_push_include_hook = ds_push_include_hook; ds_push_module_abbrev_hook = ds_push_module_abbrev_hook} -> begin
ds_push_module_abbrev_hook
end))


type 'a withenv =
env  ->  ('a * env)


let default_ds_hooks : dsenv_hooks = {ds_push_open_hook = (fun uu____2058 uu____2059 -> ()); ds_push_include_hook = (fun uu____2062 uu____2063 -> ()); ds_push_module_abbrev_hook = (fun uu____2067 uu____2068 uu____2069 -> ())}

type foundname =
| Term_name of (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.attribute Prims.list)
| Eff_name of (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident)


let uu___is_Term_name : foundname  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Term_name (_0) -> begin
true
end
| uu____2106 -> begin
false
end))


let __proj__Term_name__item___0 : foundname  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.attribute Prims.list) = (fun projectee -> (match (projectee) with
| Term_name (_0) -> begin
_0
end))


let uu___is_Eff_name : foundname  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Eff_name (_0) -> begin
true
end
| uu____2147 -> begin
false
end))


let __proj__Eff_name__item___0 : foundname  ->  (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident) = (fun projectee -> (match (projectee) with
| Eff_name (_0) -> begin
_0
end))


let set_iface : env  ->  Prims.bool  ->  env = (fun env b -> (

let uu___129_2181 = env
in {curmodule = uu___129_2181.curmodule; curmonad = uu___129_2181.curmonad; modules = uu___129_2181.modules; scope_mods = uu___129_2181.scope_mods; exported_ids = uu___129_2181.exported_ids; trans_exported_ids = uu___129_2181.trans_exported_ids; includes = uu___129_2181.includes; sigaccum = uu___129_2181.sigaccum; sigmap = uu___129_2181.sigmap; iface = b; admitted_iface = uu___129_2181.admitted_iface; expect_typ = uu___129_2181.expect_typ; docs = uu___129_2181.docs; remaining_iface_decls = uu___129_2181.remaining_iface_decls; syntax_only = uu___129_2181.syntax_only; ds_hooks = uu___129_2181.ds_hooks; dep_graph = uu___129_2181.dep_graph}))


let iface : env  ->  Prims.bool = (fun e -> e.iface)


let set_admitted_iface : env  ->  Prims.bool  ->  env = (fun e b -> (

let uu___134_2202 = e
in {curmodule = uu___134_2202.curmodule; curmonad = uu___134_2202.curmonad; modules = uu___134_2202.modules; scope_mods = uu___134_2202.scope_mods; exported_ids = uu___134_2202.exported_ids; trans_exported_ids = uu___134_2202.trans_exported_ids; includes = uu___134_2202.includes; sigaccum = uu___134_2202.sigaccum; sigmap = uu___134_2202.sigmap; iface = uu___134_2202.iface; admitted_iface = b; expect_typ = uu___134_2202.expect_typ; docs = uu___134_2202.docs; remaining_iface_decls = uu___134_2202.remaining_iface_decls; syntax_only = uu___134_2202.syntax_only; ds_hooks = uu___134_2202.ds_hooks; dep_graph = uu___134_2202.dep_graph}))


let admitted_iface : env  ->  Prims.bool = (fun e -> e.admitted_iface)


let set_expect_typ : env  ->  Prims.bool  ->  env = (fun e b -> (

let uu___139_2223 = e
in {curmodule = uu___139_2223.curmodule; curmonad = uu___139_2223.curmonad; modules = uu___139_2223.modules; scope_mods = uu___139_2223.scope_mods; exported_ids = uu___139_2223.exported_ids; trans_exported_ids = uu___139_2223.trans_exported_ids; includes = uu___139_2223.includes; sigaccum = uu___139_2223.sigaccum; sigmap = uu___139_2223.sigmap; iface = uu___139_2223.iface; admitted_iface = uu___139_2223.admitted_iface; expect_typ = b; docs = uu___139_2223.docs; remaining_iface_decls = uu___139_2223.remaining_iface_decls; syntax_only = uu___139_2223.syntax_only; ds_hooks = uu___139_2223.ds_hooks; dep_graph = uu___139_2223.dep_graph}))


let expect_typ : env  ->  Prims.bool = (fun e -> e.expect_typ)


let all_exported_id_kinds : exported_id_kind Prims.list = (Exported_id_field)::(Exported_id_term_type)::[]


let transitive_exported_ids : env  ->  FStar_Ident.lident  ->  Prims.string Prims.list = (fun env lid -> (

let module_name = (FStar_Ident.string_of_lid lid)
in (

let uu____2250 = (FStar_Util.smap_try_find env.trans_exported_ids module_name)
in (match (uu____2250) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (exported_id_set) -> begin
(

let uu____2263 = (

let uu____2267 = (exported_id_set Exported_id_term_type)
in (FStar_ST.op_Bang uu____2267))
in (FStar_All.pipe_right uu____2263 FStar_Util.set_elements))
end))))


let open_modules : env  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.modul) Prims.list = (fun e -> e.modules)


let open_modules_and_namespaces : env  ->  FStar_Ident.lident Prims.list = (fun env -> (FStar_List.filter_map (fun uu___0_2355 -> (match (uu___0_2355) with
| Open_module_or_namespace (lid, _info) -> begin
FStar_Pervasives_Native.Some (lid)
end
| uu____2360 -> begin
FStar_Pervasives_Native.None
end)) env.scope_mods))


let set_current_module : env  ->  FStar_Ident.lident  ->  env = (fun e l -> (

let uu___158_2372 = e
in {curmodule = FStar_Pervasives_Native.Some (l); curmonad = uu___158_2372.curmonad; modules = uu___158_2372.modules; scope_mods = uu___158_2372.scope_mods; exported_ids = uu___158_2372.exported_ids; trans_exported_ids = uu___158_2372.trans_exported_ids; includes = uu___158_2372.includes; sigaccum = uu___158_2372.sigaccum; sigmap = uu___158_2372.sigmap; iface = uu___158_2372.iface; admitted_iface = uu___158_2372.admitted_iface; expect_typ = uu___158_2372.expect_typ; docs = uu___158_2372.docs; remaining_iface_decls = uu___158_2372.remaining_iface_decls; syntax_only = uu___158_2372.syntax_only; ds_hooks = uu___158_2372.ds_hooks; dep_graph = uu___158_2372.dep_graph}))


let current_module : env  ->  FStar_Ident.lident = (fun env -> (match (env.curmodule) with
| FStar_Pervasives_Native.None -> begin
(failwith "Unset current module")
end
| FStar_Pervasives_Native.Some (m) -> begin
m
end))


let iface_decls : env  ->  FStar_Ident.lident  ->  FStar_Parser_AST.decl Prims.list FStar_Pervasives_Native.option = (fun env l -> (

let uu____2396 = (FStar_All.pipe_right env.remaining_iface_decls (FStar_List.tryFind (fun uu____2430 -> (match (uu____2430) with
| (m, uu____2439) -> begin
(FStar_Ident.lid_equals l m)
end))))
in (match (uu____2396) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (uu____2456, decls) -> begin
FStar_Pervasives_Native.Some (decls)
end)))


let set_iface_decls : env  ->  FStar_Ident.lident  ->  FStar_Parser_AST.decl Prims.list  ->  env = (fun env l ds -> (

let uu____2490 = (FStar_List.partition (fun uu____2520 -> (match (uu____2520) with
| (m, uu____2529) -> begin
(FStar_Ident.lid_equals l m)
end)) env.remaining_iface_decls)
in (match (uu____2490) with
| (uu____2534, rest) -> begin
(

let uu___183_2568 = env
in {curmodule = uu___183_2568.curmodule; curmonad = uu___183_2568.curmonad; modules = uu___183_2568.modules; scope_mods = uu___183_2568.scope_mods; exported_ids = uu___183_2568.exported_ids; trans_exported_ids = uu___183_2568.trans_exported_ids; includes = uu___183_2568.includes; sigaccum = uu___183_2568.sigaccum; sigmap = uu___183_2568.sigmap; iface = uu___183_2568.iface; admitted_iface = uu___183_2568.admitted_iface; expect_typ = uu___183_2568.expect_typ; docs = uu___183_2568.docs; remaining_iface_decls = (((l), (ds)))::rest; syntax_only = uu___183_2568.syntax_only; ds_hooks = uu___183_2568.ds_hooks; dep_graph = uu___183_2568.dep_graph})
end)))


let qual : FStar_Ident.lident  ->  FStar_Ident.ident  ->  FStar_Ident.lident = FStar_Syntax_Util.qual_id


let qualify : env  ->  FStar_Ident.ident  ->  FStar_Ident.lident = (fun env id1 -> (match (env.curmonad) with
| FStar_Pervasives_Native.None -> begin
(

let uu____2597 = (current_module env)
in (qual uu____2597 id1))
end
| FStar_Pervasives_Native.Some (monad) -> begin
(

let uu____2599 = (

let uu____2600 = (current_module env)
in (qual uu____2600 monad))
in (FStar_Syntax_Util.mk_field_projector_name_from_ident uu____2599 id1))
end))


let syntax_only : env  ->  Prims.bool = (fun env -> env.syntax_only)


let set_syntax_only : env  ->  Prims.bool  ->  env = (fun env b -> (

let uu___193_2621 = env
in {curmodule = uu___193_2621.curmodule; curmonad = uu___193_2621.curmonad; modules = uu___193_2621.modules; scope_mods = uu___193_2621.scope_mods; exported_ids = uu___193_2621.exported_ids; trans_exported_ids = uu___193_2621.trans_exported_ids; includes = uu___193_2621.includes; sigaccum = uu___193_2621.sigaccum; sigmap = uu___193_2621.sigmap; iface = uu___193_2621.iface; admitted_iface = uu___193_2621.admitted_iface; expect_typ = uu___193_2621.expect_typ; docs = uu___193_2621.docs; remaining_iface_decls = uu___193_2621.remaining_iface_decls; syntax_only = b; ds_hooks = uu___193_2621.ds_hooks; dep_graph = uu___193_2621.dep_graph}))


let ds_hooks : env  ->  dsenv_hooks = (fun env -> env.ds_hooks)


let set_ds_hooks : env  ->  dsenv_hooks  ->  env = (fun env hooks -> (

let uu___198_2639 = env
in {curmodule = uu___198_2639.curmodule; curmonad = uu___198_2639.curmonad; modules = uu___198_2639.modules; scope_mods = uu___198_2639.scope_mods; exported_ids = uu___198_2639.exported_ids; trans_exported_ids = uu___198_2639.trans_exported_ids; includes = uu___198_2639.includes; sigaccum = uu___198_2639.sigaccum; sigmap = uu___198_2639.sigmap; iface = uu___198_2639.iface; admitted_iface = uu___198_2639.admitted_iface; expect_typ = uu___198_2639.expect_typ; docs = uu___198_2639.docs; remaining_iface_decls = uu___198_2639.remaining_iface_decls; syntax_only = uu___198_2639.syntax_only; ds_hooks = hooks; dep_graph = uu___198_2639.dep_graph}))


let new_sigmap : 'Auu____2645 . unit  ->  'Auu____2645 FStar_Util.smap = (fun uu____2652 -> (FStar_Util.smap_create (Prims.parse_int "100")))


let empty_env : FStar_Parser_Dep.deps  ->  env = (fun deps -> (

let uu____2660 = (new_sigmap ())
in (

let uu____2665 = (new_sigmap ())
in (

let uu____2670 = (new_sigmap ())
in (

let uu____2681 = (new_sigmap ())
in (

let uu____2694 = (new_sigmap ())
in {curmodule = FStar_Pervasives_Native.None; curmonad = FStar_Pervasives_Native.None; modules = []; scope_mods = []; exported_ids = uu____2660; trans_exported_ids = uu____2665; includes = uu____2670; sigaccum = []; sigmap = uu____2681; iface = false; admitted_iface = false; expect_typ = false; docs = uu____2694; remaining_iface_decls = []; syntax_only = false; ds_hooks = default_ds_hooks; dep_graph = deps}))))))


let dep_graph : env  ->  FStar_Parser_Dep.deps = (fun env -> env.dep_graph)


let set_dep_graph : env  ->  FStar_Parser_Dep.deps  ->  env = (fun env ds -> (

let uu___205_2728 = env
in {curmodule = uu___205_2728.curmodule; curmonad = uu___205_2728.curmonad; modules = uu___205_2728.modules; scope_mods = uu___205_2728.scope_mods; exported_ids = uu___205_2728.exported_ids; trans_exported_ids = uu___205_2728.trans_exported_ids; includes = uu___205_2728.includes; sigaccum = uu___205_2728.sigaccum; sigmap = uu___205_2728.sigmap; iface = uu___205_2728.iface; admitted_iface = uu___205_2728.admitted_iface; expect_typ = uu___205_2728.expect_typ; docs = uu___205_2728.docs; remaining_iface_decls = uu___205_2728.remaining_iface_decls; syntax_only = uu___205_2728.syntax_only; ds_hooks = uu___205_2728.ds_hooks; dep_graph = ds}))


let sigmap : env  ->  (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap = (fun env -> env.sigmap)


let has_all_in_scope : env  ->  Prims.bool = (fun env -> (FStar_List.existsb (fun uu____2756 -> (match (uu____2756) with
| (m, uu____2763) -> begin
(FStar_Ident.lid_equals m FStar_Parser_Const.all_lid)
end)) env.modules))


let set_bv_range : FStar_Syntax_Syntax.bv  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.bv = (fun bv r -> (

let id1 = (

let uu___214_2776 = bv.FStar_Syntax_Syntax.ppname
in {FStar_Ident.idText = uu___214_2776.FStar_Ident.idText; FStar_Ident.idRange = r})
in (

let uu___217_2777 = bv
in {FStar_Syntax_Syntax.ppname = id1; FStar_Syntax_Syntax.index = uu___217_2777.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu___217_2777.FStar_Syntax_Syntax.sort})))


let bv_to_name : FStar_Syntax_Syntax.bv  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.term = (fun bv r -> (FStar_Syntax_Syntax.bv_to_name (set_bv_range bv r)))


let unmangleMap : (Prims.string * Prims.string * FStar_Syntax_Syntax.delta_depth * FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option) Prims.list = ((("op_ColonColon"), ("Cons"), (FStar_Syntax_Syntax.delta_constant), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor))))::((("not"), ("op_Negation"), (FStar_Syntax_Syntax.delta_equational), (FStar_Pervasives_Native.None)))::[]


let unmangleOpName : FStar_Ident.ident  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun id1 -> (FStar_Util.find_map unmangleMap (fun uu____2880 -> (match (uu____2880) with
| (x, y, dd, dq) -> begin
(match ((Prims.op_Equality id1.FStar_Ident.idText x)) with
| true -> begin
(

let uu____2911 = (

let uu____2912 = (FStar_Ident.lid_of_path (("Prims")::(y)::[]) id1.FStar_Ident.idRange)
in (FStar_Syntax_Syntax.fvar uu____2912 dd dq))
in FStar_Pervasives_Native.Some (uu____2911))
end
| uu____2917 -> begin
FStar_Pervasives_Native.None
end)
end))))

type 'a cont_t =
| Cont_ok of 'a
| Cont_fail
| Cont_ignore


let uu___is_Cont_ok : 'a . 'a cont_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Cont_ok (_0) -> begin
true
end
| uu____2952 -> begin
false
end))


let __proj__Cont_ok__item___0 : 'a . 'a cont_t  ->  'a = (fun projectee -> (match (projectee) with
| Cont_ok (_0) -> begin
_0
end))


let uu___is_Cont_fail : 'a . 'a cont_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Cont_fail -> begin
true
end
| uu____2989 -> begin
false
end))


let uu___is_Cont_ignore : 'a . 'a cont_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Cont_ignore -> begin
true
end
| uu____3010 -> begin
false
end))


let option_of_cont : 'a . (unit  ->  'a FStar_Pervasives_Native.option)  ->  'a cont_t  ->  'a FStar_Pervasives_Native.option = (fun k_ignore uu___1_3040 -> (match (uu___1_3040) with
| Cont_ok (a) -> begin
FStar_Pervasives_Native.Some (a)
end
| Cont_fail -> begin
FStar_Pervasives_Native.None
end
| Cont_ignore -> begin
(k_ignore ())
end))


let find_in_record : 'Auu____3059 . FStar_Ident.ident Prims.list  ->  FStar_Ident.ident  ->  record_or_dc  ->  (record_or_dc  ->  'Auu____3059 cont_t)  ->  'Auu____3059 cont_t = (fun ns id1 record cont -> (

let typename' = (FStar_Ident.lid_of_ids (FStar_List.append ns ((record.typename.FStar_Ident.ident)::[])))
in (

let uu____3096 = (FStar_Ident.lid_equals typename' record.typename)
in (match (uu____3096) with
| true -> begin
(

let fname = (FStar_Ident.lid_of_ids (FStar_List.append record.typename.FStar_Ident.ns ((id1)::[])))
in (

let find1 = (FStar_Util.find_map record.fields (fun uu____3112 -> (match (uu____3112) with
| (f, uu____3120) -> begin
(match ((Prims.op_Equality id1.FStar_Ident.idText f.FStar_Ident.idText)) with
| true -> begin
FStar_Pervasives_Native.Some (record)
end
| uu____3125 -> begin
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
| uu____3130 -> begin
Cont_ignore
end))))


let get_exported_id_set : env  ->  Prims.string  ->  (exported_id_kind  ->  string_set FStar_ST.ref) FStar_Pervasives_Native.option = (fun e mname -> (FStar_Util.smap_try_find e.exported_ids mname))


let get_trans_exported_id_set : env  ->  Prims.string  ->  (exported_id_kind  ->  string_set FStar_ST.ref) FStar_Pervasives_Native.option = (fun e mname -> (FStar_Util.smap_try_find e.trans_exported_ids mname))


let string_of_exported_id_kind : exported_id_kind  ->  Prims.string = (fun uu___2_3194 -> (match (uu___2_3194) with
| Exported_id_field -> begin
"field"
end
| Exported_id_term_type -> begin
"term/type"
end))


let find_in_module_with_includes : 'a . exported_id_kind  ->  (FStar_Ident.lident  ->  'a cont_t)  ->  'a cont_t  ->  env  ->  FStar_Ident.lident  ->  FStar_Ident.ident  ->  'a cont_t = (fun eikind find_in_module find_in_module_default env ns id1 -> (

let idstr = id1.FStar_Ident.idText
in (

let rec aux = (fun uu___3_3270 -> (match (uu___3_3270) with
| [] -> begin
find_in_module_default
end
| (modul)::q -> begin
(

let mname = modul.FStar_Ident.str
in (

let not_shadowed = (

let uu____3283 = (get_exported_id_set env mname)
in (match (uu____3283) with
| FStar_Pervasives_Native.None -> begin
true
end
| FStar_Pervasives_Native.Some (mex) -> begin
(

let mexports = (

let uu____3310 = (mex eikind)
in (FStar_ST.op_Bang uu____3310))
in (FStar_Util.set_mem idstr mexports))
end))
in (

let mincludes = (

let uu____3372 = (FStar_Util.smap_try_find env.includes mname)
in (match (uu____3372) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (minc) -> begin
(FStar_ST.op_Bang minc)
end))
in (

let look_into = (match (not_shadowed) with
| true -> begin
(

let uu____3427 = (qual modul id1)
in (find_in_module uu____3427))
end
| uu____3428 -> begin
Cont_ignore
end)
in (match (look_into) with
| Cont_ignore -> begin
(aux (FStar_List.append mincludes q))
end
| uu____3432 -> begin
look_into
end)))))
end))
in (aux ((ns)::[])))))


let is_exported_id_field : exported_id_kind  ->  Prims.bool = (fun uu___4_3441 -> (match (uu___4_3441) with
| Exported_id_field -> begin
true
end
| uu____3444 -> begin
false
end))


let try_lookup_id'' : 'a . env  ->  FStar_Ident.ident  ->  exported_id_kind  ->  (local_binding  ->  'a cont_t)  ->  (rec_binding  ->  'a cont_t)  ->  (record_or_dc  ->  'a cont_t)  ->  (FStar_Ident.lident  ->  'a cont_t)  ->  ('a cont_t  ->  FStar_Ident.ident  ->  'a cont_t)  ->  'a FStar_Pervasives_Native.option = (fun env id1 eikind k_local_binding k_rec_binding k_record find_in_module lookup_default_id -> (

let check_local_binding_id = (fun uu___5_3568 -> (match (uu___5_3568) with
| (id', uu____3571, uu____3572) -> begin
(Prims.op_Equality id'.FStar_Ident.idText id1.FStar_Ident.idText)
end))
in (

let check_rec_binding_id = (fun uu___6_3580 -> (match (uu___6_3580) with
| (id', uu____3583, uu____3584, uu____3585) -> begin
(Prims.op_Equality id'.FStar_Ident.idText id1.FStar_Ident.idText)
end))
in (

let curmod_ns = (

let uu____3590 = (current_module env)
in (FStar_Ident.ids_of_lid uu____3590))
in (

let proc = (fun uu___7_3598 -> (match (uu___7_3598) with
| Local_binding (l) when (check_local_binding_id l) -> begin
(

let uu____3602 = l
in (match (uu____3602) with
| (uu____3605, uu____3606, used_marker) -> begin
((FStar_ST.op_Colon_Equals used_marker true);
(k_local_binding l);
)
end))
end
| Rec_binding (r) when (check_rec_binding_id r) -> begin
(

let uu____3632 = r
in (match (uu____3632) with
| (uu____3635, uu____3636, uu____3637, used_marker) -> begin
((FStar_ST.op_Colon_Equals used_marker true);
(k_rec_binding r);
)
end))
end
| Open_module_or_namespace (ns, Open_module) -> begin
(find_in_module_with_includes eikind find_in_module Cont_ignore env ns id1)
end
| Top_level_def (id') when (Prims.op_Equality id'.FStar_Ident.idText id1.FStar_Ident.idText) -> begin
(lookup_default_id Cont_ignore id1)
end
| Record_or_dc (r) when (is_exported_id_field eikind) -> begin
(

let uu____3666 = (FStar_Ident.lid_of_ids curmod_ns)
in (find_in_module_with_includes Exported_id_field (fun lid -> (

let id2 = lid.FStar_Ident.ident
in (find_in_record lid.FStar_Ident.ns id2 r k_record))) Cont_ignore env uu____3666 id1))
end
| uu____3671 -> begin
Cont_ignore
end))
in (

let rec aux = (fun uu___8_3681 -> (match (uu___8_3681) with
| (a)::q -> begin
(

let uu____3690 = (proc a)
in (option_of_cont (fun uu____3694 -> (aux q)) uu____3690))
end
| [] -> begin
(

let uu____3695 = (lookup_default_id Cont_fail id1)
in (option_of_cont (fun uu____3699 -> FStar_Pervasives_Native.None) uu____3695))
end))
in (aux env.scope_mods)))))))


let found_local_binding : 'Auu____3709 'Auu____3710 . FStar_Range.range  ->  ('Auu____3709 * FStar_Syntax_Syntax.bv * 'Auu____3710)  ->  FStar_Syntax_Syntax.term = (fun r uu____3726 -> (match (uu____3726) with
| (id', x, uu____3735) -> begin
(bv_to_name x r)
end))


let find_in_module : 'Auu____3747 . env  ->  FStar_Ident.lident  ->  (FStar_Ident.lident  ->  (FStar_Syntax_Syntax.sigelt * Prims.bool)  ->  'Auu____3747)  ->  'Auu____3747  ->  'Auu____3747 = (fun env lid k_global_def k_not_found -> (

let uu____3788 = (FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str)
in (match (uu____3788) with
| FStar_Pervasives_Native.Some (sb) -> begin
(k_global_def lid sb)
end
| FStar_Pervasives_Native.None -> begin
k_not_found
end)))


let try_lookup_id : env  ->  FStar_Ident.ident  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun env id1 -> (

let uu____3832 = (unmangleOpName id1)
in (match (uu____3832) with
| FStar_Pervasives_Native.Some (f) -> begin
FStar_Pervasives_Native.Some (f)
end
| uu____3838 -> begin
(try_lookup_id'' env id1 Exported_id_term_type (fun r -> (

let uu____3844 = (found_local_binding id1.FStar_Ident.idRange r)
in Cont_ok (uu____3844))) (fun uu____3846 -> Cont_fail) (fun uu____3848 -> Cont_ignore) (fun i -> (find_in_module env i (fun uu____3855 uu____3856 -> Cont_fail) Cont_ignore)) (fun uu____3864 uu____3865 -> Cont_fail))
end)))


let lookup_default_id : 'a . env  ->  FStar_Ident.ident  ->  (FStar_Ident.lident  ->  (FStar_Syntax_Syntax.sigelt * Prims.bool)  ->  'a cont_t)  ->  'a cont_t  ->  'a cont_t = (fun env id1 k_global_def k_not_found -> (

let find_in_monad = (match (env.curmonad) with
| FStar_Pervasives_Native.Some (uu____3939) -> begin
(

let lid = (qualify env id1)
in (

let uu____3941 = (FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str)
in (match (uu____3941) with
| FStar_Pervasives_Native.Some (r) -> begin
(

let uu____3969 = (k_global_def lid r)
in FStar_Pervasives_Native.Some (uu____3969))
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

let uu____3993 = (current_module env)
in (qual uu____3993 id1))
in (find_in_module env lid k_global_def k_not_found))
end)))


let lid_is_curmod : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match (env.curmodule) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (m) -> begin
(FStar_Ident.lid_equals lid m)
end))


let module_is_defined : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> ((lid_is_curmod env lid) || (FStar_List.existsb (fun x -> (FStar_Ident.lid_equals lid (FStar_Pervasives_Native.fst x))) env.modules)))


let resolve_module_name : env  ->  FStar_Ident.lident  ->  Prims.bool  ->  FStar_Ident.lident FStar_Pervasives_Native.option = (fun env lid honor_ns -> (

let nslen = (FStar_List.length lid.FStar_Ident.ns)
in (

let rec aux = (fun uu___9_4065 -> (match (uu___9_4065) with
| [] -> begin
(

let uu____4070 = (module_is_defined env lid)
in (match (uu____4070) with
| true -> begin
FStar_Pervasives_Native.Some (lid)
end
| uu____4075 -> begin
FStar_Pervasives_Native.None
end))
end
| (Open_module_or_namespace (ns, Open_namespace))::q when honor_ns -> begin
(

let new_lid = (

let uu____4082 = (

let uu____4083 = (FStar_Ident.path_of_lid ns)
in (

let uu____4087 = (FStar_Ident.path_of_lid lid)
in (FStar_List.append uu____4083 uu____4087)))
in (

let uu____4092 = (FStar_Ident.range_of_lid lid)
in (FStar_Ident.lid_of_path uu____4082 uu____4092)))
in (

let uu____4093 = (module_is_defined env new_lid)
in (match (uu____4093) with
| true -> begin
FStar_Pervasives_Native.Some (new_lid)
end
| uu____4098 -> begin
(aux q)
end)))
end
| (Module_abbrev (name, modul))::uu____4102 when ((Prims.op_Equality nslen (Prims.parse_int "0")) && (Prims.op_Equality name.FStar_Ident.idText lid.FStar_Ident.ident.FStar_Ident.idText)) -> begin
FStar_Pervasives_Native.Some (modul)
end
| (uu____4108)::q -> begin
(aux q)
end))
in (aux env.scope_mods))))


let fail_if_curmodule : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  unit = (fun env ns_original ns_resolved -> (

let uu____4128 = (

let uu____4130 = (current_module env)
in (FStar_Ident.lid_equals ns_resolved uu____4130))
in (match (uu____4128) with
| true -> begin
(

let uu____4132 = (FStar_Ident.lid_equals ns_resolved FStar_Parser_Const.prims_lid)
in (match (uu____4132) with
| true -> begin
()
end
| uu____4135 -> begin
(

let uu____4137 = (

let uu____4143 = (FStar_Util.format1 "Reference %s to current module is forbidden (see GitHub issue #451)" ns_original.FStar_Ident.str)
in ((FStar_Errors.Fatal_ForbiddenReferenceToCurrentModule), (uu____4143)))
in (

let uu____4147 = (FStar_Ident.range_of_lid ns_original)
in (FStar_Errors.raise_error uu____4137 uu____4147)))
end))
end
| uu____4148 -> begin
()
end)))


let fail_if_qualified_by_curmodule : env  ->  FStar_Ident.lident  ->  unit = (fun env lid -> (match (lid.FStar_Ident.ns) with
| [] -> begin
()
end
| uu____4161 -> begin
(

let modul_orig = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in (

let uu____4165 = (resolve_module_name env modul_orig true)
in (match (uu____4165) with
| FStar_Pervasives_Native.Some (modul_res) -> begin
(fail_if_curmodule env modul_orig modul_res)
end
| uu____4170 -> begin
()
end)))
end))


let is_open : env  ->  FStar_Ident.lident  ->  open_kind  ->  Prims.bool = (fun env lid open_kind -> (FStar_List.existsb (fun uu___10_4193 -> (match (uu___10_4193) with
| Open_module_or_namespace (ns, k) -> begin
((Prims.op_Equality k open_kind) && (FStar_Ident.lid_equals lid ns))
end
| uu____4197 -> begin
false
end)) env.scope_mods))


let namespace_is_open : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (is_open env lid Open_namespace))


let module_is_open : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> ((lid_is_curmod env lid) || (is_open env lid Open_module)))


let shorten_module_path : env  ->  FStar_Ident.ident Prims.list  ->  Prims.bool  ->  (FStar_Ident.ident Prims.list * FStar_Ident.ident Prims.list) = (fun env ids is_full_path -> (

let rec aux = (fun revns id1 -> (

let lid = (FStar_Ident.lid_of_ns_and_id (FStar_List.rev revns) id1)
in (match ((namespace_is_open env lid)) with
| true -> begin
FStar_Pervasives_Native.Some ((((FStar_List.rev ((id1)::revns))), ([])))
end
| uu____4302 -> begin
(match (revns) with
| [] -> begin
FStar_Pervasives_Native.None
end
| (ns_last_id)::rev_ns_prefix -> begin
(

let uu____4326 = (aux rev_ns_prefix ns_last_id)
in (FStar_All.pipe_right uu____4326 (FStar_Util.map_option (fun uu____4376 -> (match (uu____4376) with
| (stripped_ids, rev_kept_ids) -> begin
((stripped_ids), ((id1)::rev_kept_ids))
end)))))
end)
end)))
in (

let do_shorten = (fun env1 ids1 -> (match ((FStar_List.rev ids1)) with
| [] -> begin
(([]), ([]))
end
| (ns_last_id)::ns_rev_prefix -> begin
(

let uu____4446 = (aux ns_rev_prefix ns_last_id)
in (match (uu____4446) with
| FStar_Pervasives_Native.None -> begin
(([]), (ids1))
end
| FStar_Pervasives_Native.Some (stripped_ids, rev_kept_ids) -> begin
((stripped_ids), ((FStar_List.rev rev_kept_ids)))
end))
end))
in (match ((is_full_path && ((FStar_List.length ids) > (Prims.parse_int "0")))) with
| true -> begin
(

let uu____4509 = (

let uu____4512 = (FStar_Ident.lid_of_ids ids)
in (resolve_module_name env uu____4512 true))
in (match (uu____4509) with
| FStar_Pervasives_Native.Some (m) when (module_is_open env m) -> begin
((ids), ([]))
end
| uu____4527 -> begin
(do_shorten env ids)
end))
end
| uu____4530 -> begin
(do_shorten env ids)
end))))


let resolve_in_open_namespaces'' : 'a . env  ->  FStar_Ident.lident  ->  exported_id_kind  ->  (local_binding  ->  'a cont_t)  ->  (rec_binding  ->  'a cont_t)  ->  (record_or_dc  ->  'a cont_t)  ->  (FStar_Ident.lident  ->  'a cont_t)  ->  ('a cont_t  ->  FStar_Ident.ident  ->  'a cont_t)  ->  'a FStar_Pervasives_Native.option = (fun env lid eikind k_local_binding k_rec_binding k_record f_module l_default -> (match (lid.FStar_Ident.ns) with
| (uu____4648)::uu____4649 -> begin
(

let uu____4652 = (

let uu____4655 = (

let uu____4656 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in (

let uu____4657 = (FStar_Ident.range_of_lid lid)
in (FStar_Ident.set_lid_range uu____4656 uu____4657)))
in (resolve_module_name env uu____4655 true))
in (match (uu____4652) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (modul) -> begin
(

let uu____4662 = (find_in_module_with_includes eikind f_module Cont_fail env modul lid.FStar_Ident.ident)
in (option_of_cont (fun uu____4666 -> FStar_Pervasives_Native.None) uu____4662))
end))
end
| [] -> begin
(try_lookup_id'' env lid.FStar_Ident.ident eikind k_local_binding k_rec_binding k_record f_module l_default)
end))


let cont_of_option : 'a . 'a cont_t  ->  'a FStar_Pervasives_Native.option  ->  'a cont_t = (fun k_none uu___11_4690 -> (match (uu___11_4690) with
| FStar_Pervasives_Native.Some (v1) -> begin
Cont_ok (v1)
end
| FStar_Pervasives_Native.None -> begin
k_none
end))


let resolve_in_open_namespaces' : 'a . env  ->  FStar_Ident.lident  ->  (local_binding  ->  'a FStar_Pervasives_Native.option)  ->  (rec_binding  ->  'a FStar_Pervasives_Native.option)  ->  (FStar_Ident.lident  ->  (FStar_Syntax_Syntax.sigelt * Prims.bool)  ->  'a FStar_Pervasives_Native.option)  ->  'a FStar_Pervasives_Native.option = (fun env lid k_local_binding k_rec_binding k_global_def -> (

let k_global_def' = (fun k lid1 def -> (

let uu____4811 = (k_global_def lid1 def)
in (cont_of_option k uu____4811)))
in (

let f_module = (fun lid' -> (

let k = Cont_ignore
in (find_in_module env lid' (k_global_def' k) k)))
in (

let l_default = (fun k i -> (lookup_default_id env i (k_global_def' k) k))
in (resolve_in_open_namespaces'' env lid Exported_id_term_type (fun l -> (

let uu____4847 = (k_local_binding l)
in (cont_of_option Cont_fail uu____4847))) (fun r -> (

let uu____4853 = (k_rec_binding r)
in (cont_of_option Cont_fail uu____4853))) (fun uu____4857 -> Cont_ignore) f_module l_default)))))


let fv_qual_of_se : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option = (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (uu____4868, uu____4869, uu____4870, l, uu____4872, uu____4873) -> begin
(

let qopt = (FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals (fun uu___12_4886 -> (match (uu___12_4886) with
| FStar_Syntax_Syntax.RecordConstructor (uu____4889, fs) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (((l), (fs))))
end
| uu____4901 -> begin
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
| FStar_Syntax_Syntax.Sig_declare_typ (uu____4907, uu____4908, uu____4909) -> begin
FStar_Pervasives_Native.None
end
| uu____4910 -> begin
FStar_Pervasives_Native.None
end))


let lb_fv : FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.fv = (fun lbs lid -> (

let uu____4926 = (FStar_Util.find_map lbs (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let uu____4934 = (FStar_Syntax_Syntax.fv_eq_lid fv lid)
in (match (uu____4934) with
| true -> begin
FStar_Pervasives_Native.Some (fv)
end
| uu____4939 -> begin
FStar_Pervasives_Native.None
end)))))
in (FStar_All.pipe_right uu____4926 FStar_Util.must)))


let ns_of_lid_equals : FStar_Ident.lident  ->  FStar_Ident.lident  ->  Prims.bool = (fun lid ns -> ((

let uu____4957 = (

let uu____4958 = (FStar_Ident.ids_of_lid ns)
in (FStar_List.length uu____4958))
in (Prims.op_Equality (FStar_List.length lid.FStar_Ident.ns) uu____4957)) && (

let uu____4962 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in (FStar_Ident.lid_equals uu____4962 ns))))


let delta_depth_of_declaration : FStar_Ident.lident  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.delta_depth = (fun lid quals -> (

let dd = (

let uu____4979 = ((FStar_Syntax_Util.is_primop_lid lid) || (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___13_4986 -> (match (uu___13_4986) with
| FStar_Syntax_Syntax.Projector (uu____4988) -> begin
true
end
| FStar_Syntax_Syntax.Discriminator (uu____4994) -> begin
true
end
| uu____4996 -> begin
false
end)))))
in (match (uu____4979) with
| true -> begin
FStar_Syntax_Syntax.delta_equational
end
| uu____4999 -> begin
FStar_Syntax_Syntax.delta_constant
end))
in (

let uu____5001 = ((FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___14_5007 -> (match (uu___14_5007) with
| FStar_Syntax_Syntax.Abstract -> begin
true
end
| uu____5010 -> begin
false
end)))) || ((FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___15_5016 -> (match (uu___15_5016) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| uu____5019 -> begin
false
end)))) && (

let uu____5022 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___16_5028 -> (match (uu___16_5028) with
| FStar_Syntax_Syntax.New -> begin
true
end
| uu____5031 -> begin
false
end))))
in (not (uu____5022)))))
in (match (uu____5001) with
| true -> begin
FStar_Syntax_Syntax.Delta_abstract (dd)
end
| uu____5034 -> begin
dd
end))))


let try_lookup_name : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  foundname FStar_Pervasives_Native.option = (fun any_val exclude_interf env lid -> (

let occurrence_range = (FStar_Ident.range_of_lid lid)
in (

let k_global_def = (fun source_lid uu___19_5083 -> (match (uu___19_5083) with
| (uu____5091, true) when exclude_interf -> begin
FStar_Pervasives_Native.None
end
| (se, uu____5095) -> begin
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____5100) -> begin
(

let uu____5117 = (

let uu____5118 = (

let uu____5125 = (FStar_Syntax_Syntax.fvar source_lid FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in ((uu____5125), (se.FStar_Syntax_Syntax.sigattrs)))
in Term_name (uu____5118))
in FStar_Pervasives_Native.Some (uu____5117))
end
| FStar_Syntax_Syntax.Sig_datacon (uu____5128) -> begin
(

let uu____5144 = (

let uu____5145 = (

let uu____5152 = (

let uu____5153 = (fv_qual_of_se se)
in (FStar_Syntax_Syntax.fvar source_lid FStar_Syntax_Syntax.delta_constant uu____5153))
in ((uu____5152), (se.FStar_Syntax_Syntax.sigattrs)))
in Term_name (uu____5145))
in FStar_Pervasives_Native.Some (uu____5144))
end
| FStar_Syntax_Syntax.Sig_let ((uu____5158, lbs), uu____5160) -> begin
(

let fv = (lb_fv lbs source_lid)
in (

let uu____5172 = (

let uu____5173 = (

let uu____5180 = (FStar_Syntax_Syntax.fvar source_lid fv.FStar_Syntax_Syntax.fv_delta fv.FStar_Syntax_Syntax.fv_qual)
in ((uu____5180), (se.FStar_Syntax_Syntax.sigattrs)))
in Term_name (uu____5173))
in FStar_Pervasives_Native.Some (uu____5172)))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid1, uu____5184, uu____5185) -> begin
(

let quals = se.FStar_Syntax_Syntax.sigquals
in (

let uu____5189 = (any_val || (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___17_5195 -> (match (uu___17_5195) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| uu____5198 -> begin
false
end)))))
in (match (uu____5189) with
| true -> begin
(

let lid2 = (

let uu____5204 = (FStar_Ident.range_of_lid source_lid)
in (FStar_Ident.set_lid_range lid1 uu____5204))
in (

let dd = (delta_depth_of_declaration lid2 quals)
in (

let uu____5206 = (FStar_Util.find_map quals (fun uu___18_5211 -> (match (uu___18_5211) with
| FStar_Syntax_Syntax.Reflectable (refl_monad) -> begin
FStar_Pervasives_Native.Some (refl_monad)
end
| uu____5215 -> begin
FStar_Pervasives_Native.None
end)))
in (match (uu____5206) with
| FStar_Pervasives_Native.Some (refl_monad) -> begin
(

let refl_const = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (refl_monad))) FStar_Pervasives_Native.None occurrence_range)
in FStar_Pervasives_Native.Some (Term_name (((refl_const), (se.FStar_Syntax_Syntax.sigattrs)))))
end
| uu____5224 -> begin
(

let uu____5227 = (

let uu____5228 = (

let uu____5235 = (

let uu____5236 = (fv_qual_of_se se)
in (FStar_Syntax_Syntax.fvar lid2 dd uu____5236))
in ((uu____5235), (se.FStar_Syntax_Syntax.sigattrs)))
in Term_name (uu____5228))
in FStar_Pervasives_Native.Some (uu____5227))
end))))
end
| uu____5241 -> begin
FStar_Pervasives_Native.None
end)))
end
| FStar_Syntax_Syntax.Sig_new_effect (ne) -> begin
(

let uu____5244 = (

let uu____5245 = (

let uu____5250 = (

let uu____5251 = (FStar_Ident.range_of_lid source_lid)
in (FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname uu____5251))
in ((se), (uu____5250)))
in Eff_name (uu____5245))
in FStar_Pervasives_Native.Some (uu____5244))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (uu____5252) -> begin
FStar_Pervasives_Native.Some (Eff_name (((se), (source_lid))))
end
| FStar_Syntax_Syntax.Sig_splice (lids, t) -> begin
(

let uu____5271 = (

let uu____5272 = (

let uu____5279 = (FStar_Syntax_Syntax.fvar source_lid (FStar_Syntax_Syntax.Delta_constant_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None)
in ((uu____5279), ([])))
in Term_name (uu____5272))
in FStar_Pervasives_Native.Some (uu____5271))
end
| uu____5283 -> begin
FStar_Pervasives_Native.None
end)
end))
in (

let k_local_binding = (fun r -> (

let t = (

let uu____5305 = (FStar_Ident.range_of_lid lid)
in (found_local_binding uu____5305 r))
in FStar_Pervasives_Native.Some (Term_name (((t), ([]))))))
in (

let k_rec_binding = (fun uu____5363 -> (match (uu____5363) with
| (id1, l, dd, used_marker) -> begin
((FStar_ST.op_Colon_Equals used_marker true);
(

let uu____5521 = (

let uu____5522 = (

let uu____5529 = (

let uu____5530 = (

let uu____5531 = (FStar_Ident.range_of_lid lid)
in (FStar_Ident.set_lid_range l uu____5531))
in (FStar_Syntax_Syntax.fvar uu____5530 dd FStar_Pervasives_Native.None))
in ((uu____5529), ([])))
in Term_name (uu____5522))
in FStar_Pervasives_Native.Some (uu____5521));
)
end))
in (

let found_unmangled = (match (lid.FStar_Ident.ns) with
| [] -> begin
(

let uu____5539 = (unmangleOpName lid.FStar_Ident.ident)
in (match (uu____5539) with
| FStar_Pervasives_Native.Some (t) -> begin
FStar_Pervasives_Native.Some (Term_name (((t), ([]))))
end
| uu____5547 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____5550 -> begin
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

let uu____5588 = (try_lookup_name true exclude_interf env lid)
in (match (uu____5588) with
| FStar_Pervasives_Native.Some (Eff_name (o, l)) -> begin
FStar_Pervasives_Native.Some (((o), (l)))
end
| uu____5604 -> begin
FStar_Pervasives_Native.None
end)))


let try_lookup_effect_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident FStar_Pervasives_Native.option = (fun env l -> (

let uu____5624 = (try_lookup_effect_name' (not (env.iface)) env l)
in (match (uu____5624) with
| FStar_Pervasives_Native.Some (o, l1) -> begin
FStar_Pervasives_Native.Some (l1)
end
| uu____5639 -> begin
FStar_Pervasives_Native.None
end)))


let try_lookup_effect_name_and_attributes : env  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.cflag Prims.list) FStar_Pervasives_Native.option = (fun env l -> (

let uu____5665 = (try_lookup_effect_name' (not (env.iface)) env l)
in (match (uu____5665) with
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect (ne); FStar_Syntax_Syntax.sigrng = uu____5681; FStar_Syntax_Syntax.sigquals = uu____5682; FStar_Syntax_Syntax.sigmeta = uu____5683; FStar_Syntax_Syntax.sigattrs = uu____5684; FStar_Syntax_Syntax.sigopts = uu____5685}, l1) -> begin
FStar_Pervasives_Native.Some (((l1), (ne.FStar_Syntax_Syntax.cattributes)))
end
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_effect_abbrev (uu____5705, uu____5706, uu____5707, uu____5708, cattributes); FStar_Syntax_Syntax.sigrng = uu____5710; FStar_Syntax_Syntax.sigquals = uu____5711; FStar_Syntax_Syntax.sigmeta = uu____5712; FStar_Syntax_Syntax.sigattrs = uu____5713; FStar_Syntax_Syntax.sigopts = uu____5714}, l1) -> begin
FStar_Pervasives_Native.Some (((l1), (cattributes)))
end
| uu____5738 -> begin
FStar_Pervasives_Native.None
end)))


let try_lookup_effect_defn : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl FStar_Pervasives_Native.option = (fun env l -> (

let uu____5764 = (try_lookup_effect_name' (not (env.iface)) env l)
in (match (uu____5764) with
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect (ne); FStar_Syntax_Syntax.sigrng = uu____5774; FStar_Syntax_Syntax.sigquals = uu____5775; FStar_Syntax_Syntax.sigmeta = uu____5776; FStar_Syntax_Syntax.sigattrs = uu____5777; FStar_Syntax_Syntax.sigopts = uu____5778}, uu____5779) -> begin
FStar_Pervasives_Native.Some (ne)
end
| uu____5790 -> begin
FStar_Pervasives_Native.None
end)))


let is_effect_name : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let uu____5809 = (try_lookup_effect_name env lid)
in (match (uu____5809) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (uu____5814) -> begin
true
end)))


let try_lookup_root_effect_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident FStar_Pervasives_Native.option = (fun env l -> (

let uu____5829 = (try_lookup_effect_name' (not (env.iface)) env l)
in (match (uu____5829) with
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_effect_abbrev (l', uu____5839, uu____5840, uu____5841, uu____5842); FStar_Syntax_Syntax.sigrng = uu____5843; FStar_Syntax_Syntax.sigquals = uu____5844; FStar_Syntax_Syntax.sigmeta = uu____5845; FStar_Syntax_Syntax.sigattrs = uu____5846; FStar_Syntax_Syntax.sigopts = uu____5847}, uu____5848) -> begin
(

let rec aux = (fun new_name -> (

let uu____5871 = (FStar_Util.smap_try_find (sigmap env) new_name.FStar_Ident.str)
in (match (uu____5871) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (s, uu____5892) -> begin
(match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_new_effect (ne) -> begin
(

let uu____5903 = (

let uu____5904 = (FStar_Ident.range_of_lid l)
in (FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname uu____5904))
in FStar_Pervasives_Native.Some (uu____5903))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (uu____5905, uu____5906, uu____5907, cmp, uu____5909) -> begin
(

let l'' = (FStar_Syntax_Util.comp_effect_name cmp)
in (aux l''))
end
| uu____5915 -> begin
FStar_Pervasives_Native.None
end)
end)))
in (aux l'))
end
| FStar_Pervasives_Native.Some (uu____5916, l') -> begin
FStar_Pervasives_Native.Some (l')
end
| uu____5922 -> begin
FStar_Pervasives_Native.None
end)))


let lookup_letbinding_quals_and_attrs : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.qualifier Prims.list * FStar_Syntax_Syntax.attribute Prims.list) = (fun env lid -> (

let k_global_def = (fun lid1 uu___20_5973 -> (match (uu___20_5973) with
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (uu____5989, uu____5990, uu____5991); FStar_Syntax_Syntax.sigrng = uu____5992; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = uu____5994; FStar_Syntax_Syntax.sigattrs = attrs; FStar_Syntax_Syntax.sigopts = uu____5996}, uu____5997) -> begin
FStar_Pervasives_Native.Some (((quals), (attrs)))
end
| uu____6018 -> begin
FStar_Pervasives_Native.None
end))
in (

let uu____6032 = (resolve_in_open_namespaces' env lid (fun uu____6052 -> FStar_Pervasives_Native.None) (fun uu____6062 -> FStar_Pervasives_Native.None) k_global_def)
in (match (uu____6032) with
| FStar_Pervasives_Native.Some (qa) -> begin
qa
end
| uu____6096 -> begin
(([]), ([]))
end))))


let try_lookup_module : env  ->  FStar_Ident.path  ->  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option = (fun env path -> (

let uu____6124 = (FStar_List.tryFind (fun uu____6139 -> (match (uu____6139) with
| (mlid, modul) -> begin
(

let uu____6147 = (FStar_Ident.path_of_lid mlid)
in (Prims.op_Equality uu____6147 path))
end)) env.modules)
in (match (uu____6124) with
| FStar_Pervasives_Native.Some (uu____6150, modul) -> begin
FStar_Pervasives_Native.Some (modul)
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end)))


let try_lookup_let : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun env lid -> (

let k_global_def = (fun lid1 uu___21_6190 -> (match (uu___21_6190) with
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let ((uu____6198, lbs), uu____6200); FStar_Syntax_Syntax.sigrng = uu____6201; FStar_Syntax_Syntax.sigquals = uu____6202; FStar_Syntax_Syntax.sigmeta = uu____6203; FStar_Syntax_Syntax.sigattrs = uu____6204; FStar_Syntax_Syntax.sigopts = uu____6205}, uu____6206) -> begin
(

let fv = (lb_fv lbs lid1)
in (

let uu____6226 = (FStar_Syntax_Syntax.fvar lid1 fv.FStar_Syntax_Syntax.fv_delta fv.FStar_Syntax_Syntax.fv_qual)
in FStar_Pervasives_Native.Some (uu____6226)))
end
| uu____6227 -> begin
FStar_Pervasives_Native.None
end))
in (resolve_in_open_namespaces' env lid (fun uu____6234 -> FStar_Pervasives_Native.None) (fun uu____6236 -> FStar_Pervasives_Native.None) k_global_def)))


let try_lookup_definition : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun env lid -> (

let k_global_def = (fun lid1 uu___22_6269 -> (match (uu___22_6269) with
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (lbs, uu____6280); FStar_Syntax_Syntax.sigrng = uu____6281; FStar_Syntax_Syntax.sigquals = uu____6282; FStar_Syntax_Syntax.sigmeta = uu____6283; FStar_Syntax_Syntax.sigattrs = uu____6284; FStar_Syntax_Syntax.sigopts = uu____6285}, uu____6286) -> begin
(FStar_Util.find_map (FStar_Pervasives_Native.snd lbs) (fun lb -> (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv lid1) -> begin
FStar_Pervasives_Native.Some (lb.FStar_Syntax_Syntax.lbdef)
end
| uu____6314 -> begin
FStar_Pervasives_Native.None
end)))
end
| uu____6321 -> begin
FStar_Pervasives_Native.None
end))
in (resolve_in_open_namespaces' env lid (fun uu____6332 -> FStar_Pervasives_Native.None) (fun uu____6336 -> FStar_Pervasives_Native.None) k_global_def)))


let empty_include_smap : FStar_Ident.lident Prims.list FStar_ST.ref FStar_Util.smap = (new_sigmap ())


let empty_exported_id_smap : exported_id_set FStar_Util.smap = (new_sigmap ())


let try_lookup_lid' : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.attribute Prims.list) FStar_Pervasives_Native.option = (fun any_val exclude_interface env lid -> (

let uu____6396 = (try_lookup_name any_val exclude_interface env lid)
in (match (uu____6396) with
| FStar_Pervasives_Native.Some (Term_name (e, attrs)) -> begin
FStar_Pervasives_Native.Some (((e), (attrs)))
end
| uu____6421 -> begin
FStar_Pervasives_Native.None
end)))


let drop_attributes : (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.attribute Prims.list) FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun x -> (match (x) with
| FStar_Pervasives_Native.Some (t, uu____6459) -> begin
FStar_Pervasives_Native.Some (t)
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end))


let try_lookup_lid_with_attributes : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.attribute Prims.list) FStar_Pervasives_Native.option = (fun env l -> (try_lookup_lid' env.iface false env l))


let try_lookup_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun env l -> (

let uu____6517 = (try_lookup_lid_with_attributes env l)
in (FStar_All.pipe_right uu____6517 drop_attributes)))


let resolve_to_fully_qualified_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident FStar_Pervasives_Native.option = (fun env l -> (

let uu____6549 = (try_lookup_lid env l)
in (match (uu____6549) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (e) -> begin
(

let uu____6555 = (

let uu____6556 = (FStar_Syntax_Subst.compress e)
in uu____6556.FStar_Syntax_Syntax.n)
in (match (uu____6555) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
FStar_Pervasives_Native.Some (fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end
| uu____6562 -> begin
FStar_Pervasives_Native.None
end))
end)))


let shorten_lid' : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (

let uu____6574 = (shorten_module_path env lid.FStar_Ident.ns true)
in (match (uu____6574) with
| (uu____6584, short) -> begin
(FStar_Ident.lid_of_ns_and_id short lid.FStar_Ident.ident)
end)))


let shorten_lid : env  ->  FStar_Ident.lid  ->  FStar_Ident.lid = (fun env lid -> (match (env.curmodule) with
| FStar_Pervasives_Native.None -> begin
(shorten_lid' env lid)
end
| uu____6605 -> begin
(

let lid_without_ns = (FStar_Ident.lid_of_ns_and_id [] lid.FStar_Ident.ident)
in (

let uu____6609 = (resolve_to_fully_qualified_name env lid_without_ns)
in (match (uu____6609) with
| FStar_Pervasives_Native.Some (lid') when (Prims.op_Equality lid'.FStar_Ident.str lid.FStar_Ident.str) -> begin
lid_without_ns
end
| uu____6614 -> begin
(shorten_lid' env lid)
end)))
end))


let try_lookup_lid_with_attributes_no_resolve : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.attribute Prims.list) FStar_Pervasives_Native.option = (fun env l -> (

let env' = (

let uu___885_6645 = env
in {curmodule = uu___885_6645.curmodule; curmonad = uu___885_6645.curmonad; modules = uu___885_6645.modules; scope_mods = []; exported_ids = empty_exported_id_smap; trans_exported_ids = uu___885_6645.trans_exported_ids; includes = empty_include_smap; sigaccum = uu___885_6645.sigaccum; sigmap = uu___885_6645.sigmap; iface = uu___885_6645.iface; admitted_iface = uu___885_6645.admitted_iface; expect_typ = uu___885_6645.expect_typ; docs = uu___885_6645.docs; remaining_iface_decls = uu___885_6645.remaining_iface_decls; syntax_only = uu___885_6645.syntax_only; ds_hooks = uu___885_6645.ds_hooks; dep_graph = uu___885_6645.dep_graph})
in (try_lookup_lid_with_attributes env' l)))


let try_lookup_lid_no_resolve : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun env l -> (

let uu____6661 = (try_lookup_lid_with_attributes_no_resolve env l)
in (FStar_All.pipe_right uu____6661 drop_attributes)))


let try_lookup_doc : env  ->  FStar_Ident.lid  ->  FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option = (fun env l -> (FStar_Util.smap_try_find env.docs l.FStar_Ident.str))


let try_lookup_datacon : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.fv FStar_Pervasives_Native.option = (fun env lid -> (

let k_global_def = (fun lid1 se -> (match (se) with
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (uu____6731, uu____6732, uu____6733); FStar_Syntax_Syntax.sigrng = uu____6734; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = uu____6736; FStar_Syntax_Syntax.sigattrs = uu____6737; FStar_Syntax_Syntax.sigopts = uu____6738}, uu____6739) -> begin
(

let uu____6748 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___23_6754 -> (match (uu___23_6754) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| uu____6757 -> begin
false
end))))
in (match (uu____6748) with
| true -> begin
(

let uu____6762 = (FStar_Syntax_Syntax.lid_as_fv lid1 FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in FStar_Pervasives_Native.Some (uu____6762))
end
| uu____6763 -> begin
FStar_Pervasives_Native.None
end))
end
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (uu____6765); FStar_Syntax_Syntax.sigrng = uu____6766; FStar_Syntax_Syntax.sigquals = uu____6767; FStar_Syntax_Syntax.sigmeta = uu____6768; FStar_Syntax_Syntax.sigattrs = uu____6769; FStar_Syntax_Syntax.sigopts = uu____6770}, uu____6771) -> begin
(

let qual1 = (fv_qual_of_se (FStar_Pervasives_Native.fst se))
in (

let uu____6799 = (FStar_Syntax_Syntax.lid_as_fv lid1 FStar_Syntax_Syntax.delta_constant qual1)
in FStar_Pervasives_Native.Some (uu____6799)))
end
| uu____6800 -> begin
FStar_Pervasives_Native.None
end))
in (resolve_in_open_namespaces' env lid (fun uu____6807 -> FStar_Pervasives_Native.None) (fun uu____6809 -> FStar_Pervasives_Native.None) k_global_def)))


let find_all_datacons : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.list FStar_Pervasives_Native.option = (fun env lid -> (

let k_global_def = (fun lid1 uu___24_6844 -> (match (uu___24_6844) with
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (uu____6854, uu____6855, uu____6856, uu____6857, datas, uu____6859); FStar_Syntax_Syntax.sigrng = uu____6860; FStar_Syntax_Syntax.sigquals = uu____6861; FStar_Syntax_Syntax.sigmeta = uu____6862; FStar_Syntax_Syntax.sigattrs = uu____6863; FStar_Syntax_Syntax.sigopts = uu____6864}, uu____6865) -> begin
FStar_Pervasives_Native.Some (datas)
end
| uu____6884 -> begin
FStar_Pervasives_Native.None
end))
in (resolve_in_open_namespaces' env lid (fun uu____6895 -> FStar_Pervasives_Native.None) (fun uu____6899 -> FStar_Pervasives_Native.None) k_global_def)))


let record_cache_aux_with_filter : ((((unit  ->  unit) * (unit  ->  unit)) * (((unit  ->  (Prims.int * unit)) * (Prims.int FStar_Pervasives_Native.option  ->  unit)) * ((unit  ->  record_or_dc Prims.list) * (record_or_dc  ->  unit)))) * (unit  ->  unit)) = (

let record_cache = (FStar_Util.mk_ref (([])::[]))
in (

let push1 = (fun uu____6978 -> (

let uu____6979 = (

let uu____6984 = (

let uu____6987 = (FStar_ST.op_Bang record_cache)
in (FStar_List.hd uu____6987))
in (

let uu____7021 = (FStar_ST.op_Bang record_cache)
in (uu____6984)::uu____7021))
in (FStar_ST.op_Colon_Equals record_cache uu____6979)))
in (

let pop1 = (fun uu____7087 -> (

let uu____7088 = (

let uu____7093 = (FStar_ST.op_Bang record_cache)
in (FStar_List.tl uu____7093))
in (FStar_ST.op_Colon_Equals record_cache uu____7088)))
in (

let snapshot1 = (fun uu____7164 -> (FStar_Common.snapshot push1 record_cache ()))
in (

let rollback1 = (fun depth -> (FStar_Common.rollback pop1 record_cache depth))
in (

let peek1 = (fun uu____7188 -> (

let uu____7189 = (FStar_ST.op_Bang record_cache)
in (FStar_List.hd uu____7189)))
in (

let insert = (fun r -> (

let uu____7229 = (

let uu____7234 = (

let uu____7237 = (peek1 ())
in (r)::uu____7237)
in (

let uu____7240 = (

let uu____7245 = (FStar_ST.op_Bang record_cache)
in (FStar_List.tl uu____7245))
in (uu____7234)::uu____7240))
in (FStar_ST.op_Colon_Equals record_cache uu____7229)))
in (

let filter1 = (fun uu____7313 -> (

let rc = (peek1 ())
in (

let filtered = (FStar_List.filter (fun r -> (not (r.is_private_or_abstract))) rc)
in (

let uu____7322 = (

let uu____7327 = (

let uu____7332 = (FStar_ST.op_Bang record_cache)
in (FStar_List.tl uu____7332))
in (filtered)::uu____7327)
in (FStar_ST.op_Colon_Equals record_cache uu____7322)))))
in (

let aux = ((((push1), (pop1))), (((((snapshot1), (rollback1))), (((peek1), (insert))))))
in ((aux), (filter1)))))))))))


let record_cache_aux : (((unit  ->  unit) * (unit  ->  unit)) * (((unit  ->  (Prims.int * unit)) * (Prims.int FStar_Pervasives_Native.option  ->  unit)) * ((unit  ->  record_or_dc Prims.list) * (record_or_dc  ->  unit)))) = (FStar_Pervasives_Native.fst record_cache_aux_with_filter)


let filter_record_cache : unit  ->  unit = (FStar_Pervasives_Native.snd record_cache_aux_with_filter)


let push_record_cache : unit  ->  unit = (FStar_Pervasives_Native.fst (FStar_Pervasives_Native.fst record_cache_aux))


let pop_record_cache : unit  ->  unit = (FStar_Pervasives_Native.snd (FStar_Pervasives_Native.fst record_cache_aux))


let snapshot_record_cache : unit  ->  (Prims.int * unit) = (FStar_Pervasives_Native.fst (FStar_Pervasives_Native.fst (FStar_Pervasives_Native.snd record_cache_aux)))


let rollback_record_cache : Prims.int FStar_Pervasives_Native.option  ->  unit = (FStar_Pervasives_Native.snd (FStar_Pervasives_Native.fst (FStar_Pervasives_Native.snd record_cache_aux)))


let peek_record_cache : unit  ->  record_or_dc Prims.list = (FStar_Pervasives_Native.fst (FStar_Pervasives_Native.snd (FStar_Pervasives_Native.snd record_cache_aux)))


let insert_record_cache : record_or_dc  ->  unit = (FStar_Pervasives_Native.snd (FStar_Pervasives_Native.snd (FStar_Pervasives_Native.snd record_cache_aux)))


let extract_record : env  ->  scope_mod Prims.list FStar_ST.ref  ->  FStar_Syntax_Syntax.sigelt  ->  unit = (fun e new_globs se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_bundle (sigs, uu____8258) -> begin
(

let is_record = (FStar_Util.for_some (fun uu___25_8277 -> (match (uu___25_8277) with
| FStar_Syntax_Syntax.RecordType (uu____8279) -> begin
true
end
| FStar_Syntax_Syntax.RecordConstructor (uu____8289) -> begin
true
end
| uu____8299 -> begin
false
end)))
in (

let find_dc = (fun dc -> (FStar_All.pipe_right sigs (FStar_Util.find_opt (fun uu___26_8325 -> (match (uu___26_8325) with
| {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (lid, uu____8328, uu____8329, uu____8330, uu____8331, uu____8332); FStar_Syntax_Syntax.sigrng = uu____8333; FStar_Syntax_Syntax.sigquals = uu____8334; FStar_Syntax_Syntax.sigmeta = uu____8335; FStar_Syntax_Syntax.sigattrs = uu____8336; FStar_Syntax_Syntax.sigopts = uu____8337} -> begin
(FStar_Ident.lid_equals dc lid)
end
| uu____8350 -> begin
false
end)))))
in (FStar_All.pipe_right sigs (FStar_List.iter (fun uu___27_8388 -> (match (uu___27_8388) with
| {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (typename, univs1, parms, uu____8392, uu____8393, (dc)::[]); FStar_Syntax_Syntax.sigrng = uu____8395; FStar_Syntax_Syntax.sigquals = typename_quals; FStar_Syntax_Syntax.sigmeta = uu____8397; FStar_Syntax_Syntax.sigattrs = uu____8398; FStar_Syntax_Syntax.sigopts = uu____8399} -> begin
(

let uu____8412 = (

let uu____8413 = (find_dc dc)
in (FStar_All.pipe_left FStar_Util.must uu____8413))
in (match (uu____8412) with
| {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (constrname, uu____8419, t, uu____8421, uu____8422, uu____8423); FStar_Syntax_Syntax.sigrng = uu____8424; FStar_Syntax_Syntax.sigquals = uu____8425; FStar_Syntax_Syntax.sigmeta = uu____8426; FStar_Syntax_Syntax.sigattrs = uu____8427; FStar_Syntax_Syntax.sigopts = uu____8428} -> begin
(

let uu____8441 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____8441) with
| (formals, uu____8457) -> begin
(

let is_rec = (is_record typename_quals)
in (

let formals' = (FStar_All.pipe_right formals (FStar_List.collect (fun uu____8511 -> (match (uu____8511) with
| (x, q) -> begin
(

let uu____8524 = ((FStar_Syntax_Syntax.is_null_bv x) || (is_rec && (FStar_Syntax_Syntax.is_implicit q)))
in (match (uu____8524) with
| true -> begin
[]
end
| uu____8537 -> begin
(((x), (q)))::[]
end))
end))))
in (

let fields' = (FStar_All.pipe_right formals' (FStar_List.map (fun uu____8579 -> (match (uu____8579) with
| (x, q) -> begin
((x.FStar_Syntax_Syntax.ppname), (x.FStar_Syntax_Syntax.sort))
end))))
in (

let fields = fields'
in (

let record = {typename = typename; constrname = constrname.FStar_Ident.ident; parms = parms; fields = fields; is_private_or_abstract = ((FStar_List.contains FStar_Syntax_Syntax.Private typename_quals) || (FStar_List.contains FStar_Syntax_Syntax.Abstract typename_quals)); is_record = is_rec}
in ((

let uu____8603 = (

let uu____8606 = (FStar_ST.op_Bang new_globs)
in (Record_or_dc (record))::uu____8606)
in (FStar_ST.op_Colon_Equals new_globs uu____8603));
(match (()) with
| () -> begin
((

let add_field = (fun uu____8665 -> (match (uu____8665) with
| (id1, uu____8671) -> begin
(

let modul = (

let uu____8674 = (FStar_Ident.lid_of_ids constrname.FStar_Ident.ns)
in uu____8674.FStar_Ident.str)
in (

let uu____8675 = (get_exported_id_set e modul)
in (match (uu____8675) with
| FStar_Pervasives_Native.Some (my_ex) -> begin
(

let my_exported_ids = (my_ex Exported_id_field)
in ((

let uu____8698 = (

let uu____8699 = (FStar_ST.op_Bang my_exported_ids)
in (FStar_Util.set_add id1.FStar_Ident.idText uu____8699))
in (FStar_ST.op_Colon_Equals my_exported_ids uu____8698));
(match (()) with
| () -> begin
(

let projname = (

let uu____8744 = (

let uu____8745 = (FStar_Syntax_Util.mk_field_projector_name_from_ident constrname id1)
in uu____8745.FStar_Ident.ident)
in uu____8744.FStar_Ident.idText)
in (

let uu____8747 = (

let uu____8748 = (FStar_ST.op_Bang my_exported_ids)
in (FStar_Util.set_add projname uu____8748))
in (FStar_ST.op_Colon_Equals my_exported_ids uu____8747)))
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
| uu____8800 -> begin
()
end))
end
| uu____8801 -> begin
()
end))))))
end
| uu____8802 -> begin
()
end))


let try_lookup_record_or_dc_by_field_name : env  ->  FStar_Ident.lident  ->  record_or_dc FStar_Pervasives_Native.option = (fun env fieldname -> (

let find_in_cache = (fun fieldname1 -> (

let uu____8824 = ((fieldname1.FStar_Ident.ns), (fieldname1.FStar_Ident.ident))
in (match (uu____8824) with
| (ns, id1) -> begin
(

let uu____8841 = (peek_record_cache ())
in (FStar_Util.find_map uu____8841 (fun record -> (

let uu____8847 = (find_in_record ns id1 record (fun r -> Cont_ok (r)))
in (option_of_cont (fun uu____8853 -> FStar_Pervasives_Native.None) uu____8847)))))
end)))
in (resolve_in_open_namespaces'' env fieldname Exported_id_field (fun uu____8855 -> Cont_ignore) (fun uu____8857 -> Cont_ignore) (fun r -> Cont_ok (r)) (fun fn -> (

let uu____8863 = (find_in_cache fn)
in (cont_of_option Cont_ignore uu____8863))) (fun k uu____8869 -> k))))


let try_lookup_record_by_field_name : env  ->  FStar_Ident.lident  ->  record_or_dc FStar_Pervasives_Native.option = (fun env fieldname -> (

let uu____8885 = (try_lookup_record_or_dc_by_field_name env fieldname)
in (match (uu____8885) with
| FStar_Pervasives_Native.Some (r) when r.is_record -> begin
FStar_Pervasives_Native.Some (r)
end
| uu____8891 -> begin
FStar_Pervasives_Native.None
end)))


let belongs_to_record : env  ->  FStar_Ident.lident  ->  record_or_dc  ->  Prims.bool = (fun env lid record -> (

let uu____8911 = (try_lookup_record_by_field_name env lid)
in (match (uu____8911) with
| FStar_Pervasives_Native.Some (record') when (

let uu____8916 = (

let uu____8918 = (FStar_Ident.path_of_ns record.typename.FStar_Ident.ns)
in (FStar_Ident.text_of_path uu____8918))
in (

let uu____8919 = (

let uu____8921 = (FStar_Ident.path_of_ns record'.typename.FStar_Ident.ns)
in (FStar_Ident.text_of_path uu____8921))
in (Prims.op_Equality uu____8916 uu____8919))) -> begin
(

let uu____8923 = (find_in_record record.typename.FStar_Ident.ns lid.FStar_Ident.ident record (fun uu____8927 -> Cont_ok (())))
in (match (uu____8923) with
| Cont_ok (uu____8929) -> begin
true
end
| uu____8931 -> begin
false
end))
end
| uu____8935 -> begin
false
end)))


let try_lookup_dc_by_field_name : env  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * Prims.bool) FStar_Pervasives_Native.option = (fun env fieldname -> (

let uu____8957 = (try_lookup_record_or_dc_by_field_name env fieldname)
in (match (uu____8957) with
| FStar_Pervasives_Native.Some (r) -> begin
(

let uu____8968 = (

let uu____8974 = (

let uu____8975 = (FStar_Ident.lid_of_ids (FStar_List.append r.typename.FStar_Ident.ns ((r.constrname)::[])))
in (

let uu____8976 = (FStar_Ident.range_of_lid fieldname)
in (FStar_Ident.set_lid_range uu____8975 uu____8976)))
in ((uu____8974), (r.is_record)))
in FStar_Pervasives_Native.Some (uu____8968))
end
| uu____8983 -> begin
FStar_Pervasives_Native.None
end)))


let string_set_ref_new : unit  ->  Prims.string FStar_Util.set FStar_ST.ref = (fun uu____9001 -> (

let uu____9002 = (FStar_Util.new_set FStar_Util.compare)
in (FStar_Util.mk_ref uu____9002)))


let exported_id_set_new : unit  ->  exported_id_kind  ->  Prims.string FStar_Util.set FStar_ST.ref = (fun uu____9023 -> (

let term_type_set = (string_set_ref_new ())
in (

let field_set = (string_set_ref_new ())
in (fun uu___28_9036 -> (match (uu___28_9036) with
| Exported_id_term_type -> begin
term_type_set
end
| Exported_id_field -> begin
field_set
end)))))


let unique : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  Prims.bool = (fun any_val exclude_interface env lid -> (

let filter_scope_mods = (fun uu___29_9074 -> (match (uu___29_9074) with
| Rec_binding (uu____9076) -> begin
true
end
| uu____9078 -> begin
false
end))
in (

let this_env = (

let uu___1117_9081 = env
in (

let uu____9082 = (FStar_List.filter filter_scope_mods env.scope_mods)
in {curmodule = uu___1117_9081.curmodule; curmonad = uu___1117_9081.curmonad; modules = uu___1117_9081.modules; scope_mods = uu____9082; exported_ids = empty_exported_id_smap; trans_exported_ids = uu___1117_9081.trans_exported_ids; includes = empty_include_smap; sigaccum = uu___1117_9081.sigaccum; sigmap = uu___1117_9081.sigmap; iface = uu___1117_9081.iface; admitted_iface = uu___1117_9081.admitted_iface; expect_typ = uu___1117_9081.expect_typ; docs = uu___1117_9081.docs; remaining_iface_decls = uu___1117_9081.remaining_iface_decls; syntax_only = uu___1117_9081.syntax_only; ds_hooks = uu___1117_9081.ds_hooks; dep_graph = uu___1117_9081.dep_graph}))
in (

let uu____9085 = (try_lookup_lid' any_val exclude_interface this_env lid)
in (match (uu____9085) with
| FStar_Pervasives_Native.None -> begin
true
end
| FStar_Pervasives_Native.Some (uu____9102) -> begin
false
end)))))


let push_scope_mod : env  ->  scope_mod  ->  env = (fun env scope_mod -> (

let uu___1125_9127 = env
in {curmodule = uu___1125_9127.curmodule; curmonad = uu___1125_9127.curmonad; modules = uu___1125_9127.modules; scope_mods = (scope_mod)::env.scope_mods; exported_ids = uu___1125_9127.exported_ids; trans_exported_ids = uu___1125_9127.trans_exported_ids; includes = uu___1125_9127.includes; sigaccum = uu___1125_9127.sigaccum; sigmap = uu___1125_9127.sigmap; iface = uu___1125_9127.iface; admitted_iface = uu___1125_9127.admitted_iface; expect_typ = uu___1125_9127.expect_typ; docs = uu___1125_9127.docs; remaining_iface_decls = uu___1125_9127.remaining_iface_decls; syntax_only = uu___1125_9127.syntax_only; ds_hooks = uu___1125_9127.ds_hooks; dep_graph = uu___1125_9127.dep_graph}))


let push_bv' : env  ->  FStar_Ident.ident  ->  (env * FStar_Syntax_Syntax.bv * used_marker) = (fun env x -> (

let bv = (FStar_Syntax_Syntax.gen_bv x.FStar_Ident.idText (FStar_Pervasives_Native.Some (x.FStar_Ident.idRange)) FStar_Syntax_Syntax.tun)
in (

let used_marker = (FStar_Util.mk_ref false)
in (((push_scope_mod env (Local_binding (((x), (bv), (used_marker)))))), (bv), (used_marker)))))


let push_bv : env  ->  FStar_Ident.ident  ->  (env * FStar_Syntax_Syntax.bv) = (fun env x -> (

let uu____9167 = (push_bv' env x)
in (match (uu____9167) with
| (env1, bv, uu____9180) -> begin
((env1), (bv))
end)))


let push_top_level_rec_binding : env  ->  FStar_Ident.ident  ->  FStar_Syntax_Syntax.delta_depth  ->  (env * Prims.bool FStar_ST.ref) = (fun env0 x dd -> (

let l = (qualify env0 x)
in (

let uu____9212 = ((unique false true env0 l) || (FStar_Options.interactive ()))
in (match (uu____9212) with
| true -> begin
(

let used_marker = (FStar_Util.mk_ref false)
in (((push_scope_mod env0 (Rec_binding (((x), (l), (dd), (used_marker)))))), (used_marker)))
end
| uu____9233 -> begin
(

let uu____9235 = (FStar_Ident.range_of_lid l)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_DuplicateTopLevelNames), ((Prims.op_Hat "Duplicate top-level names " l.FStar_Ident.str))) uu____9235))
end))))


let push_sigelt' : Prims.bool  ->  env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun fail_on_dup env s -> (

let err = (fun l -> (

let sopt = (FStar_Util.smap_try_find (sigmap env) l.FStar_Ident.str)
in (

let r = (match (sopt) with
| FStar_Pervasives_Native.Some (se, uu____9286) -> begin
(

let uu____9294 = (FStar_Util.find_opt (FStar_Ident.lid_equals l) (FStar_Syntax_Util.lids_of_sigelt se))
in (match (uu____9294) with
| FStar_Pervasives_Native.Some (l1) -> begin
(

let uu____9299 = (FStar_Ident.range_of_lid l1)
in (FStar_All.pipe_left FStar_Range.string_of_range uu____9299))
end
| FStar_Pervasives_Native.None -> begin
"<unknown>"
end))
end
| FStar_Pervasives_Native.None -> begin
"<unknown>"
end)
in (

let uu____9308 = (

let uu____9314 = (

let uu____9316 = (FStar_Ident.text_of_lid l)
in (FStar_Util.format2 "Duplicate top-level names [%s]; previously declared at %s" uu____9316 r))
in ((FStar_Errors.Fatal_DuplicateTopLevelNames), (uu____9314)))
in (

let uu____9320 = (FStar_Ident.range_of_lid l)
in (FStar_Errors.raise_error uu____9308 uu____9320))))))
in (

let globals = (FStar_Util.mk_ref env.scope_mods)
in (

let env1 = (

let uu____9329 = (match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let (uu____9342) -> begin
((false), (true))
end
| FStar_Syntax_Syntax.Sig_bundle (uu____9353) -> begin
((false), (true))
end
| uu____9366 -> begin
((false), (false))
end)
in (match (uu____9329) with
| (any_val, exclude_interface) -> begin
(

let lids = (FStar_Syntax_Util.lids_of_sigelt s)
in (

let uu____9380 = (FStar_Util.find_map lids (fun l -> (

let uu____9386 = (

let uu____9388 = (unique any_val exclude_interface env l)
in (not (uu____9388)))
in (match (uu____9386) with
| true -> begin
FStar_Pervasives_Native.Some (l)
end
| uu____9393 -> begin
FStar_Pervasives_Native.None
end))))
in (match (uu____9380) with
| FStar_Pervasives_Native.Some (l) when fail_on_dup -> begin
(err l)
end
| uu____9396 -> begin
((extract_record env globals s);
(

let uu___1174_9400 = env
in {curmodule = uu___1174_9400.curmodule; curmonad = uu___1174_9400.curmonad; modules = uu___1174_9400.modules; scope_mods = uu___1174_9400.scope_mods; exported_ids = uu___1174_9400.exported_ids; trans_exported_ids = uu___1174_9400.trans_exported_ids; includes = uu___1174_9400.includes; sigaccum = (s)::env.sigaccum; sigmap = uu___1174_9400.sigmap; iface = uu___1174_9400.iface; admitted_iface = uu___1174_9400.admitted_iface; expect_typ = uu___1174_9400.expect_typ; docs = uu___1174_9400.docs; remaining_iface_decls = uu___1174_9400.remaining_iface_decls; syntax_only = uu___1174_9400.syntax_only; ds_hooks = uu___1174_9400.ds_hooks; dep_graph = uu___1174_9400.dep_graph});
)
end)))
end))
in (

let env2 = (

let uu___1177_9402 = env1
in (

let uu____9403 = (FStar_ST.op_Bang globals)
in {curmodule = uu___1177_9402.curmodule; curmonad = uu___1177_9402.curmonad; modules = uu___1177_9402.modules; scope_mods = uu____9403; exported_ids = uu___1177_9402.exported_ids; trans_exported_ids = uu___1177_9402.trans_exported_ids; includes = uu___1177_9402.includes; sigaccum = uu___1177_9402.sigaccum; sigmap = uu___1177_9402.sigmap; iface = uu___1177_9402.iface; admitted_iface = uu___1177_9402.admitted_iface; expect_typ = uu___1177_9402.expect_typ; docs = uu___1177_9402.docs; remaining_iface_decls = uu___1177_9402.remaining_iface_decls; syntax_only = uu___1177_9402.syntax_only; ds_hooks = uu___1177_9402.ds_hooks; dep_graph = uu___1177_9402.dep_graph}))
in (

let uu____9429 = (match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____9455) -> begin
(

let uu____9464 = (FStar_List.map (fun se -> (((FStar_Syntax_Util.lids_of_sigelt se)), (se))) ses)
in ((env2), (uu____9464)))
end
| uu____9491 -> begin
((env2), (((((FStar_Syntax_Util.lids_of_sigelt s)), (s)))::[]))
end)
in (match (uu____9429) with
| (env3, lss) -> begin
((FStar_All.pipe_right lss (FStar_List.iter (fun uu____9550 -> (match (uu____9550) with
| (lids, se) -> begin
(FStar_All.pipe_right lids (FStar_List.iter (fun lid -> ((

let uu____9572 = (

let uu____9575 = (FStar_ST.op_Bang globals)
in (Top_level_def (lid.FStar_Ident.ident))::uu____9575)
in (FStar_ST.op_Colon_Equals globals uu____9572));
(match (()) with
| () -> begin
(

let modul = (

let uu____9626 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in uu____9626.FStar_Ident.str)
in ((

let uu____9628 = (get_exported_id_set env3 modul)
in (match (uu____9628) with
| FStar_Pervasives_Native.Some (f) -> begin
(

let my_exported_ids = (f Exported_id_term_type)
in (

let uu____9650 = (

let uu____9651 = (FStar_ST.op_Bang my_exported_ids)
in (FStar_Util.set_add lid.FStar_Ident.ident.FStar_Ident.idText uu____9651))
in (FStar_ST.op_Colon_Equals my_exported_ids uu____9650)))
end
| FStar_Pervasives_Native.None -> begin
()
end));
(match (()) with
| () -> begin
(

let is_iface = (env3.iface && (not (env3.admitted_iface)))
in (FStar_Util.smap_add (sigmap env3) lid.FStar_Ident.str ((se), ((env3.iface && (not (env3.admitted_iface)))))))
end);
))
end);
))))
end))));
(

let env4 = (

let uu___1202_9708 = env3
in (

let uu____9709 = (FStar_ST.op_Bang globals)
in {curmodule = uu___1202_9708.curmodule; curmonad = uu___1202_9708.curmonad; modules = uu___1202_9708.modules; scope_mods = uu____9709; exported_ids = uu___1202_9708.exported_ids; trans_exported_ids = uu___1202_9708.trans_exported_ids; includes = uu___1202_9708.includes; sigaccum = uu___1202_9708.sigaccum; sigmap = uu___1202_9708.sigmap; iface = uu___1202_9708.iface; admitted_iface = uu___1202_9708.admitted_iface; expect_typ = uu___1202_9708.expect_typ; docs = uu___1202_9708.docs; remaining_iface_decls = uu___1202_9708.remaining_iface_decls; syntax_only = uu___1202_9708.syntax_only; ds_hooks = uu___1202_9708.ds_hooks; dep_graph = uu___1202_9708.dep_graph}))
in env4);
)
end)))))))


let push_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env se -> (push_sigelt' true env se))


let push_sigelt_force : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env se -> (push_sigelt' false env se))


let push_namespace : env  ->  FStar_Ident.lident  ->  env = (fun env ns -> (

let uu____9770 = (

let uu____9775 = (resolve_module_name env ns false)
in (match (uu____9775) with
| FStar_Pervasives_Native.None -> begin
(

let modules = env.modules
in (

let uu____9790 = (FStar_All.pipe_right modules (FStar_Util.for_some (fun uu____9808 -> (match (uu____9808) with
| (m, uu____9815) -> begin
(

let uu____9816 = (

let uu____9818 = (FStar_Ident.text_of_lid m)
in (Prims.op_Hat uu____9818 "."))
in (

let uu____9821 = (

let uu____9823 = (FStar_Ident.text_of_lid ns)
in (Prims.op_Hat uu____9823 "."))
in (FStar_Util.starts_with uu____9816 uu____9821)))
end))))
in (match (uu____9790) with
| true -> begin
((ns), (Open_namespace))
end
| uu____9831 -> begin
(

let uu____9833 = (

let uu____9839 = (

let uu____9841 = (FStar_Ident.text_of_lid ns)
in (FStar_Util.format1 "Namespace %s cannot be found" uu____9841))
in ((FStar_Errors.Fatal_NameSpaceNotFound), (uu____9839)))
in (

let uu____9845 = (FStar_Ident.range_of_lid ns)
in (FStar_Errors.raise_error uu____9833 uu____9845)))
end)))
end
| FStar_Pervasives_Native.Some (ns') -> begin
((fail_if_curmodule env ns ns');
((ns'), (Open_module));
)
end))
in (match (uu____9770) with
| (ns', kd) -> begin
((env.ds_hooks.ds_push_open_hook env ((ns'), (kd)));
(push_scope_mod env (Open_module_or_namespace (((ns'), (kd)))));
)
end)))


let push_include : env  ->  FStar_Ident.lident  ->  env = (fun env ns -> (

let ns0 = ns
in (

let uu____9867 = (resolve_module_name env ns false)
in (match (uu____9867) with
| FStar_Pervasives_Native.Some (ns1) -> begin
((env.ds_hooks.ds_push_include_hook env ns1);
(fail_if_curmodule env ns0 ns1);
(

let env1 = (push_scope_mod env (Open_module_or_namespace (((ns1), (Open_module)))))
in (

let curmod = (

let uu____9877 = (current_module env1)
in uu____9877.FStar_Ident.str)
in ((

let uu____9879 = (FStar_Util.smap_try_find env1.includes curmod)
in (match (uu____9879) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (incl) -> begin
(

let uu____9903 = (

let uu____9906 = (FStar_ST.op_Bang incl)
in (ns1)::uu____9906)
in (FStar_ST.op_Colon_Equals incl uu____9903))
end));
(match (()) with
| () -> begin
(

let uu____9955 = (get_trans_exported_id_set env1 ns1.FStar_Ident.str)
in (match (uu____9955) with
| FStar_Pervasives_Native.Some (ns_trans_exports) -> begin
((

let uu____9975 = (

let uu____10072 = (get_exported_id_set env1 curmod)
in (

let uu____10119 = (get_trans_exported_id_set env1 curmod)
in ((uu____10072), (uu____10119))))
in (match (uu____9975) with
| (FStar_Pervasives_Native.Some (cur_exports), FStar_Pervasives_Native.Some (cur_trans_exports)) -> begin
(

let update_exports = (fun k -> (

let ns_ex = (

let uu____10535 = (ns_trans_exports k)
in (FStar_ST.op_Bang uu____10535))
in (

let ex = (cur_exports k)
in ((

let uu____10636 = (

let uu____10640 = (FStar_ST.op_Bang ex)
in (FStar_Util.set_difference uu____10640 ns_ex))
in (FStar_ST.op_Colon_Equals ex uu____10636));
(match (()) with
| () -> begin
(

let trans_ex = (cur_trans_exports k)
in (

let uu____10732 = (

let uu____10736 = (FStar_ST.op_Bang trans_ex)
in (FStar_Util.set_union uu____10736 ns_ex))
in (FStar_ST.op_Colon_Equals trans_ex uu____10732)))
end);
))))
in (FStar_List.iter update_exports all_exported_id_kinds))
end
| uu____10785 -> begin
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

let uu____10887 = (

let uu____10893 = (FStar_Util.format1 "include: Module %s was not prepared" ns1.FStar_Ident.str)
in ((FStar_Errors.Fatal_IncludeModuleNotPrepared), (uu____10893)))
in (

let uu____10897 = (FStar_Ident.range_of_lid ns1)
in (FStar_Errors.raise_error uu____10887 uu____10897)))
end))
end);
)));
)
end
| uu____10898 -> begin
(

let uu____10901 = (

let uu____10907 = (FStar_Util.format1 "include: Module %s cannot be found" ns.FStar_Ident.str)
in ((FStar_Errors.Fatal_ModuleNotFound), (uu____10907)))
in (

let uu____10911 = (FStar_Ident.range_of_lid ns)
in (FStar_Errors.raise_error uu____10901 uu____10911)))
end))))


let push_module_abbrev : env  ->  FStar_Ident.ident  ->  FStar_Ident.lident  ->  env = (fun env x l -> (

let uu____10928 = (module_is_defined env l)
in (match (uu____10928) with
| true -> begin
((fail_if_curmodule env l l);
(env.ds_hooks.ds_push_module_abbrev_hook env x l);
(push_scope_mod env (Module_abbrev (((x), (l)))));
)
end
| uu____10933 -> begin
(

let uu____10935 = (

let uu____10941 = (

let uu____10943 = (FStar_Ident.text_of_lid l)
in (FStar_Util.format1 "Module %s cannot be found" uu____10943))
in ((FStar_Errors.Fatal_ModuleNotFound), (uu____10941)))
in (

let uu____10947 = (FStar_Ident.range_of_lid l)
in (FStar_Errors.raise_error uu____10935 uu____10947)))
end)))


let push_doc : env  ->  FStar_Ident.lident  ->  FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option  ->  env = (fun env l doc_opt -> (match (doc_opt) with
| FStar_Pervasives_Native.None -> begin
env
end
| FStar_Pervasives_Native.Some (doc1) -> begin
((

let uu____10970 = (FStar_Util.smap_try_find env.docs l.FStar_Ident.str)
in (match (uu____10970) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (old_doc) -> begin
(

let uu____10974 = (FStar_Ident.range_of_lid l)
in (

let uu____10975 = (

let uu____10981 = (

let uu____10983 = (FStar_Ident.string_of_lid l)
in (

let uu____10985 = (FStar_Parser_AST.string_of_fsdoc old_doc)
in (

let uu____10987 = (FStar_Parser_AST.string_of_fsdoc doc1)
in (FStar_Util.format3 "Overwriting doc of %s; old doc was [%s]; new doc are [%s]" uu____10983 uu____10985 uu____10987))))
in ((FStar_Errors.Warning_DocOverwrite), (uu____10981)))
in (FStar_Errors.log_issue uu____10974 uu____10975)))
end));
(FStar_Util.smap_add env.docs l.FStar_Ident.str doc1);
env;
)
end))


let check_admits : env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.modul = (fun env m -> (

let admitted_sig_lids = (FStar_All.pipe_right env.sigaccum (FStar_List.fold_left (fun lids se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_declare_typ (l, u, t) when (

let uu____11034 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_List.contains FStar_Syntax_Syntax.Assumption))
in (not (uu____11034))) -> begin
(

let uu____11039 = (FStar_Util.smap_try_find (sigmap env) l.FStar_Ident.str)
in (match (uu____11039) with
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (uu____11054); FStar_Syntax_Syntax.sigrng = uu____11055; FStar_Syntax_Syntax.sigquals = uu____11056; FStar_Syntax_Syntax.sigmeta = uu____11057; FStar_Syntax_Syntax.sigattrs = uu____11058; FStar_Syntax_Syntax.sigopts = uu____11059}, uu____11060) -> begin
lids
end
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (uu____11080); FStar_Syntax_Syntax.sigrng = uu____11081; FStar_Syntax_Syntax.sigquals = uu____11082; FStar_Syntax_Syntax.sigmeta = uu____11083; FStar_Syntax_Syntax.sigattrs = uu____11084; FStar_Syntax_Syntax.sigopts = uu____11085}, uu____11086) -> begin
lids
end
| uu____11116 -> begin
((

let uu____11125 = (

let uu____11127 = (FStar_Options.interactive ())
in (not (uu____11127)))
in (match (uu____11125) with
| true -> begin
(

let uu____11130 = (FStar_Ident.range_of_lid l)
in (

let uu____11131 = (

let uu____11137 = (

let uu____11139 = (FStar_Ident.string_of_lid l)
in (FStar_Util.format1 "Admitting %s without a definition" uu____11139))
in ((FStar_Errors.Warning_AdmitWithoutDefinition), (uu____11137)))
in (FStar_Errors.log_issue uu____11130 uu____11131)))
end
| uu____11143 -> begin
()
end));
(

let quals = (FStar_Syntax_Syntax.Assumption)::se.FStar_Syntax_Syntax.sigquals
in ((FStar_Util.smap_add (sigmap env) l.FStar_Ident.str (((

let uu___1307_11156 = se
in {FStar_Syntax_Syntax.sigel = uu___1307_11156.FStar_Syntax_Syntax.sigel; FStar_Syntax_Syntax.sigrng = uu___1307_11156.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = uu___1307_11156.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___1307_11156.FStar_Syntax_Syntax.sigattrs; FStar_Syntax_Syntax.sigopts = uu___1307_11156.FStar_Syntax_Syntax.sigopts})), (false)));
(l)::lids;
));
)
end))
end
| uu____11158 -> begin
lids
end)) []))
in (

let uu___1312_11159 = m
in (

let uu____11160 = (FStar_All.pipe_right m.FStar_Syntax_Syntax.declarations (FStar_List.map (fun s -> (match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____11170, uu____11171) when (FStar_List.existsb (fun l -> (FStar_Ident.lid_equals l lid)) admitted_sig_lids) -> begin
(

let uu___1321_11174 = s
in {FStar_Syntax_Syntax.sigel = uu___1321_11174.FStar_Syntax_Syntax.sigel; FStar_Syntax_Syntax.sigrng = uu___1321_11174.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Assumption)::s.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___1321_11174.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___1321_11174.FStar_Syntax_Syntax.sigattrs; FStar_Syntax_Syntax.sigopts = uu___1321_11174.FStar_Syntax_Syntax.sigopts})
end
| uu____11175 -> begin
s
end))))
in {FStar_Syntax_Syntax.name = uu___1312_11159.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = uu____11160; FStar_Syntax_Syntax.exports = uu___1312_11159.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = uu___1312_11159.FStar_Syntax_Syntax.is_interface}))))


let finish : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env modul -> ((FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations (FStar_List.iter (fun se -> (

let quals = se.FStar_Syntax_Syntax.sigquals
in (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____11199) -> begin
(match (((FStar_List.contains FStar_Syntax_Syntax.Private quals) || (FStar_List.contains FStar_Syntax_Syntax.Abstract quals))) with
| true -> begin
(FStar_All.pipe_right ses (FStar_List.iter (fun se1 -> (match (se1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (lid, uu____11220, uu____11221, uu____11222, uu____11223, uu____11224) -> begin
(FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str)
end
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, univ_names, binders, typ, uu____11240, uu____11241) -> begin
((FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str);
(match ((not ((FStar_List.contains FStar_Syntax_Syntax.Private quals)))) with
| true -> begin
(

let sigel = (

let uu____11258 = (

let uu____11265 = (

let uu____11266 = (FStar_Ident.range_of_lid lid)
in (

let uu____11267 = (

let uu____11274 = (

let uu____11275 = (

let uu____11290 = (FStar_Syntax_Syntax.mk_Total typ)
in ((binders), (uu____11290)))
in FStar_Syntax_Syntax.Tm_arrow (uu____11275))
in (FStar_Syntax_Syntax.mk uu____11274))
in (uu____11267 FStar_Pervasives_Native.None uu____11266)))
in ((lid), (univ_names), (uu____11265)))
in FStar_Syntax_Syntax.Sig_declare_typ (uu____11258))
in (

let se2 = (

let uu___1353_11304 = se1
in {FStar_Syntax_Syntax.sigel = sigel; FStar_Syntax_Syntax.sigrng = uu___1353_11304.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Assumption)::quals; FStar_Syntax_Syntax.sigmeta = uu___1353_11304.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___1353_11304.FStar_Syntax_Syntax.sigattrs; FStar_Syntax_Syntax.sigopts = uu___1353_11304.FStar_Syntax_Syntax.sigopts})
in (FStar_Util.smap_add (sigmap env) lid.FStar_Ident.str ((se2), (false)))))
end
| uu____11312 -> begin
()
end);
)
end
| uu____11314 -> begin
()
end))))
end
| uu____11315 -> begin
()
end)
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____11318, uu____11319) -> begin
(match ((FStar_List.contains FStar_Syntax_Syntax.Private quals)) with
| true -> begin
(FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str)
end
| uu____11326 -> begin
()
end)
end
| FStar_Syntax_Syntax.Sig_let ((uu____11328, lbs), uu____11330) -> begin
((match (((FStar_List.contains FStar_Syntax_Syntax.Private quals) || (FStar_List.contains FStar_Syntax_Syntax.Abstract quals))) with
| true -> begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (

let uu____11348 = (

let uu____11350 = (

let uu____11351 = (

let uu____11354 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in uu____11354.FStar_Syntax_Syntax.fv_name)
in uu____11351.FStar_Syntax_Syntax.v)
in uu____11350.FStar_Ident.str)
in (FStar_Util.smap_remove (sigmap env) uu____11348)))))
end
| uu____11360 -> begin
()
end);
(match (((FStar_List.contains FStar_Syntax_Syntax.Abstract quals) && (not ((FStar_List.contains FStar_Syntax_Syntax.Private quals))))) with
| true -> begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (

let lid = (

let uu____11371 = (

let uu____11374 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in uu____11374.FStar_Syntax_Syntax.fv_name)
in uu____11371.FStar_Syntax_Syntax.v)
in (

let quals1 = (FStar_Syntax_Syntax.Assumption)::quals
in (

let decl = (

let uu___1376_11379 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp))); FStar_Syntax_Syntax.sigrng = uu___1376_11379.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = uu___1376_11379.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___1376_11379.FStar_Syntax_Syntax.sigattrs; FStar_Syntax_Syntax.sigopts = uu___1376_11379.FStar_Syntax_Syntax.sigopts})
in (FStar_Util.smap_add (sigmap env) lid.FStar_Ident.str ((decl), (false)))))))))
end
| uu____11387 -> begin
()
end);
)
end
| uu____11389 -> begin
()
end)))));
(

let curmod = (

let uu____11392 = (current_module env)
in uu____11392.FStar_Ident.str)
in ((

let uu____11394 = (

let uu____11491 = (get_exported_id_set env curmod)
in (

let uu____11538 = (get_trans_exported_id_set env curmod)
in ((uu____11491), (uu____11538))))
in (match (uu____11394) with
| (FStar_Pervasives_Native.Some (cur_ex), FStar_Pervasives_Native.Some (cur_trans_ex)) -> begin
(

let update_exports = (fun eikind -> (

let cur_ex_set = (

let uu____11957 = (cur_ex eikind)
in (FStar_ST.op_Bang uu____11957))
in (

let cur_trans_ex_set_ref = (cur_trans_ex eikind)
in (

let uu____12063 = (

let uu____12067 = (FStar_ST.op_Bang cur_trans_ex_set_ref)
in (FStar_Util.set_union cur_ex_set uu____12067))
in (FStar_ST.op_Colon_Equals cur_trans_ex_set_ref uu____12063)))))
in (FStar_List.iter update_exports all_exported_id_kinds))
end
| uu____12116 -> begin
()
end));
(match (()) with
| () -> begin
((filter_record_cache ());
(match (()) with
| () -> begin
(

let uu___1394_12214 = env
in {curmodule = FStar_Pervasives_Native.None; curmonad = uu___1394_12214.curmonad; modules = (((modul.FStar_Syntax_Syntax.name), (modul)))::env.modules; scope_mods = []; exported_ids = uu___1394_12214.exported_ids; trans_exported_ids = uu___1394_12214.trans_exported_ids; includes = uu___1394_12214.includes; sigaccum = []; sigmap = uu___1394_12214.sigmap; iface = uu___1394_12214.iface; admitted_iface = uu___1394_12214.admitted_iface; expect_typ = uu___1394_12214.expect_typ; docs = uu___1394_12214.docs; remaining_iface_decls = uu___1394_12214.remaining_iface_decls; syntax_only = uu___1394_12214.syntax_only; ds_hooks = uu___1394_12214.ds_hooks; dep_graph = uu___1394_12214.dep_graph})
end);
)
end);
));
))


let stack : env Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let push : env  ->  env = (fun env -> (FStar_Util.atomically (fun uu____12241 -> ((push_record_cache ());
(

let uu____12244 = (

let uu____12247 = (FStar_ST.op_Bang stack)
in (env)::uu____12247)
in (FStar_ST.op_Colon_Equals stack uu____12244));
(

let uu___1400_12296 = env
in (

let uu____12297 = (FStar_Util.smap_copy env.exported_ids)
in (

let uu____12302 = (FStar_Util.smap_copy env.trans_exported_ids)
in (

let uu____12307 = (FStar_Util.smap_copy env.includes)
in (

let uu____12318 = (FStar_Util.smap_copy env.sigmap)
in (

let uu____12331 = (FStar_Util.smap_copy env.docs)
in {curmodule = uu___1400_12296.curmodule; curmonad = uu___1400_12296.curmonad; modules = uu___1400_12296.modules; scope_mods = uu___1400_12296.scope_mods; exported_ids = uu____12297; trans_exported_ids = uu____12302; includes = uu____12307; sigaccum = uu___1400_12296.sigaccum; sigmap = uu____12318; iface = uu___1400_12296.iface; admitted_iface = uu___1400_12296.admitted_iface; expect_typ = uu___1400_12296.expect_typ; docs = uu____12331; remaining_iface_decls = uu___1400_12296.remaining_iface_decls; syntax_only = uu___1400_12296.syntax_only; ds_hooks = uu___1400_12296.ds_hooks; dep_graph = uu___1400_12296.dep_graph}))))));
))))


let pop : unit  ->  env = (fun uu____12339 -> (FStar_Util.atomically (fun uu____12346 -> (

let uu____12347 = (FStar_ST.op_Bang stack)
in (match (uu____12347) with
| (env)::tl1 -> begin
((pop_record_cache ());
(FStar_ST.op_Colon_Equals stack tl1);
env;
)
end
| uu____12402 -> begin
(failwith "Impossible: Too many pops")
end)))))


let snapshot : env  ->  (Prims.int * env) = (fun env -> (FStar_Common.snapshot push stack env))


let rollback : Prims.int FStar_Pervasives_Native.option  ->  env = (fun depth -> (FStar_Common.rollback pop stack depth))


let export_interface : FStar_Ident.lident  ->  env  ->  env = (fun m env -> (

let sigelt_in_m = (fun se -> (match ((FStar_Syntax_Util.lids_of_sigelt se)) with
| (l)::uu____12449 -> begin
(Prims.op_Equality l.FStar_Ident.nsstr m.FStar_Ident.str)
end
| uu____12453 -> begin
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

let uu____12495 = (FStar_Util.smap_try_find sm' k)
in (match (uu____12495) with
| FStar_Pervasives_Native.Some (se, true) when (sigelt_in_m se) -> begin
((FStar_Util.smap_remove sm' k);
(

let se1 = (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_declare_typ (l, u, t) -> begin
(

let uu___1435_12526 = se
in {FStar_Syntax_Syntax.sigel = uu___1435_12526.FStar_Syntax_Syntax.sigel; FStar_Syntax_Syntax.sigrng = uu___1435_12526.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Assumption)::se.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___1435_12526.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___1435_12526.FStar_Syntax_Syntax.sigattrs; FStar_Syntax_Syntax.sigopts = uu___1435_12526.FStar_Syntax_Syntax.sigopts})
end
| uu____12527 -> begin
se
end)
in (FStar_Util.smap_add sm' k ((se1), (false))));
)
end
| uu____12535 -> begin
()
end)))));
env1;
)))))))


let finish_module_or_interface : env  ->  FStar_Syntax_Syntax.modul  ->  (env * FStar_Syntax_Syntax.modul) = (fun env modul -> (

let modul1 = (match ((not (modul.FStar_Syntax_Syntax.is_interface))) with
| true -> begin
(check_admits env modul)
end
| uu____12560 -> begin
modul
end)
in (

let uu____12562 = (finish env modul1)
in ((uu____12562), (modul1)))))

type exported_ids =
{exported_id_terms : Prims.string Prims.list; exported_id_fields : Prims.string Prims.list}


let __proj__Mkexported_ids__item__exported_id_terms : exported_ids  ->  Prims.string Prims.list = (fun projectee -> (match (projectee) with
| {exported_id_terms = exported_id_terms; exported_id_fields = exported_id_fields} -> begin
exported_id_terms
end))


let __proj__Mkexported_ids__item__exported_id_fields : exported_ids  ->  Prims.string Prims.list = (fun projectee -> (match (projectee) with
| {exported_id_terms = exported_id_terms; exported_id_fields = exported_id_fields} -> begin
exported_id_fields
end))


let as_exported_ids : exported_id_set  ->  exported_ids = (fun e -> (

let terms = (

let uu____12631 = (

let uu____12635 = (e Exported_id_term_type)
in (FStar_ST.op_Bang uu____12635))
in (FStar_Util.set_elements uu____12631))
in (

let fields = (

let uu____12698 = (

let uu____12702 = (e Exported_id_field)
in (FStar_ST.op_Bang uu____12702))
in (FStar_Util.set_elements uu____12698))
in {exported_id_terms = terms; exported_id_fields = fields})))


let as_exported_id_set : exported_ids FStar_Pervasives_Native.option  ->  exported_id_kind  ->  Prims.string FStar_Util.set FStar_ST.ref = (fun e -> (match (e) with
| FStar_Pervasives_Native.None -> begin
(exported_id_set_new ())
end
| FStar_Pervasives_Native.Some (e1) -> begin
(

let terms = (

let uu____12794 = (FStar_Util.as_set e1.exported_id_terms FStar_Util.compare)
in (FStar_Util.mk_ref uu____12794))
in (

let fields = (

let uu____12808 = (FStar_Util.as_set e1.exported_id_fields FStar_Util.compare)
in (FStar_Util.mk_ref uu____12808))
in (fun uu___30_12816 -> (match (uu___30_12816) with
| Exported_id_term_type -> begin
terms
end
| Exported_id_field -> begin
fields
end))))
end))

type module_inclusion_info =
{mii_exported_ids : exported_ids FStar_Pervasives_Native.option; mii_trans_exported_ids : exported_ids FStar_Pervasives_Native.option; mii_includes : FStar_Ident.lident Prims.list FStar_Pervasives_Native.option}


let __proj__Mkmodule_inclusion_info__item__mii_exported_ids : module_inclusion_info  ->  exported_ids FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {mii_exported_ids = mii_exported_ids; mii_trans_exported_ids = mii_trans_exported_ids; mii_includes = mii_includes} -> begin
mii_exported_ids
end))


let __proj__Mkmodule_inclusion_info__item__mii_trans_exported_ids : module_inclusion_info  ->  exported_ids FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {mii_exported_ids = mii_exported_ids; mii_trans_exported_ids = mii_trans_exported_ids; mii_includes = mii_includes} -> begin
mii_trans_exported_ids
end))


let __proj__Mkmodule_inclusion_info__item__mii_includes : module_inclusion_info  ->  FStar_Ident.lident Prims.list FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {mii_exported_ids = mii_exported_ids; mii_trans_exported_ids = mii_trans_exported_ids; mii_includes = mii_includes} -> begin
mii_includes
end))


let default_mii : module_inclusion_info = {mii_exported_ids = FStar_Pervasives_Native.None; mii_trans_exported_ids = FStar_Pervasives_Native.None; mii_includes = FStar_Pervasives_Native.None}


let as_includes : 'Auu____12920 . 'Auu____12920 Prims.list FStar_Pervasives_Native.option  ->  'Auu____12920 Prims.list FStar_ST.ref = (fun uu___31_12933 -> (match (uu___31_12933) with
| FStar_Pervasives_Native.None -> begin
(FStar_Util.mk_ref [])
end
| FStar_Pervasives_Native.Some (l) -> begin
(FStar_Util.mk_ref l)
end))


let inclusion_info : env  ->  FStar_Ident.lident  ->  module_inclusion_info = (fun env l -> (

let mname = (FStar_Ident.string_of_lid l)
in (

let as_ids_opt = (fun m -> (

let uu____12976 = (FStar_Util.smap_try_find m mname)
in (FStar_Util.map_opt uu____12976 as_exported_ids)))
in (

let uu____12982 = (as_ids_opt env.exported_ids)
in (

let uu____12985 = (as_ids_opt env.trans_exported_ids)
in (

let uu____12988 = (

let uu____12993 = (FStar_Util.smap_try_find env.includes mname)
in (FStar_Util.map_opt uu____12993 (fun r -> (FStar_ST.op_Bang r))))
in {mii_exported_ids = uu____12982; mii_trans_exported_ids = uu____12985; mii_includes = uu____12988}))))))


let prepare_module_or_interface : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  module_inclusion_info  ->  (env * Prims.bool) = (fun intf admitted env mname mii -> (

let prep = (fun env1 -> (

let filename = (

let uu____13082 = (FStar_Ident.text_of_lid mname)
in (FStar_Util.strcat uu____13082 ".fst"))
in (

let auto_open = (FStar_Parser_Dep.hard_coded_dependencies filename)
in (

let auto_open1 = (

let convert_kind = (fun uu___32_13104 -> (match (uu___32_13104) with
| FStar_Parser_Dep.Open_namespace -> begin
Open_namespace
end
| FStar_Parser_Dep.Open_module -> begin
Open_module
end))
in (FStar_List.map (fun uu____13116 -> (match (uu____13116) with
| (lid, kind) -> begin
((lid), ((convert_kind kind)))
end)) auto_open))
in (

let namespace_of_module = (match (((FStar_List.length mname.FStar_Ident.ns) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____13142 = (

let uu____13147 = (FStar_Ident.lid_of_ids mname.FStar_Ident.ns)
in ((uu____13147), (Open_namespace)))
in (uu____13142)::[])
end
| uu____13156 -> begin
[]
end)
in (

let auto_open2 = (FStar_List.append namespace_of_module (FStar_List.rev auto_open1))
in ((

let uu____13178 = (as_exported_id_set mii.mii_exported_ids)
in (FStar_Util.smap_add env1.exported_ids mname.FStar_Ident.str uu____13178));
(match (()) with
| () -> begin
((

let uu____13183 = (as_exported_id_set mii.mii_trans_exported_ids)
in (FStar_Util.smap_add env1.trans_exported_ids mname.FStar_Ident.str uu____13183));
(match (()) with
| () -> begin
((

let uu____13188 = (as_includes mii.mii_includes)
in (FStar_Util.smap_add env1.includes mname.FStar_Ident.str uu____13188));
(match (()) with
| () -> begin
(

let env' = (

let uu___1505_13198 = env1
in (

let uu____13199 = (FStar_List.map (fun x -> Open_module_or_namespace (x)) auto_open2)
in {curmodule = FStar_Pervasives_Native.Some (mname); curmonad = uu___1505_13198.curmonad; modules = uu___1505_13198.modules; scope_mods = uu____13199; exported_ids = uu___1505_13198.exported_ids; trans_exported_ids = uu___1505_13198.trans_exported_ids; includes = uu___1505_13198.includes; sigaccum = uu___1505_13198.sigaccum; sigmap = env1.sigmap; iface = intf; admitted_iface = admitted; expect_typ = uu___1505_13198.expect_typ; docs = uu___1505_13198.docs; remaining_iface_decls = uu___1505_13198.remaining_iface_decls; syntax_only = uu___1505_13198.syntax_only; ds_hooks = uu___1505_13198.ds_hooks; dep_graph = uu___1505_13198.dep_graph}))
in ((FStar_List.iter (fun op -> (env1.ds_hooks.ds_push_open_hook env' op)) (FStar_List.rev auto_open2));
env';
))
end);
)
end);
)
end);
)))))))
in (

let uu____13211 = (FStar_All.pipe_right env.modules (FStar_Util.find_opt (fun uu____13237 -> (match (uu____13237) with
| (l, uu____13244) -> begin
(FStar_Ident.lid_equals l mname)
end))))
in (match (uu____13211) with
| FStar_Pervasives_Native.None -> begin
(

let uu____13254 = (prep env)
in ((uu____13254), (false)))
end
| FStar_Pervasives_Native.Some (uu____13257, m) -> begin
((

let uu____13264 = ((

let uu____13268 = (FStar_Options.interactive ())
in (not (uu____13268))) && ((not (m.FStar_Syntax_Syntax.is_interface)) || intf))
in (match (uu____13264) with
| true -> begin
(

let uu____13271 = (

let uu____13277 = (FStar_Util.format1 "Duplicate module or interface name: %s" mname.FStar_Ident.str)
in ((FStar_Errors.Fatal_DuplicateModuleOrInterface), (uu____13277)))
in (

let uu____13281 = (FStar_Ident.range_of_lid mname)
in (FStar_Errors.raise_error uu____13271 uu____13281)))
end
| uu____13282 -> begin
()
end));
(

let uu____13284 = (

let uu____13285 = (push env)
in (prep uu____13285))
in ((uu____13284), (true)));
)
end))))


let enter_monad_scope : env  ->  FStar_Ident.ident  ->  env = (fun env mname -> (match (env.curmonad) with
| FStar_Pervasives_Native.Some (mname') -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_MonadAlreadyDefined), ((Prims.op_Hat "Trying to define monad " (Prims.op_Hat mname.FStar_Ident.idText (Prims.op_Hat ", but already in monad scope " mname'.FStar_Ident.idText))))) mname.FStar_Ident.idRange)
end
| FStar_Pervasives_Native.None -> begin
(

let uu___1526_13303 = env
in {curmodule = uu___1526_13303.curmodule; curmonad = FStar_Pervasives_Native.Some (mname); modules = uu___1526_13303.modules; scope_mods = uu___1526_13303.scope_mods; exported_ids = uu___1526_13303.exported_ids; trans_exported_ids = uu___1526_13303.trans_exported_ids; includes = uu___1526_13303.includes; sigaccum = uu___1526_13303.sigaccum; sigmap = uu___1526_13303.sigmap; iface = uu___1526_13303.iface; admitted_iface = uu___1526_13303.admitted_iface; expect_typ = uu___1526_13303.expect_typ; docs = uu___1526_13303.docs; remaining_iface_decls = uu___1526_13303.remaining_iface_decls; syntax_only = uu___1526_13303.syntax_only; ds_hooks = uu___1526_13303.ds_hooks; dep_graph = uu___1526_13303.dep_graph})
end))


let fail_or : 'a . env  ->  (FStar_Ident.lident  ->  'a FStar_Pervasives_Native.option)  ->  FStar_Ident.lident  ->  'a = (fun env lookup1 lid -> (

let uu____13338 = (lookup1 lid)
in (match (uu____13338) with
| FStar_Pervasives_Native.None -> begin
(

let opened_modules = (FStar_List.map (fun uu____13353 -> (match (uu____13353) with
| (lid1, uu____13360) -> begin
(FStar_Ident.text_of_lid lid1)
end)) env.modules)
in (

let msg = (

let uu____13363 = (FStar_Ident.text_of_lid lid)
in (FStar_Util.format1 "Identifier not found: [%s]" uu____13363))
in (

let msg1 = (match ((Prims.op_Equality (FStar_List.length lid.FStar_Ident.ns) (Prims.parse_int "0"))) with
| true -> begin
msg
end
| uu____13372 -> begin
(

let modul = (

let uu____13375 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in (

let uu____13376 = (FStar_Ident.range_of_lid lid)
in (FStar_Ident.set_lid_range uu____13375 uu____13376)))
in (

let uu____13377 = (resolve_module_name env modul true)
in (match (uu____13377) with
| FStar_Pervasives_Native.None -> begin
(

let opened_modules1 = (FStar_String.concat ", " opened_modules)
in (FStar_Util.format3 "%s\nModule %s does not belong to the list of modules in scope, namely %s" msg modul.FStar_Ident.str opened_modules1))
end
| FStar_Pervasives_Native.Some (modul') when (not ((FStar_List.existsb (fun m -> (Prims.op_Equality m modul'.FStar_Ident.str)) opened_modules))) -> begin
(

let opened_modules1 = (FStar_String.concat ", " opened_modules)
in (FStar_Util.format4 "%s\nModule %s resolved into %s, which does not belong to the list of modules in scope, namely %s" msg modul.FStar_Ident.str modul'.FStar_Ident.str opened_modules1))
end
| FStar_Pervasives_Native.Some (modul') -> begin
(FStar_Util.format4 "%s\nModule %s resolved into %s, definition %s not found" msg modul.FStar_Ident.str modul'.FStar_Ident.str lid.FStar_Ident.ident.FStar_Ident.idText)
end)))
end)
in (

let uu____13398 = (FStar_Ident.range_of_lid lid)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_IdentifierNotFound), (msg1)) uu____13398)))))
end
| FStar_Pervasives_Native.Some (r) -> begin
r
end)))


let fail_or2 : 'a . (FStar_Ident.ident  ->  'a FStar_Pervasives_Native.option)  ->  FStar_Ident.ident  ->  'a = (fun lookup1 id1 -> (

let uu____13428 = (lookup1 id1)
in (match (uu____13428) with
| FStar_Pervasives_Native.None -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_IdentifierNotFound), ((Prims.op_Hat "Identifier not found [" (Prims.op_Hat id1.FStar_Ident.idText "]")))) id1.FStar_Ident.idRange)
end
| FStar_Pervasives_Native.Some (r) -> begin
r
end)))




