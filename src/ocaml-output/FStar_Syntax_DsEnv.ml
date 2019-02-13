
open Prims
open FStar_Pervasives

type local_binding =
(FStar_Ident.ident * FStar_Syntax_Syntax.bv)


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
| uu____23 -> begin
false
end))


let uu___is_Open_namespace : open_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Open_namespace -> begin
true
end
| uu____34 -> begin
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
| uu____254 -> begin
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
| uu____274 -> begin
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
| uu____294 -> begin
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
| uu____314 -> begin
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
| uu____334 -> begin
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
| uu____354 -> begin
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
| uu____376 -> begin
false
end))


let uu___is_Exported_id_field : exported_id_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Exported_id_field -> begin
true
end
| uu____387 -> begin
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


let default_ds_hooks : dsenv_hooks = {ds_push_open_hook = (fun uu____2007 uu____2008 -> ()); ds_push_include_hook = (fun uu____2011 uu____2012 -> ()); ds_push_module_abbrev_hook = (fun uu____2016 uu____2017 uu____2018 -> ())}

type foundname =
| Term_name of (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.attribute Prims.list)
| Eff_name of (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident)


let uu___is_Term_name : foundname  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Term_name (_0) -> begin
true
end
| uu____2055 -> begin
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
| uu____2097 -> begin
false
end))


let __proj__Eff_name__item___0 : foundname  ->  (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident) = (fun projectee -> (match (projectee) with
| Eff_name (_0) -> begin
_0
end))


let set_iface : env  ->  Prims.bool  ->  env = (fun env b -> (

let uu___206_2132 = env
in {curmodule = uu___206_2132.curmodule; curmonad = uu___206_2132.curmonad; modules = uu___206_2132.modules; scope_mods = uu___206_2132.scope_mods; exported_ids = uu___206_2132.exported_ids; trans_exported_ids = uu___206_2132.trans_exported_ids; includes = uu___206_2132.includes; sigaccum = uu___206_2132.sigaccum; sigmap = uu___206_2132.sigmap; iface = b; admitted_iface = uu___206_2132.admitted_iface; expect_typ = uu___206_2132.expect_typ; docs = uu___206_2132.docs; remaining_iface_decls = uu___206_2132.remaining_iface_decls; syntax_only = uu___206_2132.syntax_only; ds_hooks = uu___206_2132.ds_hooks; dep_graph = uu___206_2132.dep_graph}))


let iface : env  ->  Prims.bool = (fun e -> e.iface)


let set_admitted_iface : env  ->  Prims.bool  ->  env = (fun e b -> (

let uu___207_2153 = e
in {curmodule = uu___207_2153.curmodule; curmonad = uu___207_2153.curmonad; modules = uu___207_2153.modules; scope_mods = uu___207_2153.scope_mods; exported_ids = uu___207_2153.exported_ids; trans_exported_ids = uu___207_2153.trans_exported_ids; includes = uu___207_2153.includes; sigaccum = uu___207_2153.sigaccum; sigmap = uu___207_2153.sigmap; iface = uu___207_2153.iface; admitted_iface = b; expect_typ = uu___207_2153.expect_typ; docs = uu___207_2153.docs; remaining_iface_decls = uu___207_2153.remaining_iface_decls; syntax_only = uu___207_2153.syntax_only; ds_hooks = uu___207_2153.ds_hooks; dep_graph = uu___207_2153.dep_graph}))


let admitted_iface : env  ->  Prims.bool = (fun e -> e.admitted_iface)


let set_expect_typ : env  ->  Prims.bool  ->  env = (fun e b -> (

let uu___208_2174 = e
in {curmodule = uu___208_2174.curmodule; curmonad = uu___208_2174.curmonad; modules = uu___208_2174.modules; scope_mods = uu___208_2174.scope_mods; exported_ids = uu___208_2174.exported_ids; trans_exported_ids = uu___208_2174.trans_exported_ids; includes = uu___208_2174.includes; sigaccum = uu___208_2174.sigaccum; sigmap = uu___208_2174.sigmap; iface = uu___208_2174.iface; admitted_iface = uu___208_2174.admitted_iface; expect_typ = b; docs = uu___208_2174.docs; remaining_iface_decls = uu___208_2174.remaining_iface_decls; syntax_only = uu___208_2174.syntax_only; ds_hooks = uu___208_2174.ds_hooks; dep_graph = uu___208_2174.dep_graph}))


let expect_typ : env  ->  Prims.bool = (fun e -> e.expect_typ)


let all_exported_id_kinds : exported_id_kind Prims.list = (Exported_id_field)::(Exported_id_term_type)::[]


let transitive_exported_ids : env  ->  FStar_Ident.lident  ->  Prims.string Prims.list = (fun env lid -> (

let module_name = (FStar_Ident.string_of_lid lid)
in (

let uu____2201 = (FStar_Util.smap_try_find env.trans_exported_ids module_name)
in (match (uu____2201) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (exported_id_set) -> begin
(

let uu____2214 = (

let uu____2218 = (exported_id_set Exported_id_term_type)
in (FStar_ST.op_Bang uu____2218))
in (FStar_All.pipe_right uu____2214 FStar_Util.set_elements))
end))))


let open_modules : env  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.modul) Prims.list = (fun e -> e.modules)


let open_modules_and_namespaces : env  ->  FStar_Ident.lident Prims.list = (fun env -> (FStar_List.filter_map (fun uu___173_2359 -> (match (uu___173_2359) with
| Open_module_or_namespace (lid, _info) -> begin
FStar_Pervasives_Native.Some (lid)
end
| uu____2364 -> begin
FStar_Pervasives_Native.None
end)) env.scope_mods))


let set_current_module : env  ->  FStar_Ident.lident  ->  env = (fun e l -> (

let uu___209_2376 = e
in {curmodule = FStar_Pervasives_Native.Some (l); curmonad = uu___209_2376.curmonad; modules = uu___209_2376.modules; scope_mods = uu___209_2376.scope_mods; exported_ids = uu___209_2376.exported_ids; trans_exported_ids = uu___209_2376.trans_exported_ids; includes = uu___209_2376.includes; sigaccum = uu___209_2376.sigaccum; sigmap = uu___209_2376.sigmap; iface = uu___209_2376.iface; admitted_iface = uu___209_2376.admitted_iface; expect_typ = uu___209_2376.expect_typ; docs = uu___209_2376.docs; remaining_iface_decls = uu___209_2376.remaining_iface_decls; syntax_only = uu___209_2376.syntax_only; ds_hooks = uu___209_2376.ds_hooks; dep_graph = uu___209_2376.dep_graph}))


let current_module : env  ->  FStar_Ident.lident = (fun env -> (match (env.curmodule) with
| FStar_Pervasives_Native.None -> begin
(failwith "Unset current module")
end
| FStar_Pervasives_Native.Some (m) -> begin
m
end))


let iface_decls : env  ->  FStar_Ident.lident  ->  FStar_Parser_AST.decl Prims.list FStar_Pervasives_Native.option = (fun env l -> (

let uu____2400 = (FStar_All.pipe_right env.remaining_iface_decls (FStar_List.tryFind (fun uu____2434 -> (match (uu____2434) with
| (m, uu____2443) -> begin
(FStar_Ident.lid_equals l m)
end))))
in (match (uu____2400) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (uu____2460, decls) -> begin
FStar_Pervasives_Native.Some (decls)
end)))


let set_iface_decls : env  ->  FStar_Ident.lident  ->  FStar_Parser_AST.decl Prims.list  ->  env = (fun env l ds -> (

let uu____2494 = (FStar_List.partition (fun uu____2524 -> (match (uu____2524) with
| (m, uu____2533) -> begin
(FStar_Ident.lid_equals l m)
end)) env.remaining_iface_decls)
in (match (uu____2494) with
| (uu____2538, rest) -> begin
(

let uu___210_2572 = env
in {curmodule = uu___210_2572.curmodule; curmonad = uu___210_2572.curmonad; modules = uu___210_2572.modules; scope_mods = uu___210_2572.scope_mods; exported_ids = uu___210_2572.exported_ids; trans_exported_ids = uu___210_2572.trans_exported_ids; includes = uu___210_2572.includes; sigaccum = uu___210_2572.sigaccum; sigmap = uu___210_2572.sigmap; iface = uu___210_2572.iface; admitted_iface = uu___210_2572.admitted_iface; expect_typ = uu___210_2572.expect_typ; docs = uu___210_2572.docs; remaining_iface_decls = (((l), (ds)))::rest; syntax_only = uu___210_2572.syntax_only; ds_hooks = uu___210_2572.ds_hooks; dep_graph = uu___210_2572.dep_graph})
end)))


let qual : FStar_Ident.lident  ->  FStar_Ident.ident  ->  FStar_Ident.lident = FStar_Syntax_Util.qual_id


let qualify : env  ->  FStar_Ident.ident  ->  FStar_Ident.lident = (fun env id1 -> (match (env.curmonad) with
| FStar_Pervasives_Native.None -> begin
(

let uu____2601 = (current_module env)
in (qual uu____2601 id1))
end
| FStar_Pervasives_Native.Some (monad) -> begin
(

let uu____2603 = (

let uu____2604 = (current_module env)
in (qual uu____2604 monad))
in (FStar_Syntax_Util.mk_field_projector_name_from_ident uu____2603 id1))
end))


let syntax_only : env  ->  Prims.bool = (fun env -> env.syntax_only)


let set_syntax_only : env  ->  Prims.bool  ->  env = (fun env b -> (

let uu___211_2625 = env
in {curmodule = uu___211_2625.curmodule; curmonad = uu___211_2625.curmonad; modules = uu___211_2625.modules; scope_mods = uu___211_2625.scope_mods; exported_ids = uu___211_2625.exported_ids; trans_exported_ids = uu___211_2625.trans_exported_ids; includes = uu___211_2625.includes; sigaccum = uu___211_2625.sigaccum; sigmap = uu___211_2625.sigmap; iface = uu___211_2625.iface; admitted_iface = uu___211_2625.admitted_iface; expect_typ = uu___211_2625.expect_typ; docs = uu___211_2625.docs; remaining_iface_decls = uu___211_2625.remaining_iface_decls; syntax_only = b; ds_hooks = uu___211_2625.ds_hooks; dep_graph = uu___211_2625.dep_graph}))


let ds_hooks : env  ->  dsenv_hooks = (fun env -> env.ds_hooks)


let set_ds_hooks : env  ->  dsenv_hooks  ->  env = (fun env hooks -> (

let uu___212_2643 = env
in {curmodule = uu___212_2643.curmodule; curmonad = uu___212_2643.curmonad; modules = uu___212_2643.modules; scope_mods = uu___212_2643.scope_mods; exported_ids = uu___212_2643.exported_ids; trans_exported_ids = uu___212_2643.trans_exported_ids; includes = uu___212_2643.includes; sigaccum = uu___212_2643.sigaccum; sigmap = uu___212_2643.sigmap; iface = uu___212_2643.iface; admitted_iface = uu___212_2643.admitted_iface; expect_typ = uu___212_2643.expect_typ; docs = uu___212_2643.docs; remaining_iface_decls = uu___212_2643.remaining_iface_decls; syntax_only = uu___212_2643.syntax_only; ds_hooks = hooks; dep_graph = uu___212_2643.dep_graph}))


let new_sigmap : 'Auu____2649 . unit  ->  'Auu____2649 FStar_Util.smap = (fun uu____2656 -> (FStar_Util.smap_create (Prims.parse_int "100")))


let empty_env : FStar_Parser_Dep.deps  ->  env = (fun deps -> (

let uu____2664 = (new_sigmap ())
in (

let uu____2669 = (new_sigmap ())
in (

let uu____2674 = (new_sigmap ())
in (

let uu____2685 = (new_sigmap ())
in (

let uu____2698 = (new_sigmap ())
in {curmodule = FStar_Pervasives_Native.None; curmonad = FStar_Pervasives_Native.None; modules = []; scope_mods = []; exported_ids = uu____2664; trans_exported_ids = uu____2669; includes = uu____2674; sigaccum = []; sigmap = uu____2685; iface = false; admitted_iface = false; expect_typ = false; docs = uu____2698; remaining_iface_decls = []; syntax_only = false; ds_hooks = default_ds_hooks; dep_graph = deps}))))))


let dep_graph : env  ->  FStar_Parser_Dep.deps = (fun env -> env.dep_graph)


let set_dep_graph : env  ->  FStar_Parser_Dep.deps  ->  env = (fun env ds -> (

let uu___213_2732 = env
in {curmodule = uu___213_2732.curmodule; curmonad = uu___213_2732.curmonad; modules = uu___213_2732.modules; scope_mods = uu___213_2732.scope_mods; exported_ids = uu___213_2732.exported_ids; trans_exported_ids = uu___213_2732.trans_exported_ids; includes = uu___213_2732.includes; sigaccum = uu___213_2732.sigaccum; sigmap = uu___213_2732.sigmap; iface = uu___213_2732.iface; admitted_iface = uu___213_2732.admitted_iface; expect_typ = uu___213_2732.expect_typ; docs = uu___213_2732.docs; remaining_iface_decls = uu___213_2732.remaining_iface_decls; syntax_only = uu___213_2732.syntax_only; ds_hooks = uu___213_2732.ds_hooks; dep_graph = ds}))


let sigmap : env  ->  (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap = (fun env -> env.sigmap)


let has_all_in_scope : env  ->  Prims.bool = (fun env -> (FStar_List.existsb (fun uu____2760 -> (match (uu____2760) with
| (m, uu____2767) -> begin
(FStar_Ident.lid_equals m FStar_Parser_Const.all_lid)
end)) env.modules))


let set_bv_range : FStar_Syntax_Syntax.bv  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.bv = (fun bv r -> (

let id1 = (

let uu___214_2780 = bv.FStar_Syntax_Syntax.ppname
in {FStar_Ident.idText = uu___214_2780.FStar_Ident.idText; FStar_Ident.idRange = r})
in (

let uu___215_2781 = bv
in {FStar_Syntax_Syntax.ppname = id1; FStar_Syntax_Syntax.index = uu___215_2781.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu___215_2781.FStar_Syntax_Syntax.sort})))


let bv_to_name : FStar_Syntax_Syntax.bv  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.term = (fun bv r -> (FStar_Syntax_Syntax.bv_to_name (set_bv_range bv r)))


let unmangleMap : (Prims.string * Prims.string * FStar_Syntax_Syntax.delta_depth * FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option) Prims.list = ((("op_ColonColon"), ("Cons"), (FStar_Syntax_Syntax.delta_constant), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor))))::((("not"), ("op_Negation"), (FStar_Syntax_Syntax.delta_equational), (FStar_Pervasives_Native.None)))::[]


let unmangleOpName : FStar_Ident.ident  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun id1 -> (FStar_Util.find_map unmangleMap (fun uu____2884 -> (match (uu____2884) with
| (x, y, dd, dq) -> begin
(match ((Prims.op_Equality id1.FStar_Ident.idText x)) with
| true -> begin
(

let uu____2915 = (

let uu____2916 = (FStar_Ident.lid_of_path (("Prims")::(y)::[]) id1.FStar_Ident.idRange)
in (FStar_Syntax_Syntax.fvar uu____2916 dd dq))
in FStar_Pervasives_Native.Some (uu____2915))
end
| uu____2921 -> begin
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
| uu____2956 -> begin
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
| uu____2994 -> begin
false
end))


let uu___is_Cont_ignore : 'a . 'a cont_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Cont_ignore -> begin
true
end
| uu____3015 -> begin
false
end))


let option_of_cont : 'a . (unit  ->  'a FStar_Pervasives_Native.option)  ->  'a cont_t  ->  'a FStar_Pervasives_Native.option = (fun k_ignore uu___174_3045 -> (match (uu___174_3045) with
| Cont_ok (a) -> begin
FStar_Pervasives_Native.Some (a)
end
| Cont_fail -> begin
FStar_Pervasives_Native.None
end
| Cont_ignore -> begin
(k_ignore ())
end))


let find_in_record : 'Auu____3064 . FStar_Ident.ident Prims.list  ->  FStar_Ident.ident  ->  record_or_dc  ->  (record_or_dc  ->  'Auu____3064 cont_t)  ->  'Auu____3064 cont_t = (fun ns id1 record cont -> (

let typename' = (FStar_Ident.lid_of_ids (FStar_List.append ns ((record.typename.FStar_Ident.ident)::[])))
in (

let uu____3101 = (FStar_Ident.lid_equals typename' record.typename)
in (match (uu____3101) with
| true -> begin
(

let fname = (FStar_Ident.lid_of_ids (FStar_List.append record.typename.FStar_Ident.ns ((id1)::[])))
in (

let find1 = (FStar_Util.find_map record.fields (fun uu____3117 -> (match (uu____3117) with
| (f, uu____3125) -> begin
(match ((Prims.op_Equality id1.FStar_Ident.idText f.FStar_Ident.idText)) with
| true -> begin
FStar_Pervasives_Native.Some (record)
end
| uu____3130 -> begin
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
| uu____3135 -> begin
Cont_ignore
end))))


let get_exported_id_set : env  ->  Prims.string  ->  (exported_id_kind  ->  string_set FStar_ST.ref) FStar_Pervasives_Native.option = (fun e mname -> (FStar_Util.smap_try_find e.exported_ids mname))


let get_trans_exported_id_set : env  ->  Prims.string  ->  (exported_id_kind  ->  string_set FStar_ST.ref) FStar_Pervasives_Native.option = (fun e mname -> (FStar_Util.smap_try_find e.trans_exported_ids mname))


let string_of_exported_id_kind : exported_id_kind  ->  Prims.string = (fun uu___175_3199 -> (match (uu___175_3199) with
| Exported_id_field -> begin
"field"
end
| Exported_id_term_type -> begin
"term/type"
end))


let find_in_module_with_includes : 'a . exported_id_kind  ->  (FStar_Ident.lident  ->  'a cont_t)  ->  'a cont_t  ->  env  ->  FStar_Ident.lident  ->  FStar_Ident.ident  ->  'a cont_t = (fun eikind find_in_module find_in_module_default env ns id1 -> (

let idstr = id1.FStar_Ident.idText
in (

let rec aux = (fun uu___176_3275 -> (match (uu___176_3275) with
| [] -> begin
find_in_module_default
end
| (modul)::q -> begin
(

let mname = modul.FStar_Ident.str
in (

let not_shadowed = (

let uu____3288 = (get_exported_id_set env mname)
in (match (uu____3288) with
| FStar_Pervasives_Native.None -> begin
true
end
| FStar_Pervasives_Native.Some (mex) -> begin
(

let mexports = (

let uu____3315 = (mex eikind)
in (FStar_ST.op_Bang uu____3315))
in (FStar_Util.set_mem idstr mexports))
end))
in (

let mincludes = (

let uu____3430 = (FStar_Util.smap_try_find env.includes mname)
in (match (uu____3430) with
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

let uu____3507 = (qual modul id1)
in (find_in_module uu____3507))
end
| uu____3508 -> begin
Cont_ignore
end)
in (match (look_into) with
| Cont_ignore -> begin
(aux (FStar_List.append mincludes q))
end
| uu____3512 -> begin
look_into
end)))))
end))
in (aux ((ns)::[])))))


let is_exported_id_field : exported_id_kind  ->  Prims.bool = (fun uu___177_3521 -> (match (uu___177_3521) with
| Exported_id_field -> begin
true
end
| uu____3524 -> begin
false
end))


let try_lookup_id'' : 'a . env  ->  FStar_Ident.ident  ->  exported_id_kind  ->  (local_binding  ->  'a cont_t)  ->  (rec_binding  ->  'a cont_t)  ->  (record_or_dc  ->  'a cont_t)  ->  (FStar_Ident.lident  ->  'a cont_t)  ->  ('a cont_t  ->  FStar_Ident.ident  ->  'a cont_t)  ->  'a FStar_Pervasives_Native.option = (fun env id1 eikind k_local_binding k_rec_binding k_record find_in_module lookup_default_id -> (

let check_local_binding_id = (fun uu___178_3648 -> (match (uu___178_3648) with
| (id', uu____3651) -> begin
(Prims.op_Equality id'.FStar_Ident.idText id1.FStar_Ident.idText)
end))
in (

let check_rec_binding_id = (fun uu___179_3659 -> (match (uu___179_3659) with
| (id', uu____3662, uu____3663) -> begin
(Prims.op_Equality id'.FStar_Ident.idText id1.FStar_Ident.idText)
end))
in (

let curmod_ns = (

let uu____3668 = (current_module env)
in (FStar_Ident.ids_of_lid uu____3668))
in (

let proc = (fun uu___180_3676 -> (match (uu___180_3676) with
| Local_binding (l) when (check_local_binding_id l) -> begin
(k_local_binding l)
end
| Rec_binding (r) when (check_rec_binding_id r) -> begin
(k_rec_binding r)
end
| Open_module_or_namespace (ns, Open_module) -> begin
(find_in_module_with_includes eikind find_in_module Cont_ignore env ns id1)
end
| Top_level_def (id') when (Prims.op_Equality id'.FStar_Ident.idText id1.FStar_Ident.idText) -> begin
(lookup_default_id Cont_ignore id1)
end
| Record_or_dc (r) when (is_exported_id_field eikind) -> begin
(

let uu____3685 = (FStar_Ident.lid_of_ids curmod_ns)
in (find_in_module_with_includes Exported_id_field (fun lid -> (

let id2 = lid.FStar_Ident.ident
in (find_in_record lid.FStar_Ident.ns id2 r k_record))) Cont_ignore env uu____3685 id1))
end
| uu____3690 -> begin
Cont_ignore
end))
in (

let rec aux = (fun uu___181_3700 -> (match (uu___181_3700) with
| (a)::q -> begin
(

let uu____3709 = (proc a)
in (option_of_cont (fun uu____3713 -> (aux q)) uu____3709))
end
| [] -> begin
(

let uu____3714 = (lookup_default_id Cont_fail id1)
in (option_of_cont (fun uu____3718 -> FStar_Pervasives_Native.None) uu____3714))
end))
in (aux env.scope_mods)))))))


let found_local_binding : 'Auu____3726 . FStar_Range.range  ->  ('Auu____3726 * FStar_Syntax_Syntax.bv)  ->  FStar_Syntax_Syntax.term = (fun r uu____3740 -> (match (uu____3740) with
| (id', x) -> begin
(bv_to_name x r)
end))


let find_in_module : 'Auu____3758 . env  ->  FStar_Ident.lident  ->  (FStar_Ident.lident  ->  (FStar_Syntax_Syntax.sigelt * Prims.bool)  ->  'Auu____3758)  ->  'Auu____3758  ->  'Auu____3758 = (fun env lid k_global_def k_not_found -> (

let uu____3799 = (FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str)
in (match (uu____3799) with
| FStar_Pervasives_Native.Some (sb) -> begin
(k_global_def lid sb)
end
| FStar_Pervasives_Native.None -> begin
k_not_found
end)))


let try_lookup_id : env  ->  FStar_Ident.ident  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun env id1 -> (

let uu____3843 = (unmangleOpName id1)
in (match (uu____3843) with
| FStar_Pervasives_Native.Some (f) -> begin
FStar_Pervasives_Native.Some (f)
end
| uu____3849 -> begin
(try_lookup_id'' env id1 Exported_id_term_type (fun r -> (

let uu____3855 = (found_local_binding id1.FStar_Ident.idRange r)
in Cont_ok (uu____3855))) (fun uu____3857 -> Cont_fail) (fun uu____3859 -> Cont_ignore) (fun i -> (find_in_module env i (fun uu____3866 uu____3867 -> Cont_fail) Cont_ignore)) (fun uu____3875 uu____3876 -> Cont_fail))
end)))


let lookup_default_id : 'a . env  ->  FStar_Ident.ident  ->  (FStar_Ident.lident  ->  (FStar_Syntax_Syntax.sigelt * Prims.bool)  ->  'a cont_t)  ->  'a cont_t  ->  'a cont_t = (fun env id1 k_global_def k_not_found -> (

let find_in_monad = (match (env.curmonad) with
| FStar_Pervasives_Native.Some (uu____3950) -> begin
(

let lid = (qualify env id1)
in (

let uu____3952 = (FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str)
in (match (uu____3952) with
| FStar_Pervasives_Native.Some (r) -> begin
(

let uu____3980 = (k_global_def lid r)
in FStar_Pervasives_Native.Some (uu____3980))
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

let uu____4004 = (current_module env)
in (qual uu____4004 id1))
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

let rec aux = (fun uu___182_4076 -> (match (uu___182_4076) with
| [] -> begin
(

let uu____4081 = (module_is_defined env lid)
in (match (uu____4081) with
| true -> begin
FStar_Pervasives_Native.Some (lid)
end
| uu____4086 -> begin
FStar_Pervasives_Native.None
end))
end
| (Open_module_or_namespace (ns, Open_namespace))::q when honor_ns -> begin
(

let new_lid = (

let uu____4093 = (

let uu____4094 = (FStar_Ident.path_of_lid ns)
in (

let uu____4098 = (FStar_Ident.path_of_lid lid)
in (FStar_List.append uu____4094 uu____4098)))
in (

let uu____4103 = (FStar_Ident.range_of_lid lid)
in (FStar_Ident.lid_of_path uu____4093 uu____4103)))
in (

let uu____4104 = (module_is_defined env new_lid)
in (match (uu____4104) with
| true -> begin
FStar_Pervasives_Native.Some (new_lid)
end
| uu____4109 -> begin
(aux q)
end)))
end
| (Module_abbrev (name, modul))::uu____4113 when ((Prims.op_Equality nslen (Prims.parse_int "0")) && (Prims.op_Equality name.FStar_Ident.idText lid.FStar_Ident.ident.FStar_Ident.idText)) -> begin
FStar_Pervasives_Native.Some (modul)
end
| (uu____4123)::q -> begin
(aux q)
end))
in (aux env.scope_mods))))


let fail_if_curmodule : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  unit = (fun env ns_original ns_resolved -> (

let uu____4143 = (

let uu____4145 = (current_module env)
in (FStar_Ident.lid_equals ns_resolved uu____4145))
in (match (uu____4143) with
| true -> begin
(

let uu____4147 = (FStar_Ident.lid_equals ns_resolved FStar_Parser_Const.prims_lid)
in (match (uu____4147) with
| true -> begin
()
end
| uu____4150 -> begin
(

let uu____4152 = (

let uu____4158 = (FStar_Util.format1 "Reference %s to current module is forbidden (see GitHub issue #451)" ns_original.FStar_Ident.str)
in ((FStar_Errors.Fatal_ForbiddenReferenceToCurrentModule), (uu____4158)))
in (

let uu____4162 = (FStar_Ident.range_of_lid ns_original)
in (FStar_Errors.raise_error uu____4152 uu____4162)))
end))
end
| uu____4163 -> begin
()
end)))


let fail_if_qualified_by_curmodule : env  ->  FStar_Ident.lident  ->  unit = (fun env lid -> (match (lid.FStar_Ident.ns) with
| [] -> begin
()
end
| uu____4176 -> begin
(

let modul_orig = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in (

let uu____4180 = (resolve_module_name env modul_orig true)
in (match (uu____4180) with
| FStar_Pervasives_Native.Some (modul_res) -> begin
(fail_if_curmodule env modul_orig modul_res)
end
| uu____4185 -> begin
()
end)))
end))


let is_open : env  ->  FStar_Ident.lident  ->  open_kind  ->  Prims.bool = (fun env lid open_kind -> (FStar_List.existsb (fun uu___183_4208 -> (match (uu___183_4208) with
| Open_module_or_namespace (ns, k) -> begin
((Prims.op_Equality k open_kind) && (FStar_Ident.lid_equals lid ns))
end
| uu____4212 -> begin
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
| uu____4317 -> begin
(match (revns) with
| [] -> begin
FStar_Pervasives_Native.None
end
| (ns_last_id)::rev_ns_prefix -> begin
(

let uu____4341 = (aux rev_ns_prefix ns_last_id)
in (FStar_All.pipe_right uu____4341 (FStar_Util.map_option (fun uu____4391 -> (match (uu____4391) with
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

let uu____4461 = (aux ns_rev_prefix ns_last_id)
in (match (uu____4461) with
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

let uu____4524 = (

let uu____4527 = (FStar_Ident.lid_of_ids ids)
in (resolve_module_name env uu____4527 true))
in (match (uu____4524) with
| FStar_Pervasives_Native.Some (m) when (module_is_open env m) -> begin
((ids), ([]))
end
| uu____4542 -> begin
(do_shorten env ids)
end))
end
| uu____4545 -> begin
(do_shorten env ids)
end))))


let resolve_in_open_namespaces'' : 'a . env  ->  FStar_Ident.lident  ->  exported_id_kind  ->  (local_binding  ->  'a cont_t)  ->  (rec_binding  ->  'a cont_t)  ->  (record_or_dc  ->  'a cont_t)  ->  (FStar_Ident.lident  ->  'a cont_t)  ->  ('a cont_t  ->  FStar_Ident.ident  ->  'a cont_t)  ->  'a FStar_Pervasives_Native.option = (fun env lid eikind k_local_binding k_rec_binding k_record f_module l_default -> (match (lid.FStar_Ident.ns) with
| (uu____4663)::uu____4664 -> begin
(

let uu____4667 = (

let uu____4670 = (

let uu____4671 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in (

let uu____4672 = (FStar_Ident.range_of_lid lid)
in (FStar_Ident.set_lid_range uu____4671 uu____4672)))
in (resolve_module_name env uu____4670 true))
in (match (uu____4667) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (modul) -> begin
(

let uu____4677 = (find_in_module_with_includes eikind f_module Cont_fail env modul lid.FStar_Ident.ident)
in (option_of_cont (fun uu____4681 -> FStar_Pervasives_Native.None) uu____4677))
end))
end
| [] -> begin
(try_lookup_id'' env lid.FStar_Ident.ident eikind k_local_binding k_rec_binding k_record f_module l_default)
end))


let cont_of_option : 'a . 'a cont_t  ->  'a FStar_Pervasives_Native.option  ->  'a cont_t = (fun k_none uu___184_4705 -> (match (uu___184_4705) with
| FStar_Pervasives_Native.Some (v1) -> begin
Cont_ok (v1)
end
| FStar_Pervasives_Native.None -> begin
k_none
end))


let resolve_in_open_namespaces' : 'a . env  ->  FStar_Ident.lident  ->  (local_binding  ->  'a FStar_Pervasives_Native.option)  ->  (rec_binding  ->  'a FStar_Pervasives_Native.option)  ->  (FStar_Ident.lident  ->  (FStar_Syntax_Syntax.sigelt * Prims.bool)  ->  'a FStar_Pervasives_Native.option)  ->  'a FStar_Pervasives_Native.option = (fun env lid k_local_binding k_rec_binding k_global_def -> (

let k_global_def' = (fun k lid1 def -> (

let uu____4826 = (k_global_def lid1 def)
in (cont_of_option k uu____4826)))
in (

let f_module = (fun lid' -> (

let k = Cont_ignore
in (find_in_module env lid' (k_global_def' k) k)))
in (

let l_default = (fun k i -> (lookup_default_id env i (k_global_def' k) k))
in (resolve_in_open_namespaces'' env lid Exported_id_term_type (fun l -> (

let uu____4862 = (k_local_binding l)
in (cont_of_option Cont_fail uu____4862))) (fun r -> (

let uu____4868 = (k_rec_binding r)
in (cont_of_option Cont_fail uu____4868))) (fun uu____4872 -> Cont_ignore) f_module l_default)))))


let fv_qual_of_se : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option = (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (uu____4883, uu____4884, uu____4885, l, uu____4887, uu____4888) -> begin
(

let qopt = (FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals (fun uu___185_4901 -> (match (uu___185_4901) with
| FStar_Syntax_Syntax.RecordConstructor (uu____4904, fs) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (((l), (fs))))
end
| uu____4916 -> begin
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
| FStar_Syntax_Syntax.Sig_declare_typ (uu____4922, uu____4923, uu____4924) -> begin
FStar_Pervasives_Native.None
end
| uu____4925 -> begin
FStar_Pervasives_Native.None
end))


let lb_fv : FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.fv = (fun lbs lid -> (

let uu____4941 = (FStar_Util.find_map lbs (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let uu____4949 = (FStar_Syntax_Syntax.fv_eq_lid fv lid)
in (match (uu____4949) with
| true -> begin
FStar_Pervasives_Native.Some (fv)
end
| uu____4954 -> begin
FStar_Pervasives_Native.None
end)))))
in (FStar_All.pipe_right uu____4941 FStar_Util.must)))


let ns_of_lid_equals : FStar_Ident.lident  ->  FStar_Ident.lident  ->  Prims.bool = (fun lid ns -> ((

let uu____4972 = (

let uu____4973 = (FStar_Ident.ids_of_lid ns)
in (FStar_List.length uu____4973))
in (Prims.op_Equality (FStar_List.length lid.FStar_Ident.ns) uu____4972)) && (

let uu____4981 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in (FStar_Ident.lid_equals uu____4981 ns))))


let delta_depth_of_declaration : FStar_Ident.lident  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.delta_depth = (fun lid quals -> (

let dd = (

let uu____4998 = ((FStar_Syntax_Util.is_primop_lid lid) || (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___186_5005 -> (match (uu___186_5005) with
| FStar_Syntax_Syntax.Projector (uu____5007) -> begin
true
end
| FStar_Syntax_Syntax.Discriminator (uu____5013) -> begin
true
end
| uu____5015 -> begin
false
end)))))
in (match (uu____4998) with
| true -> begin
FStar_Syntax_Syntax.delta_equational
end
| uu____5018 -> begin
FStar_Syntax_Syntax.delta_constant
end))
in (

let uu____5020 = ((FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___187_5026 -> (match (uu___187_5026) with
| FStar_Syntax_Syntax.Abstract -> begin
true
end
| uu____5029 -> begin
false
end)))) || ((FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___188_5035 -> (match (uu___188_5035) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| uu____5038 -> begin
false
end)))) && (

let uu____5041 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___189_5047 -> (match (uu___189_5047) with
| FStar_Syntax_Syntax.New -> begin
true
end
| uu____5050 -> begin
false
end))))
in (not (uu____5041)))))
in (match (uu____5020) with
| true -> begin
FStar_Syntax_Syntax.Delta_abstract (dd)
end
| uu____5053 -> begin
dd
end))))


let try_lookup_name : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  foundname FStar_Pervasives_Native.option = (fun any_val exclude_interf env lid -> (

let occurrence_range = (FStar_Ident.range_of_lid lid)
in (

let k_global_def = (fun source_lid uu___192_5102 -> (match (uu___192_5102) with
| (uu____5110, true) when exclude_interf -> begin
FStar_Pervasives_Native.None
end
| (se, uu____5114) -> begin
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____5119) -> begin
(

let uu____5136 = (

let uu____5137 = (

let uu____5144 = (FStar_Syntax_Syntax.fvar source_lid FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in ((uu____5144), (se.FStar_Syntax_Syntax.sigattrs)))
in Term_name (uu____5137))
in FStar_Pervasives_Native.Some (uu____5136))
end
| FStar_Syntax_Syntax.Sig_datacon (uu____5147) -> begin
(

let uu____5163 = (

let uu____5164 = (

let uu____5171 = (

let uu____5172 = (fv_qual_of_se se)
in (FStar_Syntax_Syntax.fvar source_lid FStar_Syntax_Syntax.delta_constant uu____5172))
in ((uu____5171), (se.FStar_Syntax_Syntax.sigattrs)))
in Term_name (uu____5164))
in FStar_Pervasives_Native.Some (uu____5163))
end
| FStar_Syntax_Syntax.Sig_let ((uu____5177, lbs), uu____5179) -> begin
(

let fv = (lb_fv lbs source_lid)
in (

let uu____5191 = (

let uu____5192 = (

let uu____5199 = (FStar_Syntax_Syntax.fvar source_lid fv.FStar_Syntax_Syntax.fv_delta fv.FStar_Syntax_Syntax.fv_qual)
in ((uu____5199), (se.FStar_Syntax_Syntax.sigattrs)))
in Term_name (uu____5192))
in FStar_Pervasives_Native.Some (uu____5191)))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid1, uu____5203, uu____5204) -> begin
(

let quals = se.FStar_Syntax_Syntax.sigquals
in (

let uu____5208 = (any_val || (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___190_5214 -> (match (uu___190_5214) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| uu____5217 -> begin
false
end)))))
in (match (uu____5208) with
| true -> begin
(

let lid2 = (

let uu____5223 = (FStar_Ident.range_of_lid source_lid)
in (FStar_Ident.set_lid_range lid1 uu____5223))
in (

let dd = (delta_depth_of_declaration lid2 quals)
in (

let uu____5225 = (FStar_Util.find_map quals (fun uu___191_5230 -> (match (uu___191_5230) with
| FStar_Syntax_Syntax.Reflectable (refl_monad) -> begin
FStar_Pervasives_Native.Some (refl_monad)
end
| uu____5234 -> begin
FStar_Pervasives_Native.None
end)))
in (match (uu____5225) with
| FStar_Pervasives_Native.Some (refl_monad) -> begin
(

let refl_const = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (refl_monad))) FStar_Pervasives_Native.None occurrence_range)
in FStar_Pervasives_Native.Some (Term_name (((refl_const), (se.FStar_Syntax_Syntax.sigattrs)))))
end
| uu____5243 -> begin
(

let uu____5246 = (

let uu____5247 = (

let uu____5254 = (

let uu____5255 = (fv_qual_of_se se)
in (FStar_Syntax_Syntax.fvar lid2 dd uu____5255))
in ((uu____5254), (se.FStar_Syntax_Syntax.sigattrs)))
in Term_name (uu____5247))
in FStar_Pervasives_Native.Some (uu____5246))
end))))
end
| uu____5260 -> begin
FStar_Pervasives_Native.None
end)))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (ne) -> begin
(

let uu____5263 = (

let uu____5264 = (

let uu____5269 = (

let uu____5270 = (FStar_Ident.range_of_lid source_lid)
in (FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname uu____5270))
in ((se), (uu____5269)))
in Eff_name (uu____5264))
in FStar_Pervasives_Native.Some (uu____5263))
end
| FStar_Syntax_Syntax.Sig_new_effect (ne) -> begin
(

let uu____5272 = (

let uu____5273 = (

let uu____5278 = (

let uu____5279 = (FStar_Ident.range_of_lid source_lid)
in (FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname uu____5279))
in ((se), (uu____5278)))
in Eff_name (uu____5273))
in FStar_Pervasives_Native.Some (uu____5272))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (uu____5280) -> begin
FStar_Pervasives_Native.Some (Eff_name (((se), (source_lid))))
end
| FStar_Syntax_Syntax.Sig_splice (lids, t) -> begin
(

let uu____5299 = (

let uu____5300 = (

let uu____5307 = (FStar_Syntax_Syntax.fvar source_lid (FStar_Syntax_Syntax.Delta_constant_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None)
in ((uu____5307), ([])))
in Term_name (uu____5300))
in FStar_Pervasives_Native.Some (uu____5299))
end
| uu____5311 -> begin
FStar_Pervasives_Native.None
end)
end))
in (

let k_local_binding = (fun r -> (

let t = (

let uu____5329 = (FStar_Ident.range_of_lid lid)
in (found_local_binding uu____5329 r))
in FStar_Pervasives_Native.Some (Term_name (((t), ([]))))))
in (

let k_rec_binding = (fun uu____5345 -> (match (uu____5345) with
| (id1, l, dd) -> begin
(

let uu____5357 = (

let uu____5358 = (

let uu____5365 = (

let uu____5366 = (

let uu____5367 = (FStar_Ident.range_of_lid lid)
in (FStar_Ident.set_lid_range l uu____5367))
in (FStar_Syntax_Syntax.fvar uu____5366 dd FStar_Pervasives_Native.None))
in ((uu____5365), ([])))
in Term_name (uu____5358))
in FStar_Pervasives_Native.Some (uu____5357))
end))
in (

let found_unmangled = (match (lid.FStar_Ident.ns) with
| [] -> begin
(

let uu____5375 = (unmangleOpName lid.FStar_Ident.ident)
in (match (uu____5375) with
| FStar_Pervasives_Native.Some (t) -> begin
FStar_Pervasives_Native.Some (Term_name (((t), ([]))))
end
| uu____5383 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____5386 -> begin
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

let uu____5424 = (try_lookup_name true exclude_interf env lid)
in (match (uu____5424) with
| FStar_Pervasives_Native.Some (Eff_name (o, l)) -> begin
FStar_Pervasives_Native.Some (((o), (l)))
end
| uu____5440 -> begin
FStar_Pervasives_Native.None
end)))


let try_lookup_effect_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident FStar_Pervasives_Native.option = (fun env l -> (

let uu____5460 = (try_lookup_effect_name' (not (env.iface)) env l)
in (match (uu____5460) with
| FStar_Pervasives_Native.Some (o, l1) -> begin
FStar_Pervasives_Native.Some (l1)
end
| uu____5475 -> begin
FStar_Pervasives_Native.None
end)))


let try_lookup_effect_name_and_attributes : env  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.cflag Prims.list) FStar_Pervasives_Native.option = (fun env l -> (

let uu____5501 = (try_lookup_effect_name' (not (env.iface)) env l)
in (match (uu____5501) with
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect (ne); FStar_Syntax_Syntax.sigrng = uu____5517; FStar_Syntax_Syntax.sigquals = uu____5518; FStar_Syntax_Syntax.sigmeta = uu____5519; FStar_Syntax_Syntax.sigattrs = uu____5520}, l1) -> begin
FStar_Pervasives_Native.Some (((l1), (ne.FStar_Syntax_Syntax.cattributes)))
end
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect_for_free (ne); FStar_Syntax_Syntax.sigrng = uu____5539; FStar_Syntax_Syntax.sigquals = uu____5540; FStar_Syntax_Syntax.sigmeta = uu____5541; FStar_Syntax_Syntax.sigattrs = uu____5542}, l1) -> begin
FStar_Pervasives_Native.Some (((l1), (ne.FStar_Syntax_Syntax.cattributes)))
end
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_effect_abbrev (uu____5560, uu____5561, uu____5562, uu____5563, cattributes); FStar_Syntax_Syntax.sigrng = uu____5565; FStar_Syntax_Syntax.sigquals = uu____5566; FStar_Syntax_Syntax.sigmeta = uu____5567; FStar_Syntax_Syntax.sigattrs = uu____5568}, l1) -> begin
FStar_Pervasives_Native.Some (((l1), (cattributes)))
end
| uu____5590 -> begin
FStar_Pervasives_Native.None
end)))


let try_lookup_effect_defn : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl FStar_Pervasives_Native.option = (fun env l -> (

let uu____5616 = (try_lookup_effect_name' (not (env.iface)) env l)
in (match (uu____5616) with
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect (ne); FStar_Syntax_Syntax.sigrng = uu____5626; FStar_Syntax_Syntax.sigquals = uu____5627; FStar_Syntax_Syntax.sigmeta = uu____5628; FStar_Syntax_Syntax.sigattrs = uu____5629}, uu____5630) -> begin
FStar_Pervasives_Native.Some (ne)
end
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect_for_free (ne); FStar_Syntax_Syntax.sigrng = uu____5640; FStar_Syntax_Syntax.sigquals = uu____5641; FStar_Syntax_Syntax.sigmeta = uu____5642; FStar_Syntax_Syntax.sigattrs = uu____5643}, uu____5644) -> begin
FStar_Pervasives_Native.Some (ne)
end
| uu____5653 -> begin
FStar_Pervasives_Native.None
end)))


let is_effect_name : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let uu____5672 = (try_lookup_effect_name env lid)
in (match (uu____5672) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (uu____5677) -> begin
true
end)))


let try_lookup_root_effect_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident FStar_Pervasives_Native.option = (fun env l -> (

let uu____5692 = (try_lookup_effect_name' (not (env.iface)) env l)
in (match (uu____5692) with
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_effect_abbrev (l', uu____5702, uu____5703, uu____5704, uu____5705); FStar_Syntax_Syntax.sigrng = uu____5706; FStar_Syntax_Syntax.sigquals = uu____5707; FStar_Syntax_Syntax.sigmeta = uu____5708; FStar_Syntax_Syntax.sigattrs = uu____5709}, uu____5710) -> begin
(

let rec aux = (fun new_name -> (

let uu____5731 = (FStar_Util.smap_try_find (sigmap env) new_name.FStar_Ident.str)
in (match (uu____5731) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (s, uu____5752) -> begin
(match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_new_effect_for_free (ne) -> begin
(

let uu____5763 = (

let uu____5764 = (FStar_Ident.range_of_lid l)
in (FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname uu____5764))
in FStar_Pervasives_Native.Some (uu____5763))
end
| FStar_Syntax_Syntax.Sig_new_effect (ne) -> begin
(

let uu____5766 = (

let uu____5767 = (FStar_Ident.range_of_lid l)
in (FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname uu____5767))
in FStar_Pervasives_Native.Some (uu____5766))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (uu____5768, uu____5769, uu____5770, cmp, uu____5772) -> begin
(

let l'' = (FStar_Syntax_Util.comp_effect_name cmp)
in (aux l''))
end
| uu____5778 -> begin
FStar_Pervasives_Native.None
end)
end)))
in (aux l'))
end
| FStar_Pervasives_Native.Some (uu____5779, l') -> begin
FStar_Pervasives_Native.Some (l')
end
| uu____5785 -> begin
FStar_Pervasives_Native.None
end)))


let lookup_letbinding_quals : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.qualifier Prims.list = (fun env lid -> (

let k_global_def = (fun lid1 uu___193_5824 -> (match (uu___193_5824) with
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (uu____5834, uu____5835, uu____5836); FStar_Syntax_Syntax.sigrng = uu____5837; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = uu____5839; FStar_Syntax_Syntax.sigattrs = uu____5840}, uu____5841) -> begin
FStar_Pervasives_Native.Some (quals)
end
| uu____5850 -> begin
FStar_Pervasives_Native.None
end))
in (

let uu____5858 = (resolve_in_open_namespaces' env lid (fun uu____5866 -> FStar_Pervasives_Native.None) (fun uu____5870 -> FStar_Pervasives_Native.None) k_global_def)
in (match (uu____5858) with
| FStar_Pervasives_Native.Some (quals) -> begin
quals
end
| uu____5880 -> begin
[]
end))))


let try_lookup_module : env  ->  FStar_Ident.path  ->  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option = (fun env path -> (

let uu____5898 = (FStar_List.tryFind (fun uu____5913 -> (match (uu____5913) with
| (mlid, modul) -> begin
(

let uu____5921 = (FStar_Ident.path_of_lid mlid)
in (Prims.op_Equality uu____5921 path))
end)) env.modules)
in (match (uu____5898) with
| FStar_Pervasives_Native.Some (uu____5924, modul) -> begin
FStar_Pervasives_Native.Some (modul)
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end)))


let try_lookup_let : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun env lid -> (

let k_global_def = (fun lid1 uu___194_5964 -> (match (uu___194_5964) with
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let ((uu____5972, lbs), uu____5974); FStar_Syntax_Syntax.sigrng = uu____5975; FStar_Syntax_Syntax.sigquals = uu____5976; FStar_Syntax_Syntax.sigmeta = uu____5977; FStar_Syntax_Syntax.sigattrs = uu____5978}, uu____5979) -> begin
(

let fv = (lb_fv lbs lid1)
in (

let uu____5997 = (FStar_Syntax_Syntax.fvar lid1 fv.FStar_Syntax_Syntax.fv_delta fv.FStar_Syntax_Syntax.fv_qual)
in FStar_Pervasives_Native.Some (uu____5997)))
end
| uu____5998 -> begin
FStar_Pervasives_Native.None
end))
in (resolve_in_open_namespaces' env lid (fun uu____6005 -> FStar_Pervasives_Native.None) (fun uu____6007 -> FStar_Pervasives_Native.None) k_global_def)))


let try_lookup_definition : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun env lid -> (

let k_global_def = (fun lid1 uu___195_6040 -> (match (uu___195_6040) with
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (lbs, uu____6051); FStar_Syntax_Syntax.sigrng = uu____6052; FStar_Syntax_Syntax.sigquals = uu____6053; FStar_Syntax_Syntax.sigmeta = uu____6054; FStar_Syntax_Syntax.sigattrs = uu____6055}, uu____6056) -> begin
(FStar_Util.find_map (FStar_Pervasives_Native.snd lbs) (fun lb -> (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv lid1) -> begin
FStar_Pervasives_Native.Some (lb.FStar_Syntax_Syntax.lbdef)
end
| uu____6082 -> begin
FStar_Pervasives_Native.None
end)))
end
| uu____6089 -> begin
FStar_Pervasives_Native.None
end))
in (resolve_in_open_namespaces' env lid (fun uu____6100 -> FStar_Pervasives_Native.None) (fun uu____6104 -> FStar_Pervasives_Native.None) k_global_def)))


let empty_include_smap : FStar_Ident.lident Prims.list FStar_ST.ref FStar_Util.smap = (new_sigmap ())


let empty_exported_id_smap : exported_id_set FStar_Util.smap = (new_sigmap ())


let try_lookup_lid' : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.attribute Prims.list) FStar_Pervasives_Native.option = (fun any_val exclude_interface env lid -> (

let uu____6164 = (try_lookup_name any_val exclude_interface env lid)
in (match (uu____6164) with
| FStar_Pervasives_Native.Some (Term_name (e, attrs)) -> begin
FStar_Pervasives_Native.Some (((e), (attrs)))
end
| uu____6189 -> begin
FStar_Pervasives_Native.None
end)))


let drop_attributes : (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.attribute Prims.list) FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun x -> (match (x) with
| FStar_Pervasives_Native.Some (t, uu____6227) -> begin
FStar_Pervasives_Native.Some (t)
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end))


let try_lookup_lid_with_attributes : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.attribute Prims.list) FStar_Pervasives_Native.option = (fun env l -> (try_lookup_lid' env.iface false env l))


let try_lookup_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun env l -> (

let uu____6285 = (try_lookup_lid_with_attributes env l)
in (FStar_All.pipe_right uu____6285 drop_attributes)))


let resolve_to_fully_qualified_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident FStar_Pervasives_Native.option = (fun env l -> (

let uu____6317 = (try_lookup_lid env l)
in (match (uu____6317) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (e) -> begin
(

let uu____6323 = (

let uu____6324 = (FStar_Syntax_Subst.compress e)
in uu____6324.FStar_Syntax_Syntax.n)
in (match (uu____6323) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
FStar_Pervasives_Native.Some (fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end
| uu____6330 -> begin
FStar_Pervasives_Native.None
end))
end)))


let shorten_lid' : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (

let uu____6342 = (shorten_module_path env lid.FStar_Ident.ns true)
in (match (uu____6342) with
| (uu____6352, short) -> begin
(FStar_Ident.lid_of_ns_and_id short lid.FStar_Ident.ident)
end)))


let shorten_lid : env  ->  FStar_Ident.lid  ->  FStar_Ident.lid = (fun env lid -> (match (env.curmodule) with
| FStar_Pervasives_Native.None -> begin
(shorten_lid' env lid)
end
| uu____6373 -> begin
(

let lid_without_ns = (FStar_Ident.lid_of_ns_and_id [] lid.FStar_Ident.ident)
in (

let uu____6377 = (resolve_to_fully_qualified_name env lid_without_ns)
in (match (uu____6377) with
| FStar_Pervasives_Native.Some (lid') when (Prims.op_Equality lid'.FStar_Ident.str lid.FStar_Ident.str) -> begin
lid_without_ns
end
| uu____6382 -> begin
(shorten_lid' env lid)
end)))
end))


let try_lookup_lid_with_attributes_no_resolve : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.attribute Prims.list) FStar_Pervasives_Native.option = (fun env l -> (

let env' = (

let uu___216_6413 = env
in {curmodule = uu___216_6413.curmodule; curmonad = uu___216_6413.curmonad; modules = uu___216_6413.modules; scope_mods = []; exported_ids = empty_exported_id_smap; trans_exported_ids = uu___216_6413.trans_exported_ids; includes = empty_include_smap; sigaccum = uu___216_6413.sigaccum; sigmap = uu___216_6413.sigmap; iface = uu___216_6413.iface; admitted_iface = uu___216_6413.admitted_iface; expect_typ = uu___216_6413.expect_typ; docs = uu___216_6413.docs; remaining_iface_decls = uu___216_6413.remaining_iface_decls; syntax_only = uu___216_6413.syntax_only; ds_hooks = uu___216_6413.ds_hooks; dep_graph = uu___216_6413.dep_graph})
in (try_lookup_lid_with_attributes env' l)))


let try_lookup_lid_no_resolve : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun env l -> (

let uu____6429 = (try_lookup_lid_with_attributes_no_resolve env l)
in (FStar_All.pipe_right uu____6429 drop_attributes)))


let try_lookup_doc : env  ->  FStar_Ident.lid  ->  FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option = (fun env l -> (FStar_Util.smap_try_find env.docs l.FStar_Ident.str))


let try_lookup_datacon : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.fv FStar_Pervasives_Native.option = (fun env lid -> (

let k_global_def = (fun lid1 se -> (match (se) with
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (uu____6499, uu____6500, uu____6501); FStar_Syntax_Syntax.sigrng = uu____6502; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = uu____6504; FStar_Syntax_Syntax.sigattrs = uu____6505}, uu____6506) -> begin
(

let uu____6513 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___196_6519 -> (match (uu___196_6519) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| uu____6522 -> begin
false
end))))
in (match (uu____6513) with
| true -> begin
(

let uu____6527 = (FStar_Syntax_Syntax.lid_as_fv lid1 FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in FStar_Pervasives_Native.Some (uu____6527))
end
| uu____6528 -> begin
FStar_Pervasives_Native.None
end))
end
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (uu____6530); FStar_Syntax_Syntax.sigrng = uu____6531; FStar_Syntax_Syntax.sigquals = uu____6532; FStar_Syntax_Syntax.sigmeta = uu____6533; FStar_Syntax_Syntax.sigattrs = uu____6534}, uu____6535) -> begin
(

let qual1 = (fv_qual_of_se (FStar_Pervasives_Native.fst se))
in (

let uu____6561 = (FStar_Syntax_Syntax.lid_as_fv lid1 FStar_Syntax_Syntax.delta_constant qual1)
in FStar_Pervasives_Native.Some (uu____6561)))
end
| uu____6562 -> begin
FStar_Pervasives_Native.None
end))
in (resolve_in_open_namespaces' env lid (fun uu____6569 -> FStar_Pervasives_Native.None) (fun uu____6571 -> FStar_Pervasives_Native.None) k_global_def)))


let find_all_datacons : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.list FStar_Pervasives_Native.option = (fun env lid -> (

let k_global_def = (fun lid1 uu___197_6606 -> (match (uu___197_6606) with
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (uu____6616, uu____6617, uu____6618, uu____6619, datas, uu____6621); FStar_Syntax_Syntax.sigrng = uu____6622; FStar_Syntax_Syntax.sigquals = uu____6623; FStar_Syntax_Syntax.sigmeta = uu____6624; FStar_Syntax_Syntax.sigattrs = uu____6625}, uu____6626) -> begin
FStar_Pervasives_Native.Some (datas)
end
| uu____6643 -> begin
FStar_Pervasives_Native.None
end))
in (resolve_in_open_namespaces' env lid (fun uu____6654 -> FStar_Pervasives_Native.None) (fun uu____6658 -> FStar_Pervasives_Native.None) k_global_def)))


let record_cache_aux_with_filter : ((((unit  ->  unit) * (unit  ->  unit)) * (((unit  ->  (Prims.int * unit)) * (Prims.int FStar_Pervasives_Native.option  ->  unit)) * ((unit  ->  record_or_dc Prims.list) * (record_or_dc  ->  unit)))) * (unit  ->  unit)) = (

let record_cache = (FStar_Util.mk_ref (([])::[]))
in (

let push1 = (fun uu____6737 -> (

let uu____6738 = (

let uu____6743 = (

let uu____6746 = (FStar_ST.op_Bang record_cache)
in (FStar_List.hd uu____6746))
in (

let uu____6802 = (FStar_ST.op_Bang record_cache)
in (uu____6743)::uu____6802))
in (FStar_ST.op_Colon_Equals record_cache uu____6738)))
in (

let pop1 = (fun uu____6912 -> (

let uu____6913 = (

let uu____6918 = (FStar_ST.op_Bang record_cache)
in (FStar_List.tl uu____6918))
in (FStar_ST.op_Colon_Equals record_cache uu____6913)))
in (

let snapshot1 = (fun uu____7033 -> (FStar_Common.snapshot push1 record_cache ()))
in (

let rollback1 = (fun depth -> (FStar_Common.rollback pop1 record_cache depth))
in (

let peek1 = (fun uu____7101 -> (

let uu____7102 = (FStar_ST.op_Bang record_cache)
in (FStar_List.hd uu____7102)))
in (

let insert = (fun r -> (

let uu____7164 = (

let uu____7169 = (

let uu____7172 = (peek1 ())
in (r)::uu____7172)
in (

let uu____7175 = (

let uu____7180 = (FStar_ST.op_Bang record_cache)
in (FStar_List.tl uu____7180))
in (uu____7169)::uu____7175))
in (FStar_ST.op_Colon_Equals record_cache uu____7164)))
in (

let filter1 = (fun uu____7292 -> (

let rc = (peek1 ())
in (

let filtered = (FStar_List.filter (fun r -> (not (r.is_private_or_abstract))) rc)
in (

let uu____7301 = (

let uu____7306 = (

let uu____7311 = (FStar_ST.op_Bang record_cache)
in (FStar_List.tl uu____7311))
in (filtered)::uu____7306)
in (FStar_ST.op_Colon_Equals record_cache uu____7301)))))
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
| FStar_Syntax_Syntax.Sig_bundle (sigs, uu____8303) -> begin
(

let is_record = (FStar_Util.for_some (fun uu___198_8322 -> (match (uu___198_8322) with
| FStar_Syntax_Syntax.RecordType (uu____8324) -> begin
true
end
| FStar_Syntax_Syntax.RecordConstructor (uu____8334) -> begin
true
end
| uu____8344 -> begin
false
end)))
in (

let find_dc = (fun dc -> (FStar_All.pipe_right sigs (FStar_Util.find_opt (fun uu___199_8369 -> (match (uu___199_8369) with
| {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (lid, uu____8372, uu____8373, uu____8374, uu____8375, uu____8376); FStar_Syntax_Syntax.sigrng = uu____8377; FStar_Syntax_Syntax.sigquals = uu____8378; FStar_Syntax_Syntax.sigmeta = uu____8379; FStar_Syntax_Syntax.sigattrs = uu____8380} -> begin
(FStar_Ident.lid_equals dc lid)
end
| uu____8391 -> begin
false
end)))))
in (FStar_All.pipe_right sigs (FStar_List.iter (fun uu___200_8427 -> (match (uu___200_8427) with
| {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (typename, univs1, parms, uu____8431, uu____8432, (dc)::[]); FStar_Syntax_Syntax.sigrng = uu____8434; FStar_Syntax_Syntax.sigquals = typename_quals; FStar_Syntax_Syntax.sigmeta = uu____8436; FStar_Syntax_Syntax.sigattrs = uu____8437} -> begin
(

let uu____8448 = (

let uu____8449 = (find_dc dc)
in (FStar_All.pipe_left FStar_Util.must uu____8449))
in (match (uu____8448) with
| {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (constrname, uu____8455, t, uu____8457, uu____8458, uu____8459); FStar_Syntax_Syntax.sigrng = uu____8460; FStar_Syntax_Syntax.sigquals = uu____8461; FStar_Syntax_Syntax.sigmeta = uu____8462; FStar_Syntax_Syntax.sigattrs = uu____8463} -> begin
(

let uu____8474 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____8474) with
| (formals, uu____8490) -> begin
(

let is_rec = (is_record typename_quals)
in (

let formals' = (FStar_All.pipe_right formals (FStar_List.collect (fun uu____8544 -> (match (uu____8544) with
| (x, q) -> begin
(

let uu____8557 = ((FStar_Syntax_Syntax.is_null_bv x) || (is_rec && (FStar_Syntax_Syntax.is_implicit q)))
in (match (uu____8557) with
| true -> begin
[]
end
| uu____8570 -> begin
(((x), (q)))::[]
end))
end))))
in (

let fields' = (FStar_All.pipe_right formals' (FStar_List.map (fun uu____8612 -> (match (uu____8612) with
| (x, q) -> begin
((x.FStar_Syntax_Syntax.ppname), (x.FStar_Syntax_Syntax.sort))
end))))
in (

let fields = fields'
in (

let record = {typename = typename; constrname = constrname.FStar_Ident.ident; parms = parms; fields = fields; is_private_or_abstract = ((FStar_List.contains FStar_Syntax_Syntax.Private typename_quals) || (FStar_List.contains FStar_Syntax_Syntax.Abstract typename_quals)); is_record = is_rec}
in ((

let uu____8636 = (

let uu____8639 = (FStar_ST.op_Bang new_globs)
in (Record_or_dc (record))::uu____8639)
in (FStar_ST.op_Colon_Equals new_globs uu____8636));
(match (()) with
| () -> begin
((

let add_field = (fun uu____8742 -> (match (uu____8742) with
| (id1, uu____8748) -> begin
(

let modul = (

let uu____8751 = (FStar_Ident.lid_of_ids constrname.FStar_Ident.ns)
in uu____8751.FStar_Ident.str)
in (

let uu____8752 = (get_exported_id_set e modul)
in (match (uu____8752) with
| FStar_Pervasives_Native.Some (my_ex) -> begin
(

let my_exported_ids = (my_ex Exported_id_field)
in ((

let uu____8786 = (

let uu____8787 = (FStar_ST.op_Bang my_exported_ids)
in (FStar_Util.set_add id1.FStar_Ident.idText uu____8787))
in (FStar_ST.op_Colon_Equals my_exported_ids uu____8786));
(match (()) with
| () -> begin
(

let projname = (

let uu____8876 = (

let uu____8877 = (FStar_Syntax_Util.mk_field_projector_name_from_ident constrname id1)
in uu____8877.FStar_Ident.ident)
in uu____8876.FStar_Ident.idText)
in (

let uu____8879 = (

let uu____8880 = (FStar_ST.op_Bang my_exported_ids)
in (FStar_Util.set_add projname uu____8880))
in (FStar_ST.op_Colon_Equals my_exported_ids uu____8879)))
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
| uu____8976 -> begin
()
end))
end
| uu____8977 -> begin
()
end))))))
end
| uu____8978 -> begin
()
end))


let try_lookup_record_or_dc_by_field_name : env  ->  FStar_Ident.lident  ->  record_or_dc FStar_Pervasives_Native.option = (fun env fieldname -> (

let find_in_cache = (fun fieldname1 -> (

let uu____9000 = ((fieldname1.FStar_Ident.ns), (fieldname1.FStar_Ident.ident))
in (match (uu____9000) with
| (ns, id1) -> begin
(

let uu____9017 = (peek_record_cache ())
in (FStar_Util.find_map uu____9017 (fun record -> (

let uu____9023 = (find_in_record ns id1 record (fun r -> Cont_ok (r)))
in (option_of_cont (fun uu____9029 -> FStar_Pervasives_Native.None) uu____9023)))))
end)))
in (resolve_in_open_namespaces'' env fieldname Exported_id_field (fun uu____9031 -> Cont_ignore) (fun uu____9033 -> Cont_ignore) (fun r -> Cont_ok (r)) (fun fn -> (

let uu____9039 = (find_in_cache fn)
in (cont_of_option Cont_ignore uu____9039))) (fun k uu____9045 -> k))))


let try_lookup_record_by_field_name : env  ->  FStar_Ident.lident  ->  record_or_dc FStar_Pervasives_Native.option = (fun env fieldname -> (

let uu____9061 = (try_lookup_record_or_dc_by_field_name env fieldname)
in (match (uu____9061) with
| FStar_Pervasives_Native.Some (r) when r.is_record -> begin
FStar_Pervasives_Native.Some (r)
end
| uu____9067 -> begin
FStar_Pervasives_Native.None
end)))


let belongs_to_record : env  ->  FStar_Ident.lident  ->  record_or_dc  ->  Prims.bool = (fun env lid record -> (

let uu____9087 = (try_lookup_record_by_field_name env lid)
in (match (uu____9087) with
| FStar_Pervasives_Native.Some (record') when (

let uu____9092 = (

let uu____9094 = (FStar_Ident.path_of_ns record.typename.FStar_Ident.ns)
in (FStar_Ident.text_of_path uu____9094))
in (

let uu____9095 = (

let uu____9097 = (FStar_Ident.path_of_ns record'.typename.FStar_Ident.ns)
in (FStar_Ident.text_of_path uu____9097))
in (Prims.op_Equality uu____9092 uu____9095))) -> begin
(

let uu____9099 = (find_in_record record.typename.FStar_Ident.ns lid.FStar_Ident.ident record (fun uu____9103 -> Cont_ok (())))
in (match (uu____9099) with
| Cont_ok (uu____9105) -> begin
true
end
| uu____9107 -> begin
false
end))
end
| uu____9111 -> begin
false
end)))


let try_lookup_dc_by_field_name : env  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * Prims.bool) FStar_Pervasives_Native.option = (fun env fieldname -> (

let uu____9133 = (try_lookup_record_or_dc_by_field_name env fieldname)
in (match (uu____9133) with
| FStar_Pervasives_Native.Some (r) -> begin
(

let uu____9144 = (

let uu____9150 = (

let uu____9151 = (FStar_Ident.lid_of_ids (FStar_List.append r.typename.FStar_Ident.ns ((r.constrname)::[])))
in (

let uu____9152 = (FStar_Ident.range_of_lid fieldname)
in (FStar_Ident.set_lid_range uu____9151 uu____9152)))
in ((uu____9150), (r.is_record)))
in FStar_Pervasives_Native.Some (uu____9144))
end
| uu____9159 -> begin
FStar_Pervasives_Native.None
end)))


let string_set_ref_new : unit  ->  Prims.string FStar_Util.set FStar_ST.ref = (fun uu____9188 -> (

let uu____9189 = (FStar_Util.new_set FStar_Util.compare)
in (FStar_Util.mk_ref uu____9189)))


let exported_id_set_new : unit  ->  exported_id_kind  ->  Prims.string FStar_Util.set FStar_ST.ref = (fun uu____9221 -> (

let term_type_set = (string_set_ref_new ())
in (

let field_set = (string_set_ref_new ())
in (fun uu___201_9234 -> (match (uu___201_9234) with
| Exported_id_term_type -> begin
term_type_set
end
| Exported_id_field -> begin
field_set
end)))))


let unique : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  Prims.bool = (fun any_val exclude_interface env lid -> (

let filter_scope_mods = (fun uu___202_9294 -> (match (uu___202_9294) with
| Rec_binding (uu____9296) -> begin
true
end
| uu____9298 -> begin
false
end))
in (

let this_env = (

let uu___217_9301 = env
in (

let uu____9302 = (FStar_List.filter filter_scope_mods env.scope_mods)
in {curmodule = uu___217_9301.curmodule; curmonad = uu___217_9301.curmonad; modules = uu___217_9301.modules; scope_mods = uu____9302; exported_ids = empty_exported_id_smap; trans_exported_ids = uu___217_9301.trans_exported_ids; includes = empty_include_smap; sigaccum = uu___217_9301.sigaccum; sigmap = uu___217_9301.sigmap; iface = uu___217_9301.iface; admitted_iface = uu___217_9301.admitted_iface; expect_typ = uu___217_9301.expect_typ; docs = uu___217_9301.docs; remaining_iface_decls = uu___217_9301.remaining_iface_decls; syntax_only = uu___217_9301.syntax_only; ds_hooks = uu___217_9301.ds_hooks; dep_graph = uu___217_9301.dep_graph}))
in (

let uu____9305 = (try_lookup_lid' any_val exclude_interface this_env lid)
in (match (uu____9305) with
| FStar_Pervasives_Native.None -> begin
true
end
| FStar_Pervasives_Native.Some (uu____9322) -> begin
false
end)))))


let push_scope_mod : env  ->  scope_mod  ->  env = (fun env scope_mod -> (

let uu___218_9347 = env
in {curmodule = uu___218_9347.curmodule; curmonad = uu___218_9347.curmonad; modules = uu___218_9347.modules; scope_mods = (scope_mod)::env.scope_mods; exported_ids = uu___218_9347.exported_ids; trans_exported_ids = uu___218_9347.trans_exported_ids; includes = uu___218_9347.includes; sigaccum = uu___218_9347.sigaccum; sigmap = uu___218_9347.sigmap; iface = uu___218_9347.iface; admitted_iface = uu___218_9347.admitted_iface; expect_typ = uu___218_9347.expect_typ; docs = uu___218_9347.docs; remaining_iface_decls = uu___218_9347.remaining_iface_decls; syntax_only = uu___218_9347.syntax_only; ds_hooks = uu___218_9347.ds_hooks; dep_graph = uu___218_9347.dep_graph}))


let push_bv : env  ->  FStar_Ident.ident  ->  (env * FStar_Syntax_Syntax.bv) = (fun env x -> (

let bv = (FStar_Syntax_Syntax.gen_bv x.FStar_Ident.idText (FStar_Pervasives_Native.Some (x.FStar_Ident.idRange)) FStar_Syntax_Syntax.tun)
in (((push_scope_mod env (Local_binding (((x), (bv)))))), (bv))))


let push_top_level_rec_binding : env  ->  FStar_Ident.ident  ->  FStar_Syntax_Syntax.delta_depth  ->  env = (fun env x dd -> (

let l = (qualify env x)
in (

let uu____9381 = ((unique false true env l) || (FStar_Options.interactive ()))
in (match (uu____9381) with
| true -> begin
(push_scope_mod env (Rec_binding (((x), (l), (dd)))))
end
| uu____9386 -> begin
(

let uu____9388 = (FStar_Ident.range_of_lid l)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_DuplicateTopLevelNames), ((Prims.strcat "Duplicate top-level names " l.FStar_Ident.str))) uu____9388))
end))))


let push_sigelt' : Prims.bool  ->  env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun fail_on_dup env s -> (

let err = (fun l -> (

let sopt = (FStar_Util.smap_try_find (sigmap env) l.FStar_Ident.str)
in (

let r = (match (sopt) with
| FStar_Pervasives_Native.Some (se, uu____9432) -> begin
(

let uu____9440 = (FStar_Util.find_opt (FStar_Ident.lid_equals l) (FStar_Syntax_Util.lids_of_sigelt se))
in (match (uu____9440) with
| FStar_Pervasives_Native.Some (l1) -> begin
(

let uu____9445 = (FStar_Ident.range_of_lid l1)
in (FStar_All.pipe_left FStar_Range.string_of_range uu____9445))
end
| FStar_Pervasives_Native.None -> begin
"<unknown>"
end))
end
| FStar_Pervasives_Native.None -> begin
"<unknown>"
end)
in (

let uu____9454 = (

let uu____9460 = (

let uu____9462 = (FStar_Ident.text_of_lid l)
in (FStar_Util.format2 "Duplicate top-level names [%s]; previously declared at %s" uu____9462 r))
in ((FStar_Errors.Fatal_DuplicateTopLevelNames), (uu____9460)))
in (

let uu____9466 = (FStar_Ident.range_of_lid l)
in (FStar_Errors.raise_error uu____9454 uu____9466))))))
in (

let globals = (FStar_Util.mk_ref env.scope_mods)
in (

let env1 = (

let uu____9475 = (match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let (uu____9488) -> begin
((false), (true))
end
| FStar_Syntax_Syntax.Sig_bundle (uu____9499) -> begin
((false), (true))
end
| uu____9512 -> begin
((false), (false))
end)
in (match (uu____9475) with
| (any_val, exclude_interface) -> begin
(

let lids = (FStar_Syntax_Util.lids_of_sigelt s)
in (

let uu____9526 = (FStar_Util.find_map lids (fun l -> (

let uu____9532 = (

let uu____9534 = (unique any_val exclude_interface env l)
in (not (uu____9534)))
in (match (uu____9532) with
| true -> begin
FStar_Pervasives_Native.Some (l)
end
| uu____9539 -> begin
FStar_Pervasives_Native.None
end))))
in (match (uu____9526) with
| FStar_Pervasives_Native.Some (l) when fail_on_dup -> begin
(err l)
end
| uu____9542 -> begin
((extract_record env globals s);
(

let uu___219_9568 = env
in {curmodule = uu___219_9568.curmodule; curmonad = uu___219_9568.curmonad; modules = uu___219_9568.modules; scope_mods = uu___219_9568.scope_mods; exported_ids = uu___219_9568.exported_ids; trans_exported_ids = uu___219_9568.trans_exported_ids; includes = uu___219_9568.includes; sigaccum = (s)::env.sigaccum; sigmap = uu___219_9568.sigmap; iface = uu___219_9568.iface; admitted_iface = uu___219_9568.admitted_iface; expect_typ = uu___219_9568.expect_typ; docs = uu___219_9568.docs; remaining_iface_decls = uu___219_9568.remaining_iface_decls; syntax_only = uu___219_9568.syntax_only; ds_hooks = uu___219_9568.ds_hooks; dep_graph = uu___219_9568.dep_graph});
)
end)))
end))
in (

let env2 = (

let uu___220_9570 = env1
in (

let uu____9571 = (FStar_ST.op_Bang globals)
in {curmodule = uu___220_9570.curmodule; curmonad = uu___220_9570.curmonad; modules = uu___220_9570.modules; scope_mods = uu____9571; exported_ids = uu___220_9570.exported_ids; trans_exported_ids = uu___220_9570.trans_exported_ids; includes = uu___220_9570.includes; sigaccum = uu___220_9570.sigaccum; sigmap = uu___220_9570.sigmap; iface = uu___220_9570.iface; admitted_iface = uu___220_9570.admitted_iface; expect_typ = uu___220_9570.expect_typ; docs = uu___220_9570.docs; remaining_iface_decls = uu___220_9570.remaining_iface_decls; syntax_only = uu___220_9570.syntax_only; ds_hooks = uu___220_9570.ds_hooks; dep_graph = uu___220_9570.dep_graph}))
in (

let uu____9619 = (match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____9645) -> begin
(

let uu____9654 = (FStar_List.map (fun se -> (((FStar_Syntax_Util.lids_of_sigelt se)), (se))) ses)
in ((env2), (uu____9654)))
end
| uu____9681 -> begin
((env2), (((((FStar_Syntax_Util.lids_of_sigelt s)), (s)))::[]))
end)
in (match (uu____9619) with
| (env3, lss) -> begin
((FStar_All.pipe_right lss (FStar_List.iter (fun uu____9740 -> (match (uu____9740) with
| (lids, se) -> begin
(FStar_All.pipe_right lids (FStar_List.iter (fun lid -> ((

let uu____9762 = (

let uu____9765 = (FStar_ST.op_Bang globals)
in (Top_level_def (lid.FStar_Ident.ident))::uu____9765)
in (FStar_ST.op_Colon_Equals globals uu____9762));
(match (()) with
| () -> begin
(

let modul = (

let uu____9860 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in uu____9860.FStar_Ident.str)
in ((

let uu____9862 = (get_exported_id_set env3 modul)
in (match (uu____9862) with
| FStar_Pervasives_Native.Some (f) -> begin
(

let my_exported_ids = (f Exported_id_term_type)
in (

let uu____9895 = (

let uu____9896 = (FStar_ST.op_Bang my_exported_ids)
in (FStar_Util.set_add lid.FStar_Ident.ident.FStar_Ident.idText uu____9896))
in (FStar_ST.op_Colon_Equals my_exported_ids uu____9895)))
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

let uu___221_9997 = env3
in (

let uu____9998 = (FStar_ST.op_Bang globals)
in {curmodule = uu___221_9997.curmodule; curmonad = uu___221_9997.curmonad; modules = uu___221_9997.modules; scope_mods = uu____9998; exported_ids = uu___221_9997.exported_ids; trans_exported_ids = uu___221_9997.trans_exported_ids; includes = uu___221_9997.includes; sigaccum = uu___221_9997.sigaccum; sigmap = uu___221_9997.sigmap; iface = uu___221_9997.iface; admitted_iface = uu___221_9997.admitted_iface; expect_typ = uu___221_9997.expect_typ; docs = uu___221_9997.docs; remaining_iface_decls = uu___221_9997.remaining_iface_decls; syntax_only = uu___221_9997.syntax_only; ds_hooks = uu___221_9997.ds_hooks; dep_graph = uu___221_9997.dep_graph}))
in env4);
)
end)))))))


let push_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env se -> (push_sigelt' true env se))


let push_sigelt_force : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env se -> (push_sigelt' false env se))


let push_namespace : env  ->  FStar_Ident.lident  ->  env = (fun env ns -> (

let uu____10081 = (

let uu____10086 = (resolve_module_name env ns false)
in (match (uu____10086) with
| FStar_Pervasives_Native.None -> begin
(

let modules = env.modules
in (

let uu____10101 = (FStar_All.pipe_right modules (FStar_Util.for_some (fun uu____10119 -> (match (uu____10119) with
| (m, uu____10126) -> begin
(

let uu____10127 = (

let uu____10129 = (FStar_Ident.text_of_lid m)
in (Prims.strcat uu____10129 "."))
in (

let uu____10132 = (

let uu____10134 = (FStar_Ident.text_of_lid ns)
in (Prims.strcat uu____10134 "."))
in (FStar_Util.starts_with uu____10127 uu____10132)))
end))))
in (match (uu____10101) with
| true -> begin
((ns), (Open_namespace))
end
| uu____10142 -> begin
(

let uu____10144 = (

let uu____10150 = (

let uu____10152 = (FStar_Ident.text_of_lid ns)
in (FStar_Util.format1 "Namespace %s cannot be found" uu____10152))
in ((FStar_Errors.Fatal_NameSpaceNotFound), (uu____10150)))
in (

let uu____10156 = (FStar_Ident.range_of_lid ns)
in (FStar_Errors.raise_error uu____10144 uu____10156)))
end)))
end
| FStar_Pervasives_Native.Some (ns') -> begin
((fail_if_curmodule env ns ns');
((ns'), (Open_module));
)
end))
in (match (uu____10081) with
| (ns', kd) -> begin
((env.ds_hooks.ds_push_open_hook env ((ns'), (kd)));
(push_scope_mod env (Open_module_or_namespace (((ns'), (kd)))));
)
end)))


let push_include : env  ->  FStar_Ident.lident  ->  env = (fun env ns -> (

let ns0 = ns
in (

let uu____10178 = (resolve_module_name env ns false)
in (match (uu____10178) with
| FStar_Pervasives_Native.Some (ns1) -> begin
((env.ds_hooks.ds_push_include_hook env ns1);
(fail_if_curmodule env ns0 ns1);
(

let env1 = (push_scope_mod env (Open_module_or_namespace (((ns1), (Open_module)))))
in (

let curmod = (

let uu____10188 = (current_module env1)
in uu____10188.FStar_Ident.str)
in ((

let uu____10190 = (FStar_Util.smap_try_find env1.includes curmod)
in (match (uu____10190) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (incl) -> begin
(

let uu____10214 = (

let uu____10217 = (FStar_ST.op_Bang incl)
in (ns1)::uu____10217)
in (FStar_ST.op_Colon_Equals incl uu____10214))
end));
(match (()) with
| () -> begin
(

let uu____10310 = (get_trans_exported_id_set env1 ns1.FStar_Ident.str)
in (match (uu____10310) with
| FStar_Pervasives_Native.Some (ns_trans_exports) -> begin
((

let uu____10330 = (

let uu____10427 = (get_exported_id_set env1 curmod)
in (

let uu____10474 = (get_trans_exported_id_set env1 curmod)
in ((uu____10427), (uu____10474))))
in (match (uu____10330) with
| (FStar_Pervasives_Native.Some (cur_exports), FStar_Pervasives_Native.Some (cur_trans_exports)) -> begin
(

let update_exports = (fun k -> (

let ns_ex = (

let uu____10890 = (ns_trans_exports k)
in (FStar_ST.op_Bang uu____10890))
in (

let ex = (cur_exports k)
in ((

let uu____11065 = (

let uu____11069 = (FStar_ST.op_Bang ex)
in (FStar_Util.set_difference uu____11069 ns_ex))
in (FStar_ST.op_Colon_Equals ex uu____11065));
(match (()) with
| () -> begin
(

let trans_ex = (cur_trans_exports k)
in (

let uu____11266 = (

let uu____11270 = (FStar_ST.op_Bang trans_ex)
in (FStar_Util.set_union uu____11270 ns_ex))
in (FStar_ST.op_Colon_Equals trans_ex uu____11266)))
end);
))))
in (FStar_List.iter update_exports all_exported_id_kinds))
end
| uu____11403 -> begin
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

let uu____11505 = (

let uu____11511 = (FStar_Util.format1 "include: Module %s was not prepared" ns1.FStar_Ident.str)
in ((FStar_Errors.Fatal_IncludeModuleNotPrepared), (uu____11511)))
in (

let uu____11515 = (FStar_Ident.range_of_lid ns1)
in (FStar_Errors.raise_error uu____11505 uu____11515)))
end))
end);
)));
)
end
| uu____11516 -> begin
(

let uu____11519 = (

let uu____11525 = (FStar_Util.format1 "include: Module %s cannot be found" ns.FStar_Ident.str)
in ((FStar_Errors.Fatal_ModuleNotFound), (uu____11525)))
in (

let uu____11529 = (FStar_Ident.range_of_lid ns)
in (FStar_Errors.raise_error uu____11519 uu____11529)))
end))))


let push_module_abbrev : env  ->  FStar_Ident.ident  ->  FStar_Ident.lident  ->  env = (fun env x l -> (

let uu____11546 = (module_is_defined env l)
in (match (uu____11546) with
| true -> begin
((fail_if_curmodule env l l);
(env.ds_hooks.ds_push_module_abbrev_hook env x l);
(push_scope_mod env (Module_abbrev (((x), (l)))));
)
end
| uu____11551 -> begin
(

let uu____11553 = (

let uu____11559 = (

let uu____11561 = (FStar_Ident.text_of_lid l)
in (FStar_Util.format1 "Module %s cannot be found" uu____11561))
in ((FStar_Errors.Fatal_ModuleNotFound), (uu____11559)))
in (

let uu____11565 = (FStar_Ident.range_of_lid l)
in (FStar_Errors.raise_error uu____11553 uu____11565)))
end)))


let push_doc : env  ->  FStar_Ident.lident  ->  FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option  ->  env = (fun env l doc_opt -> (match (doc_opt) with
| FStar_Pervasives_Native.None -> begin
env
end
| FStar_Pervasives_Native.Some (doc1) -> begin
((

let uu____11588 = (FStar_Util.smap_try_find env.docs l.FStar_Ident.str)
in (match (uu____11588) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (old_doc) -> begin
(

let uu____11592 = (FStar_Ident.range_of_lid l)
in (

let uu____11593 = (

let uu____11599 = (

let uu____11601 = (FStar_Ident.string_of_lid l)
in (

let uu____11603 = (FStar_Parser_AST.string_of_fsdoc old_doc)
in (

let uu____11605 = (FStar_Parser_AST.string_of_fsdoc doc1)
in (FStar_Util.format3 "Overwriting doc of %s; old doc was [%s]; new doc are [%s]" uu____11601 uu____11603 uu____11605))))
in ((FStar_Errors.Warning_DocOverwrite), (uu____11599)))
in (FStar_Errors.log_issue uu____11592 uu____11593)))
end));
(FStar_Util.smap_add env.docs l.FStar_Ident.str doc1);
env;
)
end))


let check_admits : env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.modul = (fun env m -> (

let admitted_sig_lids = (FStar_All.pipe_right env.sigaccum (FStar_List.fold_left (fun lids se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_declare_typ (l, u, t) when (

let uu____11651 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_List.contains FStar_Syntax_Syntax.Assumption))
in (not (uu____11651))) -> begin
(

let uu____11656 = (FStar_Util.smap_try_find (sigmap env) l.FStar_Ident.str)
in (match (uu____11656) with
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (uu____11671); FStar_Syntax_Syntax.sigrng = uu____11672; FStar_Syntax_Syntax.sigquals = uu____11673; FStar_Syntax_Syntax.sigmeta = uu____11674; FStar_Syntax_Syntax.sigattrs = uu____11675}, uu____11676) -> begin
lids
end
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (uu____11694); FStar_Syntax_Syntax.sigrng = uu____11695; FStar_Syntax_Syntax.sigquals = uu____11696; FStar_Syntax_Syntax.sigmeta = uu____11697; FStar_Syntax_Syntax.sigattrs = uu____11698}, uu____11699) -> begin
lids
end
| uu____11727 -> begin
((

let uu____11736 = (

let uu____11738 = (FStar_Options.interactive ())
in (not (uu____11738)))
in (match (uu____11736) with
| true -> begin
(

let uu____11741 = (FStar_Ident.range_of_lid l)
in (

let uu____11742 = (

let uu____11748 = (

let uu____11750 = (FStar_Ident.string_of_lid l)
in (FStar_Util.format1 "Admitting %s without a definition" uu____11750))
in ((FStar_Errors.Warning_AdmitWithoutDefinition), (uu____11748)))
in (FStar_Errors.log_issue uu____11741 uu____11742)))
end
| uu____11754 -> begin
()
end));
(

let quals = (FStar_Syntax_Syntax.Assumption)::se.FStar_Syntax_Syntax.sigquals
in ((FStar_Util.smap_add (sigmap env) l.FStar_Ident.str (((

let uu___222_11767 = se
in {FStar_Syntax_Syntax.sigel = uu___222_11767.FStar_Syntax_Syntax.sigel; FStar_Syntax_Syntax.sigrng = uu___222_11767.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = uu___222_11767.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___222_11767.FStar_Syntax_Syntax.sigattrs})), (false)));
(l)::lids;
));
)
end))
end
| uu____11769 -> begin
lids
end)) []))
in (

let uu___223_11770 = m
in (

let uu____11771 = (FStar_All.pipe_right m.FStar_Syntax_Syntax.declarations (FStar_List.map (fun s -> (match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____11781, uu____11782) when (FStar_List.existsb (fun l -> (FStar_Ident.lid_equals l lid)) admitted_sig_lids) -> begin
(

let uu___224_11785 = s
in {FStar_Syntax_Syntax.sigel = uu___224_11785.FStar_Syntax_Syntax.sigel; FStar_Syntax_Syntax.sigrng = uu___224_11785.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Assumption)::s.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___224_11785.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___224_11785.FStar_Syntax_Syntax.sigattrs})
end
| uu____11786 -> begin
s
end))))
in {FStar_Syntax_Syntax.name = uu___223_11770.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = uu____11771; FStar_Syntax_Syntax.exports = uu___223_11770.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = uu___223_11770.FStar_Syntax_Syntax.is_interface}))))


let finish : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env modul -> ((FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations (FStar_List.iter (fun se -> (

let quals = se.FStar_Syntax_Syntax.sigquals
in (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____11810) -> begin
(match (((FStar_List.contains FStar_Syntax_Syntax.Private quals) || (FStar_List.contains FStar_Syntax_Syntax.Abstract quals))) with
| true -> begin
(FStar_All.pipe_right ses (FStar_List.iter (fun se1 -> (match (se1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (lid, uu____11831, uu____11832, uu____11833, uu____11834, uu____11835) -> begin
(FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str)
end
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, univ_names, binders, typ, uu____11851, uu____11852) -> begin
((FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str);
(match ((not ((FStar_List.contains FStar_Syntax_Syntax.Private quals)))) with
| true -> begin
(

let sigel = (

let uu____11869 = (

let uu____11876 = (

let uu____11877 = (FStar_Ident.range_of_lid lid)
in (

let uu____11878 = (

let uu____11885 = (

let uu____11886 = (

let uu____11901 = (FStar_Syntax_Syntax.mk_Total typ)
in ((binders), (uu____11901)))
in FStar_Syntax_Syntax.Tm_arrow (uu____11886))
in (FStar_Syntax_Syntax.mk uu____11885))
in (uu____11878 FStar_Pervasives_Native.None uu____11877)))
in ((lid), (univ_names), (uu____11876)))
in FStar_Syntax_Syntax.Sig_declare_typ (uu____11869))
in (

let se2 = (

let uu___225_11918 = se1
in {FStar_Syntax_Syntax.sigel = sigel; FStar_Syntax_Syntax.sigrng = uu___225_11918.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Assumption)::quals; FStar_Syntax_Syntax.sigmeta = uu___225_11918.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___225_11918.FStar_Syntax_Syntax.sigattrs})
in (FStar_Util.smap_add (sigmap env) lid.FStar_Ident.str ((se2), (false)))))
end
| uu____11926 -> begin
()
end);
)
end
| uu____11928 -> begin
()
end))))
end
| uu____11929 -> begin
()
end)
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____11932, uu____11933) -> begin
(match ((FStar_List.contains FStar_Syntax_Syntax.Private quals)) with
| true -> begin
(FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str)
end
| uu____11940 -> begin
()
end)
end
| FStar_Syntax_Syntax.Sig_let ((uu____11942, lbs), uu____11944) -> begin
((match (((FStar_List.contains FStar_Syntax_Syntax.Private quals) || (FStar_List.contains FStar_Syntax_Syntax.Abstract quals))) with
| true -> begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (

let uu____11962 = (

let uu____11964 = (

let uu____11965 = (

let uu____11968 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in uu____11968.FStar_Syntax_Syntax.fv_name)
in uu____11965.FStar_Syntax_Syntax.v)
in uu____11964.FStar_Ident.str)
in (FStar_Util.smap_remove (sigmap env) uu____11962)))))
end
| uu____11974 -> begin
()
end);
(match (((FStar_List.contains FStar_Syntax_Syntax.Abstract quals) && (not ((FStar_List.contains FStar_Syntax_Syntax.Private quals))))) with
| true -> begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (

let lid = (

let uu____11985 = (

let uu____11988 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in uu____11988.FStar_Syntax_Syntax.fv_name)
in uu____11985.FStar_Syntax_Syntax.v)
in (

let quals1 = (FStar_Syntax_Syntax.Assumption)::quals
in (

let decl = (

let uu___226_11993 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp))); FStar_Syntax_Syntax.sigrng = uu___226_11993.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = uu___226_11993.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___226_11993.FStar_Syntax_Syntax.sigattrs})
in (FStar_Util.smap_add (sigmap env) lid.FStar_Ident.str ((decl), (false)))))))))
end
| uu____12001 -> begin
()
end);
)
end
| uu____12003 -> begin
()
end)))));
(

let curmod = (

let uu____12006 = (current_module env)
in uu____12006.FStar_Ident.str)
in ((

let uu____12008 = (

let uu____12105 = (get_exported_id_set env curmod)
in (

let uu____12152 = (get_trans_exported_id_set env curmod)
in ((uu____12105), (uu____12152))))
in (match (uu____12008) with
| (FStar_Pervasives_Native.Some (cur_ex), FStar_Pervasives_Native.Some (cur_trans_ex)) -> begin
(

let update_exports = (fun eikind -> (

let cur_ex_set = (

let uu____12571 = (cur_ex eikind)
in (FStar_ST.op_Bang uu____12571))
in (

let cur_trans_ex_set_ref = (cur_trans_ex eikind)
in (

let uu____12761 = (

let uu____12765 = (FStar_ST.op_Bang cur_trans_ex_set_ref)
in (FStar_Util.set_union cur_ex_set uu____12765))
in (FStar_ST.op_Colon_Equals cur_trans_ex_set_ref uu____12761)))))
in (FStar_List.iter update_exports all_exported_id_kinds))
end
| uu____12898 -> begin
()
end));
(match (()) with
| () -> begin
((filter_record_cache ());
(match (()) with
| () -> begin
(

let uu___227_12996 = env
in {curmodule = FStar_Pervasives_Native.None; curmonad = uu___227_12996.curmonad; modules = (((modul.FStar_Syntax_Syntax.name), (modul)))::env.modules; scope_mods = []; exported_ids = uu___227_12996.exported_ids; trans_exported_ids = uu___227_12996.trans_exported_ids; includes = uu___227_12996.includes; sigaccum = []; sigmap = uu___227_12996.sigmap; iface = uu___227_12996.iface; admitted_iface = uu___227_12996.admitted_iface; expect_typ = uu___227_12996.expect_typ; docs = uu___227_12996.docs; remaining_iface_decls = uu___227_12996.remaining_iface_decls; syntax_only = uu___227_12996.syntax_only; ds_hooks = uu___227_12996.ds_hooks; dep_graph = uu___227_12996.dep_graph})
end);
)
end);
));
))


let stack : env Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let push : env  ->  env = (fun env -> (FStar_Util.atomically (fun uu____13034 -> ((push_record_cache ());
(

let uu____13037 = (

let uu____13040 = (FStar_ST.op_Bang stack)
in (env)::uu____13040)
in (FStar_ST.op_Colon_Equals stack uu____13037));
(

let uu___228_13089 = env
in (

let uu____13090 = (FStar_Util.smap_copy env.exported_ids)
in (

let uu____13095 = (FStar_Util.smap_copy env.trans_exported_ids)
in (

let uu____13100 = (FStar_Util.smap_copy env.includes)
in (

let uu____13111 = (FStar_Util.smap_copy env.sigmap)
in (

let uu____13124 = (FStar_Util.smap_copy env.docs)
in {curmodule = uu___228_13089.curmodule; curmonad = uu___228_13089.curmonad; modules = uu___228_13089.modules; scope_mods = uu___228_13089.scope_mods; exported_ids = uu____13090; trans_exported_ids = uu____13095; includes = uu____13100; sigaccum = uu___228_13089.sigaccum; sigmap = uu____13111; iface = uu___228_13089.iface; admitted_iface = uu___228_13089.admitted_iface; expect_typ = uu___228_13089.expect_typ; docs = uu____13124; remaining_iface_decls = uu___228_13089.remaining_iface_decls; syntax_only = uu___228_13089.syntax_only; ds_hooks = uu___228_13089.ds_hooks; dep_graph = uu___228_13089.dep_graph}))))));
))))


let pop : unit  ->  env = (fun uu____13132 -> (FStar_Util.atomically (fun uu____13139 -> (

let uu____13140 = (FStar_ST.op_Bang stack)
in (match (uu____13140) with
| (env)::tl1 -> begin
((pop_record_cache ());
(FStar_ST.op_Colon_Equals stack tl1);
env;
)
end
| uu____13195 -> begin
(failwith "Impossible: Too many pops")
end)))))


let snapshot : env  ->  (Prims.int * env) = (fun env -> (FStar_Common.snapshot push stack env))


let rollback : Prims.int FStar_Pervasives_Native.option  ->  env = (fun depth -> (FStar_Common.rollback pop stack depth))


let export_interface : FStar_Ident.lident  ->  env  ->  env = (fun m env -> (

let sigelt_in_m = (fun se -> (match ((FStar_Syntax_Util.lids_of_sigelt se)) with
| (l)::uu____13242 -> begin
(Prims.op_Equality l.FStar_Ident.nsstr m.FStar_Ident.str)
end
| uu____13246 -> begin
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

let uu____13288 = (FStar_Util.smap_try_find sm' k)
in (match (uu____13288) with
| FStar_Pervasives_Native.Some (se, true) when (sigelt_in_m se) -> begin
((FStar_Util.smap_remove sm' k);
(

let se1 = (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_declare_typ (l, u, t) -> begin
(

let uu___229_13319 = se
in {FStar_Syntax_Syntax.sigel = uu___229_13319.FStar_Syntax_Syntax.sigel; FStar_Syntax_Syntax.sigrng = uu___229_13319.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Assumption)::se.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___229_13319.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___229_13319.FStar_Syntax_Syntax.sigattrs})
end
| uu____13320 -> begin
se
end)
in (FStar_Util.smap_add sm' k ((se1), (false))));
)
end
| uu____13328 -> begin
()
end)))));
env1;
)))))))


let finish_module_or_interface : env  ->  FStar_Syntax_Syntax.modul  ->  (env * FStar_Syntax_Syntax.modul) = (fun env modul -> (

let modul1 = (match ((not (modul.FStar_Syntax_Syntax.is_interface))) with
| true -> begin
(check_admits env modul)
end
| uu____13353 -> begin
modul
end)
in (

let uu____13355 = (finish env modul1)
in ((uu____13355), (modul1)))))

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

let uu____13457 = (

let uu____13461 = (e Exported_id_term_type)
in (FStar_ST.op_Bang uu____13461))
in (FStar_Util.set_elements uu____13457))
in (

let fields = (

let uu____13577 = (

let uu____13581 = (e Exported_id_field)
in (FStar_ST.op_Bang uu____13581))
in (FStar_Util.set_elements uu____13577))
in {exported_id_terms = terms; exported_id_fields = fields})))


let as_exported_id_set : exported_ids FStar_Pervasives_Native.option  ->  exported_id_kind  ->  Prims.string FStar_Util.set FStar_ST.ref = (fun e -> (match (e) with
| FStar_Pervasives_Native.None -> begin
(exported_id_set_new ())
end
| FStar_Pervasives_Native.Some (e1) -> begin
(

let terms = (

let uu____13737 = (FStar_Util.as_set e1.exported_id_terms FStar_Util.compare)
in (FStar_Util.mk_ref uu____13737))
in (

let fields = (

let uu____13751 = (FStar_Util.as_set e1.exported_id_fields FStar_Util.compare)
in (FStar_Util.mk_ref uu____13751))
in (fun uu___203_13759 -> (match (uu___203_13759) with
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


let as_includes : 'Auu____13896 . 'Auu____13896 Prims.list FStar_Pervasives_Native.option  ->  'Auu____13896 Prims.list FStar_ST.ref = (fun uu___204_13909 -> (match (uu___204_13909) with
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

let uu____13952 = (FStar_Util.smap_try_find m mname)
in (FStar_Util.map_opt uu____13952 as_exported_ids)))
in (

let uu____13958 = (as_ids_opt env.exported_ids)
in (

let uu____13961 = (as_ids_opt env.trans_exported_ids)
in (

let uu____13964 = (

let uu____13969 = (FStar_Util.smap_try_find env.includes mname)
in (FStar_Util.map_opt uu____13969 (fun r -> (FStar_ST.op_Bang r))))
in {mii_exported_ids = uu____13958; mii_trans_exported_ids = uu____13961; mii_includes = uu____13964}))))))


let prepare_module_or_interface : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  module_inclusion_info  ->  (env * Prims.bool) = (fun intf admitted env mname mii -> (

let prep = (fun env1 -> (

let filename = (

let uu____14091 = (FStar_Ident.text_of_lid mname)
in (FStar_Util.strcat uu____14091 ".fst"))
in (

let auto_open = (FStar_Parser_Dep.hard_coded_dependencies filename)
in (

let auto_open1 = (

let convert_kind = (fun uu___205_14113 -> (match (uu___205_14113) with
| FStar_Parser_Dep.Open_namespace -> begin
Open_namespace
end
| FStar_Parser_Dep.Open_module -> begin
Open_module
end))
in (FStar_List.map (fun uu____14125 -> (match (uu____14125) with
| (lid, kind) -> begin
((lid), ((convert_kind kind)))
end)) auto_open))
in (

let namespace_of_module = (match (((FStar_List.length mname.FStar_Ident.ns) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____14151 = (

let uu____14156 = (FStar_Ident.lid_of_ids mname.FStar_Ident.ns)
in ((uu____14156), (Open_namespace)))
in (uu____14151)::[])
end
| uu____14165 -> begin
[]
end)
in (

let auto_open2 = (FStar_List.append namespace_of_module (FStar_List.rev auto_open1))
in ((

let uu____14187 = (as_exported_id_set mii.mii_exported_ids)
in (FStar_Util.smap_add env1.exported_ids mname.FStar_Ident.str uu____14187));
(match (()) with
| () -> begin
((

let uu____14214 = (as_exported_id_set mii.mii_trans_exported_ids)
in (FStar_Util.smap_add env1.trans_exported_ids mname.FStar_Ident.str uu____14214));
(match (()) with
| () -> begin
((

let uu____14241 = (as_includes mii.mii_includes)
in (FStar_Util.smap_add env1.includes mname.FStar_Ident.str uu____14241));
(match (()) with
| () -> begin
(

let env' = (

let uu___230_14273 = env1
in (

let uu____14274 = (FStar_List.map (fun x -> Open_module_or_namespace (x)) auto_open2)
in {curmodule = FStar_Pervasives_Native.Some (mname); curmonad = uu___230_14273.curmonad; modules = uu___230_14273.modules; scope_mods = uu____14274; exported_ids = uu___230_14273.exported_ids; trans_exported_ids = uu___230_14273.trans_exported_ids; includes = uu___230_14273.includes; sigaccum = uu___230_14273.sigaccum; sigmap = env1.sigmap; iface = intf; admitted_iface = admitted; expect_typ = uu___230_14273.expect_typ; docs = uu___230_14273.docs; remaining_iface_decls = uu___230_14273.remaining_iface_decls; syntax_only = uu___230_14273.syntax_only; ds_hooks = uu___230_14273.ds_hooks; dep_graph = uu___230_14273.dep_graph}))
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

let uu____14286 = (FStar_All.pipe_right env.modules (FStar_Util.find_opt (fun uu____14312 -> (match (uu____14312) with
| (l, uu____14319) -> begin
(FStar_Ident.lid_equals l mname)
end))))
in (match (uu____14286) with
| FStar_Pervasives_Native.None -> begin
(

let uu____14329 = (prep env)
in ((uu____14329), (false)))
end
| FStar_Pervasives_Native.Some (uu____14332, m) -> begin
((

let uu____14339 = ((

let uu____14343 = (FStar_Options.interactive ())
in (not (uu____14343))) && ((not (m.FStar_Syntax_Syntax.is_interface)) || intf))
in (match (uu____14339) with
| true -> begin
(

let uu____14346 = (

let uu____14352 = (FStar_Util.format1 "Duplicate module or interface name: %s" mname.FStar_Ident.str)
in ((FStar_Errors.Fatal_DuplicateModuleOrInterface), (uu____14352)))
in (

let uu____14356 = (FStar_Ident.range_of_lid mname)
in (FStar_Errors.raise_error uu____14346 uu____14356)))
end
| uu____14357 -> begin
()
end));
(

let uu____14359 = (

let uu____14360 = (push env)
in (prep uu____14360))
in ((uu____14359), (true)));
)
end))))


let enter_monad_scope : env  ->  FStar_Ident.ident  ->  env = (fun env mname -> (match (env.curmonad) with
| FStar_Pervasives_Native.Some (mname') -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_MonadAlreadyDefined), ((Prims.strcat "Trying to define monad " (Prims.strcat mname.FStar_Ident.idText (Prims.strcat ", but already in monad scope " mname'.FStar_Ident.idText))))) mname.FStar_Ident.idRange)
end
| FStar_Pervasives_Native.None -> begin
(

let uu___231_14378 = env
in {curmodule = uu___231_14378.curmodule; curmonad = FStar_Pervasives_Native.Some (mname); modules = uu___231_14378.modules; scope_mods = uu___231_14378.scope_mods; exported_ids = uu___231_14378.exported_ids; trans_exported_ids = uu___231_14378.trans_exported_ids; includes = uu___231_14378.includes; sigaccum = uu___231_14378.sigaccum; sigmap = uu___231_14378.sigmap; iface = uu___231_14378.iface; admitted_iface = uu___231_14378.admitted_iface; expect_typ = uu___231_14378.expect_typ; docs = uu___231_14378.docs; remaining_iface_decls = uu___231_14378.remaining_iface_decls; syntax_only = uu___231_14378.syntax_only; ds_hooks = uu___231_14378.ds_hooks; dep_graph = uu___231_14378.dep_graph})
end))


let fail_or : 'a . env  ->  (FStar_Ident.lident  ->  'a FStar_Pervasives_Native.option)  ->  FStar_Ident.lident  ->  'a = (fun env lookup1 lid -> (

let uu____14413 = (lookup1 lid)
in (match (uu____14413) with
| FStar_Pervasives_Native.None -> begin
(

let opened_modules = (FStar_List.map (fun uu____14428 -> (match (uu____14428) with
| (lid1, uu____14435) -> begin
(FStar_Ident.text_of_lid lid1)
end)) env.modules)
in (

let msg = (

let uu____14438 = (FStar_Ident.text_of_lid lid)
in (FStar_Util.format1 "Identifier not found: [%s]" uu____14438))
in (

let msg1 = (match ((Prims.op_Equality (FStar_List.length lid.FStar_Ident.ns) (Prims.parse_int "0"))) with
| true -> begin
msg
end
| uu____14447 -> begin
(

let modul = (

let uu____14450 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in (

let uu____14451 = (FStar_Ident.range_of_lid lid)
in (FStar_Ident.set_lid_range uu____14450 uu____14451)))
in (

let uu____14452 = (resolve_module_name env modul true)
in (match (uu____14452) with
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

let uu____14473 = (FStar_Ident.range_of_lid lid)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_IdentifierNotFound), (msg1)) uu____14473)))))
end
| FStar_Pervasives_Native.Some (r) -> begin
r
end)))


let fail_or2 : 'a . (FStar_Ident.ident  ->  'a FStar_Pervasives_Native.option)  ->  FStar_Ident.ident  ->  'a = (fun lookup1 id1 -> (

let uu____14503 = (lookup1 id1)
in (match (uu____14503) with
| FStar_Pervasives_Native.None -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_IdentifierNotFound), ((Prims.strcat "Identifier not found [" (Prims.strcat id1.FStar_Ident.idText "]")))) id1.FStar_Ident.idRange)
end
| FStar_Pervasives_Native.Some (r) -> begin
r
end)))




