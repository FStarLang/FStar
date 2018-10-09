
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
| uu____20 -> begin
false
end))


let uu___is_Open_namespace : open_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Open_namespace -> begin
true
end
| uu____26 -> begin
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
| uu____217 -> begin
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
| uu____231 -> begin
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
| uu____245 -> begin
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
| uu____259 -> begin
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
| uu____273 -> begin
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
| uu____287 -> begin
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
| uu____302 -> begin
false
end))


let uu___is_Exported_id_field : exported_id_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Exported_id_field -> begin
true
end
| uu____308 -> begin
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


let default_ds_hooks : dsenv_hooks = {ds_push_open_hook = (fun uu____1806 uu____1807 -> ()); ds_push_include_hook = (fun uu____1810 uu____1811 -> ()); ds_push_module_abbrev_hook = (fun uu____1815 uu____1816 uu____1817 -> ())}

type foundname =
| Term_name of (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.attribute Prims.list)
| Eff_name of (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident)


let uu___is_Term_name : foundname  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Term_name (_0) -> begin
true
end
| uu____1850 -> begin
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
| uu____1886 -> begin
false
end))


let __proj__Eff_name__item___0 : foundname  ->  (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident) = (fun projectee -> (match (projectee) with
| Eff_name (_0) -> begin
_0
end))


let set_iface : env  ->  Prims.bool  ->  env = (fun env b -> (

let uu___204_1916 = env
in {curmodule = uu___204_1916.curmodule; curmonad = uu___204_1916.curmonad; modules = uu___204_1916.modules; scope_mods = uu___204_1916.scope_mods; exported_ids = uu___204_1916.exported_ids; trans_exported_ids = uu___204_1916.trans_exported_ids; includes = uu___204_1916.includes; sigaccum = uu___204_1916.sigaccum; sigmap = uu___204_1916.sigmap; iface = b; admitted_iface = uu___204_1916.admitted_iface; expect_typ = uu___204_1916.expect_typ; docs = uu___204_1916.docs; remaining_iface_decls = uu___204_1916.remaining_iface_decls; syntax_only = uu___204_1916.syntax_only; ds_hooks = uu___204_1916.ds_hooks; dep_graph = uu___204_1916.dep_graph}))


let iface : env  ->  Prims.bool = (fun e -> e.iface)


let set_admitted_iface : env  ->  Prims.bool  ->  env = (fun e b -> (

let uu___205_1932 = e
in {curmodule = uu___205_1932.curmodule; curmonad = uu___205_1932.curmonad; modules = uu___205_1932.modules; scope_mods = uu___205_1932.scope_mods; exported_ids = uu___205_1932.exported_ids; trans_exported_ids = uu___205_1932.trans_exported_ids; includes = uu___205_1932.includes; sigaccum = uu___205_1932.sigaccum; sigmap = uu___205_1932.sigmap; iface = uu___205_1932.iface; admitted_iface = b; expect_typ = uu___205_1932.expect_typ; docs = uu___205_1932.docs; remaining_iface_decls = uu___205_1932.remaining_iface_decls; syntax_only = uu___205_1932.syntax_only; ds_hooks = uu___205_1932.ds_hooks; dep_graph = uu___205_1932.dep_graph}))


let admitted_iface : env  ->  Prims.bool = (fun e -> e.admitted_iface)


let set_expect_typ : env  ->  Prims.bool  ->  env = (fun e b -> (

let uu___206_1948 = e
in {curmodule = uu___206_1948.curmodule; curmonad = uu___206_1948.curmonad; modules = uu___206_1948.modules; scope_mods = uu___206_1948.scope_mods; exported_ids = uu___206_1948.exported_ids; trans_exported_ids = uu___206_1948.trans_exported_ids; includes = uu___206_1948.includes; sigaccum = uu___206_1948.sigaccum; sigmap = uu___206_1948.sigmap; iface = uu___206_1948.iface; admitted_iface = uu___206_1948.admitted_iface; expect_typ = b; docs = uu___206_1948.docs; remaining_iface_decls = uu___206_1948.remaining_iface_decls; syntax_only = uu___206_1948.syntax_only; ds_hooks = uu___206_1948.ds_hooks; dep_graph = uu___206_1948.dep_graph}))


let expect_typ : env  ->  Prims.bool = (fun e -> e.expect_typ)


let all_exported_id_kinds : exported_id_kind Prims.list = (Exported_id_field)::(Exported_id_term_type)::[]


let transitive_exported_ids : env  ->  FStar_Ident.lident  ->  Prims.string Prims.list = (fun env lid -> (

let module_name = (FStar_Ident.string_of_lid lid)
in (

let uu____1969 = (FStar_Util.smap_try_find env.trans_exported_ids module_name)
in (match (uu____1969) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (exported_id_set) -> begin
(

let uu____1980 = (

let uu____1983 = (exported_id_set Exported_id_term_type)
in (FStar_ST.op_Bang uu____1983))
in (FStar_All.pipe_right uu____1980 FStar_Util.set_elements))
end))))


let open_modules : env  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.modul) Prims.list = (fun e -> e.modules)


let open_modules_and_namespaces : env  ->  FStar_Ident.lident Prims.list = (fun env -> (FStar_List.filter_map (fun uu___171_2119 -> (match (uu___171_2119) with
| Open_module_or_namespace (lid, _info) -> begin
FStar_Pervasives_Native.Some (lid)
end
| uu____2124 -> begin
FStar_Pervasives_Native.None
end)) env.scope_mods))


let set_current_module : env  ->  FStar_Ident.lident  ->  env = (fun e l -> (

let uu___207_2135 = e
in {curmodule = FStar_Pervasives_Native.Some (l); curmonad = uu___207_2135.curmonad; modules = uu___207_2135.modules; scope_mods = uu___207_2135.scope_mods; exported_ids = uu___207_2135.exported_ids; trans_exported_ids = uu___207_2135.trans_exported_ids; includes = uu___207_2135.includes; sigaccum = uu___207_2135.sigaccum; sigmap = uu___207_2135.sigmap; iface = uu___207_2135.iface; admitted_iface = uu___207_2135.admitted_iface; expect_typ = uu___207_2135.expect_typ; docs = uu___207_2135.docs; remaining_iface_decls = uu___207_2135.remaining_iface_decls; syntax_only = uu___207_2135.syntax_only; ds_hooks = uu___207_2135.ds_hooks; dep_graph = uu___207_2135.dep_graph}))


let current_module : env  ->  FStar_Ident.lident = (fun env -> (match (env.curmodule) with
| FStar_Pervasives_Native.None -> begin
(failwith "Unset current module")
end
| FStar_Pervasives_Native.Some (m) -> begin
m
end))


let iface_decls : env  ->  FStar_Ident.lident  ->  FStar_Parser_AST.decl Prims.list FStar_Pervasives_Native.option = (fun env l -> (

let uu____2156 = (FStar_All.pipe_right env.remaining_iface_decls (FStar_List.tryFind (fun uu____2190 -> (match (uu____2190) with
| (m, uu____2198) -> begin
(FStar_Ident.lid_equals l m)
end))))
in (match (uu____2156) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (uu____2215, decls) -> begin
FStar_Pervasives_Native.Some (decls)
end)))


let set_iface_decls : env  ->  FStar_Ident.lident  ->  FStar_Parser_AST.decl Prims.list  ->  env = (fun env l ds -> (

let uu____2248 = (FStar_List.partition (fun uu____2278 -> (match (uu____2278) with
| (m, uu____2286) -> begin
(FStar_Ident.lid_equals l m)
end)) env.remaining_iface_decls)
in (match (uu____2248) with
| (uu____2291, rest) -> begin
(

let uu___208_2325 = env
in {curmodule = uu___208_2325.curmodule; curmonad = uu___208_2325.curmonad; modules = uu___208_2325.modules; scope_mods = uu___208_2325.scope_mods; exported_ids = uu___208_2325.exported_ids; trans_exported_ids = uu___208_2325.trans_exported_ids; includes = uu___208_2325.includes; sigaccum = uu___208_2325.sigaccum; sigmap = uu___208_2325.sigmap; iface = uu___208_2325.iface; admitted_iface = uu___208_2325.admitted_iface; expect_typ = uu___208_2325.expect_typ; docs = uu___208_2325.docs; remaining_iface_decls = (((l), (ds)))::rest; syntax_only = uu___208_2325.syntax_only; ds_hooks = uu___208_2325.ds_hooks; dep_graph = uu___208_2325.dep_graph})
end)))


let qual : FStar_Ident.lident  ->  FStar_Ident.ident  ->  FStar_Ident.lident = FStar_Syntax_Util.qual_id


let qualify : env  ->  FStar_Ident.ident  ->  FStar_Ident.lident = (fun env id1 -> (match (env.curmonad) with
| FStar_Pervasives_Native.None -> begin
(

let uu____2352 = (current_module env)
in (qual uu____2352 id1))
end
| FStar_Pervasives_Native.Some (monad) -> begin
(

let uu____2354 = (

let uu____2355 = (current_module env)
in (qual uu____2355 monad))
in (FStar_Syntax_Util.mk_field_projector_name_from_ident uu____2354 id1))
end))


let syntax_only : env  ->  Prims.bool = (fun env -> env.syntax_only)


let set_syntax_only : env  ->  Prims.bool  ->  env = (fun env b -> (

let uu___209_2371 = env
in {curmodule = uu___209_2371.curmodule; curmonad = uu___209_2371.curmonad; modules = uu___209_2371.modules; scope_mods = uu___209_2371.scope_mods; exported_ids = uu___209_2371.exported_ids; trans_exported_ids = uu___209_2371.trans_exported_ids; includes = uu___209_2371.includes; sigaccum = uu___209_2371.sigaccum; sigmap = uu___209_2371.sigmap; iface = uu___209_2371.iface; admitted_iface = uu___209_2371.admitted_iface; expect_typ = uu___209_2371.expect_typ; docs = uu___209_2371.docs; remaining_iface_decls = uu___209_2371.remaining_iface_decls; syntax_only = b; ds_hooks = uu___209_2371.ds_hooks; dep_graph = uu___209_2371.dep_graph}))


let ds_hooks : env  ->  dsenv_hooks = (fun env -> env.ds_hooks)


let set_ds_hooks : env  ->  dsenv_hooks  ->  env = (fun env hooks -> (

let uu___210_2387 = env
in {curmodule = uu___210_2387.curmodule; curmonad = uu___210_2387.curmonad; modules = uu___210_2387.modules; scope_mods = uu___210_2387.scope_mods; exported_ids = uu___210_2387.exported_ids; trans_exported_ids = uu___210_2387.trans_exported_ids; includes = uu___210_2387.includes; sigaccum = uu___210_2387.sigaccum; sigmap = uu___210_2387.sigmap; iface = uu___210_2387.iface; admitted_iface = uu___210_2387.admitted_iface; expect_typ = uu___210_2387.expect_typ; docs = uu___210_2387.docs; remaining_iface_decls = uu___210_2387.remaining_iface_decls; syntax_only = uu___210_2387.syntax_only; ds_hooks = hooks; dep_graph = uu___210_2387.dep_graph}))


let new_sigmap : 'Auu____2392 . unit  ->  'Auu____2392 FStar_Util.smap = (fun uu____2399 -> (FStar_Util.smap_create (Prims.parse_int "100")))


let empty_env : FStar_Parser_Dep.deps  ->  env = (fun deps -> (

let uu____2405 = (new_sigmap ())
in (

let uu____2410 = (new_sigmap ())
in (

let uu____2415 = (new_sigmap ())
in (

let uu____2426 = (new_sigmap ())
in (

let uu____2437 = (new_sigmap ())
in {curmodule = FStar_Pervasives_Native.None; curmonad = FStar_Pervasives_Native.None; modules = []; scope_mods = []; exported_ids = uu____2405; trans_exported_ids = uu____2410; includes = uu____2415; sigaccum = []; sigmap = uu____2426; iface = false; admitted_iface = false; expect_typ = false; docs = uu____2437; remaining_iface_decls = []; syntax_only = false; ds_hooks = default_ds_hooks; dep_graph = deps}))))))


let dep_graph : env  ->  FStar_Parser_Dep.deps = (fun env -> env.dep_graph)


let set_dep_graph : env  ->  FStar_Parser_Dep.deps  ->  env = (fun env ds -> (

let uu___211_2465 = env
in {curmodule = uu___211_2465.curmodule; curmonad = uu___211_2465.curmonad; modules = uu___211_2465.modules; scope_mods = uu___211_2465.scope_mods; exported_ids = uu___211_2465.exported_ids; trans_exported_ids = uu___211_2465.trans_exported_ids; includes = uu___211_2465.includes; sigaccum = uu___211_2465.sigaccum; sigmap = uu___211_2465.sigmap; iface = uu___211_2465.iface; admitted_iface = uu___211_2465.admitted_iface; expect_typ = uu___211_2465.expect_typ; docs = uu___211_2465.docs; remaining_iface_decls = uu___211_2465.remaining_iface_decls; syntax_only = uu___211_2465.syntax_only; ds_hooks = uu___211_2465.ds_hooks; dep_graph = ds}))


let sigmap : env  ->  (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap = (fun env -> env.sigmap)


let has_all_in_scope : env  ->  Prims.bool = (fun env -> (FStar_List.existsb (fun uu____2489 -> (match (uu____2489) with
| (m, uu____2495) -> begin
(FStar_Ident.lid_equals m FStar_Parser_Const.all_lid)
end)) env.modules))


let set_bv_range : FStar_Syntax_Syntax.bv  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.bv = (fun bv r -> (

let id1 = (

let uu___212_2507 = bv.FStar_Syntax_Syntax.ppname
in {FStar_Ident.idText = uu___212_2507.FStar_Ident.idText; FStar_Ident.idRange = r})
in (

let uu___213_2508 = bv
in {FStar_Syntax_Syntax.ppname = id1; FStar_Syntax_Syntax.index = uu___213_2508.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu___213_2508.FStar_Syntax_Syntax.sort})))


let bv_to_name : FStar_Syntax_Syntax.bv  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.term = (fun bv r -> (FStar_Syntax_Syntax.bv_to_name (set_bv_range bv r)))


let unmangleMap : (Prims.string * Prims.string * FStar_Syntax_Syntax.delta_depth * FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option) Prims.list = ((("op_ColonColon"), ("Cons"), (FStar_Syntax_Syntax.delta_constant), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor))))::((("not"), ("op_Negation"), (FStar_Syntax_Syntax.delta_equational), (FStar_Pervasives_Native.None)))::[]


let unmangleOpName : FStar_Ident.ident  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun id1 -> (FStar_Util.find_map unmangleMap (fun uu____2590 -> (match (uu____2590) with
| (x, y, dd, dq) -> begin
(match ((Prims.op_Equality id1.FStar_Ident.idText x)) with
| true -> begin
(

let uu____2613 = (

let uu____2614 = (FStar_Ident.lid_of_path (("Prims")::(y)::[]) id1.FStar_Ident.idRange)
in (FStar_Syntax_Syntax.fvar uu____2614 dd dq))
in FStar_Pervasives_Native.Some (uu____2613))
end
| uu____2615 -> begin
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
| uu____2646 -> begin
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
| uu____2679 -> begin
false
end))


let uu___is_Cont_ignore : 'a . 'a cont_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Cont_ignore -> begin
true
end
| uu____2696 -> begin
false
end))


let option_of_cont : 'a . (unit  ->  'a FStar_Pervasives_Native.option)  ->  'a cont_t  ->  'a FStar_Pervasives_Native.option = (fun k_ignore uu___172_2724 -> (match (uu___172_2724) with
| Cont_ok (a) -> begin
FStar_Pervasives_Native.Some (a)
end
| Cont_fail -> begin
FStar_Pervasives_Native.None
end
| Cont_ignore -> begin
(k_ignore ())
end))


let find_in_record : 'Auu____2742 . FStar_Ident.ident Prims.list  ->  FStar_Ident.ident  ->  record_or_dc  ->  (record_or_dc  ->  'Auu____2742 cont_t)  ->  'Auu____2742 cont_t = (fun ns id1 record cont -> (

let typename' = (FStar_Ident.lid_of_ids (FStar_List.append ns ((record.typename.FStar_Ident.ident)::[])))
in (

let uu____2779 = (FStar_Ident.lid_equals typename' record.typename)
in (match (uu____2779) with
| true -> begin
(

let fname = (FStar_Ident.lid_of_ids (FStar_List.append record.typename.FStar_Ident.ns ((id1)::[])))
in (

let find1 = (FStar_Util.find_map record.fields (fun uu____2793 -> (match (uu____2793) with
| (f, uu____2801) -> begin
(match ((Prims.op_Equality id1.FStar_Ident.idText f.FStar_Ident.idText)) with
| true -> begin
FStar_Pervasives_Native.Some (record)
end
| uu____2804 -> begin
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
| uu____2808 -> begin
Cont_ignore
end))))


let get_exported_id_set : env  ->  Prims.string  ->  (exported_id_kind  ->  string_set FStar_ST.ref) FStar_Pervasives_Native.option = (fun e mname -> (FStar_Util.smap_try_find e.exported_ids mname))


let get_trans_exported_id_set : env  ->  Prims.string  ->  (exported_id_kind  ->  string_set FStar_ST.ref) FStar_Pervasives_Native.option = (fun e mname -> (FStar_Util.smap_try_find e.trans_exported_ids mname))


let string_of_exported_id_kind : exported_id_kind  ->  Prims.string = (fun uu___173_2863 -> (match (uu___173_2863) with
| Exported_id_field -> begin
"field"
end
| Exported_id_term_type -> begin
"term/type"
end))


let find_in_module_with_includes : 'a . exported_id_kind  ->  (FStar_Ident.lident  ->  'a cont_t)  ->  'a cont_t  ->  env  ->  FStar_Ident.lident  ->  FStar_Ident.ident  ->  'a cont_t = (fun eikind find_in_module find_in_module_default env ns id1 -> (

let idstr = id1.FStar_Ident.idText
in (

let rec aux = (fun uu___174_2934 -> (match (uu___174_2934) with
| [] -> begin
find_in_module_default
end
| (modul)::q -> begin
(

let mname = modul.FStar_Ident.str
in (

let not_shadowed = (

let uu____2945 = (get_exported_id_set env mname)
in (match (uu____2945) with
| FStar_Pervasives_Native.None -> begin
true
end
| FStar_Pervasives_Native.Some (mex) -> begin
(

let mexports = (

let uu____2970 = (mex eikind)
in (FStar_ST.op_Bang uu____2970))
in (FStar_Util.set_mem idstr mexports))
end))
in (

let mincludes = (

let uu____3084 = (FStar_Util.smap_try_find env.includes mname)
in (match (uu____3084) with
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

let uu____3160 = (qual modul id1)
in (find_in_module uu____3160))
end
| uu____3161 -> begin
Cont_ignore
end)
in (match (look_into) with
| Cont_ignore -> begin
(aux (FStar_List.append mincludes q))
end
| uu____3164 -> begin
look_into
end)))))
end))
in (aux ((ns)::[])))))


let is_exported_id_field : exported_id_kind  ->  Prims.bool = (fun uu___175_3171 -> (match (uu___175_3171) with
| Exported_id_field -> begin
true
end
| uu____3172 -> begin
false
end))


let try_lookup_id'' : 'a . env  ->  FStar_Ident.ident  ->  exported_id_kind  ->  (local_binding  ->  'a cont_t)  ->  (rec_binding  ->  'a cont_t)  ->  (record_or_dc  ->  'a cont_t)  ->  (FStar_Ident.lident  ->  'a cont_t)  ->  ('a cont_t  ->  FStar_Ident.ident  ->  'a cont_t)  ->  'a FStar_Pervasives_Native.option = (fun env id1 eikind k_local_binding k_rec_binding k_record find_in_module lookup_default_id -> (

let check_local_binding_id = (fun uu___176_3293 -> (match (uu___176_3293) with
| (id', uu____3295) -> begin
(Prims.op_Equality id'.FStar_Ident.idText id1.FStar_Ident.idText)
end))
in (

let check_rec_binding_id = (fun uu___177_3301 -> (match (uu___177_3301) with
| (id', uu____3303, uu____3304) -> begin
(Prims.op_Equality id'.FStar_Ident.idText id1.FStar_Ident.idText)
end))
in (

let curmod_ns = (

let uu____3308 = (current_module env)
in (FStar_Ident.ids_of_lid uu____3308))
in (

let proc = (fun uu___178_3316 -> (match (uu___178_3316) with
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

let uu____3324 = (FStar_Ident.lid_of_ids curmod_ns)
in (find_in_module_with_includes Exported_id_field (fun lid -> (

let id2 = lid.FStar_Ident.ident
in (find_in_record lid.FStar_Ident.ns id2 r k_record))) Cont_ignore env uu____3324 id1))
end
| uu____3329 -> begin
Cont_ignore
end))
in (

let rec aux = (fun uu___179_3339 -> (match (uu___179_3339) with
| (a)::q -> begin
(

let uu____3348 = (proc a)
in (option_of_cont (fun uu____3352 -> (aux q)) uu____3348))
end
| [] -> begin
(

let uu____3353 = (lookup_default_id Cont_fail id1)
in (option_of_cont (fun uu____3357 -> FStar_Pervasives_Native.None) uu____3353))
end))
in (aux env.scope_mods)))))))


let found_local_binding : 'Auu____3364 . FStar_Range.range  ->  ('Auu____3364 * FStar_Syntax_Syntax.bv)  ->  FStar_Syntax_Syntax.term = (fun r uu____3378 -> (match (uu____3378) with
| (id', x) -> begin
(bv_to_name x r)
end))


let find_in_module : 'Auu____3395 . env  ->  FStar_Ident.lident  ->  (FStar_Ident.lident  ->  (FStar_Syntax_Syntax.sigelt * Prims.bool)  ->  'Auu____3395)  ->  'Auu____3395  ->  'Auu____3395 = (fun env lid k_global_def k_not_found -> (

let uu____3434 = (FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str)
in (match (uu____3434) with
| FStar_Pervasives_Native.Some (sb) -> begin
(k_global_def lid sb)
end
| FStar_Pervasives_Native.None -> begin
k_not_found
end)))


let try_lookup_id : env  ->  FStar_Ident.ident  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun env id1 -> (

let uu____3472 = (unmangleOpName id1)
in (match (uu____3472) with
| FStar_Pervasives_Native.Some (f) -> begin
FStar_Pervasives_Native.Some (f)
end
| uu____3478 -> begin
(try_lookup_id'' env id1 Exported_id_term_type (fun r -> (

let uu____3484 = (found_local_binding id1.FStar_Ident.idRange r)
in Cont_ok (uu____3484))) (fun uu____3486 -> Cont_fail) (fun uu____3488 -> Cont_ignore) (fun i -> (find_in_module env i (fun uu____3495 uu____3496 -> Cont_fail) Cont_ignore)) (fun uu____3503 uu____3504 -> Cont_fail))
end)))


let lookup_default_id : 'a . env  ->  FStar_Ident.ident  ->  (FStar_Ident.lident  ->  (FStar_Syntax_Syntax.sigelt * Prims.bool)  ->  'a cont_t)  ->  'a cont_t  ->  'a cont_t = (fun env id1 k_global_def k_not_found -> (

let find_in_monad = (match (env.curmonad) with
| FStar_Pervasives_Native.Some (uu____3575) -> begin
(

let lid = (qualify env id1)
in (

let uu____3577 = (FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str)
in (match (uu____3577) with
| FStar_Pervasives_Native.Some (r) -> begin
(

let uu____3601 = (k_global_def lid r)
in FStar_Pervasives_Native.Some (uu____3601))
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

let uu____3624 = (current_module env)
in (qual uu____3624 id1))
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

let rec aux = (fun uu___180_3687 -> (match (uu___180_3687) with
| [] -> begin
(

let uu____3692 = (module_is_defined env lid)
in (match (uu____3692) with
| true -> begin
FStar_Pervasives_Native.Some (lid)
end
| uu____3695 -> begin
FStar_Pervasives_Native.None
end))
end
| (Open_module_or_namespace (ns, Open_namespace))::q when honor_ns -> begin
(

let new_lid = (

let uu____3701 = (

let uu____3702 = (FStar_Ident.path_of_lid ns)
in (

let uu____3705 = (FStar_Ident.path_of_lid lid)
in (FStar_List.append uu____3702 uu____3705)))
in (

let uu____3708 = (FStar_Ident.range_of_lid lid)
in (FStar_Ident.lid_of_path uu____3701 uu____3708)))
in (

let uu____3709 = (module_is_defined env new_lid)
in (match (uu____3709) with
| true -> begin
FStar_Pervasives_Native.Some (new_lid)
end
| uu____3712 -> begin
(aux q)
end)))
end
| (Module_abbrev (name, modul))::uu____3715 when ((Prims.op_Equality nslen (Prims.parse_int "0")) && (Prims.op_Equality name.FStar_Ident.idText lid.FStar_Ident.ident.FStar_Ident.idText)) -> begin
FStar_Pervasives_Native.Some (modul)
end
| (uu____3722)::q -> begin
(aux q)
end))
in (aux env.scope_mods))))


let fail_if_curmodule : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  unit = (fun env ns_original ns_resolved -> (

let uu____3741 = (

let uu____3742 = (current_module env)
in (FStar_Ident.lid_equals ns_resolved uu____3742))
in (match (uu____3741) with
| true -> begin
(

let uu____3743 = (FStar_Ident.lid_equals ns_resolved FStar_Parser_Const.prims_lid)
in (match (uu____3743) with
| true -> begin
()
end
| uu____3744 -> begin
(

let uu____3745 = (

let uu____3750 = (FStar_Util.format1 "Reference %s to current module is forbidden (see GitHub issue #451)" ns_original.FStar_Ident.str)
in ((FStar_Errors.Fatal_ForbiddenReferenceToCurrentModule), (uu____3750)))
in (

let uu____3751 = (FStar_Ident.range_of_lid ns_original)
in (FStar_Errors.raise_error uu____3745 uu____3751)))
end))
end
| uu____3752 -> begin
()
end)))


let fail_if_qualified_by_curmodule : env  ->  FStar_Ident.lident  ->  unit = (fun env lid -> (match (lid.FStar_Ident.ns) with
| [] -> begin
()
end
| uu____3763 -> begin
(

let modul_orig = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in (

let uu____3767 = (resolve_module_name env modul_orig true)
in (match (uu____3767) with
| FStar_Pervasives_Native.Some (modul_res) -> begin
(fail_if_curmodule env modul_orig modul_res)
end
| uu____3771 -> begin
()
end)))
end))


let is_open : env  ->  FStar_Ident.lident  ->  open_kind  ->  Prims.bool = (fun env lid open_kind -> (FStar_List.existsb (fun uu___181_3792 -> (match (uu___181_3792) with
| Open_module_or_namespace (ns, k) -> begin
((Prims.op_Equality k open_kind) && (FStar_Ident.lid_equals lid ns))
end
| uu____3795 -> begin
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
| uu____3891 -> begin
(match (revns) with
| [] -> begin
FStar_Pervasives_Native.None
end
| (ns_last_id)::rev_ns_prefix -> begin
(

let uu____3914 = (aux rev_ns_prefix ns_last_id)
in (FStar_All.pipe_right uu____3914 (FStar_Util.map_option (fun uu____3964 -> (match (uu____3964) with
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

let uu____4034 = (aux ns_rev_prefix ns_last_id)
in (match (uu____4034) with
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

let uu____4095 = (

let uu____4098 = (FStar_Ident.lid_of_ids ids)
in (resolve_module_name env uu____4098 true))
in (match (uu____4095) with
| FStar_Pervasives_Native.Some (m) when (module_is_open env m) -> begin
((ids), ([]))
end
| uu____4112 -> begin
(do_shorten env ids)
end))
end
| uu____4115 -> begin
(do_shorten env ids)
end))))


let resolve_in_open_namespaces'' : 'a . env  ->  FStar_Ident.lident  ->  exported_id_kind  ->  (local_binding  ->  'a cont_t)  ->  (rec_binding  ->  'a cont_t)  ->  (record_or_dc  ->  'a cont_t)  ->  (FStar_Ident.lident  ->  'a cont_t)  ->  ('a cont_t  ->  FStar_Ident.ident  ->  'a cont_t)  ->  'a FStar_Pervasives_Native.option = (fun env lid eikind k_local_binding k_rec_binding k_record f_module l_default -> (match (lid.FStar_Ident.ns) with
| (uu____4231)::uu____4232 -> begin
(

let uu____4235 = (

let uu____4238 = (

let uu____4239 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in (

let uu____4240 = (FStar_Ident.range_of_lid lid)
in (FStar_Ident.set_lid_range uu____4239 uu____4240)))
in (resolve_module_name env uu____4238 true))
in (match (uu____4235) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (modul) -> begin
(

let uu____4244 = (find_in_module_with_includes eikind f_module Cont_fail env modul lid.FStar_Ident.ident)
in (option_of_cont (fun uu____4248 -> FStar_Pervasives_Native.None) uu____4244))
end))
end
| [] -> begin
(try_lookup_id'' env lid.FStar_Ident.ident eikind k_local_binding k_rec_binding k_record f_module l_default)
end))


let cont_of_option : 'a . 'a cont_t  ->  'a FStar_Pervasives_Native.option  ->  'a cont_t = (fun k_none uu___182_4271 -> (match (uu___182_4271) with
| FStar_Pervasives_Native.Some (v1) -> begin
Cont_ok (v1)
end
| FStar_Pervasives_Native.None -> begin
k_none
end))


let resolve_in_open_namespaces' : 'a . env  ->  FStar_Ident.lident  ->  (local_binding  ->  'a FStar_Pervasives_Native.option)  ->  (rec_binding  ->  'a FStar_Pervasives_Native.option)  ->  (FStar_Ident.lident  ->  (FStar_Syntax_Syntax.sigelt * Prims.bool)  ->  'a FStar_Pervasives_Native.option)  ->  'a FStar_Pervasives_Native.option = (fun env lid k_local_binding k_rec_binding k_global_def -> (

let k_global_def' = (fun k lid1 def -> (

let uu____4387 = (k_global_def lid1 def)
in (cont_of_option k uu____4387)))
in (

let f_module = (fun lid' -> (

let k = Cont_ignore
in (find_in_module env lid' (k_global_def' k) k)))
in (

let l_default = (fun k i -> (lookup_default_id env i (k_global_def' k) k))
in (resolve_in_open_namespaces'' env lid Exported_id_term_type (fun l -> (

let uu____4423 = (k_local_binding l)
in (cont_of_option Cont_fail uu____4423))) (fun r -> (

let uu____4429 = (k_rec_binding r)
in (cont_of_option Cont_fail uu____4429))) (fun uu____4433 -> Cont_ignore) f_module l_default)))))


let fv_qual_of_se : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option = (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (uu____4443, uu____4444, uu____4445, l, uu____4447, uu____4448) -> begin
(

let qopt = (FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals (fun uu___183_4459 -> (match (uu___183_4459) with
| FStar_Syntax_Syntax.RecordConstructor (uu____4462, fs) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (((l), (fs))))
end
| uu____4474 -> begin
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
| FStar_Syntax_Syntax.Sig_declare_typ (uu____4480, uu____4481, uu____4482) -> begin
FStar_Pervasives_Native.None
end
| uu____4483 -> begin
FStar_Pervasives_Native.None
end))


let lb_fv : FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.fv = (fun lbs lid -> (

let uu____4498 = (FStar_Util.find_map lbs (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let uu____4506 = (FStar_Syntax_Syntax.fv_eq_lid fv lid)
in (match (uu____4506) with
| true -> begin
FStar_Pervasives_Native.Some (fv)
end
| uu____4509 -> begin
FStar_Pervasives_Native.None
end)))))
in (FStar_All.pipe_right uu____4498 FStar_Util.must)))


let ns_of_lid_equals : FStar_Ident.lident  ->  FStar_Ident.lident  ->  Prims.bool = (fun lid ns -> ((

let uu____4524 = (

let uu____4525 = (FStar_Ident.ids_of_lid ns)
in (FStar_List.length uu____4525))
in (Prims.op_Equality (FStar_List.length lid.FStar_Ident.ns) uu____4524)) && (

let uu____4533 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in (FStar_Ident.lid_equals uu____4533 ns))))


let delta_depth_of_declaration : FStar_Ident.lident  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.delta_depth = (fun lid quals -> (

let dd = (

let uu____4549 = ((FStar_Syntax_Util.is_primop_lid lid) || (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___184_4554 -> (match (uu___184_4554) with
| FStar_Syntax_Syntax.Projector (uu____4555) -> begin
true
end
| FStar_Syntax_Syntax.Discriminator (uu____4560) -> begin
true
end
| uu____4561 -> begin
false
end)))))
in (match (uu____4549) with
| true -> begin
FStar_Syntax_Syntax.delta_equational
end
| uu____4562 -> begin
FStar_Syntax_Syntax.delta_constant
end))
in (

let uu____4563 = ((FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___185_4567 -> (match (uu___185_4567) with
| FStar_Syntax_Syntax.Abstract -> begin
true
end
| uu____4568 -> begin
false
end)))) || ((FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___186_4572 -> (match (uu___186_4572) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| uu____4573 -> begin
false
end)))) && (

let uu____4575 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___187_4579 -> (match (uu___187_4579) with
| FStar_Syntax_Syntax.New -> begin
true
end
| uu____4580 -> begin
false
end))))
in (not (uu____4575)))))
in (match (uu____4563) with
| true -> begin
FStar_Syntax_Syntax.Delta_abstract (dd)
end
| uu____4581 -> begin
dd
end))))


let try_lookup_name : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  foundname FStar_Pervasives_Native.option = (fun any_val exclude_interf env lid -> (

let occurrence_range = (FStar_Ident.range_of_lid lid)
in (

let k_global_def = (fun source_lid uu___190_4623 -> (match (uu___190_4623) with
| (uu____4630, true) when exclude_interf -> begin
FStar_Pervasives_Native.None
end
| (se, uu____4632) -> begin
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____4635) -> begin
(

let uu____4652 = (

let uu____4653 = (

let uu____4660 = (FStar_Syntax_Syntax.fvar source_lid FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in ((uu____4660), (se.FStar_Syntax_Syntax.sigattrs)))
in Term_name (uu____4653))
in FStar_Pervasives_Native.Some (uu____4652))
end
| FStar_Syntax_Syntax.Sig_datacon (uu____4663) -> begin
(

let uu____4678 = (

let uu____4679 = (

let uu____4686 = (

let uu____4687 = (fv_qual_of_se se)
in (FStar_Syntax_Syntax.fvar source_lid FStar_Syntax_Syntax.delta_constant uu____4687))
in ((uu____4686), (se.FStar_Syntax_Syntax.sigattrs)))
in Term_name (uu____4679))
in FStar_Pervasives_Native.Some (uu____4678))
end
| FStar_Syntax_Syntax.Sig_let ((uu____4692, lbs), uu____4694) -> begin
(

let fv = (lb_fv lbs source_lid)
in (

let uu____4704 = (

let uu____4705 = (

let uu____4712 = (FStar_Syntax_Syntax.fvar source_lid fv.FStar_Syntax_Syntax.fv_delta fv.FStar_Syntax_Syntax.fv_qual)
in ((uu____4712), (se.FStar_Syntax_Syntax.sigattrs)))
in Term_name (uu____4705))
in FStar_Pervasives_Native.Some (uu____4704)))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid1, uu____4716, uu____4717) -> begin
(

let quals = se.FStar_Syntax_Syntax.sigquals
in (

let uu____4721 = (any_val || (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___188_4725 -> (match (uu___188_4725) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| uu____4726 -> begin
false
end)))))
in (match (uu____4721) with
| true -> begin
(

let lid2 = (

let uu____4730 = (FStar_Ident.range_of_lid source_lid)
in (FStar_Ident.set_lid_range lid1 uu____4730))
in (

let dd = (delta_depth_of_declaration lid2 quals)
in (

let uu____4732 = (FStar_Util.find_map quals (fun uu___189_4737 -> (match (uu___189_4737) with
| FStar_Syntax_Syntax.Reflectable (refl_monad) -> begin
FStar_Pervasives_Native.Some (refl_monad)
end
| uu____4741 -> begin
FStar_Pervasives_Native.None
end)))
in (match (uu____4732) with
| FStar_Pervasives_Native.Some (refl_monad) -> begin
(

let refl_const = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (refl_monad))) FStar_Pervasives_Native.None occurrence_range)
in FStar_Pervasives_Native.Some (Term_name (((refl_const), (se.FStar_Syntax_Syntax.sigattrs)))))
end
| uu____4750 -> begin
(

let uu____4753 = (

let uu____4754 = (

let uu____4761 = (

let uu____4762 = (fv_qual_of_se se)
in (FStar_Syntax_Syntax.fvar lid2 dd uu____4762))
in ((uu____4761), (se.FStar_Syntax_Syntax.sigattrs)))
in Term_name (uu____4754))
in FStar_Pervasives_Native.Some (uu____4753))
end))))
end
| uu____4767 -> begin
FStar_Pervasives_Native.None
end)))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (ne) -> begin
(

let uu____4769 = (

let uu____4770 = (

let uu____4775 = (

let uu____4776 = (FStar_Ident.range_of_lid source_lid)
in (FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname uu____4776))
in ((se), (uu____4775)))
in Eff_name (uu____4770))
in FStar_Pervasives_Native.Some (uu____4769))
end
| FStar_Syntax_Syntax.Sig_new_effect (ne) -> begin
(

let uu____4778 = (

let uu____4779 = (

let uu____4784 = (

let uu____4785 = (FStar_Ident.range_of_lid source_lid)
in (FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname uu____4785))
in ((se), (uu____4784)))
in Eff_name (uu____4779))
in FStar_Pervasives_Native.Some (uu____4778))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (uu____4786) -> begin
FStar_Pervasives_Native.Some (Eff_name (((se), (source_lid))))
end
| FStar_Syntax_Syntax.Sig_splice (lids, t) -> begin
(

let uu____4805 = (

let uu____4806 = (

let uu____4813 = (FStar_Syntax_Syntax.fvar source_lid (FStar_Syntax_Syntax.Delta_constant_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None)
in ((uu____4813), ([])))
in Term_name (uu____4806))
in FStar_Pervasives_Native.Some (uu____4805))
end
| uu____4816 -> begin
FStar_Pervasives_Native.None
end)
end))
in (

let k_local_binding = (fun r -> (

let t = (

let uu____4834 = (FStar_Ident.range_of_lid lid)
in (found_local_binding uu____4834 r))
in FStar_Pervasives_Native.Some (Term_name (((t), ([]))))))
in (

let k_rec_binding = (fun uu____4850 -> (match (uu____4850) with
| (id1, l, dd) -> begin
(

let uu____4862 = (

let uu____4863 = (

let uu____4870 = (

let uu____4871 = (

let uu____4872 = (FStar_Ident.range_of_lid lid)
in (FStar_Ident.set_lid_range l uu____4872))
in (FStar_Syntax_Syntax.fvar uu____4871 dd FStar_Pervasives_Native.None))
in ((uu____4870), ([])))
in Term_name (uu____4863))
in FStar_Pervasives_Native.Some (uu____4862))
end))
in (

let found_unmangled = (match (lid.FStar_Ident.ns) with
| [] -> begin
(

let uu____4880 = (unmangleOpName lid.FStar_Ident.ident)
in (match (uu____4880) with
| FStar_Pervasives_Native.Some (t) -> begin
FStar_Pervasives_Native.Some (Term_name (((t), ([]))))
end
| uu____4888 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____4891 -> begin
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

let uu____4926 = (try_lookup_name true exclude_interf env lid)
in (match (uu____4926) with
| FStar_Pervasives_Native.Some (Eff_name (o, l)) -> begin
FStar_Pervasives_Native.Some (((o), (l)))
end
| uu____4941 -> begin
FStar_Pervasives_Native.None
end)))


let try_lookup_effect_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident FStar_Pervasives_Native.option = (fun env l -> (

let uu____4960 = (try_lookup_effect_name' (not (env.iface)) env l)
in (match (uu____4960) with
| FStar_Pervasives_Native.Some (o, l1) -> begin
FStar_Pervasives_Native.Some (l1)
end
| uu____4975 -> begin
FStar_Pervasives_Native.None
end)))


let try_lookup_effect_name_and_attributes : env  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.cflag Prims.list) FStar_Pervasives_Native.option = (fun env l -> (

let uu____5000 = (try_lookup_effect_name' (not (env.iface)) env l)
in (match (uu____5000) with
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect (ne); FStar_Syntax_Syntax.sigrng = uu____5016; FStar_Syntax_Syntax.sigquals = uu____5017; FStar_Syntax_Syntax.sigmeta = uu____5018; FStar_Syntax_Syntax.sigattrs = uu____5019}, l1) -> begin
FStar_Pervasives_Native.Some (((l1), (ne.FStar_Syntax_Syntax.cattributes)))
end
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect_for_free (ne); FStar_Syntax_Syntax.sigrng = uu____5038; FStar_Syntax_Syntax.sigquals = uu____5039; FStar_Syntax_Syntax.sigmeta = uu____5040; FStar_Syntax_Syntax.sigattrs = uu____5041}, l1) -> begin
FStar_Pervasives_Native.Some (((l1), (ne.FStar_Syntax_Syntax.cattributes)))
end
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_effect_abbrev (uu____5059, uu____5060, uu____5061, uu____5062, cattributes); FStar_Syntax_Syntax.sigrng = uu____5064; FStar_Syntax_Syntax.sigquals = uu____5065; FStar_Syntax_Syntax.sigmeta = uu____5066; FStar_Syntax_Syntax.sigattrs = uu____5067}, l1) -> begin
FStar_Pervasives_Native.Some (((l1), (cattributes)))
end
| uu____5089 -> begin
FStar_Pervasives_Native.None
end)))


let try_lookup_effect_defn : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl FStar_Pervasives_Native.option = (fun env l -> (

let uu____5114 = (try_lookup_effect_name' (not (env.iface)) env l)
in (match (uu____5114) with
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect (ne); FStar_Syntax_Syntax.sigrng = uu____5124; FStar_Syntax_Syntax.sigquals = uu____5125; FStar_Syntax_Syntax.sigmeta = uu____5126; FStar_Syntax_Syntax.sigattrs = uu____5127}, uu____5128) -> begin
FStar_Pervasives_Native.Some (ne)
end
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect_for_free (ne); FStar_Syntax_Syntax.sigrng = uu____5138; FStar_Syntax_Syntax.sigquals = uu____5139; FStar_Syntax_Syntax.sigmeta = uu____5140; FStar_Syntax_Syntax.sigattrs = uu____5141}, uu____5142) -> begin
FStar_Pervasives_Native.Some (ne)
end
| uu____5151 -> begin
FStar_Pervasives_Native.None
end)))


let is_effect_name : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let uu____5168 = (try_lookup_effect_name env lid)
in (match (uu____5168) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (uu____5171) -> begin
true
end)))


let try_lookup_root_effect_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident FStar_Pervasives_Native.option = (fun env l -> (

let uu____5184 = (try_lookup_effect_name' (not (env.iface)) env l)
in (match (uu____5184) with
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_effect_abbrev (l', uu____5194, uu____5195, uu____5196, uu____5197); FStar_Syntax_Syntax.sigrng = uu____5198; FStar_Syntax_Syntax.sigquals = uu____5199; FStar_Syntax_Syntax.sigmeta = uu____5200; FStar_Syntax_Syntax.sigattrs = uu____5201}, uu____5202) -> begin
(

let rec aux = (fun new_name -> (

let uu____5223 = (FStar_Util.smap_try_find (sigmap env) new_name.FStar_Ident.str)
in (match (uu____5223) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (s, uu____5241) -> begin
(match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_new_effect_for_free (ne) -> begin
(

let uu____5249 = (

let uu____5250 = (FStar_Ident.range_of_lid l)
in (FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname uu____5250))
in FStar_Pervasives_Native.Some (uu____5249))
end
| FStar_Syntax_Syntax.Sig_new_effect (ne) -> begin
(

let uu____5252 = (

let uu____5253 = (FStar_Ident.range_of_lid l)
in (FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname uu____5253))
in FStar_Pervasives_Native.Some (uu____5252))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (uu____5254, uu____5255, uu____5256, cmp, uu____5258) -> begin
(

let l'' = (FStar_Syntax_Util.comp_effect_name cmp)
in (aux l''))
end
| uu____5264 -> begin
FStar_Pervasives_Native.None
end)
end)))
in (aux l'))
end
| FStar_Pervasives_Native.Some (uu____5265, l') -> begin
FStar_Pervasives_Native.Some (l')
end
| uu____5271 -> begin
FStar_Pervasives_Native.None
end)))


let lookup_letbinding_quals : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.qualifier Prims.list = (fun env lid -> (

let k_global_def = (fun lid1 uu___191_5308 -> (match (uu___191_5308) with
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (uu____5317, uu____5318, uu____5319); FStar_Syntax_Syntax.sigrng = uu____5320; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = uu____5322; FStar_Syntax_Syntax.sigattrs = uu____5323}, uu____5324) -> begin
FStar_Pervasives_Native.Some (quals)
end
| uu____5331 -> begin
FStar_Pervasives_Native.None
end))
in (

let uu____5338 = (resolve_in_open_namespaces' env lid (fun uu____5346 -> FStar_Pervasives_Native.None) (fun uu____5350 -> FStar_Pervasives_Native.None) k_global_def)
in (match (uu____5338) with
| FStar_Pervasives_Native.Some (quals) -> begin
quals
end
| uu____5360 -> begin
[]
end))))


let try_lookup_module : env  ->  FStar_Ident.path  ->  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option = (fun env path -> (

let uu____5377 = (FStar_List.tryFind (fun uu____5392 -> (match (uu____5392) with
| (mlid, modul) -> begin
(

let uu____5399 = (FStar_Ident.path_of_lid mlid)
in (Prims.op_Equality uu____5399 path))
end)) env.modules)
in (match (uu____5377) with
| FStar_Pervasives_Native.Some (uu____5402, modul) -> begin
FStar_Pervasives_Native.Some (modul)
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end)))


let try_lookup_let : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun env lid -> (

let k_global_def = (fun lid1 uu___192_5440 -> (match (uu___192_5440) with
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let ((uu____5447, lbs), uu____5449); FStar_Syntax_Syntax.sigrng = uu____5450; FStar_Syntax_Syntax.sigquals = uu____5451; FStar_Syntax_Syntax.sigmeta = uu____5452; FStar_Syntax_Syntax.sigattrs = uu____5453}, uu____5454) -> begin
(

let fv = (lb_fv lbs lid1)
in (

let uu____5468 = (FStar_Syntax_Syntax.fvar lid1 fv.FStar_Syntax_Syntax.fv_delta fv.FStar_Syntax_Syntax.fv_qual)
in FStar_Pervasives_Native.Some (uu____5468)))
end
| uu____5469 -> begin
FStar_Pervasives_Native.None
end))
in (resolve_in_open_namespaces' env lid (fun uu____5475 -> FStar_Pervasives_Native.None) (fun uu____5477 -> FStar_Pervasives_Native.None) k_global_def)))


let try_lookup_definition : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun env lid -> (

let k_global_def = (fun lid1 uu___193_5508 -> (match (uu___193_5508) with
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (lbs, uu____5518); FStar_Syntax_Syntax.sigrng = uu____5519; FStar_Syntax_Syntax.sigquals = uu____5520; FStar_Syntax_Syntax.sigmeta = uu____5521; FStar_Syntax_Syntax.sigattrs = uu____5522}, uu____5523) -> begin
(FStar_Util.find_map (FStar_Pervasives_Native.snd lbs) (fun lb -> (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv lid1) -> begin
FStar_Pervasives_Native.Some (lb.FStar_Syntax_Syntax.lbdef)
end
| uu____5546 -> begin
FStar_Pervasives_Native.None
end)))
end
| uu____5553 -> begin
FStar_Pervasives_Native.None
end))
in (resolve_in_open_namespaces' env lid (fun uu____5563 -> FStar_Pervasives_Native.None) (fun uu____5567 -> FStar_Pervasives_Native.None) k_global_def)))


let empty_include_smap : FStar_Ident.lident Prims.list FStar_ST.ref FStar_Util.smap = (new_sigmap ())


let empty_exported_id_smap : exported_id_set FStar_Util.smap = (new_sigmap ())


let try_lookup_lid' : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.attribute Prims.list) FStar_Pervasives_Native.option = (fun any_val exclude_interface env lid -> (

let uu____5620 = (try_lookup_name any_val exclude_interface env lid)
in (match (uu____5620) with
| FStar_Pervasives_Native.Some (Term_name (e, attrs)) -> begin
FStar_Pervasives_Native.Some (((e), (attrs)))
end
| uu____5645 -> begin
FStar_Pervasives_Native.None
end)))


let drop_attributes : (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.attribute Prims.list) FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun x -> (match (x) with
| FStar_Pervasives_Native.Some (t, uu____5682) -> begin
FStar_Pervasives_Native.Some (t)
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end))


let try_lookup_lid_with_attributes : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.attribute Prims.list) FStar_Pervasives_Native.option = (fun env l -> (try_lookup_lid' env.iface false env l))


let try_lookup_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun env l -> (

let uu____5737 = (try_lookup_lid_with_attributes env l)
in (FStar_All.pipe_right uu____5737 drop_attributes)))


let resolve_to_fully_qualified_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident FStar_Pervasives_Native.option = (fun env l -> (

let uu____5768 = (try_lookup_lid env l)
in (match (uu____5768) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (e) -> begin
(

let uu____5774 = (

let uu____5775 = (FStar_Syntax_Subst.compress e)
in uu____5775.FStar_Syntax_Syntax.n)
in (match (uu____5774) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
FStar_Pervasives_Native.Some (fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end
| uu____5781 -> begin
FStar_Pervasives_Native.None
end))
end)))


let shorten_lid' : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (

let uu____5792 = (shorten_module_path env lid.FStar_Ident.ns true)
in (match (uu____5792) with
| (uu____5801, short) -> begin
(FStar_Ident.lid_of_ns_and_id short lid.FStar_Ident.ident)
end)))


let shorten_lid : env  ->  FStar_Ident.lid  ->  FStar_Ident.lid = (fun env lid -> (match (env.curmodule) with
| FStar_Pervasives_Native.None -> begin
(shorten_lid' env lid)
end
| uu____5821 -> begin
(

let lid_without_ns = (FStar_Ident.lid_of_ns_and_id [] lid.FStar_Ident.ident)
in (

let uu____5825 = (resolve_to_fully_qualified_name env lid_without_ns)
in (match (uu____5825) with
| FStar_Pervasives_Native.Some (lid') when (Prims.op_Equality lid'.FStar_Ident.str lid.FStar_Ident.str) -> begin
lid_without_ns
end
| uu____5829 -> begin
(shorten_lid' env lid)
end)))
end))


let try_lookup_lid_with_attributes_no_resolve : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.attribute Prims.list) FStar_Pervasives_Native.option = (fun env l -> (

let env' = (

let uu___214_5859 = env
in {curmodule = uu___214_5859.curmodule; curmonad = uu___214_5859.curmonad; modules = uu___214_5859.modules; scope_mods = []; exported_ids = empty_exported_id_smap; trans_exported_ids = uu___214_5859.trans_exported_ids; includes = empty_include_smap; sigaccum = uu___214_5859.sigaccum; sigmap = uu___214_5859.sigmap; iface = uu___214_5859.iface; admitted_iface = uu___214_5859.admitted_iface; expect_typ = uu___214_5859.expect_typ; docs = uu___214_5859.docs; remaining_iface_decls = uu___214_5859.remaining_iface_decls; syntax_only = uu___214_5859.syntax_only; ds_hooks = uu___214_5859.ds_hooks; dep_graph = uu___214_5859.dep_graph})
in (try_lookup_lid_with_attributes env' l)))


let try_lookup_lid_no_resolve : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun env l -> (

let uu____5874 = (try_lookup_lid_with_attributes_no_resolve env l)
in (FStar_All.pipe_right uu____5874 drop_attributes)))


let try_lookup_doc : env  ->  FStar_Ident.lid  ->  FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option = (fun env l -> (FStar_Util.smap_try_find env.docs l.FStar_Ident.str))


let try_lookup_datacon : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.fv FStar_Pervasives_Native.option = (fun env lid -> (

let k_global_def = (fun lid1 se -> (match (se) with
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (uu____5940, uu____5941, uu____5942); FStar_Syntax_Syntax.sigrng = uu____5943; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = uu____5945; FStar_Syntax_Syntax.sigattrs = uu____5946}, uu____5947) -> begin
(

let uu____5952 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___194_5956 -> (match (uu___194_5956) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| uu____5957 -> begin
false
end))))
in (match (uu____5952) with
| true -> begin
(

let uu____5960 = (FStar_Syntax_Syntax.lid_as_fv lid1 FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in FStar_Pervasives_Native.Some (uu____5960))
end
| uu____5961 -> begin
FStar_Pervasives_Native.None
end))
end
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (uu____5962); FStar_Syntax_Syntax.sigrng = uu____5963; FStar_Syntax_Syntax.sigquals = uu____5964; FStar_Syntax_Syntax.sigmeta = uu____5965; FStar_Syntax_Syntax.sigattrs = uu____5966}, uu____5967) -> begin
(

let qual1 = (fv_qual_of_se (FStar_Pervasives_Native.fst se))
in (

let uu____5989 = (FStar_Syntax_Syntax.lid_as_fv lid1 FStar_Syntax_Syntax.delta_constant qual1)
in FStar_Pervasives_Native.Some (uu____5989)))
end
| uu____5990 -> begin
FStar_Pervasives_Native.None
end))
in (resolve_in_open_namespaces' env lid (fun uu____5996 -> FStar_Pervasives_Native.None) (fun uu____5998 -> FStar_Pervasives_Native.None) k_global_def)))


let find_all_datacons : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.list FStar_Pervasives_Native.option = (fun env lid -> (

let k_global_def = (fun lid1 uu___195_6031 -> (match (uu___195_6031) with
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (uu____6040, uu____6041, uu____6042, uu____6043, datas, uu____6045); FStar_Syntax_Syntax.sigrng = uu____6046; FStar_Syntax_Syntax.sigquals = uu____6047; FStar_Syntax_Syntax.sigmeta = uu____6048; FStar_Syntax_Syntax.sigattrs = uu____6049}, uu____6050) -> begin
FStar_Pervasives_Native.Some (datas)
end
| uu____6065 -> begin
FStar_Pervasives_Native.None
end))
in (resolve_in_open_namespaces' env lid (fun uu____6075 -> FStar_Pervasives_Native.None) (fun uu____6079 -> FStar_Pervasives_Native.None) k_global_def)))


let record_cache_aux_with_filter : ((((unit  ->  unit) * (unit  ->  unit)) * (((unit  ->  (Prims.int * unit)) * (Prims.int FStar_Pervasives_Native.option  ->  unit)) * ((unit  ->  record_or_dc Prims.list) * (record_or_dc  ->  unit)))) * (unit  ->  unit)) = (

let record_cache = (FStar_Util.mk_ref (([])::[]))
in (

let push1 = (fun uu____6155 -> (

let uu____6156 = (

let uu____6161 = (

let uu____6164 = (FStar_ST.op_Bang record_cache)
in (FStar_List.hd uu____6164))
in (

let uu____6220 = (FStar_ST.op_Bang record_cache)
in (uu____6161)::uu____6220))
in (FStar_ST.op_Colon_Equals record_cache uu____6156)))
in (

let pop1 = (fun uu____6330 -> (

let uu____6331 = (

let uu____6336 = (FStar_ST.op_Bang record_cache)
in (FStar_List.tl uu____6336))
in (FStar_ST.op_Colon_Equals record_cache uu____6331)))
in (

let snapshot1 = (fun uu____6450 -> (FStar_Common.snapshot push1 record_cache ()))
in (

let rollback1 = (fun depth -> (FStar_Common.rollback pop1 record_cache depth))
in (

let peek1 = (fun uu____6516 -> (

let uu____6517 = (FStar_ST.op_Bang record_cache)
in (FStar_List.hd uu____6517)))
in (

let insert = (fun r -> (

let uu____6579 = (

let uu____6584 = (

let uu____6587 = (peek1 ())
in (r)::uu____6587)
in (

let uu____6590 = (

let uu____6595 = (FStar_ST.op_Bang record_cache)
in (FStar_List.tl uu____6595))
in (uu____6584)::uu____6590))
in (FStar_ST.op_Colon_Equals record_cache uu____6579)))
in (

let filter1 = (fun uu____6707 -> (

let rc = (peek1 ())
in (

let filtered = (FStar_List.filter (fun r -> (not (r.is_private_or_abstract))) rc)
in (

let uu____6716 = (

let uu____6721 = (

let uu____6726 = (FStar_ST.op_Bang record_cache)
in (FStar_List.tl uu____6726))
in (filtered)::uu____6721)
in (FStar_ST.op_Colon_Equals record_cache uu____6716)))))
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
| FStar_Syntax_Syntax.Sig_bundle (sigs, uu____7667) -> begin
(

let is_record = (FStar_Util.for_some (fun uu___196_7685 -> (match (uu___196_7685) with
| FStar_Syntax_Syntax.RecordType (uu____7686) -> begin
true
end
| FStar_Syntax_Syntax.RecordConstructor (uu____7695) -> begin
true
end
| uu____7704 -> begin
false
end)))
in (

let find_dc = (fun dc -> (FStar_All.pipe_right sigs (FStar_Util.find_opt (fun uu___197_7728 -> (match (uu___197_7728) with
| {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (lid, uu____7730, uu____7731, uu____7732, uu____7733, uu____7734); FStar_Syntax_Syntax.sigrng = uu____7735; FStar_Syntax_Syntax.sigquals = uu____7736; FStar_Syntax_Syntax.sigmeta = uu____7737; FStar_Syntax_Syntax.sigattrs = uu____7738} -> begin
(FStar_Ident.lid_equals dc lid)
end
| uu____7747 -> begin
false
end)))))
in (FStar_All.pipe_right sigs (FStar_List.iter (fun uu___198_7782 -> (match (uu___198_7782) with
| {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (typename, univs1, parms, uu____7786, uu____7787, (dc)::[]); FStar_Syntax_Syntax.sigrng = uu____7789; FStar_Syntax_Syntax.sigquals = typename_quals; FStar_Syntax_Syntax.sigmeta = uu____7791; FStar_Syntax_Syntax.sigattrs = uu____7792} -> begin
(

let uu____7803 = (

let uu____7804 = (find_dc dc)
in (FStar_All.pipe_left FStar_Util.must uu____7804))
in (match (uu____7803) with
| {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (constrname, uu____7810, t, uu____7812, uu____7813, uu____7814); FStar_Syntax_Syntax.sigrng = uu____7815; FStar_Syntax_Syntax.sigquals = uu____7816; FStar_Syntax_Syntax.sigmeta = uu____7817; FStar_Syntax_Syntax.sigattrs = uu____7818} -> begin
(

let uu____7827 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____7827) with
| (formals, uu____7843) -> begin
(

let is_rec = (is_record typename_quals)
in (

let formals' = (FStar_All.pipe_right formals (FStar_List.collect (fun uu____7896 -> (match (uu____7896) with
| (x, q) -> begin
(

let uu____7909 = ((FStar_Syntax_Syntax.is_null_bv x) || (is_rec && (FStar_Syntax_Syntax.is_implicit q)))
in (match (uu____7909) with
| true -> begin
[]
end
| uu____7920 -> begin
(((x), (q)))::[]
end))
end))))
in (

let fields' = (FStar_All.pipe_right formals' (FStar_List.map (fun uu____7961 -> (match (uu____7961) with
| (x, q) -> begin
((x.FStar_Syntax_Syntax.ppname), (x.FStar_Syntax_Syntax.sort))
end))))
in (

let fields = fields'
in (

let record = {typename = typename; constrname = constrname.FStar_Ident.ident; parms = parms; fields = fields; is_private_or_abstract = ((FStar_List.contains FStar_Syntax_Syntax.Private typename_quals) || (FStar_List.contains FStar_Syntax_Syntax.Abstract typename_quals)); is_record = is_rec}
in ((

let uu____7985 = (

let uu____7988 = (FStar_ST.op_Bang new_globs)
in (Record_or_dc (record))::uu____7988)
in (FStar_ST.op_Colon_Equals new_globs uu____7985));
(match (()) with
| () -> begin
((

let add_field = (fun uu____8091 -> (match (uu____8091) with
| (id1, uu____8097) -> begin
(

let modul = (

let uu____8099 = (FStar_Ident.lid_of_ids constrname.FStar_Ident.ns)
in uu____8099.FStar_Ident.str)
in (

let uu____8100 = (get_exported_id_set e modul)
in (match (uu____8100) with
| FStar_Pervasives_Native.Some (my_ex) -> begin
(

let my_exported_ids = (my_ex Exported_id_field)
in ((

let uu____8134 = (

let uu____8135 = (FStar_ST.op_Bang my_exported_ids)
in (FStar_Util.set_add id1.FStar_Ident.idText uu____8135))
in (FStar_ST.op_Colon_Equals my_exported_ids uu____8134));
(match (()) with
| () -> begin
(

let projname = (

let uu____8221 = (

let uu____8222 = (FStar_Syntax_Util.mk_field_projector_name_from_ident constrname id1)
in uu____8222.FStar_Ident.ident)
in uu____8221.FStar_Ident.idText)
in (

let uu____8224 = (

let uu____8225 = (FStar_ST.op_Bang my_exported_ids)
in (FStar_Util.set_add projname uu____8225))
in (FStar_ST.op_Colon_Equals my_exported_ids uu____8224)))
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
| uu____8319 -> begin
()
end))
end
| uu____8320 -> begin
()
end))))))
end
| uu____8321 -> begin
()
end))


let try_lookup_record_or_dc_by_field_name : env  ->  FStar_Ident.lident  ->  record_or_dc FStar_Pervasives_Native.option = (fun env fieldname -> (

let find_in_cache = (fun fieldname1 -> (

let uu____8342 = ((fieldname1.FStar_Ident.ns), (fieldname1.FStar_Ident.ident))
in (match (uu____8342) with
| (ns, id1) -> begin
(

let uu____8359 = (peek_record_cache ())
in (FStar_Util.find_map uu____8359 (fun record -> (

let uu____8365 = (find_in_record ns id1 record (fun r -> Cont_ok (r)))
in (option_of_cont (fun uu____8371 -> FStar_Pervasives_Native.None) uu____8365)))))
end)))
in (resolve_in_open_namespaces'' env fieldname Exported_id_field (fun uu____8373 -> Cont_ignore) (fun uu____8375 -> Cont_ignore) (fun r -> Cont_ok (r)) (fun fn -> (

let uu____8381 = (find_in_cache fn)
in (cont_of_option Cont_ignore uu____8381))) (fun k uu____8387 -> k))))


let try_lookup_record_by_field_name : env  ->  FStar_Ident.lident  ->  record_or_dc FStar_Pervasives_Native.option = (fun env fieldname -> (

let uu____8402 = (try_lookup_record_or_dc_by_field_name env fieldname)
in (match (uu____8402) with
| FStar_Pervasives_Native.Some (r) when r.is_record -> begin
FStar_Pervasives_Native.Some (r)
end
| uu____8408 -> begin
FStar_Pervasives_Native.None
end)))


let belongs_to_record : env  ->  FStar_Ident.lident  ->  record_or_dc  ->  Prims.bool = (fun env lid record -> (

let uu____8426 = (try_lookup_record_by_field_name env lid)
in (match (uu____8426) with
| FStar_Pervasives_Native.Some (record') when (

let uu____8430 = (

let uu____8431 = (FStar_Ident.path_of_ns record.typename.FStar_Ident.ns)
in (FStar_Ident.text_of_path uu____8431))
in (

let uu____8432 = (

let uu____8433 = (FStar_Ident.path_of_ns record'.typename.FStar_Ident.ns)
in (FStar_Ident.text_of_path uu____8433))
in (Prims.op_Equality uu____8430 uu____8432))) -> begin
(

let uu____8434 = (find_in_record record.typename.FStar_Ident.ns lid.FStar_Ident.ident record (fun uu____8438 -> Cont_ok (())))
in (match (uu____8434) with
| Cont_ok (uu____8439) -> begin
true
end
| uu____8440 -> begin
false
end))
end
| uu____8443 -> begin
false
end)))


let try_lookup_dc_by_field_name : env  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * Prims.bool) FStar_Pervasives_Native.option = (fun env fieldname -> (

let uu____8462 = (try_lookup_record_or_dc_by_field_name env fieldname)
in (match (uu____8462) with
| FStar_Pervasives_Native.Some (r) -> begin
(

let uu____8472 = (

let uu____8477 = (

let uu____8478 = (FStar_Ident.lid_of_ids (FStar_List.append r.typename.FStar_Ident.ns ((r.constrname)::[])))
in (

let uu____8479 = (FStar_Ident.range_of_lid fieldname)
in (FStar_Ident.set_lid_range uu____8478 uu____8479)))
in ((uu____8477), (r.is_record)))
in FStar_Pervasives_Native.Some (uu____8472))
end
| uu____8484 -> begin
FStar_Pervasives_Native.None
end)))


let string_set_ref_new : unit  ->  Prims.string FStar_Util.set FStar_ST.ref = (fun uu____8510 -> (

let uu____8511 = (FStar_Util.new_set FStar_Util.compare)
in (FStar_Util.mk_ref uu____8511)))


let exported_id_set_new : unit  ->  exported_id_kind  ->  Prims.string FStar_Util.set FStar_ST.ref = (fun uu____8538 -> (

let term_type_set = (string_set_ref_new ())
in (

let field_set = (string_set_ref_new ())
in (fun uu___199_8549 -> (match (uu___199_8549) with
| Exported_id_term_type -> begin
term_type_set
end
| Exported_id_field -> begin
field_set
end)))))


let unique : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  Prims.bool = (fun any_val exclude_interface env lid -> (

let filter_scope_mods = (fun uu___200_8601 -> (match (uu___200_8601) with
| Rec_binding (uu____8602) -> begin
true
end
| uu____8603 -> begin
false
end))
in (

let this_env = (

let uu___215_8605 = env
in (

let uu____8606 = (FStar_List.filter filter_scope_mods env.scope_mods)
in {curmodule = uu___215_8605.curmodule; curmonad = uu___215_8605.curmonad; modules = uu___215_8605.modules; scope_mods = uu____8606; exported_ids = empty_exported_id_smap; trans_exported_ids = uu___215_8605.trans_exported_ids; includes = empty_include_smap; sigaccum = uu___215_8605.sigaccum; sigmap = uu___215_8605.sigmap; iface = uu___215_8605.iface; admitted_iface = uu___215_8605.admitted_iface; expect_typ = uu___215_8605.expect_typ; docs = uu___215_8605.docs; remaining_iface_decls = uu___215_8605.remaining_iface_decls; syntax_only = uu___215_8605.syntax_only; ds_hooks = uu___215_8605.ds_hooks; dep_graph = uu___215_8605.dep_graph}))
in (

let uu____8609 = (try_lookup_lid' any_val exclude_interface this_env lid)
in (match (uu____8609) with
| FStar_Pervasives_Native.None -> begin
true
end
| FStar_Pervasives_Native.Some (uu____8624) -> begin
false
end)))))


let push_scope_mod : env  ->  scope_mod  ->  env = (fun env scope_mod -> (

let uu___216_8647 = env
in {curmodule = uu___216_8647.curmodule; curmonad = uu___216_8647.curmonad; modules = uu___216_8647.modules; scope_mods = (scope_mod)::env.scope_mods; exported_ids = uu___216_8647.exported_ids; trans_exported_ids = uu___216_8647.trans_exported_ids; includes = uu___216_8647.includes; sigaccum = uu___216_8647.sigaccum; sigmap = uu___216_8647.sigmap; iface = uu___216_8647.iface; admitted_iface = uu___216_8647.admitted_iface; expect_typ = uu___216_8647.expect_typ; docs = uu___216_8647.docs; remaining_iface_decls = uu___216_8647.remaining_iface_decls; syntax_only = uu___216_8647.syntax_only; ds_hooks = uu___216_8647.ds_hooks; dep_graph = uu___216_8647.dep_graph}))


let push_bv : env  ->  FStar_Ident.ident  ->  (env * FStar_Syntax_Syntax.bv) = (fun env x -> (

let bv = (FStar_Syntax_Syntax.gen_bv x.FStar_Ident.idText (FStar_Pervasives_Native.Some (x.FStar_Ident.idRange)) FStar_Syntax_Syntax.tun)
in (((push_scope_mod env (Local_binding (((x), (bv)))))), (bv))))


let push_top_level_rec_binding : env  ->  FStar_Ident.ident  ->  FStar_Syntax_Syntax.delta_depth  ->  env = (fun env x dd -> (

let l = (qualify env x)
in (

let uu____8679 = ((unique false true env l) || (FStar_Options.interactive ()))
in (match (uu____8679) with
| true -> begin
(push_scope_mod env (Rec_binding (((x), (l), (dd)))))
end
| uu____8680 -> begin
(

let uu____8681 = (FStar_Ident.range_of_lid l)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_DuplicateTopLevelNames), ((Prims.strcat "Duplicate top-level names " l.FStar_Ident.str))) uu____8681))
end))))


let push_sigelt' : Prims.bool  ->  env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun fail_on_dup env s -> (

let err = (fun l -> (

let sopt = (FStar_Util.smap_try_find (sigmap env) l.FStar_Ident.str)
in (

let r = (match (sopt) with
| FStar_Pervasives_Native.Some (se, uu____8716) -> begin
(

let uu____8721 = (FStar_Util.find_opt (FStar_Ident.lid_equals l) (FStar_Syntax_Util.lids_of_sigelt se))
in (match (uu____8721) with
| FStar_Pervasives_Native.Some (l1) -> begin
(

let uu____8725 = (FStar_Ident.range_of_lid l1)
in (FStar_All.pipe_left FStar_Range.string_of_range uu____8725))
end
| FStar_Pervasives_Native.None -> begin
"<unknown>"
end))
end
| FStar_Pervasives_Native.None -> begin
"<unknown>"
end)
in (

let uu____8730 = (

let uu____8735 = (

let uu____8736 = (FStar_Ident.text_of_lid l)
in (FStar_Util.format2 "Duplicate top-level names [%s]; previously declared at %s" uu____8736 r))
in ((FStar_Errors.Fatal_DuplicateTopLevelNames), (uu____8735)))
in (

let uu____8737 = (FStar_Ident.range_of_lid l)
in (FStar_Errors.raise_error uu____8730 uu____8737))))))
in (

let globals = (FStar_Util.mk_ref env.scope_mods)
in (

let env1 = (

let uu____8746 = (match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let (uu____8755) -> begin
((false), (true))
end
| FStar_Syntax_Syntax.Sig_bundle (uu____8762) -> begin
((false), (true))
end
| uu____8771 -> begin
((false), (false))
end)
in (match (uu____8746) with
| (any_val, exclude_interface) -> begin
(

let lids = (FStar_Syntax_Util.lids_of_sigelt s)
in (

let uu____8777 = (FStar_Util.find_map lids (fun l -> (

let uu____8783 = (

let uu____8784 = (unique any_val exclude_interface env l)
in (not (uu____8784)))
in (match (uu____8783) with
| true -> begin
FStar_Pervasives_Native.Some (l)
end
| uu____8787 -> begin
FStar_Pervasives_Native.None
end))))
in (match (uu____8777) with
| FStar_Pervasives_Native.Some (l) when fail_on_dup -> begin
(err l)
end
| uu____8789 -> begin
((extract_record env globals s);
(

let uu___217_8815 = env
in {curmodule = uu___217_8815.curmodule; curmonad = uu___217_8815.curmonad; modules = uu___217_8815.modules; scope_mods = uu___217_8815.scope_mods; exported_ids = uu___217_8815.exported_ids; trans_exported_ids = uu___217_8815.trans_exported_ids; includes = uu___217_8815.includes; sigaccum = (s)::env.sigaccum; sigmap = uu___217_8815.sigmap; iface = uu___217_8815.iface; admitted_iface = uu___217_8815.admitted_iface; expect_typ = uu___217_8815.expect_typ; docs = uu___217_8815.docs; remaining_iface_decls = uu___217_8815.remaining_iface_decls; syntax_only = uu___217_8815.syntax_only; ds_hooks = uu___217_8815.ds_hooks; dep_graph = uu___217_8815.dep_graph});
)
end)))
end))
in (

let env2 = (

let uu___218_8817 = env1
in (

let uu____8818 = (FStar_ST.op_Bang globals)
in {curmodule = uu___218_8817.curmodule; curmonad = uu___218_8817.curmonad; modules = uu___218_8817.modules; scope_mods = uu____8818; exported_ids = uu___218_8817.exported_ids; trans_exported_ids = uu___218_8817.trans_exported_ids; includes = uu___218_8817.includes; sigaccum = uu___218_8817.sigaccum; sigmap = uu___218_8817.sigmap; iface = uu___218_8817.iface; admitted_iface = uu___218_8817.admitted_iface; expect_typ = uu___218_8817.expect_typ; docs = uu___218_8817.docs; remaining_iface_decls = uu___218_8817.remaining_iface_decls; syntax_only = uu___218_8817.syntax_only; ds_hooks = uu___218_8817.ds_hooks; dep_graph = uu___218_8817.dep_graph}))
in (

let uu____8866 = (match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____8892) -> begin
(

let uu____8901 = (FStar_List.map (fun se -> (((FStar_Syntax_Util.lids_of_sigelt se)), (se))) ses)
in ((env2), (uu____8901)))
end
| uu____8928 -> begin
((env2), (((((FStar_Syntax_Util.lids_of_sigelt s)), (s)))::[]))
end)
in (match (uu____8866) with
| (env3, lss) -> begin
((FStar_All.pipe_right lss (FStar_List.iter (fun uu____8987 -> (match (uu____8987) with
| (lids, se) -> begin
(FStar_All.pipe_right lids (FStar_List.iter (fun lid -> ((

let uu____9009 = (

let uu____9012 = (FStar_ST.op_Bang globals)
in (Top_level_def (lid.FStar_Ident.ident))::uu____9012)
in (FStar_ST.op_Colon_Equals globals uu____9009));
(match (()) with
| () -> begin
(

let modul = (

let uu____9106 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in uu____9106.FStar_Ident.str)
in ((

let uu____9108 = (get_exported_id_set env3 modul)
in (match (uu____9108) with
| FStar_Pervasives_Native.Some (f) -> begin
(

let my_exported_ids = (f Exported_id_term_type)
in (

let uu____9141 = (

let uu____9142 = (FStar_ST.op_Bang my_exported_ids)
in (FStar_Util.set_add lid.FStar_Ident.ident.FStar_Ident.idText uu____9142))
in (FStar_ST.op_Colon_Equals my_exported_ids uu____9141)))
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

let uu___219_9238 = env3
in (

let uu____9239 = (FStar_ST.op_Bang globals)
in {curmodule = uu___219_9238.curmodule; curmonad = uu___219_9238.curmonad; modules = uu___219_9238.modules; scope_mods = uu____9239; exported_ids = uu___219_9238.exported_ids; trans_exported_ids = uu___219_9238.trans_exported_ids; includes = uu___219_9238.includes; sigaccum = uu___219_9238.sigaccum; sigmap = uu___219_9238.sigmap; iface = uu___219_9238.iface; admitted_iface = uu___219_9238.admitted_iface; expect_typ = uu___219_9238.expect_typ; docs = uu___219_9238.docs; remaining_iface_decls = uu___219_9238.remaining_iface_decls; syntax_only = uu___219_9238.syntax_only; ds_hooks = uu___219_9238.ds_hooks; dep_graph = uu___219_9238.dep_graph}))
in env4);
)
end)))))))


let push_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env se -> (push_sigelt' true env se))


let push_sigelt_force : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env se -> (push_sigelt' false env se))


let push_namespace : env  ->  FStar_Ident.lident  ->  env = (fun env ns -> (

let uu____9317 = (

let uu____9322 = (resolve_module_name env ns false)
in (match (uu____9322) with
| FStar_Pervasives_Native.None -> begin
(

let modules = env.modules
in (

let uu____9336 = (FStar_All.pipe_right modules (FStar_Util.for_some (fun uu____9352 -> (match (uu____9352) with
| (m, uu____9358) -> begin
(

let uu____9359 = (

let uu____9360 = (FStar_Ident.text_of_lid m)
in (Prims.strcat uu____9360 "."))
in (

let uu____9361 = (

let uu____9362 = (FStar_Ident.text_of_lid ns)
in (Prims.strcat uu____9362 "."))
in (FStar_Util.starts_with uu____9359 uu____9361)))
end))))
in (match (uu____9336) with
| true -> begin
((ns), (Open_namespace))
end
| uu____9367 -> begin
(

let uu____9368 = (

let uu____9373 = (

let uu____9374 = (FStar_Ident.text_of_lid ns)
in (FStar_Util.format1 "Namespace %s cannot be found" uu____9374))
in ((FStar_Errors.Fatal_NameSpaceNotFound), (uu____9373)))
in (

let uu____9375 = (FStar_Ident.range_of_lid ns)
in (FStar_Errors.raise_error uu____9368 uu____9375)))
end)))
end
| FStar_Pervasives_Native.Some (ns') -> begin
((fail_if_curmodule env ns ns');
((ns'), (Open_module));
)
end))
in (match (uu____9317) with
| (ns', kd) -> begin
((env.ds_hooks.ds_push_open_hook env ((ns'), (kd)));
(push_scope_mod env (Open_module_or_namespace (((ns'), (kd)))));
)
end)))


let push_include : env  ->  FStar_Ident.lident  ->  env = (fun env ns -> (

let ns0 = ns
in (

let uu____9396 = (resolve_module_name env ns false)
in (match (uu____9396) with
| FStar_Pervasives_Native.Some (ns1) -> begin
((env.ds_hooks.ds_push_include_hook env ns1);
(fail_if_curmodule env ns0 ns1);
(

let env1 = (push_scope_mod env (Open_module_or_namespace (((ns1), (Open_module)))))
in (

let curmod = (

let uu____9404 = (current_module env1)
in uu____9404.FStar_Ident.str)
in ((

let uu____9406 = (FStar_Util.smap_try_find env1.includes curmod)
in (match (uu____9406) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (incl) -> begin
(

let uu____9430 = (

let uu____9433 = (FStar_ST.op_Bang incl)
in (ns1)::uu____9433)
in (FStar_ST.op_Colon_Equals incl uu____9430))
end));
(match (()) with
| () -> begin
(

let uu____9526 = (get_trans_exported_id_set env1 ns1.FStar_Ident.str)
in (match (uu____9526) with
| FStar_Pervasives_Native.Some (ns_trans_exports) -> begin
((

let uu____9546 = (

let uu____9641 = (get_exported_id_set env1 curmod)
in (

let uu____9687 = (get_trans_exported_id_set env1 curmod)
in ((uu____9641), (uu____9687))))
in (match (uu____9546) with
| (FStar_Pervasives_Native.Some (cur_exports), FStar_Pervasives_Native.Some (cur_trans_exports)) -> begin
(

let update_exports = (fun k -> (

let ns_ex = (

let uu____10094 = (ns_trans_exports k)
in (FStar_ST.op_Bang uu____10094))
in (

let ex = (cur_exports k)
in ((

let uu____10268 = (

let uu____10271 = (FStar_ST.op_Bang ex)
in (FStar_Util.set_difference uu____10271 ns_ex))
in (FStar_ST.op_Colon_Equals ex uu____10268));
(match (()) with
| () -> begin
(

let trans_ex = (cur_trans_exports k)
in (

let uu____10463 = (

let uu____10466 = (FStar_ST.op_Bang trans_ex)
in (FStar_Util.set_union uu____10466 ns_ex))
in (FStar_ST.op_Colon_Equals trans_ex uu____10463)))
end);
))))
in (FStar_List.iter update_exports all_exported_id_kinds))
end
| uu____10595 -> begin
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

let uu____10695 = (

let uu____10700 = (FStar_Util.format1 "include: Module %s was not prepared" ns1.FStar_Ident.str)
in ((FStar_Errors.Fatal_IncludeModuleNotPrepared), (uu____10700)))
in (

let uu____10701 = (FStar_Ident.range_of_lid ns1)
in (FStar_Errors.raise_error uu____10695 uu____10701)))
end))
end);
)));
)
end
| uu____10702 -> begin
(

let uu____10705 = (

let uu____10710 = (FStar_Util.format1 "include: Module %s cannot be found" ns.FStar_Ident.str)
in ((FStar_Errors.Fatal_ModuleNotFound), (uu____10710)))
in (

let uu____10711 = (FStar_Ident.range_of_lid ns)
in (FStar_Errors.raise_error uu____10705 uu____10711)))
end))))


let push_module_abbrev : env  ->  FStar_Ident.ident  ->  FStar_Ident.lident  ->  env = (fun env x l -> (

let uu____10727 = (module_is_defined env l)
in (match (uu____10727) with
| true -> begin
((fail_if_curmodule env l l);
(env.ds_hooks.ds_push_module_abbrev_hook env x l);
(push_scope_mod env (Module_abbrev (((x), (l)))));
)
end
| uu____10730 -> begin
(

let uu____10731 = (

let uu____10736 = (

let uu____10737 = (FStar_Ident.text_of_lid l)
in (FStar_Util.format1 "Module %s cannot be found" uu____10737))
in ((FStar_Errors.Fatal_ModuleNotFound), (uu____10736)))
in (

let uu____10738 = (FStar_Ident.range_of_lid l)
in (FStar_Errors.raise_error uu____10731 uu____10738)))
end)))


let push_doc : env  ->  FStar_Ident.lident  ->  FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option  ->  env = (fun env l doc_opt -> (match (doc_opt) with
| FStar_Pervasives_Native.None -> begin
env
end
| FStar_Pervasives_Native.Some (doc1) -> begin
((

let uu____10760 = (FStar_Util.smap_try_find env.docs l.FStar_Ident.str)
in (match (uu____10760) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (old_doc) -> begin
(

let uu____10764 = (FStar_Ident.range_of_lid l)
in (

let uu____10765 = (

let uu____10770 = (

let uu____10771 = (FStar_Ident.string_of_lid l)
in (

let uu____10772 = (FStar_Parser_AST.string_of_fsdoc old_doc)
in (

let uu____10773 = (FStar_Parser_AST.string_of_fsdoc doc1)
in (FStar_Util.format3 "Overwriting doc of %s; old doc was [%s]; new doc are [%s]" uu____10771 uu____10772 uu____10773))))
in ((FStar_Errors.Warning_DocOverwrite), (uu____10770)))
in (FStar_Errors.log_issue uu____10764 uu____10765)))
end));
(FStar_Util.smap_add env.docs l.FStar_Ident.str doc1);
env;
)
end))


let check_admits : env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.modul = (fun env m -> (

let admitted_sig_lids = (FStar_All.pipe_right env.sigaccum (FStar_List.fold_left (fun lids se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_declare_typ (l, u, t) when (

let uu____10815 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_List.contains FStar_Syntax_Syntax.Assumption))
in (not (uu____10815))) -> begin
(

let uu____10818 = (FStar_Util.smap_try_find (sigmap env) l.FStar_Ident.str)
in (match (uu____10818) with
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (uu____10831); FStar_Syntax_Syntax.sigrng = uu____10832; FStar_Syntax_Syntax.sigquals = uu____10833; FStar_Syntax_Syntax.sigmeta = uu____10834; FStar_Syntax_Syntax.sigattrs = uu____10835}, uu____10836) -> begin
lids
end
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (uu____10851); FStar_Syntax_Syntax.sigrng = uu____10852; FStar_Syntax_Syntax.sigquals = uu____10853; FStar_Syntax_Syntax.sigmeta = uu____10854; FStar_Syntax_Syntax.sigattrs = uu____10855}, uu____10856) -> begin
lids
end
| uu____10881 -> begin
((

let uu____10889 = (

let uu____10890 = (FStar_Options.interactive ())
in (not (uu____10890)))
in (match (uu____10889) with
| true -> begin
(

let uu____10891 = (FStar_Ident.range_of_lid l)
in (

let uu____10892 = (

let uu____10897 = (

let uu____10898 = (FStar_Ident.string_of_lid l)
in (FStar_Util.format1 "Admitting %s without a definition" uu____10898))
in ((FStar_Errors.Warning_AdmitWithoutDefinition), (uu____10897)))
in (FStar_Errors.log_issue uu____10891 uu____10892)))
end
| uu____10899 -> begin
()
end));
(

let quals = (FStar_Syntax_Syntax.Assumption)::se.FStar_Syntax_Syntax.sigquals
in ((FStar_Util.smap_add (sigmap env) l.FStar_Ident.str (((

let uu___220_10909 = se
in {FStar_Syntax_Syntax.sigel = uu___220_10909.FStar_Syntax_Syntax.sigel; FStar_Syntax_Syntax.sigrng = uu___220_10909.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = uu___220_10909.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___220_10909.FStar_Syntax_Syntax.sigattrs})), (false)));
(l)::lids;
));
)
end))
end
| uu____10910 -> begin
lids
end)) []))
in (

let uu___221_10911 = m
in (

let uu____10912 = (FStar_All.pipe_right m.FStar_Syntax_Syntax.declarations (FStar_List.map (fun s -> (match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____10922, uu____10923) when (FStar_List.existsb (fun l -> (FStar_Ident.lid_equals l lid)) admitted_sig_lids) -> begin
(

let uu___222_10926 = s
in {FStar_Syntax_Syntax.sigel = uu___222_10926.FStar_Syntax_Syntax.sigel; FStar_Syntax_Syntax.sigrng = uu___222_10926.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Assumption)::s.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___222_10926.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___222_10926.FStar_Syntax_Syntax.sigattrs})
end
| uu____10927 -> begin
s
end))))
in {FStar_Syntax_Syntax.name = uu___221_10911.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = uu____10912; FStar_Syntax_Syntax.exports = uu___221_10911.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = uu___221_10911.FStar_Syntax_Syntax.is_interface}))))


let finish : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env modul -> ((FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations (FStar_List.iter (fun se -> (

let quals = se.FStar_Syntax_Syntax.sigquals
in (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____10950) -> begin
(match (((FStar_List.contains FStar_Syntax_Syntax.Private quals) || (FStar_List.contains FStar_Syntax_Syntax.Abstract quals))) with
| true -> begin
(FStar_All.pipe_right ses (FStar_List.iter (fun se1 -> (match (se1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (lid, uu____10970, uu____10971, uu____10972, uu____10973, uu____10974) -> begin
(FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str)
end
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, univ_names, binders, typ, uu____10987, uu____10988) -> begin
((FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str);
(match ((not ((FStar_List.contains FStar_Syntax_Syntax.Private quals)))) with
| true -> begin
(

let sigel = (

let uu____11003 = (

let uu____11010 = (

let uu____11011 = (FStar_Ident.range_of_lid lid)
in (

let uu____11012 = (

let uu____11019 = (

let uu____11020 = (

let uu____11035 = (FStar_Syntax_Syntax.mk_Total typ)
in ((binders), (uu____11035)))
in FStar_Syntax_Syntax.Tm_arrow (uu____11020))
in (FStar_Syntax_Syntax.mk uu____11019))
in (uu____11012 FStar_Pervasives_Native.None uu____11011)))
in ((lid), (univ_names), (uu____11010)))
in FStar_Syntax_Syntax.Sig_declare_typ (uu____11003))
in (

let se2 = (

let uu___223_11052 = se1
in {FStar_Syntax_Syntax.sigel = sigel; FStar_Syntax_Syntax.sigrng = uu___223_11052.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Assumption)::quals; FStar_Syntax_Syntax.sigmeta = uu___223_11052.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___223_11052.FStar_Syntax_Syntax.sigattrs})
in (FStar_Util.smap_add (sigmap env) lid.FStar_Ident.str ((se2), (false)))))
end
| uu____11057 -> begin
()
end);
)
end
| uu____11058 -> begin
()
end))))
end
| uu____11059 -> begin
()
end)
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____11061, uu____11062) -> begin
(match ((FStar_List.contains FStar_Syntax_Syntax.Private quals)) with
| true -> begin
(FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str)
end
| uu____11067 -> begin
()
end)
end
| FStar_Syntax_Syntax.Sig_let ((uu____11068, lbs), uu____11070) -> begin
((match (((FStar_List.contains FStar_Syntax_Syntax.Private quals) || (FStar_List.contains FStar_Syntax_Syntax.Abstract quals))) with
| true -> begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (

let uu____11085 = (

let uu____11086 = (

let uu____11087 = (

let uu____11090 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in uu____11090.FStar_Syntax_Syntax.fv_name)
in uu____11087.FStar_Syntax_Syntax.v)
in uu____11086.FStar_Ident.str)
in (FStar_Util.smap_remove (sigmap env) uu____11085)))))
end
| uu____11095 -> begin
()
end);
(match (((FStar_List.contains FStar_Syntax_Syntax.Abstract quals) && (not ((FStar_List.contains FStar_Syntax_Syntax.Private quals))))) with
| true -> begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (

let lid = (

let uu____11104 = (

let uu____11107 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in uu____11107.FStar_Syntax_Syntax.fv_name)
in uu____11104.FStar_Syntax_Syntax.v)
in (

let quals1 = (FStar_Syntax_Syntax.Assumption)::quals
in (

let decl = (

let uu___224_11112 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp))); FStar_Syntax_Syntax.sigrng = uu___224_11112.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = uu___224_11112.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___224_11112.FStar_Syntax_Syntax.sigattrs})
in (FStar_Util.smap_add (sigmap env) lid.FStar_Ident.str ((decl), (false)))))))))
end
| uu____11117 -> begin
()
end);
)
end
| uu____11118 -> begin
()
end)))));
(

let curmod = (

let uu____11120 = (current_module env)
in uu____11120.FStar_Ident.str)
in ((

let uu____11122 = (

let uu____11217 = (get_exported_id_set env curmod)
in (

let uu____11263 = (get_trans_exported_id_set env curmod)
in ((uu____11217), (uu____11263))))
in (match (uu____11122) with
| (FStar_Pervasives_Native.Some (cur_ex), FStar_Pervasives_Native.Some (cur_trans_ex)) -> begin
(

let update_exports = (fun eikind -> (

let cur_ex_set = (

let uu____11672 = (cur_ex eikind)
in (FStar_ST.op_Bang uu____11672))
in (

let cur_trans_ex_set_ref = (cur_trans_ex eikind)
in (

let uu____11859 = (

let uu____11862 = (FStar_ST.op_Bang cur_trans_ex_set_ref)
in (FStar_Util.set_union cur_ex_set uu____11862))
in (FStar_ST.op_Colon_Equals cur_trans_ex_set_ref uu____11859)))))
in (FStar_List.iter update_exports all_exported_id_kinds))
end
| uu____11991 -> begin
()
end));
(match (()) with
| () -> begin
((filter_record_cache ());
(match (()) with
| () -> begin
(

let uu___225_12087 = env
in {curmodule = FStar_Pervasives_Native.None; curmonad = uu___225_12087.curmonad; modules = (((modul.FStar_Syntax_Syntax.name), (modul)))::env.modules; scope_mods = []; exported_ids = uu___225_12087.exported_ids; trans_exported_ids = uu___225_12087.trans_exported_ids; includes = uu___225_12087.includes; sigaccum = []; sigmap = uu___225_12087.sigmap; iface = uu___225_12087.iface; admitted_iface = uu___225_12087.admitted_iface; expect_typ = uu___225_12087.expect_typ; docs = uu___225_12087.docs; remaining_iface_decls = uu___225_12087.remaining_iface_decls; syntax_only = uu___225_12087.syntax_only; ds_hooks = uu___225_12087.ds_hooks; dep_graph = uu___225_12087.dep_graph})
end);
)
end);
));
))


let stack : env Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let push : env  ->  env = (fun env -> (FStar_Util.atomically (fun uu____12123 -> ((push_record_cache ());
(

let uu____12126 = (

let uu____12129 = (FStar_ST.op_Bang stack)
in (env)::uu____12129)
in (FStar_ST.op_Colon_Equals stack uu____12126));
(

let uu___226_12178 = env
in (

let uu____12179 = (FStar_Util.smap_copy env.exported_ids)
in (

let uu____12184 = (FStar_Util.smap_copy env.trans_exported_ids)
in (

let uu____12189 = (FStar_Util.smap_copy env.includes)
in (

let uu____12200 = (FStar_Util.smap_copy env.sigmap)
in (

let uu____12211 = (FStar_Util.smap_copy env.docs)
in {curmodule = uu___226_12178.curmodule; curmonad = uu___226_12178.curmonad; modules = uu___226_12178.modules; scope_mods = uu___226_12178.scope_mods; exported_ids = uu____12179; trans_exported_ids = uu____12184; includes = uu____12189; sigaccum = uu___226_12178.sigaccum; sigmap = uu____12200; iface = uu___226_12178.iface; admitted_iface = uu___226_12178.admitted_iface; expect_typ = uu___226_12178.expect_typ; docs = uu____12211; remaining_iface_decls = uu___226_12178.remaining_iface_decls; syntax_only = uu___226_12178.syntax_only; ds_hooks = uu___226_12178.ds_hooks; dep_graph = uu___226_12178.dep_graph}))))));
))))


let pop : unit  ->  env = (fun uu____12218 -> (FStar_Util.atomically (fun uu____12225 -> (

let uu____12226 = (FStar_ST.op_Bang stack)
in (match (uu____12226) with
| (env)::tl1 -> begin
((pop_record_cache ());
(FStar_ST.op_Colon_Equals stack tl1);
env;
)
end
| uu____12281 -> begin
(failwith "Impossible: Too many pops")
end)))))


let snapshot : env  ->  (Prims.int * env) = (fun env -> (FStar_Common.snapshot push stack env))


let rollback : Prims.int FStar_Pervasives_Native.option  ->  env = (fun depth -> (FStar_Common.rollback pop stack depth))


let export_interface : FStar_Ident.lident  ->  env  ->  env = (fun m env -> (

let sigelt_in_m = (fun se -> (match ((FStar_Syntax_Util.lids_of_sigelt se)) with
| (l)::uu____12319 -> begin
(Prims.op_Equality l.FStar_Ident.nsstr m.FStar_Ident.str)
end
| uu____12322 -> begin
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

let uu____12356 = (FStar_Util.smap_try_find sm' k)
in (match (uu____12356) with
| FStar_Pervasives_Native.Some (se, true) when (sigelt_in_m se) -> begin
((FStar_Util.smap_remove sm' k);
(

let se1 = (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_declare_typ (l, u, t) -> begin
(

let uu___227_12381 = se
in {FStar_Syntax_Syntax.sigel = uu___227_12381.FStar_Syntax_Syntax.sigel; FStar_Syntax_Syntax.sigrng = uu___227_12381.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Assumption)::se.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___227_12381.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___227_12381.FStar_Syntax_Syntax.sigattrs})
end
| uu____12382 -> begin
se
end)
in (FStar_Util.smap_add sm' k ((se1), (false))));
)
end
| uu____12387 -> begin
()
end)))));
env1;
)))))))


let finish_module_or_interface : env  ->  FStar_Syntax_Syntax.modul  ->  (env * FStar_Syntax_Syntax.modul) = (fun env modul -> (

let modul1 = (match ((not (modul.FStar_Syntax_Syntax.is_interface))) with
| true -> begin
(check_admits env modul)
end
| uu____12409 -> begin
modul
end)
in (

let uu____12410 = (finish env modul1)
in ((uu____12410), (modul1)))))

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

let uu____12498 = (

let uu____12501 = (e Exported_id_term_type)
in (FStar_ST.op_Bang uu____12501))
in (FStar_Util.set_elements uu____12498))
in (

let fields = (

let uu____12615 = (

let uu____12618 = (e Exported_id_field)
in (FStar_ST.op_Bang uu____12618))
in (FStar_Util.set_elements uu____12615))
in {exported_id_terms = terms; exported_id_fields = fields})))


let as_exported_id_set : exported_ids FStar_Pervasives_Native.option  ->  exported_id_kind  ->  Prims.string FStar_Util.set FStar_ST.ref = (fun e -> (match (e) with
| FStar_Pervasives_Native.None -> begin
(exported_id_set_new ())
end
| FStar_Pervasives_Native.Some (e1) -> begin
(

let terms = (

let uu____12769 = (FStar_Util.as_set e1.exported_id_terms FStar_Util.compare)
in (FStar_Util.mk_ref uu____12769))
in (

let fields = (

let uu____12779 = (FStar_Util.as_set e1.exported_id_fields FStar_Util.compare)
in (FStar_Util.mk_ref uu____12779))
in (fun uu___201_12784 -> (match (uu___201_12784) with
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


let as_includes : 'Auu____12915 . 'Auu____12915 Prims.list FStar_Pervasives_Native.option  ->  'Auu____12915 Prims.list FStar_ST.ref = (fun uu___202_12928 -> (match (uu___202_12928) with
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

let uu____12969 = (FStar_Util.smap_try_find m mname)
in (FStar_Util.map_opt uu____12969 as_exported_ids)))
in (

let uu____12975 = (as_ids_opt env.exported_ids)
in (

let uu____12978 = (as_ids_opt env.trans_exported_ids)
in (

let uu____12981 = (

let uu____12986 = (FStar_Util.smap_try_find env.includes mname)
in (FStar_Util.map_opt uu____12986 (fun r -> (FStar_ST.op_Bang r))))
in {mii_exported_ids = uu____12975; mii_trans_exported_ids = uu____12978; mii_includes = uu____12981}))))))


let prepare_module_or_interface : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  module_inclusion_info  ->  (env * Prims.bool) = (fun intf admitted env mname mii -> (

let prep = (fun env1 -> (

let filename = (

let uu____13101 = (FStar_Ident.text_of_lid mname)
in (FStar_Util.strcat uu____13101 ".fst"))
in (

let auto_open = (FStar_Parser_Dep.hard_coded_dependencies filename)
in (

let auto_open1 = (

let convert_kind = (fun uu___203_13121 -> (match (uu___203_13121) with
| FStar_Parser_Dep.Open_namespace -> begin
Open_namespace
end
| FStar_Parser_Dep.Open_module -> begin
Open_module
end))
in (FStar_List.map (fun uu____13133 -> (match (uu____13133) with
| (lid, kind) -> begin
((lid), ((convert_kind kind)))
end)) auto_open))
in (

let namespace_of_module = (match (((FStar_List.length mname.FStar_Ident.ns) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____13157 = (

let uu____13162 = (FStar_Ident.lid_of_ids mname.FStar_Ident.ns)
in ((uu____13162), (Open_namespace)))
in (uu____13157)::[])
end
| uu____13171 -> begin
[]
end)
in (

let auto_open2 = (FStar_List.append namespace_of_module (FStar_List.rev auto_open1))
in ((

let uu____13192 = (as_exported_id_set mii.mii_exported_ids)
in (FStar_Util.smap_add env1.exported_ids mname.FStar_Ident.str uu____13192));
(match (()) with
| () -> begin
((

let uu____13219 = (as_exported_id_set mii.mii_trans_exported_ids)
in (FStar_Util.smap_add env1.trans_exported_ids mname.FStar_Ident.str uu____13219));
(match (()) with
| () -> begin
((

let uu____13246 = (as_includes mii.mii_includes)
in (FStar_Util.smap_add env1.includes mname.FStar_Ident.str uu____13246));
(match (()) with
| () -> begin
(

let env' = (

let uu___228_13278 = env1
in (

let uu____13279 = (FStar_List.map (fun x -> Open_module_or_namespace (x)) auto_open2)
in {curmodule = FStar_Pervasives_Native.Some (mname); curmonad = uu___228_13278.curmonad; modules = uu___228_13278.modules; scope_mods = uu____13279; exported_ids = uu___228_13278.exported_ids; trans_exported_ids = uu___228_13278.trans_exported_ids; includes = uu___228_13278.includes; sigaccum = uu___228_13278.sigaccum; sigmap = env1.sigmap; iface = intf; admitted_iface = admitted; expect_typ = uu___228_13278.expect_typ; docs = uu___228_13278.docs; remaining_iface_decls = uu___228_13278.remaining_iface_decls; syntax_only = uu___228_13278.syntax_only; ds_hooks = uu___228_13278.ds_hooks; dep_graph = uu___228_13278.dep_graph}))
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

let uu____13291 = (FStar_All.pipe_right env.modules (FStar_Util.find_opt (fun uu____13317 -> (match (uu____13317) with
| (l, uu____13323) -> begin
(FStar_Ident.lid_equals l mname)
end))))
in (match (uu____13291) with
| FStar_Pervasives_Native.None -> begin
(

let uu____13332 = (prep env)
in ((uu____13332), (false)))
end
| FStar_Pervasives_Native.Some (uu____13333, m) -> begin
((

let uu____13340 = ((

let uu____13343 = (FStar_Options.interactive ())
in (not (uu____13343))) && ((not (m.FStar_Syntax_Syntax.is_interface)) || intf))
in (match (uu____13340) with
| true -> begin
(

let uu____13344 = (

let uu____13349 = (FStar_Util.format1 "Duplicate module or interface name: %s" mname.FStar_Ident.str)
in ((FStar_Errors.Fatal_DuplicateModuleOrInterface), (uu____13349)))
in (

let uu____13350 = (FStar_Ident.range_of_lid mname)
in (FStar_Errors.raise_error uu____13344 uu____13350)))
end
| uu____13351 -> begin
()
end));
(

let uu____13352 = (

let uu____13353 = (push env)
in (prep uu____13353))
in ((uu____13352), (true)));
)
end))))


let enter_monad_scope : env  ->  FStar_Ident.ident  ->  env = (fun env mname -> (match (env.curmonad) with
| FStar_Pervasives_Native.Some (mname') -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_MonadAlreadyDefined), ((Prims.strcat "Trying to define monad " (Prims.strcat mname.FStar_Ident.idText (Prims.strcat ", but already in monad scope " mname'.FStar_Ident.idText))))) mname.FStar_Ident.idRange)
end
| FStar_Pervasives_Native.None -> begin
(

let uu___229_13365 = env
in {curmodule = uu___229_13365.curmodule; curmonad = FStar_Pervasives_Native.Some (mname); modules = uu___229_13365.modules; scope_mods = uu___229_13365.scope_mods; exported_ids = uu___229_13365.exported_ids; trans_exported_ids = uu___229_13365.trans_exported_ids; includes = uu___229_13365.includes; sigaccum = uu___229_13365.sigaccum; sigmap = uu___229_13365.sigmap; iface = uu___229_13365.iface; admitted_iface = uu___229_13365.admitted_iface; expect_typ = uu___229_13365.expect_typ; docs = uu___229_13365.docs; remaining_iface_decls = uu___229_13365.remaining_iface_decls; syntax_only = uu___229_13365.syntax_only; ds_hooks = uu___229_13365.ds_hooks; dep_graph = uu___229_13365.dep_graph})
end))


let fail_or : 'a . env  ->  (FStar_Ident.lident  ->  'a FStar_Pervasives_Native.option)  ->  FStar_Ident.lident  ->  'a = (fun env lookup1 lid -> (

let uu____13399 = (lookup1 lid)
in (match (uu____13399) with
| FStar_Pervasives_Native.None -> begin
(

let opened_modules = (FStar_List.map (fun uu____13412 -> (match (uu____13412) with
| (lid1, uu____13418) -> begin
(FStar_Ident.text_of_lid lid1)
end)) env.modules)
in (

let msg = (

let uu____13420 = (FStar_Ident.text_of_lid lid)
in (FStar_Util.format1 "Identifier not found: [%s]" uu____13420))
in (

let msg1 = (match ((Prims.op_Equality (FStar_List.length lid.FStar_Ident.ns) (Prims.parse_int "0"))) with
| true -> begin
msg
end
| uu____13422 -> begin
(

let modul = (

let uu____13424 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in (

let uu____13425 = (FStar_Ident.range_of_lid lid)
in (FStar_Ident.set_lid_range uu____13424 uu____13425)))
in (

let uu____13426 = (resolve_module_name env modul true)
in (match (uu____13426) with
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

let uu____13435 = (FStar_Ident.range_of_lid lid)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_IdentifierNotFound), (msg1)) uu____13435)))))
end
| FStar_Pervasives_Native.Some (r) -> begin
r
end)))


let fail_or2 : 'a . (FStar_Ident.ident  ->  'a FStar_Pervasives_Native.option)  ->  FStar_Ident.ident  ->  'a = (fun lookup1 id1 -> (

let uu____13463 = (lookup1 id1)
in (match (uu____13463) with
| FStar_Pervasives_Native.None -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_IdentifierNotFound), ((Prims.strcat "Identifier not found [" (Prims.strcat id1.FStar_Ident.idText "]")))) id1.FStar_Ident.idRange)
end
| FStar_Pervasives_Native.Some (r) -> begin
r
end)))




