
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
| uu____22 -> begin
false
end))


let uu___is_Open_namespace : open_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Open_namespace -> begin
true
end
| uu____28 -> begin
false
end))


type open_module_or_namespace =
(FStar_Ident.lident * open_kind)

type record_or_dc =
{typename : FStar_Ident.lident; constrname : FStar_Ident.ident; parms : FStar_Syntax_Syntax.binders; fields : (FStar_Ident.ident * FStar_Syntax_Syntax.typ) Prims.list; is_private_or_abstract : Prims.bool; is_record : Prims.bool}


let __proj__Mkrecord_or_dc__item__typename : record_or_dc  ->  FStar_Ident.lident = (fun projectee -> (match (projectee) with
| {typename = __fname__typename; constrname = __fname__constrname; parms = __fname__parms; fields = __fname__fields; is_private_or_abstract = __fname__is_private_or_abstract; is_record = __fname__is_record} -> begin
__fname__typename
end))


let __proj__Mkrecord_or_dc__item__constrname : record_or_dc  ->  FStar_Ident.ident = (fun projectee -> (match (projectee) with
| {typename = __fname__typename; constrname = __fname__constrname; parms = __fname__parms; fields = __fname__fields; is_private_or_abstract = __fname__is_private_or_abstract; is_record = __fname__is_record} -> begin
__fname__constrname
end))


let __proj__Mkrecord_or_dc__item__parms : record_or_dc  ->  FStar_Syntax_Syntax.binders = (fun projectee -> (match (projectee) with
| {typename = __fname__typename; constrname = __fname__constrname; parms = __fname__parms; fields = __fname__fields; is_private_or_abstract = __fname__is_private_or_abstract; is_record = __fname__is_record} -> begin
__fname__parms
end))


let __proj__Mkrecord_or_dc__item__fields : record_or_dc  ->  (FStar_Ident.ident * FStar_Syntax_Syntax.typ) Prims.list = (fun projectee -> (match (projectee) with
| {typename = __fname__typename; constrname = __fname__constrname; parms = __fname__parms; fields = __fname__fields; is_private_or_abstract = __fname__is_private_or_abstract; is_record = __fname__is_record} -> begin
__fname__fields
end))


let __proj__Mkrecord_or_dc__item__is_private_or_abstract : record_or_dc  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {typename = __fname__typename; constrname = __fname__constrname; parms = __fname__parms; fields = __fname__fields; is_private_or_abstract = __fname__is_private_or_abstract; is_record = __fname__is_record} -> begin
__fname__is_private_or_abstract
end))


let __proj__Mkrecord_or_dc__item__is_record : record_or_dc  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {typename = __fname__typename; constrname = __fname__constrname; parms = __fname__parms; fields = __fname__fields; is_private_or_abstract = __fname__is_private_or_abstract; is_record = __fname__is_record} -> begin
__fname__is_record
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
| uu____219 -> begin
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
| uu____233 -> begin
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
| uu____247 -> begin
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
| uu____261 -> begin
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
| uu____275 -> begin
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
| uu____289 -> begin
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
| uu____304 -> begin
false
end))


let uu___is_Exported_id_field : exported_id_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Exported_id_field -> begin
true
end
| uu____310 -> begin
false
end))


type exported_id_set =
exported_id_kind  ->  string_set FStar_ST.ref

type env =
{curmodule : FStar_Ident.lident FStar_Pervasives_Native.option; curmonad : FStar_Ident.ident FStar_Pervasives_Native.option; modules : (FStar_Ident.lident * FStar_Syntax_Syntax.modul) Prims.list; scope_mods : scope_mod Prims.list; exported_ids : exported_id_set FStar_Util.smap; trans_exported_ids : exported_id_set FStar_Util.smap; includes : FStar_Ident.lident Prims.list FStar_ST.ref FStar_Util.smap; sigaccum : FStar_Syntax_Syntax.sigelts; sigmap : (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap; iface : Prims.bool; admitted_iface : Prims.bool; expect_typ : Prims.bool; docs : FStar_Parser_AST.fsdoc FStar_Util.smap; remaining_iface_decls : (FStar_Ident.lident * FStar_Parser_AST.decl Prims.list) Prims.list; syntax_only : Prims.bool; ds_hooks : dsenv_hooks} 
 and dsenv_hooks =
{ds_push_open_hook : env  ->  open_module_or_namespace  ->  unit; ds_push_include_hook : env  ->  FStar_Ident.lident  ->  unit; ds_push_module_abbrev_hook : env  ->  FStar_Ident.ident  ->  FStar_Ident.lident  ->  unit}


let __proj__Mkenv__item__curmodule : env  ->  FStar_Ident.lident FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {curmodule = __fname__curmodule; curmonad = __fname__curmonad; modules = __fname__modules; scope_mods = __fname__scope_mods; exported_ids = __fname__exported_ids; trans_exported_ids = __fname__trans_exported_ids; includes = __fname__includes; sigaccum = __fname__sigaccum; sigmap = __fname__sigmap; iface = __fname__iface; admitted_iface = __fname__admitted_iface; expect_typ = __fname__expect_typ; docs = __fname__docs; remaining_iface_decls = __fname__remaining_iface_decls; syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks} -> begin
__fname__curmodule
end))


let __proj__Mkenv__item__curmonad : env  ->  FStar_Ident.ident FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {curmodule = __fname__curmodule; curmonad = __fname__curmonad; modules = __fname__modules; scope_mods = __fname__scope_mods; exported_ids = __fname__exported_ids; trans_exported_ids = __fname__trans_exported_ids; includes = __fname__includes; sigaccum = __fname__sigaccum; sigmap = __fname__sigmap; iface = __fname__iface; admitted_iface = __fname__admitted_iface; expect_typ = __fname__expect_typ; docs = __fname__docs; remaining_iface_decls = __fname__remaining_iface_decls; syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks} -> begin
__fname__curmonad
end))


let __proj__Mkenv__item__modules : env  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.modul) Prims.list = (fun projectee -> (match (projectee) with
| {curmodule = __fname__curmodule; curmonad = __fname__curmonad; modules = __fname__modules; scope_mods = __fname__scope_mods; exported_ids = __fname__exported_ids; trans_exported_ids = __fname__trans_exported_ids; includes = __fname__includes; sigaccum = __fname__sigaccum; sigmap = __fname__sigmap; iface = __fname__iface; admitted_iface = __fname__admitted_iface; expect_typ = __fname__expect_typ; docs = __fname__docs; remaining_iface_decls = __fname__remaining_iface_decls; syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks} -> begin
__fname__modules
end))


let __proj__Mkenv__item__scope_mods : env  ->  scope_mod Prims.list = (fun projectee -> (match (projectee) with
| {curmodule = __fname__curmodule; curmonad = __fname__curmonad; modules = __fname__modules; scope_mods = __fname__scope_mods; exported_ids = __fname__exported_ids; trans_exported_ids = __fname__trans_exported_ids; includes = __fname__includes; sigaccum = __fname__sigaccum; sigmap = __fname__sigmap; iface = __fname__iface; admitted_iface = __fname__admitted_iface; expect_typ = __fname__expect_typ; docs = __fname__docs; remaining_iface_decls = __fname__remaining_iface_decls; syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks} -> begin
__fname__scope_mods
end))


let __proj__Mkenv__item__exported_ids : env  ->  exported_id_set FStar_Util.smap = (fun projectee -> (match (projectee) with
| {curmodule = __fname__curmodule; curmonad = __fname__curmonad; modules = __fname__modules; scope_mods = __fname__scope_mods; exported_ids = __fname__exported_ids; trans_exported_ids = __fname__trans_exported_ids; includes = __fname__includes; sigaccum = __fname__sigaccum; sigmap = __fname__sigmap; iface = __fname__iface; admitted_iface = __fname__admitted_iface; expect_typ = __fname__expect_typ; docs = __fname__docs; remaining_iface_decls = __fname__remaining_iface_decls; syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks} -> begin
__fname__exported_ids
end))


let __proj__Mkenv__item__trans_exported_ids : env  ->  exported_id_set FStar_Util.smap = (fun projectee -> (match (projectee) with
| {curmodule = __fname__curmodule; curmonad = __fname__curmonad; modules = __fname__modules; scope_mods = __fname__scope_mods; exported_ids = __fname__exported_ids; trans_exported_ids = __fname__trans_exported_ids; includes = __fname__includes; sigaccum = __fname__sigaccum; sigmap = __fname__sigmap; iface = __fname__iface; admitted_iface = __fname__admitted_iface; expect_typ = __fname__expect_typ; docs = __fname__docs; remaining_iface_decls = __fname__remaining_iface_decls; syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks} -> begin
__fname__trans_exported_ids
end))


let __proj__Mkenv__item__includes : env  ->  FStar_Ident.lident Prims.list FStar_ST.ref FStar_Util.smap = (fun projectee -> (match (projectee) with
| {curmodule = __fname__curmodule; curmonad = __fname__curmonad; modules = __fname__modules; scope_mods = __fname__scope_mods; exported_ids = __fname__exported_ids; trans_exported_ids = __fname__trans_exported_ids; includes = __fname__includes; sigaccum = __fname__sigaccum; sigmap = __fname__sigmap; iface = __fname__iface; admitted_iface = __fname__admitted_iface; expect_typ = __fname__expect_typ; docs = __fname__docs; remaining_iface_decls = __fname__remaining_iface_decls; syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks} -> begin
__fname__includes
end))


let __proj__Mkenv__item__sigaccum : env  ->  FStar_Syntax_Syntax.sigelts = (fun projectee -> (match (projectee) with
| {curmodule = __fname__curmodule; curmonad = __fname__curmonad; modules = __fname__modules; scope_mods = __fname__scope_mods; exported_ids = __fname__exported_ids; trans_exported_ids = __fname__trans_exported_ids; includes = __fname__includes; sigaccum = __fname__sigaccum; sigmap = __fname__sigmap; iface = __fname__iface; admitted_iface = __fname__admitted_iface; expect_typ = __fname__expect_typ; docs = __fname__docs; remaining_iface_decls = __fname__remaining_iface_decls; syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks} -> begin
__fname__sigaccum
end))


let __proj__Mkenv__item__sigmap : env  ->  (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap = (fun projectee -> (match (projectee) with
| {curmodule = __fname__curmodule; curmonad = __fname__curmonad; modules = __fname__modules; scope_mods = __fname__scope_mods; exported_ids = __fname__exported_ids; trans_exported_ids = __fname__trans_exported_ids; includes = __fname__includes; sigaccum = __fname__sigaccum; sigmap = __fname__sigmap; iface = __fname__iface; admitted_iface = __fname__admitted_iface; expect_typ = __fname__expect_typ; docs = __fname__docs; remaining_iface_decls = __fname__remaining_iface_decls; syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks} -> begin
__fname__sigmap
end))


let __proj__Mkenv__item__iface : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {curmodule = __fname__curmodule; curmonad = __fname__curmonad; modules = __fname__modules; scope_mods = __fname__scope_mods; exported_ids = __fname__exported_ids; trans_exported_ids = __fname__trans_exported_ids; includes = __fname__includes; sigaccum = __fname__sigaccum; sigmap = __fname__sigmap; iface = __fname__iface; admitted_iface = __fname__admitted_iface; expect_typ = __fname__expect_typ; docs = __fname__docs; remaining_iface_decls = __fname__remaining_iface_decls; syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks} -> begin
__fname__iface
end))


let __proj__Mkenv__item__admitted_iface : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {curmodule = __fname__curmodule; curmonad = __fname__curmonad; modules = __fname__modules; scope_mods = __fname__scope_mods; exported_ids = __fname__exported_ids; trans_exported_ids = __fname__trans_exported_ids; includes = __fname__includes; sigaccum = __fname__sigaccum; sigmap = __fname__sigmap; iface = __fname__iface; admitted_iface = __fname__admitted_iface; expect_typ = __fname__expect_typ; docs = __fname__docs; remaining_iface_decls = __fname__remaining_iface_decls; syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks} -> begin
__fname__admitted_iface
end))


let __proj__Mkenv__item__expect_typ : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {curmodule = __fname__curmodule; curmonad = __fname__curmonad; modules = __fname__modules; scope_mods = __fname__scope_mods; exported_ids = __fname__exported_ids; trans_exported_ids = __fname__trans_exported_ids; includes = __fname__includes; sigaccum = __fname__sigaccum; sigmap = __fname__sigmap; iface = __fname__iface; admitted_iface = __fname__admitted_iface; expect_typ = __fname__expect_typ; docs = __fname__docs; remaining_iface_decls = __fname__remaining_iface_decls; syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks} -> begin
__fname__expect_typ
end))


let __proj__Mkenv__item__docs : env  ->  FStar_Parser_AST.fsdoc FStar_Util.smap = (fun projectee -> (match (projectee) with
| {curmodule = __fname__curmodule; curmonad = __fname__curmonad; modules = __fname__modules; scope_mods = __fname__scope_mods; exported_ids = __fname__exported_ids; trans_exported_ids = __fname__trans_exported_ids; includes = __fname__includes; sigaccum = __fname__sigaccum; sigmap = __fname__sigmap; iface = __fname__iface; admitted_iface = __fname__admitted_iface; expect_typ = __fname__expect_typ; docs = __fname__docs; remaining_iface_decls = __fname__remaining_iface_decls; syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks} -> begin
__fname__docs
end))


let __proj__Mkenv__item__remaining_iface_decls : env  ->  (FStar_Ident.lident * FStar_Parser_AST.decl Prims.list) Prims.list = (fun projectee -> (match (projectee) with
| {curmodule = __fname__curmodule; curmonad = __fname__curmonad; modules = __fname__modules; scope_mods = __fname__scope_mods; exported_ids = __fname__exported_ids; trans_exported_ids = __fname__trans_exported_ids; includes = __fname__includes; sigaccum = __fname__sigaccum; sigmap = __fname__sigmap; iface = __fname__iface; admitted_iface = __fname__admitted_iface; expect_typ = __fname__expect_typ; docs = __fname__docs; remaining_iface_decls = __fname__remaining_iface_decls; syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks} -> begin
__fname__remaining_iface_decls
end))


let __proj__Mkenv__item__syntax_only : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {curmodule = __fname__curmodule; curmonad = __fname__curmonad; modules = __fname__modules; scope_mods = __fname__scope_mods; exported_ids = __fname__exported_ids; trans_exported_ids = __fname__trans_exported_ids; includes = __fname__includes; sigaccum = __fname__sigaccum; sigmap = __fname__sigmap; iface = __fname__iface; admitted_iface = __fname__admitted_iface; expect_typ = __fname__expect_typ; docs = __fname__docs; remaining_iface_decls = __fname__remaining_iface_decls; syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks} -> begin
__fname__syntax_only
end))


let __proj__Mkenv__item__ds_hooks : env  ->  dsenv_hooks = (fun projectee -> (match (projectee) with
| {curmodule = __fname__curmodule; curmonad = __fname__curmonad; modules = __fname__modules; scope_mods = __fname__scope_mods; exported_ids = __fname__exported_ids; trans_exported_ids = __fname__trans_exported_ids; includes = __fname__includes; sigaccum = __fname__sigaccum; sigmap = __fname__sigmap; iface = __fname__iface; admitted_iface = __fname__admitted_iface; expect_typ = __fname__expect_typ; docs = __fname__docs; remaining_iface_decls = __fname__remaining_iface_decls; syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks} -> begin
__fname__ds_hooks
end))


let __proj__Mkdsenv_hooks__item__ds_push_open_hook : dsenv_hooks  ->  env  ->  open_module_or_namespace  ->  unit = (fun projectee -> (match (projectee) with
| {ds_push_open_hook = __fname__ds_push_open_hook; ds_push_include_hook = __fname__ds_push_include_hook; ds_push_module_abbrev_hook = __fname__ds_push_module_abbrev_hook} -> begin
__fname__ds_push_open_hook
end))


let __proj__Mkdsenv_hooks__item__ds_push_include_hook : dsenv_hooks  ->  env  ->  FStar_Ident.lident  ->  unit = (fun projectee -> (match (projectee) with
| {ds_push_open_hook = __fname__ds_push_open_hook; ds_push_include_hook = __fname__ds_push_include_hook; ds_push_module_abbrev_hook = __fname__ds_push_module_abbrev_hook} -> begin
__fname__ds_push_include_hook
end))


let __proj__Mkdsenv_hooks__item__ds_push_module_abbrev_hook : dsenv_hooks  ->  env  ->  FStar_Ident.ident  ->  FStar_Ident.lident  ->  unit = (fun projectee -> (match (projectee) with
| {ds_push_open_hook = __fname__ds_push_open_hook; ds_push_include_hook = __fname__ds_push_include_hook; ds_push_module_abbrev_hook = __fname__ds_push_module_abbrev_hook} -> begin
__fname__ds_push_module_abbrev_hook
end))


type 'a withenv =
env  ->  ('a * env)


let default_ds_hooks : dsenv_hooks = {ds_push_open_hook = (fun uu____1725 uu____1726 -> ()); ds_push_include_hook = (fun uu____1729 uu____1730 -> ()); ds_push_module_abbrev_hook = (fun uu____1734 uu____1735 uu____1736 -> ())}

type foundname =
| Term_name of (FStar_Syntax_Syntax.typ * Prims.bool * FStar_Syntax_Syntax.attribute Prims.list)
| Eff_name of (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident)


let uu___is_Term_name : foundname  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Term_name (_0) -> begin
true
end
| uu____1773 -> begin
false
end))


let __proj__Term_name__item___0 : foundname  ->  (FStar_Syntax_Syntax.typ * Prims.bool * FStar_Syntax_Syntax.attribute Prims.list) = (fun projectee -> (match (projectee) with
| Term_name (_0) -> begin
_0
end))


let uu___is_Eff_name : foundname  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Eff_name (_0) -> begin
true
end
| uu____1815 -> begin
false
end))


let __proj__Eff_name__item___0 : foundname  ->  (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident) = (fun projectee -> (match (projectee) with
| Eff_name (_0) -> begin
_0
end))


let set_iface : env  ->  Prims.bool  ->  env = (fun env b -> (

let uu___114_1845 = env
in {curmodule = uu___114_1845.curmodule; curmonad = uu___114_1845.curmonad; modules = uu___114_1845.modules; scope_mods = uu___114_1845.scope_mods; exported_ids = uu___114_1845.exported_ids; trans_exported_ids = uu___114_1845.trans_exported_ids; includes = uu___114_1845.includes; sigaccum = uu___114_1845.sigaccum; sigmap = uu___114_1845.sigmap; iface = b; admitted_iface = uu___114_1845.admitted_iface; expect_typ = uu___114_1845.expect_typ; docs = uu___114_1845.docs; remaining_iface_decls = uu___114_1845.remaining_iface_decls; syntax_only = uu___114_1845.syntax_only; ds_hooks = uu___114_1845.ds_hooks}))


let iface : env  ->  Prims.bool = (fun e -> e.iface)


let set_admitted_iface : env  ->  Prims.bool  ->  env = (fun e b -> (

let uu___115_1861 = e
in {curmodule = uu___115_1861.curmodule; curmonad = uu___115_1861.curmonad; modules = uu___115_1861.modules; scope_mods = uu___115_1861.scope_mods; exported_ids = uu___115_1861.exported_ids; trans_exported_ids = uu___115_1861.trans_exported_ids; includes = uu___115_1861.includes; sigaccum = uu___115_1861.sigaccum; sigmap = uu___115_1861.sigmap; iface = uu___115_1861.iface; admitted_iface = b; expect_typ = uu___115_1861.expect_typ; docs = uu___115_1861.docs; remaining_iface_decls = uu___115_1861.remaining_iface_decls; syntax_only = uu___115_1861.syntax_only; ds_hooks = uu___115_1861.ds_hooks}))


let admitted_iface : env  ->  Prims.bool = (fun e -> e.admitted_iface)


let set_expect_typ : env  ->  Prims.bool  ->  env = (fun e b -> (

let uu___116_1877 = e
in {curmodule = uu___116_1877.curmodule; curmonad = uu___116_1877.curmonad; modules = uu___116_1877.modules; scope_mods = uu___116_1877.scope_mods; exported_ids = uu___116_1877.exported_ids; trans_exported_ids = uu___116_1877.trans_exported_ids; includes = uu___116_1877.includes; sigaccum = uu___116_1877.sigaccum; sigmap = uu___116_1877.sigmap; iface = uu___116_1877.iface; admitted_iface = uu___116_1877.admitted_iface; expect_typ = b; docs = uu___116_1877.docs; remaining_iface_decls = uu___116_1877.remaining_iface_decls; syntax_only = uu___116_1877.syntax_only; ds_hooks = uu___116_1877.ds_hooks}))


let expect_typ : env  ->  Prims.bool = (fun e -> e.expect_typ)


let all_exported_id_kinds : exported_id_kind Prims.list = (Exported_id_field)::(Exported_id_term_type)::[]


let transitive_exported_ids : env  ->  FStar_Ident.lident  ->  Prims.string Prims.list = (fun env lid -> (

let module_name = (FStar_Ident.string_of_lid lid)
in (

let uu____1898 = (FStar_Util.smap_try_find env.trans_exported_ids module_name)
in (match (uu____1898) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (exported_id_set) -> begin
(

let uu____1909 = (

let uu____1910 = (exported_id_set Exported_id_term_type)
in (FStar_ST.op_Bang uu____1910))
in (FStar_All.pipe_right uu____1909 FStar_Util.set_elements))
end))))


let open_modules : env  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.modul) Prims.list = (fun e -> e.modules)


let open_modules_and_namespaces : env  ->  FStar_Ident.lident Prims.list = (fun env -> (FStar_List.filter_map (fun uu___82_2052 -> (match (uu___82_2052) with
| Open_module_or_namespace (lid, _info) -> begin
FStar_Pervasives_Native.Some (lid)
end
| uu____2057 -> begin
FStar_Pervasives_Native.None
end)) env.scope_mods))


let set_current_module : env  ->  FStar_Ident.lident  ->  env = (fun e l -> (

let uu___117_2068 = e
in {curmodule = FStar_Pervasives_Native.Some (l); curmonad = uu___117_2068.curmonad; modules = uu___117_2068.modules; scope_mods = uu___117_2068.scope_mods; exported_ids = uu___117_2068.exported_ids; trans_exported_ids = uu___117_2068.trans_exported_ids; includes = uu___117_2068.includes; sigaccum = uu___117_2068.sigaccum; sigmap = uu___117_2068.sigmap; iface = uu___117_2068.iface; admitted_iface = uu___117_2068.admitted_iface; expect_typ = uu___117_2068.expect_typ; docs = uu___117_2068.docs; remaining_iface_decls = uu___117_2068.remaining_iface_decls; syntax_only = uu___117_2068.syntax_only; ds_hooks = uu___117_2068.ds_hooks}))


let current_module : env  ->  FStar_Ident.lident = (fun env -> (match (env.curmodule) with
| FStar_Pervasives_Native.None -> begin
(failwith "Unset current module")
end
| FStar_Pervasives_Native.Some (m) -> begin
m
end))


let iface_decls : env  ->  FStar_Ident.lident  ->  FStar_Parser_AST.decl Prims.list FStar_Pervasives_Native.option = (fun env l -> (

let uu____2089 = (FStar_All.pipe_right env.remaining_iface_decls (FStar_List.tryFind (fun uu____2123 -> (match (uu____2123) with
| (m, uu____2131) -> begin
(FStar_Ident.lid_equals l m)
end))))
in (match (uu____2089) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (uu____2148, decls) -> begin
FStar_Pervasives_Native.Some (decls)
end)))


let set_iface_decls : env  ->  FStar_Ident.lident  ->  FStar_Parser_AST.decl Prims.list  ->  env = (fun env l ds -> (

let uu____2181 = (FStar_List.partition (fun uu____2211 -> (match (uu____2211) with
| (m, uu____2219) -> begin
(FStar_Ident.lid_equals l m)
end)) env.remaining_iface_decls)
in (match (uu____2181) with
| (uu____2224, rest) -> begin
(

let uu___118_2258 = env
in {curmodule = uu___118_2258.curmodule; curmonad = uu___118_2258.curmonad; modules = uu___118_2258.modules; scope_mods = uu___118_2258.scope_mods; exported_ids = uu___118_2258.exported_ids; trans_exported_ids = uu___118_2258.trans_exported_ids; includes = uu___118_2258.includes; sigaccum = uu___118_2258.sigaccum; sigmap = uu___118_2258.sigmap; iface = uu___118_2258.iface; admitted_iface = uu___118_2258.admitted_iface; expect_typ = uu___118_2258.expect_typ; docs = uu___118_2258.docs; remaining_iface_decls = (((l), (ds)))::rest; syntax_only = uu___118_2258.syntax_only; ds_hooks = uu___118_2258.ds_hooks})
end)))


let qual : FStar_Ident.lident  ->  FStar_Ident.ident  ->  FStar_Ident.lident = FStar_Syntax_Util.qual_id


let qualify : env  ->  FStar_Ident.ident  ->  FStar_Ident.lident = (fun env id1 -> (match (env.curmonad) with
| FStar_Pervasives_Native.None -> begin
(

let uu____2285 = (current_module env)
in (qual uu____2285 id1))
end
| FStar_Pervasives_Native.Some (monad) -> begin
(

let uu____2287 = (

let uu____2288 = (current_module env)
in (qual uu____2288 monad))
in (FStar_Syntax_Util.mk_field_projector_name_from_ident uu____2287 id1))
end))


let syntax_only : env  ->  Prims.bool = (fun env -> env.syntax_only)


let set_syntax_only : env  ->  Prims.bool  ->  env = (fun env b -> (

let uu___119_2304 = env
in {curmodule = uu___119_2304.curmodule; curmonad = uu___119_2304.curmonad; modules = uu___119_2304.modules; scope_mods = uu___119_2304.scope_mods; exported_ids = uu___119_2304.exported_ids; trans_exported_ids = uu___119_2304.trans_exported_ids; includes = uu___119_2304.includes; sigaccum = uu___119_2304.sigaccum; sigmap = uu___119_2304.sigmap; iface = uu___119_2304.iface; admitted_iface = uu___119_2304.admitted_iface; expect_typ = uu___119_2304.expect_typ; docs = uu___119_2304.docs; remaining_iface_decls = uu___119_2304.remaining_iface_decls; syntax_only = b; ds_hooks = uu___119_2304.ds_hooks}))


let ds_hooks : env  ->  dsenv_hooks = (fun env -> env.ds_hooks)


let set_ds_hooks : env  ->  dsenv_hooks  ->  env = (fun env hooks -> (

let uu___120_2320 = env
in {curmodule = uu___120_2320.curmodule; curmonad = uu___120_2320.curmonad; modules = uu___120_2320.modules; scope_mods = uu___120_2320.scope_mods; exported_ids = uu___120_2320.exported_ids; trans_exported_ids = uu___120_2320.trans_exported_ids; includes = uu___120_2320.includes; sigaccum = uu___120_2320.sigaccum; sigmap = uu___120_2320.sigmap; iface = uu___120_2320.iface; admitted_iface = uu___120_2320.admitted_iface; expect_typ = uu___120_2320.expect_typ; docs = uu___120_2320.docs; remaining_iface_decls = uu___120_2320.remaining_iface_decls; syntax_only = uu___120_2320.syntax_only; ds_hooks = hooks}))


let new_sigmap : 'Auu____2325 . unit  ->  'Auu____2325 FStar_Util.smap = (fun uu____2332 -> (FStar_Util.smap_create (Prims.parse_int "100")))


let empty_env : unit  ->  env = (fun uu____2337 -> (

let uu____2338 = (new_sigmap ())
in (

let uu____2343 = (new_sigmap ())
in (

let uu____2348 = (new_sigmap ())
in (

let uu____2359 = (new_sigmap ())
in (

let uu____2370 = (new_sigmap ())
in {curmodule = FStar_Pervasives_Native.None; curmonad = FStar_Pervasives_Native.None; modules = []; scope_mods = []; exported_ids = uu____2338; trans_exported_ids = uu____2343; includes = uu____2348; sigaccum = []; sigmap = uu____2359; iface = false; admitted_iface = false; expect_typ = false; docs = uu____2370; remaining_iface_decls = []; syntax_only = false; ds_hooks = default_ds_hooks}))))))


let sigmap : env  ->  (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap = (fun env -> env.sigmap)


let has_all_in_scope : env  ->  Prims.bool = (fun env -> (FStar_List.existsb (fun uu____2406 -> (match (uu____2406) with
| (m, uu____2412) -> begin
(FStar_Ident.lid_equals m FStar_Parser_Const.all_lid)
end)) env.modules))


let set_bv_range : FStar_Syntax_Syntax.bv  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.bv = (fun bv r -> (

let id1 = (

let uu___121_2424 = bv.FStar_Syntax_Syntax.ppname
in {FStar_Ident.idText = uu___121_2424.FStar_Ident.idText; FStar_Ident.idRange = r})
in (

let uu___122_2425 = bv
in {FStar_Syntax_Syntax.ppname = id1; FStar_Syntax_Syntax.index = uu___122_2425.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu___122_2425.FStar_Syntax_Syntax.sort})))


let bv_to_name : FStar_Syntax_Syntax.bv  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.term = (fun bv r -> (FStar_Syntax_Syntax.bv_to_name (set_bv_range bv r)))


let unmangleMap : (Prims.string * Prims.string * FStar_Syntax_Syntax.delta_depth * FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option) Prims.list = ((("op_ColonColon"), ("Cons"), (FStar_Syntax_Syntax.Delta_constant), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor))))::((("not"), ("op_Negation"), (FStar_Syntax_Syntax.Delta_equational), (FStar_Pervasives_Native.None)))::[]


let unmangleOpName : FStar_Ident.ident  ->  (FStar_Syntax_Syntax.term * Prims.bool) FStar_Pervasives_Native.option = (fun id1 -> (

let t = (FStar_Util.find_map unmangleMap (fun uu____2518 -> (match (uu____2518) with
| (x, y, dd, dq) -> begin
(match ((Prims.op_Equality id1.FStar_Ident.idText x)) with
| true -> begin
(

let uu____2541 = (

let uu____2542 = (FStar_Ident.lid_of_path (("Prims")::(y)::[]) id1.FStar_Ident.idRange)
in (FStar_Syntax_Syntax.fvar uu____2542 dd dq))
in FStar_Pervasives_Native.Some (uu____2541))
end
| uu____2543 -> begin
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


let uu___is_Cont_ok : 'a . 'a cont_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Cont_ok (_0) -> begin
true
end
| uu____2589 -> begin
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
| uu____2622 -> begin
false
end))


let uu___is_Cont_ignore : 'a . 'a cont_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Cont_ignore -> begin
true
end
| uu____2639 -> begin
false
end))


let option_of_cont : 'a . (unit  ->  'a FStar_Pervasives_Native.option)  ->  'a cont_t  ->  'a FStar_Pervasives_Native.option = (fun k_ignore uu___83_2667 -> (match (uu___83_2667) with
| Cont_ok (a) -> begin
FStar_Pervasives_Native.Some (a)
end
| Cont_fail -> begin
FStar_Pervasives_Native.None
end
| Cont_ignore -> begin
(k_ignore ())
end))


let find_in_record : 'Auu____2685 . FStar_Ident.ident Prims.list  ->  FStar_Ident.ident  ->  record_or_dc  ->  (record_or_dc  ->  'Auu____2685 cont_t)  ->  'Auu____2685 cont_t = (fun ns id1 record cont -> (

let typename' = (FStar_Ident.lid_of_ids (FStar_List.append ns ((record.typename.FStar_Ident.ident)::[])))
in (

let uu____2722 = (FStar_Ident.lid_equals typename' record.typename)
in (match (uu____2722) with
| true -> begin
(

let fname = (FStar_Ident.lid_of_ids (FStar_List.append record.typename.FStar_Ident.ns ((id1)::[])))
in (

let find1 = (FStar_Util.find_map record.fields (fun uu____2736 -> (match (uu____2736) with
| (f, uu____2744) -> begin
(match ((Prims.op_Equality id1.FStar_Ident.idText f.FStar_Ident.idText)) with
| true -> begin
FStar_Pervasives_Native.Some (record)
end
| uu____2747 -> begin
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
| uu____2751 -> begin
Cont_ignore
end))))


let get_exported_id_set : env  ->  Prims.string  ->  (exported_id_kind  ->  string_set FStar_ST.ref) FStar_Pervasives_Native.option = (fun e mname -> (FStar_Util.smap_try_find e.exported_ids mname))


let get_trans_exported_id_set : env  ->  Prims.string  ->  (exported_id_kind  ->  string_set FStar_ST.ref) FStar_Pervasives_Native.option = (fun e mname -> (FStar_Util.smap_try_find e.trans_exported_ids mname))


let string_of_exported_id_kind : exported_id_kind  ->  Prims.string = (fun uu___84_2806 -> (match (uu___84_2806) with
| Exported_id_field -> begin
"field"
end
| Exported_id_term_type -> begin
"term/type"
end))


let find_in_module_with_includes : 'a . exported_id_kind  ->  (FStar_Ident.lident  ->  'a cont_t)  ->  'a cont_t  ->  env  ->  FStar_Ident.lident  ->  FStar_Ident.ident  ->  'a cont_t = (fun eikind find_in_module find_in_module_default env ns id1 -> (

let idstr = id1.FStar_Ident.idText
in (

let rec aux = (fun uu___85_2877 -> (match (uu___85_2877) with
| [] -> begin
find_in_module_default
end
| (modul)::q -> begin
(

let mname = modul.FStar_Ident.str
in (

let not_shadowed = (

let uu____2888 = (get_exported_id_set env mname)
in (match (uu____2888) with
| FStar_Pervasives_Native.None -> begin
true
end
| FStar_Pervasives_Native.Some (mex) -> begin
(

let mexports = (

let uu____2913 = (mex eikind)
in (FStar_ST.op_Bang uu____2913))
in (FStar_Util.set_mem idstr mexports))
end))
in (

let mincludes = (

let uu____3035 = (FStar_Util.smap_try_find env.includes mname)
in (match (uu____3035) with
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

let uu____3115 = (qual modul id1)
in (find_in_module uu____3115))
end
| uu____3116 -> begin
Cont_ignore
end)
in (match (look_into) with
| Cont_ignore -> begin
(aux (FStar_List.append mincludes q))
end
| uu____3119 -> begin
look_into
end)))))
end))
in (aux ((ns)::[])))))


let is_exported_id_field : exported_id_kind  ->  Prims.bool = (fun uu___86_3126 -> (match (uu___86_3126) with
| Exported_id_field -> begin
true
end
| uu____3127 -> begin
false
end))


let try_lookup_id'' : 'a . env  ->  FStar_Ident.ident  ->  exported_id_kind  ->  (local_binding  ->  'a cont_t)  ->  (rec_binding  ->  'a cont_t)  ->  (record_or_dc  ->  'a cont_t)  ->  (FStar_Ident.lident  ->  'a cont_t)  ->  ('a cont_t  ->  FStar_Ident.ident  ->  'a cont_t)  ->  'a FStar_Pervasives_Native.option = (fun env id1 eikind k_local_binding k_rec_binding k_record find_in_module lookup_default_id -> (

let check_local_binding_id = (fun uu___87_3248 -> (match (uu___87_3248) with
| (id', uu____3250, uu____3251) -> begin
(Prims.op_Equality id'.FStar_Ident.idText id1.FStar_Ident.idText)
end))
in (

let check_rec_binding_id = (fun uu___88_3257 -> (match (uu___88_3257) with
| (id', uu____3259, uu____3260) -> begin
(Prims.op_Equality id'.FStar_Ident.idText id1.FStar_Ident.idText)
end))
in (

let curmod_ns = (

let uu____3264 = (current_module env)
in (FStar_Ident.ids_of_lid uu____3264))
in (

let proc = (fun uu___89_3272 -> (match (uu___89_3272) with
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

let uu____3280 = (FStar_Ident.lid_of_ids curmod_ns)
in (find_in_module_with_includes Exported_id_field (fun lid -> (

let id2 = lid.FStar_Ident.ident
in (find_in_record lid.FStar_Ident.ns id2 r k_record))) Cont_ignore env uu____3280 id1))
end
| uu____3285 -> begin
Cont_ignore
end))
in (

let rec aux = (fun uu___90_3295 -> (match (uu___90_3295) with
| (a)::q -> begin
(

let uu____3304 = (proc a)
in (option_of_cont (fun uu____3308 -> (aux q)) uu____3304))
end
| [] -> begin
(

let uu____3309 = (lookup_default_id Cont_fail id1)
in (option_of_cont (fun uu____3313 -> FStar_Pervasives_Native.None) uu____3309))
end))
in (aux env.scope_mods)))))))


let found_local_binding : 'Auu____3322 'Auu____3323 . FStar_Range.range  ->  ('Auu____3322 * FStar_Syntax_Syntax.bv * 'Auu____3323)  ->  (FStar_Syntax_Syntax.term * 'Auu____3323) = (fun r uu____3343 -> (match (uu____3343) with
| (id', x, mut) -> begin
(

let uu____3353 = (bv_to_name x r)
in ((uu____3353), (mut)))
end))


let find_in_module : 'Auu____3364 . env  ->  FStar_Ident.lident  ->  (FStar_Ident.lident  ->  (FStar_Syntax_Syntax.sigelt * Prims.bool)  ->  'Auu____3364)  ->  'Auu____3364  ->  'Auu____3364 = (fun env lid k_global_def k_not_found -> (

let uu____3403 = (FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str)
in (match (uu____3403) with
| FStar_Pervasives_Native.Some (sb) -> begin
(k_global_def lid sb)
end
| FStar_Pervasives_Native.None -> begin
k_not_found
end)))


let try_lookup_id : env  ->  FStar_Ident.ident  ->  (FStar_Syntax_Syntax.term * Prims.bool) FStar_Pervasives_Native.option = (fun env id1 -> (

let uu____3443 = (unmangleOpName id1)
in (match (uu____3443) with
| FStar_Pervasives_Native.Some (f) -> begin
FStar_Pervasives_Native.Some (f)
end
| uu____3469 -> begin
(try_lookup_id'' env id1 Exported_id_term_type (fun r -> (

let uu____3483 = (found_local_binding id1.FStar_Ident.idRange r)
in Cont_ok (uu____3483))) (fun uu____3493 -> Cont_fail) (fun uu____3499 -> Cont_ignore) (fun i -> (find_in_module env i (fun uu____3514 uu____3515 -> Cont_fail) Cont_ignore)) (fun uu____3530 uu____3531 -> Cont_fail))
end)))


let lookup_default_id : 'a . env  ->  FStar_Ident.ident  ->  (FStar_Ident.lident  ->  (FStar_Syntax_Syntax.sigelt * Prims.bool)  ->  'a cont_t)  ->  'a cont_t  ->  'a cont_t = (fun env id1 k_global_def k_not_found -> (

let find_in_monad = (match (env.curmonad) with
| FStar_Pervasives_Native.Some (uu____3610) -> begin
(

let lid = (qualify env id1)
in (

let uu____3612 = (FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str)
in (match (uu____3612) with
| FStar_Pervasives_Native.Some (r) -> begin
(

let uu____3636 = (k_global_def lid r)
in FStar_Pervasives_Native.Some (uu____3636))
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

let uu____3659 = (current_module env)
in (qual uu____3659 id1))
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

let rec aux = (fun uu___91_3722 -> (match (uu___91_3722) with
| [] -> begin
(

let uu____3727 = (module_is_defined env lid)
in (match (uu____3727) with
| true -> begin
FStar_Pervasives_Native.Some (lid)
end
| uu____3730 -> begin
FStar_Pervasives_Native.None
end))
end
| (Open_module_or_namespace (ns, Open_namespace))::q when honor_ns -> begin
(

let new_lid = (

let uu____3736 = (

let uu____3737 = (FStar_Ident.path_of_lid ns)
in (

let uu____3740 = (FStar_Ident.path_of_lid lid)
in (FStar_List.append uu____3737 uu____3740)))
in (

let uu____3743 = (FStar_Ident.range_of_lid lid)
in (FStar_Ident.lid_of_path uu____3736 uu____3743)))
in (

let uu____3744 = (module_is_defined env new_lid)
in (match (uu____3744) with
| true -> begin
FStar_Pervasives_Native.Some (new_lid)
end
| uu____3747 -> begin
(aux q)
end)))
end
| (Module_abbrev (name, modul))::uu____3750 when ((Prims.op_Equality nslen (Prims.parse_int "0")) && (Prims.op_Equality name.FStar_Ident.idText lid.FStar_Ident.ident.FStar_Ident.idText)) -> begin
FStar_Pervasives_Native.Some (modul)
end
| (uu____3757)::q -> begin
(aux q)
end))
in (aux env.scope_mods))))


let fail_if_curmodule : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  unit = (fun env ns_original ns_resolved -> (

let uu____3776 = (

let uu____3777 = (current_module env)
in (FStar_Ident.lid_equals ns_resolved uu____3777))
in (match (uu____3776) with
| true -> begin
(

let uu____3778 = (FStar_Ident.lid_equals ns_resolved FStar_Parser_Const.prims_lid)
in (match (uu____3778) with
| true -> begin
()
end
| uu____3779 -> begin
(

let uu____3780 = (

let uu____3785 = (FStar_Util.format1 "Reference %s to current module is forbidden (see GitHub issue #451)" ns_original.FStar_Ident.str)
in ((FStar_Errors.Fatal_ForbiddenReferenceToCurrentModule), (uu____3785)))
in (

let uu____3786 = (FStar_Ident.range_of_lid ns_original)
in (FStar_Errors.raise_error uu____3780 uu____3786)))
end))
end
| uu____3787 -> begin
()
end)))


let fail_if_qualified_by_curmodule : env  ->  FStar_Ident.lident  ->  unit = (fun env lid -> (match (lid.FStar_Ident.ns) with
| [] -> begin
()
end
| uu____3798 -> begin
(

let modul_orig = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in (

let uu____3802 = (resolve_module_name env modul_orig true)
in (match (uu____3802) with
| FStar_Pervasives_Native.Some (modul_res) -> begin
(fail_if_curmodule env modul_orig modul_res)
end
| uu____3806 -> begin
()
end)))
end))


let is_open : env  ->  FStar_Ident.lident  ->  open_kind  ->  Prims.bool = (fun env lid open_kind -> (FStar_List.existsb (fun uu___92_3827 -> (match (uu___92_3827) with
| Open_module_or_namespace (ns, k) -> begin
((Prims.op_Equality k open_kind) && (FStar_Ident.lid_equals lid ns))
end
| uu____3830 -> begin
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
| uu____3926 -> begin
(match (revns) with
| [] -> begin
FStar_Pervasives_Native.None
end
| (ns_last_id)::rev_ns_prefix -> begin
(

let uu____3949 = (aux rev_ns_prefix ns_last_id)
in (FStar_All.pipe_right uu____3949 (FStar_Util.map_option (fun uu____3999 -> (match (uu____3999) with
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

let uu____4069 = (aux ns_rev_prefix ns_last_id)
in (match (uu____4069) with
| FStar_Pervasives_Native.None -> begin
(([]), (ids1))
end
| FStar_Pervasives_Native.Some (stripped_ids, rev_kept_ids) -> begin
((stripped_ids), ((FStar_List.rev rev_kept_ids)))
end))
end))
in (match (is_full_path) with
| true -> begin
(

let uu____4130 = (

let uu____4133 = (FStar_Ident.lid_of_ids ids)
in (resolve_module_name env uu____4133 true))
in (match (uu____4130) with
| FStar_Pervasives_Native.Some (m) when (module_is_open env m) -> begin
((ids), ([]))
end
| uu____4147 -> begin
(do_shorten env ids)
end))
end
| uu____4150 -> begin
(do_shorten env ids)
end))))


let resolve_in_open_namespaces'' : 'a . env  ->  FStar_Ident.lident  ->  exported_id_kind  ->  (local_binding  ->  'a cont_t)  ->  (rec_binding  ->  'a cont_t)  ->  (record_or_dc  ->  'a cont_t)  ->  (FStar_Ident.lident  ->  'a cont_t)  ->  ('a cont_t  ->  FStar_Ident.ident  ->  'a cont_t)  ->  'a FStar_Pervasives_Native.option = (fun env lid eikind k_local_binding k_rec_binding k_record f_module l_default -> (match (lid.FStar_Ident.ns) with
| (uu____4266)::uu____4267 -> begin
(

let uu____4270 = (

let uu____4273 = (

let uu____4274 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in (

let uu____4275 = (FStar_Ident.range_of_lid lid)
in (FStar_Ident.set_lid_range uu____4274 uu____4275)))
in (resolve_module_name env uu____4273 true))
in (match (uu____4270) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (modul) -> begin
(

let uu____4279 = (find_in_module_with_includes eikind f_module Cont_fail env modul lid.FStar_Ident.ident)
in (option_of_cont (fun uu____4283 -> FStar_Pervasives_Native.None) uu____4279))
end))
end
| [] -> begin
(try_lookup_id'' env lid.FStar_Ident.ident eikind k_local_binding k_rec_binding k_record f_module l_default)
end))


let cont_of_option : 'a . 'a cont_t  ->  'a FStar_Pervasives_Native.option  ->  'a cont_t = (fun k_none uu___93_4306 -> (match (uu___93_4306) with
| FStar_Pervasives_Native.Some (v1) -> begin
Cont_ok (v1)
end
| FStar_Pervasives_Native.None -> begin
k_none
end))


let resolve_in_open_namespaces' : 'a . env  ->  FStar_Ident.lident  ->  (local_binding  ->  'a FStar_Pervasives_Native.option)  ->  (rec_binding  ->  'a FStar_Pervasives_Native.option)  ->  (FStar_Ident.lident  ->  (FStar_Syntax_Syntax.sigelt * Prims.bool)  ->  'a FStar_Pervasives_Native.option)  ->  'a FStar_Pervasives_Native.option = (fun env lid k_local_binding k_rec_binding k_global_def -> (

let k_global_def' = (fun k lid1 def -> (

let uu____4422 = (k_global_def lid1 def)
in (cont_of_option k uu____4422)))
in (

let f_module = (fun lid' -> (

let k = Cont_ignore
in (find_in_module env lid' (k_global_def' k) k)))
in (

let l_default = (fun k i -> (lookup_default_id env i (k_global_def' k) k))
in (resolve_in_open_namespaces'' env lid Exported_id_term_type (fun l -> (

let uu____4458 = (k_local_binding l)
in (cont_of_option Cont_fail uu____4458))) (fun r -> (

let uu____4464 = (k_rec_binding r)
in (cont_of_option Cont_fail uu____4464))) (fun uu____4468 -> Cont_ignore) f_module l_default)))))


let fv_qual_of_se : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option = (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (uu____4478, uu____4479, uu____4480, l, uu____4482, uu____4483) -> begin
(

let qopt = (FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals (fun uu___94_4494 -> (match (uu___94_4494) with
| FStar_Syntax_Syntax.RecordConstructor (uu____4497, fs) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (((l), (fs))))
end
| uu____4509 -> begin
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
| FStar_Syntax_Syntax.Sig_declare_typ (uu____4515, uu____4516, uu____4517) -> begin
FStar_Pervasives_Native.None
end
| uu____4518 -> begin
FStar_Pervasives_Native.None
end))


let lb_fv : FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.fv = (fun lbs lid -> (

let uu____4533 = (FStar_Util.find_map lbs (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let uu____4541 = (FStar_Syntax_Syntax.fv_eq_lid fv lid)
in (match (uu____4541) with
| true -> begin
FStar_Pervasives_Native.Some (fv)
end
| uu____4544 -> begin
FStar_Pervasives_Native.None
end)))))
in (FStar_All.pipe_right uu____4533 FStar_Util.must)))


let ns_of_lid_equals : FStar_Ident.lident  ->  FStar_Ident.lident  ->  Prims.bool = (fun lid ns -> ((

let uu____4559 = (

let uu____4560 = (FStar_Ident.ids_of_lid ns)
in (FStar_List.length uu____4560))
in (Prims.op_Equality (FStar_List.length lid.FStar_Ident.ns) uu____4559)) && (

let uu____4568 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in (FStar_Ident.lid_equals uu____4568 ns))))


let try_lookup_name : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  foundname FStar_Pervasives_Native.option = (fun any_val exclude_interf env lid -> (

let occurrence_range = (FStar_Ident.range_of_lid lid)
in (

let k_global_def = (fun source_lid uu___99_4610 -> (match (uu___99_4610) with
| (uu____4617, true) when exclude_interf -> begin
FStar_Pervasives_Native.None
end
| (se, uu____4619) -> begin
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____4622) -> begin
(

let uu____4639 = (

let uu____4640 = (

let uu____4649 = (FStar_Syntax_Syntax.fvar source_lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in ((uu____4649), (false), (se.FStar_Syntax_Syntax.sigattrs)))
in Term_name (uu____4640))
in FStar_Pervasives_Native.Some (uu____4639))
end
| FStar_Syntax_Syntax.Sig_datacon (uu____4652) -> begin
(

let uu____4667 = (

let uu____4668 = (

let uu____4677 = (

let uu____4678 = (fv_qual_of_se se)
in (FStar_Syntax_Syntax.fvar source_lid FStar_Syntax_Syntax.Delta_constant uu____4678))
in ((uu____4677), (false), (se.FStar_Syntax_Syntax.sigattrs)))
in Term_name (uu____4668))
in FStar_Pervasives_Native.Some (uu____4667))
end
| FStar_Syntax_Syntax.Sig_let ((uu____4683, lbs), uu____4685) -> begin
(

let fv = (lb_fv lbs source_lid)
in (

let uu____4695 = (

let uu____4696 = (

let uu____4705 = (FStar_Syntax_Syntax.fvar source_lid fv.FStar_Syntax_Syntax.fv_delta fv.FStar_Syntax_Syntax.fv_qual)
in ((uu____4705), (false), (se.FStar_Syntax_Syntax.sigattrs)))
in Term_name (uu____4696))
in FStar_Pervasives_Native.Some (uu____4695)))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid1, uu____4709, uu____4710) -> begin
(

let quals = se.FStar_Syntax_Syntax.sigquals
in (

let uu____4714 = (any_val || (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___95_4718 -> (match (uu___95_4718) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| uu____4719 -> begin
false
end)))))
in (match (uu____4714) with
| true -> begin
(

let lid2 = (

let uu____4723 = (FStar_Ident.range_of_lid source_lid)
in (FStar_Ident.set_lid_range lid1 uu____4723))
in (

let dd = (

let uu____4725 = ((FStar_Syntax_Util.is_primop_lid lid2) || (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___96_4730 -> (match (uu___96_4730) with
| FStar_Syntax_Syntax.Projector (uu____4731) -> begin
true
end
| FStar_Syntax_Syntax.Discriminator (uu____4736) -> begin
true
end
| uu____4737 -> begin
false
end)))))
in (match (uu____4725) with
| true -> begin
FStar_Syntax_Syntax.Delta_equational
end
| uu____4738 -> begin
FStar_Syntax_Syntax.Delta_constant
end))
in (

let dd1 = (

let uu____4740 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___97_4744 -> (match (uu___97_4744) with
| FStar_Syntax_Syntax.Abstract -> begin
true
end
| uu____4745 -> begin
false
end))))
in (match (uu____4740) with
| true -> begin
FStar_Syntax_Syntax.Delta_abstract (dd)
end
| uu____4746 -> begin
dd
end))
in (

let uu____4747 = (FStar_Util.find_map quals (fun uu___98_4752 -> (match (uu___98_4752) with
| FStar_Syntax_Syntax.Reflectable (refl_monad) -> begin
FStar_Pervasives_Native.Some (refl_monad)
end
| uu____4756 -> begin
FStar_Pervasives_Native.None
end)))
in (match (uu____4747) with
| FStar_Pervasives_Native.Some (refl_monad) -> begin
(

let refl_const = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (refl_monad))) FStar_Pervasives_Native.None occurrence_range)
in FStar_Pervasives_Native.Some (Term_name (((refl_const), (false), (se.FStar_Syntax_Syntax.sigattrs)))))
end
| uu____4765 -> begin
(

let uu____4768 = (

let uu____4769 = (

let uu____4778 = (

let uu____4779 = (fv_qual_of_se se)
in (FStar_Syntax_Syntax.fvar lid2 dd1 uu____4779))
in ((uu____4778), (false), (se.FStar_Syntax_Syntax.sigattrs)))
in Term_name (uu____4769))
in FStar_Pervasives_Native.Some (uu____4768))
end)))))
end
| uu____4784 -> begin
FStar_Pervasives_Native.None
end)))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (ne) -> begin
(

let uu____4786 = (

let uu____4787 = (

let uu____4792 = (

let uu____4793 = (FStar_Ident.range_of_lid source_lid)
in (FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname uu____4793))
in ((se), (uu____4792)))
in Eff_name (uu____4787))
in FStar_Pervasives_Native.Some (uu____4786))
end
| FStar_Syntax_Syntax.Sig_new_effect (ne) -> begin
(

let uu____4795 = (

let uu____4796 = (

let uu____4801 = (

let uu____4802 = (FStar_Ident.range_of_lid source_lid)
in (FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname uu____4802))
in ((se), (uu____4801)))
in Eff_name (uu____4796))
in FStar_Pervasives_Native.Some (uu____4795))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (uu____4803) -> begin
FStar_Pervasives_Native.Some (Eff_name (((se), (source_lid))))
end
| FStar_Syntax_Syntax.Sig_splice (lids, t) -> begin
(

let uu____4822 = (

let uu____4823 = (

let uu____4832 = (FStar_Syntax_Syntax.fvar source_lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None)
in ((uu____4832), (false), ([])))
in Term_name (uu____4823))
in FStar_Pervasives_Native.Some (uu____4822))
end
| uu____4835 -> begin
FStar_Pervasives_Native.None
end)
end))
in (

let k_local_binding = (fun r -> (

let uu____4856 = (

let uu____4861 = (FStar_Ident.range_of_lid lid)
in (found_local_binding uu____4861 r))
in (match (uu____4856) with
| (t, mut) -> begin
FStar_Pervasives_Native.Some (Term_name (((t), (mut), ([]))))
end)))
in (

let k_rec_binding = (fun uu____4881 -> (match (uu____4881) with
| (id1, l, dd) -> begin
(

let uu____4893 = (

let uu____4894 = (

let uu____4903 = (

let uu____4904 = (

let uu____4905 = (FStar_Ident.range_of_lid lid)
in (FStar_Ident.set_lid_range l uu____4905))
in (FStar_Syntax_Syntax.fvar uu____4904 dd FStar_Pervasives_Native.None))
in ((uu____4903), (false), ([])))
in Term_name (uu____4894))
in FStar_Pervasives_Native.Some (uu____4893))
end))
in (

let found_unmangled = (match (lid.FStar_Ident.ns) with
| [] -> begin
(

let uu____4913 = (unmangleOpName lid.FStar_Ident.ident)
in (match (uu____4913) with
| FStar_Pervasives_Native.Some (t, mut) -> begin
FStar_Pervasives_Native.Some (Term_name (((t), (mut), ([]))))
end
| uu____4930 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____4937 -> begin
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

let uu____4972 = (try_lookup_name true exclude_interf env lid)
in (match (uu____4972) with
| FStar_Pervasives_Native.Some (Eff_name (o, l)) -> begin
FStar_Pervasives_Native.Some (((o), (l)))
end
| uu____4987 -> begin
FStar_Pervasives_Native.None
end)))


let try_lookup_effect_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident FStar_Pervasives_Native.option = (fun env l -> (

let uu____5006 = (try_lookup_effect_name' (not (env.iface)) env l)
in (match (uu____5006) with
| FStar_Pervasives_Native.Some (o, l1) -> begin
FStar_Pervasives_Native.Some (l1)
end
| uu____5021 -> begin
FStar_Pervasives_Native.None
end)))


let try_lookup_effect_name_and_attributes : env  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.cflags Prims.list) FStar_Pervasives_Native.option = (fun env l -> (

let uu____5046 = (try_lookup_effect_name' (not (env.iface)) env l)
in (match (uu____5046) with
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect (ne); FStar_Syntax_Syntax.sigrng = uu____5062; FStar_Syntax_Syntax.sigquals = uu____5063; FStar_Syntax_Syntax.sigmeta = uu____5064; FStar_Syntax_Syntax.sigattrs = uu____5065}, l1) -> begin
FStar_Pervasives_Native.Some (((l1), (ne.FStar_Syntax_Syntax.cattributes)))
end
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect_for_free (ne); FStar_Syntax_Syntax.sigrng = uu____5084; FStar_Syntax_Syntax.sigquals = uu____5085; FStar_Syntax_Syntax.sigmeta = uu____5086; FStar_Syntax_Syntax.sigattrs = uu____5087}, l1) -> begin
FStar_Pervasives_Native.Some (((l1), (ne.FStar_Syntax_Syntax.cattributes)))
end
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_effect_abbrev (uu____5105, uu____5106, uu____5107, uu____5108, cattributes); FStar_Syntax_Syntax.sigrng = uu____5110; FStar_Syntax_Syntax.sigquals = uu____5111; FStar_Syntax_Syntax.sigmeta = uu____5112; FStar_Syntax_Syntax.sigattrs = uu____5113}, l1) -> begin
FStar_Pervasives_Native.Some (((l1), (cattributes)))
end
| uu____5135 -> begin
FStar_Pervasives_Native.None
end)))


let try_lookup_effect_defn : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl FStar_Pervasives_Native.option = (fun env l -> (

let uu____5160 = (try_lookup_effect_name' (not (env.iface)) env l)
in (match (uu____5160) with
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect (ne); FStar_Syntax_Syntax.sigrng = uu____5170; FStar_Syntax_Syntax.sigquals = uu____5171; FStar_Syntax_Syntax.sigmeta = uu____5172; FStar_Syntax_Syntax.sigattrs = uu____5173}, uu____5174) -> begin
FStar_Pervasives_Native.Some (ne)
end
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect_for_free (ne); FStar_Syntax_Syntax.sigrng = uu____5184; FStar_Syntax_Syntax.sigquals = uu____5185; FStar_Syntax_Syntax.sigmeta = uu____5186; FStar_Syntax_Syntax.sigattrs = uu____5187}, uu____5188) -> begin
FStar_Pervasives_Native.Some (ne)
end
| uu____5197 -> begin
FStar_Pervasives_Native.None
end)))


let is_effect_name : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let uu____5214 = (try_lookup_effect_name env lid)
in (match (uu____5214) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (uu____5217) -> begin
true
end)))


let try_lookup_root_effect_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident FStar_Pervasives_Native.option = (fun env l -> (

let uu____5230 = (try_lookup_effect_name' (not (env.iface)) env l)
in (match (uu____5230) with
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_effect_abbrev (l', uu____5240, uu____5241, uu____5242, uu____5243); FStar_Syntax_Syntax.sigrng = uu____5244; FStar_Syntax_Syntax.sigquals = uu____5245; FStar_Syntax_Syntax.sigmeta = uu____5246; FStar_Syntax_Syntax.sigattrs = uu____5247}, uu____5248) -> begin
(

let rec aux = (fun new_name -> (

let uu____5269 = (FStar_Util.smap_try_find (sigmap env) new_name.FStar_Ident.str)
in (match (uu____5269) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (s, uu____5287) -> begin
(match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_new_effect_for_free (ne) -> begin
(

let uu____5295 = (

let uu____5296 = (FStar_Ident.range_of_lid l)
in (FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname uu____5296))
in FStar_Pervasives_Native.Some (uu____5295))
end
| FStar_Syntax_Syntax.Sig_new_effect (ne) -> begin
(

let uu____5298 = (

let uu____5299 = (FStar_Ident.range_of_lid l)
in (FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname uu____5299))
in FStar_Pervasives_Native.Some (uu____5298))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (uu____5300, uu____5301, uu____5302, cmp, uu____5304) -> begin
(

let l'' = (FStar_Syntax_Util.comp_effect_name cmp)
in (aux l''))
end
| uu____5310 -> begin
FStar_Pervasives_Native.None
end)
end)))
in (aux l'))
end
| FStar_Pervasives_Native.Some (uu____5311, l') -> begin
FStar_Pervasives_Native.Some (l')
end
| uu____5317 -> begin
FStar_Pervasives_Native.None
end)))


let lookup_letbinding_quals : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.qualifier Prims.list = (fun env lid -> (

let k_global_def = (fun lid1 uu___100_5354 -> (match (uu___100_5354) with
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (uu____5363, uu____5364, uu____5365); FStar_Syntax_Syntax.sigrng = uu____5366; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = uu____5368; FStar_Syntax_Syntax.sigattrs = uu____5369}, uu____5370) -> begin
FStar_Pervasives_Native.Some (quals)
end
| uu____5377 -> begin
FStar_Pervasives_Native.None
end))
in (

let uu____5384 = (resolve_in_open_namespaces' env lid (fun uu____5392 -> FStar_Pervasives_Native.None) (fun uu____5396 -> FStar_Pervasives_Native.None) k_global_def)
in (match (uu____5384) with
| FStar_Pervasives_Native.Some (quals) -> begin
quals
end
| uu____5406 -> begin
[]
end))))


let try_lookup_module : env  ->  FStar_Ident.path  ->  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option = (fun env path -> (

let uu____5423 = (FStar_List.tryFind (fun uu____5438 -> (match (uu____5438) with
| (mlid, modul) -> begin
(

let uu____5445 = (FStar_Ident.path_of_lid mlid)
in (Prims.op_Equality uu____5445 path))
end)) env.modules)
in (match (uu____5423) with
| FStar_Pervasives_Native.Some (uu____5448, modul) -> begin
FStar_Pervasives_Native.Some (modul)
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end)))


let try_lookup_let : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun env lid -> (

let k_global_def = (fun lid1 uu___101_5486 -> (match (uu___101_5486) with
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let ((uu____5493, lbs), uu____5495); FStar_Syntax_Syntax.sigrng = uu____5496; FStar_Syntax_Syntax.sigquals = uu____5497; FStar_Syntax_Syntax.sigmeta = uu____5498; FStar_Syntax_Syntax.sigattrs = uu____5499}, uu____5500) -> begin
(

let fv = (lb_fv lbs lid1)
in (

let uu____5514 = (FStar_Syntax_Syntax.fvar lid1 fv.FStar_Syntax_Syntax.fv_delta fv.FStar_Syntax_Syntax.fv_qual)
in FStar_Pervasives_Native.Some (uu____5514)))
end
| uu____5515 -> begin
FStar_Pervasives_Native.None
end))
in (resolve_in_open_namespaces' env lid (fun uu____5521 -> FStar_Pervasives_Native.None) (fun uu____5523 -> FStar_Pervasives_Native.None) k_global_def)))


let try_lookup_definition : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun env lid -> (

let k_global_def = (fun lid1 uu___102_5554 -> (match (uu___102_5554) with
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (lbs, uu____5564); FStar_Syntax_Syntax.sigrng = uu____5565; FStar_Syntax_Syntax.sigquals = uu____5566; FStar_Syntax_Syntax.sigmeta = uu____5567; FStar_Syntax_Syntax.sigattrs = uu____5568}, uu____5569) -> begin
(FStar_Util.find_map (FStar_Pervasives_Native.snd lbs) (fun lb -> (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv lid1) -> begin
FStar_Pervasives_Native.Some (lb.FStar_Syntax_Syntax.lbdef)
end
| uu____5592 -> begin
FStar_Pervasives_Native.None
end)))
end
| uu____5599 -> begin
FStar_Pervasives_Native.None
end))
in (resolve_in_open_namespaces' env lid (fun uu____5609 -> FStar_Pervasives_Native.None) (fun uu____5613 -> FStar_Pervasives_Native.None) k_global_def)))


let empty_include_smap : FStar_Ident.lident Prims.list FStar_ST.ref FStar_Util.smap = (new_sigmap ())


let empty_exported_id_smap : exported_id_set FStar_Util.smap = (new_sigmap ())


let try_lookup_lid' : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term * Prims.bool * FStar_Syntax_Syntax.attribute Prims.list) FStar_Pervasives_Native.option = (fun any_val exclude_interface env lid -> (

let uu____5670 = (try_lookup_name any_val exclude_interface env lid)
in (match (uu____5670) with
| FStar_Pervasives_Native.Some (Term_name (e, mut, attrs)) -> begin
FStar_Pervasives_Native.Some (((e), (mut), (attrs)))
end
| uu____5700 -> begin
FStar_Pervasives_Native.None
end)))


let drop_attributes : (FStar_Syntax_Syntax.term * Prims.bool * FStar_Syntax_Syntax.attribute Prims.list) FStar_Pervasives_Native.option  ->  (FStar_Syntax_Syntax.term * Prims.bool) FStar_Pervasives_Native.option = (fun x -> (match (x) with
| FStar_Pervasives_Native.Some (t, mut, uu____5756) -> begin
FStar_Pervasives_Native.Some (((t), (mut)))
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end))


let try_lookup_lid_with_attributes : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term * Prims.bool * FStar_Syntax_Syntax.attribute Prims.list) FStar_Pervasives_Native.option = (fun env l -> (try_lookup_lid' env.iface false env l))


let try_lookup_lid : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term * Prims.bool) FStar_Pervasives_Native.option = (fun env l -> (

let uu____5831 = (try_lookup_lid_with_attributes env l)
in (FStar_All.pipe_right uu____5831 drop_attributes)))


let resolve_to_fully_qualified_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident FStar_Pervasives_Native.option = (fun env l -> (

let uu____5870 = (try_lookup_lid env l)
in (match (uu____5870) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (e, uu____5884) -> begin
(

let uu____5889 = (

let uu____5890 = (FStar_Syntax_Subst.compress e)
in uu____5890.FStar_Syntax_Syntax.n)
in (match (uu____5889) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
FStar_Pervasives_Native.Some (fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end
| uu____5896 -> begin
FStar_Pervasives_Native.None
end))
end)))


let shorten_lid' : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (

let uu____5907 = (shorten_module_path env lid.FStar_Ident.ns true)
in (match (uu____5907) with
| (uu____5916, short) -> begin
(FStar_Ident.lid_of_ns_and_id short lid.FStar_Ident.ident)
end)))


let shorten_lid : env  ->  FStar_Ident.lid  ->  FStar_Ident.lid = (fun env lid -> (match (env.curmodule) with
| FStar_Pervasives_Native.None -> begin
(shorten_lid' env lid)
end
| uu____5936 -> begin
(

let lid_without_ns = (FStar_Ident.lid_of_ns_and_id [] lid.FStar_Ident.ident)
in (

let uu____5940 = (resolve_to_fully_qualified_name env lid_without_ns)
in (match (uu____5940) with
| FStar_Pervasives_Native.Some (lid') when (Prims.op_Equality lid'.FStar_Ident.str lid.FStar_Ident.str) -> begin
lid_without_ns
end
| uu____5944 -> begin
(shorten_lid' env lid)
end)))
end))


let try_lookup_lid_with_attributes_no_resolve : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term * Prims.bool * FStar_Syntax_Syntax.attribute Prims.list) FStar_Pervasives_Native.option = (fun env l -> (

let env' = (

let uu___123_5978 = env
in {curmodule = uu___123_5978.curmodule; curmonad = uu___123_5978.curmonad; modules = uu___123_5978.modules; scope_mods = []; exported_ids = empty_exported_id_smap; trans_exported_ids = uu___123_5978.trans_exported_ids; includes = empty_include_smap; sigaccum = uu___123_5978.sigaccum; sigmap = uu___123_5978.sigmap; iface = uu___123_5978.iface; admitted_iface = uu___123_5978.admitted_iface; expect_typ = uu___123_5978.expect_typ; docs = uu___123_5978.docs; remaining_iface_decls = uu___123_5978.remaining_iface_decls; syntax_only = uu___123_5978.syntax_only; ds_hooks = uu___123_5978.ds_hooks})
in (try_lookup_lid_with_attributes env' l)))


let try_lookup_lid_no_resolve : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term * Prims.bool) FStar_Pervasives_Native.option = (fun env l -> (

let uu____6001 = (try_lookup_lid_with_attributes_no_resolve env l)
in (FStar_All.pipe_right uu____6001 drop_attributes)))


let try_lookup_doc : env  ->  FStar_Ident.lid  ->  FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option = (fun env l -> (FStar_Util.smap_try_find env.docs l.FStar_Ident.str))


let try_lookup_datacon : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.fv FStar_Pervasives_Native.option = (fun env lid -> (

let k_global_def = (fun lid1 uu___104_6068 -> (match (uu___104_6068) with
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (uu____6075, uu____6076, uu____6077); FStar_Syntax_Syntax.sigrng = uu____6078; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = uu____6080; FStar_Syntax_Syntax.sigattrs = uu____6081}, uu____6082) -> begin
(

let uu____6087 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___103_6091 -> (match (uu___103_6091) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| uu____6092 -> begin
false
end))))
in (match (uu____6087) with
| true -> begin
(

let uu____6095 = (FStar_Syntax_Syntax.lid_as_fv lid1 FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in FStar_Pervasives_Native.Some (uu____6095))
end
| uu____6096 -> begin
FStar_Pervasives_Native.None
end))
end
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (uu____6097); FStar_Syntax_Syntax.sigrng = uu____6098; FStar_Syntax_Syntax.sigquals = uu____6099; FStar_Syntax_Syntax.sigmeta = uu____6100; FStar_Syntax_Syntax.sigattrs = uu____6101}, uu____6102) -> begin
(

let uu____6121 = (FStar_Syntax_Syntax.lid_as_fv lid1 FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))
in FStar_Pervasives_Native.Some (uu____6121))
end
| uu____6122 -> begin
FStar_Pervasives_Native.None
end))
in (resolve_in_open_namespaces' env lid (fun uu____6128 -> FStar_Pervasives_Native.None) (fun uu____6130 -> FStar_Pervasives_Native.None) k_global_def)))


let find_all_datacons : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.list FStar_Pervasives_Native.option = (fun env lid -> (

let k_global_def = (fun lid1 uu___105_6163 -> (match (uu___105_6163) with
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (uu____6172, uu____6173, uu____6174, uu____6175, datas, uu____6177); FStar_Syntax_Syntax.sigrng = uu____6178; FStar_Syntax_Syntax.sigquals = uu____6179; FStar_Syntax_Syntax.sigmeta = uu____6180; FStar_Syntax_Syntax.sigattrs = uu____6181}, uu____6182) -> begin
FStar_Pervasives_Native.Some (datas)
end
| uu____6197 -> begin
FStar_Pervasives_Native.None
end))
in (resolve_in_open_namespaces' env lid (fun uu____6207 -> FStar_Pervasives_Native.None) (fun uu____6211 -> FStar_Pervasives_Native.None) k_global_def)))


let record_cache_aux_with_filter : (((unit  ->  unit) * (unit  ->  unit) * (unit  ->  record_or_dc Prims.list) * (record_or_dc  ->  unit)) * (unit  ->  unit)) = (

let record_cache = (FStar_Util.mk_ref (([])::[]))
in (

let push1 = (fun uu____6263 -> (

let uu____6264 = (

let uu____6269 = (

let uu____6272 = (FStar_ST.op_Bang record_cache)
in (FStar_List.hd uu____6272))
in (

let uu____6332 = (FStar_ST.op_Bang record_cache)
in (uu____6269)::uu____6332))
in (FStar_ST.op_Colon_Equals record_cache uu____6264)))
in (

let pop1 = (fun uu____6450 -> (

let uu____6451 = (

let uu____6456 = (FStar_ST.op_Bang record_cache)
in (FStar_List.tl uu____6456))
in (FStar_ST.op_Colon_Equals record_cache uu____6451)))
in (

let peek1 = (fun uu____6576 -> (

let uu____6577 = (FStar_ST.op_Bang record_cache)
in (FStar_List.hd uu____6577)))
in (

let insert = (fun r -> (

let uu____6643 = (

let uu____6648 = (

let uu____6651 = (peek1 ())
in (r)::uu____6651)
in (

let uu____6654 = (

let uu____6659 = (FStar_ST.op_Bang record_cache)
in (FStar_List.tl uu____6659))
in (uu____6648)::uu____6654))
in (FStar_ST.op_Colon_Equals record_cache uu____6643)))
in (

let filter1 = (fun uu____6779 -> (

let rc = (peek1 ())
in (

let filtered = (FStar_List.filter (fun r -> (not (r.is_private_or_abstract))) rc)
in (

let uu____6788 = (

let uu____6793 = (

let uu____6798 = (FStar_ST.op_Bang record_cache)
in (FStar_List.tl uu____6798))
in (filtered)::uu____6793)
in (FStar_ST.op_Colon_Equals record_cache uu____6788)))))
in (

let aux = ((push1), (pop1), (peek1), (insert))
in ((aux), (filter1)))))))))


let record_cache_aux : ((unit  ->  unit) * (unit  ->  unit) * (unit  ->  record_or_dc Prims.list) * (record_or_dc  ->  unit)) = (

let uu____6997 = record_cache_aux_with_filter
in (match (uu____6997) with
| (aux, uu____7050) -> begin
aux
end))


let filter_record_cache : unit  ->  unit = (

let uu____7105 = record_cache_aux_with_filter
in (match (uu____7105) with
| (uu____7138, filter1) -> begin
filter1
end))


let push_record_cache : unit  ->  unit = (

let uu____7194 = record_cache_aux
in (match (uu____7194) with
| (push1, uu____7221, uu____7222, uu____7223) -> begin
push1
end))


let pop_record_cache : unit  ->  unit = (

let uu____7256 = record_cache_aux
in (match (uu____7256) with
| (uu____7282, pop1, uu____7284, uu____7285) -> begin
pop1
end))


let peek_record_cache : unit  ->  record_or_dc Prims.list = (

let uu____7320 = record_cache_aux
in (match (uu____7320) with
| (uu____7348, uu____7349, peek1, uu____7351) -> begin
peek1
end))


let insert_record_cache : record_or_dc  ->  unit = (

let uu____7384 = record_cache_aux
in (match (uu____7384) with
| (uu____7410, uu____7411, uu____7412, insert) -> begin
insert
end))


let extract_record : env  ->  scope_mod Prims.list FStar_ST.ref  ->  FStar_Syntax_Syntax.sigelt  ->  unit = (fun e new_globs se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_bundle (sigs, uu____7488) -> begin
(

let is_record = (FStar_Util.for_some (fun uu___106_7506 -> (match (uu___106_7506) with
| FStar_Syntax_Syntax.RecordType (uu____7507) -> begin
true
end
| FStar_Syntax_Syntax.RecordConstructor (uu____7516) -> begin
true
end
| uu____7525 -> begin
false
end)))
in (

let find_dc = (fun dc -> (FStar_All.pipe_right sigs (FStar_Util.find_opt (fun uu___107_7549 -> (match (uu___107_7549) with
| {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (lid, uu____7551, uu____7552, uu____7553, uu____7554, uu____7555); FStar_Syntax_Syntax.sigrng = uu____7556; FStar_Syntax_Syntax.sigquals = uu____7557; FStar_Syntax_Syntax.sigmeta = uu____7558; FStar_Syntax_Syntax.sigattrs = uu____7559} -> begin
(FStar_Ident.lid_equals dc lid)
end
| uu____7568 -> begin
false
end)))))
in (FStar_All.pipe_right sigs (FStar_List.iter (fun uu___108_7603 -> (match (uu___108_7603) with
| {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (typename, univs1, parms, uu____7607, uu____7608, (dc)::[]); FStar_Syntax_Syntax.sigrng = uu____7610; FStar_Syntax_Syntax.sigquals = typename_quals; FStar_Syntax_Syntax.sigmeta = uu____7612; FStar_Syntax_Syntax.sigattrs = uu____7613} -> begin
(

let uu____7624 = (

let uu____7625 = (find_dc dc)
in (FStar_All.pipe_left FStar_Util.must uu____7625))
in (match (uu____7624) with
| {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (constrname, uu____7631, t, uu____7633, uu____7634, uu____7635); FStar_Syntax_Syntax.sigrng = uu____7636; FStar_Syntax_Syntax.sigquals = uu____7637; FStar_Syntax_Syntax.sigmeta = uu____7638; FStar_Syntax_Syntax.sigattrs = uu____7639} -> begin
(

let uu____7648 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____7648) with
| (formals, uu____7662) -> begin
(

let is_rec = (is_record typename_quals)
in (

let formals' = (FStar_All.pipe_right formals (FStar_List.collect (fun uu____7711 -> (match (uu____7711) with
| (x, q) -> begin
(

let uu____7724 = ((FStar_Syntax_Syntax.is_null_bv x) || (is_rec && (FStar_Syntax_Syntax.is_implicit q)))
in (match (uu____7724) with
| true -> begin
[]
end
| uu____7735 -> begin
(((x), (q)))::[]
end))
end))))
in (

let fields' = (FStar_All.pipe_right formals' (FStar_List.map (fun uu____7781 -> (match (uu____7781) with
| (x, q) -> begin
(

let uu____7794 = (match (is_rec) with
| true -> begin
(FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname)
end
| uu____7795 -> begin
x.FStar_Syntax_Syntax.ppname
end)
in ((uu____7794), (x.FStar_Syntax_Syntax.sort)))
end))))
in (

let fields = fields'
in (

let record = {typename = typename; constrname = constrname.FStar_Ident.ident; parms = parms; fields = fields; is_private_or_abstract = ((FStar_List.contains FStar_Syntax_Syntax.Private typename_quals) || (FStar_List.contains FStar_Syntax_Syntax.Abstract typename_quals)); is_record = is_rec}
in ((

let uu____7809 = (

let uu____7812 = (FStar_ST.op_Bang new_globs)
in (Record_or_dc (record))::uu____7812)
in (FStar_ST.op_Colon_Equals new_globs uu____7809));
(match (()) with
| () -> begin
((

let add_field = (fun uu____7925 -> (match (uu____7925) with
| (id1, uu____7933) -> begin
(

let modul = (

let uu____7939 = (FStar_Ident.lid_of_ids constrname.FStar_Ident.ns)
in uu____7939.FStar_Ident.str)
in (

let uu____7940 = (get_exported_id_set e modul)
in (match (uu____7940) with
| FStar_Pervasives_Native.Some (my_ex) -> begin
(

let my_exported_ids = (my_ex Exported_id_field)
in ((

let uu____7974 = (

let uu____7975 = (FStar_ST.op_Bang my_exported_ids)
in (FStar_Util.set_add id1.FStar_Ident.idText uu____7975))
in (FStar_ST.op_Colon_Equals my_exported_ids uu____7974));
(match (()) with
| () -> begin
(

let projname = (

let uu____8069 = (

let uu____8070 = (FStar_Syntax_Util.mk_field_projector_name_from_ident constrname id1)
in uu____8070.FStar_Ident.ident)
in uu____8069.FStar_Ident.idText)
in (

let uu____8072 = (

let uu____8073 = (FStar_ST.op_Bang my_exported_ids)
in (FStar_Util.set_add projname uu____8073))
in (FStar_ST.op_Colon_Equals my_exported_ids uu____8072)))
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
| uu____8177 -> begin
()
end))
end
| uu____8178 -> begin
()
end))))))
end
| uu____8179 -> begin
()
end))


let try_lookup_record_or_dc_by_field_name : env  ->  FStar_Ident.lident  ->  record_or_dc FStar_Pervasives_Native.option = (fun env fieldname -> (

let find_in_cache = (fun fieldname1 -> (

let uu____8200 = ((fieldname1.FStar_Ident.ns), (fieldname1.FStar_Ident.ident))
in (match (uu____8200) with
| (ns, id1) -> begin
(

let uu____8217 = (peek_record_cache ())
in (FStar_Util.find_map uu____8217 (fun record -> (

let uu____8223 = (find_in_record ns id1 record (fun r -> Cont_ok (r)))
in (option_of_cont (fun uu____8229 -> FStar_Pervasives_Native.None) uu____8223)))))
end)))
in (resolve_in_open_namespaces'' env fieldname Exported_id_field (fun uu____8231 -> Cont_ignore) (fun uu____8233 -> Cont_ignore) (fun r -> Cont_ok (r)) (fun fn -> (

let uu____8239 = (find_in_cache fn)
in (cont_of_option Cont_ignore uu____8239))) (fun k uu____8245 -> k))))


let try_lookup_record_by_field_name : env  ->  FStar_Ident.lident  ->  record_or_dc FStar_Pervasives_Native.option = (fun env fieldname -> (

let uu____8260 = (try_lookup_record_or_dc_by_field_name env fieldname)
in (match (uu____8260) with
| FStar_Pervasives_Native.Some (r) when r.is_record -> begin
FStar_Pervasives_Native.Some (r)
end
| uu____8266 -> begin
FStar_Pervasives_Native.None
end)))


let belongs_to_record : env  ->  FStar_Ident.lident  ->  record_or_dc  ->  Prims.bool = (fun env lid record -> (

let uu____8284 = (try_lookup_record_by_field_name env lid)
in (match (uu____8284) with
| FStar_Pervasives_Native.Some (record') when (

let uu____8288 = (

let uu____8289 = (FStar_Ident.path_of_ns record.typename.FStar_Ident.ns)
in (FStar_Ident.text_of_path uu____8289))
in (

let uu____8290 = (

let uu____8291 = (FStar_Ident.path_of_ns record'.typename.FStar_Ident.ns)
in (FStar_Ident.text_of_path uu____8291))
in (Prims.op_Equality uu____8288 uu____8290))) -> begin
(

let uu____8292 = (find_in_record record.typename.FStar_Ident.ns lid.FStar_Ident.ident record (fun uu____8296 -> Cont_ok (())))
in (match (uu____8292) with
| Cont_ok (uu____8297) -> begin
true
end
| uu____8298 -> begin
false
end))
end
| uu____8301 -> begin
false
end)))


let try_lookup_dc_by_field_name : env  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * Prims.bool) FStar_Pervasives_Native.option = (fun env fieldname -> (

let uu____8320 = (try_lookup_record_or_dc_by_field_name env fieldname)
in (match (uu____8320) with
| FStar_Pervasives_Native.Some (r) -> begin
(

let uu____8330 = (

let uu____8335 = (

let uu____8336 = (FStar_Ident.lid_of_ids (FStar_List.append r.typename.FStar_Ident.ns ((r.constrname)::[])))
in (

let uu____8337 = (FStar_Ident.range_of_lid fieldname)
in (FStar_Ident.set_lid_range uu____8336 uu____8337)))
in ((uu____8335), (r.is_record)))
in FStar_Pervasives_Native.Some (uu____8330))
end
| uu____8342 -> begin
FStar_Pervasives_Native.None
end)))


let string_set_ref_new : unit  ->  Prims.string FStar_Util.set FStar_ST.ref = (fun uu____8368 -> (

let uu____8369 = (FStar_Util.new_set FStar_Util.compare)
in (FStar_Util.mk_ref uu____8369)))


let exported_id_set_new : unit  ->  exported_id_kind  ->  Prims.string FStar_Util.set FStar_ST.ref = (fun uu____8396 -> (

let term_type_set = (string_set_ref_new ())
in (

let field_set = (string_set_ref_new ())
in (fun uu___109_8407 -> (match (uu___109_8407) with
| Exported_id_term_type -> begin
term_type_set
end
| Exported_id_field -> begin
field_set
end)))))


let unique : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  Prims.bool = (fun any_val exclude_interface env lid -> (

let filter_scope_mods = (fun uu___110_8459 -> (match (uu___110_8459) with
| Rec_binding (uu____8460) -> begin
true
end
| uu____8461 -> begin
false
end))
in (

let this_env = (

let uu___124_8463 = env
in (

let uu____8464 = (FStar_List.filter filter_scope_mods env.scope_mods)
in {curmodule = uu___124_8463.curmodule; curmonad = uu___124_8463.curmonad; modules = uu___124_8463.modules; scope_mods = uu____8464; exported_ids = empty_exported_id_smap; trans_exported_ids = uu___124_8463.trans_exported_ids; includes = empty_include_smap; sigaccum = uu___124_8463.sigaccum; sigmap = uu___124_8463.sigmap; iface = uu___124_8463.iface; admitted_iface = uu___124_8463.admitted_iface; expect_typ = uu___124_8463.expect_typ; docs = uu___124_8463.docs; remaining_iface_decls = uu___124_8463.remaining_iface_decls; syntax_only = uu___124_8463.syntax_only; ds_hooks = uu___124_8463.ds_hooks}))
in (

let uu____8467 = (try_lookup_lid' any_val exclude_interface this_env lid)
in (match (uu____8467) with
| FStar_Pervasives_Native.None -> begin
true
end
| FStar_Pervasives_Native.Some (uu____8486) -> begin
false
end)))))


let push_scope_mod : env  ->  scope_mod  ->  env = (fun env scope_mod -> (

let uu___125_8513 = env
in {curmodule = uu___125_8513.curmodule; curmonad = uu___125_8513.curmonad; modules = uu___125_8513.modules; scope_mods = (scope_mod)::env.scope_mods; exported_ids = uu___125_8513.exported_ids; trans_exported_ids = uu___125_8513.trans_exported_ids; includes = uu___125_8513.includes; sigaccum = uu___125_8513.sigaccum; sigmap = uu___125_8513.sigmap; iface = uu___125_8513.iface; admitted_iface = uu___125_8513.admitted_iface; expect_typ = uu___125_8513.expect_typ; docs = uu___125_8513.docs; remaining_iface_decls = uu___125_8513.remaining_iface_decls; syntax_only = uu___125_8513.syntax_only; ds_hooks = uu___125_8513.ds_hooks}))


let push_bv' : env  ->  FStar_Ident.ident  ->  Prims.bool  ->  (env * FStar_Syntax_Syntax.bv) = (fun env x is_mutable -> (

let bv = (FStar_Syntax_Syntax.gen_bv x.FStar_Ident.idText (FStar_Pervasives_Native.Some (x.FStar_Ident.idRange)) FStar_Syntax_Syntax.tun)
in (((push_scope_mod env (Local_binding (((x), (bv), (is_mutable)))))), (bv))))


let push_bv_mutable : env  ->  FStar_Ident.ident  ->  (env * FStar_Syntax_Syntax.bv) = (fun env x -> (push_bv' env x true))


let push_bv : env  ->  FStar_Ident.ident  ->  (env * FStar_Syntax_Syntax.bv) = (fun env x -> (push_bv' env x false))


let push_top_level_rec_binding : env  ->  FStar_Ident.ident  ->  FStar_Syntax_Syntax.delta_depth  ->  env = (fun env x dd -> (

let l = (qualify env x)
in (

let uu____8578 = ((unique false true env l) || (FStar_Options.interactive ()))
in (match (uu____8578) with
| true -> begin
(push_scope_mod env (Rec_binding (((x), (l), (dd)))))
end
| uu____8579 -> begin
(

let uu____8580 = (FStar_Ident.range_of_lid l)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_DuplicateTopLevelNames), ((Prims.strcat "Duplicate top-level names " l.FStar_Ident.str))) uu____8580))
end))))


let push_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env s -> (

let err = (fun l -> (

let sopt = (FStar_Util.smap_try_find (sigmap env) l.FStar_Ident.str)
in (

let r = (match (sopt) with
| FStar_Pervasives_Native.Some (se, uu____8610) -> begin
(

let uu____8615 = (FStar_Util.find_opt (FStar_Ident.lid_equals l) (FStar_Syntax_Util.lids_of_sigelt se))
in (match (uu____8615) with
| FStar_Pervasives_Native.Some (l1) -> begin
(

let uu____8619 = (FStar_Ident.range_of_lid l1)
in (FStar_All.pipe_left FStar_Range.string_of_range uu____8619))
end
| FStar_Pervasives_Native.None -> begin
"<unknown>"
end))
end
| FStar_Pervasives_Native.None -> begin
"<unknown>"
end)
in (

let uu____8624 = (

let uu____8629 = (

let uu____8630 = (FStar_Ident.text_of_lid l)
in (FStar_Util.format2 "Duplicate top-level names [%s]; previously declared at %s" uu____8630 r))
in ((FStar_Errors.Fatal_DuplicateTopLevelNames), (uu____8629)))
in (

let uu____8631 = (FStar_Ident.range_of_lid l)
in (FStar_Errors.raise_error uu____8624 uu____8631))))))
in (

let globals = (FStar_Util.mk_ref env.scope_mods)
in (

let env1 = (

let uu____8640 = (match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let (uu____8649) -> begin
((false), (true))
end
| FStar_Syntax_Syntax.Sig_bundle (uu____8656) -> begin
((false), (true))
end
| uu____8665 -> begin
((false), (false))
end)
in (match (uu____8640) with
| (any_val, exclude_interface) -> begin
(

let lids = (FStar_Syntax_Util.lids_of_sigelt s)
in (

let uu____8671 = (FStar_Util.find_map lids (fun l -> (

let uu____8677 = (

let uu____8678 = (unique any_val exclude_interface env l)
in (not (uu____8678)))
in (match (uu____8677) with
| true -> begin
FStar_Pervasives_Native.Some (l)
end
| uu____8681 -> begin
FStar_Pervasives_Native.None
end))))
in (match (uu____8671) with
| FStar_Pervasives_Native.Some (l) -> begin
(err l)
end
| uu____8683 -> begin
((extract_record env globals s);
(

let uu___126_8709 = env
in {curmodule = uu___126_8709.curmodule; curmonad = uu___126_8709.curmonad; modules = uu___126_8709.modules; scope_mods = uu___126_8709.scope_mods; exported_ids = uu___126_8709.exported_ids; trans_exported_ids = uu___126_8709.trans_exported_ids; includes = uu___126_8709.includes; sigaccum = (s)::env.sigaccum; sigmap = uu___126_8709.sigmap; iface = uu___126_8709.iface; admitted_iface = uu___126_8709.admitted_iface; expect_typ = uu___126_8709.expect_typ; docs = uu___126_8709.docs; remaining_iface_decls = uu___126_8709.remaining_iface_decls; syntax_only = uu___126_8709.syntax_only; ds_hooks = uu___126_8709.ds_hooks});
)
end)))
end))
in (

let env2 = (

let uu___127_8711 = env1
in (

let uu____8712 = (FStar_ST.op_Bang globals)
in {curmodule = uu___127_8711.curmodule; curmonad = uu___127_8711.curmonad; modules = uu___127_8711.modules; scope_mods = uu____8712; exported_ids = uu___127_8711.exported_ids; trans_exported_ids = uu___127_8711.trans_exported_ids; includes = uu___127_8711.includes; sigaccum = uu___127_8711.sigaccum; sigmap = uu___127_8711.sigmap; iface = uu___127_8711.iface; admitted_iface = uu___127_8711.admitted_iface; expect_typ = uu___127_8711.expect_typ; docs = uu___127_8711.docs; remaining_iface_decls = uu___127_8711.remaining_iface_decls; syntax_only = uu___127_8711.syntax_only; ds_hooks = uu___127_8711.ds_hooks}))
in (

let uu____8764 = (match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____8790) -> begin
(

let uu____8799 = (FStar_List.map (fun se -> (((FStar_Syntax_Util.lids_of_sigelt se)), (se))) ses)
in ((env2), (uu____8799)))
end
| uu____8826 -> begin
((env2), (((((FStar_Syntax_Util.lids_of_sigelt s)), (s)))::[]))
end)
in (match (uu____8764) with
| (env3, lss) -> begin
((FStar_All.pipe_right lss (FStar_List.iter (fun uu____8885 -> (match (uu____8885) with
| (lids, se) -> begin
(FStar_All.pipe_right lids (FStar_List.iter (fun lid -> ((

let uu____8907 = (

let uu____8910 = (FStar_ST.op_Bang globals)
in (Top_level_def (lid.FStar_Ident.ident))::uu____8910)
in (FStar_ST.op_Colon_Equals globals uu____8907));
(match (()) with
| () -> begin
(

let modul = (

let uu____9012 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in uu____9012.FStar_Ident.str)
in ((

let uu____9014 = (get_exported_id_set env3 modul)
in (match (uu____9014) with
| FStar_Pervasives_Native.Some (f) -> begin
(

let my_exported_ids = (f Exported_id_term_type)
in (

let uu____9047 = (

let uu____9048 = (FStar_ST.op_Bang my_exported_ids)
in (FStar_Util.set_add lid.FStar_Ident.ident.FStar_Ident.idText uu____9048))
in (FStar_ST.op_Colon_Equals my_exported_ids uu____9047)))
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

let uu___128_9152 = env3
in (

let uu____9153 = (FStar_ST.op_Bang globals)
in {curmodule = uu___128_9152.curmodule; curmonad = uu___128_9152.curmonad; modules = uu___128_9152.modules; scope_mods = uu____9153; exported_ids = uu___128_9152.exported_ids; trans_exported_ids = uu___128_9152.trans_exported_ids; includes = uu___128_9152.includes; sigaccum = uu___128_9152.sigaccum; sigmap = uu___128_9152.sigmap; iface = uu___128_9152.iface; admitted_iface = uu___128_9152.admitted_iface; expect_typ = uu___128_9152.expect_typ; docs = uu___128_9152.docs; remaining_iface_decls = uu___128_9152.remaining_iface_decls; syntax_only = uu___128_9152.syntax_only; ds_hooks = uu___128_9152.ds_hooks}))
in env4);
)
end)))))))


let push_namespace : env  ->  FStar_Ident.lident  ->  env = (fun env ns -> (

let uu____9215 = (

let uu____9220 = (resolve_module_name env ns false)
in (match (uu____9220) with
| FStar_Pervasives_Native.None -> begin
(

let modules = env.modules
in (

let uu____9234 = (FStar_All.pipe_right modules (FStar_Util.for_some (fun uu____9250 -> (match (uu____9250) with
| (m, uu____9256) -> begin
(

let uu____9257 = (

let uu____9258 = (FStar_Ident.text_of_lid m)
in (Prims.strcat uu____9258 "."))
in (

let uu____9259 = (

let uu____9260 = (FStar_Ident.text_of_lid ns)
in (Prims.strcat uu____9260 "."))
in (FStar_Util.starts_with uu____9257 uu____9259)))
end))))
in (match (uu____9234) with
| true -> begin
((ns), (Open_namespace))
end
| uu____9265 -> begin
(

let uu____9266 = (

let uu____9271 = (

let uu____9272 = (FStar_Ident.text_of_lid ns)
in (FStar_Util.format1 "Namespace %s cannot be found" uu____9272))
in ((FStar_Errors.Fatal_NameSpaceNotFound), (uu____9271)))
in (

let uu____9273 = (FStar_Ident.range_of_lid ns)
in (FStar_Errors.raise_error uu____9266 uu____9273)))
end)))
end
| FStar_Pervasives_Native.Some (ns') -> begin
((fail_if_curmodule env ns ns');
((ns'), (Open_module));
)
end))
in (match (uu____9215) with
| (ns', kd) -> begin
((env.ds_hooks.ds_push_open_hook env ((ns'), (kd)));
(push_scope_mod env (Open_module_or_namespace (((ns'), (kd)))));
)
end)))


let push_include : env  ->  FStar_Ident.lident  ->  env = (fun env ns -> (

let ns0 = ns
in (

let uu____9294 = (resolve_module_name env ns false)
in (match (uu____9294) with
| FStar_Pervasives_Native.Some (ns1) -> begin
((env.ds_hooks.ds_push_include_hook env ns1);
(fail_if_curmodule env ns0 ns1);
(

let env1 = (push_scope_mod env (Open_module_or_namespace (((ns1), (Open_module)))))
in (

let curmod = (

let uu____9302 = (current_module env1)
in uu____9302.FStar_Ident.str)
in ((

let uu____9304 = (FStar_Util.smap_try_find env1.includes curmod)
in (match (uu____9304) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (incl) -> begin
(

let uu____9328 = (

let uu____9331 = (FStar_ST.op_Bang incl)
in (ns1)::uu____9331)
in (FStar_ST.op_Colon_Equals incl uu____9328))
end));
(match (()) with
| () -> begin
(

let uu____9432 = (get_trans_exported_id_set env1 ns1.FStar_Ident.str)
in (match (uu____9432) with
| FStar_Pervasives_Native.Some (ns_trans_exports) -> begin
((

let uu____9452 = (

let uu____9555 = (get_exported_id_set env1 curmod)
in (

let uu____9605 = (get_trans_exported_id_set env1 curmod)
in ((uu____9555), (uu____9605))))
in (match (uu____9452) with
| (FStar_Pervasives_Native.Some (cur_exports), FStar_Pervasives_Native.Some (cur_trans_exports)) -> begin
(

let update_exports = (fun k -> (

let ns_ex = (

let uu____10048 = (ns_trans_exports k)
in (FStar_ST.op_Bang uu____10048))
in (

let ex = (cur_exports k)
in ((

let uu____10234 = (

let uu____10237 = (FStar_ST.op_Bang ex)
in (FStar_Util.set_difference uu____10237 ns_ex))
in (FStar_ST.op_Colon_Equals ex uu____10234));
(match (()) with
| () -> begin
(

let trans_ex = (cur_trans_exports k)
in (

let uu____10441 = (

let uu____10444 = (FStar_ST.op_Bang trans_ex)
in (FStar_Util.set_union uu____10444 ns_ex))
in (FStar_ST.op_Colon_Equals trans_ex uu____10441)))
end);
))))
in (FStar_List.iter update_exports all_exported_id_kinds))
end
| uu____10581 -> begin
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

let uu____10689 = (

let uu____10694 = (FStar_Util.format1 "include: Module %s was not prepared" ns1.FStar_Ident.str)
in ((FStar_Errors.Fatal_IncludeModuleNotPrepared), (uu____10694)))
in (

let uu____10695 = (FStar_Ident.range_of_lid ns1)
in (FStar_Errors.raise_error uu____10689 uu____10695)))
end))
end);
)));
)
end
| uu____10696 -> begin
(

let uu____10699 = (

let uu____10704 = (FStar_Util.format1 "include: Module %s cannot be found" ns.FStar_Ident.str)
in ((FStar_Errors.Fatal_ModuleNotFound), (uu____10704)))
in (

let uu____10705 = (FStar_Ident.range_of_lid ns)
in (FStar_Errors.raise_error uu____10699 uu____10705)))
end))))


let push_module_abbrev : env  ->  FStar_Ident.ident  ->  FStar_Ident.lident  ->  env = (fun env x l -> (

let uu____10721 = (module_is_defined env l)
in (match (uu____10721) with
| true -> begin
((fail_if_curmodule env l l);
(env.ds_hooks.ds_push_module_abbrev_hook env x l);
(push_scope_mod env (Module_abbrev (((x), (l)))));
)
end
| uu____10724 -> begin
(

let uu____10725 = (

let uu____10730 = (

let uu____10731 = (FStar_Ident.text_of_lid l)
in (FStar_Util.format1 "Module %s cannot be found" uu____10731))
in ((FStar_Errors.Fatal_ModuleNotFound), (uu____10730)))
in (

let uu____10732 = (FStar_Ident.range_of_lid l)
in (FStar_Errors.raise_error uu____10725 uu____10732)))
end)))


let push_doc : env  ->  FStar_Ident.lident  ->  FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option  ->  env = (fun env l doc_opt -> (match (doc_opt) with
| FStar_Pervasives_Native.None -> begin
env
end
| FStar_Pervasives_Native.Some (doc1) -> begin
((

let uu____10754 = (FStar_Util.smap_try_find env.docs l.FStar_Ident.str)
in (match (uu____10754) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (old_doc) -> begin
(

let uu____10758 = (FStar_Ident.range_of_lid l)
in (

let uu____10759 = (

let uu____10764 = (

let uu____10765 = (FStar_Ident.string_of_lid l)
in (

let uu____10766 = (FStar_Parser_AST.string_of_fsdoc old_doc)
in (

let uu____10767 = (FStar_Parser_AST.string_of_fsdoc doc1)
in (FStar_Util.format3 "Overwriting doc of %s; old doc was [%s]; new doc are [%s]" uu____10765 uu____10766 uu____10767))))
in ((FStar_Errors.Warning_DocOverwrite), (uu____10764)))
in (FStar_Errors.log_issue uu____10758 uu____10759)))
end));
(FStar_Util.smap_add env.docs l.FStar_Ident.str doc1);
env;
)
end))


let check_admits : env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.modul = (fun env m -> (

let admitted_sig_lids = (FStar_All.pipe_right env.sigaccum (FStar_List.fold_left (fun lids se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_declare_typ (l, u, t) when (

let uu____10809 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_List.contains FStar_Syntax_Syntax.Assumption))
in (not (uu____10809))) -> begin
(

let uu____10812 = (FStar_Util.smap_try_find (sigmap env) l.FStar_Ident.str)
in (match (uu____10812) with
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (uu____10825); FStar_Syntax_Syntax.sigrng = uu____10826; FStar_Syntax_Syntax.sigquals = uu____10827; FStar_Syntax_Syntax.sigmeta = uu____10828; FStar_Syntax_Syntax.sigattrs = uu____10829}, uu____10830) -> begin
lids
end
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (uu____10845); FStar_Syntax_Syntax.sigrng = uu____10846; FStar_Syntax_Syntax.sigquals = uu____10847; FStar_Syntax_Syntax.sigmeta = uu____10848; FStar_Syntax_Syntax.sigattrs = uu____10849}, uu____10850) -> begin
lids
end
| uu____10875 -> begin
((

let uu____10883 = (

let uu____10884 = (FStar_Options.interactive ())
in (not (uu____10884)))
in (match (uu____10883) with
| true -> begin
(

let uu____10885 = (FStar_Ident.range_of_lid l)
in (

let uu____10886 = (

let uu____10891 = (

let uu____10892 = (FStar_Ident.string_of_lid l)
in (FStar_Util.format1 "Admitting %s without a definition" uu____10892))
in ((FStar_Errors.Warning_AdmitWithoutDefinition), (uu____10891)))
in (FStar_Errors.log_issue uu____10885 uu____10886)))
end
| uu____10893 -> begin
()
end));
(

let quals = (FStar_Syntax_Syntax.Assumption)::se.FStar_Syntax_Syntax.sigquals
in ((FStar_Util.smap_add (sigmap env) l.FStar_Ident.str (((

let uu___129_10903 = se
in {FStar_Syntax_Syntax.sigel = uu___129_10903.FStar_Syntax_Syntax.sigel; FStar_Syntax_Syntax.sigrng = uu___129_10903.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = uu___129_10903.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___129_10903.FStar_Syntax_Syntax.sigattrs})), (false)));
(l)::lids;
));
)
end))
end
| uu____10904 -> begin
lids
end)) []))
in (

let uu___130_10905 = m
in (

let uu____10906 = (FStar_All.pipe_right m.FStar_Syntax_Syntax.declarations (FStar_List.map (fun s -> (match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____10916, uu____10917) when (FStar_List.existsb (fun l -> (FStar_Ident.lid_equals l lid)) admitted_sig_lids) -> begin
(

let uu___131_10920 = s
in {FStar_Syntax_Syntax.sigel = uu___131_10920.FStar_Syntax_Syntax.sigel; FStar_Syntax_Syntax.sigrng = uu___131_10920.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Assumption)::s.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___131_10920.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___131_10920.FStar_Syntax_Syntax.sigattrs})
end
| uu____10921 -> begin
s
end))))
in {FStar_Syntax_Syntax.name = uu___130_10905.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = uu____10906; FStar_Syntax_Syntax.exports = uu___130_10905.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = uu___130_10905.FStar_Syntax_Syntax.is_interface}))))


let finish : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env modul -> ((FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations (FStar_List.iter (fun se -> (

let quals = se.FStar_Syntax_Syntax.sigquals
in (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____10944) -> begin
(match (((FStar_List.contains FStar_Syntax_Syntax.Private quals) || (FStar_List.contains FStar_Syntax_Syntax.Abstract quals))) with
| true -> begin
(FStar_All.pipe_right ses (FStar_List.iter (fun se1 -> (match (se1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (lid, uu____10964, uu____10965, uu____10966, uu____10967, uu____10968) -> begin
(FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str)
end
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, univ_names, binders, typ, uu____10981, uu____10982) -> begin
((FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str);
(match ((not ((FStar_List.contains FStar_Syntax_Syntax.Private quals)))) with
| true -> begin
(

let sigel = (

let uu____10997 = (

let uu____11004 = (

let uu____11005 = (FStar_Ident.range_of_lid lid)
in (

let uu____11006 = (

let uu____11013 = (

let uu____11014 = (

let uu____11027 = (FStar_Syntax_Syntax.mk_Total typ)
in ((binders), (uu____11027)))
in FStar_Syntax_Syntax.Tm_arrow (uu____11014))
in (FStar_Syntax_Syntax.mk uu____11013))
in (uu____11006 FStar_Pervasives_Native.None uu____11005)))
in ((lid), (univ_names), (uu____11004)))
in FStar_Syntax_Syntax.Sig_declare_typ (uu____10997))
in (

let se2 = (

let uu___132_11042 = se1
in {FStar_Syntax_Syntax.sigel = sigel; FStar_Syntax_Syntax.sigrng = uu___132_11042.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Assumption)::quals; FStar_Syntax_Syntax.sigmeta = uu___132_11042.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___132_11042.FStar_Syntax_Syntax.sigattrs})
in (FStar_Util.smap_add (sigmap env) lid.FStar_Ident.str ((se2), (false)))))
end
| uu____11047 -> begin
()
end);
)
end
| uu____11048 -> begin
()
end))))
end
| uu____11049 -> begin
()
end)
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____11051, uu____11052) -> begin
(match ((FStar_List.contains FStar_Syntax_Syntax.Private quals)) with
| true -> begin
(FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str)
end
| uu____11057 -> begin
()
end)
end
| FStar_Syntax_Syntax.Sig_let ((uu____11058, lbs), uu____11060) -> begin
((match (((FStar_List.contains FStar_Syntax_Syntax.Private quals) || (FStar_List.contains FStar_Syntax_Syntax.Abstract quals))) with
| true -> begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (

let uu____11075 = (

let uu____11076 = (

let uu____11077 = (

let uu____11080 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in uu____11080.FStar_Syntax_Syntax.fv_name)
in uu____11077.FStar_Syntax_Syntax.v)
in uu____11076.FStar_Ident.str)
in (FStar_Util.smap_remove (sigmap env) uu____11075)))))
end
| uu____11085 -> begin
()
end);
(match (((FStar_List.contains FStar_Syntax_Syntax.Abstract quals) && (not ((FStar_List.contains FStar_Syntax_Syntax.Private quals))))) with
| true -> begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (

let lid = (

let uu____11094 = (

let uu____11097 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in uu____11097.FStar_Syntax_Syntax.fv_name)
in uu____11094.FStar_Syntax_Syntax.v)
in (

let quals1 = (FStar_Syntax_Syntax.Assumption)::quals
in (

let decl = (

let uu___133_11102 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp))); FStar_Syntax_Syntax.sigrng = uu___133_11102.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = uu___133_11102.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___133_11102.FStar_Syntax_Syntax.sigattrs})
in (FStar_Util.smap_add (sigmap env) lid.FStar_Ident.str ((decl), (false)))))))))
end
| uu____11107 -> begin
()
end);
)
end
| uu____11108 -> begin
()
end)))));
(

let curmod = (

let uu____11110 = (current_module env)
in uu____11110.FStar_Ident.str)
in ((

let uu____11112 = (

let uu____11215 = (get_exported_id_set env curmod)
in (

let uu____11265 = (get_trans_exported_id_set env curmod)
in ((uu____11215), (uu____11265))))
in (match (uu____11112) with
| (FStar_Pervasives_Native.Some (cur_ex), FStar_Pervasives_Native.Some (cur_trans_ex)) -> begin
(

let update_exports = (fun eikind -> (

let cur_ex_set = (

let uu____11710 = (cur_ex eikind)
in (FStar_ST.op_Bang uu____11710))
in (

let cur_trans_ex_set_ref = (cur_trans_ex eikind)
in (

let uu____11909 = (

let uu____11912 = (FStar_ST.op_Bang cur_trans_ex_set_ref)
in (FStar_Util.set_union cur_ex_set uu____11912))
in (FStar_ST.op_Colon_Equals cur_trans_ex_set_ref uu____11909)))))
in (FStar_List.iter update_exports all_exported_id_kinds))
end
| uu____12049 -> begin
()
end));
(match (()) with
| () -> begin
((filter_record_cache ());
(match (()) with
| () -> begin
(

let uu___134_12153 = env
in {curmodule = FStar_Pervasives_Native.None; curmonad = uu___134_12153.curmonad; modules = (((modul.FStar_Syntax_Syntax.name), (modul)))::env.modules; scope_mods = []; exported_ids = uu___134_12153.exported_ids; trans_exported_ids = uu___134_12153.trans_exported_ids; includes = uu___134_12153.includes; sigaccum = []; sigmap = uu___134_12153.sigmap; iface = uu___134_12153.iface; admitted_iface = uu___134_12153.admitted_iface; expect_typ = uu___134_12153.expect_typ; docs = uu___134_12153.docs; remaining_iface_decls = uu___134_12153.remaining_iface_decls; syntax_only = uu___134_12153.syntax_only; ds_hooks = uu___134_12153.ds_hooks})
end);
)
end);
));
))


let stack : env Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let push : env  ->  env = (fun env -> ((push_record_cache ());
(

let uu____12182 = (

let uu____12185 = (FStar_ST.op_Bang stack)
in (env)::uu____12185)
in (FStar_ST.op_Colon_Equals stack uu____12182));
(

let uu___135_12242 = env
in (

let uu____12243 = (FStar_Util.smap_copy (sigmap env))
in (

let uu____12254 = (FStar_Util.smap_copy env.docs)
in {curmodule = uu___135_12242.curmodule; curmonad = uu___135_12242.curmonad; modules = uu___135_12242.modules; scope_mods = uu___135_12242.scope_mods; exported_ids = uu___135_12242.exported_ids; trans_exported_ids = uu___135_12242.trans_exported_ids; includes = uu___135_12242.includes; sigaccum = uu___135_12242.sigaccum; sigmap = uu____12243; iface = uu___135_12242.iface; admitted_iface = uu___135_12242.admitted_iface; expect_typ = uu___135_12242.expect_typ; docs = uu____12254; remaining_iface_decls = uu___135_12242.remaining_iface_decls; syntax_only = uu___135_12242.syntax_only; ds_hooks = uu___135_12242.ds_hooks})));
))


let pop : unit  ->  env = (fun uu____12261 -> (

let uu____12262 = (FStar_ST.op_Bang stack)
in (match (uu____12262) with
| (env)::tl1 -> begin
((pop_record_cache ());
(FStar_ST.op_Colon_Equals stack tl1);
env;
)
end
| uu____12325 -> begin
(failwith "Impossible: Too many pops")
end)))


let export_interface : FStar_Ident.lident  ->  env  ->  env = (fun m env -> (

let sigelt_in_m = (fun se -> (match ((FStar_Syntax_Util.lids_of_sigelt se)) with
| (l)::uu____12345 -> begin
(Prims.op_Equality l.FStar_Ident.nsstr m.FStar_Ident.str)
end
| uu____12348 -> begin
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

let uu____12382 = (FStar_Util.smap_try_find sm' k)
in (match (uu____12382) with
| FStar_Pervasives_Native.Some (se, true) when (sigelt_in_m se) -> begin
((FStar_Util.smap_remove sm' k);
(

let se1 = (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_declare_typ (l, u, t) -> begin
(

let uu___136_12407 = se
in {FStar_Syntax_Syntax.sigel = uu___136_12407.FStar_Syntax_Syntax.sigel; FStar_Syntax_Syntax.sigrng = uu___136_12407.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Assumption)::se.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___136_12407.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___136_12407.FStar_Syntax_Syntax.sigattrs})
end
| uu____12408 -> begin
se
end)
in (FStar_Util.smap_add sm' k ((se1), (false))));
)
end
| uu____12413 -> begin
()
end)))));
env1;
)))))))


let finish_module_or_interface : env  ->  FStar_Syntax_Syntax.modul  ->  (env * FStar_Syntax_Syntax.modul) = (fun env modul -> (

let modul1 = (match ((not (modul.FStar_Syntax_Syntax.is_interface))) with
| true -> begin
(check_admits env modul)
end
| uu____12435 -> begin
modul
end)
in (

let uu____12436 = (finish env modul1)
in ((uu____12436), (modul1)))))

type exported_ids =
{exported_id_terms : Prims.string Prims.list; exported_id_fields : Prims.string Prims.list}


let __proj__Mkexported_ids__item__exported_id_terms : exported_ids  ->  Prims.string Prims.list = (fun projectee -> (match (projectee) with
| {exported_id_terms = __fname__exported_id_terms; exported_id_fields = __fname__exported_id_fields} -> begin
__fname__exported_id_terms
end))


let __proj__Mkexported_ids__item__exported_id_fields : exported_ids  ->  Prims.string Prims.list = (fun projectee -> (match (projectee) with
| {exported_id_terms = __fname__exported_id_terms; exported_id_fields = __fname__exported_id_fields} -> begin
__fname__exported_id_fields
end))


let as_exported_ids : exported_id_set  ->  exported_ids = (fun e -> (

let terms = (

let uu____12524 = (

let uu____12527 = (e Exported_id_term_type)
in (FStar_ST.op_Bang uu____12527))
in (FStar_Util.set_elements uu____12524))
in (

let fields = (

let uu____12649 = (

let uu____12652 = (e Exported_id_field)
in (FStar_ST.op_Bang uu____12652))
in (FStar_Util.set_elements uu____12649))
in {exported_id_terms = terms; exported_id_fields = fields})))


let as_exported_id_set : exported_ids FStar_Pervasives_Native.option  ->  exported_id_kind  ->  Prims.string FStar_Util.set FStar_ST.ref = (fun e -> (match (e) with
| FStar_Pervasives_Native.None -> begin
(exported_id_set_new ())
end
| FStar_Pervasives_Native.Some (e1) -> begin
(

let terms = (

let uu____12811 = (FStar_Util.as_set e1.exported_id_terms FStar_Util.compare)
in (FStar_Util.mk_ref uu____12811))
in (

let fields = (

let uu____12821 = (FStar_Util.as_set e1.exported_id_fields FStar_Util.compare)
in (FStar_Util.mk_ref uu____12821))
in (fun uu___111_12826 -> (match (uu___111_12826) with
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
| {mii_exported_ids = __fname__mii_exported_ids; mii_trans_exported_ids = __fname__mii_trans_exported_ids; mii_includes = __fname__mii_includes} -> begin
__fname__mii_exported_ids
end))


let __proj__Mkmodule_inclusion_info__item__mii_trans_exported_ids : module_inclusion_info  ->  exported_ids FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {mii_exported_ids = __fname__mii_exported_ids; mii_trans_exported_ids = __fname__mii_trans_exported_ids; mii_includes = __fname__mii_includes} -> begin
__fname__mii_trans_exported_ids
end))


let __proj__Mkmodule_inclusion_info__item__mii_includes : module_inclusion_info  ->  FStar_Ident.lident Prims.list FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {mii_exported_ids = __fname__mii_exported_ids; mii_trans_exported_ids = __fname__mii_trans_exported_ids; mii_includes = __fname__mii_includes} -> begin
__fname__mii_includes
end))


let default_mii : module_inclusion_info = {mii_exported_ids = FStar_Pervasives_Native.None; mii_trans_exported_ids = FStar_Pervasives_Native.None; mii_includes = FStar_Pervasives_Native.None}


let as_includes : 'Auu____12957 . 'Auu____12957 Prims.list FStar_Pervasives_Native.option  ->  'Auu____12957 Prims.list FStar_ST.ref = (fun uu___112_12970 -> (match (uu___112_12970) with
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

let uu____13011 = (FStar_Util.smap_try_find m mname)
in (FStar_Util.map_opt uu____13011 as_exported_ids)))
in (

let uu____13017 = (as_ids_opt env.exported_ids)
in (

let uu____13020 = (as_ids_opt env.trans_exported_ids)
in (

let uu____13023 = (

let uu____13028 = (FStar_Util.smap_try_find env.includes mname)
in (FStar_Util.map_opt uu____13028 (fun r -> (FStar_ST.op_Bang r))))
in {mii_exported_ids = uu____13017; mii_trans_exported_ids = uu____13020; mii_includes = uu____13023}))))))


let prepare_module_or_interface : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  module_inclusion_info  ->  (env * Prims.bool) = (fun intf admitted env mname mii -> (

let prep = (fun env1 -> (

let filename = (

let uu____13147 = (FStar_Ident.text_of_lid mname)
in (FStar_Util.strcat uu____13147 ".fst"))
in (

let auto_open = (FStar_Parser_Dep.hard_coded_dependencies filename)
in (

let auto_open1 = (

let convert_kind = (fun uu___113_13167 -> (match (uu___113_13167) with
| FStar_Parser_Dep.Open_namespace -> begin
Open_namespace
end
| FStar_Parser_Dep.Open_module -> begin
Open_module
end))
in (FStar_List.map (fun uu____13179 -> (match (uu____13179) with
| (lid, kind) -> begin
((lid), ((convert_kind kind)))
end)) auto_open))
in (

let namespace_of_module = (match (((FStar_List.length mname.FStar_Ident.ns) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____13203 = (

let uu____13208 = (FStar_Ident.lid_of_ids mname.FStar_Ident.ns)
in ((uu____13208), (Open_namespace)))
in (uu____13203)::[])
end
| uu____13217 -> begin
[]
end)
in (

let auto_open2 = (FStar_List.append namespace_of_module (FStar_List.rev auto_open1))
in ((

let uu____13238 = (as_exported_id_set mii.mii_exported_ids)
in (FStar_Util.smap_add env1.exported_ids mname.FStar_Ident.str uu____13238));
(match (()) with
| () -> begin
((

let uu____13265 = (as_exported_id_set mii.mii_trans_exported_ids)
in (FStar_Util.smap_add env1.trans_exported_ids mname.FStar_Ident.str uu____13265));
(match (()) with
| () -> begin
((

let uu____13292 = (as_includes mii.mii_includes)
in (FStar_Util.smap_add env1.includes mname.FStar_Ident.str uu____13292));
(match (()) with
| () -> begin
(

let env' = (

let uu___137_13324 = env1
in (

let uu____13325 = (FStar_List.map (fun x -> Open_module_or_namespace (x)) auto_open2)
in {curmodule = FStar_Pervasives_Native.Some (mname); curmonad = uu___137_13324.curmonad; modules = uu___137_13324.modules; scope_mods = uu____13325; exported_ids = uu___137_13324.exported_ids; trans_exported_ids = uu___137_13324.trans_exported_ids; includes = uu___137_13324.includes; sigaccum = uu___137_13324.sigaccum; sigmap = env1.sigmap; iface = intf; admitted_iface = admitted; expect_typ = uu___137_13324.expect_typ; docs = uu___137_13324.docs; remaining_iface_decls = uu___137_13324.remaining_iface_decls; syntax_only = uu___137_13324.syntax_only; ds_hooks = uu___137_13324.ds_hooks}))
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

let uu____13337 = (FStar_All.pipe_right env.modules (FStar_Util.find_opt (fun uu____13363 -> (match (uu____13363) with
| (l, uu____13369) -> begin
(FStar_Ident.lid_equals l mname)
end))))
in (match (uu____13337) with
| FStar_Pervasives_Native.None -> begin
(

let uu____13378 = (prep env)
in ((uu____13378), (false)))
end
| FStar_Pervasives_Native.Some (uu____13379, m) -> begin
((

let uu____13386 = ((

let uu____13389 = (FStar_Options.interactive ())
in (not (uu____13389))) && ((not (m.FStar_Syntax_Syntax.is_interface)) || intf))
in (match (uu____13386) with
| true -> begin
(

let uu____13390 = (

let uu____13395 = (FStar_Util.format1 "Duplicate module or interface name: %s" mname.FStar_Ident.str)
in ((FStar_Errors.Fatal_DuplicateModuleOrInterface), (uu____13395)))
in (

let uu____13396 = (FStar_Ident.range_of_lid mname)
in (FStar_Errors.raise_error uu____13390 uu____13396)))
end
| uu____13397 -> begin
()
end));
(

let uu____13398 = (

let uu____13399 = (push env)
in (prep uu____13399))
in ((uu____13398), (true)));
)
end))))


let enter_monad_scope : env  ->  FStar_Ident.ident  ->  env = (fun env mname -> (match (env.curmonad) with
| FStar_Pervasives_Native.Some (mname') -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_MonadAlreadyDefined), ((Prims.strcat "Trying to define monad " (Prims.strcat mname.FStar_Ident.idText (Prims.strcat ", but already in monad scope " mname'.FStar_Ident.idText))))) mname.FStar_Ident.idRange)
end
| FStar_Pervasives_Native.None -> begin
(

let uu___138_13411 = env
in {curmodule = uu___138_13411.curmodule; curmonad = FStar_Pervasives_Native.Some (mname); modules = uu___138_13411.modules; scope_mods = uu___138_13411.scope_mods; exported_ids = uu___138_13411.exported_ids; trans_exported_ids = uu___138_13411.trans_exported_ids; includes = uu___138_13411.includes; sigaccum = uu___138_13411.sigaccum; sigmap = uu___138_13411.sigmap; iface = uu___138_13411.iface; admitted_iface = uu___138_13411.admitted_iface; expect_typ = uu___138_13411.expect_typ; docs = uu___138_13411.docs; remaining_iface_decls = uu___138_13411.remaining_iface_decls; syntax_only = uu___138_13411.syntax_only; ds_hooks = uu___138_13411.ds_hooks})
end))


let fail_or : 'a . env  ->  (FStar_Ident.lident  ->  'a FStar_Pervasives_Native.option)  ->  FStar_Ident.lident  ->  'a = (fun env lookup1 lid -> (

let uu____13445 = (lookup1 lid)
in (match (uu____13445) with
| FStar_Pervasives_Native.None -> begin
(

let opened_modules = (FStar_List.map (fun uu____13458 -> (match (uu____13458) with
| (lid1, uu____13464) -> begin
(FStar_Ident.text_of_lid lid1)
end)) env.modules)
in (

let msg = (

let uu____13466 = (FStar_Ident.text_of_lid lid)
in (FStar_Util.format1 "Identifier not found: [%s]" uu____13466))
in (

let msg1 = (match ((Prims.op_Equality (FStar_List.length lid.FStar_Ident.ns) (Prims.parse_int "0"))) with
| true -> begin
msg
end
| uu____13468 -> begin
(

let modul = (

let uu____13470 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in (

let uu____13471 = (FStar_Ident.range_of_lid lid)
in (FStar_Ident.set_lid_range uu____13470 uu____13471)))
in (

let uu____13472 = (resolve_module_name env modul true)
in (match (uu____13472) with
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

let uu____13481 = (FStar_Ident.range_of_lid lid)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_IdentifierNotFound), (msg1)) uu____13481)))))
end
| FStar_Pervasives_Native.Some (r) -> begin
r
end)))


let fail_or2 : 'a . (FStar_Ident.ident  ->  'a FStar_Pervasives_Native.option)  ->  FStar_Ident.ident  ->  'a = (fun lookup1 id1 -> (

let uu____13509 = (lookup1 id1)
in (match (uu____13509) with
| FStar_Pervasives_Native.None -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_IdentifierNotFound), ((Prims.strcat "Identifier not found [" (Prims.strcat id1.FStar_Ident.idText "]")))) id1.FStar_Ident.idRange)
end
| FStar_Pervasives_Native.Some (r) -> begin
r
end)))


let mk_copy : env  ->  env = (fun en -> (

let uu___139_13518 = en
in (

let uu____13519 = (FStar_Util.smap_copy en.exported_ids)
in (

let uu____13524 = (FStar_Util.smap_copy en.trans_exported_ids)
in (

let uu____13529 = (FStar_Util.smap_copy en.sigmap)
in (

let uu____13540 = (FStar_Util.smap_copy en.docs)
in {curmodule = uu___139_13518.curmodule; curmonad = uu___139_13518.curmonad; modules = uu___139_13518.modules; scope_mods = uu___139_13518.scope_mods; exported_ids = uu____13519; trans_exported_ids = uu____13524; includes = uu___139_13518.includes; sigaccum = uu___139_13518.sigaccum; sigmap = uu____13529; iface = uu___139_13518.iface; admitted_iface = uu___139_13518.admitted_iface; expect_typ = uu___139_13518.expect_typ; docs = uu____13540; remaining_iface_decls = uu___139_13518.remaining_iface_decls; syntax_only = uu___139_13518.syntax_only; ds_hooks = uu___139_13518.ds_hooks}))))))




