
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

let uu____1912 = (exported_id_set Exported_id_term_type)
in (FStar_ST.op_Bang uu____1912))
in (FStar_All.pipe_right uu____1909 FStar_Util.set_elements))
end))))


let open_modules : env  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.modul) Prims.list = (fun e -> e.modules)


let open_modules_and_namespaces : env  ->  FStar_Ident.lident Prims.list = (fun env -> (FStar_List.filter_map (fun uu___82_2056 -> (match (uu___82_2056) with
| Open_module_or_namespace (lid, _info) -> begin
FStar_Pervasives_Native.Some (lid)
end
| uu____2061 -> begin
FStar_Pervasives_Native.None
end)) env.scope_mods))


let set_current_module : env  ->  FStar_Ident.lident  ->  env = (fun e l -> (

let uu___117_2072 = e
in {curmodule = FStar_Pervasives_Native.Some (l); curmonad = uu___117_2072.curmonad; modules = uu___117_2072.modules; scope_mods = uu___117_2072.scope_mods; exported_ids = uu___117_2072.exported_ids; trans_exported_ids = uu___117_2072.trans_exported_ids; includes = uu___117_2072.includes; sigaccum = uu___117_2072.sigaccum; sigmap = uu___117_2072.sigmap; iface = uu___117_2072.iface; admitted_iface = uu___117_2072.admitted_iface; expect_typ = uu___117_2072.expect_typ; docs = uu___117_2072.docs; remaining_iface_decls = uu___117_2072.remaining_iface_decls; syntax_only = uu___117_2072.syntax_only; ds_hooks = uu___117_2072.ds_hooks}))


let current_module : env  ->  FStar_Ident.lident = (fun env -> (match (env.curmodule) with
| FStar_Pervasives_Native.None -> begin
(failwith "Unset current module")
end
| FStar_Pervasives_Native.Some (m) -> begin
m
end))


let iface_decls : env  ->  FStar_Ident.lident  ->  FStar_Parser_AST.decl Prims.list FStar_Pervasives_Native.option = (fun env l -> (

let uu____2093 = (FStar_All.pipe_right env.remaining_iface_decls (FStar_List.tryFind (fun uu____2127 -> (match (uu____2127) with
| (m, uu____2135) -> begin
(FStar_Ident.lid_equals l m)
end))))
in (match (uu____2093) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (uu____2152, decls) -> begin
FStar_Pervasives_Native.Some (decls)
end)))


let set_iface_decls : env  ->  FStar_Ident.lident  ->  FStar_Parser_AST.decl Prims.list  ->  env = (fun env l ds -> (

let uu____2185 = (FStar_List.partition (fun uu____2215 -> (match (uu____2215) with
| (m, uu____2223) -> begin
(FStar_Ident.lid_equals l m)
end)) env.remaining_iface_decls)
in (match (uu____2185) with
| (uu____2228, rest) -> begin
(

let uu___118_2262 = env
in {curmodule = uu___118_2262.curmodule; curmonad = uu___118_2262.curmonad; modules = uu___118_2262.modules; scope_mods = uu___118_2262.scope_mods; exported_ids = uu___118_2262.exported_ids; trans_exported_ids = uu___118_2262.trans_exported_ids; includes = uu___118_2262.includes; sigaccum = uu___118_2262.sigaccum; sigmap = uu___118_2262.sigmap; iface = uu___118_2262.iface; admitted_iface = uu___118_2262.admitted_iface; expect_typ = uu___118_2262.expect_typ; docs = uu___118_2262.docs; remaining_iface_decls = (((l), (ds)))::rest; syntax_only = uu___118_2262.syntax_only; ds_hooks = uu___118_2262.ds_hooks})
end)))


let qual : FStar_Ident.lident  ->  FStar_Ident.ident  ->  FStar_Ident.lident = FStar_Syntax_Util.qual_id


let qualify : env  ->  FStar_Ident.ident  ->  FStar_Ident.lident = (fun env id1 -> (match (env.curmonad) with
| FStar_Pervasives_Native.None -> begin
(

let uu____2289 = (current_module env)
in (qual uu____2289 id1))
end
| FStar_Pervasives_Native.Some (monad) -> begin
(

let uu____2291 = (

let uu____2292 = (current_module env)
in (qual uu____2292 monad))
in (FStar_Syntax_Util.mk_field_projector_name_from_ident uu____2291 id1))
end))


let syntax_only : env  ->  Prims.bool = (fun env -> env.syntax_only)


let set_syntax_only : env  ->  Prims.bool  ->  env = (fun env b -> (

let uu___119_2308 = env
in {curmodule = uu___119_2308.curmodule; curmonad = uu___119_2308.curmonad; modules = uu___119_2308.modules; scope_mods = uu___119_2308.scope_mods; exported_ids = uu___119_2308.exported_ids; trans_exported_ids = uu___119_2308.trans_exported_ids; includes = uu___119_2308.includes; sigaccum = uu___119_2308.sigaccum; sigmap = uu___119_2308.sigmap; iface = uu___119_2308.iface; admitted_iface = uu___119_2308.admitted_iface; expect_typ = uu___119_2308.expect_typ; docs = uu___119_2308.docs; remaining_iface_decls = uu___119_2308.remaining_iface_decls; syntax_only = b; ds_hooks = uu___119_2308.ds_hooks}))


let ds_hooks : env  ->  dsenv_hooks = (fun env -> env.ds_hooks)


let set_ds_hooks : env  ->  dsenv_hooks  ->  env = (fun env hooks -> (

let uu___120_2324 = env
in {curmodule = uu___120_2324.curmodule; curmonad = uu___120_2324.curmonad; modules = uu___120_2324.modules; scope_mods = uu___120_2324.scope_mods; exported_ids = uu___120_2324.exported_ids; trans_exported_ids = uu___120_2324.trans_exported_ids; includes = uu___120_2324.includes; sigaccum = uu___120_2324.sigaccum; sigmap = uu___120_2324.sigmap; iface = uu___120_2324.iface; admitted_iface = uu___120_2324.admitted_iface; expect_typ = uu___120_2324.expect_typ; docs = uu___120_2324.docs; remaining_iface_decls = uu___120_2324.remaining_iface_decls; syntax_only = uu___120_2324.syntax_only; ds_hooks = hooks}))


let new_sigmap : 'Auu____2329 . unit  ->  'Auu____2329 FStar_Util.smap = (fun uu____2336 -> (FStar_Util.smap_create (Prims.parse_int "100")))


let empty_env : unit  ->  env = (fun uu____2341 -> (

let uu____2342 = (new_sigmap ())
in (

let uu____2347 = (new_sigmap ())
in (

let uu____2352 = (new_sigmap ())
in (

let uu____2363 = (new_sigmap ())
in (

let uu____2374 = (new_sigmap ())
in {curmodule = FStar_Pervasives_Native.None; curmonad = FStar_Pervasives_Native.None; modules = []; scope_mods = []; exported_ids = uu____2342; trans_exported_ids = uu____2347; includes = uu____2352; sigaccum = []; sigmap = uu____2363; iface = false; admitted_iface = false; expect_typ = false; docs = uu____2374; remaining_iface_decls = []; syntax_only = false; ds_hooks = default_ds_hooks}))))))


let sigmap : env  ->  (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap = (fun env -> env.sigmap)


let has_all_in_scope : env  ->  Prims.bool = (fun env -> (FStar_List.existsb (fun uu____2410 -> (match (uu____2410) with
| (m, uu____2416) -> begin
(FStar_Ident.lid_equals m FStar_Parser_Const.all_lid)
end)) env.modules))


let set_bv_range : FStar_Syntax_Syntax.bv  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.bv = (fun bv r -> (

let id1 = (

let uu___121_2428 = bv.FStar_Syntax_Syntax.ppname
in {FStar_Ident.idText = uu___121_2428.FStar_Ident.idText; FStar_Ident.idRange = r})
in (

let uu___122_2429 = bv
in {FStar_Syntax_Syntax.ppname = id1; FStar_Syntax_Syntax.index = uu___122_2429.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu___122_2429.FStar_Syntax_Syntax.sort})))


let bv_to_name : FStar_Syntax_Syntax.bv  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.term = (fun bv r -> (FStar_Syntax_Syntax.bv_to_name (set_bv_range bv r)))


let unmangleMap : (Prims.string * Prims.string * FStar_Syntax_Syntax.delta_depth * FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option) Prims.list = ((("op_ColonColon"), ("Cons"), (FStar_Syntax_Syntax.Delta_constant), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor))))::((("not"), ("op_Negation"), (FStar_Syntax_Syntax.Delta_equational), (FStar_Pervasives_Native.None)))::[]


let unmangleOpName : FStar_Ident.ident  ->  (FStar_Syntax_Syntax.term * Prims.bool) FStar_Pervasives_Native.option = (fun id1 -> (

let t = (FStar_Util.find_map unmangleMap (fun uu____2522 -> (match (uu____2522) with
| (x, y, dd, dq) -> begin
(match ((Prims.op_Equality id1.FStar_Ident.idText x)) with
| true -> begin
(

let uu____2545 = (

let uu____2546 = (FStar_Ident.lid_of_path (("Prims")::(y)::[]) id1.FStar_Ident.idRange)
in (FStar_Syntax_Syntax.fvar uu____2546 dd dq))
in FStar_Pervasives_Native.Some (uu____2545))
end
| uu____2547 -> begin
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
| uu____2593 -> begin
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
| uu____2626 -> begin
false
end))


let uu___is_Cont_ignore : 'a . 'a cont_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Cont_ignore -> begin
true
end
| uu____2643 -> begin
false
end))


let option_of_cont : 'a . (unit  ->  'a FStar_Pervasives_Native.option)  ->  'a cont_t  ->  'a FStar_Pervasives_Native.option = (fun k_ignore uu___83_2671 -> (match (uu___83_2671) with
| Cont_ok (a) -> begin
FStar_Pervasives_Native.Some (a)
end
| Cont_fail -> begin
FStar_Pervasives_Native.None
end
| Cont_ignore -> begin
(k_ignore ())
end))


let find_in_record : 'Auu____2689 . FStar_Ident.ident Prims.list  ->  FStar_Ident.ident  ->  record_or_dc  ->  (record_or_dc  ->  'Auu____2689 cont_t)  ->  'Auu____2689 cont_t = (fun ns id1 record cont -> (

let typename' = (FStar_Ident.lid_of_ids (FStar_List.append ns ((record.typename.FStar_Ident.ident)::[])))
in (

let uu____2726 = (FStar_Ident.lid_equals typename' record.typename)
in (match (uu____2726) with
| true -> begin
(

let fname = (FStar_Ident.lid_of_ids (FStar_List.append record.typename.FStar_Ident.ns ((id1)::[])))
in (

let find1 = (FStar_Util.find_map record.fields (fun uu____2740 -> (match (uu____2740) with
| (f, uu____2748) -> begin
(match ((Prims.op_Equality id1.FStar_Ident.idText f.FStar_Ident.idText)) with
| true -> begin
FStar_Pervasives_Native.Some (record)
end
| uu____2751 -> begin
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
| uu____2755 -> begin
Cont_ignore
end))))


let get_exported_id_set : env  ->  Prims.string  ->  (exported_id_kind  ->  string_set FStar_ST.ref) FStar_Pervasives_Native.option = (fun e mname -> (FStar_Util.smap_try_find e.exported_ids mname))


let get_trans_exported_id_set : env  ->  Prims.string  ->  (exported_id_kind  ->  string_set FStar_ST.ref) FStar_Pervasives_Native.option = (fun e mname -> (FStar_Util.smap_try_find e.trans_exported_ids mname))


let string_of_exported_id_kind : exported_id_kind  ->  Prims.string = (fun uu___84_2810 -> (match (uu___84_2810) with
| Exported_id_field -> begin
"field"
end
| Exported_id_term_type -> begin
"term/type"
end))


let find_in_module_with_includes : 'a . exported_id_kind  ->  (FStar_Ident.lident  ->  'a cont_t)  ->  'a cont_t  ->  env  ->  FStar_Ident.lident  ->  FStar_Ident.ident  ->  'a cont_t = (fun eikind find_in_module find_in_module_default env ns id1 -> (

let idstr = id1.FStar_Ident.idText
in (

let rec aux = (fun uu___85_2881 -> (match (uu___85_2881) with
| [] -> begin
find_in_module_default
end
| (modul)::q -> begin
(

let mname = modul.FStar_Ident.str
in (

let not_shadowed = (

let uu____2892 = (get_exported_id_set env mname)
in (match (uu____2892) with
| FStar_Pervasives_Native.None -> begin
true
end
| FStar_Pervasives_Native.Some (mex) -> begin
(

let mexports = (

let uu____2917 = (mex eikind)
in (FStar_ST.op_Bang uu____2917))
in (FStar_Util.set_mem idstr mexports))
end))
in (

let mincludes = (

let uu____3039 = (FStar_Util.smap_try_find env.includes mname)
in (match (uu____3039) with
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

let uu____3119 = (qual modul id1)
in (find_in_module uu____3119))
end
| uu____3120 -> begin
Cont_ignore
end)
in (match (look_into) with
| Cont_ignore -> begin
(aux (FStar_List.append mincludes q))
end
| uu____3123 -> begin
look_into
end)))))
end))
in (aux ((ns)::[])))))


let is_exported_id_field : exported_id_kind  ->  Prims.bool = (fun uu___86_3130 -> (match (uu___86_3130) with
| Exported_id_field -> begin
true
end
| uu____3131 -> begin
false
end))


let try_lookup_id'' : 'a . env  ->  FStar_Ident.ident  ->  exported_id_kind  ->  (local_binding  ->  'a cont_t)  ->  (rec_binding  ->  'a cont_t)  ->  (record_or_dc  ->  'a cont_t)  ->  (FStar_Ident.lident  ->  'a cont_t)  ->  ('a cont_t  ->  FStar_Ident.ident  ->  'a cont_t)  ->  'a FStar_Pervasives_Native.option = (fun env id1 eikind k_local_binding k_rec_binding k_record find_in_module lookup_default_id -> (

let check_local_binding_id = (fun uu___87_3252 -> (match (uu___87_3252) with
| (id', uu____3254, uu____3255) -> begin
(Prims.op_Equality id'.FStar_Ident.idText id1.FStar_Ident.idText)
end))
in (

let check_rec_binding_id = (fun uu___88_3261 -> (match (uu___88_3261) with
| (id', uu____3263, uu____3264) -> begin
(Prims.op_Equality id'.FStar_Ident.idText id1.FStar_Ident.idText)
end))
in (

let curmod_ns = (

let uu____3268 = (current_module env)
in (FStar_Ident.ids_of_lid uu____3268))
in (

let proc = (fun uu___89_3276 -> (match (uu___89_3276) with
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

let uu____3284 = (FStar_Ident.lid_of_ids curmod_ns)
in (find_in_module_with_includes Exported_id_field (fun lid -> (

let id2 = lid.FStar_Ident.ident
in (find_in_record lid.FStar_Ident.ns id2 r k_record))) Cont_ignore env uu____3284 id1))
end
| uu____3289 -> begin
Cont_ignore
end))
in (

let rec aux = (fun uu___90_3299 -> (match (uu___90_3299) with
| (a)::q -> begin
(

let uu____3308 = (proc a)
in (option_of_cont (fun uu____3312 -> (aux q)) uu____3308))
end
| [] -> begin
(

let uu____3313 = (lookup_default_id Cont_fail id1)
in (option_of_cont (fun uu____3317 -> FStar_Pervasives_Native.None) uu____3313))
end))
in (aux env.scope_mods)))))))


let found_local_binding : 'Auu____3326 'Auu____3327 . FStar_Range.range  ->  ('Auu____3326 * FStar_Syntax_Syntax.bv * 'Auu____3327)  ->  (FStar_Syntax_Syntax.term * 'Auu____3327) = (fun r uu____3347 -> (match (uu____3347) with
| (id', x, mut) -> begin
(

let uu____3357 = (bv_to_name x r)
in ((uu____3357), (mut)))
end))


let find_in_module : 'Auu____3368 . env  ->  FStar_Ident.lident  ->  (FStar_Ident.lident  ->  (FStar_Syntax_Syntax.sigelt * Prims.bool)  ->  'Auu____3368)  ->  'Auu____3368  ->  'Auu____3368 = (fun env lid k_global_def k_not_found -> (

let uu____3407 = (FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str)
in (match (uu____3407) with
| FStar_Pervasives_Native.Some (sb) -> begin
(k_global_def lid sb)
end
| FStar_Pervasives_Native.None -> begin
k_not_found
end)))


let try_lookup_id : env  ->  FStar_Ident.ident  ->  (FStar_Syntax_Syntax.term * Prims.bool) FStar_Pervasives_Native.option = (fun env id1 -> (

let uu____3447 = (unmangleOpName id1)
in (match (uu____3447) with
| FStar_Pervasives_Native.Some (f) -> begin
FStar_Pervasives_Native.Some (f)
end
| uu____3473 -> begin
(try_lookup_id'' env id1 Exported_id_term_type (fun r -> (

let uu____3487 = (found_local_binding id1.FStar_Ident.idRange r)
in Cont_ok (uu____3487))) (fun uu____3497 -> Cont_fail) (fun uu____3503 -> Cont_ignore) (fun i -> (find_in_module env i (fun uu____3518 uu____3519 -> Cont_fail) Cont_ignore)) (fun uu____3534 uu____3535 -> Cont_fail))
end)))


let lookup_default_id : 'a . env  ->  FStar_Ident.ident  ->  (FStar_Ident.lident  ->  (FStar_Syntax_Syntax.sigelt * Prims.bool)  ->  'a cont_t)  ->  'a cont_t  ->  'a cont_t = (fun env id1 k_global_def k_not_found -> (

let find_in_monad = (match (env.curmonad) with
| FStar_Pervasives_Native.Some (uu____3614) -> begin
(

let lid = (qualify env id1)
in (

let uu____3616 = (FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str)
in (match (uu____3616) with
| FStar_Pervasives_Native.Some (r) -> begin
(

let uu____3640 = (k_global_def lid r)
in FStar_Pervasives_Native.Some (uu____3640))
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

let uu____3663 = (current_module env)
in (qual uu____3663 id1))
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

let rec aux = (fun uu___91_3726 -> (match (uu___91_3726) with
| [] -> begin
(

let uu____3731 = (module_is_defined env lid)
in (match (uu____3731) with
| true -> begin
FStar_Pervasives_Native.Some (lid)
end
| uu____3734 -> begin
FStar_Pervasives_Native.None
end))
end
| (Open_module_or_namespace (ns, Open_namespace))::q when honor_ns -> begin
(

let new_lid = (

let uu____3740 = (

let uu____3741 = (FStar_Ident.path_of_lid ns)
in (

let uu____3744 = (FStar_Ident.path_of_lid lid)
in (FStar_List.append uu____3741 uu____3744)))
in (

let uu____3747 = (FStar_Ident.range_of_lid lid)
in (FStar_Ident.lid_of_path uu____3740 uu____3747)))
in (

let uu____3748 = (module_is_defined env new_lid)
in (match (uu____3748) with
| true -> begin
FStar_Pervasives_Native.Some (new_lid)
end
| uu____3751 -> begin
(aux q)
end)))
end
| (Module_abbrev (name, modul))::uu____3754 when ((Prims.op_Equality nslen (Prims.parse_int "0")) && (Prims.op_Equality name.FStar_Ident.idText lid.FStar_Ident.ident.FStar_Ident.idText)) -> begin
FStar_Pervasives_Native.Some (modul)
end
| (uu____3762)::q -> begin
(aux q)
end))
in (aux env.scope_mods))))


let fail_if_curmodule : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  unit = (fun env ns_original ns_resolved -> (

let uu____3781 = (

let uu____3782 = (current_module env)
in (FStar_Ident.lid_equals ns_resolved uu____3782))
in (match (uu____3781) with
| true -> begin
(

let uu____3783 = (FStar_Ident.lid_equals ns_resolved FStar_Parser_Const.prims_lid)
in (match (uu____3783) with
| true -> begin
()
end
| uu____3784 -> begin
(

let uu____3785 = (

let uu____3790 = (FStar_Util.format1 "Reference %s to current module is forbidden (see GitHub issue #451)" ns_original.FStar_Ident.str)
in ((FStar_Errors.Fatal_ForbiddenReferenceToCurrentModule), (uu____3790)))
in (

let uu____3791 = (FStar_Ident.range_of_lid ns_original)
in (FStar_Errors.raise_error uu____3785 uu____3791)))
end))
end
| uu____3792 -> begin
()
end)))


let fail_if_qualified_by_curmodule : env  ->  FStar_Ident.lident  ->  unit = (fun env lid -> (match (lid.FStar_Ident.ns) with
| [] -> begin
()
end
| uu____3803 -> begin
(

let modul_orig = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in (

let uu____3807 = (resolve_module_name env modul_orig true)
in (match (uu____3807) with
| FStar_Pervasives_Native.Some (modul_res) -> begin
(fail_if_curmodule env modul_orig modul_res)
end
| uu____3811 -> begin
()
end)))
end))


let is_open : env  ->  FStar_Ident.lident  ->  open_kind  ->  Prims.bool = (fun env lid open_kind -> (FStar_List.existsb (fun uu___92_3832 -> (match (uu___92_3832) with
| Open_module_or_namespace (ns, k) -> begin
((Prims.op_Equality k open_kind) && (FStar_Ident.lid_equals lid ns))
end
| uu____3835 -> begin
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
| uu____3931 -> begin
(match (revns) with
| [] -> begin
FStar_Pervasives_Native.None
end
| (ns_last_id)::rev_ns_prefix -> begin
(

let uu____3954 = (aux rev_ns_prefix ns_last_id)
in (FStar_All.pipe_right uu____3954 (FStar_Util.map_option (fun uu____4004 -> (match (uu____4004) with
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

let uu____4074 = (aux ns_rev_prefix ns_last_id)
in (match (uu____4074) with
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

let uu____4135 = (

let uu____4138 = (FStar_Ident.lid_of_ids ids)
in (resolve_module_name env uu____4138 true))
in (match (uu____4135) with
| FStar_Pervasives_Native.Some (m) when (module_is_open env m) -> begin
((ids), ([]))
end
| uu____4152 -> begin
(do_shorten env ids)
end))
end
| uu____4155 -> begin
(do_shorten env ids)
end))))


let resolve_in_open_namespaces'' : 'a . env  ->  FStar_Ident.lident  ->  exported_id_kind  ->  (local_binding  ->  'a cont_t)  ->  (rec_binding  ->  'a cont_t)  ->  (record_or_dc  ->  'a cont_t)  ->  (FStar_Ident.lident  ->  'a cont_t)  ->  ('a cont_t  ->  FStar_Ident.ident  ->  'a cont_t)  ->  'a FStar_Pervasives_Native.option = (fun env lid eikind k_local_binding k_rec_binding k_record f_module l_default -> (match (lid.FStar_Ident.ns) with
| (uu____4271)::uu____4272 -> begin
(

let uu____4275 = (

let uu____4278 = (

let uu____4279 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in (

let uu____4280 = (FStar_Ident.range_of_lid lid)
in (FStar_Ident.set_lid_range uu____4279 uu____4280)))
in (resolve_module_name env uu____4278 true))
in (match (uu____4275) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (modul) -> begin
(

let uu____4284 = (find_in_module_with_includes eikind f_module Cont_fail env modul lid.FStar_Ident.ident)
in (option_of_cont (fun uu____4288 -> FStar_Pervasives_Native.None) uu____4284))
end))
end
| [] -> begin
(try_lookup_id'' env lid.FStar_Ident.ident eikind k_local_binding k_rec_binding k_record f_module l_default)
end))


let cont_of_option : 'a . 'a cont_t  ->  'a FStar_Pervasives_Native.option  ->  'a cont_t = (fun k_none uu___93_4311 -> (match (uu___93_4311) with
| FStar_Pervasives_Native.Some (v1) -> begin
Cont_ok (v1)
end
| FStar_Pervasives_Native.None -> begin
k_none
end))


let resolve_in_open_namespaces' : 'a . env  ->  FStar_Ident.lident  ->  (local_binding  ->  'a FStar_Pervasives_Native.option)  ->  (rec_binding  ->  'a FStar_Pervasives_Native.option)  ->  (FStar_Ident.lident  ->  (FStar_Syntax_Syntax.sigelt * Prims.bool)  ->  'a FStar_Pervasives_Native.option)  ->  'a FStar_Pervasives_Native.option = (fun env lid k_local_binding k_rec_binding k_global_def -> (

let k_global_def' = (fun k lid1 def -> (

let uu____4427 = (k_global_def lid1 def)
in (cont_of_option k uu____4427)))
in (

let f_module = (fun lid' -> (

let k = Cont_ignore
in (find_in_module env lid' (k_global_def' k) k)))
in (

let l_default = (fun k i -> (lookup_default_id env i (k_global_def' k) k))
in (resolve_in_open_namespaces'' env lid Exported_id_term_type (fun l -> (

let uu____4463 = (k_local_binding l)
in (cont_of_option Cont_fail uu____4463))) (fun r -> (

let uu____4469 = (k_rec_binding r)
in (cont_of_option Cont_fail uu____4469))) (fun uu____4473 -> Cont_ignore) f_module l_default)))))


let fv_qual_of_se : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option = (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (uu____4483, uu____4484, uu____4485, l, uu____4487, uu____4488) -> begin
(

let qopt = (FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals (fun uu___94_4499 -> (match (uu___94_4499) with
| FStar_Syntax_Syntax.RecordConstructor (uu____4502, fs) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (((l), (fs))))
end
| uu____4514 -> begin
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
| FStar_Syntax_Syntax.Sig_declare_typ (uu____4520, uu____4521, uu____4522) -> begin
FStar_Pervasives_Native.None
end
| uu____4523 -> begin
FStar_Pervasives_Native.None
end))


let lb_fv : FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.fv = (fun lbs lid -> (

let uu____4538 = (FStar_Util.find_map lbs (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let uu____4546 = (FStar_Syntax_Syntax.fv_eq_lid fv lid)
in (match (uu____4546) with
| true -> begin
FStar_Pervasives_Native.Some (fv)
end
| uu____4549 -> begin
FStar_Pervasives_Native.None
end)))))
in (FStar_All.pipe_right uu____4538 FStar_Util.must)))


let ns_of_lid_equals : FStar_Ident.lident  ->  FStar_Ident.lident  ->  Prims.bool = (fun lid ns -> ((

let uu____4564 = (

let uu____4565 = (FStar_Ident.ids_of_lid ns)
in (FStar_List.length uu____4565))
in (Prims.op_Equality (FStar_List.length lid.FStar_Ident.ns) uu____4564)) && (

let uu____4573 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in (FStar_Ident.lid_equals uu____4573 ns))))


let try_lookup_name : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  foundname FStar_Pervasives_Native.option = (fun any_val exclude_interf env lid -> (

let occurrence_range = (FStar_Ident.range_of_lid lid)
in (

let k_global_def = (fun source_lid uu___99_4615 -> (match (uu___99_4615) with
| (uu____4622, true) when exclude_interf -> begin
FStar_Pervasives_Native.None
end
| (se, uu____4624) -> begin
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____4627) -> begin
(

let uu____4644 = (

let uu____4645 = (

let uu____4654 = (FStar_Syntax_Syntax.fvar source_lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in ((uu____4654), (false), (se.FStar_Syntax_Syntax.sigattrs)))
in Term_name (uu____4645))
in FStar_Pervasives_Native.Some (uu____4644))
end
| FStar_Syntax_Syntax.Sig_datacon (uu____4657) -> begin
(

let uu____4672 = (

let uu____4673 = (

let uu____4682 = (

let uu____4683 = (fv_qual_of_se se)
in (FStar_Syntax_Syntax.fvar source_lid FStar_Syntax_Syntax.Delta_constant uu____4683))
in ((uu____4682), (false), (se.FStar_Syntax_Syntax.sigattrs)))
in Term_name (uu____4673))
in FStar_Pervasives_Native.Some (uu____4672))
end
| FStar_Syntax_Syntax.Sig_let ((uu____4688, lbs), uu____4690) -> begin
(

let fv = (lb_fv lbs source_lid)
in (

let uu____4700 = (

let uu____4701 = (

let uu____4710 = (FStar_Syntax_Syntax.fvar source_lid fv.FStar_Syntax_Syntax.fv_delta fv.FStar_Syntax_Syntax.fv_qual)
in ((uu____4710), (false), (se.FStar_Syntax_Syntax.sigattrs)))
in Term_name (uu____4701))
in FStar_Pervasives_Native.Some (uu____4700)))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid1, uu____4714, uu____4715) -> begin
(

let quals = se.FStar_Syntax_Syntax.sigquals
in (

let uu____4719 = (any_val || (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___95_4723 -> (match (uu___95_4723) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| uu____4724 -> begin
false
end)))))
in (match (uu____4719) with
| true -> begin
(

let lid2 = (

let uu____4728 = (FStar_Ident.range_of_lid source_lid)
in (FStar_Ident.set_lid_range lid1 uu____4728))
in (

let dd = (

let uu____4730 = ((FStar_Syntax_Util.is_primop_lid lid2) || (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___96_4735 -> (match (uu___96_4735) with
| FStar_Syntax_Syntax.Projector (uu____4736) -> begin
true
end
| FStar_Syntax_Syntax.Discriminator (uu____4741) -> begin
true
end
| uu____4742 -> begin
false
end)))))
in (match (uu____4730) with
| true -> begin
FStar_Syntax_Syntax.Delta_equational
end
| uu____4743 -> begin
FStar_Syntax_Syntax.Delta_constant
end))
in (

let dd1 = (

let uu____4745 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___97_4749 -> (match (uu___97_4749) with
| FStar_Syntax_Syntax.Abstract -> begin
true
end
| uu____4750 -> begin
false
end))))
in (match (uu____4745) with
| true -> begin
FStar_Syntax_Syntax.Delta_abstract (dd)
end
| uu____4751 -> begin
dd
end))
in (

let uu____4752 = (FStar_Util.find_map quals (fun uu___98_4757 -> (match (uu___98_4757) with
| FStar_Syntax_Syntax.Reflectable (refl_monad) -> begin
FStar_Pervasives_Native.Some (refl_monad)
end
| uu____4761 -> begin
FStar_Pervasives_Native.None
end)))
in (match (uu____4752) with
| FStar_Pervasives_Native.Some (refl_monad) -> begin
(

let refl_const = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (refl_monad))) FStar_Pervasives_Native.None occurrence_range)
in FStar_Pervasives_Native.Some (Term_name (((refl_const), (false), (se.FStar_Syntax_Syntax.sigattrs)))))
end
| uu____4770 -> begin
(

let uu____4773 = (

let uu____4774 = (

let uu____4783 = (

let uu____4784 = (fv_qual_of_se se)
in (FStar_Syntax_Syntax.fvar lid2 dd1 uu____4784))
in ((uu____4783), (false), (se.FStar_Syntax_Syntax.sigattrs)))
in Term_name (uu____4774))
in FStar_Pervasives_Native.Some (uu____4773))
end)))))
end
| uu____4789 -> begin
FStar_Pervasives_Native.None
end)))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (ne) -> begin
(

let uu____4791 = (

let uu____4792 = (

let uu____4797 = (

let uu____4798 = (FStar_Ident.range_of_lid source_lid)
in (FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname uu____4798))
in ((se), (uu____4797)))
in Eff_name (uu____4792))
in FStar_Pervasives_Native.Some (uu____4791))
end
| FStar_Syntax_Syntax.Sig_new_effect (ne) -> begin
(

let uu____4800 = (

let uu____4801 = (

let uu____4806 = (

let uu____4807 = (FStar_Ident.range_of_lid source_lid)
in (FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname uu____4807))
in ((se), (uu____4806)))
in Eff_name (uu____4801))
in FStar_Pervasives_Native.Some (uu____4800))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (uu____4808) -> begin
FStar_Pervasives_Native.Some (Eff_name (((se), (source_lid))))
end
| FStar_Syntax_Syntax.Sig_splice (lids, t) -> begin
(

let uu____4827 = (

let uu____4828 = (

let uu____4837 = (FStar_Syntax_Syntax.fvar source_lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None)
in ((uu____4837), (false), ([])))
in Term_name (uu____4828))
in FStar_Pervasives_Native.Some (uu____4827))
end
| uu____4840 -> begin
FStar_Pervasives_Native.None
end)
end))
in (

let k_local_binding = (fun r -> (

let uu____4861 = (

let uu____4866 = (FStar_Ident.range_of_lid lid)
in (found_local_binding uu____4866 r))
in (match (uu____4861) with
| (t, mut) -> begin
FStar_Pervasives_Native.Some (Term_name (((t), (mut), ([]))))
end)))
in (

let k_rec_binding = (fun uu____4886 -> (match (uu____4886) with
| (id1, l, dd) -> begin
(

let uu____4898 = (

let uu____4899 = (

let uu____4908 = (

let uu____4909 = (

let uu____4910 = (FStar_Ident.range_of_lid lid)
in (FStar_Ident.set_lid_range l uu____4910))
in (FStar_Syntax_Syntax.fvar uu____4909 dd FStar_Pervasives_Native.None))
in ((uu____4908), (false), ([])))
in Term_name (uu____4899))
in FStar_Pervasives_Native.Some (uu____4898))
end))
in (

let found_unmangled = (match (lid.FStar_Ident.ns) with
| [] -> begin
(

let uu____4918 = (unmangleOpName lid.FStar_Ident.ident)
in (match (uu____4918) with
| FStar_Pervasives_Native.Some (t, mut) -> begin
FStar_Pervasives_Native.Some (Term_name (((t), (mut), ([]))))
end
| uu____4935 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____4942 -> begin
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

let uu____4977 = (try_lookup_name true exclude_interf env lid)
in (match (uu____4977) with
| FStar_Pervasives_Native.Some (Eff_name (o, l)) -> begin
FStar_Pervasives_Native.Some (((o), (l)))
end
| uu____4992 -> begin
FStar_Pervasives_Native.None
end)))


let try_lookup_effect_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident FStar_Pervasives_Native.option = (fun env l -> (

let uu____5011 = (try_lookup_effect_name' (not (env.iface)) env l)
in (match (uu____5011) with
| FStar_Pervasives_Native.Some (o, l1) -> begin
FStar_Pervasives_Native.Some (l1)
end
| uu____5026 -> begin
FStar_Pervasives_Native.None
end)))


let try_lookup_effect_name_and_attributes : env  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.cflags Prims.list) FStar_Pervasives_Native.option = (fun env l -> (

let uu____5051 = (try_lookup_effect_name' (not (env.iface)) env l)
in (match (uu____5051) with
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect (ne); FStar_Syntax_Syntax.sigrng = uu____5067; FStar_Syntax_Syntax.sigquals = uu____5068; FStar_Syntax_Syntax.sigmeta = uu____5069; FStar_Syntax_Syntax.sigattrs = uu____5070}, l1) -> begin
FStar_Pervasives_Native.Some (((l1), (ne.FStar_Syntax_Syntax.cattributes)))
end
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect_for_free (ne); FStar_Syntax_Syntax.sigrng = uu____5089; FStar_Syntax_Syntax.sigquals = uu____5090; FStar_Syntax_Syntax.sigmeta = uu____5091; FStar_Syntax_Syntax.sigattrs = uu____5092}, l1) -> begin
FStar_Pervasives_Native.Some (((l1), (ne.FStar_Syntax_Syntax.cattributes)))
end
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_effect_abbrev (uu____5110, uu____5111, uu____5112, uu____5113, cattributes); FStar_Syntax_Syntax.sigrng = uu____5115; FStar_Syntax_Syntax.sigquals = uu____5116; FStar_Syntax_Syntax.sigmeta = uu____5117; FStar_Syntax_Syntax.sigattrs = uu____5118}, l1) -> begin
FStar_Pervasives_Native.Some (((l1), (cattributes)))
end
| uu____5140 -> begin
FStar_Pervasives_Native.None
end)))


let try_lookup_effect_defn : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl FStar_Pervasives_Native.option = (fun env l -> (

let uu____5165 = (try_lookup_effect_name' (not (env.iface)) env l)
in (match (uu____5165) with
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect (ne); FStar_Syntax_Syntax.sigrng = uu____5175; FStar_Syntax_Syntax.sigquals = uu____5176; FStar_Syntax_Syntax.sigmeta = uu____5177; FStar_Syntax_Syntax.sigattrs = uu____5178}, uu____5179) -> begin
FStar_Pervasives_Native.Some (ne)
end
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect_for_free (ne); FStar_Syntax_Syntax.sigrng = uu____5189; FStar_Syntax_Syntax.sigquals = uu____5190; FStar_Syntax_Syntax.sigmeta = uu____5191; FStar_Syntax_Syntax.sigattrs = uu____5192}, uu____5193) -> begin
FStar_Pervasives_Native.Some (ne)
end
| uu____5202 -> begin
FStar_Pervasives_Native.None
end)))


let is_effect_name : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let uu____5219 = (try_lookup_effect_name env lid)
in (match (uu____5219) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (uu____5222) -> begin
true
end)))


let try_lookup_root_effect_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident FStar_Pervasives_Native.option = (fun env l -> (

let uu____5235 = (try_lookup_effect_name' (not (env.iface)) env l)
in (match (uu____5235) with
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_effect_abbrev (l', uu____5245, uu____5246, uu____5247, uu____5248); FStar_Syntax_Syntax.sigrng = uu____5249; FStar_Syntax_Syntax.sigquals = uu____5250; FStar_Syntax_Syntax.sigmeta = uu____5251; FStar_Syntax_Syntax.sigattrs = uu____5252}, uu____5253) -> begin
(

let rec aux = (fun new_name -> (

let uu____5274 = (FStar_Util.smap_try_find (sigmap env) new_name.FStar_Ident.str)
in (match (uu____5274) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (s, uu____5292) -> begin
(match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_new_effect_for_free (ne) -> begin
(

let uu____5300 = (

let uu____5301 = (FStar_Ident.range_of_lid l)
in (FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname uu____5301))
in FStar_Pervasives_Native.Some (uu____5300))
end
| FStar_Syntax_Syntax.Sig_new_effect (ne) -> begin
(

let uu____5303 = (

let uu____5304 = (FStar_Ident.range_of_lid l)
in (FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname uu____5304))
in FStar_Pervasives_Native.Some (uu____5303))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (uu____5305, uu____5306, uu____5307, cmp, uu____5309) -> begin
(

let l'' = (FStar_Syntax_Util.comp_effect_name cmp)
in (aux l''))
end
| uu____5315 -> begin
FStar_Pervasives_Native.None
end)
end)))
in (aux l'))
end
| FStar_Pervasives_Native.Some (uu____5316, l') -> begin
FStar_Pervasives_Native.Some (l')
end
| uu____5322 -> begin
FStar_Pervasives_Native.None
end)))


let lookup_letbinding_quals : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.qualifier Prims.list = (fun env lid -> (

let k_global_def = (fun lid1 uu___100_5359 -> (match (uu___100_5359) with
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (uu____5368, uu____5369, uu____5370); FStar_Syntax_Syntax.sigrng = uu____5371; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = uu____5373; FStar_Syntax_Syntax.sigattrs = uu____5374}, uu____5375) -> begin
FStar_Pervasives_Native.Some (quals)
end
| uu____5382 -> begin
FStar_Pervasives_Native.None
end))
in (

let uu____5389 = (resolve_in_open_namespaces' env lid (fun uu____5397 -> FStar_Pervasives_Native.None) (fun uu____5401 -> FStar_Pervasives_Native.None) k_global_def)
in (match (uu____5389) with
| FStar_Pervasives_Native.Some (quals) -> begin
quals
end
| uu____5411 -> begin
[]
end))))


let try_lookup_module : env  ->  FStar_Ident.path  ->  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option = (fun env path -> (

let uu____5428 = (FStar_List.tryFind (fun uu____5443 -> (match (uu____5443) with
| (mlid, modul) -> begin
(

let uu____5450 = (FStar_Ident.path_of_lid mlid)
in (Prims.op_Equality uu____5450 path))
end)) env.modules)
in (match (uu____5428) with
| FStar_Pervasives_Native.Some (uu____5453, modul) -> begin
FStar_Pervasives_Native.Some (modul)
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end)))


let try_lookup_let : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun env lid -> (

let k_global_def = (fun lid1 uu___101_5491 -> (match (uu___101_5491) with
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let ((uu____5498, lbs), uu____5500); FStar_Syntax_Syntax.sigrng = uu____5501; FStar_Syntax_Syntax.sigquals = uu____5502; FStar_Syntax_Syntax.sigmeta = uu____5503; FStar_Syntax_Syntax.sigattrs = uu____5504}, uu____5505) -> begin
(

let fv = (lb_fv lbs lid1)
in (

let uu____5519 = (FStar_Syntax_Syntax.fvar lid1 fv.FStar_Syntax_Syntax.fv_delta fv.FStar_Syntax_Syntax.fv_qual)
in FStar_Pervasives_Native.Some (uu____5519)))
end
| uu____5520 -> begin
FStar_Pervasives_Native.None
end))
in (resolve_in_open_namespaces' env lid (fun uu____5526 -> FStar_Pervasives_Native.None) (fun uu____5528 -> FStar_Pervasives_Native.None) k_global_def)))


let try_lookup_definition : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun env lid -> (

let k_global_def = (fun lid1 uu___102_5559 -> (match (uu___102_5559) with
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (lbs, uu____5569); FStar_Syntax_Syntax.sigrng = uu____5570; FStar_Syntax_Syntax.sigquals = uu____5571; FStar_Syntax_Syntax.sigmeta = uu____5572; FStar_Syntax_Syntax.sigattrs = uu____5573}, uu____5574) -> begin
(FStar_Util.find_map (FStar_Pervasives_Native.snd lbs) (fun lb -> (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv lid1) -> begin
FStar_Pervasives_Native.Some (lb.FStar_Syntax_Syntax.lbdef)
end
| uu____5597 -> begin
FStar_Pervasives_Native.None
end)))
end
| uu____5604 -> begin
FStar_Pervasives_Native.None
end))
in (resolve_in_open_namespaces' env lid (fun uu____5614 -> FStar_Pervasives_Native.None) (fun uu____5618 -> FStar_Pervasives_Native.None) k_global_def)))


let empty_include_smap : FStar_Ident.lident Prims.list FStar_ST.ref FStar_Util.smap = (new_sigmap ())


let empty_exported_id_smap : exported_id_set FStar_Util.smap = (new_sigmap ())


let try_lookup_lid' : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term * Prims.bool * FStar_Syntax_Syntax.attribute Prims.list) FStar_Pervasives_Native.option = (fun any_val exclude_interface env lid -> (

let uu____5675 = (try_lookup_name any_val exclude_interface env lid)
in (match (uu____5675) with
| FStar_Pervasives_Native.Some (Term_name (e, mut, attrs)) -> begin
FStar_Pervasives_Native.Some (((e), (mut), (attrs)))
end
| uu____5705 -> begin
FStar_Pervasives_Native.None
end)))


let drop_attributes : (FStar_Syntax_Syntax.term * Prims.bool * FStar_Syntax_Syntax.attribute Prims.list) FStar_Pervasives_Native.option  ->  (FStar_Syntax_Syntax.term * Prims.bool) FStar_Pervasives_Native.option = (fun x -> (match (x) with
| FStar_Pervasives_Native.Some (t, mut, uu____5761) -> begin
FStar_Pervasives_Native.Some (((t), (mut)))
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end))


let try_lookup_lid_with_attributes : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term * Prims.bool * FStar_Syntax_Syntax.attribute Prims.list) FStar_Pervasives_Native.option = (fun env l -> (try_lookup_lid' env.iface false env l))


let try_lookup_lid : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term * Prims.bool) FStar_Pervasives_Native.option = (fun env l -> (

let uu____5836 = (try_lookup_lid_with_attributes env l)
in (FStar_All.pipe_right uu____5836 drop_attributes)))


let resolve_to_fully_qualified_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident FStar_Pervasives_Native.option = (fun env l -> (

let uu____5875 = (try_lookup_lid env l)
in (match (uu____5875) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (e, uu____5889) -> begin
(

let uu____5894 = (

let uu____5895 = (FStar_Syntax_Subst.compress e)
in uu____5895.FStar_Syntax_Syntax.n)
in (match (uu____5894) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
FStar_Pervasives_Native.Some (fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end
| uu____5901 -> begin
FStar_Pervasives_Native.None
end))
end)))


let shorten_lid' : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (

let uu____5912 = (shorten_module_path env lid.FStar_Ident.ns true)
in (match (uu____5912) with
| (uu____5921, short) -> begin
(FStar_Ident.lid_of_ns_and_id short lid.FStar_Ident.ident)
end)))


let shorten_lid : env  ->  FStar_Ident.lid  ->  FStar_Ident.lid = (fun env lid -> (match (env.curmodule) with
| FStar_Pervasives_Native.None -> begin
(shorten_lid' env lid)
end
| uu____5941 -> begin
(

let lid_without_ns = (FStar_Ident.lid_of_ns_and_id [] lid.FStar_Ident.ident)
in (

let uu____5945 = (resolve_to_fully_qualified_name env lid_without_ns)
in (match (uu____5945) with
| FStar_Pervasives_Native.Some (lid') when (Prims.op_Equality lid'.FStar_Ident.str lid.FStar_Ident.str) -> begin
lid_without_ns
end
| uu____5949 -> begin
(shorten_lid' env lid)
end)))
end))


let try_lookup_lid_with_attributes_no_resolve : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term * Prims.bool * FStar_Syntax_Syntax.attribute Prims.list) FStar_Pervasives_Native.option = (fun env l -> (

let env' = (

let uu___123_5983 = env
in {curmodule = uu___123_5983.curmodule; curmonad = uu___123_5983.curmonad; modules = uu___123_5983.modules; scope_mods = []; exported_ids = empty_exported_id_smap; trans_exported_ids = uu___123_5983.trans_exported_ids; includes = empty_include_smap; sigaccum = uu___123_5983.sigaccum; sigmap = uu___123_5983.sigmap; iface = uu___123_5983.iface; admitted_iface = uu___123_5983.admitted_iface; expect_typ = uu___123_5983.expect_typ; docs = uu___123_5983.docs; remaining_iface_decls = uu___123_5983.remaining_iface_decls; syntax_only = uu___123_5983.syntax_only; ds_hooks = uu___123_5983.ds_hooks})
in (try_lookup_lid_with_attributes env' l)))


let try_lookup_lid_no_resolve : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term * Prims.bool) FStar_Pervasives_Native.option = (fun env l -> (

let uu____6006 = (try_lookup_lid_with_attributes_no_resolve env l)
in (FStar_All.pipe_right uu____6006 drop_attributes)))


let try_lookup_doc : env  ->  FStar_Ident.lid  ->  FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option = (fun env l -> (FStar_Util.smap_try_find env.docs l.FStar_Ident.str))


let try_lookup_datacon : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.fv FStar_Pervasives_Native.option = (fun env lid -> (

let k_global_def = (fun lid1 uu___104_6073 -> (match (uu___104_6073) with
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (uu____6080, uu____6081, uu____6082); FStar_Syntax_Syntax.sigrng = uu____6083; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = uu____6085; FStar_Syntax_Syntax.sigattrs = uu____6086}, uu____6087) -> begin
(

let uu____6092 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___103_6096 -> (match (uu___103_6096) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| uu____6097 -> begin
false
end))))
in (match (uu____6092) with
| true -> begin
(

let uu____6100 = (FStar_Syntax_Syntax.lid_as_fv lid1 FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in FStar_Pervasives_Native.Some (uu____6100))
end
| uu____6101 -> begin
FStar_Pervasives_Native.None
end))
end
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (uu____6102); FStar_Syntax_Syntax.sigrng = uu____6103; FStar_Syntax_Syntax.sigquals = uu____6104; FStar_Syntax_Syntax.sigmeta = uu____6105; FStar_Syntax_Syntax.sigattrs = uu____6106}, uu____6107) -> begin
(

let uu____6126 = (FStar_Syntax_Syntax.lid_as_fv lid1 FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))
in FStar_Pervasives_Native.Some (uu____6126))
end
| uu____6127 -> begin
FStar_Pervasives_Native.None
end))
in (resolve_in_open_namespaces' env lid (fun uu____6133 -> FStar_Pervasives_Native.None) (fun uu____6135 -> FStar_Pervasives_Native.None) k_global_def)))


let find_all_datacons : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.list FStar_Pervasives_Native.option = (fun env lid -> (

let k_global_def = (fun lid1 uu___105_6168 -> (match (uu___105_6168) with
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (uu____6177, uu____6178, uu____6179, uu____6180, datas, uu____6182); FStar_Syntax_Syntax.sigrng = uu____6183; FStar_Syntax_Syntax.sigquals = uu____6184; FStar_Syntax_Syntax.sigmeta = uu____6185; FStar_Syntax_Syntax.sigattrs = uu____6186}, uu____6187) -> begin
FStar_Pervasives_Native.Some (datas)
end
| uu____6202 -> begin
FStar_Pervasives_Native.None
end))
in (resolve_in_open_namespaces' env lid (fun uu____6212 -> FStar_Pervasives_Native.None) (fun uu____6216 -> FStar_Pervasives_Native.None) k_global_def)))


let record_cache_aux_with_filter : (((unit  ->  unit) * (unit  ->  unit) * (unit  ->  record_or_dc Prims.list) * (record_or_dc  ->  unit)) * (unit  ->  unit)) = (

let record_cache = (FStar_Util.mk_ref (([])::[]))
in (

let push1 = (fun uu____6268 -> (

let uu____6269 = (

let uu____6274 = (

let uu____6277 = (FStar_ST.op_Bang record_cache)
in (FStar_List.hd uu____6277))
in (

let uu____6337 = (FStar_ST.op_Bang record_cache)
in (uu____6274)::uu____6337))
in (FStar_ST.op_Colon_Equals record_cache uu____6269)))
in (

let pop1 = (fun uu____6455 -> (

let uu____6456 = (

let uu____6461 = (FStar_ST.op_Bang record_cache)
in (FStar_List.tl uu____6461))
in (FStar_ST.op_Colon_Equals record_cache uu____6456)))
in (

let peek1 = (fun uu____6581 -> (

let uu____6582 = (FStar_ST.op_Bang record_cache)
in (FStar_List.hd uu____6582)))
in (

let insert = (fun r -> (

let uu____6648 = (

let uu____6653 = (

let uu____6656 = (peek1 ())
in (r)::uu____6656)
in (

let uu____6659 = (

let uu____6664 = (FStar_ST.op_Bang record_cache)
in (FStar_List.tl uu____6664))
in (uu____6653)::uu____6659))
in (FStar_ST.op_Colon_Equals record_cache uu____6648)))
in (

let filter1 = (fun uu____6784 -> (

let rc = (peek1 ())
in (

let filtered = (FStar_List.filter (fun r -> (not (r.is_private_or_abstract))) rc)
in (

let uu____6793 = (

let uu____6798 = (

let uu____6803 = (FStar_ST.op_Bang record_cache)
in (FStar_List.tl uu____6803))
in (filtered)::uu____6798)
in (FStar_ST.op_Colon_Equals record_cache uu____6793)))))
in (

let aux = ((push1), (pop1), (peek1), (insert))
in ((aux), (filter1)))))))))


let record_cache_aux : ((unit  ->  unit) * (unit  ->  unit) * (unit  ->  record_or_dc Prims.list) * (record_or_dc  ->  unit)) = (

let uu____7002 = record_cache_aux_with_filter
in (match (uu____7002) with
| (aux, uu____7055) -> begin
aux
end))


let filter_record_cache : unit  ->  unit = (

let uu____7110 = record_cache_aux_with_filter
in (match (uu____7110) with
| (uu____7143, filter1) -> begin
filter1
end))


let push_record_cache : unit  ->  unit = (

let uu____7199 = record_cache_aux
in (match (uu____7199) with
| (push1, uu____7226, uu____7227, uu____7228) -> begin
push1
end))


let pop_record_cache : unit  ->  unit = (

let uu____7261 = record_cache_aux
in (match (uu____7261) with
| (uu____7287, pop1, uu____7289, uu____7290) -> begin
pop1
end))


let peek_record_cache : unit  ->  record_or_dc Prims.list = (

let uu____7325 = record_cache_aux
in (match (uu____7325) with
| (uu____7353, uu____7354, peek1, uu____7356) -> begin
peek1
end))


let insert_record_cache : record_or_dc  ->  unit = (

let uu____7389 = record_cache_aux
in (match (uu____7389) with
| (uu____7415, uu____7416, uu____7417, insert) -> begin
insert
end))


let extract_record : env  ->  scope_mod Prims.list FStar_ST.ref  ->  FStar_Syntax_Syntax.sigelt  ->  unit = (fun e new_globs se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_bundle (sigs, uu____7493) -> begin
(

let is_record = (FStar_Util.for_some (fun uu___106_7511 -> (match (uu___106_7511) with
| FStar_Syntax_Syntax.RecordType (uu____7512) -> begin
true
end
| FStar_Syntax_Syntax.RecordConstructor (uu____7521) -> begin
true
end
| uu____7530 -> begin
false
end)))
in (

let find_dc = (fun dc -> (FStar_All.pipe_right sigs (FStar_Util.find_opt (fun uu___107_7554 -> (match (uu___107_7554) with
| {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (lid, uu____7556, uu____7557, uu____7558, uu____7559, uu____7560); FStar_Syntax_Syntax.sigrng = uu____7561; FStar_Syntax_Syntax.sigquals = uu____7562; FStar_Syntax_Syntax.sigmeta = uu____7563; FStar_Syntax_Syntax.sigattrs = uu____7564} -> begin
(FStar_Ident.lid_equals dc lid)
end
| uu____7573 -> begin
false
end)))))
in (FStar_All.pipe_right sigs (FStar_List.iter (fun uu___108_7608 -> (match (uu___108_7608) with
| {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (typename, univs1, parms, uu____7612, uu____7613, (dc)::[]); FStar_Syntax_Syntax.sigrng = uu____7615; FStar_Syntax_Syntax.sigquals = typename_quals; FStar_Syntax_Syntax.sigmeta = uu____7617; FStar_Syntax_Syntax.sigattrs = uu____7618} -> begin
(

let uu____7629 = (

let uu____7630 = (find_dc dc)
in (FStar_All.pipe_left FStar_Util.must uu____7630))
in (match (uu____7629) with
| {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (constrname, uu____7636, t, uu____7638, uu____7639, uu____7640); FStar_Syntax_Syntax.sigrng = uu____7641; FStar_Syntax_Syntax.sigquals = uu____7642; FStar_Syntax_Syntax.sigmeta = uu____7643; FStar_Syntax_Syntax.sigattrs = uu____7644} -> begin
(

let uu____7653 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____7653) with
| (formals, uu____7667) -> begin
(

let is_rec = (is_record typename_quals)
in (

let formals' = (FStar_All.pipe_right formals (FStar_List.collect (fun uu____7716 -> (match (uu____7716) with
| (x, q) -> begin
(

let uu____7729 = ((FStar_Syntax_Syntax.is_null_bv x) || (is_rec && (FStar_Syntax_Syntax.is_implicit q)))
in (match (uu____7729) with
| true -> begin
[]
end
| uu____7740 -> begin
(((x), (q)))::[]
end))
end))))
in (

let fields' = (FStar_All.pipe_right formals' (FStar_List.map (fun uu____7782 -> (match (uu____7782) with
| (x, q) -> begin
(

let uu____7795 = (match (is_rec) with
| true -> begin
(FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname)
end
| uu____7796 -> begin
x.FStar_Syntax_Syntax.ppname
end)
in ((uu____7795), (x.FStar_Syntax_Syntax.sort)))
end))))
in (

let fields = fields'
in (

let record = {typename = typename; constrname = constrname.FStar_Ident.ident; parms = parms; fields = fields; is_private_or_abstract = ((FStar_List.contains FStar_Syntax_Syntax.Private typename_quals) || (FStar_List.contains FStar_Syntax_Syntax.Abstract typename_quals)); is_record = is_rec}
in ((

let uu____7808 = (

let uu____7811 = (FStar_ST.op_Bang new_globs)
in (Record_or_dc (record))::uu____7811)
in (FStar_ST.op_Colon_Equals new_globs uu____7808));
(match (()) with
| () -> begin
((

let add_field = (fun uu____7922 -> (match (uu____7922) with
| (id1, uu____7928) -> begin
(

let modul = (

let uu____7930 = (FStar_Ident.lid_of_ids constrname.FStar_Ident.ns)
in uu____7930.FStar_Ident.str)
in (

let uu____7931 = (get_exported_id_set e modul)
in (match (uu____7931) with
| FStar_Pervasives_Native.Some (my_ex) -> begin
(

let my_exported_ids = (my_ex Exported_id_field)
in ((

let uu____7965 = (

let uu____7966 = (FStar_ST.op_Bang my_exported_ids)
in (FStar_Util.set_add id1.FStar_Ident.idText uu____7966))
in (FStar_ST.op_Colon_Equals my_exported_ids uu____7965));
(match (()) with
| () -> begin
(

let projname = (

let uu____8060 = (

let uu____8061 = (FStar_Syntax_Util.mk_field_projector_name_from_ident constrname id1)
in uu____8061.FStar_Ident.ident)
in uu____8060.FStar_Ident.idText)
in (

let uu____8063 = (

let uu____8064 = (FStar_ST.op_Bang my_exported_ids)
in (FStar_Util.set_add projname uu____8064))
in (FStar_ST.op_Colon_Equals my_exported_ids uu____8063)))
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
| uu____8166 -> begin
()
end))
end
| uu____8167 -> begin
()
end))))))
end
| uu____8168 -> begin
()
end))


let try_lookup_record_or_dc_by_field_name : env  ->  FStar_Ident.lident  ->  record_or_dc FStar_Pervasives_Native.option = (fun env fieldname -> (

let find_in_cache = (fun fieldname1 -> (

let uu____8189 = ((fieldname1.FStar_Ident.ns), (fieldname1.FStar_Ident.ident))
in (match (uu____8189) with
| (ns, id1) -> begin
(

let uu____8206 = (peek_record_cache ())
in (FStar_Util.find_map uu____8206 (fun record -> (

let uu____8212 = (find_in_record ns id1 record (fun r -> Cont_ok (r)))
in (option_of_cont (fun uu____8218 -> FStar_Pervasives_Native.None) uu____8212)))))
end)))
in (resolve_in_open_namespaces'' env fieldname Exported_id_field (fun uu____8220 -> Cont_ignore) (fun uu____8222 -> Cont_ignore) (fun r -> Cont_ok (r)) (fun fn -> (

let uu____8228 = (find_in_cache fn)
in (cont_of_option Cont_ignore uu____8228))) (fun k uu____8234 -> k))))


let try_lookup_record_by_field_name : env  ->  FStar_Ident.lident  ->  record_or_dc FStar_Pervasives_Native.option = (fun env fieldname -> (

let uu____8249 = (try_lookup_record_or_dc_by_field_name env fieldname)
in (match (uu____8249) with
| FStar_Pervasives_Native.Some (r) when r.is_record -> begin
FStar_Pervasives_Native.Some (r)
end
| uu____8255 -> begin
FStar_Pervasives_Native.None
end)))


let belongs_to_record : env  ->  FStar_Ident.lident  ->  record_or_dc  ->  Prims.bool = (fun env lid record -> (

let uu____8273 = (try_lookup_record_by_field_name env lid)
in (match (uu____8273) with
| FStar_Pervasives_Native.Some (record') when (

let uu____8277 = (

let uu____8278 = (FStar_Ident.path_of_ns record.typename.FStar_Ident.ns)
in (FStar_Ident.text_of_path uu____8278))
in (

let uu____8279 = (

let uu____8280 = (FStar_Ident.path_of_ns record'.typename.FStar_Ident.ns)
in (FStar_Ident.text_of_path uu____8280))
in (Prims.op_Equality uu____8277 uu____8279))) -> begin
(

let uu____8281 = (find_in_record record.typename.FStar_Ident.ns lid.FStar_Ident.ident record (fun uu____8285 -> Cont_ok (())))
in (match (uu____8281) with
| Cont_ok (uu____8286) -> begin
true
end
| uu____8287 -> begin
false
end))
end
| uu____8290 -> begin
false
end)))


let try_lookup_dc_by_field_name : env  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * Prims.bool) FStar_Pervasives_Native.option = (fun env fieldname -> (

let uu____8309 = (try_lookup_record_or_dc_by_field_name env fieldname)
in (match (uu____8309) with
| FStar_Pervasives_Native.Some (r) -> begin
(

let uu____8319 = (

let uu____8324 = (

let uu____8325 = (FStar_Ident.lid_of_ids (FStar_List.append r.typename.FStar_Ident.ns ((r.constrname)::[])))
in (

let uu____8326 = (FStar_Ident.range_of_lid fieldname)
in (FStar_Ident.set_lid_range uu____8325 uu____8326)))
in ((uu____8324), (r.is_record)))
in FStar_Pervasives_Native.Some (uu____8319))
end
| uu____8331 -> begin
FStar_Pervasives_Native.None
end)))


let string_set_ref_new : unit  ->  Prims.string FStar_Util.set FStar_ST.ref = (fun uu____8357 -> (

let uu____8358 = (FStar_Util.new_set FStar_Util.compare)
in (FStar_Util.mk_ref uu____8358)))


let exported_id_set_new : unit  ->  exported_id_kind  ->  Prims.string FStar_Util.set FStar_ST.ref = (fun uu____8385 -> (

let term_type_set = (string_set_ref_new ())
in (

let field_set = (string_set_ref_new ())
in (fun uu___109_8396 -> (match (uu___109_8396) with
| Exported_id_term_type -> begin
term_type_set
end
| Exported_id_field -> begin
field_set
end)))))


let unique : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  Prims.bool = (fun any_val exclude_interface env lid -> (

let filter_scope_mods = (fun uu___110_8448 -> (match (uu___110_8448) with
| Rec_binding (uu____8449) -> begin
true
end
| uu____8450 -> begin
false
end))
in (

let this_env = (

let uu___124_8452 = env
in (

let uu____8453 = (FStar_List.filter filter_scope_mods env.scope_mods)
in {curmodule = uu___124_8452.curmodule; curmonad = uu___124_8452.curmonad; modules = uu___124_8452.modules; scope_mods = uu____8453; exported_ids = empty_exported_id_smap; trans_exported_ids = uu___124_8452.trans_exported_ids; includes = empty_include_smap; sigaccum = uu___124_8452.sigaccum; sigmap = uu___124_8452.sigmap; iface = uu___124_8452.iface; admitted_iface = uu___124_8452.admitted_iface; expect_typ = uu___124_8452.expect_typ; docs = uu___124_8452.docs; remaining_iface_decls = uu___124_8452.remaining_iface_decls; syntax_only = uu___124_8452.syntax_only; ds_hooks = uu___124_8452.ds_hooks}))
in (

let uu____8456 = (try_lookup_lid' any_val exclude_interface this_env lid)
in (match (uu____8456) with
| FStar_Pervasives_Native.None -> begin
true
end
| FStar_Pervasives_Native.Some (uu____8475) -> begin
false
end)))))


let push_scope_mod : env  ->  scope_mod  ->  env = (fun env scope_mod -> (

let uu___125_8502 = env
in {curmodule = uu___125_8502.curmodule; curmonad = uu___125_8502.curmonad; modules = uu___125_8502.modules; scope_mods = (scope_mod)::env.scope_mods; exported_ids = uu___125_8502.exported_ids; trans_exported_ids = uu___125_8502.trans_exported_ids; includes = uu___125_8502.includes; sigaccum = uu___125_8502.sigaccum; sigmap = uu___125_8502.sigmap; iface = uu___125_8502.iface; admitted_iface = uu___125_8502.admitted_iface; expect_typ = uu___125_8502.expect_typ; docs = uu___125_8502.docs; remaining_iface_decls = uu___125_8502.remaining_iface_decls; syntax_only = uu___125_8502.syntax_only; ds_hooks = uu___125_8502.ds_hooks}))


let push_bv' : env  ->  FStar_Ident.ident  ->  Prims.bool  ->  (env * FStar_Syntax_Syntax.bv) = (fun env x is_mutable -> (

let bv = (FStar_Syntax_Syntax.gen_bv x.FStar_Ident.idText (FStar_Pervasives_Native.Some (x.FStar_Ident.idRange)) FStar_Syntax_Syntax.tun)
in (((push_scope_mod env (Local_binding (((x), (bv), (is_mutable)))))), (bv))))


let push_bv_mutable : env  ->  FStar_Ident.ident  ->  (env * FStar_Syntax_Syntax.bv) = (fun env x -> (push_bv' env x true))


let push_bv : env  ->  FStar_Ident.ident  ->  (env * FStar_Syntax_Syntax.bv) = (fun env x -> (push_bv' env x false))


let push_top_level_rec_binding : env  ->  FStar_Ident.ident  ->  FStar_Syntax_Syntax.delta_depth  ->  env = (fun env x dd -> (

let l = (qualify env x)
in (

let uu____8567 = ((unique false true env l) || (FStar_Options.interactive ()))
in (match (uu____8567) with
| true -> begin
(push_scope_mod env (Rec_binding (((x), (l), (dd)))))
end
| uu____8568 -> begin
(

let uu____8569 = (FStar_Ident.range_of_lid l)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_DuplicateTopLevelNames), ((Prims.strcat "Duplicate top-level names " l.FStar_Ident.str))) uu____8569))
end))))


let push_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env s -> (

let err = (fun l -> (

let sopt = (FStar_Util.smap_try_find (sigmap env) l.FStar_Ident.str)
in (

let r = (match (sopt) with
| FStar_Pervasives_Native.Some (se, uu____8599) -> begin
(

let uu____8604 = (FStar_Util.find_opt (FStar_Ident.lid_equals l) (FStar_Syntax_Util.lids_of_sigelt se))
in (match (uu____8604) with
| FStar_Pervasives_Native.Some (l1) -> begin
(

let uu____8608 = (FStar_Ident.range_of_lid l1)
in (FStar_All.pipe_left FStar_Range.string_of_range uu____8608))
end
| FStar_Pervasives_Native.None -> begin
"<unknown>"
end))
end
| FStar_Pervasives_Native.None -> begin
"<unknown>"
end)
in (

let uu____8613 = (

let uu____8618 = (

let uu____8619 = (FStar_Ident.text_of_lid l)
in (FStar_Util.format2 "Duplicate top-level names [%s]; previously declared at %s" uu____8619 r))
in ((FStar_Errors.Fatal_DuplicateTopLevelNames), (uu____8618)))
in (

let uu____8620 = (FStar_Ident.range_of_lid l)
in (FStar_Errors.raise_error uu____8613 uu____8620))))))
in (

let globals = (FStar_Util.mk_ref env.scope_mods)
in (

let env1 = (

let uu____8629 = (match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let (uu____8638) -> begin
((false), (true))
end
| FStar_Syntax_Syntax.Sig_bundle (uu____8645) -> begin
((false), (true))
end
| uu____8654 -> begin
((false), (false))
end)
in (match (uu____8629) with
| (any_val, exclude_interface) -> begin
(

let lids = (FStar_Syntax_Util.lids_of_sigelt s)
in (

let uu____8660 = (FStar_Util.find_map lids (fun l -> (

let uu____8666 = (

let uu____8667 = (unique any_val exclude_interface env l)
in (not (uu____8667)))
in (match (uu____8666) with
| true -> begin
FStar_Pervasives_Native.Some (l)
end
| uu____8670 -> begin
FStar_Pervasives_Native.None
end))))
in (match (uu____8660) with
| FStar_Pervasives_Native.Some (l) -> begin
(err l)
end
| uu____8672 -> begin
((extract_record env globals s);
(

let uu___126_8698 = env
in {curmodule = uu___126_8698.curmodule; curmonad = uu___126_8698.curmonad; modules = uu___126_8698.modules; scope_mods = uu___126_8698.scope_mods; exported_ids = uu___126_8698.exported_ids; trans_exported_ids = uu___126_8698.trans_exported_ids; includes = uu___126_8698.includes; sigaccum = (s)::env.sigaccum; sigmap = uu___126_8698.sigmap; iface = uu___126_8698.iface; admitted_iface = uu___126_8698.admitted_iface; expect_typ = uu___126_8698.expect_typ; docs = uu___126_8698.docs; remaining_iface_decls = uu___126_8698.remaining_iface_decls; syntax_only = uu___126_8698.syntax_only; ds_hooks = uu___126_8698.ds_hooks});
)
end)))
end))
in (

let env2 = (

let uu___127_8700 = env1
in (

let uu____8701 = (FStar_ST.op_Bang globals)
in {curmodule = uu___127_8700.curmodule; curmonad = uu___127_8700.curmonad; modules = uu___127_8700.modules; scope_mods = uu____8701; exported_ids = uu___127_8700.exported_ids; trans_exported_ids = uu___127_8700.trans_exported_ids; includes = uu___127_8700.includes; sigaccum = uu___127_8700.sigaccum; sigmap = uu___127_8700.sigmap; iface = uu___127_8700.iface; admitted_iface = uu___127_8700.admitted_iface; expect_typ = uu___127_8700.expect_typ; docs = uu___127_8700.docs; remaining_iface_decls = uu___127_8700.remaining_iface_decls; syntax_only = uu___127_8700.syntax_only; ds_hooks = uu___127_8700.ds_hooks}))
in (

let uu____8753 = (match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____8779) -> begin
(

let uu____8788 = (FStar_List.map (fun se -> (((FStar_Syntax_Util.lids_of_sigelt se)), (se))) ses)
in ((env2), (uu____8788)))
end
| uu____8815 -> begin
((env2), (((((FStar_Syntax_Util.lids_of_sigelt s)), (s)))::[]))
end)
in (match (uu____8753) with
| (env3, lss) -> begin
((FStar_All.pipe_right lss (FStar_List.iter (fun uu____8874 -> (match (uu____8874) with
| (lids, se) -> begin
(FStar_All.pipe_right lids (FStar_List.iter (fun lid -> ((

let uu____8896 = (

let uu____8899 = (FStar_ST.op_Bang globals)
in (Top_level_def (lid.FStar_Ident.ident))::uu____8899)
in (FStar_ST.op_Colon_Equals globals uu____8896));
(match (()) with
| () -> begin
(

let modul = (

let uu____9001 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in uu____9001.FStar_Ident.str)
in ((

let uu____9003 = (get_exported_id_set env3 modul)
in (match (uu____9003) with
| FStar_Pervasives_Native.Some (f) -> begin
(

let my_exported_ids = (f Exported_id_term_type)
in (

let uu____9036 = (

let uu____9037 = (FStar_ST.op_Bang my_exported_ids)
in (FStar_Util.set_add lid.FStar_Ident.ident.FStar_Ident.idText uu____9037))
in (FStar_ST.op_Colon_Equals my_exported_ids uu____9036)))
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

let uu___128_9141 = env3
in (

let uu____9142 = (FStar_ST.op_Bang globals)
in {curmodule = uu___128_9141.curmodule; curmonad = uu___128_9141.curmonad; modules = uu___128_9141.modules; scope_mods = uu____9142; exported_ids = uu___128_9141.exported_ids; trans_exported_ids = uu___128_9141.trans_exported_ids; includes = uu___128_9141.includes; sigaccum = uu___128_9141.sigaccum; sigmap = uu___128_9141.sigmap; iface = uu___128_9141.iface; admitted_iface = uu___128_9141.admitted_iface; expect_typ = uu___128_9141.expect_typ; docs = uu___128_9141.docs; remaining_iface_decls = uu___128_9141.remaining_iface_decls; syntax_only = uu___128_9141.syntax_only; ds_hooks = uu___128_9141.ds_hooks}))
in env4);
)
end)))))))


let push_namespace : env  ->  FStar_Ident.lident  ->  env = (fun env ns -> (

let uu____9204 = (

let uu____9209 = (resolve_module_name env ns false)
in (match (uu____9209) with
| FStar_Pervasives_Native.None -> begin
(

let modules = env.modules
in (

let uu____9223 = (FStar_All.pipe_right modules (FStar_Util.for_some (fun uu____9239 -> (match (uu____9239) with
| (m, uu____9245) -> begin
(

let uu____9246 = (

let uu____9247 = (FStar_Ident.text_of_lid m)
in (Prims.strcat uu____9247 "."))
in (

let uu____9248 = (

let uu____9249 = (FStar_Ident.text_of_lid ns)
in (Prims.strcat uu____9249 "."))
in (FStar_Util.starts_with uu____9246 uu____9248)))
end))))
in (match (uu____9223) with
| true -> begin
((ns), (Open_namespace))
end
| uu____9254 -> begin
(

let uu____9255 = (

let uu____9260 = (

let uu____9261 = (FStar_Ident.text_of_lid ns)
in (FStar_Util.format1 "Namespace %s cannot be found" uu____9261))
in ((FStar_Errors.Fatal_NameSpaceNotFound), (uu____9260)))
in (

let uu____9262 = (FStar_Ident.range_of_lid ns)
in (FStar_Errors.raise_error uu____9255 uu____9262)))
end)))
end
| FStar_Pervasives_Native.Some (ns') -> begin
((fail_if_curmodule env ns ns');
((ns'), (Open_module));
)
end))
in (match (uu____9204) with
| (ns', kd) -> begin
((env.ds_hooks.ds_push_open_hook env ((ns'), (kd)));
(push_scope_mod env (Open_module_or_namespace (((ns'), (kd)))));
)
end)))


let push_include : env  ->  FStar_Ident.lident  ->  env = (fun env ns -> (

let ns0 = ns
in (

let uu____9283 = (resolve_module_name env ns false)
in (match (uu____9283) with
| FStar_Pervasives_Native.Some (ns1) -> begin
((env.ds_hooks.ds_push_include_hook env ns1);
(fail_if_curmodule env ns0 ns1);
(

let env1 = (push_scope_mod env (Open_module_or_namespace (((ns1), (Open_module)))))
in (

let curmod = (

let uu____9291 = (current_module env1)
in uu____9291.FStar_Ident.str)
in ((

let uu____9293 = (FStar_Util.smap_try_find env1.includes curmod)
in (match (uu____9293) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (incl) -> begin
(

let uu____9317 = (

let uu____9320 = (FStar_ST.op_Bang incl)
in (ns1)::uu____9320)
in (FStar_ST.op_Colon_Equals incl uu____9317))
end));
(match (()) with
| () -> begin
(

let uu____9421 = (get_trans_exported_id_set env1 ns1.FStar_Ident.str)
in (match (uu____9421) with
| FStar_Pervasives_Native.Some (ns_trans_exports) -> begin
((

let uu____9441 = (

let uu____9544 = (get_exported_id_set env1 curmod)
in (

let uu____9594 = (get_trans_exported_id_set env1 curmod)
in ((uu____9544), (uu____9594))))
in (match (uu____9441) with
| (FStar_Pervasives_Native.Some (cur_exports), FStar_Pervasives_Native.Some (cur_trans_exports)) -> begin
(

let update_exports = (fun k -> (

let ns_ex = (

let uu____10037 = (ns_trans_exports k)
in (FStar_ST.op_Bang uu____10037))
in (

let ex = (cur_exports k)
in ((

let uu____10223 = (

let uu____10226 = (FStar_ST.op_Bang ex)
in (FStar_Util.set_difference uu____10226 ns_ex))
in (FStar_ST.op_Colon_Equals ex uu____10223));
(match (()) with
| () -> begin
(

let trans_ex = (cur_trans_exports k)
in (

let uu____10430 = (

let uu____10433 = (FStar_ST.op_Bang trans_ex)
in (FStar_Util.set_union uu____10433 ns_ex))
in (FStar_ST.op_Colon_Equals trans_ex uu____10430)))
end);
))))
in (FStar_List.iter update_exports all_exported_id_kinds))
end
| uu____10570 -> begin
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

let uu____10678 = (

let uu____10683 = (FStar_Util.format1 "include: Module %s was not prepared" ns1.FStar_Ident.str)
in ((FStar_Errors.Fatal_IncludeModuleNotPrepared), (uu____10683)))
in (

let uu____10684 = (FStar_Ident.range_of_lid ns1)
in (FStar_Errors.raise_error uu____10678 uu____10684)))
end))
end);
)));
)
end
| uu____10685 -> begin
(

let uu____10688 = (

let uu____10693 = (FStar_Util.format1 "include: Module %s cannot be found" ns.FStar_Ident.str)
in ((FStar_Errors.Fatal_ModuleNotFound), (uu____10693)))
in (

let uu____10694 = (FStar_Ident.range_of_lid ns)
in (FStar_Errors.raise_error uu____10688 uu____10694)))
end))))


let push_module_abbrev : env  ->  FStar_Ident.ident  ->  FStar_Ident.lident  ->  env = (fun env x l -> (

let uu____10710 = (module_is_defined env l)
in (match (uu____10710) with
| true -> begin
((fail_if_curmodule env l l);
(env.ds_hooks.ds_push_module_abbrev_hook env x l);
(push_scope_mod env (Module_abbrev (((x), (l)))));
)
end
| uu____10713 -> begin
(

let uu____10714 = (

let uu____10719 = (

let uu____10720 = (FStar_Ident.text_of_lid l)
in (FStar_Util.format1 "Module %s cannot be found" uu____10720))
in ((FStar_Errors.Fatal_ModuleNotFound), (uu____10719)))
in (

let uu____10721 = (FStar_Ident.range_of_lid l)
in (FStar_Errors.raise_error uu____10714 uu____10721)))
end)))


let push_doc : env  ->  FStar_Ident.lident  ->  FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option  ->  env = (fun env l doc_opt -> (match (doc_opt) with
| FStar_Pervasives_Native.None -> begin
env
end
| FStar_Pervasives_Native.Some (doc1) -> begin
((

let uu____10743 = (FStar_Util.smap_try_find env.docs l.FStar_Ident.str)
in (match (uu____10743) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (old_doc) -> begin
(

let uu____10747 = (FStar_Ident.range_of_lid l)
in (

let uu____10748 = (

let uu____10753 = (

let uu____10754 = (FStar_Ident.string_of_lid l)
in (

let uu____10755 = (FStar_Parser_AST.string_of_fsdoc old_doc)
in (

let uu____10756 = (FStar_Parser_AST.string_of_fsdoc doc1)
in (FStar_Util.format3 "Overwriting doc of %s; old doc was [%s]; new doc are [%s]" uu____10754 uu____10755 uu____10756))))
in ((FStar_Errors.Warning_DocOverwrite), (uu____10753)))
in (FStar_Errors.log_issue uu____10747 uu____10748)))
end));
(FStar_Util.smap_add env.docs l.FStar_Ident.str doc1);
env;
)
end))


let check_admits : env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.modul = (fun env m -> (

let admitted_sig_lids = (FStar_All.pipe_right env.sigaccum (FStar_List.fold_left (fun lids se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_declare_typ (l, u, t) when (

let uu____10798 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_List.contains FStar_Syntax_Syntax.Assumption))
in (not (uu____10798))) -> begin
(

let uu____10801 = (FStar_Util.smap_try_find (sigmap env) l.FStar_Ident.str)
in (match (uu____10801) with
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (uu____10814); FStar_Syntax_Syntax.sigrng = uu____10815; FStar_Syntax_Syntax.sigquals = uu____10816; FStar_Syntax_Syntax.sigmeta = uu____10817; FStar_Syntax_Syntax.sigattrs = uu____10818}, uu____10819) -> begin
lids
end
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (uu____10834); FStar_Syntax_Syntax.sigrng = uu____10835; FStar_Syntax_Syntax.sigquals = uu____10836; FStar_Syntax_Syntax.sigmeta = uu____10837; FStar_Syntax_Syntax.sigattrs = uu____10838}, uu____10839) -> begin
lids
end
| uu____10864 -> begin
((

let uu____10872 = (

let uu____10873 = (FStar_Options.interactive ())
in (not (uu____10873)))
in (match (uu____10872) with
| true -> begin
(

let uu____10874 = (FStar_Ident.range_of_lid l)
in (

let uu____10875 = (

let uu____10880 = (

let uu____10881 = (FStar_Ident.string_of_lid l)
in (FStar_Util.format1 "Admitting %s without a definition" uu____10881))
in ((FStar_Errors.Warning_AdmitWithoutDefinition), (uu____10880)))
in (FStar_Errors.log_issue uu____10874 uu____10875)))
end
| uu____10882 -> begin
()
end));
(

let quals = (FStar_Syntax_Syntax.Assumption)::se.FStar_Syntax_Syntax.sigquals
in ((FStar_Util.smap_add (sigmap env) l.FStar_Ident.str (((

let uu___129_10892 = se
in {FStar_Syntax_Syntax.sigel = uu___129_10892.FStar_Syntax_Syntax.sigel; FStar_Syntax_Syntax.sigrng = uu___129_10892.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = uu___129_10892.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___129_10892.FStar_Syntax_Syntax.sigattrs})), (false)));
(l)::lids;
));
)
end))
end
| uu____10893 -> begin
lids
end)) []))
in (

let uu___130_10894 = m
in (

let uu____10895 = (FStar_All.pipe_right m.FStar_Syntax_Syntax.declarations (FStar_List.map (fun s -> (match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____10905, uu____10906) when (FStar_List.existsb (fun l -> (FStar_Ident.lid_equals l lid)) admitted_sig_lids) -> begin
(

let uu___131_10909 = s
in {FStar_Syntax_Syntax.sigel = uu___131_10909.FStar_Syntax_Syntax.sigel; FStar_Syntax_Syntax.sigrng = uu___131_10909.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Assumption)::s.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___131_10909.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___131_10909.FStar_Syntax_Syntax.sigattrs})
end
| uu____10910 -> begin
s
end))))
in {FStar_Syntax_Syntax.name = uu___130_10894.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = uu____10895; FStar_Syntax_Syntax.exports = uu___130_10894.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = uu___130_10894.FStar_Syntax_Syntax.is_interface}))))


let finish : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env modul -> ((FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations (FStar_List.iter (fun se -> (

let quals = se.FStar_Syntax_Syntax.sigquals
in (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____10933) -> begin
(match (((FStar_List.contains FStar_Syntax_Syntax.Private quals) || (FStar_List.contains FStar_Syntax_Syntax.Abstract quals))) with
| true -> begin
(FStar_All.pipe_right ses (FStar_List.iter (fun se1 -> (match (se1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (lid, uu____10953, uu____10954, uu____10955, uu____10956, uu____10957) -> begin
(FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str)
end
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, univ_names, binders, typ, uu____10970, uu____10971) -> begin
((FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str);
(match ((not ((FStar_List.contains FStar_Syntax_Syntax.Private quals)))) with
| true -> begin
(

let sigel = (

let uu____10986 = (

let uu____10993 = (

let uu____10994 = (FStar_Ident.range_of_lid lid)
in (

let uu____10995 = (

let uu____11002 = (

let uu____11003 = (

let uu____11016 = (FStar_Syntax_Syntax.mk_Total typ)
in ((binders), (uu____11016)))
in FStar_Syntax_Syntax.Tm_arrow (uu____11003))
in (FStar_Syntax_Syntax.mk uu____11002))
in (uu____10995 FStar_Pervasives_Native.None uu____10994)))
in ((lid), (univ_names), (uu____10993)))
in FStar_Syntax_Syntax.Sig_declare_typ (uu____10986))
in (

let se2 = (

let uu___132_11031 = se1
in {FStar_Syntax_Syntax.sigel = sigel; FStar_Syntax_Syntax.sigrng = uu___132_11031.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Assumption)::quals; FStar_Syntax_Syntax.sigmeta = uu___132_11031.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___132_11031.FStar_Syntax_Syntax.sigattrs})
in (FStar_Util.smap_add (sigmap env) lid.FStar_Ident.str ((se2), (false)))))
end
| uu____11036 -> begin
()
end);
)
end
| uu____11037 -> begin
()
end))))
end
| uu____11038 -> begin
()
end)
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____11040, uu____11041) -> begin
(match ((FStar_List.contains FStar_Syntax_Syntax.Private quals)) with
| true -> begin
(FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str)
end
| uu____11046 -> begin
()
end)
end
| FStar_Syntax_Syntax.Sig_let ((uu____11047, lbs), uu____11049) -> begin
((match (((FStar_List.contains FStar_Syntax_Syntax.Private quals) || (FStar_List.contains FStar_Syntax_Syntax.Abstract quals))) with
| true -> begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (

let uu____11064 = (

let uu____11065 = (

let uu____11066 = (

let uu____11069 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in uu____11069.FStar_Syntax_Syntax.fv_name)
in uu____11066.FStar_Syntax_Syntax.v)
in uu____11065.FStar_Ident.str)
in (FStar_Util.smap_remove (sigmap env) uu____11064)))))
end
| uu____11074 -> begin
()
end);
(match (((FStar_List.contains FStar_Syntax_Syntax.Abstract quals) && (not ((FStar_List.contains FStar_Syntax_Syntax.Private quals))))) with
| true -> begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (

let lid = (

let uu____11083 = (

let uu____11086 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in uu____11086.FStar_Syntax_Syntax.fv_name)
in uu____11083.FStar_Syntax_Syntax.v)
in (

let quals1 = (FStar_Syntax_Syntax.Assumption)::quals
in (

let decl = (

let uu___133_11091 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp))); FStar_Syntax_Syntax.sigrng = uu___133_11091.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = uu___133_11091.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___133_11091.FStar_Syntax_Syntax.sigattrs})
in (FStar_Util.smap_add (sigmap env) lid.FStar_Ident.str ((decl), (false)))))))))
end
| uu____11096 -> begin
()
end);
)
end
| uu____11097 -> begin
()
end)))));
(

let curmod = (

let uu____11099 = (current_module env)
in uu____11099.FStar_Ident.str)
in ((

let uu____11101 = (

let uu____11204 = (get_exported_id_set env curmod)
in (

let uu____11254 = (get_trans_exported_id_set env curmod)
in ((uu____11204), (uu____11254))))
in (match (uu____11101) with
| (FStar_Pervasives_Native.Some (cur_ex), FStar_Pervasives_Native.Some (cur_trans_ex)) -> begin
(

let update_exports = (fun eikind -> (

let cur_ex_set = (

let uu____11699 = (cur_ex eikind)
in (FStar_ST.op_Bang uu____11699))
in (

let cur_trans_ex_set_ref = (cur_trans_ex eikind)
in (

let uu____11898 = (

let uu____11901 = (FStar_ST.op_Bang cur_trans_ex_set_ref)
in (FStar_Util.set_union cur_ex_set uu____11901))
in (FStar_ST.op_Colon_Equals cur_trans_ex_set_ref uu____11898)))))
in (FStar_List.iter update_exports all_exported_id_kinds))
end
| uu____12038 -> begin
()
end));
(match (()) with
| () -> begin
((filter_record_cache ());
(match (()) with
| () -> begin
(

let uu___134_12142 = env
in {curmodule = FStar_Pervasives_Native.None; curmonad = uu___134_12142.curmonad; modules = (((modul.FStar_Syntax_Syntax.name), (modul)))::env.modules; scope_mods = []; exported_ids = uu___134_12142.exported_ids; trans_exported_ids = uu___134_12142.trans_exported_ids; includes = uu___134_12142.includes; sigaccum = []; sigmap = uu___134_12142.sigmap; iface = uu___134_12142.iface; admitted_iface = uu___134_12142.admitted_iface; expect_typ = uu___134_12142.expect_typ; docs = uu___134_12142.docs; remaining_iface_decls = uu___134_12142.remaining_iface_decls; syntax_only = uu___134_12142.syntax_only; ds_hooks = uu___134_12142.ds_hooks})
end);
)
end);
));
))


let stack : env Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let push : env  ->  env = (fun env -> ((push_record_cache ());
(

let uu____12171 = (

let uu____12174 = (FStar_ST.op_Bang stack)
in (env)::uu____12174)
in (FStar_ST.op_Colon_Equals stack uu____12171));
(

let uu___135_12231 = env
in (

let uu____12232 = (FStar_Util.smap_copy (sigmap env))
in (

let uu____12243 = (FStar_Util.smap_copy env.docs)
in {curmodule = uu___135_12231.curmodule; curmonad = uu___135_12231.curmonad; modules = uu___135_12231.modules; scope_mods = uu___135_12231.scope_mods; exported_ids = uu___135_12231.exported_ids; trans_exported_ids = uu___135_12231.trans_exported_ids; includes = uu___135_12231.includes; sigaccum = uu___135_12231.sigaccum; sigmap = uu____12232; iface = uu___135_12231.iface; admitted_iface = uu___135_12231.admitted_iface; expect_typ = uu___135_12231.expect_typ; docs = uu____12243; remaining_iface_decls = uu___135_12231.remaining_iface_decls; syntax_only = uu___135_12231.syntax_only; ds_hooks = uu___135_12231.ds_hooks})));
))


let pop : unit  ->  env = (fun uu____12250 -> (

let uu____12251 = (FStar_ST.op_Bang stack)
in (match (uu____12251) with
| (env)::tl1 -> begin
((pop_record_cache ());
(FStar_ST.op_Colon_Equals stack tl1);
env;
)
end
| uu____12314 -> begin
(failwith "Impossible: Too many pops")
end)))


let export_interface : FStar_Ident.lident  ->  env  ->  env = (fun m env -> (

let sigelt_in_m = (fun se -> (match ((FStar_Syntax_Util.lids_of_sigelt se)) with
| (l)::uu____12334 -> begin
(Prims.op_Equality l.FStar_Ident.nsstr m.FStar_Ident.str)
end
| uu____12337 -> begin
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

let uu____12371 = (FStar_Util.smap_try_find sm' k)
in (match (uu____12371) with
| FStar_Pervasives_Native.Some (se, true) when (sigelt_in_m se) -> begin
((FStar_Util.smap_remove sm' k);
(

let se1 = (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_declare_typ (l, u, t) -> begin
(

let uu___136_12396 = se
in {FStar_Syntax_Syntax.sigel = uu___136_12396.FStar_Syntax_Syntax.sigel; FStar_Syntax_Syntax.sigrng = uu___136_12396.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Assumption)::se.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___136_12396.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___136_12396.FStar_Syntax_Syntax.sigattrs})
end
| uu____12397 -> begin
se
end)
in (FStar_Util.smap_add sm' k ((se1), (false))));
)
end
| uu____12402 -> begin
()
end)))));
env1;
)))))))


let finish_module_or_interface : env  ->  FStar_Syntax_Syntax.modul  ->  (env * FStar_Syntax_Syntax.modul) = (fun env modul -> (

let modul1 = (match ((not (modul.FStar_Syntax_Syntax.is_interface))) with
| true -> begin
(check_admits env modul)
end
| uu____12424 -> begin
modul
end)
in (

let uu____12425 = (finish env modul1)
in ((uu____12425), (modul1)))))

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

let uu____12513 = (

let uu____12516 = (e Exported_id_term_type)
in (FStar_ST.op_Bang uu____12516))
in (FStar_Util.set_elements uu____12513))
in (

let fields = (

let uu____12638 = (

let uu____12641 = (e Exported_id_field)
in (FStar_ST.op_Bang uu____12641))
in (FStar_Util.set_elements uu____12638))
in {exported_id_terms = terms; exported_id_fields = fields})))


let as_exported_id_set : exported_ids FStar_Pervasives_Native.option  ->  exported_id_kind  ->  Prims.string FStar_Util.set FStar_ST.ref = (fun e -> (match (e) with
| FStar_Pervasives_Native.None -> begin
(exported_id_set_new ())
end
| FStar_Pervasives_Native.Some (e1) -> begin
(

let terms = (

let uu____12800 = (FStar_Util.as_set e1.exported_id_terms FStar_Util.compare)
in (FStar_Util.mk_ref uu____12800))
in (

let fields = (

let uu____12810 = (FStar_Util.as_set e1.exported_id_fields FStar_Util.compare)
in (FStar_Util.mk_ref uu____12810))
in (fun uu___111_12815 -> (match (uu___111_12815) with
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


let as_includes : 'Auu____12946 . 'Auu____12946 Prims.list FStar_Pervasives_Native.option  ->  'Auu____12946 Prims.list FStar_ST.ref = (fun uu___112_12959 -> (match (uu___112_12959) with
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

let uu____13000 = (FStar_Util.smap_try_find m mname)
in (FStar_Util.map_opt uu____13000 as_exported_ids)))
in (

let uu____13006 = (as_ids_opt env.exported_ids)
in (

let uu____13009 = (as_ids_opt env.trans_exported_ids)
in (

let uu____13012 = (

let uu____13017 = (FStar_Util.smap_try_find env.includes mname)
in (FStar_Util.map_opt uu____13017 (fun r -> (FStar_ST.op_Bang r))))
in {mii_exported_ids = uu____13006; mii_trans_exported_ids = uu____13009; mii_includes = uu____13012}))))))


let prepare_module_or_interface : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  module_inclusion_info  ->  (env * Prims.bool) = (fun intf admitted env mname mii -> (

let prep = (fun env1 -> (

let filename = (

let uu____13136 = (FStar_Ident.text_of_lid mname)
in (FStar_Util.strcat uu____13136 ".fst"))
in (

let auto_open = (FStar_Parser_Dep.hard_coded_dependencies filename)
in (

let auto_open1 = (

let convert_kind = (fun uu___113_13156 -> (match (uu___113_13156) with
| FStar_Parser_Dep.Open_namespace -> begin
Open_namespace
end
| FStar_Parser_Dep.Open_module -> begin
Open_module
end))
in (FStar_List.map (fun uu____13168 -> (match (uu____13168) with
| (lid, kind) -> begin
((lid), ((convert_kind kind)))
end)) auto_open))
in (

let namespace_of_module = (match (((FStar_List.length mname.FStar_Ident.ns) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____13192 = (

let uu____13197 = (FStar_Ident.lid_of_ids mname.FStar_Ident.ns)
in ((uu____13197), (Open_namespace)))
in (uu____13192)::[])
end
| uu____13206 -> begin
[]
end)
in (

let auto_open2 = (FStar_List.append namespace_of_module (FStar_List.rev auto_open1))
in ((

let uu____13227 = (as_exported_id_set mii.mii_exported_ids)
in (FStar_Util.smap_add env1.exported_ids mname.FStar_Ident.str uu____13227));
(match (()) with
| () -> begin
((

let uu____13254 = (as_exported_id_set mii.mii_trans_exported_ids)
in (FStar_Util.smap_add env1.trans_exported_ids mname.FStar_Ident.str uu____13254));
(match (()) with
| () -> begin
((

let uu____13281 = (as_includes mii.mii_includes)
in (FStar_Util.smap_add env1.includes mname.FStar_Ident.str uu____13281));
(match (()) with
| () -> begin
(

let env' = (

let uu___137_13313 = env1
in (

let uu____13314 = (FStar_List.map (fun x -> Open_module_or_namespace (x)) auto_open2)
in {curmodule = FStar_Pervasives_Native.Some (mname); curmonad = uu___137_13313.curmonad; modules = uu___137_13313.modules; scope_mods = uu____13314; exported_ids = uu___137_13313.exported_ids; trans_exported_ids = uu___137_13313.trans_exported_ids; includes = uu___137_13313.includes; sigaccum = uu___137_13313.sigaccum; sigmap = env1.sigmap; iface = intf; admitted_iface = admitted; expect_typ = uu___137_13313.expect_typ; docs = uu___137_13313.docs; remaining_iface_decls = uu___137_13313.remaining_iface_decls; syntax_only = uu___137_13313.syntax_only; ds_hooks = uu___137_13313.ds_hooks}))
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

let uu____13326 = (FStar_All.pipe_right env.modules (FStar_Util.find_opt (fun uu____13352 -> (match (uu____13352) with
| (l, uu____13358) -> begin
(FStar_Ident.lid_equals l mname)
end))))
in (match (uu____13326) with
| FStar_Pervasives_Native.None -> begin
(

let uu____13367 = (prep env)
in ((uu____13367), (false)))
end
| FStar_Pervasives_Native.Some (uu____13368, m) -> begin
((

let uu____13375 = ((

let uu____13378 = (FStar_Options.interactive ())
in (not (uu____13378))) && ((not (m.FStar_Syntax_Syntax.is_interface)) || intf))
in (match (uu____13375) with
| true -> begin
(

let uu____13379 = (

let uu____13384 = (FStar_Util.format1 "Duplicate module or interface name: %s" mname.FStar_Ident.str)
in ((FStar_Errors.Fatal_DuplicateModuleOrInterface), (uu____13384)))
in (

let uu____13385 = (FStar_Ident.range_of_lid mname)
in (FStar_Errors.raise_error uu____13379 uu____13385)))
end
| uu____13386 -> begin
()
end));
(

let uu____13387 = (

let uu____13388 = (push env)
in (prep uu____13388))
in ((uu____13387), (true)));
)
end))))


let enter_monad_scope : env  ->  FStar_Ident.ident  ->  env = (fun env mname -> (match (env.curmonad) with
| FStar_Pervasives_Native.Some (mname') -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_MonadAlreadyDefined), ((Prims.strcat "Trying to define monad " (Prims.strcat mname.FStar_Ident.idText (Prims.strcat ", but already in monad scope " mname'.FStar_Ident.idText))))) mname.FStar_Ident.idRange)
end
| FStar_Pervasives_Native.None -> begin
(

let uu___138_13400 = env
in {curmodule = uu___138_13400.curmodule; curmonad = FStar_Pervasives_Native.Some (mname); modules = uu___138_13400.modules; scope_mods = uu___138_13400.scope_mods; exported_ids = uu___138_13400.exported_ids; trans_exported_ids = uu___138_13400.trans_exported_ids; includes = uu___138_13400.includes; sigaccum = uu___138_13400.sigaccum; sigmap = uu___138_13400.sigmap; iface = uu___138_13400.iface; admitted_iface = uu___138_13400.admitted_iface; expect_typ = uu___138_13400.expect_typ; docs = uu___138_13400.docs; remaining_iface_decls = uu___138_13400.remaining_iface_decls; syntax_only = uu___138_13400.syntax_only; ds_hooks = uu___138_13400.ds_hooks})
end))


let fail_or : 'a . env  ->  (FStar_Ident.lident  ->  'a FStar_Pervasives_Native.option)  ->  FStar_Ident.lident  ->  'a = (fun env lookup1 lid -> (

let uu____13434 = (lookup1 lid)
in (match (uu____13434) with
| FStar_Pervasives_Native.None -> begin
(

let opened_modules = (FStar_List.map (fun uu____13447 -> (match (uu____13447) with
| (lid1, uu____13453) -> begin
(FStar_Ident.text_of_lid lid1)
end)) env.modules)
in (

let msg = (

let uu____13455 = (FStar_Ident.text_of_lid lid)
in (FStar_Util.format1 "Identifier not found: [%s]" uu____13455))
in (

let msg1 = (match ((Prims.op_Equality (FStar_List.length lid.FStar_Ident.ns) (Prims.parse_int "0"))) with
| true -> begin
msg
end
| uu____13458 -> begin
(

let modul = (

let uu____13460 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in (

let uu____13461 = (FStar_Ident.range_of_lid lid)
in (FStar_Ident.set_lid_range uu____13460 uu____13461)))
in (

let uu____13462 = (resolve_module_name env modul true)
in (match (uu____13462) with
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

let uu____13471 = (FStar_Ident.range_of_lid lid)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_IdentifierNotFound), (msg1)) uu____13471)))))
end
| FStar_Pervasives_Native.Some (r) -> begin
r
end)))


let fail_or2 : 'a . (FStar_Ident.ident  ->  'a FStar_Pervasives_Native.option)  ->  FStar_Ident.ident  ->  'a = (fun lookup1 id1 -> (

let uu____13499 = (lookup1 id1)
in (match (uu____13499) with
| FStar_Pervasives_Native.None -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_IdentifierNotFound), ((Prims.strcat "Identifier not found [" (Prims.strcat id1.FStar_Ident.idText "]")))) id1.FStar_Ident.idRange)
end
| FStar_Pervasives_Native.Some (r) -> begin
r
end)))


let mk_copy : env  ->  env = (fun en -> (

let uu___139_13508 = en
in (

let uu____13509 = (FStar_Util.smap_copy en.exported_ids)
in (

let uu____13514 = (FStar_Util.smap_copy en.trans_exported_ids)
in (

let uu____13519 = (FStar_Util.smap_copy en.sigmap)
in (

let uu____13530 = (FStar_Util.smap_copy en.docs)
in {curmodule = uu___139_13508.curmodule; curmonad = uu___139_13508.curmonad; modules = uu___139_13508.modules; scope_mods = uu___139_13508.scope_mods; exported_ids = uu____13509; trans_exported_ids = uu____13514; includes = uu___139_13508.includes; sigaccum = uu___139_13508.sigaccum; sigmap = uu____13519; iface = uu___139_13508.iface; admitted_iface = uu___139_13508.admitted_iface; expect_typ = uu___139_13508.expect_typ; docs = uu____13530; remaining_iface_decls = uu___139_13508.remaining_iface_decls; syntax_only = uu___139_13508.syntax_only; ds_hooks = uu___139_13508.ds_hooks}))))))




