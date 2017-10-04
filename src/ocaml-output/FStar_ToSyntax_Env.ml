
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
| uu____21 -> begin
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
| uu____198 -> begin
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
| uu____212 -> begin
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
| uu____226 -> begin
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
| uu____240 -> begin
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
| uu____254 -> begin
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
| uu____268 -> begin
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
| uu____283 -> begin
false
end))


let uu___is_Exported_id_field : exported_id_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Exported_id_field -> begin
true
end
| uu____288 -> begin
false
end))


type exported_id_set =
exported_id_kind  ->  string_set FStar_ST.ref

type env =
{curmodule : FStar_Ident.lident FStar_Pervasives_Native.option; curmonad : FStar_Ident.ident FStar_Pervasives_Native.option; modules : (FStar_Ident.lident * FStar_Syntax_Syntax.modul) Prims.list; scope_mods : scope_mod Prims.list; exported_ids : exported_id_set FStar_Util.smap; trans_exported_ids : exported_id_set FStar_Util.smap; includes : FStar_Ident.lident Prims.list FStar_ST.ref FStar_Util.smap; sigaccum : FStar_Syntax_Syntax.sigelts; sigmap : (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap; iface : Prims.bool; admitted_iface : Prims.bool; expect_typ : Prims.bool; docs : FStar_Parser_AST.fsdoc FStar_Util.smap; remaining_iface_decls : (FStar_Ident.lident * FStar_Parser_AST.decl Prims.list) Prims.list; syntax_only : Prims.bool; ds_hooks : dsenv_hooks} 
 and dsenv_hooks =
{ds_push_open_hook : env  ->  open_module_or_namespace  ->  Prims.unit; ds_push_include_hook : env  ->  FStar_Ident.lident  ->  Prims.unit; ds_push_module_abbrev_hook : env  ->  FStar_Ident.ident  ->  FStar_Ident.lident  ->  Prims.unit}


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


let __proj__Mkdsenv_hooks__item__ds_push_open_hook : dsenv_hooks  ->  env  ->  open_module_or_namespace  ->  Prims.unit = (fun projectee -> (match (projectee) with
| {ds_push_open_hook = __fname__ds_push_open_hook; ds_push_include_hook = __fname__ds_push_include_hook; ds_push_module_abbrev_hook = __fname__ds_push_module_abbrev_hook} -> begin
__fname__ds_push_open_hook
end))


let __proj__Mkdsenv_hooks__item__ds_push_include_hook : dsenv_hooks  ->  env  ->  FStar_Ident.lident  ->  Prims.unit = (fun projectee -> (match (projectee) with
| {ds_push_open_hook = __fname__ds_push_open_hook; ds_push_include_hook = __fname__ds_push_include_hook; ds_push_module_abbrev_hook = __fname__ds_push_module_abbrev_hook} -> begin
__fname__ds_push_include_hook
end))


let __proj__Mkdsenv_hooks__item__ds_push_module_abbrev_hook : dsenv_hooks  ->  env  ->  FStar_Ident.ident  ->  FStar_Ident.lident  ->  Prims.unit = (fun projectee -> (match (projectee) with
| {ds_push_open_hook = __fname__ds_push_open_hook; ds_push_include_hook = __fname__ds_push_include_hook; ds_push_module_abbrev_hook = __fname__ds_push_module_abbrev_hook} -> begin
__fname__ds_push_module_abbrev_hook
end))


type 'a withenv =
env  ->  ('a * env)


let default_ds_hooks : dsenv_hooks = {ds_push_open_hook = (fun uu____1571 uu____1572 -> ()); ds_push_include_hook = (fun uu____1575 uu____1576 -> ()); ds_push_module_abbrev_hook = (fun uu____1580 uu____1581 uu____1582 -> ())}

type foundname =
| Term_name of (FStar_Syntax_Syntax.typ * Prims.bool)
| Eff_name of (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident)


let uu___is_Term_name : foundname  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Term_name (_0) -> begin
true
end
| uu____1608 -> begin
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
| uu____1638 -> begin
false
end))


let __proj__Eff_name__item___0 : foundname  ->  (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident) = (fun projectee -> (match (projectee) with
| Eff_name (_0) -> begin
_0
end))


let set_iface : env  ->  Prims.bool  ->  env = (fun env b -> (

let uu___184_1667 = env
in {curmodule = uu___184_1667.curmodule; curmonad = uu___184_1667.curmonad; modules = uu___184_1667.modules; scope_mods = uu___184_1667.scope_mods; exported_ids = uu___184_1667.exported_ids; trans_exported_ids = uu___184_1667.trans_exported_ids; includes = uu___184_1667.includes; sigaccum = uu___184_1667.sigaccum; sigmap = uu___184_1667.sigmap; iface = b; admitted_iface = uu___184_1667.admitted_iface; expect_typ = uu___184_1667.expect_typ; docs = uu___184_1667.docs; remaining_iface_decls = uu___184_1667.remaining_iface_decls; syntax_only = uu___184_1667.syntax_only; ds_hooks = uu___184_1667.ds_hooks}))


let iface : env  ->  Prims.bool = (fun e -> e.iface)


let set_admitted_iface : env  ->  Prims.bool  ->  env = (fun e b -> (

let uu___185_1680 = e
in {curmodule = uu___185_1680.curmodule; curmonad = uu___185_1680.curmonad; modules = uu___185_1680.modules; scope_mods = uu___185_1680.scope_mods; exported_ids = uu___185_1680.exported_ids; trans_exported_ids = uu___185_1680.trans_exported_ids; includes = uu___185_1680.includes; sigaccum = uu___185_1680.sigaccum; sigmap = uu___185_1680.sigmap; iface = uu___185_1680.iface; admitted_iface = b; expect_typ = uu___185_1680.expect_typ; docs = uu___185_1680.docs; remaining_iface_decls = uu___185_1680.remaining_iface_decls; syntax_only = uu___185_1680.syntax_only; ds_hooks = uu___185_1680.ds_hooks}))


let admitted_iface : env  ->  Prims.bool = (fun e -> e.admitted_iface)


let set_expect_typ : env  ->  Prims.bool  ->  env = (fun e b -> (

let uu___186_1693 = e
in {curmodule = uu___186_1693.curmodule; curmonad = uu___186_1693.curmonad; modules = uu___186_1693.modules; scope_mods = uu___186_1693.scope_mods; exported_ids = uu___186_1693.exported_ids; trans_exported_ids = uu___186_1693.trans_exported_ids; includes = uu___186_1693.includes; sigaccum = uu___186_1693.sigaccum; sigmap = uu___186_1693.sigmap; iface = uu___186_1693.iface; admitted_iface = uu___186_1693.admitted_iface; expect_typ = b; docs = uu___186_1693.docs; remaining_iface_decls = uu___186_1693.remaining_iface_decls; syntax_only = uu___186_1693.syntax_only; ds_hooks = uu___186_1693.ds_hooks}))


let expect_typ : env  ->  Prims.bool = (fun e -> e.expect_typ)


let all_exported_id_kinds : exported_id_kind Prims.list = (Exported_id_field)::(Exported_id_term_type)::[]


let transitive_exported_ids : env  ->  FStar_Ident.lident  ->  Prims.string Prims.list = (fun env lid -> (

let module_name = (FStar_Ident.string_of_lid lid)
in (

let uu____1711 = (FStar_Util.smap_try_find env.trans_exported_ids module_name)
in (match (uu____1711) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (exported_id_set) -> begin
(

let uu____1717 = (

let uu____1718 = (exported_id_set Exported_id_term_type)
in (FStar_ST.op_Bang uu____1718))
in (FStar_All.pipe_right uu____1717 FStar_Util.set_elements))
end))))


let open_modules : env  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.modul) Prims.list = (fun e -> e.modules)


let open_modules_and_namespaces : env  ->  FStar_Ident.lident Prims.list = (fun env -> (FStar_List.filter_map (fun uu___153_1983 -> (match (uu___153_1983) with
| Open_module_or_namespace (lid, _info) -> begin
FStar_Pervasives_Native.Some (lid)
end
| uu____1988 -> begin
FStar_Pervasives_Native.None
end)) env.scope_mods))


let set_current_module : env  ->  FStar_Ident.lident  ->  env = (fun e l -> (

let uu___187_1997 = e
in {curmodule = FStar_Pervasives_Native.Some (l); curmonad = uu___187_1997.curmonad; modules = uu___187_1997.modules; scope_mods = uu___187_1997.scope_mods; exported_ids = uu___187_1997.exported_ids; trans_exported_ids = uu___187_1997.trans_exported_ids; includes = uu___187_1997.includes; sigaccum = uu___187_1997.sigaccum; sigmap = uu___187_1997.sigmap; iface = uu___187_1997.iface; admitted_iface = uu___187_1997.admitted_iface; expect_typ = uu___187_1997.expect_typ; docs = uu___187_1997.docs; remaining_iface_decls = uu___187_1997.remaining_iface_decls; syntax_only = uu___187_1997.syntax_only; ds_hooks = uu___187_1997.ds_hooks}))


let current_module : env  ->  FStar_Ident.lident = (fun env -> (match (env.curmodule) with
| FStar_Pervasives_Native.None -> begin
(failwith "Unset current module")
end
| FStar_Pervasives_Native.Some (m) -> begin
m
end))


let iface_decls : env  ->  FStar_Ident.lident  ->  FStar_Parser_AST.decl Prims.list FStar_Pervasives_Native.option = (fun env l -> (

let uu____2015 = (FStar_All.pipe_right env.remaining_iface_decls (FStar_List.tryFind (fun uu____2049 -> (match (uu____2049) with
| (m, uu____2057) -> begin
(FStar_Ident.lid_equals l m)
end))))
in (match (uu____2015) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (uu____2074, decls) -> begin
FStar_Pervasives_Native.Some (decls)
end)))


let set_iface_decls : env  ->  FStar_Ident.lident  ->  FStar_Parser_AST.decl Prims.list  ->  env = (fun env l ds -> (

let uu____2104 = (FStar_List.partition (fun uu____2134 -> (match (uu____2134) with
| (m, uu____2142) -> begin
(FStar_Ident.lid_equals l m)
end)) env.remaining_iface_decls)
in (match (uu____2104) with
| (uu____2147, rest) -> begin
(

let uu___188_2181 = env
in {curmodule = uu___188_2181.curmodule; curmonad = uu___188_2181.curmonad; modules = uu___188_2181.modules; scope_mods = uu___188_2181.scope_mods; exported_ids = uu___188_2181.exported_ids; trans_exported_ids = uu___188_2181.trans_exported_ids; includes = uu___188_2181.includes; sigaccum = uu___188_2181.sigaccum; sigmap = uu___188_2181.sigmap; iface = uu___188_2181.iface; admitted_iface = uu___188_2181.admitted_iface; expect_typ = uu___188_2181.expect_typ; docs = uu___188_2181.docs; remaining_iface_decls = (((l), (ds)))::rest; syntax_only = uu___188_2181.syntax_only; ds_hooks = uu___188_2181.ds_hooks})
end)))


let qual : FStar_Ident.lident  ->  FStar_Ident.ident  ->  FStar_Ident.lident = FStar_Syntax_Util.qual_id


let qualify : env  ->  FStar_Ident.ident  ->  FStar_Ident.lident = (fun env id -> (match (env.curmonad) with
| FStar_Pervasives_Native.None -> begin
(

let uu____2204 = (current_module env)
in (qual uu____2204 id))
end
| FStar_Pervasives_Native.Some (monad) -> begin
(

let uu____2206 = (

let uu____2207 = (current_module env)
in (qual uu____2207 monad))
in (FStar_Syntax_Util.mk_field_projector_name_from_ident uu____2206 id))
end))


let syntax_only : env  ->  Prims.bool = (fun env -> env.syntax_only)


let set_syntax_only : env  ->  Prims.bool  ->  env = (fun env b -> (

let uu___189_2220 = env
in {curmodule = uu___189_2220.curmodule; curmonad = uu___189_2220.curmonad; modules = uu___189_2220.modules; scope_mods = uu___189_2220.scope_mods; exported_ids = uu___189_2220.exported_ids; trans_exported_ids = uu___189_2220.trans_exported_ids; includes = uu___189_2220.includes; sigaccum = uu___189_2220.sigaccum; sigmap = uu___189_2220.sigmap; iface = uu___189_2220.iface; admitted_iface = uu___189_2220.admitted_iface; expect_typ = uu___189_2220.expect_typ; docs = uu___189_2220.docs; remaining_iface_decls = uu___189_2220.remaining_iface_decls; syntax_only = b; ds_hooks = uu___189_2220.ds_hooks}))


let ds_hooks : env  ->  dsenv_hooks = (fun env -> env.ds_hooks)


let set_ds_hooks : env  ->  dsenv_hooks  ->  env = (fun env hooks -> (

let uu___190_2233 = env
in {curmodule = uu___190_2233.curmodule; curmonad = uu___190_2233.curmonad; modules = uu___190_2233.modules; scope_mods = uu___190_2233.scope_mods; exported_ids = uu___190_2233.exported_ids; trans_exported_ids = uu___190_2233.trans_exported_ids; includes = uu___190_2233.includes; sigaccum = uu___190_2233.sigaccum; sigmap = uu___190_2233.sigmap; iface = uu___190_2233.iface; admitted_iface = uu___190_2233.admitted_iface; expect_typ = uu___190_2233.expect_typ; docs = uu___190_2233.docs; remaining_iface_decls = uu___190_2233.remaining_iface_decls; syntax_only = uu___190_2233.syntax_only; ds_hooks = hooks}))


let new_sigmap : 'Auu____2238 . Prims.unit  ->  'Auu____2238 FStar_Util.smap = (fun uu____2244 -> (FStar_Util.smap_create (Prims.parse_int "100")))


let empty_env : Prims.unit  ->  env = (fun uu____2248 -> (

let uu____2249 = (new_sigmap ())
in (

let uu____2252 = (new_sigmap ())
in (

let uu____2255 = (new_sigmap ())
in (

let uu____2266 = (new_sigmap ())
in (

let uu____2277 = (new_sigmap ())
in {curmodule = FStar_Pervasives_Native.None; curmonad = FStar_Pervasives_Native.None; modules = []; scope_mods = []; exported_ids = uu____2249; trans_exported_ids = uu____2252; includes = uu____2255; sigaccum = []; sigmap = uu____2266; iface = false; admitted_iface = false; expect_typ = false; docs = uu____2277; remaining_iface_decls = []; syntax_only = false; ds_hooks = default_ds_hooks}))))))


let sigmap : env  ->  (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap = (fun env -> env.sigmap)


let has_all_in_scope : env  ->  Prims.bool = (fun env -> (FStar_List.existsb (fun uu____2311 -> (match (uu____2311) with
| (m, uu____2317) -> begin
(FStar_Ident.lid_equals m FStar_Parser_Const.all_lid)
end)) env.modules))


let set_bv_range : FStar_Syntax_Syntax.bv  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.bv = (fun bv r -> (

let id = (

let uu___191_2327 = bv.FStar_Syntax_Syntax.ppname
in {FStar_Ident.idText = uu___191_2327.FStar_Ident.idText; FStar_Ident.idRange = r})
in (

let uu___192_2328 = bv
in {FStar_Syntax_Syntax.ppname = id; FStar_Syntax_Syntax.index = uu___192_2328.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu___192_2328.FStar_Syntax_Syntax.sort})))


let bv_to_name : FStar_Syntax_Syntax.bv  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.term = (fun bv r -> (FStar_Syntax_Syntax.bv_to_name (set_bv_range bv r)))


let unmangleMap : (Prims.string * Prims.string * FStar_Syntax_Syntax.delta_depth * FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option) Prims.list = ((("op_ColonColon"), ("Cons"), (FStar_Syntax_Syntax.Delta_constant), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor))))::((("not"), ("op_Negation"), (FStar_Syntax_Syntax.Delta_equational), (FStar_Pervasives_Native.None)))::[]


let unmangleOpName : FStar_Ident.ident  ->  (FStar_Syntax_Syntax.term * Prims.bool) FStar_Pervasives_Native.option = (fun id -> (

let t = (FStar_Util.find_map unmangleMap (fun uu____2418 -> (match (uu____2418) with
| (x, y, dd, dq) -> begin
(match ((Prims.op_Equality id.FStar_Ident.idText x)) with
| true -> begin
(

let uu____2441 = (

let uu____2442 = (FStar_Ident.lid_of_path (("Prims")::(y)::[]) id.FStar_Ident.idRange)
in (FStar_Syntax_Syntax.fvar uu____2442 dd dq))
in FStar_Pervasives_Native.Some (uu____2441))
end
| uu____2443 -> begin
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
| uu____2487 -> begin
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
| uu____2520 -> begin
false
end))


let uu___is_Cont_ignore : 'a . 'a cont_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Cont_ignore -> begin
true
end
| uu____2536 -> begin
false
end))


let option_of_cont : 'a . (Prims.unit  ->  'a FStar_Pervasives_Native.option)  ->  'a cont_t  ->  'a FStar_Pervasives_Native.option = (fun k_ignore uu___154_2562 -> (match (uu___154_2562) with
| Cont_ok (a) -> begin
FStar_Pervasives_Native.Some (a)
end
| Cont_fail -> begin
FStar_Pervasives_Native.None
end
| Cont_ignore -> begin
(k_ignore ())
end))


let find_in_record : 'Auu____2580 . FStar_Ident.ident Prims.list  ->  FStar_Ident.ident  ->  record_or_dc  ->  (record_or_dc  ->  'Auu____2580 cont_t)  ->  'Auu____2580 cont_t = (fun ns id record cont -> (

let typename' = (FStar_Ident.lid_of_ids (FStar_List.append ns ((record.typename.FStar_Ident.ident)::[])))
in (match ((FStar_Ident.lid_equals typename' record.typename)) with
| true -> begin
(

let fname = (FStar_Ident.lid_of_ids (FStar_List.append record.typename.FStar_Ident.ns ((id)::[])))
in (

let find1 = (FStar_Util.find_map record.fields (fun uu____2626 -> (match (uu____2626) with
| (f, uu____2634) -> begin
(match ((Prims.op_Equality id.FStar_Ident.idText f.FStar_Ident.idText)) with
| true -> begin
FStar_Pervasives_Native.Some (record)
end
| uu____2637 -> begin
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
| uu____2641 -> begin
Cont_ignore
end)))


let get_exported_id_set : env  ->  Prims.string  ->  (exported_id_kind  ->  string_set FStar_ST.ref) FStar_Pervasives_Native.option = (fun e mname -> (FStar_Util.smap_try_find e.exported_ids mname))


let get_trans_exported_id_set : env  ->  Prims.string  ->  (exported_id_kind  ->  string_set FStar_ST.ref) FStar_Pervasives_Native.option = (fun e mname -> (FStar_Util.smap_try_find e.trans_exported_ids mname))


let string_of_exported_id_kind : exported_id_kind  ->  Prims.string = (fun uu___155_2685 -> (match (uu___155_2685) with
| Exported_id_field -> begin
"field"
end
| Exported_id_term_type -> begin
"term/type"
end))


let find_in_module_with_includes : 'a . exported_id_kind  ->  (FStar_Ident.lident  ->  'a cont_t)  ->  'a cont_t  ->  env  ->  FStar_Ident.lident  ->  FStar_Ident.ident  ->  'a cont_t = (fun eikind find_in_module find_in_module_default env ns id -> (

let idstr = id.FStar_Ident.idText
in (

let rec aux = (fun uu___156_2748 -> (match (uu___156_2748) with
| [] -> begin
find_in_module_default
end
| (modul)::q -> begin
(

let mname = modul.FStar_Ident.str
in (

let not_shadowed = (

let uu____2759 = (get_exported_id_set env mname)
in (match (uu____2759) with
| FStar_Pervasives_Native.None -> begin
true
end
| FStar_Pervasives_Native.Some (mex) -> begin
(

let mexports = (

let uu____2780 = (mex eikind)
in (FStar_ST.op_Bang uu____2780))
in (FStar_Util.set_mem idstr mexports))
end))
in (

let mincludes = (

let uu____3027 = (FStar_Util.smap_try_find env.includes mname)
in (match (uu____3027) with
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

let uu____3122 = (qual modul id)
in (find_in_module uu____3122))
end
| uu____3123 -> begin
Cont_ignore
end)
in (match (look_into) with
| Cont_ignore -> begin
(aux (FStar_List.append mincludes q))
end
| uu____3126 -> begin
look_into
end)))))
end))
in (aux ((ns)::[])))))


let is_exported_id_field : exported_id_kind  ->  Prims.bool = (fun uu___157_3132 -> (match (uu___157_3132) with
| Exported_id_field -> begin
true
end
| uu____3133 -> begin
false
end))


let try_lookup_id'' : 'a . env  ->  FStar_Ident.ident  ->  exported_id_kind  ->  (local_binding  ->  'a cont_t)  ->  (rec_binding  ->  'a cont_t)  ->  (record_or_dc  ->  'a cont_t)  ->  (FStar_Ident.lident  ->  'a cont_t)  ->  ('a cont_t  ->  FStar_Ident.ident  ->  'a cont_t)  ->  'a FStar_Pervasives_Native.option = (fun env id eikind k_local_binding k_rec_binding k_record find_in_module lookup_default_id -> (

let check_local_binding_id = (fun uu___158_3244 -> (match (uu___158_3244) with
| (id', uu____3246, uu____3247) -> begin
(Prims.op_Equality id'.FStar_Ident.idText id.FStar_Ident.idText)
end))
in (

let check_rec_binding_id = (fun uu___159_3251 -> (match (uu___159_3251) with
| (id', uu____3253, uu____3254) -> begin
(Prims.op_Equality id'.FStar_Ident.idText id.FStar_Ident.idText)
end))
in (

let curmod_ns = (

let uu____3258 = (current_module env)
in (FStar_Ident.ids_of_lid uu____3258))
in (

let proc = (fun uu___160_3264 -> (match (uu___160_3264) with
| Local_binding (l) when (check_local_binding_id l) -> begin
(k_local_binding l)
end
| Rec_binding (r) when (check_rec_binding_id r) -> begin
(k_rec_binding r)
end
| Open_module_or_namespace (ns, Open_module) -> begin
(find_in_module_with_includes eikind find_in_module Cont_ignore env ns id)
end
| Top_level_def (id') when (Prims.op_Equality id'.FStar_Ident.idText id.FStar_Ident.idText) -> begin
(lookup_default_id Cont_ignore id)
end
| Record_or_dc (r) when (is_exported_id_field eikind) -> begin
(

let uu____3272 = (FStar_Ident.lid_of_ids curmod_ns)
in (find_in_module_with_includes Exported_id_field (fun lid -> (

let id1 = lid.FStar_Ident.ident
in (find_in_record lid.FStar_Ident.ns id1 r k_record))) Cont_ignore env uu____3272 id))
end
| uu____3277 -> begin
Cont_ignore
end))
in (

let rec aux = (fun uu___161_3285 -> (match (uu___161_3285) with
| (a)::q -> begin
(

let uu____3294 = (proc a)
in (option_of_cont (fun uu____3298 -> (aux q)) uu____3294))
end
| [] -> begin
(

let uu____3299 = (lookup_default_id Cont_fail id)
in (option_of_cont (fun uu____3303 -> FStar_Pervasives_Native.None) uu____3299))
end))
in (aux env.scope_mods)))))))


let found_local_binding : 'Auu____3312 'Auu____3313 . FStar_Range.range  ->  ('Auu____3313 * FStar_Syntax_Syntax.bv * 'Auu____3312)  ->  (FStar_Syntax_Syntax.term * 'Auu____3312) = (fun r uu____3331 -> (match (uu____3331) with
| (id', x, mut) -> begin
(

let uu____3341 = (bv_to_name x r)
in ((uu____3341), (mut)))
end))


let find_in_module : 'Auu____3352 . env  ->  FStar_Ident.lident  ->  (FStar_Ident.lident  ->  (FStar_Syntax_Syntax.sigelt * Prims.bool)  ->  'Auu____3352)  ->  'Auu____3352  ->  'Auu____3352 = (fun env lid k_global_def k_not_found -> (

let uu____3387 = (FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str)
in (match (uu____3387) with
| FStar_Pervasives_Native.Some (sb) -> begin
(k_global_def lid sb)
end
| FStar_Pervasives_Native.None -> begin
k_not_found
end)))


let try_lookup_id : env  ->  FStar_Ident.ident  ->  (FStar_Syntax_Syntax.term * Prims.bool) FStar_Pervasives_Native.option = (fun env id -> (

let uu____3425 = (unmangleOpName id)
in (match (uu____3425) with
| FStar_Pervasives_Native.Some (f) -> begin
FStar_Pervasives_Native.Some (f)
end
| uu____3451 -> begin
(try_lookup_id'' env id Exported_id_term_type (fun r -> (

let uu____3465 = (found_local_binding id.FStar_Ident.idRange r)
in Cont_ok (uu____3465))) (fun uu____3475 -> Cont_fail) (fun uu____3481 -> Cont_ignore) (fun i -> (find_in_module env i (fun uu____3496 uu____3497 -> Cont_fail) Cont_ignore)) (fun uu____3512 uu____3513 -> Cont_fail))
end)))


let lookup_default_id : 'a . env  ->  FStar_Ident.ident  ->  (FStar_Ident.lident  ->  (FStar_Syntax_Syntax.sigelt * Prims.bool)  ->  'a cont_t)  ->  'a cont_t  ->  'a cont_t = (fun env id k_global_def k_not_found -> (

let find_in_monad = (match (env.curmonad) with
| FStar_Pervasives_Native.Some (uu____3588) -> begin
(

let lid = (qualify env id)
in (

let uu____3590 = (FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str)
in (match (uu____3590) with
| FStar_Pervasives_Native.Some (r) -> begin
(

let uu____3614 = (k_global_def lid r)
in FStar_Pervasives_Native.Some (uu____3614))
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

let uu____3637 = (current_module env)
in (qual uu____3637 id))
in (find_in_module env lid k_global_def k_not_found))
end)))


let module_is_defined : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> ((match (env.curmodule) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (m) -> begin
(

let uu____3649 = (current_module env)
in (FStar_Ident.lid_equals lid uu____3649))
end) || (FStar_List.existsb (fun x -> (FStar_Ident.lid_equals lid (FStar_Pervasives_Native.fst x))) env.modules)))


let resolve_module_name : env  ->  FStar_Ident.lident  ->  Prims.bool  ->  FStar_Ident.lident FStar_Pervasives_Native.option = (fun env lid honor_ns -> (

let nslen = (FStar_List.length lid.FStar_Ident.ns)
in (

let rec aux = (fun uu___162_3684 -> (match (uu___162_3684) with
| [] -> begin
(

let uu____3689 = (module_is_defined env lid)
in (match (uu____3689) with
| true -> begin
FStar_Pervasives_Native.Some (lid)
end
| uu____3692 -> begin
FStar_Pervasives_Native.None
end))
end
| (Open_module_or_namespace (ns, Open_namespace))::q when honor_ns -> begin
(

let new_lid = (

let uu____3698 = (

let uu____3701 = (FStar_Ident.path_of_lid ns)
in (

let uu____3704 = (FStar_Ident.path_of_lid lid)
in (FStar_List.append uu____3701 uu____3704)))
in (FStar_Ident.lid_of_path uu____3698 (FStar_Ident.range_of_lid lid)))
in (

let uu____3707 = (module_is_defined env new_lid)
in (match (uu____3707) with
| true -> begin
FStar_Pervasives_Native.Some (new_lid)
end
| uu____3710 -> begin
(aux q)
end)))
end
| (Module_abbrev (name, modul))::uu____3713 when ((Prims.op_Equality nslen (Prims.parse_int "0")) && (Prims.op_Equality name.FStar_Ident.idText lid.FStar_Ident.ident.FStar_Ident.idText)) -> begin
FStar_Pervasives_Native.Some (modul)
end
| (uu____3720)::q -> begin
(aux q)
end))
in (aux env.scope_mods))))


let fail_if_curmodule : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  Prims.unit = (fun env ns_original ns_resolved -> (

let uu____3736 = (

let uu____3737 = (current_module env)
in (FStar_Ident.lid_equals ns_resolved uu____3737))
in (match (uu____3736) with
| true -> begin
(match ((FStar_Ident.lid_equals ns_resolved FStar_Parser_Const.prims_lid)) with
| true -> begin
()
end
| uu____3738 -> begin
(

let uu____3739 = (

let uu____3740 = (

let uu____3745 = (FStar_Util.format1 "Reference %s to current module is forbidden (see GitHub issue #451)" ns_original.FStar_Ident.str)
in ((uu____3745), ((FStar_Ident.range_of_lid ns_original))))
in FStar_Errors.Error (uu____3740))
in (FStar_Exn.raise uu____3739))
end)
end
| uu____3746 -> begin
()
end)))


let fail_if_qualified_by_curmodule : env  ->  FStar_Ident.lident  ->  Prims.unit = (fun env lid -> (match (lid.FStar_Ident.ns) with
| [] -> begin
()
end
| uu____3755 -> begin
(

let modul_orig = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in (

let uu____3759 = (resolve_module_name env modul_orig true)
in (match (uu____3759) with
| FStar_Pervasives_Native.Some (modul_res) -> begin
(fail_if_curmodule env modul_orig modul_res)
end
| uu____3763 -> begin
()
end)))
end))


let namespace_is_open : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (FStar_List.existsb (fun uu___163_3776 -> (match (uu___163_3776) with
| Open_module_or_namespace (ns, Open_namespace) -> begin
(FStar_Ident.lid_equals lid ns)
end
| uu____3778 -> begin
false
end)) env.scope_mods))


let shorten_module_path : env  ->  FStar_Ident.ident Prims.list  ->  Prims.bool  ->  (FStar_Ident.ident Prims.list * FStar_Ident.ident Prims.list) = (fun env ids is_full_path -> (

let rec aux = (fun revns id -> (

let lid = (FStar_Ident.lid_of_ns_and_id (FStar_List.rev revns) id)
in (match ((namespace_is_open env lid)) with
| true -> begin
FStar_Pervasives_Native.Some ((((FStar_List.rev ((id)::revns))), ([])))
end
| uu____3847 -> begin
(match (revns) with
| [] -> begin
FStar_Pervasives_Native.None
end
| (ns_last_id)::rev_ns_prefix -> begin
(

let uu____3870 = (aux rev_ns_prefix ns_last_id)
in (FStar_All.pipe_right uu____3870 (FStar_Util.map_option (fun uu____3920 -> (match (uu____3920) with
| (stripped_ids, rev_kept_ids) -> begin
((stripped_ids), ((id)::rev_kept_ids))
end)))))
end)
end)))
in (

let uu____3951 = (is_full_path && (

let uu____3953 = (FStar_Ident.lid_of_ids ids)
in (module_is_defined env uu____3953)))
in (match (uu____3951) with
| true -> begin
((ids), ([]))
end
| uu____3966 -> begin
(match ((FStar_List.rev ids)) with
| [] -> begin
(([]), ([]))
end
| (ns_last_id)::ns_rev_prefix -> begin
(

let uu____3983 = (aux ns_rev_prefix ns_last_id)
in (match (uu____3983) with
| FStar_Pervasives_Native.None -> begin
(([]), (ids))
end
| FStar_Pervasives_Native.Some (stripped_ids, rev_kept_ids) -> begin
((stripped_ids), ((FStar_List.rev rev_kept_ids)))
end))
end)
end))))


let shorten_lid : env  ->  FStar_Ident.lid  ->  FStar_Ident.lid = (fun env lid -> (

let uu____4044 = (shorten_module_path env lid.FStar_Ident.ns true)
in (match (uu____4044) with
| (uu____4053, short) -> begin
(FStar_Ident.lid_of_ns_and_id short lid.FStar_Ident.ident)
end)))


let resolve_in_open_namespaces'' : 'a . env  ->  FStar_Ident.lident  ->  exported_id_kind  ->  (local_binding  ->  'a cont_t)  ->  (rec_binding  ->  'a cont_t)  ->  (record_or_dc  ->  'a cont_t)  ->  (FStar_Ident.lident  ->  'a cont_t)  ->  ('a cont_t  ->  FStar_Ident.ident  ->  'a cont_t)  ->  'a FStar_Pervasives_Native.option = (fun env lid eikind k_local_binding k_rec_binding k_record f_module l_default -> (match (lid.FStar_Ident.ns) with
| (uu____4170)::uu____4171 -> begin
(

let uu____4174 = (

let uu____4177 = (

let uu____4178 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in (FStar_Ident.set_lid_range uu____4178 (FStar_Ident.range_of_lid lid)))
in (resolve_module_name env uu____4177 true))
in (match (uu____4174) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (modul) -> begin
(

let uu____4182 = (find_in_module_with_includes eikind f_module Cont_fail env modul lid.FStar_Ident.ident)
in (option_of_cont (fun uu____4186 -> FStar_Pervasives_Native.None) uu____4182))
end))
end
| [] -> begin
(try_lookup_id'' env lid.FStar_Ident.ident eikind k_local_binding k_rec_binding k_record f_module l_default)
end))


let cont_of_option : 'a . 'a cont_t  ->  'a FStar_Pervasives_Native.option  ->  'a cont_t = (fun k_none uu___164_4207 -> (match (uu___164_4207) with
| FStar_Pervasives_Native.Some (v1) -> begin
Cont_ok (v1)
end
| FStar_Pervasives_Native.None -> begin
k_none
end))


let resolve_in_open_namespaces' : 'a . env  ->  FStar_Ident.lident  ->  (local_binding  ->  'a FStar_Pervasives_Native.option)  ->  (rec_binding  ->  'a FStar_Pervasives_Native.option)  ->  (FStar_Ident.lident  ->  (FStar_Syntax_Syntax.sigelt * Prims.bool)  ->  'a FStar_Pervasives_Native.option)  ->  'a FStar_Pervasives_Native.option = (fun env lid k_local_binding k_rec_binding k_global_def -> (

let k_global_def' = (fun k lid1 def -> (

let uu____4312 = (k_global_def lid1 def)
in (cont_of_option k uu____4312)))
in (

let f_module = (fun lid' -> (

let k = Cont_ignore
in (find_in_module env lid' (k_global_def' k) k)))
in (

let l_default = (fun k i -> (lookup_default_id env i (k_global_def' k) k))
in (resolve_in_open_namespaces'' env lid Exported_id_term_type (fun l -> (

let uu____4342 = (k_local_binding l)
in (cont_of_option Cont_fail uu____4342))) (fun r -> (

let uu____4348 = (k_rec_binding r)
in (cont_of_option Cont_fail uu____4348))) (fun uu____4352 -> Cont_ignore) f_module l_default)))))


let fv_qual_of_se : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option = (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (uu____4361, uu____4362, uu____4363, l, uu____4365, uu____4366) -> begin
(

let qopt = (FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals (fun uu___165_4377 -> (match (uu___165_4377) with
| FStar_Syntax_Syntax.RecordConstructor (uu____4380, fs) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (((l), (fs))))
end
| uu____4392 -> begin
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
| FStar_Syntax_Syntax.Sig_declare_typ (uu____4398, uu____4399, uu____4400) -> begin
FStar_Pervasives_Native.None
end
| uu____4401 -> begin
FStar_Pervasives_Native.None
end))


let lb_fv : FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.fv = (fun lbs lid -> (

let uu____4414 = (FStar_Util.find_map lbs (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let uu____4422 = (FStar_Syntax_Syntax.fv_eq_lid fv lid)
in (match (uu____4422) with
| true -> begin
FStar_Pervasives_Native.Some (fv)
end
| uu____4425 -> begin
FStar_Pervasives_Native.None
end)))))
in (FStar_All.pipe_right uu____4414 FStar_Util.must)))


let ns_of_lid_equals : FStar_Ident.lident  ->  FStar_Ident.lident  ->  Prims.bool = (fun lid ns -> ((Prims.op_Equality (FStar_List.length lid.FStar_Ident.ns) (FStar_List.length (FStar_Ident.ids_of_lid ns))) && (

let uu____4437 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in (FStar_Ident.lid_equals uu____4437 ns))))


let try_lookup_name : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  foundname FStar_Pervasives_Native.option = (fun any_val exclude_interf env lid -> (

let occurrence_range = (FStar_Ident.range_of_lid lid)
in (

let k_global_def = (fun source_lid uu___169_4471 -> (match (uu___169_4471) with
| (uu____4478, true) when exclude_interf -> begin
FStar_Pervasives_Native.None
end
| (se, uu____4480) -> begin
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____4483) -> begin
(

let uu____4500 = (

let uu____4501 = (

let uu____4506 = (FStar_Syntax_Syntax.fvar source_lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in ((uu____4506), (false)))
in Term_name (uu____4501))
in FStar_Pervasives_Native.Some (uu____4500))
end
| FStar_Syntax_Syntax.Sig_datacon (uu____4507) -> begin
(

let uu____4522 = (

let uu____4523 = (

let uu____4528 = (

let uu____4529 = (fv_qual_of_se se)
in (FStar_Syntax_Syntax.fvar source_lid FStar_Syntax_Syntax.Delta_constant uu____4529))
in ((uu____4528), (false)))
in Term_name (uu____4523))
in FStar_Pervasives_Native.Some (uu____4522))
end
| FStar_Syntax_Syntax.Sig_let ((uu____4532, lbs), uu____4534) -> begin
(

let fv = (lb_fv lbs source_lid)
in (

let uu____4550 = (

let uu____4551 = (

let uu____4556 = (FStar_Syntax_Syntax.fvar source_lid fv.FStar_Syntax_Syntax.fv_delta fv.FStar_Syntax_Syntax.fv_qual)
in ((uu____4556), (false)))
in Term_name (uu____4551))
in FStar_Pervasives_Native.Some (uu____4550)))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid1, uu____4558, uu____4559) -> begin
(

let quals = se.FStar_Syntax_Syntax.sigquals
in (

let uu____4563 = (any_val || (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___166_4567 -> (match (uu___166_4567) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| uu____4568 -> begin
false
end)))))
in (match (uu____4563) with
| true -> begin
(

let lid2 = (FStar_Ident.set_lid_range lid1 (FStar_Ident.range_of_lid source_lid))
in (

let dd = (

let uu____4573 = ((FStar_Syntax_Util.is_primop_lid lid2) || (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___167_4578 -> (match (uu___167_4578) with
| FStar_Syntax_Syntax.Projector (uu____4579) -> begin
true
end
| FStar_Syntax_Syntax.Discriminator (uu____4584) -> begin
true
end
| uu____4585 -> begin
false
end)))))
in (match (uu____4573) with
| true -> begin
FStar_Syntax_Syntax.Delta_equational
end
| uu____4586 -> begin
FStar_Syntax_Syntax.Delta_constant
end))
in (

let uu____4587 = (FStar_Util.find_map quals (fun uu___168_4592 -> (match (uu___168_4592) with
| FStar_Syntax_Syntax.Reflectable (refl_monad) -> begin
FStar_Pervasives_Native.Some (refl_monad)
end
| uu____4596 -> begin
FStar_Pervasives_Native.None
end)))
in (match (uu____4587) with
| FStar_Pervasives_Native.Some (refl_monad) -> begin
(

let refl_const = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (refl_monad))) FStar_Pervasives_Native.None occurrence_range)
in FStar_Pervasives_Native.Some (Term_name (((refl_const), (false)))))
end
| uu____4605 -> begin
(

let uu____4608 = (

let uu____4609 = (

let uu____4614 = (

let uu____4615 = (fv_qual_of_se se)
in (FStar_Syntax_Syntax.fvar lid2 dd uu____4615))
in ((uu____4614), (false)))
in Term_name (uu____4609))
in FStar_Pervasives_Native.Some (uu____4608))
end))))
end
| uu____4618 -> begin
FStar_Pervasives_Native.None
end)))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (ne) -> begin
FStar_Pervasives_Native.Some (Eff_name (((se), ((FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname (FStar_Ident.range_of_lid source_lid))))))
end
| FStar_Syntax_Syntax.Sig_new_effect (ne) -> begin
FStar_Pervasives_Native.Some (Eff_name (((se), ((FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname (FStar_Ident.range_of_lid source_lid))))))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (uu____4621) -> begin
FStar_Pervasives_Native.Some (Eff_name (((se), (source_lid))))
end
| uu____4634 -> begin
FStar_Pervasives_Native.None
end)
end))
in (

let k_local_binding = (fun r -> (

let uu____4653 = (

let uu____4654 = (found_local_binding (FStar_Ident.range_of_lid lid) r)
in Term_name (uu____4654))
in FStar_Pervasives_Native.Some (uu____4653)))
in (

let k_rec_binding = (fun uu____4670 -> (match (uu____4670) with
| (id, l, dd) -> begin
(

let uu____4682 = (

let uu____4683 = (

let uu____4688 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range l (FStar_Ident.range_of_lid lid)) dd FStar_Pervasives_Native.None)
in ((uu____4688), (false)))
in Term_name (uu____4683))
in FStar_Pervasives_Native.Some (uu____4682))
end))
in (

let found_unmangled = (match (lid.FStar_Ident.ns) with
| [] -> begin
(

let uu____4694 = (unmangleOpName lid.FStar_Ident.ident)
in (match (uu____4694) with
| FStar_Pervasives_Native.Some (f) -> begin
FStar_Pervasives_Native.Some (Term_name (f))
end
| uu____4712 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____4719 -> begin
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

let uu____4751 = (try_lookup_name true exclude_interf env lid)
in (match (uu____4751) with
| FStar_Pervasives_Native.Some (Eff_name (o, l)) -> begin
FStar_Pervasives_Native.Some (((o), (l)))
end
| uu____4766 -> begin
FStar_Pervasives_Native.None
end)))


let try_lookup_effect_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident FStar_Pervasives_Native.option = (fun env l -> (

let uu____4783 = (try_lookup_effect_name' (not (env.iface)) env l)
in (match (uu____4783) with
| FStar_Pervasives_Native.Some (o, l1) -> begin
FStar_Pervasives_Native.Some (l1)
end
| uu____4798 -> begin
FStar_Pervasives_Native.None
end)))


let try_lookup_effect_name_and_attributes : env  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.cflags Prims.list) FStar_Pervasives_Native.option = (fun env l -> (

let uu____4821 = (try_lookup_effect_name' (not (env.iface)) env l)
in (match (uu____4821) with
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect (ne); FStar_Syntax_Syntax.sigrng = uu____4837; FStar_Syntax_Syntax.sigquals = uu____4838; FStar_Syntax_Syntax.sigmeta = uu____4839; FStar_Syntax_Syntax.sigattrs = uu____4840}, l1) -> begin
FStar_Pervasives_Native.Some (((l1), (ne.FStar_Syntax_Syntax.cattributes)))
end
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect_for_free (ne); FStar_Syntax_Syntax.sigrng = uu____4859; FStar_Syntax_Syntax.sigquals = uu____4860; FStar_Syntax_Syntax.sigmeta = uu____4861; FStar_Syntax_Syntax.sigattrs = uu____4862}, l1) -> begin
FStar_Pervasives_Native.Some (((l1), (ne.FStar_Syntax_Syntax.cattributes)))
end
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_effect_abbrev (uu____4880, uu____4881, uu____4882, uu____4883, cattributes); FStar_Syntax_Syntax.sigrng = uu____4885; FStar_Syntax_Syntax.sigquals = uu____4886; FStar_Syntax_Syntax.sigmeta = uu____4887; FStar_Syntax_Syntax.sigattrs = uu____4888}, l1) -> begin
FStar_Pervasives_Native.Some (((l1), (cattributes)))
end
| uu____4910 -> begin
FStar_Pervasives_Native.None
end)))


let try_lookup_effect_defn : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl FStar_Pervasives_Native.option = (fun env l -> (

let uu____4933 = (try_lookup_effect_name' (not (env.iface)) env l)
in (match (uu____4933) with
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect (ne); FStar_Syntax_Syntax.sigrng = uu____4943; FStar_Syntax_Syntax.sigquals = uu____4944; FStar_Syntax_Syntax.sigmeta = uu____4945; FStar_Syntax_Syntax.sigattrs = uu____4946}, uu____4947) -> begin
FStar_Pervasives_Native.Some (ne)
end
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect_for_free (ne); FStar_Syntax_Syntax.sigrng = uu____4957; FStar_Syntax_Syntax.sigquals = uu____4958; FStar_Syntax_Syntax.sigmeta = uu____4959; FStar_Syntax_Syntax.sigattrs = uu____4960}, uu____4961) -> begin
FStar_Pervasives_Native.Some (ne)
end
| uu____4970 -> begin
FStar_Pervasives_Native.None
end)))


let is_effect_name : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let uu____4985 = (try_lookup_effect_name env lid)
in (match (uu____4985) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (uu____4988) -> begin
true
end)))


let try_lookup_root_effect_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident FStar_Pervasives_Native.option = (fun env l -> (

let uu____4999 = (try_lookup_effect_name' (not (env.iface)) env l)
in (match (uu____4999) with
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_effect_abbrev (l', uu____5009, uu____5010, uu____5011, uu____5012); FStar_Syntax_Syntax.sigrng = uu____5013; FStar_Syntax_Syntax.sigquals = uu____5014; FStar_Syntax_Syntax.sigmeta = uu____5015; FStar_Syntax_Syntax.sigattrs = uu____5016}, uu____5017) -> begin
(

let rec aux = (fun new_name -> (

let uu____5036 = (FStar_Util.smap_try_find (sigmap env) new_name.FStar_Ident.str)
in (match (uu____5036) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (s, uu____5054) -> begin
(match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_new_effect_for_free (ne) -> begin
FStar_Pervasives_Native.Some ((FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname (FStar_Ident.range_of_lid l)))
end
| FStar_Syntax_Syntax.Sig_new_effect (ne) -> begin
FStar_Pervasives_Native.Some ((FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname (FStar_Ident.range_of_lid l)))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (uu____5063, uu____5064, uu____5065, cmp, uu____5067) -> begin
(

let l'' = (FStar_Syntax_Util.comp_effect_name cmp)
in (aux l''))
end
| uu____5073 -> begin
FStar_Pervasives_Native.None
end)
end)))
in (aux l'))
end
| FStar_Pervasives_Native.Some (uu____5074, l') -> begin
FStar_Pervasives_Native.Some (l')
end
| uu____5080 -> begin
FStar_Pervasives_Native.None
end)))


let lookup_letbinding_quals : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.qualifier Prims.list = (fun env lid -> (

let k_global_def = (fun lid1 uu___170_5111 -> (match (uu___170_5111) with
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (uu____5120, uu____5121, uu____5122); FStar_Syntax_Syntax.sigrng = uu____5123; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = uu____5125; FStar_Syntax_Syntax.sigattrs = uu____5126}, uu____5127) -> begin
FStar_Pervasives_Native.Some (quals)
end
| uu____5134 -> begin
FStar_Pervasives_Native.None
end))
in (

let uu____5141 = (resolve_in_open_namespaces' env lid (fun uu____5149 -> FStar_Pervasives_Native.None) (fun uu____5153 -> FStar_Pervasives_Native.None) k_global_def)
in (match (uu____5141) with
| FStar_Pervasives_Native.Some (quals) -> begin
quals
end
| uu____5163 -> begin
[]
end))))


let try_lookup_module : env  ->  Prims.string Prims.list  ->  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option = (fun env path -> (

let uu____5182 = (FStar_List.tryFind (fun uu____5197 -> (match (uu____5197) with
| (mlid, modul) -> begin
(

let uu____5204 = (FStar_Ident.path_of_lid mlid)
in (Prims.op_Equality uu____5204 path))
end)) env.modules)
in (match (uu____5182) with
| FStar_Pervasives_Native.Some (uu____5211, modul) -> begin
FStar_Pervasives_Native.Some (modul)
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end)))


let try_lookup_let : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun env lid -> (

let k_global_def = (fun lid1 uu___171_5243 -> (match (uu___171_5243) with
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let ((uu____5250, lbs), uu____5252); FStar_Syntax_Syntax.sigrng = uu____5253; FStar_Syntax_Syntax.sigquals = uu____5254; FStar_Syntax_Syntax.sigmeta = uu____5255; FStar_Syntax_Syntax.sigattrs = uu____5256}, uu____5257) -> begin
(

let fv = (lb_fv lbs lid1)
in (

let uu____5277 = (FStar_Syntax_Syntax.fvar lid1 fv.FStar_Syntax_Syntax.fv_delta fv.FStar_Syntax_Syntax.fv_qual)
in FStar_Pervasives_Native.Some (uu____5277)))
end
| uu____5278 -> begin
FStar_Pervasives_Native.None
end))
in (resolve_in_open_namespaces' env lid (fun uu____5284 -> FStar_Pervasives_Native.None) (fun uu____5286 -> FStar_Pervasives_Native.None) k_global_def)))


let try_lookup_definition : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun env lid -> (

let k_global_def = (fun lid1 uu___172_5311 -> (match (uu___172_5311) with
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (lbs, uu____5321); FStar_Syntax_Syntax.sigrng = uu____5322; FStar_Syntax_Syntax.sigquals = uu____5323; FStar_Syntax_Syntax.sigmeta = uu____5324; FStar_Syntax_Syntax.sigattrs = uu____5325}, uu____5326) -> begin
(FStar_Util.find_map (FStar_Pervasives_Native.snd lbs) (fun lb -> (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv lid1) -> begin
FStar_Pervasives_Native.Some (lb.FStar_Syntax_Syntax.lbdef)
end
| uu____5349 -> begin
FStar_Pervasives_Native.None
end)))
end
| uu____5356 -> begin
FStar_Pervasives_Native.None
end))
in (resolve_in_open_namespaces' env lid (fun uu____5366 -> FStar_Pervasives_Native.None) (fun uu____5370 -> FStar_Pervasives_Native.None) k_global_def)))


let empty_include_smap : FStar_Ident.lident Prims.list FStar_ST.ref FStar_Util.smap = (new_sigmap ())


let empty_exported_id_smap : exported_id_set FStar_Util.smap = (new_sigmap ())


let try_lookup_lid' : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term * Prims.bool) FStar_Pervasives_Native.option = (fun any_val exclude_interf env lid -> (

let uu____5413 = (try_lookup_name any_val exclude_interf env lid)
in (match (uu____5413) with
| FStar_Pervasives_Native.Some (Term_name (e, mut)) -> begin
FStar_Pervasives_Native.Some (((e), (mut)))
end
| uu____5428 -> begin
FStar_Pervasives_Native.None
end)))


let try_lookup_lid : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term * Prims.bool) FStar_Pervasives_Native.option = (fun env l -> (try_lookup_lid' env.iface false env l))


let resolve_to_fully_qualified_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident FStar_Pervasives_Native.option = (fun env l -> (

let uu____5459 = (try_lookup_lid env l)
in (match (uu____5459) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (e, uu____5473) -> begin
(

let uu____5478 = (

let uu____5479 = (FStar_Syntax_Subst.compress e)
in uu____5479.FStar_Syntax_Syntax.n)
in (match (uu____5478) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
FStar_Pervasives_Native.Some (fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end
| uu____5485 -> begin
FStar_Pervasives_Native.None
end))
end)))


let try_lookup_lid_no_resolve : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term * Prims.bool) FStar_Pervasives_Native.option = (fun env l -> (

let env' = (

let uu___193_5501 = env
in {curmodule = uu___193_5501.curmodule; curmonad = uu___193_5501.curmonad; modules = uu___193_5501.modules; scope_mods = []; exported_ids = empty_exported_id_smap; trans_exported_ids = uu___193_5501.trans_exported_ids; includes = empty_include_smap; sigaccum = uu___193_5501.sigaccum; sigmap = uu___193_5501.sigmap; iface = uu___193_5501.iface; admitted_iface = uu___193_5501.admitted_iface; expect_typ = uu___193_5501.expect_typ; docs = uu___193_5501.docs; remaining_iface_decls = uu___193_5501.remaining_iface_decls; syntax_only = uu___193_5501.syntax_only; ds_hooks = uu___193_5501.ds_hooks})
in (try_lookup_lid env' l)))


let try_lookup_doc : env  ->  FStar_Ident.lid  ->  FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option = (fun env l -> (FStar_Util.smap_try_find env.docs l.FStar_Ident.str))


let try_lookup_datacon : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.fv FStar_Pervasives_Native.option = (fun env lid -> (

let k_global_def = (fun lid1 uu___174_5534 -> (match (uu___174_5534) with
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (uu____5541, uu____5542, uu____5543); FStar_Syntax_Syntax.sigrng = uu____5544; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = uu____5546; FStar_Syntax_Syntax.sigattrs = uu____5547}, uu____5548) -> begin
(

let uu____5553 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___173_5557 -> (match (uu___173_5557) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| uu____5558 -> begin
false
end))))
in (match (uu____5553) with
| true -> begin
(

let uu____5561 = (FStar_Syntax_Syntax.lid_as_fv lid1 FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in FStar_Pervasives_Native.Some (uu____5561))
end
| uu____5562 -> begin
FStar_Pervasives_Native.None
end))
end
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (uu____5563); FStar_Syntax_Syntax.sigrng = uu____5564; FStar_Syntax_Syntax.sigquals = uu____5565; FStar_Syntax_Syntax.sigmeta = uu____5566; FStar_Syntax_Syntax.sigattrs = uu____5567}, uu____5568) -> begin
(

let uu____5587 = (FStar_Syntax_Syntax.lid_as_fv lid1 FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))
in FStar_Pervasives_Native.Some (uu____5587))
end
| uu____5588 -> begin
FStar_Pervasives_Native.None
end))
in (resolve_in_open_namespaces' env lid (fun uu____5594 -> FStar_Pervasives_Native.None) (fun uu____5596 -> FStar_Pervasives_Native.None) k_global_def)))


let find_all_datacons : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.list FStar_Pervasives_Native.option = (fun env lid -> (

let k_global_def = (fun lid1 uu___175_5623 -> (match (uu___175_5623) with
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (uu____5632, uu____5633, uu____5634, uu____5635, datas, uu____5637); FStar_Syntax_Syntax.sigrng = uu____5638; FStar_Syntax_Syntax.sigquals = uu____5639; FStar_Syntax_Syntax.sigmeta = uu____5640; FStar_Syntax_Syntax.sigattrs = uu____5641}, uu____5642) -> begin
FStar_Pervasives_Native.Some (datas)
end
| uu____5657 -> begin
FStar_Pervasives_Native.None
end))
in (resolve_in_open_namespaces' env lid (fun uu____5667 -> FStar_Pervasives_Native.None) (fun uu____5671 -> FStar_Pervasives_Native.None) k_global_def)))


let record_cache_aux_with_filter : (((Prims.unit  ->  Prims.unit) * (Prims.unit  ->  Prims.unit) * (Prims.unit  ->  record_or_dc Prims.list) * (record_or_dc  ->  Prims.unit)) * (Prims.unit  ->  Prims.unit)) = (

let record_cache = (FStar_Util.mk_ref (([])::[]))
in (

let push1 = (fun uu____5716 -> (

let uu____5717 = (

let uu____5722 = (

let uu____5725 = (FStar_ST.op_Bang record_cache)
in (FStar_List.hd uu____5725))
in (

let uu____5800 = (FStar_ST.op_Bang record_cache)
in (uu____5722)::uu____5800))
in (FStar_ST.op_Colon_Equals record_cache uu____5717)))
in (

let pop1 = (fun uu____5946 -> (

let uu____5947 = (

let uu____5952 = (FStar_ST.op_Bang record_cache)
in (FStar_List.tl uu____5952))
in (FStar_ST.op_Colon_Equals record_cache uu____5947)))
in (

let peek1 = (fun uu____6100 -> (

let uu____6101 = (FStar_ST.op_Bang record_cache)
in (FStar_List.hd uu____6101)))
in (

let insert = (fun r -> (

let uu____6180 = (

let uu____6185 = (

let uu____6188 = (peek1 ())
in (r)::uu____6188)
in (

let uu____6191 = (

let uu____6196 = (FStar_ST.op_Bang record_cache)
in (FStar_List.tl uu____6196))
in (uu____6185)::uu____6191))
in (FStar_ST.op_Colon_Equals record_cache uu____6180)))
in (

let filter1 = (fun uu____6344 -> (

let rc = (peek1 ())
in (

let filtered = (FStar_List.filter (fun r -> (not (r.is_private_or_abstract))) rc)
in (

let uu____6353 = (

let uu____6358 = (

let uu____6363 = (FStar_ST.op_Bang record_cache)
in (FStar_List.tl uu____6363))
in (filtered)::uu____6358)
in (FStar_ST.op_Colon_Equals record_cache uu____6353)))))
in (

let aux = ((push1), (pop1), (peek1), (insert))
in ((aux), (filter1)))))))))


let record_cache_aux : ((Prims.unit  ->  Prims.unit) * (Prims.unit  ->  Prims.unit) * (Prims.unit  ->  record_or_dc Prims.list) * (record_or_dc  ->  Prims.unit)) = (

let uu____6575 = record_cache_aux_with_filter
in (match (uu____6575) with
| (aux, uu____6619) -> begin
aux
end))


let filter_record_cache : Prims.unit  ->  Prims.unit = (

let uu____6663 = record_cache_aux_with_filter
in (match (uu____6663) with
| (uu____6690, filter1) -> begin
filter1
end))


let push_record_cache : Prims.unit  ->  Prims.unit = (

let uu____6735 = record_cache_aux
in (match (uu____6735) with
| (push1, uu____6757, uu____6758, uu____6759) -> begin
push1
end))


let pop_record_cache : Prims.unit  ->  Prims.unit = (

let uu____6783 = record_cache_aux
in (match (uu____6783) with
| (uu____6804, pop1, uu____6806, uu____6807) -> begin
pop1
end))


let peek_record_cache : Prims.unit  ->  record_or_dc Prims.list = (

let uu____6833 = record_cache_aux
in (match (uu____6833) with
| (uu____6856, uu____6857, peek1, uu____6859) -> begin
peek1
end))


let insert_record_cache : record_or_dc  ->  Prims.unit = (

let uu____6883 = record_cache_aux
in (match (uu____6883) with
| (uu____6904, uu____6905, uu____6906, insert) -> begin
insert
end))


let extract_record : env  ->  scope_mod Prims.list FStar_ST.ref  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun e new_globs se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_bundle (sigs, uu____6963) -> begin
(

let is_record = (FStar_Util.for_some (fun uu___176_6979 -> (match (uu___176_6979) with
| FStar_Syntax_Syntax.RecordType (uu____6980) -> begin
true
end
| FStar_Syntax_Syntax.RecordConstructor (uu____6989) -> begin
true
end
| uu____6998 -> begin
false
end)))
in (

let find_dc = (fun dc -> (FStar_All.pipe_right sigs (FStar_Util.find_opt (fun uu___177_7020 -> (match (uu___177_7020) with
| {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (lid, uu____7022, uu____7023, uu____7024, uu____7025, uu____7026); FStar_Syntax_Syntax.sigrng = uu____7027; FStar_Syntax_Syntax.sigquals = uu____7028; FStar_Syntax_Syntax.sigmeta = uu____7029; FStar_Syntax_Syntax.sigattrs = uu____7030} -> begin
(FStar_Ident.lid_equals dc lid)
end
| uu____7039 -> begin
false
end)))))
in (FStar_All.pipe_right sigs (FStar_List.iter (fun uu___178_7074 -> (match (uu___178_7074) with
| {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (typename, univs1, parms, uu____7078, uu____7079, (dc)::[]); FStar_Syntax_Syntax.sigrng = uu____7081; FStar_Syntax_Syntax.sigquals = typename_quals; FStar_Syntax_Syntax.sigmeta = uu____7083; FStar_Syntax_Syntax.sigattrs = uu____7084} -> begin
(

let uu____7095 = (

let uu____7096 = (find_dc dc)
in (FStar_All.pipe_left FStar_Util.must uu____7096))
in (match (uu____7095) with
| {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (constrname, uu____7102, t, uu____7104, uu____7105, uu____7106); FStar_Syntax_Syntax.sigrng = uu____7107; FStar_Syntax_Syntax.sigquals = uu____7108; FStar_Syntax_Syntax.sigmeta = uu____7109; FStar_Syntax_Syntax.sigattrs = uu____7110} -> begin
(

let uu____7119 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____7119) with
| (formals, uu____7133) -> begin
(

let is_rec = (is_record typename_quals)
in (

let formals' = (FStar_All.pipe_right formals (FStar_List.collect (fun uu____7182 -> (match (uu____7182) with
| (x, q) -> begin
(

let uu____7195 = ((FStar_Syntax_Syntax.is_null_bv x) || (is_rec && (FStar_Syntax_Syntax.is_implicit q)))
in (match (uu____7195) with
| true -> begin
[]
end
| uu____7206 -> begin
(((x), (q)))::[]
end))
end))))
in (

let fields' = (FStar_All.pipe_right formals' (FStar_List.map (fun uu____7252 -> (match (uu____7252) with
| (x, q) -> begin
(

let uu____7265 = (match (is_rec) with
| true -> begin
(FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname)
end
| uu____7266 -> begin
x.FStar_Syntax_Syntax.ppname
end)
in ((uu____7265), (x.FStar_Syntax_Syntax.sort)))
end))))
in (

let fields = fields'
in (

let record = {typename = typename; constrname = constrname.FStar_Ident.ident; parms = parms; fields = fields; is_private_or_abstract = ((FStar_List.contains FStar_Syntax_Syntax.Private typename_quals) || (FStar_List.contains FStar_Syntax_Syntax.Abstract typename_quals)); is_record = is_rec}
in ((

let uu____7280 = (

let uu____7283 = (FStar_ST.op_Bang new_globs)
in (Record_or_dc (record))::uu____7283)
in (FStar_ST.op_Colon_Equals new_globs uu____7280));
(match (()) with
| () -> begin
((

let add_field = (fun uu____7424 -> (match (uu____7424) with
| (id, uu____7432) -> begin
(

let modul = (

let uu____7438 = (FStar_Ident.lid_of_ids constrname.FStar_Ident.ns)
in uu____7438.FStar_Ident.str)
in (

let uu____7439 = (get_exported_id_set e modul)
in (match (uu____7439) with
| FStar_Pervasives_Native.Some (my_ex) -> begin
(

let my_exported_ids = (my_ex Exported_id_field)
in ((

let uu____7466 = (

let uu____7467 = (FStar_ST.op_Bang my_exported_ids)
in (FStar_Util.set_add id.FStar_Ident.idText uu____7467))
in (FStar_ST.op_Colon_Equals my_exported_ids uu____7466));
(match (()) with
| () -> begin
(

let projname = (

let uu____7591 = (

let uu____7592 = (FStar_Syntax_Util.mk_field_projector_name_from_ident constrname id)
in uu____7592.FStar_Ident.ident)
in uu____7591.FStar_Ident.idText)
in (

let uu____7594 = (

let uu____7595 = (FStar_ST.op_Bang my_exported_ids)
in (FStar_Util.set_add projname uu____7595))
in (FStar_ST.op_Colon_Equals my_exported_ids uu____7594)))
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
| uu____7728 -> begin
()
end))
end
| uu____7729 -> begin
()
end))))))
end
| uu____7730 -> begin
()
end))


let try_lookup_record_or_dc_by_field_name : env  ->  FStar_Ident.lident  ->  record_or_dc FStar_Pervasives_Native.option = (fun env fieldname -> (

let find_in_cache = (fun fieldname1 -> (

let uu____7747 = ((fieldname1.FStar_Ident.ns), (fieldname1.FStar_Ident.ident))
in (match (uu____7747) with
| (ns, id) -> begin
(

let uu____7764 = (peek_record_cache ())
in (FStar_Util.find_map uu____7764 (fun record -> (

let uu____7770 = (find_in_record ns id record (fun r -> Cont_ok (r)))
in (option_of_cont (fun uu____7776 -> FStar_Pervasives_Native.None) uu____7770)))))
end)))
in (resolve_in_open_namespaces'' env fieldname Exported_id_field (fun uu____7778 -> Cont_ignore) (fun uu____7780 -> Cont_ignore) (fun r -> Cont_ok (r)) (fun fn -> (

let uu____7786 = (find_in_cache fn)
in (cont_of_option Cont_ignore uu____7786))) (fun k uu____7792 -> k))))


let try_lookup_record_by_field_name : env  ->  FStar_Ident.lident  ->  record_or_dc FStar_Pervasives_Native.option = (fun env fieldname -> (

let uu____7805 = (try_lookup_record_or_dc_by_field_name env fieldname)
in (match (uu____7805) with
| FStar_Pervasives_Native.Some (r) when r.is_record -> begin
FStar_Pervasives_Native.Some (r)
end
| uu____7811 -> begin
FStar_Pervasives_Native.None
end)))


let belongs_to_record : env  ->  FStar_Ident.lident  ->  record_or_dc  ->  Prims.bool = (fun env lid record -> (

let uu____7826 = (try_lookup_record_by_field_name env lid)
in (match (uu____7826) with
| FStar_Pervasives_Native.Some (record') when (

let uu____7830 = (

let uu____7831 = (FStar_Ident.path_of_ns record.typename.FStar_Ident.ns)
in (FStar_Ident.text_of_path uu____7831))
in (

let uu____7834 = (

let uu____7835 = (FStar_Ident.path_of_ns record'.typename.FStar_Ident.ns)
in (FStar_Ident.text_of_path uu____7835))
in (Prims.op_Equality uu____7830 uu____7834))) -> begin
(

let uu____7838 = (find_in_record record.typename.FStar_Ident.ns lid.FStar_Ident.ident record (fun uu____7842 -> Cont_ok (())))
in (match (uu____7838) with
| Cont_ok (uu____7843) -> begin
true
end
| uu____7844 -> begin
false
end))
end
| uu____7847 -> begin
false
end)))


let try_lookup_dc_by_field_name : env  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * Prims.bool) FStar_Pervasives_Native.option = (fun env fieldname -> (

let uu____7864 = (try_lookup_record_or_dc_by_field_name env fieldname)
in (match (uu____7864) with
| FStar_Pervasives_Native.Some (r) -> begin
(

let uu____7874 = (

let uu____7879 = (

let uu____7880 = (FStar_Ident.lid_of_ids (FStar_List.append r.typename.FStar_Ident.ns ((r.constrname)::[])))
in (FStar_Ident.set_lid_range uu____7880 (FStar_Ident.range_of_lid fieldname)))
in ((uu____7879), (r.is_record)))
in FStar_Pervasives_Native.Some (uu____7874))
end
| uu____7885 -> begin
FStar_Pervasives_Native.None
end)))


let string_set_ref_new : Prims.unit  ->  Prims.string FStar_Util.set FStar_ST.ref = (fun uu____7906 -> (

let uu____7907 = (FStar_Util.new_set FStar_Util.compare)
in (FStar_Util.mk_ref uu____7907)))


let exported_id_set_new : Prims.unit  ->  exported_id_kind  ->  Prims.string FStar_Util.set FStar_ST.ref = (fun uu____7928 -> (

let term_type_set = (string_set_ref_new ())
in (

let field_set = (string_set_ref_new ())
in (fun uu___179_7939 -> (match (uu___179_7939) with
| Exported_id_term_type -> begin
term_type_set
end
| Exported_id_field -> begin
field_set
end)))))


let unique : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  Prims.bool = (fun any_val exclude_if env lid -> (

let filter_scope_mods = (fun uu___180_7977 -> (match (uu___180_7977) with
| Rec_binding (uu____7978) -> begin
true
end
| uu____7979 -> begin
false
end))
in (

let this_env = (

let uu___194_7981 = env
in (

let uu____7982 = (FStar_List.filter filter_scope_mods env.scope_mods)
in {curmodule = uu___194_7981.curmodule; curmonad = uu___194_7981.curmonad; modules = uu___194_7981.modules; scope_mods = uu____7982; exported_ids = empty_exported_id_smap; trans_exported_ids = uu___194_7981.trans_exported_ids; includes = empty_include_smap; sigaccum = uu___194_7981.sigaccum; sigmap = uu___194_7981.sigmap; iface = uu___194_7981.iface; admitted_iface = uu___194_7981.admitted_iface; expect_typ = uu___194_7981.expect_typ; docs = uu___194_7981.docs; remaining_iface_decls = uu___194_7981.remaining_iface_decls; syntax_only = uu___194_7981.syntax_only; ds_hooks = uu___194_7981.ds_hooks}))
in (

let uu____7985 = (try_lookup_lid' any_val exclude_if this_env lid)
in (match (uu____7985) with
| FStar_Pervasives_Native.None -> begin
true
end
| FStar_Pervasives_Native.Some (uu____7996) -> begin
false
end)))))


let push_scope_mod : env  ->  scope_mod  ->  env = (fun env scope_mod -> (

let uu___195_8013 = env
in {curmodule = uu___195_8013.curmodule; curmonad = uu___195_8013.curmonad; modules = uu___195_8013.modules; scope_mods = (scope_mod)::env.scope_mods; exported_ids = uu___195_8013.exported_ids; trans_exported_ids = uu___195_8013.trans_exported_ids; includes = uu___195_8013.includes; sigaccum = uu___195_8013.sigaccum; sigmap = uu___195_8013.sigmap; iface = uu___195_8013.iface; admitted_iface = uu___195_8013.admitted_iface; expect_typ = uu___195_8013.expect_typ; docs = uu___195_8013.docs; remaining_iface_decls = uu___195_8013.remaining_iface_decls; syntax_only = uu___195_8013.syntax_only; ds_hooks = uu___195_8013.ds_hooks}))


let push_bv' : env  ->  FStar_Ident.ident  ->  Prims.bool  ->  (env * FStar_Syntax_Syntax.bv) = (fun env x is_mutable -> (

let bv = (FStar_Syntax_Syntax.gen_bv x.FStar_Ident.idText (FStar_Pervasives_Native.Some (x.FStar_Ident.idRange)) FStar_Syntax_Syntax.tun)
in (((push_scope_mod env (Local_binding (((x), (bv), (is_mutable)))))), (bv))))


let push_bv_mutable : env  ->  FStar_Ident.ident  ->  (env * FStar_Syntax_Syntax.bv) = (fun env x -> (push_bv' env x true))


let push_bv : env  ->  FStar_Ident.ident  ->  (env * FStar_Syntax_Syntax.bv) = (fun env x -> (push_bv' env x false))


let push_top_level_rec_binding : env  ->  FStar_Ident.ident  ->  FStar_Syntax_Syntax.delta_depth  ->  env = (fun env x dd -> (

let l = (qualify env x)
in (

let uu____8068 = ((unique false true env l) || (FStar_Options.interactive ()))
in (match (uu____8068) with
| true -> begin
(push_scope_mod env (Rec_binding (((x), (l), (dd)))))
end
| uu____8069 -> begin
(FStar_Exn.raise (FStar_Errors.Error ((((Prims.strcat "Duplicate top-level names " l.FStar_Ident.str)), ((FStar_Ident.range_of_lid l))))))
end))))


let push_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env s -> (

let err1 = (fun l -> (

let sopt = (FStar_Util.smap_try_find (sigmap env) l.FStar_Ident.str)
in (

let r = (match (sopt) with
| FStar_Pervasives_Native.Some (se, uu____8095) -> begin
(

let uu____8100 = (FStar_Util.find_opt (FStar_Ident.lid_equals l) (FStar_Syntax_Util.lids_of_sigelt se))
in (match (uu____8100) with
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

let uu____8108 = (

let uu____8109 = (

let uu____8114 = (FStar_Util.format2 "Duplicate top-level names [%s]; previously declared at %s" (FStar_Ident.text_of_lid l) r)
in ((uu____8114), ((FStar_Ident.range_of_lid l))))
in FStar_Errors.Error (uu____8109))
in (FStar_Exn.raise uu____8108)))))
in (

let globals = (FStar_Util.mk_ref env.scope_mods)
in (

let env1 = (

let uu____8123 = (match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let (uu____8132) -> begin
((false), (true))
end
| FStar_Syntax_Syntax.Sig_bundle (uu____8139) -> begin
((true), (true))
end
| uu____8148 -> begin
((false), (false))
end)
in (match (uu____8123) with
| (any_val, exclude_if) -> begin
(

let lids = (FStar_Syntax_Util.lids_of_sigelt s)
in (

let uu____8154 = (FStar_Util.find_map lids (fun l -> (

let uu____8160 = (

let uu____8161 = (unique any_val exclude_if env l)
in (not (uu____8161)))
in (match (uu____8160) with
| true -> begin
FStar_Pervasives_Native.Some (l)
end
| uu____8164 -> begin
FStar_Pervasives_Native.None
end))))
in (match (uu____8154) with
| FStar_Pervasives_Native.Some (l) when (

let uu____8166 = (FStar_Options.interactive ())
in (not (uu____8166))) -> begin
(err1 l)
end
| uu____8167 -> begin
((extract_record env globals s);
(

let uu___196_8185 = env
in {curmodule = uu___196_8185.curmodule; curmonad = uu___196_8185.curmonad; modules = uu___196_8185.modules; scope_mods = uu___196_8185.scope_mods; exported_ids = uu___196_8185.exported_ids; trans_exported_ids = uu___196_8185.trans_exported_ids; includes = uu___196_8185.includes; sigaccum = (s)::env.sigaccum; sigmap = uu___196_8185.sigmap; iface = uu___196_8185.iface; admitted_iface = uu___196_8185.admitted_iface; expect_typ = uu___196_8185.expect_typ; docs = uu___196_8185.docs; remaining_iface_decls = uu___196_8185.remaining_iface_decls; syntax_only = uu___196_8185.syntax_only; ds_hooks = uu___196_8185.ds_hooks});
)
end)))
end))
in (

let env2 = (

let uu___197_8187 = env1
in (

let uu____8188 = (FStar_ST.op_Bang globals)
in {curmodule = uu___197_8187.curmodule; curmonad = uu___197_8187.curmonad; modules = uu___197_8187.modules; scope_mods = uu____8188; exported_ids = uu___197_8187.exported_ids; trans_exported_ids = uu___197_8187.trans_exported_ids; includes = uu___197_8187.includes; sigaccum = uu___197_8187.sigaccum; sigmap = uu___197_8187.sigmap; iface = uu___197_8187.iface; admitted_iface = uu___197_8187.admitted_iface; expect_typ = uu___197_8187.expect_typ; docs = uu___197_8187.docs; remaining_iface_decls = uu___197_8187.remaining_iface_decls; syntax_only = uu___197_8187.syntax_only; ds_hooks = uu___197_8187.ds_hooks}))
in (

let uu____8255 = (match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____8281) -> begin
(

let uu____8290 = (FStar_List.map (fun se -> (((FStar_Syntax_Util.lids_of_sigelt se)), (se))) ses)
in ((env2), (uu____8290)))
end
| uu____8317 -> begin
((env2), (((((FStar_Syntax_Util.lids_of_sigelt s)), (s)))::[]))
end)
in (match (uu____8255) with
| (env3, lss) -> begin
((FStar_All.pipe_right lss (FStar_List.iter (fun uu____8376 -> (match (uu____8376) with
| (lids, se) -> begin
(FStar_All.pipe_right lids (FStar_List.iter (fun lid -> ((

let uu____8397 = (

let uu____8400 = (FStar_ST.op_Bang globals)
in (Top_level_def (lid.FStar_Ident.ident))::uu____8400)
in (FStar_ST.op_Colon_Equals globals uu____8397));
(match (()) with
| () -> begin
(

let modul = (

let uu____8532 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in uu____8532.FStar_Ident.str)
in ((

let uu____8534 = (get_exported_id_set env3 modul)
in (match (uu____8534) with
| FStar_Pervasives_Native.Some (f) -> begin
(

let my_exported_ids = (f Exported_id_term_type)
in (

let uu____8560 = (

let uu____8561 = (FStar_ST.op_Bang my_exported_ids)
in (FStar_Util.set_add lid.FStar_Ident.ident.FStar_Ident.idText uu____8561))
in (FStar_ST.op_Colon_Equals my_exported_ids uu____8560)))
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

let uu___198_8693 = env3
in (

let uu____8694 = (FStar_ST.op_Bang globals)
in {curmodule = uu___198_8693.curmodule; curmonad = uu___198_8693.curmonad; modules = uu___198_8693.modules; scope_mods = uu____8694; exported_ids = uu___198_8693.exported_ids; trans_exported_ids = uu___198_8693.trans_exported_ids; includes = uu___198_8693.includes; sigaccum = uu___198_8693.sigaccum; sigmap = uu___198_8693.sigmap; iface = uu___198_8693.iface; admitted_iface = uu___198_8693.admitted_iface; expect_typ = uu___198_8693.expect_typ; docs = uu___198_8693.docs; remaining_iface_decls = uu___198_8693.remaining_iface_decls; syntax_only = uu___198_8693.syntax_only; ds_hooks = uu___198_8693.ds_hooks}))
in env4);
)
end)))))))


let push_namespace : env  ->  FStar_Ident.lident  ->  env = (fun env ns -> (

let uu____8769 = (

let uu____8774 = (resolve_module_name env ns false)
in (match (uu____8774) with
| FStar_Pervasives_Native.None -> begin
(

let modules = env.modules
in (

let uu____8788 = (FStar_All.pipe_right modules (FStar_Util.for_some (fun uu____8802 -> (match (uu____8802) with
| (m, uu____8808) -> begin
(FStar_Util.starts_with (Prims.strcat (FStar_Ident.text_of_lid m) ".") (Prims.strcat (FStar_Ident.text_of_lid ns) "."))
end))))
in (match (uu____8788) with
| true -> begin
((ns), (Open_namespace))
end
| uu____8813 -> begin
(

let uu____8814 = (

let uu____8815 = (

let uu____8820 = (FStar_Util.format1 "Namespace %s cannot be found" (FStar_Ident.text_of_lid ns))
in ((uu____8820), ((FStar_Ident.range_of_lid ns))))
in FStar_Errors.Error (uu____8815))
in (FStar_Exn.raise uu____8814))
end)))
end
| FStar_Pervasives_Native.Some (ns') -> begin
((fail_if_curmodule env ns ns');
((ns'), (Open_module));
)
end))
in (match (uu____8769) with
| (ns', kd) -> begin
((env.ds_hooks.ds_push_open_hook env ((ns'), (kd)));
(push_scope_mod env (Open_module_or_namespace (((ns'), (kd)))));
)
end)))


let push_include : env  ->  FStar_Ident.lident  ->  env = (fun env ns -> (

let ns0 = ns
in (

let uu____8839 = (resolve_module_name env ns false)
in (match (uu____8839) with
| FStar_Pervasives_Native.Some (ns1) -> begin
((env.ds_hooks.ds_push_include_hook env ns1);
(fail_if_curmodule env ns0 ns1);
(

let env1 = (push_scope_mod env (Open_module_or_namespace (((ns1), (Open_module)))))
in (

let curmod = (

let uu____8847 = (current_module env1)
in uu____8847.FStar_Ident.str)
in ((

let uu____8849 = (FStar_Util.smap_try_find env1.includes curmod)
in (match (uu____8849) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (incl) -> begin
(

let uu____8873 = (

let uu____8876 = (FStar_ST.op_Bang incl)
in (ns1)::uu____8876)
in (FStar_ST.op_Colon_Equals incl uu____8873))
end));
(match (()) with
| () -> begin
(

let uu____9007 = (get_trans_exported_id_set env1 ns1.FStar_Ident.str)
in (match (uu____9007) with
| FStar_Pervasives_Native.Some (ns_trans_exports) -> begin
((

let uu____9024 = (

let uu____9041 = (get_exported_id_set env1 curmod)
in (

let uu____9048 = (get_trans_exported_id_set env1 curmod)
in ((uu____9041), (uu____9048))))
in (match (uu____9024) with
| (FStar_Pervasives_Native.Some (cur_exports), FStar_Pervasives_Native.Some (cur_trans_exports)) -> begin
(

let update_exports = (fun k -> (

let ns_ex = (

let uu____9102 = (ns_trans_exports k)
in (FStar_ST.op_Bang uu____9102))
in (

let ex = (cur_exports k)
in ((

let uu____9357 = (

let uu____9358 = (FStar_ST.op_Bang ex)
in (FStar_Util.set_difference uu____9358 ns_ex))
in (FStar_ST.op_Colon_Equals ex uu____9357));
(match (()) with
| () -> begin
(

let trans_ex = (cur_trans_exports k)
in (

let uu____9492 = (

let uu____9493 = (FStar_ST.op_Bang trans_ex)
in (FStar_Util.set_union uu____9493 ns_ex))
in (FStar_ST.op_Colon_Equals trans_ex uu____9492)))
end);
))))
in (FStar_List.iter update_exports all_exported_id_kinds))
end
| uu____9616 -> begin
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

let uu____9637 = (

let uu____9638 = (

let uu____9643 = (FStar_Util.format1 "include: Module %s was not prepared" ns1.FStar_Ident.str)
in ((uu____9643), ((FStar_Ident.range_of_lid ns1))))
in FStar_Errors.Error (uu____9638))
in (FStar_Exn.raise uu____9637))
end))
end);
)));
)
end
| uu____9644 -> begin
(

let uu____9647 = (

let uu____9648 = (

let uu____9653 = (FStar_Util.format1 "include: Module %s cannot be found" ns.FStar_Ident.str)
in ((uu____9653), ((FStar_Ident.range_of_lid ns))))
in FStar_Errors.Error (uu____9648))
in (FStar_Exn.raise uu____9647))
end))))


let push_module_abbrev : env  ->  FStar_Ident.ident  ->  FStar_Ident.lident  ->  env = (fun env x l -> (

let uu____9666 = (module_is_defined env l)
in (match (uu____9666) with
| true -> begin
((fail_if_curmodule env l l);
(env.ds_hooks.ds_push_module_abbrev_hook env x l);
(push_scope_mod env (Module_abbrev (((x), (l)))));
)
end
| uu____9669 -> begin
(

let uu____9670 = (

let uu____9671 = (

let uu____9676 = (FStar_Util.format1 "Module %s cannot be found" (FStar_Ident.text_of_lid l))
in ((uu____9676), ((FStar_Ident.range_of_lid l))))
in FStar_Errors.Error (uu____9671))
in (FStar_Exn.raise uu____9670))
end)))


let push_doc : env  ->  FStar_Ident.lident  ->  FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option  ->  env = (fun env l doc_opt -> (match (doc_opt) with
| FStar_Pervasives_Native.None -> begin
env
end
| FStar_Pervasives_Native.Some (doc1) -> begin
((

let uu____9695 = (FStar_Util.smap_try_find env.docs l.FStar_Ident.str)
in (match (uu____9695) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (old_doc) -> begin
(

let uu____9699 = (

let uu____9700 = (FStar_Ident.string_of_lid l)
in (

let uu____9701 = (FStar_Parser_AST.string_of_fsdoc old_doc)
in (

let uu____9702 = (FStar_Parser_AST.string_of_fsdoc doc1)
in (FStar_Util.format3 "Overwriting doc of %s; old doc was [%s]; new doc are [%s]" uu____9700 uu____9701 uu____9702))))
in (FStar_Errors.warn (FStar_Ident.range_of_lid l) uu____9699))
end));
(FStar_Util.smap_add env.docs l.FStar_Ident.str doc1);
env;
)
end))


let check_admits : env  ->  Prims.unit = (fun env -> (FStar_All.pipe_right env.sigaccum (FStar_List.iter (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_declare_typ (l, u, t) -> begin
(

let uu____9719 = (try_lookup_lid env l)
in (match (uu____9719) with
| FStar_Pervasives_Native.None -> begin
((

let uu____9731 = (

let uu____9732 = (FStar_Options.interactive ())
in (not (uu____9732)))
in (match (uu____9731) with
| true -> begin
(

let uu____9733 = (

let uu____9734 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Admitting %s without a definition" uu____9734))
in (FStar_Errors.warn (FStar_Ident.range_of_lid l) uu____9733))
end
| uu____9735 -> begin
()
end));
(

let quals = (FStar_Syntax_Syntax.Assumption)::se.FStar_Syntax_Syntax.sigquals
in (FStar_Util.smap_add (sigmap env) l.FStar_Ident.str (((

let uu___199_9744 = se
in {FStar_Syntax_Syntax.sigel = uu___199_9744.FStar_Syntax_Syntax.sigel; FStar_Syntax_Syntax.sigrng = uu___199_9744.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = uu___199_9744.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___199_9744.FStar_Syntax_Syntax.sigattrs})), (false))));
)
end
| FStar_Pervasives_Native.Some (uu____9745) -> begin
()
end))
end
| uu____9754 -> begin
()
end)))))


let finish : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env modul -> ((FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations (FStar_List.iter (fun se -> (

let quals = se.FStar_Syntax_Syntax.sigquals
in (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____9773) -> begin
(match (((FStar_List.contains FStar_Syntax_Syntax.Private quals) || (FStar_List.contains FStar_Syntax_Syntax.Abstract quals))) with
| true -> begin
(FStar_All.pipe_right ses (FStar_List.iter (fun se1 -> (match (se1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (lid, uu____9793, uu____9794, uu____9795, uu____9796, uu____9797) -> begin
(FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str)
end
| uu____9806 -> begin
()
end))))
end
| uu____9807 -> begin
()
end)
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____9809, uu____9810) -> begin
(match ((FStar_List.contains FStar_Syntax_Syntax.Private quals)) with
| true -> begin
(FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str)
end
| uu____9815 -> begin
()
end)
end
| FStar_Syntax_Syntax.Sig_let ((uu____9816, lbs), uu____9818) -> begin
((match (((FStar_List.contains FStar_Syntax_Syntax.Private quals) || (FStar_List.contains FStar_Syntax_Syntax.Abstract quals))) with
| true -> begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (

let uu____9839 = (

let uu____9840 = (

let uu____9841 = (

let uu____9844 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in uu____9844.FStar_Syntax_Syntax.fv_name)
in uu____9841.FStar_Syntax_Syntax.v)
in uu____9840.FStar_Ident.str)
in (FStar_Util.smap_remove (sigmap env) uu____9839)))))
end
| uu____9849 -> begin
()
end);
(match (((FStar_List.contains FStar_Syntax_Syntax.Abstract quals) && (not ((FStar_List.contains FStar_Syntax_Syntax.Private quals))))) with
| true -> begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (

let lid = (

let uu____9858 = (

let uu____9861 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in uu____9861.FStar_Syntax_Syntax.fv_name)
in uu____9858.FStar_Syntax_Syntax.v)
in (

let quals1 = (FStar_Syntax_Syntax.Assumption)::quals
in (

let decl = (

let uu___200_9866 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp))); FStar_Syntax_Syntax.sigrng = uu___200_9866.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = uu___200_9866.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___200_9866.FStar_Syntax_Syntax.sigattrs})
in (FStar_Util.smap_add (sigmap env) lid.FStar_Ident.str ((decl), (false)))))))))
end
| uu____9875 -> begin
()
end);
)
end
| uu____9876 -> begin
()
end)))));
(

let curmod = (

let uu____9878 = (current_module env)
in uu____9878.FStar_Ident.str)
in ((

let uu____9880 = (

let uu____9897 = (get_exported_id_set env curmod)
in (

let uu____9904 = (get_trans_exported_id_set env curmod)
in ((uu____9897), (uu____9904))))
in (match (uu____9880) with
| (FStar_Pervasives_Native.Some (cur_ex), FStar_Pervasives_Native.Some (cur_trans_ex)) -> begin
(

let update_exports = (fun eikind -> (

let cur_ex_set = (

let uu____9958 = (cur_ex eikind)
in (FStar_ST.op_Bang uu____9958))
in (

let cur_trans_ex_set_ref = (cur_trans_ex eikind)
in (

let uu____10212 = (

let uu____10213 = (FStar_ST.op_Bang cur_trans_ex_set_ref)
in (FStar_Util.set_union cur_ex_set uu____10213))
in (FStar_ST.op_Colon_Equals cur_trans_ex_set_ref uu____10212)))))
in (FStar_List.iter update_exports all_exported_id_kinds))
end
| uu____10336 -> begin
()
end));
(match (()) with
| () -> begin
((filter_record_cache ());
(match (()) with
| () -> begin
(

let uu___201_10354 = env
in {curmodule = FStar_Pervasives_Native.None; curmonad = uu___201_10354.curmonad; modules = (((modul.FStar_Syntax_Syntax.name), (modul)))::env.modules; scope_mods = []; exported_ids = uu___201_10354.exported_ids; trans_exported_ids = uu___201_10354.trans_exported_ids; includes = uu___201_10354.includes; sigaccum = []; sigmap = uu___201_10354.sigmap; iface = uu___201_10354.iface; admitted_iface = uu___201_10354.admitted_iface; expect_typ = uu___201_10354.expect_typ; docs = uu___201_10354.docs; remaining_iface_decls = uu___201_10354.remaining_iface_decls; syntax_only = uu___201_10354.syntax_only; ds_hooks = uu___201_10354.ds_hooks})
end);
)
end);
));
))


let stack : env Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let push : env  ->  env = (fun env -> ((push_record_cache ());
(

let uu____10378 = (

let uu____10381 = (FStar_ST.op_Bang stack)
in (env)::uu____10381)
in (FStar_ST.op_Colon_Equals stack uu____10378));
(

let uu___202_10484 = env
in (

let uu____10485 = (FStar_Util.smap_copy (sigmap env))
in (

let uu____10496 = (FStar_Util.smap_copy env.docs)
in {curmodule = uu___202_10484.curmodule; curmonad = uu___202_10484.curmonad; modules = uu___202_10484.modules; scope_mods = uu___202_10484.scope_mods; exported_ids = uu___202_10484.exported_ids; trans_exported_ids = uu___202_10484.trans_exported_ids; includes = uu___202_10484.includes; sigaccum = uu___202_10484.sigaccum; sigmap = uu____10485; iface = uu___202_10484.iface; admitted_iface = uu___202_10484.admitted_iface; expect_typ = uu___202_10484.expect_typ; docs = uu____10496; remaining_iface_decls = uu___202_10484.remaining_iface_decls; syntax_only = uu___202_10484.syntax_only; ds_hooks = uu___202_10484.ds_hooks})));
))


let pop : Prims.unit  ->  env = (fun uu____10502 -> (

let uu____10503 = (FStar_ST.op_Bang stack)
in (match (uu____10503) with
| (env)::tl1 -> begin
((pop_record_cache ());
(FStar_ST.op_Colon_Equals stack tl1);
env;
)
end
| uu____10612 -> begin
(failwith "Impossible: Too many pops")
end)))


let export_interface : FStar_Ident.lident  ->  env  ->  env = (fun m env -> (

let sigelt_in_m = (fun se -> (match ((FStar_Syntax_Util.lids_of_sigelt se)) with
| (l)::uu____10628 -> begin
(Prims.op_Equality l.FStar_Ident.nsstr m.FStar_Ident.str)
end
| uu____10631 -> begin
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

let uu____10665 = (FStar_Util.smap_try_find sm' k)
in (match (uu____10665) with
| FStar_Pervasives_Native.Some (se, true) when (sigelt_in_m se) -> begin
((FStar_Util.smap_remove sm' k);
(

let se1 = (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_declare_typ (l, u, t) -> begin
(

let uu___203_10690 = se
in {FStar_Syntax_Syntax.sigel = uu___203_10690.FStar_Syntax_Syntax.sigel; FStar_Syntax_Syntax.sigrng = uu___203_10690.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Assumption)::se.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___203_10690.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___203_10690.FStar_Syntax_Syntax.sigattrs})
end
| uu____10691 -> begin
se
end)
in (FStar_Util.smap_add sm' k ((se1), (false))));
)
end
| uu____10696 -> begin
()
end)))));
env1;
)))))))


let finish_module_or_interface : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env modul -> ((match ((not (modul.FStar_Syntax_Syntax.is_interface))) with
| true -> begin
(check_admits env)
end
| uu____10712 -> begin
()
end);
(finish env modul);
))

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

let uu____10781 = (

let uu____10784 = (e Exported_id_term_type)
in (FStar_ST.op_Bang uu____10784))
in (FStar_Util.set_elements uu____10781))
in (

let fields = (

let uu____11031 = (

let uu____11034 = (e Exported_id_field)
in (FStar_ST.op_Bang uu____11034))
in (FStar_Util.set_elements uu____11031))
in {exported_id_terms = terms; exported_id_fields = fields})))


let as_exported_id_set : exported_ids FStar_Pervasives_Native.option  ->  exported_id_kind  ->  Prims.string FStar_Util.set FStar_ST.ref = (fun e -> (match (e) with
| FStar_Pervasives_Native.None -> begin
(exported_id_set_new ())
end
| FStar_Pervasives_Native.Some (e1) -> begin
(

let terms = (

let uu____11311 = (FStar_Util.as_set e1.exported_id_terms FStar_Util.compare)
in (FStar_Util.mk_ref uu____11311))
in (

let fields = (

let uu____11321 = (FStar_Util.as_set e1.exported_id_fields FStar_Util.compare)
in (FStar_Util.mk_ref uu____11321))
in (fun uu___181_11326 -> (match (uu___181_11326) with
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


let as_includes : 'Auu____11439 . 'Auu____11439 Prims.list FStar_Pervasives_Native.option  ->  'Auu____11439 Prims.list FStar_ST.ref = (fun uu___182_11451 -> (match (uu___182_11451) with
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

let uu____11486 = (FStar_Util.smap_try_find m mname)
in (FStar_Util.map_opt uu____11486 as_exported_ids)))
in (

let uu____11489 = (as_ids_opt env.exported_ids)
in (

let uu____11492 = (as_ids_opt env.trans_exported_ids)
in (

let uu____11495 = (

let uu____11500 = (FStar_Util.smap_try_find env.includes mname)
in (FStar_Util.map_opt uu____11500 (fun r -> (FStar_ST.op_Bang r))))
in {mii_exported_ids = uu____11489; mii_trans_exported_ids = uu____11492; mii_includes = uu____11495}))))))


let prepare_module_or_interface : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  module_inclusion_info  ->  (env * Prims.bool) = (fun intf admitted env mname mii -> (

let prep = (fun env1 -> (

let filename = (FStar_Util.strcat (FStar_Ident.text_of_lid mname) ".fst")
in (

let auto_open = (FStar_Parser_Dep.hard_coded_dependencies filename)
in (

let auto_open1 = (

let convert_kind = (fun uu___183_11640 -> (match (uu___183_11640) with
| FStar_Parser_Dep.Open_namespace -> begin
Open_namespace
end
| FStar_Parser_Dep.Open_module -> begin
Open_module
end))
in (FStar_List.map (fun uu____11652 -> (match (uu____11652) with
| (lid, kind) -> begin
((lid), ((convert_kind kind)))
end)) auto_open))
in (

let namespace_of_module = (match (((FStar_List.length mname.FStar_Ident.ns) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____11676 = (

let uu____11681 = (FStar_Ident.lid_of_ids mname.FStar_Ident.ns)
in ((uu____11681), (Open_namespace)))
in (uu____11676)::[])
end
| uu____11690 -> begin
[]
end)
in (

let auto_open2 = (FStar_List.append namespace_of_module (FStar_List.rev auto_open1))
in ((

let uu____11711 = (as_exported_id_set mii.mii_exported_ids)
in (FStar_Util.smap_add env1.exported_ids mname.FStar_Ident.str uu____11711));
(match (()) with
| () -> begin
((

let uu____11727 = (as_exported_id_set mii.mii_trans_exported_ids)
in (FStar_Util.smap_add env1.trans_exported_ids mname.FStar_Ident.str uu____11727));
(match (()) with
| () -> begin
((

let uu____11743 = (as_includes mii.mii_includes)
in (FStar_Util.smap_add env1.includes mname.FStar_Ident.str uu____11743));
(match (()) with
| () -> begin
(

let env' = (

let uu___204_11767 = env1
in (

let uu____11768 = (FStar_List.map (fun x -> Open_module_or_namespace (x)) auto_open2)
in {curmodule = FStar_Pervasives_Native.Some (mname); curmonad = uu___204_11767.curmonad; modules = uu___204_11767.modules; scope_mods = uu____11768; exported_ids = uu___204_11767.exported_ids; trans_exported_ids = uu___204_11767.trans_exported_ids; includes = uu___204_11767.includes; sigaccum = uu___204_11767.sigaccum; sigmap = env1.sigmap; iface = intf; admitted_iface = admitted; expect_typ = uu___204_11767.expect_typ; docs = uu___204_11767.docs; remaining_iface_decls = uu___204_11767.remaining_iface_decls; syntax_only = uu___204_11767.syntax_only; ds_hooks = uu___204_11767.ds_hooks}))
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

let uu____11780 = (FStar_All.pipe_right env.modules (FStar_Util.find_opt (fun uu____11806 -> (match (uu____11806) with
| (l, uu____11812) -> begin
(FStar_Ident.lid_equals l mname)
end))))
in (match (uu____11780) with
| FStar_Pervasives_Native.None -> begin
(

let uu____11821 = (prep env)
in ((uu____11821), (false)))
end
| FStar_Pervasives_Native.Some (uu____11822, m) -> begin
((

let uu____11829 = ((

let uu____11832 = (FStar_Options.interactive ())
in (not (uu____11832))) && ((not (m.FStar_Syntax_Syntax.is_interface)) || intf))
in (match (uu____11829) with
| true -> begin
(

let uu____11833 = (

let uu____11834 = (

let uu____11839 = (FStar_Util.format1 "Duplicate module or interface name: %s" mname.FStar_Ident.str)
in ((uu____11839), ((FStar_Ident.range_of_lid mname))))
in FStar_Errors.Error (uu____11834))
in (FStar_Exn.raise uu____11833))
end
| uu____11840 -> begin
()
end));
(

let uu____11841 = (

let uu____11842 = (push env)
in (prep uu____11842))
in ((uu____11841), (true)));
)
end))))


let enter_monad_scope : env  ->  FStar_Ident.ident  ->  env = (fun env mname -> (match (env.curmonad) with
| FStar_Pervasives_Native.Some (mname') -> begin
(FStar_Exn.raise (FStar_Errors.Error ((((Prims.strcat "Trying to define monad " (Prims.strcat mname.FStar_Ident.idText (Prims.strcat ", but already in monad scope " mname'.FStar_Ident.idText)))), (mname.FStar_Ident.idRange)))))
end
| FStar_Pervasives_Native.None -> begin
(

let uu___205_11852 = env
in {curmodule = uu___205_11852.curmodule; curmonad = FStar_Pervasives_Native.Some (mname); modules = uu___205_11852.modules; scope_mods = uu___205_11852.scope_mods; exported_ids = uu___205_11852.exported_ids; trans_exported_ids = uu___205_11852.trans_exported_ids; includes = uu___205_11852.includes; sigaccum = uu___205_11852.sigaccum; sigmap = uu___205_11852.sigmap; iface = uu___205_11852.iface; admitted_iface = uu___205_11852.admitted_iface; expect_typ = uu___205_11852.expect_typ; docs = uu___205_11852.docs; remaining_iface_decls = uu___205_11852.remaining_iface_decls; syntax_only = uu___205_11852.syntax_only; ds_hooks = uu___205_11852.ds_hooks})
end))


let fail_or : 'a . env  ->  (FStar_Ident.lident  ->  'a FStar_Pervasives_Native.option)  ->  FStar_Ident.lident  ->  'a = (fun env lookup lid -> (

let uu____11883 = (lookup lid)
in (match (uu____11883) with
| FStar_Pervasives_Native.None -> begin
(

let opened_modules = (FStar_List.map (fun uu____11896 -> (match (uu____11896) with
| (lid1, uu____11902) -> begin
(FStar_Ident.text_of_lid lid1)
end)) env.modules)
in (

let msg = (FStar_Util.format1 "Identifier not found: [%s]" (FStar_Ident.text_of_lid lid))
in (

let msg1 = (match ((Prims.op_Equality (FStar_List.length lid.FStar_Ident.ns) (Prims.parse_int "0"))) with
| true -> begin
msg
end
| uu____11905 -> begin
(

let modul = (

let uu____11907 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in (FStar_Ident.set_lid_range uu____11907 (FStar_Ident.range_of_lid lid)))
in (

let uu____11908 = (resolve_module_name env modul true)
in (match (uu____11908) with
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
in (FStar_Exn.raise (FStar_Errors.Error (((msg1), ((FStar_Ident.range_of_lid lid)))))))))
end
| FStar_Pervasives_Native.Some (r) -> begin
r
end)))


let fail_or2 : 'a . (FStar_Ident.ident  ->  'a FStar_Pervasives_Native.option)  ->  FStar_Ident.ident  ->  'a = (fun lookup id -> (

let uu____11942 = (lookup id)
in (match (uu____11942) with
| FStar_Pervasives_Native.None -> begin
(FStar_Exn.raise (FStar_Errors.Error ((((Prims.strcat "Identifier not found [" (Prims.strcat id.FStar_Ident.idText "]"))), (id.FStar_Ident.idRange)))))
end
| FStar_Pervasives_Native.Some (r) -> begin
r
end)))




