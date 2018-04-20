open Prims
type local_binding =
  (FStar_Ident.ident, FStar_Syntax_Syntax.bv, Prims.bool)
    FStar_Pervasives_Native.tuple3[@@deriving show]
type rec_binding =
  (FStar_Ident.ident, FStar_Ident.lid, FStar_Syntax_Syntax.delta_depth)
    FStar_Pervasives_Native.tuple3[@@deriving show]
type module_abbrev =
  (FStar_Ident.ident, FStar_Ident.lident) FStar_Pervasives_Native.tuple2
[@@deriving show]
type open_kind =
  | Open_module 
  | Open_namespace [@@deriving show]
let (uu___is_Open_module : open_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | Open_module -> true | uu____20 -> false
let (uu___is_Open_namespace : open_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | Open_namespace -> true | uu____24 -> false
type open_module_or_namespace =
  (FStar_Ident.lident, open_kind) FStar_Pervasives_Native.tuple2[@@deriving
                                                                  show]
type record_or_dc =
  {
  typename: FStar_Ident.lident ;
  constrname: FStar_Ident.ident ;
  parms: FStar_Syntax_Syntax.binders ;
  fields:
    (FStar_Ident.ident, FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple2 Prims.list
    ;
  is_private_or_abstract: Prims.bool ;
  is_record: Prims.bool }[@@deriving show]
let (__proj__Mkrecord_or_dc__item__typename :
  record_or_dc -> FStar_Ident.lident) =
  fun projectee ->
    match projectee with
    | { typename = __fname__typename; constrname = __fname__constrname;
        parms = __fname__parms; fields = __fname__fields;
        is_private_or_abstract = __fname__is_private_or_abstract;
        is_record = __fname__is_record;_} -> __fname__typename
let (__proj__Mkrecord_or_dc__item__constrname :
  record_or_dc -> FStar_Ident.ident) =
  fun projectee ->
    match projectee with
    | { typename = __fname__typename; constrname = __fname__constrname;
        parms = __fname__parms; fields = __fname__fields;
        is_private_or_abstract = __fname__is_private_or_abstract;
        is_record = __fname__is_record;_} -> __fname__constrname
let (__proj__Mkrecord_or_dc__item__parms :
  record_or_dc -> FStar_Syntax_Syntax.binders) =
  fun projectee ->
    match projectee with
    | { typename = __fname__typename; constrname = __fname__constrname;
        parms = __fname__parms; fields = __fname__fields;
        is_private_or_abstract = __fname__is_private_or_abstract;
        is_record = __fname__is_record;_} -> __fname__parms
let (__proj__Mkrecord_or_dc__item__fields :
  record_or_dc ->
    (FStar_Ident.ident, FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun projectee ->
    match projectee with
    | { typename = __fname__typename; constrname = __fname__constrname;
        parms = __fname__parms; fields = __fname__fields;
        is_private_or_abstract = __fname__is_private_or_abstract;
        is_record = __fname__is_record;_} -> __fname__fields
let (__proj__Mkrecord_or_dc__item__is_private_or_abstract :
  record_or_dc -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { typename = __fname__typename; constrname = __fname__constrname;
        parms = __fname__parms; fields = __fname__fields;
        is_private_or_abstract = __fname__is_private_or_abstract;
        is_record = __fname__is_record;_} -> __fname__is_private_or_abstract
let (__proj__Mkrecord_or_dc__item__is_record : record_or_dc -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { typename = __fname__typename; constrname = __fname__constrname;
        parms = __fname__parms; fields = __fname__fields;
        is_private_or_abstract = __fname__is_private_or_abstract;
        is_record = __fname__is_record;_} -> __fname__is_record
type scope_mod =
  | Local_binding of local_binding 
  | Rec_binding of rec_binding 
  | Module_abbrev of module_abbrev 
  | Open_module_or_namespace of open_module_or_namespace 
  | Top_level_def of FStar_Ident.ident 
  | Record_or_dc of record_or_dc [@@deriving show]
let (uu___is_Local_binding : scope_mod -> Prims.bool) =
  fun projectee ->
    match projectee with | Local_binding _0 -> true | uu____189 -> false
let (__proj__Local_binding__item___0 : scope_mod -> local_binding) =
  fun projectee -> match projectee with | Local_binding _0 -> _0
let (uu___is_Rec_binding : scope_mod -> Prims.bool) =
  fun projectee ->
    match projectee with | Rec_binding _0 -> true | uu____201 -> false
let (__proj__Rec_binding__item___0 : scope_mod -> rec_binding) =
  fun projectee -> match projectee with | Rec_binding _0 -> _0
let (uu___is_Module_abbrev : scope_mod -> Prims.bool) =
  fun projectee ->
    match projectee with | Module_abbrev _0 -> true | uu____213 -> false
let (__proj__Module_abbrev__item___0 : scope_mod -> module_abbrev) =
  fun projectee -> match projectee with | Module_abbrev _0 -> _0
let (uu___is_Open_module_or_namespace : scope_mod -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Open_module_or_namespace _0 -> true
    | uu____225 -> false
let (__proj__Open_module_or_namespace__item___0 :
  scope_mod -> open_module_or_namespace) =
  fun projectee -> match projectee with | Open_module_or_namespace _0 -> _0
let (uu___is_Top_level_def : scope_mod -> Prims.bool) =
  fun projectee ->
    match projectee with | Top_level_def _0 -> true | uu____237 -> false
let (__proj__Top_level_def__item___0 : scope_mod -> FStar_Ident.ident) =
  fun projectee -> match projectee with | Top_level_def _0 -> _0
let (uu___is_Record_or_dc : scope_mod -> Prims.bool) =
  fun projectee ->
    match projectee with | Record_or_dc _0 -> true | uu____249 -> false
let (__proj__Record_or_dc__item___0 : scope_mod -> record_or_dc) =
  fun projectee -> match projectee with | Record_or_dc _0 -> _0
type string_set = Prims.string FStar_Util.set[@@deriving show]
type exported_id_kind =
  | Exported_id_term_type 
  | Exported_id_field [@@deriving show]
let (uu___is_Exported_id_term_type : exported_id_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | Exported_id_term_type -> true | uu____262 -> false
let (uu___is_Exported_id_field : exported_id_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | Exported_id_field -> true | uu____266 -> false
type exported_id_set = exported_id_kind -> string_set FStar_ST.ref[@@deriving
                                                                    show]
type env =
  {
  curmodule: FStar_Ident.lident FStar_Pervasives_Native.option ;
  curmonad: FStar_Ident.ident FStar_Pervasives_Native.option ;
  modules:
    (FStar_Ident.lident, FStar_Syntax_Syntax.modul)
      FStar_Pervasives_Native.tuple2 Prims.list
    ;
  scope_mods: scope_mod Prims.list ;
  exported_ids: exported_id_set FStar_Util.smap ;
  trans_exported_ids: exported_id_set FStar_Util.smap ;
  includes: FStar_Ident.lident Prims.list FStar_ST.ref FStar_Util.smap ;
  sigaccum: FStar_Syntax_Syntax.sigelts ;
  sigmap:
    (FStar_Syntax_Syntax.sigelt, Prims.bool) FStar_Pervasives_Native.tuple2
      FStar_Util.smap
    ;
  iface: Prims.bool ;
  admitted_iface: Prims.bool ;
  expect_typ: Prims.bool ;
  docs: FStar_Parser_AST.fsdoc FStar_Util.smap ;
  remaining_iface_decls:
    (FStar_Ident.lident, FStar_Parser_AST.decl Prims.list)
      FStar_Pervasives_Native.tuple2 Prims.list
    ;
  syntax_only: Prims.bool ;
  ds_hooks: dsenv_hooks }[@@deriving show]
and dsenv_hooks =
  {
  ds_push_open_hook: env -> open_module_or_namespace -> Prims.unit ;
  ds_push_include_hook: env -> FStar_Ident.lident -> Prims.unit ;
  ds_push_module_abbrev_hook:
    env -> FStar_Ident.ident -> FStar_Ident.lident -> Prims.unit }[@@deriving
                                                                    show]
let (__proj__Mkenv__item__curmodule :
  env -> FStar_Ident.lident FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { curmodule = __fname__curmodule; curmonad = __fname__curmonad;
        modules = __fname__modules; scope_mods = __fname__scope_mods;
        exported_ids = __fname__exported_ids;
        trans_exported_ids = __fname__trans_exported_ids;
        includes = __fname__includes; sigaccum = __fname__sigaccum;
        sigmap = __fname__sigmap; iface = __fname__iface;
        admitted_iface = __fname__admitted_iface;
        expect_typ = __fname__expect_typ; docs = __fname__docs;
        remaining_iface_decls = __fname__remaining_iface_decls;
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;_}
        -> __fname__curmodule
let (__proj__Mkenv__item__curmonad :
  env -> FStar_Ident.ident FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { curmodule = __fname__curmodule; curmonad = __fname__curmonad;
        modules = __fname__modules; scope_mods = __fname__scope_mods;
        exported_ids = __fname__exported_ids;
        trans_exported_ids = __fname__trans_exported_ids;
        includes = __fname__includes; sigaccum = __fname__sigaccum;
        sigmap = __fname__sigmap; iface = __fname__iface;
        admitted_iface = __fname__admitted_iface;
        expect_typ = __fname__expect_typ; docs = __fname__docs;
        remaining_iface_decls = __fname__remaining_iface_decls;
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;_}
        -> __fname__curmonad
let (__proj__Mkenv__item__modules :
  env ->
    (FStar_Ident.lident, FStar_Syntax_Syntax.modul)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun projectee ->
    match projectee with
    | { curmodule = __fname__curmodule; curmonad = __fname__curmonad;
        modules = __fname__modules; scope_mods = __fname__scope_mods;
        exported_ids = __fname__exported_ids;
        trans_exported_ids = __fname__trans_exported_ids;
        includes = __fname__includes; sigaccum = __fname__sigaccum;
        sigmap = __fname__sigmap; iface = __fname__iface;
        admitted_iface = __fname__admitted_iface;
        expect_typ = __fname__expect_typ; docs = __fname__docs;
        remaining_iface_decls = __fname__remaining_iface_decls;
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;_}
        -> __fname__modules
let (__proj__Mkenv__item__scope_mods : env -> scope_mod Prims.list) =
  fun projectee ->
    match projectee with
    | { curmodule = __fname__curmodule; curmonad = __fname__curmonad;
        modules = __fname__modules; scope_mods = __fname__scope_mods;
        exported_ids = __fname__exported_ids;
        trans_exported_ids = __fname__trans_exported_ids;
        includes = __fname__includes; sigaccum = __fname__sigaccum;
        sigmap = __fname__sigmap; iface = __fname__iface;
        admitted_iface = __fname__admitted_iface;
        expect_typ = __fname__expect_typ; docs = __fname__docs;
        remaining_iface_decls = __fname__remaining_iface_decls;
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;_}
        -> __fname__scope_mods
let (__proj__Mkenv__item__exported_ids :
  env -> exported_id_set FStar_Util.smap) =
  fun projectee ->
    match projectee with
    | { curmodule = __fname__curmodule; curmonad = __fname__curmonad;
        modules = __fname__modules; scope_mods = __fname__scope_mods;
        exported_ids = __fname__exported_ids;
        trans_exported_ids = __fname__trans_exported_ids;
        includes = __fname__includes; sigaccum = __fname__sigaccum;
        sigmap = __fname__sigmap; iface = __fname__iface;
        admitted_iface = __fname__admitted_iface;
        expect_typ = __fname__expect_typ; docs = __fname__docs;
        remaining_iface_decls = __fname__remaining_iface_decls;
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;_}
        -> __fname__exported_ids
let (__proj__Mkenv__item__trans_exported_ids :
  env -> exported_id_set FStar_Util.smap) =
  fun projectee ->
    match projectee with
    | { curmodule = __fname__curmodule; curmonad = __fname__curmonad;
        modules = __fname__modules; scope_mods = __fname__scope_mods;
        exported_ids = __fname__exported_ids;
        trans_exported_ids = __fname__trans_exported_ids;
        includes = __fname__includes; sigaccum = __fname__sigaccum;
        sigmap = __fname__sigmap; iface = __fname__iface;
        admitted_iface = __fname__admitted_iface;
        expect_typ = __fname__expect_typ; docs = __fname__docs;
        remaining_iface_decls = __fname__remaining_iface_decls;
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;_}
        -> __fname__trans_exported_ids
let (__proj__Mkenv__item__includes :
  env -> FStar_Ident.lident Prims.list FStar_ST.ref FStar_Util.smap) =
  fun projectee ->
    match projectee with
    | { curmodule = __fname__curmodule; curmonad = __fname__curmonad;
        modules = __fname__modules; scope_mods = __fname__scope_mods;
        exported_ids = __fname__exported_ids;
        trans_exported_ids = __fname__trans_exported_ids;
        includes = __fname__includes; sigaccum = __fname__sigaccum;
        sigmap = __fname__sigmap; iface = __fname__iface;
        admitted_iface = __fname__admitted_iface;
        expect_typ = __fname__expect_typ; docs = __fname__docs;
        remaining_iface_decls = __fname__remaining_iface_decls;
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;_}
        -> __fname__includes
let (__proj__Mkenv__item__sigaccum : env -> FStar_Syntax_Syntax.sigelts) =
  fun projectee ->
    match projectee with
    | { curmodule = __fname__curmodule; curmonad = __fname__curmonad;
        modules = __fname__modules; scope_mods = __fname__scope_mods;
        exported_ids = __fname__exported_ids;
        trans_exported_ids = __fname__trans_exported_ids;
        includes = __fname__includes; sigaccum = __fname__sigaccum;
        sigmap = __fname__sigmap; iface = __fname__iface;
        admitted_iface = __fname__admitted_iface;
        expect_typ = __fname__expect_typ; docs = __fname__docs;
        remaining_iface_decls = __fname__remaining_iface_decls;
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;_}
        -> __fname__sigaccum
let (__proj__Mkenv__item__sigmap :
  env ->
    (FStar_Syntax_Syntax.sigelt, Prims.bool) FStar_Pervasives_Native.tuple2
      FStar_Util.smap)
  =
  fun projectee ->
    match projectee with
    | { curmodule = __fname__curmodule; curmonad = __fname__curmonad;
        modules = __fname__modules; scope_mods = __fname__scope_mods;
        exported_ids = __fname__exported_ids;
        trans_exported_ids = __fname__trans_exported_ids;
        includes = __fname__includes; sigaccum = __fname__sigaccum;
        sigmap = __fname__sigmap; iface = __fname__iface;
        admitted_iface = __fname__admitted_iface;
        expect_typ = __fname__expect_typ; docs = __fname__docs;
        remaining_iface_decls = __fname__remaining_iface_decls;
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;_}
        -> __fname__sigmap
let (__proj__Mkenv__item__iface : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { curmodule = __fname__curmodule; curmonad = __fname__curmonad;
        modules = __fname__modules; scope_mods = __fname__scope_mods;
        exported_ids = __fname__exported_ids;
        trans_exported_ids = __fname__trans_exported_ids;
        includes = __fname__includes; sigaccum = __fname__sigaccum;
        sigmap = __fname__sigmap; iface = __fname__iface;
        admitted_iface = __fname__admitted_iface;
        expect_typ = __fname__expect_typ; docs = __fname__docs;
        remaining_iface_decls = __fname__remaining_iface_decls;
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;_}
        -> __fname__iface
let (__proj__Mkenv__item__admitted_iface : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { curmodule = __fname__curmodule; curmonad = __fname__curmonad;
        modules = __fname__modules; scope_mods = __fname__scope_mods;
        exported_ids = __fname__exported_ids;
        trans_exported_ids = __fname__trans_exported_ids;
        includes = __fname__includes; sigaccum = __fname__sigaccum;
        sigmap = __fname__sigmap; iface = __fname__iface;
        admitted_iface = __fname__admitted_iface;
        expect_typ = __fname__expect_typ; docs = __fname__docs;
        remaining_iface_decls = __fname__remaining_iface_decls;
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;_}
        -> __fname__admitted_iface
let (__proj__Mkenv__item__expect_typ : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { curmodule = __fname__curmodule; curmonad = __fname__curmonad;
        modules = __fname__modules; scope_mods = __fname__scope_mods;
        exported_ids = __fname__exported_ids;
        trans_exported_ids = __fname__trans_exported_ids;
        includes = __fname__includes; sigaccum = __fname__sigaccum;
        sigmap = __fname__sigmap; iface = __fname__iface;
        admitted_iface = __fname__admitted_iface;
        expect_typ = __fname__expect_typ; docs = __fname__docs;
        remaining_iface_decls = __fname__remaining_iface_decls;
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;_}
        -> __fname__expect_typ
let (__proj__Mkenv__item__docs :
  env -> FStar_Parser_AST.fsdoc FStar_Util.smap) =
  fun projectee ->
    match projectee with
    | { curmodule = __fname__curmodule; curmonad = __fname__curmonad;
        modules = __fname__modules; scope_mods = __fname__scope_mods;
        exported_ids = __fname__exported_ids;
        trans_exported_ids = __fname__trans_exported_ids;
        includes = __fname__includes; sigaccum = __fname__sigaccum;
        sigmap = __fname__sigmap; iface = __fname__iface;
        admitted_iface = __fname__admitted_iface;
        expect_typ = __fname__expect_typ; docs = __fname__docs;
        remaining_iface_decls = __fname__remaining_iface_decls;
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;_}
        -> __fname__docs
let (__proj__Mkenv__item__remaining_iface_decls :
  env ->
    (FStar_Ident.lident, FStar_Parser_AST.decl Prims.list)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun projectee ->
    match projectee with
    | { curmodule = __fname__curmodule; curmonad = __fname__curmonad;
        modules = __fname__modules; scope_mods = __fname__scope_mods;
        exported_ids = __fname__exported_ids;
        trans_exported_ids = __fname__trans_exported_ids;
        includes = __fname__includes; sigaccum = __fname__sigaccum;
        sigmap = __fname__sigmap; iface = __fname__iface;
        admitted_iface = __fname__admitted_iface;
        expect_typ = __fname__expect_typ; docs = __fname__docs;
        remaining_iface_decls = __fname__remaining_iface_decls;
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;_}
        -> __fname__remaining_iface_decls
let (__proj__Mkenv__item__syntax_only : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { curmodule = __fname__curmodule; curmonad = __fname__curmonad;
        modules = __fname__modules; scope_mods = __fname__scope_mods;
        exported_ids = __fname__exported_ids;
        trans_exported_ids = __fname__trans_exported_ids;
        includes = __fname__includes; sigaccum = __fname__sigaccum;
        sigmap = __fname__sigmap; iface = __fname__iface;
        admitted_iface = __fname__admitted_iface;
        expect_typ = __fname__expect_typ; docs = __fname__docs;
        remaining_iface_decls = __fname__remaining_iface_decls;
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;_}
        -> __fname__syntax_only
let (__proj__Mkenv__item__ds_hooks : env -> dsenv_hooks) =
  fun projectee ->
    match projectee with
    | { curmodule = __fname__curmodule; curmonad = __fname__curmonad;
        modules = __fname__modules; scope_mods = __fname__scope_mods;
        exported_ids = __fname__exported_ids;
        trans_exported_ids = __fname__trans_exported_ids;
        includes = __fname__includes; sigaccum = __fname__sigaccum;
        sigmap = __fname__sigmap; iface = __fname__iface;
        admitted_iface = __fname__admitted_iface;
        expect_typ = __fname__expect_typ; docs = __fname__docs;
        remaining_iface_decls = __fname__remaining_iface_decls;
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;_}
        -> __fname__ds_hooks
let (__proj__Mkdsenv_hooks__item__ds_push_open_hook :
  dsenv_hooks -> env -> open_module_or_namespace -> Prims.unit) =
  fun projectee ->
    match projectee with
    | { ds_push_open_hook = __fname__ds_push_open_hook;
        ds_push_include_hook = __fname__ds_push_include_hook;
        ds_push_module_abbrev_hook = __fname__ds_push_module_abbrev_hook;_}
        -> __fname__ds_push_open_hook
let (__proj__Mkdsenv_hooks__item__ds_push_include_hook :
  dsenv_hooks -> env -> FStar_Ident.lident -> Prims.unit) =
  fun projectee ->
    match projectee with
    | { ds_push_open_hook = __fname__ds_push_open_hook;
        ds_push_include_hook = __fname__ds_push_include_hook;
        ds_push_module_abbrev_hook = __fname__ds_push_module_abbrev_hook;_}
        -> __fname__ds_push_include_hook
let (__proj__Mkdsenv_hooks__item__ds_push_module_abbrev_hook :
  dsenv_hooks -> env -> FStar_Ident.ident -> FStar_Ident.lident -> Prims.unit)
  =
  fun projectee ->
    match projectee with
    | { ds_push_open_hook = __fname__ds_push_open_hook;
        ds_push_include_hook = __fname__ds_push_include_hook;
        ds_push_module_abbrev_hook = __fname__ds_push_module_abbrev_hook;_}
        -> __fname__ds_push_module_abbrev_hook
type 'a withenv = env -> ('a, env) FStar_Pervasives_Native.tuple2[@@deriving
                                                                   show]
let (default_ds_hooks : dsenv_hooks) =
  {
    ds_push_open_hook = (fun uu____1607 -> fun uu____1608 -> ());
    ds_push_include_hook = (fun uu____1611 -> fun uu____1612 -> ());
    ds_push_module_abbrev_hook =
      (fun uu____1616 -> fun uu____1617 -> fun uu____1618 -> ())
  }
type foundname =
  | Term_name of (FStar_Syntax_Syntax.typ, Prims.bool,
  FStar_Syntax_Syntax.attribute Prims.list) FStar_Pervasives_Native.tuple3 
  | Eff_name of (FStar_Syntax_Syntax.sigelt, FStar_Ident.lident)
  FStar_Pervasives_Native.tuple2 [@@deriving show]
let (uu___is_Term_name : foundname -> Prims.bool) =
  fun projectee ->
    match projectee with | Term_name _0 -> true | uu____1651 -> false
let (__proj__Term_name__item___0 :
  foundname ->
    (FStar_Syntax_Syntax.typ, Prims.bool,
      FStar_Syntax_Syntax.attribute Prims.list)
      FStar_Pervasives_Native.tuple3)
  = fun projectee -> match projectee with | Term_name _0 -> _0
let (uu___is_Eff_name : foundname -> Prims.bool) =
  fun projectee ->
    match projectee with | Eff_name _0 -> true | uu____1691 -> false
let (__proj__Eff_name__item___0 :
  foundname ->
    (FStar_Syntax_Syntax.sigelt, FStar_Ident.lident)
      FStar_Pervasives_Native.tuple2)
  = fun projectee -> match projectee with | Eff_name _0 -> _0
let (set_iface : env -> Prims.bool -> env) =
  fun env ->
    fun b ->
      let uu___115_1717 = env in
      {
        curmodule = (uu___115_1717.curmodule);
        curmonad = (uu___115_1717.curmonad);
        modules = (uu___115_1717.modules);
        scope_mods = (uu___115_1717.scope_mods);
        exported_ids = (uu___115_1717.exported_ids);
        trans_exported_ids = (uu___115_1717.trans_exported_ids);
        includes = (uu___115_1717.includes);
        sigaccum = (uu___115_1717.sigaccum);
        sigmap = (uu___115_1717.sigmap);
        iface = b;
        admitted_iface = (uu___115_1717.admitted_iface);
        expect_typ = (uu___115_1717.expect_typ);
        docs = (uu___115_1717.docs);
        remaining_iface_decls = (uu___115_1717.remaining_iface_decls);
        syntax_only = (uu___115_1717.syntax_only);
        ds_hooks = (uu___115_1717.ds_hooks)
      }
let (iface : env -> Prims.bool) = fun e -> e.iface
let (set_admitted_iface : env -> Prims.bool -> env) =
  fun e ->
    fun b ->
      let uu___116_1727 = e in
      {
        curmodule = (uu___116_1727.curmodule);
        curmonad = (uu___116_1727.curmonad);
        modules = (uu___116_1727.modules);
        scope_mods = (uu___116_1727.scope_mods);
        exported_ids = (uu___116_1727.exported_ids);
        trans_exported_ids = (uu___116_1727.trans_exported_ids);
        includes = (uu___116_1727.includes);
        sigaccum = (uu___116_1727.sigaccum);
        sigmap = (uu___116_1727.sigmap);
        iface = (uu___116_1727.iface);
        admitted_iface = b;
        expect_typ = (uu___116_1727.expect_typ);
        docs = (uu___116_1727.docs);
        remaining_iface_decls = (uu___116_1727.remaining_iface_decls);
        syntax_only = (uu___116_1727.syntax_only);
        ds_hooks = (uu___116_1727.ds_hooks)
      }
let (admitted_iface : env -> Prims.bool) = fun e -> e.admitted_iface
let (set_expect_typ : env -> Prims.bool -> env) =
  fun e ->
    fun b ->
      let uu___117_1737 = e in
      {
        curmodule = (uu___117_1737.curmodule);
        curmonad = (uu___117_1737.curmonad);
        modules = (uu___117_1737.modules);
        scope_mods = (uu___117_1737.scope_mods);
        exported_ids = (uu___117_1737.exported_ids);
        trans_exported_ids = (uu___117_1737.trans_exported_ids);
        includes = (uu___117_1737.includes);
        sigaccum = (uu___117_1737.sigaccum);
        sigmap = (uu___117_1737.sigmap);
        iface = (uu___117_1737.iface);
        admitted_iface = (uu___117_1737.admitted_iface);
        expect_typ = b;
        docs = (uu___117_1737.docs);
        remaining_iface_decls = (uu___117_1737.remaining_iface_decls);
        syntax_only = (uu___117_1737.syntax_only);
        ds_hooks = (uu___117_1737.ds_hooks)
      }
let (expect_typ : env -> Prims.bool) = fun e -> e.expect_typ
let (all_exported_id_kinds : exported_id_kind Prims.list) =
  [Exported_id_field; Exported_id_term_type]
let (transitive_exported_ids :
  env -> FStar_Ident.lident -> Prims.string Prims.list) =
  fun env ->
    fun lid ->
      let module_name = FStar_Ident.string_of_lid lid in
      let uu____1752 =
        FStar_Util.smap_try_find env.trans_exported_ids module_name in
      match uu____1752 with
      | FStar_Pervasives_Native.None -> []
      | FStar_Pervasives_Native.Some exported_id_set ->
          let uu____1758 =
            let uu____1759 = exported_id_set Exported_id_term_type in
            FStar_ST.op_Bang uu____1759 in
          FStar_All.pipe_right uu____1758 FStar_Util.set_elements
let (open_modules :
  env ->
    (FStar_Ident.lident, FStar_Syntax_Syntax.modul)
      FStar_Pervasives_Native.tuple2 Prims.list)
  = fun e -> e.modules
let (open_modules_and_namespaces : env -> FStar_Ident.lident Prims.list) =
  fun env ->
    FStar_List.filter_map
      (fun uu___83_1955 ->
         match uu___83_1955 with
         | Open_module_or_namespace (lid, _info) ->
             FStar_Pervasives_Native.Some lid
         | uu____1960 -> FStar_Pervasives_Native.None) env.scope_mods
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun e ->
    fun l ->
      let uu___118_1967 = e in
      {
        curmodule = (FStar_Pervasives_Native.Some l);
        curmonad = (uu___118_1967.curmonad);
        modules = (uu___118_1967.modules);
        scope_mods = (uu___118_1967.scope_mods);
        exported_ids = (uu___118_1967.exported_ids);
        trans_exported_ids = (uu___118_1967.trans_exported_ids);
        includes = (uu___118_1967.includes);
        sigaccum = (uu___118_1967.sigaccum);
        sigmap = (uu___118_1967.sigmap);
        iface = (uu___118_1967.iface);
        admitted_iface = (uu___118_1967.admitted_iface);
        expect_typ = (uu___118_1967.expect_typ);
        docs = (uu___118_1967.docs);
        remaining_iface_decls = (uu___118_1967.remaining_iface_decls);
        syntax_only = (uu___118_1967.syntax_only);
        ds_hooks = (uu___118_1967.ds_hooks)
      }
let (current_module : env -> FStar_Ident.lident) =
  fun env ->
    match env.curmodule with
    | FStar_Pervasives_Native.None -> failwith "Unset current module"
    | FStar_Pervasives_Native.Some m -> m
let (iface_decls :
  env ->
    FStar_Ident.lident ->
      FStar_Parser_AST.decl Prims.list FStar_Pervasives_Native.option)
  =
  fun env ->
    fun l ->
      let uu____1982 =
        FStar_All.pipe_right env.remaining_iface_decls
          (FStar_List.tryFind
             (fun uu____2016 ->
                match uu____2016 with
                | (m, uu____2024) -> FStar_Ident.lid_equals l m)) in
      match uu____1982 with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (uu____2041, decls) ->
          FStar_Pervasives_Native.Some decls
let (set_iface_decls :
  env -> FStar_Ident.lident -> FStar_Parser_AST.decl Prims.list -> env) =
  fun env ->
    fun l ->
      fun ds ->
        let uu____2068 =
          FStar_List.partition
            (fun uu____2098 ->
               match uu____2098 with
               | (m, uu____2106) -> FStar_Ident.lid_equals l m)
            env.remaining_iface_decls in
        match uu____2068 with
        | (uu____2111, rest) ->
            let uu___119_2145 = env in
            {
              curmodule = (uu___119_2145.curmodule);
              curmonad = (uu___119_2145.curmonad);
              modules = (uu___119_2145.modules);
              scope_mods = (uu___119_2145.scope_mods);
              exported_ids = (uu___119_2145.exported_ids);
              trans_exported_ids = (uu___119_2145.trans_exported_ids);
              includes = (uu___119_2145.includes);
              sigaccum = (uu___119_2145.sigaccum);
              sigmap = (uu___119_2145.sigmap);
              iface = (uu___119_2145.iface);
              admitted_iface = (uu___119_2145.admitted_iface);
              expect_typ = (uu___119_2145.expect_typ);
              docs = (uu___119_2145.docs);
              remaining_iface_decls = ((l, ds) :: rest);
              syntax_only = (uu___119_2145.syntax_only);
              ds_hooks = (uu___119_2145.ds_hooks)
            }
let (qual : FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident) =
  FStar_Syntax_Util.qual_id
let (qualify : env -> FStar_Ident.ident -> FStar_Ident.lident) =
  fun env ->
    fun id1 ->
      match env.curmonad with
      | FStar_Pervasives_Native.None ->
          let uu____2164 = current_module env in qual uu____2164 id1
      | FStar_Pervasives_Native.Some monad ->
          let uu____2166 =
            let uu____2167 = current_module env in qual uu____2167 monad in
          FStar_Syntax_Util.mk_field_projector_name_from_ident uu____2166 id1
let (syntax_only : env -> Prims.bool) = fun env -> env.syntax_only
let (set_syntax_only : env -> Prims.bool -> env) =
  fun env ->
    fun b ->
      let uu___120_2177 = env in
      {
        curmodule = (uu___120_2177.curmodule);
        curmonad = (uu___120_2177.curmonad);
        modules = (uu___120_2177.modules);
        scope_mods = (uu___120_2177.scope_mods);
        exported_ids = (uu___120_2177.exported_ids);
        trans_exported_ids = (uu___120_2177.trans_exported_ids);
        includes = (uu___120_2177.includes);
        sigaccum = (uu___120_2177.sigaccum);
        sigmap = (uu___120_2177.sigmap);
        iface = (uu___120_2177.iface);
        admitted_iface = (uu___120_2177.admitted_iface);
        expect_typ = (uu___120_2177.expect_typ);
        docs = (uu___120_2177.docs);
        remaining_iface_decls = (uu___120_2177.remaining_iface_decls);
        syntax_only = b;
        ds_hooks = (uu___120_2177.ds_hooks)
      }
let (ds_hooks : env -> dsenv_hooks) = fun env -> env.ds_hooks
let (set_ds_hooks : env -> dsenv_hooks -> env) =
  fun env ->
    fun hooks ->
      let uu___121_2187 = env in
      {
        curmodule = (uu___121_2187.curmodule);
        curmonad = (uu___121_2187.curmonad);
        modules = (uu___121_2187.modules);
        scope_mods = (uu___121_2187.scope_mods);
        exported_ids = (uu___121_2187.exported_ids);
        trans_exported_ids = (uu___121_2187.trans_exported_ids);
        includes = (uu___121_2187.includes);
        sigaccum = (uu___121_2187.sigaccum);
        sigmap = (uu___121_2187.sigmap);
        iface = (uu___121_2187.iface);
        admitted_iface = (uu___121_2187.admitted_iface);
        expect_typ = (uu___121_2187.expect_typ);
        docs = (uu___121_2187.docs);
        remaining_iface_decls = (uu___121_2187.remaining_iface_decls);
        syntax_only = (uu___121_2187.syntax_only);
        ds_hooks = hooks
      }
let new_sigmap : 'Auu____2190 . Prims.unit -> 'Auu____2190 FStar_Util.smap =
  fun uu____2196 -> FStar_Util.smap_create (Prims.parse_int "100")
let (empty_env : Prims.unit -> env) =
  fun uu____2199 ->
    let uu____2200 = new_sigmap () in
    let uu____2203 = new_sigmap () in
    let uu____2206 = new_sigmap () in
    let uu____2217 = new_sigmap () in
    let uu____2228 = new_sigmap () in
    {
      curmodule = FStar_Pervasives_Native.None;
      curmonad = FStar_Pervasives_Native.None;
      modules = [];
      scope_mods = [];
      exported_ids = uu____2200;
      trans_exported_ids = uu____2203;
      includes = uu____2206;
      sigaccum = [];
      sigmap = uu____2217;
      iface = false;
      admitted_iface = false;
      expect_typ = false;
      docs = uu____2228;
      remaining_iface_decls = [];
      syntax_only = false;
      ds_hooks = default_ds_hooks
    }
let (sigmap :
  env ->
    (FStar_Syntax_Syntax.sigelt, Prims.bool) FStar_Pervasives_Native.tuple2
      FStar_Util.smap)
  = fun env -> env.sigmap
let (has_all_in_scope : env -> Prims.bool) =
  fun env ->
    FStar_List.existsb
      (fun uu____2260 ->
         match uu____2260 with
         | (m, uu____2266) ->
             FStar_Ident.lid_equals m FStar_Parser_Const.all_lid) env.modules
let (set_bv_range :
  FStar_Syntax_Syntax.bv -> FStar_Range.range -> FStar_Syntax_Syntax.bv) =
  fun bv ->
    fun r ->
      let id1 =
        let uu___122_2274 = bv.FStar_Syntax_Syntax.ppname in
        {
          FStar_Ident.idText = (uu___122_2274.FStar_Ident.idText);
          FStar_Ident.idRange = r
        } in
      let uu___123_2275 = bv in
      {
        FStar_Syntax_Syntax.ppname = id1;
        FStar_Syntax_Syntax.index = (uu___123_2275.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = (uu___123_2275.FStar_Syntax_Syntax.sort)
      }
let (bv_to_name :
  FStar_Syntax_Syntax.bv -> FStar_Range.range -> FStar_Syntax_Syntax.term) =
  fun bv -> fun r -> FStar_Syntax_Syntax.bv_to_name (set_bv_range bv r)
let (unmangleMap :
  (Prims.string, Prims.string, FStar_Syntax_Syntax.delta_depth,
    FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple4 Prims.list)
  =
  [("op_ColonColon", "Cons", FStar_Syntax_Syntax.Delta_constant,
     (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor));
  ("not", "op_Negation", FStar_Syntax_Syntax.Delta_equational,
    FStar_Pervasives_Native.None)]
let (unmangleOpName :
  FStar_Ident.ident ->
    (FStar_Syntax_Syntax.term, Prims.bool) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option)
  =
  fun id1 ->
    let t =
      FStar_Util.find_map unmangleMap
        (fun uu____2362 ->
           match uu____2362 with
           | (x, y, dd, dq) ->
               if id1.FStar_Ident.idText = x
               then
                 let uu____2385 =
                   let uu____2386 =
                     FStar_Ident.lid_of_path ["Prims"; y]
                       id1.FStar_Ident.idRange in
                   FStar_Syntax_Syntax.fvar uu____2386 dd dq in
                 FStar_Pervasives_Native.Some uu____2385
               else FStar_Pervasives_Native.None) in
    match t with
    | FStar_Pervasives_Native.Some v1 ->
        FStar_Pervasives_Native.Some (v1, false)
    | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
type 'a cont_t =
  | Cont_ok of 'a 
  | Cont_fail 
  | Cont_ignore [@@deriving show]
let uu___is_Cont_ok : 'a . 'a cont_t -> Prims.bool =
  fun projectee ->
    match projectee with | Cont_ok _0 -> true | uu____2429 -> false
let __proj__Cont_ok__item___0 : 'a . 'a cont_t -> 'a =
  fun projectee -> match projectee with | Cont_ok _0 -> _0
let uu___is_Cont_fail : 'a . 'a cont_t -> Prims.bool =
  fun projectee ->
    match projectee with | Cont_fail -> true | uu____2458 -> false
let uu___is_Cont_ignore : 'a . 'a cont_t -> Prims.bool =
  fun projectee ->
    match projectee with | Cont_ignore -> true | uu____2472 -> false
let option_of_cont :
  'a .
    (Prims.unit -> 'a FStar_Pervasives_Native.option) ->
      'a cont_t -> 'a FStar_Pervasives_Native.option
  =
  fun k_ignore ->
    fun uu___84_2495 ->
      match uu___84_2495 with
      | Cont_ok a -> FStar_Pervasives_Native.Some a
      | Cont_fail -> FStar_Pervasives_Native.None
      | Cont_ignore -> k_ignore ()
let find_in_record :
  'Auu____2508 .
    FStar_Ident.ident Prims.list ->
      FStar_Ident.ident ->
        record_or_dc ->
          (record_or_dc -> 'Auu____2508 cont_t) -> 'Auu____2508 cont_t
  =
  fun ns ->
    fun id1 ->
      fun record ->
        fun cont ->
          let typename' =
            FStar_Ident.lid_of_ids
              (FStar_List.append ns [(record.typename).FStar_Ident.ident]) in
          if FStar_Ident.lid_equals typename' record.typename
          then
            let fname =
              FStar_Ident.lid_of_ids
                (FStar_List.append (record.typename).FStar_Ident.ns [id1]) in
            let find1 =
              FStar_Util.find_map record.fields
                (fun uu____2554 ->
                   match uu____2554 with
                   | (f, uu____2562) ->
                       if id1.FStar_Ident.idText = f.FStar_Ident.idText
                       then FStar_Pervasives_Native.Some record
                       else FStar_Pervasives_Native.None) in
            match find1 with
            | FStar_Pervasives_Native.Some r -> cont r
            | FStar_Pervasives_Native.None -> Cont_ignore
          else Cont_ignore
let (get_exported_id_set :
  env ->
    Prims.string ->
      (exported_id_kind -> string_set FStar_ST.ref)
        FStar_Pervasives_Native.option)
  = fun e -> fun mname -> FStar_Util.smap_try_find e.exported_ids mname
let (get_trans_exported_id_set :
  env ->
    Prims.string ->
      (exported_id_kind -> string_set FStar_ST.ref)
        FStar_Pervasives_Native.option)
  = fun e -> fun mname -> FStar_Util.smap_try_find e.trans_exported_ids mname
let (string_of_exported_id_kind : exported_id_kind -> Prims.string) =
  fun uu___85_2608 ->
    match uu___85_2608 with
    | Exported_id_field -> "field"
    | Exported_id_term_type -> "term/type"
let find_in_module_with_includes :
  'a .
    exported_id_kind ->
      (FStar_Ident.lident -> 'a cont_t) ->
        'a cont_t ->
          env -> FStar_Ident.lident -> FStar_Ident.ident -> 'a cont_t
  =
  fun eikind ->
    fun find_in_module ->
      fun find_in_module_default ->
        fun env ->
          fun ns ->
            fun id1 ->
              let idstr = id1.FStar_Ident.idText in
              let rec aux uu___86_2664 =
                match uu___86_2664 with
                | [] -> find_in_module_default
                | modul::q ->
                    let mname = modul.FStar_Ident.str in
                    let not_shadowed =
                      let uu____2675 = get_exported_id_set env mname in
                      match uu____2675 with
                      | FStar_Pervasives_Native.None -> true
                      | FStar_Pervasives_Native.Some mex ->
                          let mexports =
                            let uu____2696 = mex eikind in
                            FStar_ST.op_Bang uu____2696 in
                          FStar_Util.set_mem idstr mexports in
                    let mincludes =
                      let uu____2876 =
                        FStar_Util.smap_try_find env.includes mname in
                      match uu____2876 with
                      | FStar_Pervasives_Native.None -> []
                      | FStar_Pervasives_Native.Some minc ->
                          FStar_ST.op_Bang minc in
                    let look_into =
                      if not_shadowed
                      then
                        let uu____3006 = qual modul id1 in
                        find_in_module uu____3006
                      else Cont_ignore in
                    (match look_into with
                     | Cont_ignore -> aux (FStar_List.append mincludes q)
                     | uu____3010 -> look_into) in
              aux [ns]
let (is_exported_id_field : exported_id_kind -> Prims.bool) =
  fun uu___87_3015 ->
    match uu___87_3015 with | Exported_id_field -> true | uu____3016 -> false
let try_lookup_id'' :
  'a .
    env ->
      FStar_Ident.ident ->
        exported_id_kind ->
          (local_binding -> 'a cont_t) ->
            (rec_binding -> 'a cont_t) ->
              (record_or_dc -> 'a cont_t) ->
                (FStar_Ident.lident -> 'a cont_t) ->
                  ('a cont_t -> FStar_Ident.ident -> 'a cont_t) ->
                    'a FStar_Pervasives_Native.option
  =
  fun env ->
    fun id1 ->
      fun eikind ->
        fun k_local_binding ->
          fun k_rec_binding ->
            fun k_record ->
              fun find_in_module ->
                fun lookup_default_id ->
                  let check_local_binding_id uu___88_3118 =
                    match uu___88_3118 with
                    | (id', uu____3120, uu____3121) ->
                        id'.FStar_Ident.idText = id1.FStar_Ident.idText in
                  let check_rec_binding_id uu___89_3125 =
                    match uu___89_3125 with
                    | (id', uu____3127, uu____3128) ->
                        id'.FStar_Ident.idText = id1.FStar_Ident.idText in
                  let curmod_ns =
                    let uu____3132 = current_module env in
                    FStar_Ident.ids_of_lid uu____3132 in
                  let proc uu___90_3138 =
                    match uu___90_3138 with
                    | Local_binding l when check_local_binding_id l ->
                        k_local_binding l
                    | Rec_binding r when check_rec_binding_id r ->
                        k_rec_binding r
                    | Open_module_or_namespace (ns, Open_module) ->
                        find_in_module_with_includes eikind find_in_module
                          Cont_ignore env ns id1
                    | Top_level_def id' when
                        id'.FStar_Ident.idText = id1.FStar_Ident.idText ->
                        lookup_default_id Cont_ignore id1
                    | Record_or_dc r when is_exported_id_field eikind ->
                        let uu____3146 = FStar_Ident.lid_of_ids curmod_ns in
                        find_in_module_with_includes Exported_id_field
                          (fun lid ->
                             let id2 = lid.FStar_Ident.ident in
                             find_in_record lid.FStar_Ident.ns id2 r k_record)
                          Cont_ignore env uu____3146 id1
                    | uu____3151 -> Cont_ignore in
                  let rec aux uu___91_3159 =
                    match uu___91_3159 with
                    | a::q ->
                        let uu____3168 = proc a in
                        option_of_cont (fun uu____3172 -> aux q) uu____3168
                    | [] ->
                        let uu____3173 = lookup_default_id Cont_fail id1 in
                        option_of_cont
                          (fun uu____3177 -> FStar_Pervasives_Native.None)
                          uu____3173 in
                  aux env.scope_mods
let found_local_binding :
  'Auu____3182 'Auu____3183 .
    FStar_Range.range ->
      ('Auu____3182, FStar_Syntax_Syntax.bv, 'Auu____3183)
        FStar_Pervasives_Native.tuple3 ->
        (FStar_Syntax_Syntax.term, 'Auu____3183)
          FStar_Pervasives_Native.tuple2
  =
  fun r ->
    fun uu____3201 ->
      match uu____3201 with
      | (id', x, mut) -> let uu____3211 = bv_to_name x r in (uu____3211, mut)
let find_in_module :
  'Auu____3217 .
    env ->
      FStar_Ident.lident ->
        (FStar_Ident.lident ->
           (FStar_Syntax_Syntax.sigelt, Prims.bool)
             FStar_Pervasives_Native.tuple2 -> 'Auu____3217)
          -> 'Auu____3217 -> 'Auu____3217
  =
  fun env ->
    fun lid ->
      fun k_global_def ->
        fun k_not_found ->
          let uu____3252 =
            FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str in
          match uu____3252 with
          | FStar_Pervasives_Native.Some sb -> k_global_def lid sb
          | FStar_Pervasives_Native.None -> k_not_found
let (try_lookup_id :
  env ->
    FStar_Ident.ident ->
      (FStar_Syntax_Syntax.term, Prims.bool) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option)
  =
  fun env ->
    fun id1 ->
      let uu____3288 = unmangleOpName id1 in
      match uu____3288 with
      | FStar_Pervasives_Native.Some f -> FStar_Pervasives_Native.Some f
      | uu____3314 ->
          try_lookup_id'' env id1 Exported_id_term_type
            (fun r ->
               let uu____3328 = found_local_binding id1.FStar_Ident.idRange r in
               Cont_ok uu____3328) (fun uu____3338 -> Cont_fail)
            (fun uu____3344 -> Cont_ignore)
            (fun i ->
               find_in_module env i
                 (fun uu____3359 -> fun uu____3360 -> Cont_fail) Cont_ignore)
            (fun uu____3375 -> fun uu____3376 -> Cont_fail)
let lookup_default_id :
  'a .
    env ->
      FStar_Ident.ident ->
        (FStar_Ident.lident ->
           (FStar_Syntax_Syntax.sigelt, Prims.bool)
             FStar_Pervasives_Native.tuple2 -> 'a cont_t)
          -> 'a cont_t -> 'a cont_t
  =
  fun env ->
    fun id1 ->
      fun k_global_def ->
        fun k_not_found ->
          let find_in_monad =
            match env.curmonad with
            | FStar_Pervasives_Native.Some uu____3446 ->
                let lid = qualify env id1 in
                let uu____3448 =
                  FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str in
                (match uu____3448 with
                 | FStar_Pervasives_Native.Some r ->
                     let uu____3472 = k_global_def lid r in
                     FStar_Pervasives_Native.Some uu____3472
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None)
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None in
          match find_in_monad with
          | FStar_Pervasives_Native.Some v1 -> v1
          | FStar_Pervasives_Native.None ->
              let lid =
                let uu____3495 = current_module env in qual uu____3495 id1 in
              find_in_module env lid k_global_def k_not_found
let (lid_is_curmod : env -> FStar_Ident.lident -> Prims.bool) =
  fun env ->
    fun lid ->
      match env.curmodule with
      | FStar_Pervasives_Native.None -> false
      | FStar_Pervasives_Native.Some m -> FStar_Ident.lid_equals lid m
let (module_is_defined : env -> FStar_Ident.lident -> Prims.bool) =
  fun env ->
    fun lid ->
      (lid_is_curmod env lid) ||
        (FStar_List.existsb
           (fun x ->
              FStar_Ident.lid_equals lid (FStar_Pervasives_Native.fst x))
           env.modules)
let (resolve_module_name :
  env ->
    FStar_Ident.lident ->
      Prims.bool -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env ->
    fun lid ->
      fun honor_ns ->
        let nslen = FStar_List.length lid.FStar_Ident.ns in
        let rec aux uu___92_3542 =
          match uu___92_3542 with
          | [] ->
              if module_is_defined env lid
              then FStar_Pervasives_Native.Some lid
              else FStar_Pervasives_Native.None
          | (Open_module_or_namespace (ns, Open_namespace))::q when honor_ns
              ->
              let new_lid =
                let uu____3555 =
                  let uu____3558 = FStar_Ident.path_of_lid ns in
                  let uu____3561 = FStar_Ident.path_of_lid lid in
                  FStar_List.append uu____3558 uu____3561 in
                FStar_Ident.lid_of_path uu____3555
                  (FStar_Ident.range_of_lid lid) in
              if module_is_defined env new_lid
              then FStar_Pervasives_Native.Some new_lid
              else aux q
          | (Module_abbrev (name, modul))::uu____3569 when
              (nslen = (Prims.parse_int "0")) &&
                (name.FStar_Ident.idText =
                   (lid.FStar_Ident.ident).FStar_Ident.idText)
              -> FStar_Pervasives_Native.Some modul
          | uu____3576::q -> aux q in
        aux env.scope_mods
let (fail_if_curmodule :
  env -> FStar_Ident.lident -> FStar_Ident.lident -> Prims.unit) =
  fun env ->
    fun ns_original ->
      fun ns_resolved ->
        let uu____3589 =
          let uu____3590 = current_module env in
          FStar_Ident.lid_equals ns_resolved uu____3590 in
        if uu____3589
        then
          (if FStar_Ident.lid_equals ns_resolved FStar_Parser_Const.prims_lid
           then ()
           else
             (let uu____3592 =
                let uu____3597 =
                  FStar_Util.format1
                    "Reference %s to current module is forbidden (see GitHub issue #451)"
                    ns_original.FStar_Ident.str in
                (FStar_Errors.Fatal_ForbiddenReferenceToCurrentModule,
                  uu____3597) in
              FStar_Errors.raise_error uu____3592
                (FStar_Ident.range_of_lid ns_original)))
        else ()
let (fail_if_qualified_by_curmodule :
  env -> FStar_Ident.lident -> Prims.unit) =
  fun env ->
    fun lid ->
      match lid.FStar_Ident.ns with
      | [] -> ()
      | uu____3605 ->
          let modul_orig = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          let uu____3609 = resolve_module_name env modul_orig true in
          (match uu____3609 with
           | FStar_Pervasives_Native.Some modul_res ->
               fail_if_curmodule env modul_orig modul_res
           | uu____3613 -> ())
let (is_open : env -> FStar_Ident.lident -> open_kind -> Prims.bool) =
  fun env ->
    fun lid ->
      fun open_kind ->
        FStar_List.existsb
          (fun uu___93_3628 ->
             match uu___93_3628 with
             | Open_module_or_namespace (ns, k) ->
                 (k = open_kind) && (FStar_Ident.lid_equals lid ns)
             | uu____3631 -> false) env.scope_mods
let (namespace_is_open : env -> FStar_Ident.lident -> Prims.bool) =
  fun env -> fun lid -> is_open env lid Open_namespace
let (module_is_open : env -> FStar_Ident.lident -> Prims.bool) =
  fun env ->
    fun lid -> (lid_is_curmod env lid) || (is_open env lid Open_module)
let (shorten_module_path :
  env ->
    FStar_Ident.ident Prims.list ->
      Prims.bool ->
        (FStar_Ident.ident Prims.list, FStar_Ident.ident Prims.list)
          FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun ids ->
      fun is_full_path ->
        let rec aux revns id1 =
          let lid = FStar_Ident.lid_of_ns_and_id (FStar_List.rev revns) id1 in
          if namespace_is_open env lid
          then
            FStar_Pervasives_Native.Some
              ((FStar_List.rev (id1 :: revns)), [])
          else
            (match revns with
             | [] -> FStar_Pervasives_Native.None
             | ns_last_id::rev_ns_prefix ->
                 let uu____3732 = aux rev_ns_prefix ns_last_id in
                 FStar_All.pipe_right uu____3732
                   (FStar_Util.map_option
                      (fun uu____3782 ->
                         match uu____3782 with
                         | (stripped_ids, rev_kept_ids) ->
                             (stripped_ids, (id1 :: rev_kept_ids))))) in
        let do_shorten env1 ids1 =
          match FStar_List.rev ids1 with
          | [] -> ([], [])
          | ns_last_id::ns_rev_prefix ->
              let uu____3848 = aux ns_rev_prefix ns_last_id in
              (match uu____3848 with
               | FStar_Pervasives_Native.None -> ([], ids1)
               | FStar_Pervasives_Native.Some (stripped_ids, rev_kept_ids) ->
                   (stripped_ids, (FStar_List.rev rev_kept_ids))) in
        if is_full_path
        then
          let uu____3909 =
            let uu____3912 = FStar_Ident.lid_of_ids ids in
            resolve_module_name env uu____3912 true in
          match uu____3909 with
          | FStar_Pervasives_Native.Some m when module_is_open env m ->
              (ids, [])
          | uu____3926 -> do_shorten env ids
        else do_shorten env ids
let resolve_in_open_namespaces'' :
  'a .
    env ->
      FStar_Ident.lident ->
        exported_id_kind ->
          (local_binding -> 'a cont_t) ->
            (rec_binding -> 'a cont_t) ->
              (record_or_dc -> 'a cont_t) ->
                (FStar_Ident.lident -> 'a cont_t) ->
                  ('a cont_t -> FStar_Ident.ident -> 'a cont_t) ->
                    'a FStar_Pervasives_Native.option
  =
  fun env ->
    fun lid ->
      fun eikind ->
        fun k_local_binding ->
          fun k_rec_binding ->
            fun k_record ->
              fun f_module ->
                fun l_default ->
                  match lid.FStar_Ident.ns with
                  | uu____4028::uu____4029 ->
                      let uu____4032 =
                        let uu____4035 =
                          let uu____4036 =
                            FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
                          FStar_Ident.set_lid_range uu____4036
                            (FStar_Ident.range_of_lid lid) in
                        resolve_module_name env uu____4035 true in
                      (match uu____4032 with
                       | FStar_Pervasives_Native.None ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some modul ->
                           let uu____4040 =
                             find_in_module_with_includes eikind f_module
                               Cont_fail env modul lid.FStar_Ident.ident in
                           option_of_cont
                             (fun uu____4044 -> FStar_Pervasives_Native.None)
                             uu____4040)
                  | [] ->
                      try_lookup_id'' env lid.FStar_Ident.ident eikind
                        k_local_binding k_rec_binding k_record f_module
                        l_default
let cont_of_option :
  'a . 'a cont_t -> 'a FStar_Pervasives_Native.option -> 'a cont_t =
  fun k_none ->
    fun uu___94_4062 ->
      match uu___94_4062 with
      | FStar_Pervasives_Native.Some v1 -> Cont_ok v1
      | FStar_Pervasives_Native.None -> k_none
let resolve_in_open_namespaces' :
  'a .
    env ->
      FStar_Ident.lident ->
        (local_binding -> 'a FStar_Pervasives_Native.option) ->
          (rec_binding -> 'a FStar_Pervasives_Native.option) ->
            (FStar_Ident.lident ->
               (FStar_Syntax_Syntax.sigelt, Prims.bool)
                 FStar_Pervasives_Native.tuple2 ->
                 'a FStar_Pervasives_Native.option)
              -> 'a FStar_Pervasives_Native.option
  =
  fun env ->
    fun lid ->
      fun k_local_binding ->
        fun k_rec_binding ->
          fun k_global_def ->
            let k_global_def' k lid1 def =
              let uu____4161 = k_global_def lid1 def in
              cont_of_option k uu____4161 in
            let f_module lid' =
              let k = Cont_ignore in
              find_in_module env lid' (k_global_def' k) k in
            let l_default k i = lookup_default_id env i (k_global_def' k) k in
            resolve_in_open_namespaces'' env lid Exported_id_term_type
              (fun l ->
                 let uu____4191 = k_local_binding l in
                 cont_of_option Cont_fail uu____4191)
              (fun r ->
                 let uu____4197 = k_rec_binding r in
                 cont_of_option Cont_fail uu____4197)
              (fun uu____4201 -> Cont_ignore) f_module l_default
let (fv_qual_of_se :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option)
  =
  fun se ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____4209, uu____4210, uu____4211, l, uu____4213, uu____4214) ->
        let qopt =
          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
            (fun uu___95_4225 ->
               match uu___95_4225 with
               | FStar_Syntax_Syntax.RecordConstructor (uu____4228, fs) ->
                   FStar_Pervasives_Native.Some
                     (FStar_Syntax_Syntax.Record_ctor (l, fs))
               | uu____4240 -> FStar_Pervasives_Native.None) in
        (match qopt with
         | FStar_Pervasives_Native.None ->
             FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor
         | x -> x)
    | FStar_Syntax_Syntax.Sig_declare_typ
        (uu____4246, uu____4247, uu____4248) -> FStar_Pervasives_Native.None
    | uu____4249 -> FStar_Pervasives_Native.None
let (lb_fv :
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Ident.lident -> FStar_Syntax_Syntax.fv)
  =
  fun lbs ->
    fun lid ->
      let uu____4260 =
        FStar_Util.find_map lbs
          (fun lb ->
             let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
             let uu____4268 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
             if uu____4268
             then FStar_Pervasives_Native.Some fv
             else FStar_Pervasives_Native.None) in
      FStar_All.pipe_right uu____4260 FStar_Util.must
let (ns_of_lid_equals :
  FStar_Ident.lident -> FStar_Ident.lident -> Prims.bool) =
  fun lid ->
    fun ns ->
      ((FStar_List.length lid.FStar_Ident.ns) =
         (FStar_List.length (FStar_Ident.ids_of_lid ns)))
        &&
        (let uu____4281 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
         FStar_Ident.lid_equals uu____4281 ns)
let (try_lookup_name :
  Prims.bool ->
    Prims.bool ->
      env -> FStar_Ident.lident -> foundname FStar_Pervasives_Native.option)
  =
  fun any_val ->
    fun exclude_interf ->
      fun env ->
        fun lid ->
          let occurrence_range = FStar_Ident.range_of_lid lid in
          let k_global_def source_lid uu___100_4311 =
            match uu___100_4311 with
            | (uu____4318, true) when exclude_interf ->
                FStar_Pervasives_Native.None
            | (se, uu____4320) ->
                (match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_inductive_typ uu____4323 ->
                     let uu____4340 =
                       let uu____4341 =
                         let uu____4350 =
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.Delta_constant
                             FStar_Pervasives_Native.None in
                         (uu____4350, false,
                           (se.FStar_Syntax_Syntax.sigattrs)) in
                       Term_name uu____4341 in
                     FStar_Pervasives_Native.Some uu____4340
                 | FStar_Syntax_Syntax.Sig_datacon uu____4353 ->
                     let uu____4368 =
                       let uu____4369 =
                         let uu____4378 =
                           let uu____4379 = fv_qual_of_se se in
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.Delta_constant uu____4379 in
                         (uu____4378, false,
                           (se.FStar_Syntax_Syntax.sigattrs)) in
                       Term_name uu____4369 in
                     FStar_Pervasives_Native.Some uu____4368
                 | FStar_Syntax_Syntax.Sig_let
                     ((uu____4384, lbs), uu____4386) ->
                     let fv = lb_fv lbs source_lid in
                     let uu____4402 =
                       let uu____4403 =
                         let uu____4412 =
                           FStar_Syntax_Syntax.fvar source_lid
                             fv.FStar_Syntax_Syntax.fv_delta
                             fv.FStar_Syntax_Syntax.fv_qual in
                         (uu____4412, false,
                           (se.FStar_Syntax_Syntax.sigattrs)) in
                       Term_name uu____4403 in
                     FStar_Pervasives_Native.Some uu____4402
                 | FStar_Syntax_Syntax.Sig_declare_typ
                     (lid1, uu____4416, uu____4417) ->
                     let quals = se.FStar_Syntax_Syntax.sigquals in
                     let uu____4421 =
                       any_val ||
                         (FStar_All.pipe_right quals
                            (FStar_Util.for_some
                               (fun uu___96_4425 ->
                                  match uu___96_4425 with
                                  | FStar_Syntax_Syntax.Assumption -> true
                                  | uu____4426 -> false))) in
                     if uu____4421
                     then
                       let lid2 =
                         FStar_Ident.set_lid_range lid1
                           (FStar_Ident.range_of_lid source_lid) in
                       let dd =
                         let uu____4431 =
                           (FStar_Syntax_Util.is_primop_lid lid2) ||
                             (FStar_All.pipe_right quals
                                (FStar_Util.for_some
                                   (fun uu___97_4436 ->
                                      match uu___97_4436 with
                                      | FStar_Syntax_Syntax.Projector
                                          uu____4437 -> true
                                      | FStar_Syntax_Syntax.Discriminator
                                          uu____4442 -> true
                                      | uu____4443 -> false))) in
                         if uu____4431
                         then FStar_Syntax_Syntax.Delta_equational
                         else FStar_Syntax_Syntax.Delta_constant in
                       let dd1 =
                         let uu____4446 =
                           FStar_All.pipe_right quals
                             (FStar_Util.for_some
                                (fun uu___98_4450 ->
                                   match uu___98_4450 with
                                   | FStar_Syntax_Syntax.Abstract -> true
                                   | uu____4451 -> false)) in
                         if uu____4446
                         then FStar_Syntax_Syntax.Delta_abstract dd
                         else dd in
                       let uu____4453 =
                         FStar_Util.find_map quals
                           (fun uu___99_4458 ->
                              match uu___99_4458 with
                              | FStar_Syntax_Syntax.Reflectable refl_monad ->
                                  FStar_Pervasives_Native.Some refl_monad
                              | uu____4462 -> FStar_Pervasives_Native.None) in
                       (match uu____4453 with
                        | FStar_Pervasives_Native.Some refl_monad ->
                            let refl_const =
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_constant
                                   (FStar_Const.Const_reflect refl_monad))
                                FStar_Pervasives_Native.None occurrence_range in
                            FStar_Pervasives_Native.Some
                              (Term_name
                                 (refl_const, false,
                                   (se.FStar_Syntax_Syntax.sigattrs)))
                        | uu____4473 ->
                            let uu____4476 =
                              let uu____4477 =
                                let uu____4486 =
                                  let uu____4487 = fv_qual_of_se se in
                                  FStar_Syntax_Syntax.fvar lid2 dd1
                                    uu____4487 in
                                (uu____4486, false,
                                  (se.FStar_Syntax_Syntax.sigattrs)) in
                              Term_name uu____4477 in
                            FStar_Pervasives_Native.Some uu____4476)
                     else FStar_Pervasives_Native.None
                 | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
                     FStar_Pervasives_Native.Some
                       (Eff_name
                          (se,
                            (FStar_Ident.set_lid_range
                               ne.FStar_Syntax_Syntax.mname
                               (FStar_Ident.range_of_lid source_lid))))
                 | FStar_Syntax_Syntax.Sig_new_effect ne ->
                     FStar_Pervasives_Native.Some
                       (Eff_name
                          (se,
                            (FStar_Ident.set_lid_range
                               ne.FStar_Syntax_Syntax.mname
                               (FStar_Ident.range_of_lid source_lid))))
                 | FStar_Syntax_Syntax.Sig_effect_abbrev uu____4495 ->
                     FStar_Pervasives_Native.Some (Eff_name (se, source_lid))
                 | uu____4508 -> FStar_Pervasives_Native.None) in
          let k_local_binding r =
            let uu____4527 =
              found_local_binding (FStar_Ident.range_of_lid lid) r in
            match uu____4527 with
            | (t, mut) ->
                FStar_Pervasives_Native.Some (Term_name (t, mut, [])) in
          let k_rec_binding uu____4549 =
            match uu____4549 with
            | (id1, l, dd) ->
                let uu____4561 =
                  let uu____4562 =
                    let uu____4571 =
                      FStar_Syntax_Syntax.fvar
                        (FStar_Ident.set_lid_range l
                           (FStar_Ident.range_of_lid lid)) dd
                        FStar_Pervasives_Native.None in
                    (uu____4571, false, []) in
                  Term_name uu____4562 in
                FStar_Pervasives_Native.Some uu____4561 in
          let found_unmangled =
            match lid.FStar_Ident.ns with
            | [] ->
                let uu____4579 = unmangleOpName lid.FStar_Ident.ident in
                (match uu____4579 with
                 | FStar_Pervasives_Native.Some (t, mut) ->
                     FStar_Pervasives_Native.Some (Term_name (t, mut, []))
                 | uu____4596 -> FStar_Pervasives_Native.None)
            | uu____4603 -> FStar_Pervasives_Native.None in
          match found_unmangled with
          | FStar_Pervasives_Native.None ->
              resolve_in_open_namespaces' env lid k_local_binding
                k_rec_binding k_global_def
          | x -> x
let (try_lookup_effect_name' :
  Prims.bool ->
    env ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.sigelt, FStar_Ident.lident)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun exclude_interf ->
    fun env ->
      fun lid ->
        let uu____4632 = try_lookup_name true exclude_interf env lid in
        match uu____4632 with
        | FStar_Pervasives_Native.Some (Eff_name (o, l)) ->
            FStar_Pervasives_Native.Some (o, l)
        | uu____4647 -> FStar_Pervasives_Native.None
let (try_lookup_effect_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env ->
    fun l ->
      let uu____4662 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____4662 with
      | FStar_Pervasives_Native.Some (o, l1) ->
          FStar_Pervasives_Native.Some l1
      | uu____4677 -> FStar_Pervasives_Native.None
let (try_lookup_effect_name_and_attributes :
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident, FStar_Syntax_Syntax.cflags Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env ->
    fun l ->
      let uu____4698 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____4698 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____4714;
             FStar_Syntax_Syntax.sigquals = uu____4715;
             FStar_Syntax_Syntax.sigmeta = uu____4716;
             FStar_Syntax_Syntax.sigattrs = uu____4717;_},
           l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____4736;
             FStar_Syntax_Syntax.sigquals = uu____4737;
             FStar_Syntax_Syntax.sigmeta = uu____4738;
             FStar_Syntax_Syntax.sigattrs = uu____4739;_},
           l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (uu____4757, uu____4758, uu____4759, uu____4760, cattributes);
             FStar_Syntax_Syntax.sigrng = uu____4762;
             FStar_Syntax_Syntax.sigquals = uu____4763;
             FStar_Syntax_Syntax.sigmeta = uu____4764;
             FStar_Syntax_Syntax.sigattrs = uu____4765;_},
           l1)
          -> FStar_Pervasives_Native.Some (l1, cattributes)
      | uu____4787 -> FStar_Pervasives_Native.None
let (try_lookup_effect_defn :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.eff_decl FStar_Pervasives_Native.option)
  =
  fun env ->
    fun l ->
      let uu____4808 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____4808 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____4818;
             FStar_Syntax_Syntax.sigquals = uu____4819;
             FStar_Syntax_Syntax.sigmeta = uu____4820;
             FStar_Syntax_Syntax.sigattrs = uu____4821;_},
           uu____4822)
          -> FStar_Pervasives_Native.Some ne
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____4832;
             FStar_Syntax_Syntax.sigquals = uu____4833;
             FStar_Syntax_Syntax.sigmeta = uu____4834;
             FStar_Syntax_Syntax.sigattrs = uu____4835;_},
           uu____4836)
          -> FStar_Pervasives_Native.Some ne
      | uu____4845 -> FStar_Pervasives_Native.None
let (is_effect_name : env -> FStar_Ident.lident -> Prims.bool) =
  fun env ->
    fun lid ->
      let uu____4858 = try_lookup_effect_name env lid in
      match uu____4858 with
      | FStar_Pervasives_Native.None -> false
      | FStar_Pervasives_Native.Some uu____4861 -> true
let (try_lookup_root_effect_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env ->
    fun l ->
      let uu____4870 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____4870 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (l', uu____4880, uu____4881, uu____4882, uu____4883);
             FStar_Syntax_Syntax.sigrng = uu____4884;
             FStar_Syntax_Syntax.sigquals = uu____4885;
             FStar_Syntax_Syntax.sigmeta = uu____4886;
             FStar_Syntax_Syntax.sigattrs = uu____4887;_},
           uu____4888)
          ->
          let rec aux new_name =
            let uu____4907 =
              FStar_Util.smap_try_find (sigmap env) new_name.FStar_Ident.str in
            match uu____4907 with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (s, uu____4925) ->
                (match s.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
                     FStar_Pervasives_Native.Some
                       (FStar_Ident.set_lid_range
                          ne.FStar_Syntax_Syntax.mname
                          (FStar_Ident.range_of_lid l))
                 | FStar_Syntax_Syntax.Sig_new_effect ne ->
                     FStar_Pervasives_Native.Some
                       (FStar_Ident.set_lid_range
                          ne.FStar_Syntax_Syntax.mname
                          (FStar_Ident.range_of_lid l))
                 | FStar_Syntax_Syntax.Sig_effect_abbrev
                     (uu____4934, uu____4935, uu____4936, cmp, uu____4938) ->
                     let l'' = FStar_Syntax_Util.comp_effect_name cmp in
                     aux l''
                 | uu____4944 -> FStar_Pervasives_Native.None) in
          aux l'
      | FStar_Pervasives_Native.Some (uu____4945, l') ->
          FStar_Pervasives_Native.Some l'
      | uu____4951 -> FStar_Pervasives_Native.None
let (lookup_letbinding_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env ->
    fun lid ->
      let k_global_def lid1 uu___101_4980 =
        match uu___101_4980 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____4989, uu____4990, uu____4991);
             FStar_Syntax_Syntax.sigrng = uu____4992;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____4994;
             FStar_Syntax_Syntax.sigattrs = uu____4995;_},
           uu____4996) -> FStar_Pervasives_Native.Some quals
        | uu____5003 -> FStar_Pervasives_Native.None in
      let uu____5010 =
        resolve_in_open_namespaces' env lid
          (fun uu____5018 -> FStar_Pervasives_Native.None)
          (fun uu____5022 -> FStar_Pervasives_Native.None) k_global_def in
      match uu____5010 with
      | FStar_Pervasives_Native.Some quals -> quals
      | uu____5032 -> []
let (try_lookup_module :
  env ->
    Prims.string Prims.list ->
      FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option)
  =
  fun env ->
    fun path ->
      let uu____5049 =
        FStar_List.tryFind
          (fun uu____5064 ->
             match uu____5064 with
             | (mlid, modul) ->
                 let uu____5071 = FStar_Ident.path_of_lid mlid in
                 uu____5071 = path) env.modules in
      match uu____5049 with
      | FStar_Pervasives_Native.Some (uu____5078, modul) ->
          FStar_Pervasives_Native.Some modul
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let (try_lookup_let :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env ->
    fun lid ->
      let k_global_def lid1 uu___102_5108 =
        match uu___102_5108 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               ((uu____5115, lbs), uu____5117);
             FStar_Syntax_Syntax.sigrng = uu____5118;
             FStar_Syntax_Syntax.sigquals = uu____5119;
             FStar_Syntax_Syntax.sigmeta = uu____5120;
             FStar_Syntax_Syntax.sigattrs = uu____5121;_},
           uu____5122) ->
            let fv = lb_fv lbs lid1 in
            let uu____5142 =
              FStar_Syntax_Syntax.fvar lid1 fv.FStar_Syntax_Syntax.fv_delta
                fv.FStar_Syntax_Syntax.fv_qual in
            FStar_Pervasives_Native.Some uu____5142
        | uu____5143 -> FStar_Pervasives_Native.None in
      resolve_in_open_namespaces' env lid
        (fun uu____5149 -> FStar_Pervasives_Native.None)
        (fun uu____5151 -> FStar_Pervasives_Native.None) k_global_def
let (try_lookup_definition :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env ->
    fun lid ->
      let k_global_def lid1 uu___103_5174 =
        match uu___103_5174 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               (lbs, uu____5184);
             FStar_Syntax_Syntax.sigrng = uu____5185;
             FStar_Syntax_Syntax.sigquals = uu____5186;
             FStar_Syntax_Syntax.sigmeta = uu____5187;
             FStar_Syntax_Syntax.sigattrs = uu____5188;_},
           uu____5189) ->
            FStar_Util.find_map (FStar_Pervasives_Native.snd lbs)
              (fun lb ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inr fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv lid1 ->
                     FStar_Pervasives_Native.Some
                       (lb.FStar_Syntax_Syntax.lbdef)
                 | uu____5212 -> FStar_Pervasives_Native.None)
        | uu____5219 -> FStar_Pervasives_Native.None in
      resolve_in_open_namespaces' env lid
        (fun uu____5229 -> FStar_Pervasives_Native.None)
        (fun uu____5233 -> FStar_Pervasives_Native.None) k_global_def
let (empty_include_smap :
  FStar_Ident.lident Prims.list FStar_ST.ref FStar_Util.smap) = new_sigmap ()
let (empty_exported_id_smap : exported_id_set FStar_Util.smap) =
  new_sigmap ()
let (try_lookup_lid' :
  Prims.bool ->
    Prims.bool ->
      env ->
        FStar_Ident.lident ->
          (FStar_Syntax_Syntax.term, Prims.bool,
            FStar_Syntax_Syntax.attribute Prims.list)
            FStar_Pervasives_Native.tuple3 FStar_Pervasives_Native.option)
  =
  fun any_val ->
    fun exclude_interface ->
      fun env ->
        fun lid ->
          let uu____5280 = try_lookup_name any_val exclude_interface env lid in
          match uu____5280 with
          | FStar_Pervasives_Native.Some (Term_name (e, mut, attrs)) ->
              FStar_Pervasives_Native.Some (e, mut, attrs)
          | uu____5310 -> FStar_Pervasives_Native.None
let (drop_attributes :
  (FStar_Syntax_Syntax.term, Prims.bool,
    FStar_Syntax_Syntax.attribute Prims.list) FStar_Pervasives_Native.tuple3
    FStar_Pervasives_Native.option ->
    (FStar_Syntax_Syntax.term, Prims.bool) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option)
  =
  fun x ->
    match x with
    | FStar_Pervasives_Native.Some (t, mut, uu____5364) ->
        FStar_Pervasives_Native.Some (t, mut)
    | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let (try_lookup_lid_with_attributes :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term, Prims.bool,
        FStar_Syntax_Syntax.attribute Prims.list)
        FStar_Pervasives_Native.tuple3 FStar_Pervasives_Native.option)
  = fun env -> fun l -> try_lookup_lid' env.iface false env l
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term, Prims.bool) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option)
  =
  fun env ->
    fun l ->
      let uu____5431 = try_lookup_lid_with_attributes env l in
      FStar_All.pipe_right uu____5431 drop_attributes
let (resolve_to_fully_qualified_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env ->
    fun l ->
      let uu____5466 = try_lookup_lid env l in
      match uu____5466 with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (e, uu____5480) ->
          let uu____5485 =
            let uu____5486 = FStar_Syntax_Subst.compress e in
            uu____5486.FStar_Syntax_Syntax.n in
          (match uu____5485 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               FStar_Pervasives_Native.Some
                 ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
           | uu____5492 -> FStar_Pervasives_Native.None)
let (shorten_lid' : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env ->
    fun lid ->
      let uu____5499 = shorten_module_path env lid.FStar_Ident.ns true in
      match uu____5499 with
      | (uu____5508, short) ->
          FStar_Ident.lid_of_ns_and_id short lid.FStar_Ident.ident
let (shorten_lid : env -> FStar_Ident.lid -> FStar_Ident.lid) =
  fun env ->
    fun lid ->
      match env.curmodule with
      | FStar_Pervasives_Native.None -> shorten_lid' env lid
      | uu____5524 ->
          let lid_without_ns =
            FStar_Ident.lid_of_ns_and_id [] lid.FStar_Ident.ident in
          let uu____5528 = resolve_to_fully_qualified_name env lid_without_ns in
          (match uu____5528 with
           | FStar_Pervasives_Native.Some lid' when
               lid'.FStar_Ident.str = lid.FStar_Ident.str -> lid_without_ns
           | uu____5532 -> shorten_lid' env lid)
let (try_lookup_lid_with_attributes_no_resolve :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term, Prims.bool,
        FStar_Syntax_Syntax.attribute Prims.list)
        FStar_Pervasives_Native.tuple3 FStar_Pervasives_Native.option)
  =
  fun env ->
    fun l ->
      let env' =
        let uu___124_5562 = env in
        {
          curmodule = (uu___124_5562.curmodule);
          curmonad = (uu___124_5562.curmonad);
          modules = (uu___124_5562.modules);
          scope_mods = [];
          exported_ids = empty_exported_id_smap;
          trans_exported_ids = (uu___124_5562.trans_exported_ids);
          includes = empty_include_smap;
          sigaccum = (uu___124_5562.sigaccum);
          sigmap = (uu___124_5562.sigmap);
          iface = (uu___124_5562.iface);
          admitted_iface = (uu___124_5562.admitted_iface);
          expect_typ = (uu___124_5562.expect_typ);
          docs = (uu___124_5562.docs);
          remaining_iface_decls = (uu___124_5562.remaining_iface_decls);
          syntax_only = (uu___124_5562.syntax_only);
          ds_hooks = (uu___124_5562.ds_hooks)
        } in
      try_lookup_lid_with_attributes env' l
let (try_lookup_lid_no_resolve :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term, Prims.bool) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option)
  =
  fun env ->
    fun l ->
      let uu____5581 = try_lookup_lid_with_attributes_no_resolve env l in
      FStar_All.pipe_right uu____5581 drop_attributes
let (try_lookup_doc :
  env ->
    FStar_Ident.lid -> FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option)
  = fun env -> fun l -> FStar_Util.smap_try_find env.docs l.FStar_Ident.str
let (try_lookup_datacon :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.fv FStar_Pervasives_Native.option)
  =
  fun env ->
    fun lid ->
      let k_global_def lid1 uu___105_5636 =
        match uu___105_5636 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____5643, uu____5644, uu____5645);
             FStar_Syntax_Syntax.sigrng = uu____5646;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____5648;
             FStar_Syntax_Syntax.sigattrs = uu____5649;_},
           uu____5650) ->
            let uu____5655 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___104_5659 ->
                      match uu___104_5659 with
                      | FStar_Syntax_Syntax.Assumption -> true
                      | uu____5660 -> false)) in
            if uu____5655
            then
              let uu____5663 =
                FStar_Syntax_Syntax.lid_as_fv lid1
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None in
              FStar_Pervasives_Native.Some uu____5663
            else FStar_Pervasives_Native.None
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
               uu____5665;
             FStar_Syntax_Syntax.sigrng = uu____5666;
             FStar_Syntax_Syntax.sigquals = uu____5667;
             FStar_Syntax_Syntax.sigmeta = uu____5668;
             FStar_Syntax_Syntax.sigattrs = uu____5669;_},
           uu____5670) ->
            let uu____5689 =
              FStar_Syntax_Syntax.lid_as_fv lid1
                FStar_Syntax_Syntax.Delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor) in
            FStar_Pervasives_Native.Some uu____5689
        | uu____5690 -> FStar_Pervasives_Native.None in
      resolve_in_open_namespaces' env lid
        (fun uu____5696 -> FStar_Pervasives_Native.None)
        (fun uu____5698 -> FStar_Pervasives_Native.None) k_global_def
let (find_all_datacons :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident Prims.list FStar_Pervasives_Native.option)
  =
  fun env ->
    fun lid ->
      let k_global_def lid1 uu___106_5723 =
        match uu___106_5723 with
        | ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_inductive_typ
               (uu____5732, uu____5733, uu____5734, uu____5735, datas,
                uu____5737);
             FStar_Syntax_Syntax.sigrng = uu____5738;
             FStar_Syntax_Syntax.sigquals = uu____5739;
             FStar_Syntax_Syntax.sigmeta = uu____5740;
             FStar_Syntax_Syntax.sigattrs = uu____5741;_},
           uu____5742) -> FStar_Pervasives_Native.Some datas
        | uu____5757 -> FStar_Pervasives_Native.None in
      resolve_in_open_namespaces' env lid
        (fun uu____5767 -> FStar_Pervasives_Native.None)
        (fun uu____5771 -> FStar_Pervasives_Native.None) k_global_def
let (record_cache_aux_with_filter :
  ((Prims.unit -> Prims.unit, Prims.unit -> Prims.unit,
     Prims.unit -> record_or_dc Prims.list, record_or_dc -> Prims.unit)
     FStar_Pervasives_Native.tuple4,
    Prims.unit -> Prims.unit) FStar_Pervasives_Native.tuple2)
  =
  let record_cache = FStar_Util.mk_ref [[]] in
  let push1 uu____5816 =
    let uu____5817 =
      let uu____5822 =
        let uu____5825 = FStar_ST.op_Bang record_cache in
        FStar_List.hd uu____5825 in
      let uu____5935 = FStar_ST.op_Bang record_cache in uu____5822 ::
        uu____5935 in
    FStar_ST.op_Colon_Equals record_cache uu____5817 in
  let pop1 uu____6151 =
    let uu____6152 =
      let uu____6157 = FStar_ST.op_Bang record_cache in
      FStar_List.tl uu____6157 in
    FStar_ST.op_Colon_Equals record_cache uu____6152 in
  let peek1 uu____6375 =
    let uu____6376 = FStar_ST.op_Bang record_cache in
    FStar_List.hd uu____6376 in
  let insert r =
    let uu____6490 =
      let uu____6495 = let uu____6498 = peek1 () in r :: uu____6498 in
      let uu____6501 =
        let uu____6506 = FStar_ST.op_Bang record_cache in
        FStar_List.tl uu____6506 in
      uu____6495 :: uu____6501 in
    FStar_ST.op_Colon_Equals record_cache uu____6490 in
  let filter1 uu____6724 =
    let rc = peek1 () in
    let filtered =
      FStar_List.filter (fun r -> Prims.op_Negation r.is_private_or_abstract)
        rc in
    let uu____6733 =
      let uu____6738 =
        let uu____6743 = FStar_ST.op_Bang record_cache in
        FStar_List.tl uu____6743 in
      filtered :: uu____6738 in
    FStar_ST.op_Colon_Equals record_cache uu____6733 in
  let aux = (push1, pop1, peek1, insert) in (aux, filter1)
let (record_cache_aux :
  (Prims.unit -> Prims.unit, Prims.unit -> Prims.unit,
    Prims.unit -> record_or_dc Prims.list, record_or_dc -> Prims.unit)
    FStar_Pervasives_Native.tuple4)
  =
  let uu____7025 = record_cache_aux_with_filter in
  match uu____7025 with | (aux, uu____7069) -> aux
let (filter_record_cache : Prims.unit -> Prims.unit) =
  let uu____7112 = record_cache_aux_with_filter in
  match uu____7112 with | (uu____7139, filter1) -> filter1
let (push_record_cache : Prims.unit -> Prims.unit) =
  let uu____7183 = record_cache_aux in
  match uu____7183 with
  | (push1, uu____7205, uu____7206, uu____7207) -> push1
let (pop_record_cache : Prims.unit -> Prims.unit) =
  let uu____7230 = record_cache_aux in
  match uu____7230 with | (uu____7251, pop1, uu____7253, uu____7254) -> pop1
let (peek_record_cache : Prims.unit -> record_or_dc Prims.list) =
  let uu____7279 = record_cache_aux in
  match uu____7279 with
  | (uu____7302, uu____7303, peek1, uu____7305) -> peek1
let (insert_record_cache : record_or_dc -> Prims.unit) =
  let uu____7328 = record_cache_aux in
  match uu____7328 with
  | (uu____7349, uu____7350, uu____7351, insert) -> insert
let (extract_record :
  env ->
    scope_mod Prims.list FStar_ST.ref ->
      FStar_Syntax_Syntax.sigelt -> Prims.unit)
  =
  fun e ->
    fun new_globs ->
      fun se ->
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_bundle (sigs, uu____7461) ->
            let is_record =
              FStar_Util.for_some
                (fun uu___107_7477 ->
                   match uu___107_7477 with
                   | FStar_Syntax_Syntax.RecordType uu____7478 -> true
                   | FStar_Syntax_Syntax.RecordConstructor uu____7487 -> true
                   | uu____7496 -> false) in
            let find_dc dc =
              FStar_All.pipe_right sigs
                (FStar_Util.find_opt
                   (fun uu___108_7518 ->
                      match uu___108_7518 with
                      | {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_datacon
                            (lid, uu____7520, uu____7521, uu____7522,
                             uu____7523, uu____7524);
                          FStar_Syntax_Syntax.sigrng = uu____7525;
                          FStar_Syntax_Syntax.sigquals = uu____7526;
                          FStar_Syntax_Syntax.sigmeta = uu____7527;
                          FStar_Syntax_Syntax.sigattrs = uu____7528;_} ->
                          FStar_Ident.lid_equals dc lid
                      | uu____7537 -> false)) in
            FStar_All.pipe_right sigs
              (FStar_List.iter
                 (fun uu___109_7572 ->
                    match uu___109_7572 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ
                          (typename, univs1, parms, uu____7576, uu____7577,
                           dc::[]);
                        FStar_Syntax_Syntax.sigrng = uu____7579;
                        FStar_Syntax_Syntax.sigquals = typename_quals;
                        FStar_Syntax_Syntax.sigmeta = uu____7581;
                        FStar_Syntax_Syntax.sigattrs = uu____7582;_} ->
                        let uu____7593 =
                          let uu____7594 = find_dc dc in
                          FStar_All.pipe_left FStar_Util.must uu____7594 in
                        (match uu____7593 with
                         | {
                             FStar_Syntax_Syntax.sigel =
                               FStar_Syntax_Syntax.Sig_datacon
                               (constrname, uu____7600, t, uu____7602,
                                uu____7603, uu____7604);
                             FStar_Syntax_Syntax.sigrng = uu____7605;
                             FStar_Syntax_Syntax.sigquals = uu____7606;
                             FStar_Syntax_Syntax.sigmeta = uu____7607;
                             FStar_Syntax_Syntax.sigattrs = uu____7608;_} ->
                             let uu____7617 =
                               FStar_Syntax_Util.arrow_formals t in
                             (match uu____7617 with
                              | (formals, uu____7631) ->
                                  let is_rec = is_record typename_quals in
                                  let formals' =
                                    FStar_All.pipe_right formals
                                      (FStar_List.collect
                                         (fun uu____7680 ->
                                            match uu____7680 with
                                            | (x, q) ->
                                                let uu____7693 =
                                                  (FStar_Syntax_Syntax.is_null_bv
                                                     x)
                                                    ||
                                                    (is_rec &&
                                                       (FStar_Syntax_Syntax.is_implicit
                                                          q)) in
                                                if uu____7693
                                                then []
                                                else [(x, q)])) in
                                  let fields' =
                                    FStar_All.pipe_right formals'
                                      (FStar_List.map
                                         (fun uu____7750 ->
                                            match uu____7750 with
                                            | (x, q) ->
                                                let uu____7763 =
                                                  if is_rec
                                                  then
                                                    FStar_Syntax_Util.unmangle_field_name
                                                      x.FStar_Syntax_Syntax.ppname
                                                  else
                                                    x.FStar_Syntax_Syntax.ppname in
                                                (uu____7763,
                                                  (x.FStar_Syntax_Syntax.sort)))) in
                                  let fields = fields' in
                                  let record =
                                    {
                                      typename;
                                      constrname =
                                        (constrname.FStar_Ident.ident);
                                      parms;
                                      fields;
                                      is_private_or_abstract =
                                        ((FStar_List.contains
                                            FStar_Syntax_Syntax.Private
                                            typename_quals)
                                           ||
                                           (FStar_List.contains
                                              FStar_Syntax_Syntax.Abstract
                                              typename_quals));
                                      is_record = is_rec
                                    } in
                                  ((let uu____7778 =
                                      let uu____7781 =
                                        FStar_ST.op_Bang new_globs in
                                      (Record_or_dc record) :: uu____7781 in
                                    FStar_ST.op_Colon_Equals new_globs
                                      uu____7778);
                                   (match () with
                                    | () ->
                                        ((let add_field uu____7992 =
                                            match uu____7992 with
                                            | (id1, uu____8000) ->
                                                let modul =
                                                  let uu____8006 =
                                                    FStar_Ident.lid_of_ids
                                                      constrname.FStar_Ident.ns in
                                                  uu____8006.FStar_Ident.str in
                                                let uu____8007 =
                                                  get_exported_id_set e modul in
                                                (match uu____8007 with
                                                 | FStar_Pervasives_Native.Some
                                                     my_ex ->
                                                     let my_exported_ids =
                                                       my_ex
                                                         Exported_id_field in
                                                     ((let uu____8062 =
                                                         let uu____8063 =
                                                           FStar_ST.op_Bang
                                                             my_exported_ids in
                                                         FStar_Util.set_add
                                                           id1.FStar_Ident.idText
                                                           uu____8063 in
                                                       FStar_ST.op_Colon_Equals
                                                         my_exported_ids
                                                         uu____8062);
                                                      (match () with
                                                       | () ->
                                                           let projname =
                                                             let uu____8257 =
                                                               let uu____8258
                                                                 =
                                                                 FStar_Syntax_Util.mk_field_projector_name_from_ident
                                                                   constrname
                                                                   id1 in
                                                               uu____8258.FStar_Ident.ident in
                                                             uu____8257.FStar_Ident.idText in
                                                           let uu____8260 =
                                                             let uu____8261 =
                                                               FStar_ST.op_Bang
                                                                 my_exported_ids in
                                                             FStar_Util.set_add
                                                               projname
                                                               uu____8261 in
                                                           FStar_ST.op_Colon_Equals
                                                             my_exported_ids
                                                             uu____8260))
                                                 | FStar_Pervasives_Native.None
                                                     -> ()) in
                                          FStar_List.iter add_field fields');
                                         (match () with
                                          | () -> insert_record_cache record)))))
                         | uu____8464 -> ())
                    | uu____8465 -> ()))
        | uu____8466 -> ()
let (try_lookup_record_or_dc_by_field_name :
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option) =
  fun env ->
    fun fieldname ->
      let find_in_cache fieldname1 =
        let uu____8481 =
          ((fieldname1.FStar_Ident.ns), (fieldname1.FStar_Ident.ident)) in
        match uu____8481 with
        | (ns, id1) ->
            let uu____8498 = peek_record_cache () in
            FStar_Util.find_map uu____8498
              (fun record ->
                 let uu____8504 =
                   find_in_record ns id1 record (fun r -> Cont_ok r) in
                 option_of_cont
                   (fun uu____8510 -> FStar_Pervasives_Native.None)
                   uu____8504) in
      resolve_in_open_namespaces'' env fieldname Exported_id_field
        (fun uu____8512 -> Cont_ignore) (fun uu____8514 -> Cont_ignore)
        (fun r -> Cont_ok r)
        (fun fn ->
           let uu____8520 = find_in_cache fn in
           cont_of_option Cont_ignore uu____8520)
        (fun k -> fun uu____8526 -> k)
let (try_lookup_record_by_field_name :
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option) =
  fun env ->
    fun fieldname ->
      let uu____8537 = try_lookup_record_or_dc_by_field_name env fieldname in
      match uu____8537 with
      | FStar_Pervasives_Native.Some r when r.is_record ->
          FStar_Pervasives_Native.Some r
      | uu____8543 -> FStar_Pervasives_Native.None
let (belongs_to_record :
  env -> FStar_Ident.lident -> record_or_dc -> Prims.bool) =
  fun env ->
    fun lid ->
      fun record ->
        let uu____8555 = try_lookup_record_by_field_name env lid in
        match uu____8555 with
        | FStar_Pervasives_Native.Some record' when
            let uu____8559 =
              let uu____8560 =
                FStar_Ident.path_of_ns (record.typename).FStar_Ident.ns in
              FStar_Ident.text_of_path uu____8560 in
            let uu____8563 =
              let uu____8564 =
                FStar_Ident.path_of_ns (record'.typename).FStar_Ident.ns in
              FStar_Ident.text_of_path uu____8564 in
            uu____8559 = uu____8563 ->
            let uu____8567 =
              find_in_record (record.typename).FStar_Ident.ns
                lid.FStar_Ident.ident record (fun uu____8571 -> Cont_ok ()) in
            (match uu____8567 with
             | Cont_ok uu____8572 -> true
             | uu____8573 -> false)
        | uu____8576 -> false
let (try_lookup_dc_by_field_name :
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident, Prims.bool) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option)
  =
  fun env ->
    fun fieldname ->
      let uu____8591 = try_lookup_record_or_dc_by_field_name env fieldname in
      match uu____8591 with
      | FStar_Pervasives_Native.Some r ->
          let uu____8601 =
            let uu____8606 =
              let uu____8607 =
                FStar_Ident.lid_of_ids
                  (FStar_List.append (r.typename).FStar_Ident.ns
                     [r.constrname]) in
              FStar_Ident.set_lid_range uu____8607
                (FStar_Ident.range_of_lid fieldname) in
            (uu____8606, (r.is_record)) in
          FStar_Pervasives_Native.Some uu____8601
      | uu____8612 -> FStar_Pervasives_Native.None
let (string_set_ref_new :
  Prims.unit -> Prims.string FStar_Util.set FStar_ST.ref) =
  fun uu____8660 ->
    let uu____8661 = FStar_Util.new_set FStar_Util.compare in
    FStar_Util.mk_ref uu____8661
let (exported_id_set_new :
  Prims.unit -> exported_id_kind -> Prims.string FStar_Util.set FStar_ST.ref)
  =
  fun uu____8709 ->
    let term_type_set = string_set_ref_new () in
    let field_set = string_set_ref_new () in
    fun uu___110_8720 ->
      match uu___110_8720 with
      | Exported_id_term_type -> term_type_set
      | Exported_id_field -> field_set
let (unique :
  Prims.bool -> Prims.bool -> env -> FStar_Ident.lident -> Prims.bool) =
  fun any_val ->
    fun exclude_interface ->
      fun env ->
        fun lid ->
          let filter_scope_mods uu___111_8810 =
            match uu___111_8810 with
            | Rec_binding uu____8811 -> true
            | uu____8812 -> false in
          let this_env =
            let uu___125_8814 = env in
            let uu____8815 =
              FStar_List.filter filter_scope_mods env.scope_mods in
            {
              curmodule = (uu___125_8814.curmodule);
              curmonad = (uu___125_8814.curmonad);
              modules = (uu___125_8814.modules);
              scope_mods = uu____8815;
              exported_ids = empty_exported_id_smap;
              trans_exported_ids = (uu___125_8814.trans_exported_ids);
              includes = empty_include_smap;
              sigaccum = (uu___125_8814.sigaccum);
              sigmap = (uu___125_8814.sigmap);
              iface = (uu___125_8814.iface);
              admitted_iface = (uu___125_8814.admitted_iface);
              expect_typ = (uu___125_8814.expect_typ);
              docs = (uu___125_8814.docs);
              remaining_iface_decls = (uu___125_8814.remaining_iface_decls);
              syntax_only = (uu___125_8814.syntax_only);
              ds_hooks = (uu___125_8814.ds_hooks)
            } in
          let uu____8818 =
            try_lookup_lid' any_val exclude_interface this_env lid in
          match uu____8818 with
          | FStar_Pervasives_Native.None -> true
          | FStar_Pervasives_Native.Some uu____8837 -> false
let (push_scope_mod : env -> scope_mod -> env) =
  fun env ->
    fun scope_mod ->
      let uu___126_8860 = env in
      {
        curmodule = (uu___126_8860.curmodule);
        curmonad = (uu___126_8860.curmonad);
        modules = (uu___126_8860.modules);
        scope_mods = (scope_mod :: (env.scope_mods));
        exported_ids = (uu___126_8860.exported_ids);
        trans_exported_ids = (uu___126_8860.trans_exported_ids);
        includes = (uu___126_8860.includes);
        sigaccum = (uu___126_8860.sigaccum);
        sigmap = (uu___126_8860.sigmap);
        iface = (uu___126_8860.iface);
        admitted_iface = (uu___126_8860.admitted_iface);
        expect_typ = (uu___126_8860.expect_typ);
        docs = (uu___126_8860.docs);
        remaining_iface_decls = (uu___126_8860.remaining_iface_decls);
        syntax_only = (uu___126_8860.syntax_only);
        ds_hooks = (uu___126_8860.ds_hooks)
      }
let (push_bv' :
  env ->
    FStar_Ident.ident ->
      Prims.bool ->
        (env, FStar_Syntax_Syntax.bv) FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun x ->
      fun is_mutable ->
        let bv =
          FStar_Syntax_Syntax.gen_bv x.FStar_Ident.idText
            (FStar_Pervasives_Native.Some (x.FStar_Ident.idRange))
            FStar_Syntax_Syntax.tun in
        ((push_scope_mod env (Local_binding (x, bv, is_mutable))), bv)
let (push_bv_mutable :
  env ->
    FStar_Ident.ident ->
      (env, FStar_Syntax_Syntax.bv) FStar_Pervasives_Native.tuple2)
  = fun env -> fun x -> push_bv' env x true
let (push_bv :
  env ->
    FStar_Ident.ident ->
      (env, FStar_Syntax_Syntax.bv) FStar_Pervasives_Native.tuple2)
  = fun env -> fun x -> push_bv' env x false
let (push_top_level_rec_binding :
  env -> FStar_Ident.ident -> FStar_Syntax_Syntax.delta_depth -> env) =
  fun env ->
    fun x ->
      fun dd ->
        let l = qualify env x in
        let uu____8905 =
          (unique false true env l) || (FStar_Options.interactive ()) in
        if uu____8905
        then push_scope_mod env (Rec_binding (x, l, dd))
        else
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_DuplicateTopLevelNames,
              (Prims.strcat "Duplicate top-level names " l.FStar_Ident.str))
            (FStar_Ident.range_of_lid l)
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env ->
    fun s ->
      let err l =
        let sopt = FStar_Util.smap_try_find (sigmap env) l.FStar_Ident.str in
        let r =
          match sopt with
          | FStar_Pervasives_Native.Some (se, uu____8930) ->
              let uu____8935 =
                FStar_Util.find_opt (FStar_Ident.lid_equals l)
                  (FStar_Syntax_Util.lids_of_sigelt se) in
              (match uu____8935 with
               | FStar_Pervasives_Native.Some l1 ->
                   FStar_All.pipe_left FStar_Range.string_of_range
                     (FStar_Ident.range_of_lid l1)
               | FStar_Pervasives_Native.None -> "<unknown>")
          | FStar_Pervasives_Native.None -> "<unknown>" in
        let uu____8943 =
          let uu____8948 =
            FStar_Util.format2
              "Duplicate top-level names [%s]; previously declared at %s"
              (FStar_Ident.text_of_lid l) r in
          (FStar_Errors.Fatal_DuplicateTopLevelNames, uu____8948) in
        FStar_Errors.raise_error uu____8943 (FStar_Ident.range_of_lid l) in
      let globals = FStar_Util.mk_ref env.scope_mods in
      let env1 =
        let uu____8957 =
          match s.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let uu____8966 -> (false, true)
          | FStar_Syntax_Syntax.Sig_bundle uu____8973 -> (false, true)
          | uu____8982 -> (false, false) in
        match uu____8957 with
        | (any_val, exclude_interface) ->
            let lids = FStar_Syntax_Util.lids_of_sigelt s in
            let uu____8988 =
              FStar_Util.find_map lids
                (fun l ->
                   let uu____8994 =
                     let uu____8995 = unique any_val exclude_interface env l in
                     Prims.op_Negation uu____8995 in
                   if uu____8994
                   then FStar_Pervasives_Native.Some l
                   else FStar_Pervasives_Native.None) in
            (match uu____8988 with
             | FStar_Pervasives_Native.Some l -> err l
             | uu____9000 ->
                 (extract_record env globals s;
                  (let uu___127_9074 = env in
                   {
                     curmodule = (uu___127_9074.curmodule);
                     curmonad = (uu___127_9074.curmonad);
                     modules = (uu___127_9074.modules);
                     scope_mods = (uu___127_9074.scope_mods);
                     exported_ids = (uu___127_9074.exported_ids);
                     trans_exported_ids = (uu___127_9074.trans_exported_ids);
                     includes = (uu___127_9074.includes);
                     sigaccum = (s :: (env.sigaccum));
                     sigmap = (uu___127_9074.sigmap);
                     iface = (uu___127_9074.iface);
                     admitted_iface = (uu___127_9074.admitted_iface);
                     expect_typ = (uu___127_9074.expect_typ);
                     docs = (uu___127_9074.docs);
                     remaining_iface_decls =
                       (uu___127_9074.remaining_iface_decls);
                     syntax_only = (uu___127_9074.syntax_only);
                     ds_hooks = (uu___127_9074.ds_hooks)
                   }))) in
      let env2 =
        let uu___128_9076 = env1 in
        let uu____9077 = FStar_ST.op_Bang globals in
        {
          curmodule = (uu___128_9076.curmodule);
          curmonad = (uu___128_9076.curmonad);
          modules = (uu___128_9076.modules);
          scope_mods = uu____9077;
          exported_ids = (uu___128_9076.exported_ids);
          trans_exported_ids = (uu___128_9076.trans_exported_ids);
          includes = (uu___128_9076.includes);
          sigaccum = (uu___128_9076.sigaccum);
          sigmap = (uu___128_9076.sigmap);
          iface = (uu___128_9076.iface);
          admitted_iface = (uu___128_9076.admitted_iface);
          expect_typ = (uu___128_9076.expect_typ);
          docs = (uu___128_9076.docs);
          remaining_iface_decls = (uu___128_9076.remaining_iface_decls);
          syntax_only = (uu___128_9076.syntax_only);
          ds_hooks = (uu___128_9076.ds_hooks)
        } in
      let uu____9179 =
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_bundle (ses, uu____9205) ->
            let uu____9214 =
              FStar_List.map
                (fun se -> ((FStar_Syntax_Util.lids_of_sigelt se), se)) ses in
            (env2, uu____9214)
        | uu____9241 -> (env2, [((FStar_Syntax_Util.lids_of_sigelt s), s)]) in
      match uu____9179 with
      | (env3, lss) ->
          (FStar_All.pipe_right lss
             (FStar_List.iter
                (fun uu____9300 ->
                   match uu____9300 with
                   | (lids, se) ->
                       FStar_All.pipe_right lids
                         (FStar_List.iter
                            (fun lid ->
                               (let uu____9322 =
                                  let uu____9325 = FStar_ST.op_Bang globals in
                                  (Top_level_def (lid.FStar_Ident.ident)) ::
                                    uu____9325 in
                                FStar_ST.op_Colon_Equals globals uu____9322);
                               (match () with
                                | () ->
                                    let modul =
                                      let uu____9527 =
                                        FStar_Ident.lid_of_ids
                                          lid.FStar_Ident.ns in
                                      uu____9527.FStar_Ident.str in
                                    ((let uu____9529 =
                                        get_exported_id_set env3 modul in
                                      match uu____9529 with
                                      | FStar_Pervasives_Native.Some f ->
                                          let my_exported_ids =
                                            f Exported_id_term_type in
                                          let uu____9583 =
                                            let uu____9584 =
                                              FStar_ST.op_Bang
                                                my_exported_ids in
                                            FStar_Util.set_add
                                              (lid.FStar_Ident.ident).FStar_Ident.idText
                                              uu____9584 in
                                          FStar_ST.op_Colon_Equals
                                            my_exported_ids uu____9583
                                      | FStar_Pervasives_Native.None -> ());
                                     (match () with
                                      | () ->
                                          let is_iface =
                                            env3.iface &&
                                              (Prims.op_Negation
                                                 env3.admitted_iface) in
                                          FStar_Util.smap_add (sigmap env3)
                                            lid.FStar_Ident.str
                                            (se,
                                              (env3.iface &&
                                                 (Prims.op_Negation
                                                    env3.admitted_iface))))))))));
           (let env4 =
              let uu___129_9787 = env3 in
              let uu____9788 = FStar_ST.op_Bang globals in
              {
                curmodule = (uu___129_9787.curmodule);
                curmonad = (uu___129_9787.curmonad);
                modules = (uu___129_9787.modules);
                scope_mods = uu____9788;
                exported_ids = (uu___129_9787.exported_ids);
                trans_exported_ids = (uu___129_9787.trans_exported_ids);
                includes = (uu___129_9787.includes);
                sigaccum = (uu___129_9787.sigaccum);
                sigmap = (uu___129_9787.sigmap);
                iface = (uu___129_9787.iface);
                admitted_iface = (uu___129_9787.admitted_iface);
                expect_typ = (uu___129_9787.expect_typ);
                docs = (uu___129_9787.docs);
                remaining_iface_decls = (uu___129_9787.remaining_iface_decls);
                syntax_only = (uu___129_9787.syntax_only);
                ds_hooks = (uu___129_9787.ds_hooks)
              } in
            env4))
let (push_namespace : env -> FStar_Ident.lident -> env) =
  fun env ->
    fun ns ->
      let uu____9896 =
        let uu____9901 = resolve_module_name env ns false in
        match uu____9901 with
        | FStar_Pervasives_Native.None ->
            let modules = env.modules in
            let uu____9915 =
              FStar_All.pipe_right modules
                (FStar_Util.for_some
                   (fun uu____9929 ->
                      match uu____9929 with
                      | (m, uu____9935) ->
                          FStar_Util.starts_with
                            (Prims.strcat (FStar_Ident.text_of_lid m) ".")
                            (Prims.strcat (FStar_Ident.text_of_lid ns) "."))) in
            if uu____9915
            then (ns, Open_namespace)
            else
              (let uu____9941 =
                 let uu____9946 =
                   FStar_Util.format1 "Namespace %s cannot be found"
                     (FStar_Ident.text_of_lid ns) in
                 (FStar_Errors.Fatal_NameSpaceNotFound, uu____9946) in
               FStar_Errors.raise_error uu____9941
                 (FStar_Ident.range_of_lid ns))
        | FStar_Pervasives_Native.Some ns' ->
            (fail_if_curmodule env ns ns'; (ns', Open_module)) in
      match uu____9896 with
      | (ns', kd) ->
          ((env.ds_hooks).ds_push_open_hook env (ns', kd);
           push_scope_mod env (Open_module_or_namespace (ns', kd)))
let (push_include : env -> FStar_Ident.lident -> env) =
  fun env ->
    fun ns ->
      let ns0 = ns in
      let uu____9963 = resolve_module_name env ns false in
      match uu____9963 with
      | FStar_Pervasives_Native.Some ns1 ->
          ((env.ds_hooks).ds_push_include_hook env ns1;
           fail_if_curmodule env ns0 ns1;
           (let env1 =
              push_scope_mod env
                (Open_module_or_namespace (ns1, Open_module)) in
            let curmod =
              let uu____9971 = current_module env1 in
              uu____9971.FStar_Ident.str in
            (let uu____9973 = FStar_Util.smap_try_find env1.includes curmod in
             match uu____9973 with
             | FStar_Pervasives_Native.None -> ()
             | FStar_Pervasives_Native.Some incl ->
                 let uu____9997 =
                   let uu____10000 = FStar_ST.op_Bang incl in ns1 ::
                     uu____10000 in
                 FStar_ST.op_Colon_Equals incl uu____9997);
            (match () with
             | () ->
                 let uu____10201 =
                   get_trans_exported_id_set env1 ns1.FStar_Ident.str in
                 (match uu____10201 with
                  | FStar_Pervasives_Native.Some ns_trans_exports ->
                      ((let uu____10218 =
                          let uu____10235 = get_exported_id_set env1 curmod in
                          let uu____10242 =
                            get_trans_exported_id_set env1 curmod in
                          (uu____10235, uu____10242) in
                        match uu____10218 with
                        | (FStar_Pervasives_Native.Some cur_exports,
                           FStar_Pervasives_Native.Some cur_trans_exports) ->
                            let update_exports k =
                              let ns_ex =
                                let uu____10296 = ns_trans_exports k in
                                FStar_ST.op_Bang uu____10296 in
                              let ex = cur_exports k in
                              (let uu____10512 =
                                 let uu____10513 = FStar_ST.op_Bang ex in
                                 FStar_Util.set_difference uu____10513 ns_ex in
                               FStar_ST.op_Colon_Equals ex uu____10512);
                              (match () with
                               | () ->
                                   let trans_ex = cur_trans_exports k in
                                   let uu____10745 =
                                     let uu____10746 =
                                       FStar_ST.op_Bang trans_ex in
                                     FStar_Util.set_union uu____10746 ns_ex in
                                   FStar_ST.op_Colon_Equals trans_ex
                                     uu____10745) in
                            FStar_List.iter update_exports
                              all_exported_id_kinds
                        | uu____10939 -> ());
                       (match () with | () -> env1))
                  | FStar_Pervasives_Native.None ->
                      let uu____10960 =
                        let uu____10965 =
                          FStar_Util.format1
                            "include: Module %s was not prepared"
                            ns1.FStar_Ident.str in
                        (FStar_Errors.Fatal_IncludeModuleNotPrepared,
                          uu____10965) in
                      FStar_Errors.raise_error uu____10960
                        (FStar_Ident.range_of_lid ns1)))))
      | uu____10966 ->
          let uu____10969 =
            let uu____10974 =
              FStar_Util.format1 "include: Module %s cannot be found"
                ns.FStar_Ident.str in
            (FStar_Errors.Fatal_ModuleNotFound, uu____10974) in
          FStar_Errors.raise_error uu____10969 (FStar_Ident.range_of_lid ns)
let (push_module_abbrev :
  env -> FStar_Ident.ident -> FStar_Ident.lident -> env) =
  fun env ->
    fun x ->
      fun l ->
        if module_is_defined env l
        then
          (fail_if_curmodule env l l;
           (env.ds_hooks).ds_push_module_abbrev_hook env x l;
           push_scope_mod env (Module_abbrev (x, l)))
        else
          (let uu____10987 =
             let uu____10992 =
               FStar_Util.format1 "Module %s cannot be found"
                 (FStar_Ident.text_of_lid l) in
             (FStar_Errors.Fatal_ModuleNotFound, uu____10992) in
           FStar_Errors.raise_error uu____10987 (FStar_Ident.range_of_lid l))
let (push_doc :
  env ->
    FStar_Ident.lident ->
      FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option -> env)
  =
  fun env ->
    fun l ->
      fun doc_opt ->
        match doc_opt with
        | FStar_Pervasives_Native.None -> env
        | FStar_Pervasives_Native.Some doc1 ->
            ((let uu____11008 =
                FStar_Util.smap_try_find env.docs l.FStar_Ident.str in
              match uu____11008 with
              | FStar_Pervasives_Native.None -> ()
              | FStar_Pervasives_Native.Some old_doc ->
                  let uu____11012 =
                    let uu____11017 =
                      let uu____11018 = FStar_Ident.string_of_lid l in
                      let uu____11019 =
                        FStar_Parser_AST.string_of_fsdoc old_doc in
                      let uu____11020 = FStar_Parser_AST.string_of_fsdoc doc1 in
                      FStar_Util.format3
                        "Overwriting doc of %s; old doc was [%s]; new doc are [%s]"
                        uu____11018 uu____11019 uu____11020 in
                    (FStar_Errors.Warning_DocOverwrite, uu____11017) in
                  FStar_Errors.log_issue (FStar_Ident.range_of_lid l)
                    uu____11012);
             FStar_Util.smap_add env.docs l.FStar_Ident.str doc1;
             env)
let (check_admits :
  env -> FStar_Syntax_Syntax.modul -> FStar_Syntax_Syntax.modul) =
  fun env ->
    fun m ->
      let admitted_sig_lids =
        FStar_All.pipe_right env.sigaccum
          (FStar_List.fold_left
             (fun lids ->
                fun se ->
                  match se.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_declare_typ (l, u, t) when
                      let uu____11056 =
                        FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption) in
                      Prims.op_Negation uu____11056 ->
                      let uu____11059 =
                        FStar_Util.smap_try_find (sigmap env)
                          l.FStar_Ident.str in
                      (match uu____11059 with
                       | FStar_Pervasives_Native.Some
                           ({
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_let uu____11072;
                              FStar_Syntax_Syntax.sigrng = uu____11073;
                              FStar_Syntax_Syntax.sigquals = uu____11074;
                              FStar_Syntax_Syntax.sigmeta = uu____11075;
                              FStar_Syntax_Syntax.sigattrs = uu____11076;_},
                            uu____11077)
                           -> lids
                       | FStar_Pervasives_Native.Some
                           ({
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_inductive_typ
                                uu____11092;
                              FStar_Syntax_Syntax.sigrng = uu____11093;
                              FStar_Syntax_Syntax.sigquals = uu____11094;
                              FStar_Syntax_Syntax.sigmeta = uu____11095;
                              FStar_Syntax_Syntax.sigattrs = uu____11096;_},
                            uu____11097)
                           -> lids
                       | uu____11122 ->
                           ((let uu____11130 =
                               let uu____11131 = FStar_Options.interactive () in
                               Prims.op_Negation uu____11131 in
                             if uu____11130
                             then
                               let uu____11132 =
                                 let uu____11137 =
                                   let uu____11138 =
                                     FStar_Ident.string_of_lid l in
                                   FStar_Util.format1
                                     "Admitting %s without a definition"
                                     uu____11138 in
                                 (FStar_Errors.Warning_AdmitWithoutDefinition,
                                   uu____11137) in
                               FStar_Errors.log_issue
                                 (FStar_Ident.range_of_lid l) uu____11132
                             else ());
                            (let quals = FStar_Syntax_Syntax.Assumption ::
                               (se.FStar_Syntax_Syntax.sigquals) in
                             FStar_Util.smap_add (sigmap env)
                               l.FStar_Ident.str
                               ((let uu___130_11149 = se in
                                 {
                                   FStar_Syntax_Syntax.sigel =
                                     (uu___130_11149.FStar_Syntax_Syntax.sigel);
                                   FStar_Syntax_Syntax.sigrng =
                                     (uu___130_11149.FStar_Syntax_Syntax.sigrng);
                                   FStar_Syntax_Syntax.sigquals = quals;
                                   FStar_Syntax_Syntax.sigmeta =
                                     (uu___130_11149.FStar_Syntax_Syntax.sigmeta);
                                   FStar_Syntax_Syntax.sigattrs =
                                     (uu___130_11149.FStar_Syntax_Syntax.sigattrs)
                                 }), false);
                             l
                             ::
                             lids)))
                  | uu____11150 -> lids) []) in
      let uu___131_11151 = m in
      let uu____11152 =
        FStar_All.pipe_right m.FStar_Syntax_Syntax.declarations
          (FStar_List.map
             (fun s ->
                match s.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_declare_typ
                    (lid, uu____11162, uu____11163) when
                    FStar_List.existsb
                      (fun l -> FStar_Ident.lid_equals l lid)
                      admitted_sig_lids
                    ->
                    let uu___132_11166 = s in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___132_11166.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___132_11166.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals =
                        (FStar_Syntax_Syntax.Assumption ::
                        (s.FStar_Syntax_Syntax.sigquals));
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___132_11166.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___132_11166.FStar_Syntax_Syntax.sigattrs)
                    }
                | uu____11167 -> s)) in
      {
        FStar_Syntax_Syntax.name = (uu___131_11151.FStar_Syntax_Syntax.name);
        FStar_Syntax_Syntax.declarations = uu____11152;
        FStar_Syntax_Syntax.exports =
          (uu___131_11151.FStar_Syntax_Syntax.exports);
        FStar_Syntax_Syntax.is_interface =
          (uu___131_11151.FStar_Syntax_Syntax.is_interface)
      }
let (finish : env -> FStar_Syntax_Syntax.modul -> env) =
  fun env ->
    fun modul ->
      FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations
        (FStar_List.iter
           (fun se ->
              let quals = se.FStar_Syntax_Syntax.sigquals in
              match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_bundle (ses, uu____11184) ->
                  if
                    (FStar_List.contains FStar_Syntax_Syntax.Private quals)
                      ||
                      (FStar_List.contains FStar_Syntax_Syntax.Abstract quals)
                  then
                    FStar_All.pipe_right ses
                      (FStar_List.iter
                         (fun se1 ->
                            match se1.FStar_Syntax_Syntax.sigel with
                            | FStar_Syntax_Syntax.Sig_datacon
                                (lid, uu____11204, uu____11205, uu____11206,
                                 uu____11207, uu____11208)
                                ->
                                FStar_Util.smap_remove (sigmap env)
                                  lid.FStar_Ident.str
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (lid, univ_names, binders, typ, uu____11221,
                                 uu____11222)
                                ->
                                (FStar_Util.smap_remove (sigmap env)
                                   lid.FStar_Ident.str;
                                 if
                                   Prims.op_Negation
                                     (FStar_List.contains
                                        FStar_Syntax_Syntax.Private quals)
                                 then
                                   (let sigel =
                                      let uu____11237 =
                                        let uu____11244 =
                                          let uu____11247 =
                                            let uu____11250 =
                                              let uu____11251 =
                                                let uu____11264 =
                                                  FStar_Syntax_Syntax.mk_Total
                                                    typ in
                                                (binders, uu____11264) in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____11251 in
                                            FStar_Syntax_Syntax.mk
                                              uu____11250 in
                                          uu____11247
                                            FStar_Pervasives_Native.None
                                            (FStar_Ident.range_of_lid lid) in
                                        (lid, univ_names, uu____11244) in
                                      FStar_Syntax_Syntax.Sig_declare_typ
                                        uu____11237 in
                                    let se2 =
                                      let uu___133_11271 = se1 in
                                      {
                                        FStar_Syntax_Syntax.sigel = sigel;
                                        FStar_Syntax_Syntax.sigrng =
                                          (uu___133_11271.FStar_Syntax_Syntax.sigrng);
                                        FStar_Syntax_Syntax.sigquals =
                                          (FStar_Syntax_Syntax.Assumption ::
                                          quals);
                                        FStar_Syntax_Syntax.sigmeta =
                                          (uu___133_11271.FStar_Syntax_Syntax.sigmeta);
                                        FStar_Syntax_Syntax.sigattrs =
                                          (uu___133_11271.FStar_Syntax_Syntax.sigattrs)
                                      } in
                                    FStar_Util.smap_add (sigmap env)
                                      lid.FStar_Ident.str (se2, false))
                                 else ())
                            | uu____11277 -> ()))
                  else ()
              | FStar_Syntax_Syntax.Sig_declare_typ
                  (lid, uu____11280, uu____11281) ->
                  if FStar_List.contains FStar_Syntax_Syntax.Private quals
                  then
                    FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str
                  else ()
              | FStar_Syntax_Syntax.Sig_let ((uu____11287, lbs), uu____11289)
                  ->
                  (if
                     (FStar_List.contains FStar_Syntax_Syntax.Private quals)
                       ||
                       (FStar_List.contains FStar_Syntax_Syntax.Abstract
                          quals)
                   then
                     FStar_All.pipe_right lbs
                       (FStar_List.iter
                          (fun lb ->
                             let uu____11310 =
                               let uu____11311 =
                                 let uu____11312 =
                                   let uu____11315 =
                                     FStar_Util.right
                                       lb.FStar_Syntax_Syntax.lbname in
                                   uu____11315.FStar_Syntax_Syntax.fv_name in
                                 uu____11312.FStar_Syntax_Syntax.v in
                               uu____11311.FStar_Ident.str in
                             FStar_Util.smap_remove (sigmap env) uu____11310))
                   else ();
                   if
                     (FStar_List.contains FStar_Syntax_Syntax.Abstract quals)
                       &&
                       (Prims.op_Negation
                          (FStar_List.contains FStar_Syntax_Syntax.Private
                             quals))
                   then
                     FStar_All.pipe_right lbs
                       (FStar_List.iter
                          (fun lb ->
                             let lid =
                               let uu____11329 =
                                 let uu____11332 =
                                   FStar_Util.right
                                     lb.FStar_Syntax_Syntax.lbname in
                                 uu____11332.FStar_Syntax_Syntax.fv_name in
                               uu____11329.FStar_Syntax_Syntax.v in
                             let quals1 = FStar_Syntax_Syntax.Assumption ::
                               quals in
                             let decl =
                               let uu___134_11337 = se in
                               {
                                 FStar_Syntax_Syntax.sigel =
                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                      (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                        (lb.FStar_Syntax_Syntax.lbtyp)));
                                 FStar_Syntax_Syntax.sigrng =
                                   (uu___134_11337.FStar_Syntax_Syntax.sigrng);
                                 FStar_Syntax_Syntax.sigquals = quals1;
                                 FStar_Syntax_Syntax.sigmeta =
                                   (uu___134_11337.FStar_Syntax_Syntax.sigmeta);
                                 FStar_Syntax_Syntax.sigattrs =
                                   (uu___134_11337.FStar_Syntax_Syntax.sigattrs)
                               } in
                             FStar_Util.smap_add (sigmap env)
                               lid.FStar_Ident.str (decl, false)))
                   else ())
              | uu____11347 -> ()));
      (let curmod =
         let uu____11349 = current_module env in uu____11349.FStar_Ident.str in
       (let uu____11351 =
          let uu____11368 = get_exported_id_set env curmod in
          let uu____11375 = get_trans_exported_id_set env curmod in
          (uu____11368, uu____11375) in
        match uu____11351 with
        | (FStar_Pervasives_Native.Some cur_ex, FStar_Pervasives_Native.Some
           cur_trans_ex) ->
            let update_exports eikind =
              let cur_ex_set =
                let uu____11429 = cur_ex eikind in
                FStar_ST.op_Bang uu____11429 in
              let cur_trans_ex_set_ref = cur_trans_ex eikind in
              let uu____11644 =
                let uu____11645 = FStar_ST.op_Bang cur_trans_ex_set_ref in
                FStar_Util.set_union cur_ex_set uu____11645 in
              FStar_ST.op_Colon_Equals cur_trans_ex_set_ref uu____11644 in
            FStar_List.iter update_exports all_exported_id_kinds
        | uu____11838 -> ());
       (match () with
        | () ->
            (filter_record_cache ();
             (match () with
              | () ->
                  let uu___135_11856 = env in
                  {
                    curmodule = FStar_Pervasives_Native.None;
                    curmonad = (uu___135_11856.curmonad);
                    modules = (((modul.FStar_Syntax_Syntax.name), modul) ::
                      (env.modules));
                    scope_mods = [];
                    exported_ids = (uu___135_11856.exported_ids);
                    trans_exported_ids = (uu___135_11856.trans_exported_ids);
                    includes = (uu___135_11856.includes);
                    sigaccum = [];
                    sigmap = (uu___135_11856.sigmap);
                    iface = (uu___135_11856.iface);
                    admitted_iface = (uu___135_11856.admitted_iface);
                    expect_typ = (uu___135_11856.expect_typ);
                    docs = (uu___135_11856.docs);
                    remaining_iface_decls =
                      (uu___135_11856.remaining_iface_decls);
                    syntax_only = (uu___135_11856.syntax_only);
                    ds_hooks = (uu___135_11856.ds_hooks)
                  }))))
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref []
let (push : env -> env) =
  fun env ->
    push_record_cache ();
    (let uu____11907 =
       let uu____11910 = FStar_ST.op_Bang stack in env :: uu____11910 in
     FStar_ST.op_Colon_Equals stack uu____11907);
    (let uu___136_11971 = env in
     let uu____11972 = FStar_Util.smap_copy (sigmap env) in
     let uu____11983 = FStar_Util.smap_copy env.docs in
     {
       curmodule = (uu___136_11971.curmodule);
       curmonad = (uu___136_11971.curmonad);
       modules = (uu___136_11971.modules);
       scope_mods = (uu___136_11971.scope_mods);
       exported_ids = (uu___136_11971.exported_ids);
       trans_exported_ids = (uu___136_11971.trans_exported_ids);
       includes = (uu___136_11971.includes);
       sigaccum = (uu___136_11971.sigaccum);
       sigmap = uu____11972;
       iface = (uu___136_11971.iface);
       admitted_iface = (uu___136_11971.admitted_iface);
       expect_typ = (uu___136_11971.expect_typ);
       docs = uu____11983;
       remaining_iface_decls = (uu___136_11971.remaining_iface_decls);
       syntax_only = (uu___136_11971.syntax_only);
       ds_hooks = (uu___136_11971.ds_hooks)
     })
let (pop : Prims.unit -> env) =
  fun uu____11988 ->
    let uu____11989 = FStar_ST.op_Bang stack in
    match uu____11989 with
    | env::tl1 ->
        (pop_record_cache (); FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____12056 -> failwith "Impossible: Too many pops"
let (export_interface : FStar_Ident.lident -> env -> env) =
  fun m ->
    fun env ->
      let sigelt_in_m se =
        match FStar_Syntax_Util.lids_of_sigelt se with
        | l::uu____12070 -> l.FStar_Ident.nsstr = m.FStar_Ident.str
        | uu____12073 -> false in
      let sm = sigmap env in
      let env1 = pop () in
      let keys = FStar_Util.smap_keys sm in
      let sm' = sigmap env1 in
      FStar_All.pipe_right keys
        (FStar_List.iter
           (fun k ->
              let uu____12107 = FStar_Util.smap_try_find sm' k in
              match uu____12107 with
              | FStar_Pervasives_Native.Some (se, true) when sigelt_in_m se
                  ->
                  (FStar_Util.smap_remove sm' k;
                   (let se1 =
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_declare_typ (l, u, t) ->
                          let uu___137_12132 = se in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (uu___137_12132.FStar_Syntax_Syntax.sigel);
                            FStar_Syntax_Syntax.sigrng =
                              (uu___137_12132.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (FStar_Syntax_Syntax.Assumption ::
                              (se.FStar_Syntax_Syntax.sigquals));
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___137_12132.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___137_12132.FStar_Syntax_Syntax.sigattrs)
                          }
                      | uu____12133 -> se in
                    FStar_Util.smap_add sm' k (se1, false)))
              | uu____12138 -> ()));
      env1
let (finish_module_or_interface :
  env ->
    FStar_Syntax_Syntax.modul ->
      (env, FStar_Syntax_Syntax.modul) FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun modul ->
      let modul1 =
        if Prims.op_Negation modul.FStar_Syntax_Syntax.is_interface
        then check_admits env modul
        else modul in
      let uu____12157 = finish env modul1 in (uu____12157, modul1)
type exported_ids =
  {
  exported_id_terms: Prims.string Prims.list ;
  exported_id_fields: Prims.string Prims.list }[@@deriving show]
let (__proj__Mkexported_ids__item__exported_id_terms :
  exported_ids -> Prims.string Prims.list) =
  fun projectee ->
    match projectee with
    | { exported_id_terms = __fname__exported_id_terms;
        exported_id_fields = __fname__exported_id_fields;_} ->
        __fname__exported_id_terms
let (__proj__Mkexported_ids__item__exported_id_fields :
  exported_ids -> Prims.string Prims.list) =
  fun projectee ->
    match projectee with
    | { exported_id_terms = __fname__exported_id_terms;
        exported_id_fields = __fname__exported_id_fields;_} ->
        __fname__exported_id_fields
let (as_exported_ids : exported_id_set -> exported_ids) =
  fun e ->
    let terms =
      let uu____12307 =
        let uu____12310 = e Exported_id_term_type in
        FStar_ST.op_Bang uu____12310 in
      FStar_Util.set_elements uu____12307 in
    let fields =
      let uu____12490 =
        let uu____12493 = e Exported_id_field in FStar_ST.op_Bang uu____12493 in
      FStar_Util.set_elements uu____12490 in
    { exported_id_terms = terms; exported_id_fields = fields }
let (as_exported_id_set :
  exported_ids FStar_Pervasives_Native.option ->
    exported_id_kind -> Prims.string FStar_Util.set FStar_ST.ref)
  =
  fun e ->
    match e with
    | FStar_Pervasives_Native.None -> exported_id_set_new ()
    | FStar_Pervasives_Native.Some e1 ->
        let terms =
          let uu____12730 =
            FStar_Util.as_set e1.exported_id_terms FStar_Util.compare in
          FStar_Util.mk_ref uu____12730 in
        let fields =
          let uu____12740 =
            FStar_Util.as_set e1.exported_id_fields FStar_Util.compare in
          FStar_Util.mk_ref uu____12740 in
        (fun uu___112_12745 ->
           match uu___112_12745 with
           | Exported_id_term_type -> terms
           | Exported_id_field -> fields)
type module_inclusion_info =
  {
  mii_exported_ids: exported_ids FStar_Pervasives_Native.option ;
  mii_trans_exported_ids: exported_ids FStar_Pervasives_Native.option ;
  mii_includes: FStar_Ident.lident Prims.list FStar_Pervasives_Native.option }
[@@deriving show]
let (__proj__Mkmodule_inclusion_info__item__mii_exported_ids :
  module_inclusion_info -> exported_ids FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { mii_exported_ids = __fname__mii_exported_ids;
        mii_trans_exported_ids = __fname__mii_trans_exported_ids;
        mii_includes = __fname__mii_includes;_} -> __fname__mii_exported_ids
let (__proj__Mkmodule_inclusion_info__item__mii_trans_exported_ids :
  module_inclusion_info -> exported_ids FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { mii_exported_ids = __fname__mii_exported_ids;
        mii_trans_exported_ids = __fname__mii_trans_exported_ids;
        mii_includes = __fname__mii_includes;_} ->
        __fname__mii_trans_exported_ids
let (__proj__Mkmodule_inclusion_info__item__mii_includes :
  module_inclusion_info ->
    FStar_Ident.lident Prims.list FStar_Pervasives_Native.option)
  =
  fun projectee ->
    match projectee with
    | { mii_exported_ids = __fname__mii_exported_ids;
        mii_trans_exported_ids = __fname__mii_trans_exported_ids;
        mii_includes = __fname__mii_includes;_} -> __fname__mii_includes
let (default_mii : module_inclusion_info) =
  {
    mii_exported_ids = FStar_Pervasives_Native.None;
    mii_trans_exported_ids = FStar_Pervasives_Native.None;
    mii_includes = FStar_Pervasives_Native.None
  }
let as_includes :
  'Auu____12937 .
    'Auu____12937 Prims.list FStar_Pervasives_Native.option ->
      'Auu____12937 Prims.list FStar_ST.ref
  =
  fun uu___113_12949 ->
    match uu___113_12949 with
    | FStar_Pervasives_Native.None -> FStar_Util.mk_ref []
    | FStar_Pervasives_Native.Some l -> FStar_Util.mk_ref l
let (inclusion_info : env -> FStar_Ident.lident -> module_inclusion_info) =
  fun env ->
    fun l ->
      let mname = FStar_Ident.string_of_lid l in
      let as_ids_opt m =
        let uu____12982 = FStar_Util.smap_try_find m mname in
        FStar_Util.map_opt uu____12982 as_exported_ids in
      let uu____12985 = as_ids_opt env.exported_ids in
      let uu____12988 = as_ids_opt env.trans_exported_ids in
      let uu____12991 =
        let uu____12996 = FStar_Util.smap_try_find env.includes mname in
        FStar_Util.map_opt uu____12996 (fun r -> FStar_ST.op_Bang r) in
      {
        mii_exported_ids = uu____12985;
        mii_trans_exported_ids = uu____12988;
        mii_includes = uu____12991
      }
let (prepare_module_or_interface :
  Prims.bool ->
    Prims.bool ->
      env ->
        FStar_Ident.lident ->
          module_inclusion_info ->
            (env, Prims.bool) FStar_Pervasives_Native.tuple2)
  =
  fun intf ->
    fun admitted ->
      fun env ->
        fun mname ->
          fun mii ->
            let prep env1 =
              let filename =
                FStar_Util.strcat (FStar_Ident.text_of_lid mname) ".fst" in
              let auto_open =
                FStar_Parser_Dep.hard_coded_dependencies filename in
              let auto_open1 =
                let convert_kind uu___114_13194 =
                  match uu___114_13194 with
                  | FStar_Parser_Dep.Open_namespace -> Open_namespace
                  | FStar_Parser_Dep.Open_module -> Open_module in
                FStar_List.map
                  (fun uu____13206 ->
                     match uu____13206 with
                     | (lid, kind) -> (lid, (convert_kind kind))) auto_open in
              let namespace_of_module =
                if
                  (FStar_List.length mname.FStar_Ident.ns) >
                    (Prims.parse_int "0")
                then
                  let uu____13230 =
                    let uu____13235 =
                      FStar_Ident.lid_of_ids mname.FStar_Ident.ns in
                    (uu____13235, Open_namespace) in
                  [uu____13230]
                else [] in
              let auto_open2 =
                FStar_List.append namespace_of_module
                  (FStar_List.rev auto_open1) in
              (let uu____13265 = as_exported_id_set mii.mii_exported_ids in
               FStar_Util.smap_add env1.exported_ids mname.FStar_Ident.str
                 uu____13265);
              (match () with
               | () ->
                   ((let uu____13337 =
                       as_exported_id_set mii.mii_trans_exported_ids in
                     FStar_Util.smap_add env1.trans_exported_ids
                       mname.FStar_Ident.str uu____13337);
                    (match () with
                     | () ->
                         ((let uu____13409 = as_includes mii.mii_includes in
                           FStar_Util.smap_add env1.includes
                             mname.FStar_Ident.str uu____13409);
                          (match () with
                           | () ->
                               let env' =
                                 let uu___138_13489 = env1 in
                                 let uu____13490 =
                                   FStar_List.map
                                     (fun x -> Open_module_or_namespace x)
                                     auto_open2 in
                                 {
                                   curmodule =
                                     (FStar_Pervasives_Native.Some mname);
                                   curmonad = (uu___138_13489.curmonad);
                                   modules = (uu___138_13489.modules);
                                   scope_mods = uu____13490;
                                   exported_ids =
                                     (uu___138_13489.exported_ids);
                                   trans_exported_ids =
                                     (uu___138_13489.trans_exported_ids);
                                   includes = (uu___138_13489.includes);
                                   sigaccum = (uu___138_13489.sigaccum);
                                   sigmap = (env1.sigmap);
                                   iface = intf;
                                   admitted_iface = admitted;
                                   expect_typ = (uu___138_13489.expect_typ);
                                   docs = (uu___138_13489.docs);
                                   remaining_iface_decls =
                                     (uu___138_13489.remaining_iface_decls);
                                   syntax_only = (uu___138_13489.syntax_only);
                                   ds_hooks = (uu___138_13489.ds_hooks)
                                 } in
                               (FStar_List.iter
                                  (fun op ->
                                     (env1.ds_hooks).ds_push_open_hook env'
                                       op) (FStar_List.rev auto_open2);
                                env')))))) in
            let uu____13502 =
              FStar_All.pipe_right env.modules
                (FStar_Util.find_opt
                   (fun uu____13528 ->
                      match uu____13528 with
                      | (l, uu____13534) -> FStar_Ident.lid_equals l mname)) in
            match uu____13502 with
            | FStar_Pervasives_Native.None ->
                let uu____13543 = prep env in (uu____13543, false)
            | FStar_Pervasives_Native.Some (uu____13544, m) ->
                ((let uu____13551 =
                    (let uu____13554 = FStar_Options.interactive () in
                     Prims.op_Negation uu____13554) &&
                      ((Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)
                         || intf) in
                  if uu____13551
                  then
                    let uu____13555 =
                      let uu____13560 =
                        FStar_Util.format1
                          "Duplicate module or interface name: %s"
                          mname.FStar_Ident.str in
                      (FStar_Errors.Fatal_DuplicateModuleOrInterface,
                        uu____13560) in
                    FStar_Errors.raise_error uu____13555
                      (FStar_Ident.range_of_lid mname)
                  else ());
                 (let uu____13562 =
                    let uu____13563 = push env in prep uu____13563 in
                  (uu____13562, true)))
let (enter_monad_scope : env -> FStar_Ident.ident -> env) =
  fun env ->
    fun mname ->
      match env.curmonad with
      | FStar_Pervasives_Native.Some mname' ->
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_MonadAlreadyDefined,
              (Prims.strcat "Trying to define monad "
                 (Prims.strcat mname.FStar_Ident.idText
                    (Prims.strcat ", but already in monad scope "
                       mname'.FStar_Ident.idText))))
            mname.FStar_Ident.idRange
      | FStar_Pervasives_Native.None ->
          let uu___139_13571 = env in
          {
            curmodule = (uu___139_13571.curmodule);
            curmonad = (FStar_Pervasives_Native.Some mname);
            modules = (uu___139_13571.modules);
            scope_mods = (uu___139_13571.scope_mods);
            exported_ids = (uu___139_13571.exported_ids);
            trans_exported_ids = (uu___139_13571.trans_exported_ids);
            includes = (uu___139_13571.includes);
            sigaccum = (uu___139_13571.sigaccum);
            sigmap = (uu___139_13571.sigmap);
            iface = (uu___139_13571.iface);
            admitted_iface = (uu___139_13571.admitted_iface);
            expect_typ = (uu___139_13571.expect_typ);
            docs = (uu___139_13571.docs);
            remaining_iface_decls = (uu___139_13571.remaining_iface_decls);
            syntax_only = (uu___139_13571.syntax_only);
            ds_hooks = (uu___139_13571.ds_hooks)
          }
let fail_or :
  'a .
    env ->
      (FStar_Ident.lident -> 'a FStar_Pervasives_Native.option) ->
        FStar_Ident.lident -> 'a
  =
  fun env ->
    fun lookup1 ->
      fun lid ->
        let uu____13598 = lookup1 lid in
        match uu____13598 with
        | FStar_Pervasives_Native.None ->
            let opened_modules =
              FStar_List.map
                (fun uu____13611 ->
                   match uu____13611 with
                   | (lid1, uu____13617) -> FStar_Ident.text_of_lid lid1)
                env.modules in
            let msg =
              FStar_Util.format1 "Identifier not found: [%s]"
                (FStar_Ident.text_of_lid lid) in
            let msg1 =
              if
                (FStar_List.length lid.FStar_Ident.ns) =
                  (Prims.parse_int "0")
              then msg
              else
                (let modul =
                   let uu____13622 =
                     FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
                   FStar_Ident.set_lid_range uu____13622
                     (FStar_Ident.range_of_lid lid) in
                 let uu____13623 = resolve_module_name env modul true in
                 match uu____13623 with
                 | FStar_Pervasives_Native.None ->
                     let opened_modules1 =
                       FStar_String.concat ", " opened_modules in
                     FStar_Util.format3
                       "%s\nModule %s does not belong to the list of modules in scope, namely %s"
                       msg modul.FStar_Ident.str opened_modules1
                 | FStar_Pervasives_Native.Some modul' when
                     Prims.op_Negation
                       (FStar_List.existsb
                          (fun m -> m = modul'.FStar_Ident.str)
                          opened_modules)
                     ->
                     let opened_modules1 =
                       FStar_String.concat ", " opened_modules in
                     FStar_Util.format4
                       "%s\nModule %s resolved into %s, which does not belong to the list of modules in scope, namely %s"
                       msg modul.FStar_Ident.str modul'.FStar_Ident.str
                       opened_modules1
                 | FStar_Pervasives_Native.Some modul' ->
                     FStar_Util.format4
                       "%s\nModule %s resolved into %s, definition %s not found"
                       msg modul.FStar_Ident.str modul'.FStar_Ident.str
                       (lid.FStar_Ident.ident).FStar_Ident.idText) in
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_IdentifierNotFound, msg1)
              (FStar_Ident.range_of_lid lid)
        | FStar_Pervasives_Native.Some r -> r
let fail_or2 :
  'a .
    (FStar_Ident.ident -> 'a FStar_Pervasives_Native.option) ->
      FStar_Ident.ident -> 'a
  =
  fun lookup1 ->
    fun id1 ->
      let uu____13654 = lookup1 id1 in
      match uu____13654 with
      | FStar_Pervasives_Native.None ->
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_IdentifierNotFound,
              (Prims.strcat "Identifier not found ["
                 (Prims.strcat id1.FStar_Ident.idText "]")))
            id1.FStar_Ident.idRange
      | FStar_Pervasives_Native.Some r -> r
let (mk_copy : env -> env) =
  fun en ->
    let uu___140_13661 = en in
    let uu____13662 = FStar_Util.smap_copy en.exported_ids in
    let uu____13665 = FStar_Util.smap_copy en.trans_exported_ids in
    let uu____13668 = FStar_Util.smap_copy en.sigmap in
    let uu____13679 = FStar_Util.smap_copy en.docs in
    {
      curmodule = (uu___140_13661.curmodule);
      curmonad = (uu___140_13661.curmonad);
      modules = (uu___140_13661.modules);
      scope_mods = (uu___140_13661.scope_mods);
      exported_ids = uu____13662;
      trans_exported_ids = uu____13665;
      includes = (uu___140_13661.includes);
      sigaccum = (uu___140_13661.sigaccum);
      sigmap = uu____13668;
      iface = (uu___140_13661.iface);
      admitted_iface = (uu___140_13661.admitted_iface);
      expect_typ = (uu___140_13661.expect_typ);
      docs = uu____13679;
      remaining_iface_decls = (uu___140_13661.remaining_iface_decls);
      syntax_only = (uu___140_13661.syntax_only);
      ds_hooks = (uu___140_13661.ds_hooks)
    }