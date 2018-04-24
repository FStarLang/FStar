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
    match projectee with | Open_module -> true | uu____22 -> false
let (uu___is_Open_namespace : open_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | Open_namespace -> true | uu____28 -> false
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
    match projectee with | Local_binding _0 -> true | uu____219 -> false
let (__proj__Local_binding__item___0 : scope_mod -> local_binding) =
  fun projectee -> match projectee with | Local_binding _0 -> _0
let (uu___is_Rec_binding : scope_mod -> Prims.bool) =
  fun projectee ->
    match projectee with | Rec_binding _0 -> true | uu____233 -> false
let (__proj__Rec_binding__item___0 : scope_mod -> rec_binding) =
  fun projectee -> match projectee with | Rec_binding _0 -> _0
let (uu___is_Module_abbrev : scope_mod -> Prims.bool) =
  fun projectee ->
    match projectee with | Module_abbrev _0 -> true | uu____247 -> false
let (__proj__Module_abbrev__item___0 : scope_mod -> module_abbrev) =
  fun projectee -> match projectee with | Module_abbrev _0 -> _0
let (uu___is_Open_module_or_namespace : scope_mod -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Open_module_or_namespace _0 -> true
    | uu____261 -> false
let (__proj__Open_module_or_namespace__item___0 :
  scope_mod -> open_module_or_namespace) =
  fun projectee -> match projectee with | Open_module_or_namespace _0 -> _0
let (uu___is_Top_level_def : scope_mod -> Prims.bool) =
  fun projectee ->
    match projectee with | Top_level_def _0 -> true | uu____275 -> false
let (__proj__Top_level_def__item___0 : scope_mod -> FStar_Ident.ident) =
  fun projectee -> match projectee with | Top_level_def _0 -> _0
let (uu___is_Record_or_dc : scope_mod -> Prims.bool) =
  fun projectee ->
    match projectee with | Record_or_dc _0 -> true | uu____289 -> false
let (__proj__Record_or_dc__item___0 : scope_mod -> record_or_dc) =
  fun projectee -> match projectee with | Record_or_dc _0 -> _0
type string_set = Prims.string FStar_Util.set[@@deriving show]
type exported_id_kind =
  | Exported_id_term_type 
  | Exported_id_field [@@deriving show]
let (uu___is_Exported_id_term_type : exported_id_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | Exported_id_term_type -> true | uu____304 -> false
let (uu___is_Exported_id_field : exported_id_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | Exported_id_field -> true | uu____310 -> false
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
  ds_push_open_hook: env -> open_module_or_namespace -> unit ;
  ds_push_include_hook: env -> FStar_Ident.lident -> unit ;
  ds_push_module_abbrev_hook:
    env -> FStar_Ident.ident -> FStar_Ident.lident -> unit }[@@deriving show]
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
  dsenv_hooks -> env -> open_module_or_namespace -> unit) =
  fun projectee ->
    match projectee with
    | { ds_push_open_hook = __fname__ds_push_open_hook;
        ds_push_include_hook = __fname__ds_push_include_hook;
        ds_push_module_abbrev_hook = __fname__ds_push_module_abbrev_hook;_}
        -> __fname__ds_push_open_hook
let (__proj__Mkdsenv_hooks__item__ds_push_include_hook :
  dsenv_hooks -> env -> FStar_Ident.lident -> unit) =
  fun projectee ->
    match projectee with
    | { ds_push_open_hook = __fname__ds_push_open_hook;
        ds_push_include_hook = __fname__ds_push_include_hook;
        ds_push_module_abbrev_hook = __fname__ds_push_module_abbrev_hook;_}
        -> __fname__ds_push_include_hook
let (__proj__Mkdsenv_hooks__item__ds_push_module_abbrev_hook :
  dsenv_hooks -> env -> FStar_Ident.ident -> FStar_Ident.lident -> unit) =
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
    ds_push_open_hook = (fun uu____1797 -> fun uu____1798 -> ());
    ds_push_include_hook = (fun uu____1801 -> fun uu____1802 -> ());
    ds_push_module_abbrev_hook =
      (fun uu____1806 -> fun uu____1807 -> fun uu____1808 -> ())
  }
type foundname =
  | Term_name of (FStar_Syntax_Syntax.typ, Prims.bool,
  FStar_Syntax_Syntax.attribute Prims.list) FStar_Pervasives_Native.tuple3 
  | Eff_name of (FStar_Syntax_Syntax.sigelt, FStar_Ident.lident)
  FStar_Pervasives_Native.tuple2 [@@deriving show]
let (uu___is_Term_name : foundname -> Prims.bool) =
  fun projectee ->
    match projectee with | Term_name _0 -> true | uu____1845 -> false
let (__proj__Term_name__item___0 :
  foundname ->
    (FStar_Syntax_Syntax.typ, Prims.bool,
      FStar_Syntax_Syntax.attribute Prims.list)
      FStar_Pervasives_Native.tuple3)
  = fun projectee -> match projectee with | Term_name _0 -> _0
let (uu___is_Eff_name : foundname -> Prims.bool) =
  fun projectee ->
    match projectee with | Eff_name _0 -> true | uu____1887 -> false
let (__proj__Eff_name__item___0 :
  foundname ->
    (FStar_Syntax_Syntax.sigelt, FStar_Ident.lident)
      FStar_Pervasives_Native.tuple2)
  = fun projectee -> match projectee with | Eff_name _0 -> _0
let (set_iface : env -> Prims.bool -> env) =
  fun env ->
    fun b ->
      let uu___115_1917 = env in
      {
        curmodule = (uu___115_1917.curmodule);
        curmonad = (uu___115_1917.curmonad);
        modules = (uu___115_1917.modules);
        scope_mods = (uu___115_1917.scope_mods);
        exported_ids = (uu___115_1917.exported_ids);
        trans_exported_ids = (uu___115_1917.trans_exported_ids);
        includes = (uu___115_1917.includes);
        sigaccum = (uu___115_1917.sigaccum);
        sigmap = (uu___115_1917.sigmap);
        iface = b;
        admitted_iface = (uu___115_1917.admitted_iface);
        expect_typ = (uu___115_1917.expect_typ);
        docs = (uu___115_1917.docs);
        remaining_iface_decls = (uu___115_1917.remaining_iface_decls);
        syntax_only = (uu___115_1917.syntax_only);
        ds_hooks = (uu___115_1917.ds_hooks)
      }
let (iface : env -> Prims.bool) = fun e -> e.iface
let (set_admitted_iface : env -> Prims.bool -> env) =
  fun e ->
    fun b ->
      let uu___116_1933 = e in
      {
        curmodule = (uu___116_1933.curmodule);
        curmonad = (uu___116_1933.curmonad);
        modules = (uu___116_1933.modules);
        scope_mods = (uu___116_1933.scope_mods);
        exported_ids = (uu___116_1933.exported_ids);
        trans_exported_ids = (uu___116_1933.trans_exported_ids);
        includes = (uu___116_1933.includes);
        sigaccum = (uu___116_1933.sigaccum);
        sigmap = (uu___116_1933.sigmap);
        iface = (uu___116_1933.iface);
        admitted_iface = b;
        expect_typ = (uu___116_1933.expect_typ);
        docs = (uu___116_1933.docs);
        remaining_iface_decls = (uu___116_1933.remaining_iface_decls);
        syntax_only = (uu___116_1933.syntax_only);
        ds_hooks = (uu___116_1933.ds_hooks)
      }
let (admitted_iface : env -> Prims.bool) = fun e -> e.admitted_iface
let (set_expect_typ : env -> Prims.bool -> env) =
  fun e ->
    fun b ->
      let uu___117_1949 = e in
      {
        curmodule = (uu___117_1949.curmodule);
        curmonad = (uu___117_1949.curmonad);
        modules = (uu___117_1949.modules);
        scope_mods = (uu___117_1949.scope_mods);
        exported_ids = (uu___117_1949.exported_ids);
        trans_exported_ids = (uu___117_1949.trans_exported_ids);
        includes = (uu___117_1949.includes);
        sigaccum = (uu___117_1949.sigaccum);
        sigmap = (uu___117_1949.sigmap);
        iface = (uu___117_1949.iface);
        admitted_iface = (uu___117_1949.admitted_iface);
        expect_typ = b;
        docs = (uu___117_1949.docs);
        remaining_iface_decls = (uu___117_1949.remaining_iface_decls);
        syntax_only = (uu___117_1949.syntax_only);
        ds_hooks = (uu___117_1949.ds_hooks)
      }
let (expect_typ : env -> Prims.bool) = fun e -> e.expect_typ
let (all_exported_id_kinds : exported_id_kind Prims.list) =
  [Exported_id_field; Exported_id_term_type]
let (transitive_exported_ids :
  env -> FStar_Ident.lident -> Prims.string Prims.list) =
  fun env ->
    fun lid ->
      let module_name = FStar_Ident.string_of_lid lid in
      let uu____1970 =
        FStar_Util.smap_try_find env.trans_exported_ids module_name in
      match uu____1970 with
      | FStar_Pervasives_Native.None -> []
      | FStar_Pervasives_Native.Some exported_id_set ->
          let uu____1981 =
            let uu____1982 = exported_id_set Exported_id_term_type in
            FStar_ST.op_Bang uu____1982 in
          FStar_All.pipe_right uu____1981 FStar_Util.set_elements
let (open_modules :
  env ->
    (FStar_Ident.lident, FStar_Syntax_Syntax.modul)
      FStar_Pervasives_Native.tuple2 Prims.list)
  = fun e -> e.modules
let (open_modules_and_namespaces : env -> FStar_Ident.lident Prims.list) =
  fun env ->
    FStar_List.filter_map
      (fun uu___84_2190 ->
         match uu___84_2190 with
         | Open_module_or_namespace (lid, _info) ->
             FStar_Pervasives_Native.Some lid
         | uu____2195 -> FStar_Pervasives_Native.None) env.scope_mods
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun e ->
    fun l ->
      let uu___118_2206 = e in
      {
        curmodule = (FStar_Pervasives_Native.Some l);
        curmonad = (uu___118_2206.curmonad);
        modules = (uu___118_2206.modules);
        scope_mods = (uu___118_2206.scope_mods);
        exported_ids = (uu___118_2206.exported_ids);
        trans_exported_ids = (uu___118_2206.trans_exported_ids);
        includes = (uu___118_2206.includes);
        sigaccum = (uu___118_2206.sigaccum);
        sigmap = (uu___118_2206.sigmap);
        iface = (uu___118_2206.iface);
        admitted_iface = (uu___118_2206.admitted_iface);
        expect_typ = (uu___118_2206.expect_typ);
        docs = (uu___118_2206.docs);
        remaining_iface_decls = (uu___118_2206.remaining_iface_decls);
        syntax_only = (uu___118_2206.syntax_only);
        ds_hooks = (uu___118_2206.ds_hooks)
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
      let uu____2227 =
        FStar_All.pipe_right env.remaining_iface_decls
          (FStar_List.tryFind
             (fun uu____2261 ->
                match uu____2261 with
                | (m, uu____2269) -> FStar_Ident.lid_equals l m)) in
      match uu____2227 with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (uu____2286, decls) ->
          FStar_Pervasives_Native.Some decls
let (set_iface_decls :
  env -> FStar_Ident.lident -> FStar_Parser_AST.decl Prims.list -> env) =
  fun env ->
    fun l ->
      fun ds ->
        let uu____2319 =
          FStar_List.partition
            (fun uu____2349 ->
               match uu____2349 with
               | (m, uu____2357) -> FStar_Ident.lid_equals l m)
            env.remaining_iface_decls in
        match uu____2319 with
        | (uu____2362, rest) ->
            let uu___119_2396 = env in
            {
              curmodule = (uu___119_2396.curmodule);
              curmonad = (uu___119_2396.curmonad);
              modules = (uu___119_2396.modules);
              scope_mods = (uu___119_2396.scope_mods);
              exported_ids = (uu___119_2396.exported_ids);
              trans_exported_ids = (uu___119_2396.trans_exported_ids);
              includes = (uu___119_2396.includes);
              sigaccum = (uu___119_2396.sigaccum);
              sigmap = (uu___119_2396.sigmap);
              iface = (uu___119_2396.iface);
              admitted_iface = (uu___119_2396.admitted_iface);
              expect_typ = (uu___119_2396.expect_typ);
              docs = (uu___119_2396.docs);
              remaining_iface_decls = ((l, ds) :: rest);
              syntax_only = (uu___119_2396.syntax_only);
              ds_hooks = (uu___119_2396.ds_hooks)
            }
let (qual : FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident) =
  FStar_Syntax_Util.qual_id
let (qualify : env -> FStar_Ident.ident -> FStar_Ident.lident) =
  fun env ->
    fun id1 ->
      match env.curmonad with
      | FStar_Pervasives_Native.None ->
          let uu____2423 = current_module env in qual uu____2423 id1
      | FStar_Pervasives_Native.Some monad ->
          let uu____2425 =
            let uu____2426 = current_module env in qual uu____2426 monad in
          FStar_Syntax_Util.mk_field_projector_name_from_ident uu____2425 id1
let (syntax_only : env -> Prims.bool) = fun env -> env.syntax_only
let (set_syntax_only : env -> Prims.bool -> env) =
  fun env ->
    fun b ->
      let uu___120_2442 = env in
      {
        curmodule = (uu___120_2442.curmodule);
        curmonad = (uu___120_2442.curmonad);
        modules = (uu___120_2442.modules);
        scope_mods = (uu___120_2442.scope_mods);
        exported_ids = (uu___120_2442.exported_ids);
        trans_exported_ids = (uu___120_2442.trans_exported_ids);
        includes = (uu___120_2442.includes);
        sigaccum = (uu___120_2442.sigaccum);
        sigmap = (uu___120_2442.sigmap);
        iface = (uu___120_2442.iface);
        admitted_iface = (uu___120_2442.admitted_iface);
        expect_typ = (uu___120_2442.expect_typ);
        docs = (uu___120_2442.docs);
        remaining_iface_decls = (uu___120_2442.remaining_iface_decls);
        syntax_only = b;
        ds_hooks = (uu___120_2442.ds_hooks)
      }
let (ds_hooks : env -> dsenv_hooks) = fun env -> env.ds_hooks
let (set_ds_hooks : env -> dsenv_hooks -> env) =
  fun env ->
    fun hooks ->
      let uu___121_2458 = env in
      {
        curmodule = (uu___121_2458.curmodule);
        curmonad = (uu___121_2458.curmonad);
        modules = (uu___121_2458.modules);
        scope_mods = (uu___121_2458.scope_mods);
        exported_ids = (uu___121_2458.exported_ids);
        trans_exported_ids = (uu___121_2458.trans_exported_ids);
        includes = (uu___121_2458.includes);
        sigaccum = (uu___121_2458.sigaccum);
        sigmap = (uu___121_2458.sigmap);
        iface = (uu___121_2458.iface);
        admitted_iface = (uu___121_2458.admitted_iface);
        expect_typ = (uu___121_2458.expect_typ);
        docs = (uu___121_2458.docs);
        remaining_iface_decls = (uu___121_2458.remaining_iface_decls);
        syntax_only = (uu___121_2458.syntax_only);
        ds_hooks = hooks
      }
let new_sigmap : 'Auu____2463 . unit -> 'Auu____2463 FStar_Util.smap =
  fun uu____2470 -> FStar_Util.smap_create (Prims.parse_int "100")
let (empty_env : unit -> env) =
  fun uu____2475 ->
    let uu____2476 = new_sigmap () in
    let uu____2481 = new_sigmap () in
    let uu____2486 = new_sigmap () in
    let uu____2497 = new_sigmap () in
    let uu____2508 = new_sigmap () in
    {
      curmodule = FStar_Pervasives_Native.None;
      curmonad = FStar_Pervasives_Native.None;
      modules = [];
      scope_mods = [];
      exported_ids = uu____2476;
      trans_exported_ids = uu____2481;
      includes = uu____2486;
      sigaccum = [];
      sigmap = uu____2497;
      iface = false;
      admitted_iface = false;
      expect_typ = false;
      docs = uu____2508;
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
      (fun uu____2544 ->
         match uu____2544 with
         | (m, uu____2550) ->
             FStar_Ident.lid_equals m FStar_Parser_Const.all_lid) env.modules
let (set_bv_range :
  FStar_Syntax_Syntax.bv -> FStar_Range.range -> FStar_Syntax_Syntax.bv) =
  fun bv ->
    fun r ->
      let id1 =
        let uu___122_2562 = bv.FStar_Syntax_Syntax.ppname in
        {
          FStar_Ident.idText = (uu___122_2562.FStar_Ident.idText);
          FStar_Ident.idRange = r
        } in
      let uu___123_2563 = bv in
      {
        FStar_Syntax_Syntax.ppname = id1;
        FStar_Syntax_Syntax.index = (uu___123_2563.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = (uu___123_2563.FStar_Syntax_Syntax.sort)
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
        (fun uu____2656 ->
           match uu____2656 with
           | (x, y, dd, dq) ->
               if id1.FStar_Ident.idText = x
               then
                 let uu____2679 =
                   let uu____2680 =
                     FStar_Ident.lid_of_path ["Prims"; y]
                       id1.FStar_Ident.idRange in
                   FStar_Syntax_Syntax.fvar uu____2680 dd dq in
                 FStar_Pervasives_Native.Some uu____2679
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
    match projectee with | Cont_ok _0 -> true | uu____2727 -> false
let __proj__Cont_ok__item___0 : 'a . 'a cont_t -> 'a =
  fun projectee -> match projectee with | Cont_ok _0 -> _0
let uu___is_Cont_fail : 'a . 'a cont_t -> Prims.bool =
  fun projectee ->
    match projectee with | Cont_fail -> true | uu____2760 -> false
let uu___is_Cont_ignore : 'a . 'a cont_t -> Prims.bool =
  fun projectee ->
    match projectee with | Cont_ignore -> true | uu____2777 -> false
let option_of_cont :
  'a .
    (unit -> 'a FStar_Pervasives_Native.option) ->
      'a cont_t -> 'a FStar_Pervasives_Native.option
  =
  fun k_ignore ->
    fun uu___85_2805 ->
      match uu___85_2805 with
      | Cont_ok a -> FStar_Pervasives_Native.Some a
      | Cont_fail -> FStar_Pervasives_Native.None
      | Cont_ignore -> k_ignore ()
let find_in_record :
  'Auu____2823 .
    FStar_Ident.ident Prims.list ->
      FStar_Ident.ident ->
        record_or_dc ->
          (record_or_dc -> 'Auu____2823 cont_t) -> 'Auu____2823 cont_t
  =
  fun ns ->
    fun id1 ->
      fun record ->
        fun cont ->
          let typename' =
            FStar_Ident.lid_of_ids
              (FStar_List.append ns [(record.typename).FStar_Ident.ident]) in
          let uu____2860 = FStar_Ident.lid_equals typename' record.typename in
          if uu____2860
          then
            let fname =
              FStar_Ident.lid_of_ids
                (FStar_List.append (record.typename).FStar_Ident.ns [id1]) in
            let find1 =
              FStar_Util.find_map record.fields
                (fun uu____2874 ->
                   match uu____2874 with
                   | (f, uu____2882) ->
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
  fun uu___86_2944 ->
    match uu___86_2944 with
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
              let rec aux uu___87_3015 =
                match uu___87_3015 with
                | [] -> find_in_module_default
                | modul::q ->
                    let mname = modul.FStar_Ident.str in
                    let not_shadowed =
                      let uu____3026 = get_exported_id_set env mname in
                      match uu____3026 with
                      | FStar_Pervasives_Native.None -> true
                      | FStar_Pervasives_Native.Some mex ->
                          let mexports =
                            let uu____3051 = mex eikind in
                            FStar_ST.op_Bang uu____3051 in
                          FStar_Util.set_mem idstr mexports in
                    let mincludes =
                      let uu____3239 =
                        FStar_Util.smap_try_find env.includes mname in
                      match uu____3239 with
                      | FStar_Pervasives_Native.None -> []
                      | FStar_Pervasives_Native.Some minc ->
                          FStar_ST.op_Bang minc in
                    let look_into =
                      if not_shadowed
                      then
                        let uu____3373 = qual modul id1 in
                        find_in_module uu____3373
                      else Cont_ignore in
                    (match look_into with
                     | Cont_ignore -> aux (FStar_List.append mincludes q)
                     | uu____3377 -> look_into) in
              aux [ns]
let (is_exported_id_field : exported_id_kind -> Prims.bool) =
  fun uu___88_3384 ->
    match uu___88_3384 with | Exported_id_field -> true | uu____3385 -> false
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
                  let check_local_binding_id uu___89_3506 =
                    match uu___89_3506 with
                    | (id', uu____3508, uu____3509) ->
                        id'.FStar_Ident.idText = id1.FStar_Ident.idText in
                  let check_rec_binding_id uu___90_3515 =
                    match uu___90_3515 with
                    | (id', uu____3517, uu____3518) ->
                        id'.FStar_Ident.idText = id1.FStar_Ident.idText in
                  let curmod_ns =
                    let uu____3522 = current_module env in
                    FStar_Ident.ids_of_lid uu____3522 in
                  let proc uu___91_3530 =
                    match uu___91_3530 with
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
                        let uu____3538 = FStar_Ident.lid_of_ids curmod_ns in
                        find_in_module_with_includes Exported_id_field
                          (fun lid ->
                             let id2 = lid.FStar_Ident.ident in
                             find_in_record lid.FStar_Ident.ns id2 r k_record)
                          Cont_ignore env uu____3538 id1
                    | uu____3543 -> Cont_ignore in
                  let rec aux uu___92_3553 =
                    match uu___92_3553 with
                    | a::q ->
                        let uu____3562 = proc a in
                        option_of_cont (fun uu____3566 -> aux q) uu____3562
                    | [] ->
                        let uu____3567 = lookup_default_id Cont_fail id1 in
                        option_of_cont
                          (fun uu____3571 -> FStar_Pervasives_Native.None)
                          uu____3567 in
                  aux env.scope_mods
let found_local_binding :
  'Auu____3580 'Auu____3581 .
    FStar_Range.range ->
      ('Auu____3580, FStar_Syntax_Syntax.bv, 'Auu____3581)
        FStar_Pervasives_Native.tuple3 ->
        (FStar_Syntax_Syntax.term, 'Auu____3581)
          FStar_Pervasives_Native.tuple2
  =
  fun r ->
    fun uu____3601 ->
      match uu____3601 with
      | (id', x, mut) -> let uu____3611 = bv_to_name x r in (uu____3611, mut)
let find_in_module :
  'Auu____3622 .
    env ->
      FStar_Ident.lident ->
        (FStar_Ident.lident ->
           (FStar_Syntax_Syntax.sigelt, Prims.bool)
             FStar_Pervasives_Native.tuple2 -> 'Auu____3622)
          -> 'Auu____3622 -> 'Auu____3622
  =
  fun env ->
    fun lid ->
      fun k_global_def ->
        fun k_not_found ->
          let uu____3661 =
            FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str in
          match uu____3661 with
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
      let uu____3701 = unmangleOpName id1 in
      match uu____3701 with
      | FStar_Pervasives_Native.Some f -> FStar_Pervasives_Native.Some f
      | uu____3727 ->
          try_lookup_id'' env id1 Exported_id_term_type
            (fun r ->
               let uu____3741 = found_local_binding id1.FStar_Ident.idRange r in
               Cont_ok uu____3741) (fun uu____3751 -> Cont_fail)
            (fun uu____3757 -> Cont_ignore)
            (fun i ->
               find_in_module env i
                 (fun uu____3772 -> fun uu____3773 -> Cont_fail) Cont_ignore)
            (fun uu____3788 -> fun uu____3789 -> Cont_fail)
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
            | FStar_Pervasives_Native.Some uu____3868 ->
                let lid = qualify env id1 in
                let uu____3870 =
                  FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str in
                (match uu____3870 with
                 | FStar_Pervasives_Native.Some r ->
                     let uu____3894 = k_global_def lid r in
                     FStar_Pervasives_Native.Some uu____3894
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None)
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None in
          match find_in_monad with
          | FStar_Pervasives_Native.Some v1 -> v1
          | FStar_Pervasives_Native.None ->
              let lid =
                let uu____3917 = current_module env in qual uu____3917 id1 in
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
        let rec aux uu___93_3980 =
          match uu___93_3980 with
          | [] ->
              let uu____3985 = module_is_defined env lid in
              if uu____3985
              then FStar_Pervasives_Native.Some lid
              else FStar_Pervasives_Native.None
          | (Open_module_or_namespace (ns, Open_namespace))::q when honor_ns
              ->
              let new_lid =
                let uu____3994 =
                  let uu____3995 = FStar_Ident.path_of_lid ns in
                  let uu____3998 = FStar_Ident.path_of_lid lid in
                  FStar_List.append uu____3995 uu____3998 in
                let uu____4001 = FStar_Ident.range_of_lid lid in
                FStar_Ident.lid_of_path uu____3994 uu____4001 in
              let uu____4002 = module_is_defined env new_lid in
              if uu____4002
              then FStar_Pervasives_Native.Some new_lid
              else aux q
          | (Module_abbrev (name, modul))::uu____4008 when
              (nslen = (Prims.parse_int "0")) &&
                (name.FStar_Ident.idText =
                   (lid.FStar_Ident.ident).FStar_Ident.idText)
              -> FStar_Pervasives_Native.Some modul
          | uu____4015::q -> aux q in
        aux env.scope_mods
let (fail_if_curmodule :
  env -> FStar_Ident.lident -> FStar_Ident.lident -> unit) =
  fun env ->
    fun ns_original ->
      fun ns_resolved ->
        let uu____4034 =
          let uu____4035 = current_module env in
          FStar_Ident.lid_equals ns_resolved uu____4035 in
        if uu____4034
        then
          let uu____4036 =
            FStar_Ident.lid_equals ns_resolved FStar_Parser_Const.prims_lid in
          (if uu____4036
           then ()
           else
             (let uu____4038 =
                let uu____4043 =
                  FStar_Util.format1
                    "Reference %s to current module is forbidden (see GitHub issue #451)"
                    ns_original.FStar_Ident.str in
                (FStar_Errors.Fatal_ForbiddenReferenceToCurrentModule,
                  uu____4043) in
              let uu____4044 = FStar_Ident.range_of_lid ns_original in
              FStar_Errors.raise_error uu____4038 uu____4044))
        else ()
let (fail_if_qualified_by_curmodule : env -> FStar_Ident.lident -> unit) =
  fun env ->
    fun lid ->
      match lid.FStar_Ident.ns with
      | [] -> ()
      | uu____4056 ->
          let modul_orig = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          let uu____4060 = resolve_module_name env modul_orig true in
          (match uu____4060 with
           | FStar_Pervasives_Native.Some modul_res ->
               fail_if_curmodule env modul_orig modul_res
           | uu____4064 -> ())
let (is_open : env -> FStar_Ident.lident -> open_kind -> Prims.bool) =
  fun env ->
    fun lid ->
      fun open_kind ->
        FStar_List.existsb
          (fun uu___94_4085 ->
             match uu___94_4085 with
             | Open_module_or_namespace (ns, k) ->
                 (k = open_kind) && (FStar_Ident.lid_equals lid ns)
             | uu____4088 -> false) env.scope_mods
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
                 let uu____4207 = aux rev_ns_prefix ns_last_id in
                 FStar_All.pipe_right uu____4207
                   (FStar_Util.map_option
                      (fun uu____4257 ->
                         match uu____4257 with
                         | (stripped_ids, rev_kept_ids) ->
                             (stripped_ids, (id1 :: rev_kept_ids))))) in
        let do_shorten env1 ids1 =
          match FStar_List.rev ids1 with
          | [] -> ([], [])
          | ns_last_id::ns_rev_prefix ->
              let uu____4327 = aux ns_rev_prefix ns_last_id in
              (match uu____4327 with
               | FStar_Pervasives_Native.None -> ([], ids1)
               | FStar_Pervasives_Native.Some (stripped_ids, rev_kept_ids) ->
                   (stripped_ids, (FStar_List.rev rev_kept_ids))) in
        if is_full_path
        then
          let uu____4388 =
            let uu____4391 = FStar_Ident.lid_of_ids ids in
            resolve_module_name env uu____4391 true in
          match uu____4388 with
          | FStar_Pervasives_Native.Some m when module_is_open env m ->
              (ids, [])
          | uu____4405 -> do_shorten env ids
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
                  | uu____4524::uu____4525 ->
                      let uu____4528 =
                        let uu____4531 =
                          let uu____4532 =
                            FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
                          let uu____4533 = FStar_Ident.range_of_lid lid in
                          FStar_Ident.set_lid_range uu____4532 uu____4533 in
                        resolve_module_name env uu____4531 true in
                      (match uu____4528 with
                       | FStar_Pervasives_Native.None ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some modul ->
                           let uu____4537 =
                             find_in_module_with_includes eikind f_module
                               Cont_fail env modul lid.FStar_Ident.ident in
                           option_of_cont
                             (fun uu____4541 -> FStar_Pervasives_Native.None)
                             uu____4537)
                  | [] ->
                      try_lookup_id'' env lid.FStar_Ident.ident eikind
                        k_local_binding k_rec_binding k_record f_module
                        l_default
let cont_of_option :
  'a . 'a cont_t -> 'a FStar_Pervasives_Native.option -> 'a cont_t =
  fun k_none ->
    fun uu___95_4564 ->
      match uu___95_4564 with
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
              let uu____4680 = k_global_def lid1 def in
              cont_of_option k uu____4680 in
            let f_module lid' =
              let k = Cont_ignore in
              find_in_module env lid' (k_global_def' k) k in
            let l_default k i = lookup_default_id env i (k_global_def' k) k in
            resolve_in_open_namespaces'' env lid Exported_id_term_type
              (fun l ->
                 let uu____4716 = k_local_binding l in
                 cont_of_option Cont_fail uu____4716)
              (fun r ->
                 let uu____4722 = k_rec_binding r in
                 cont_of_option Cont_fail uu____4722)
              (fun uu____4726 -> Cont_ignore) f_module l_default
let (fv_qual_of_se :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option)
  =
  fun se ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____4736, uu____4737, uu____4738, l, uu____4740, uu____4741) ->
        let qopt =
          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
            (fun uu___96_4752 ->
               match uu___96_4752 with
               | FStar_Syntax_Syntax.RecordConstructor (uu____4755, fs) ->
                   FStar_Pervasives_Native.Some
                     (FStar_Syntax_Syntax.Record_ctor (l, fs))
               | uu____4767 -> FStar_Pervasives_Native.None) in
        (match qopt with
         | FStar_Pervasives_Native.None ->
             FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor
         | x -> x)
    | FStar_Syntax_Syntax.Sig_declare_typ
        (uu____4773, uu____4774, uu____4775) -> FStar_Pervasives_Native.None
    | uu____4776 -> FStar_Pervasives_Native.None
let (lb_fv :
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Ident.lident -> FStar_Syntax_Syntax.fv)
  =
  fun lbs ->
    fun lid ->
      let uu____4791 =
        FStar_Util.find_map lbs
          (fun lb ->
             let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
             let uu____4799 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
             if uu____4799
             then FStar_Pervasives_Native.Some fv
             else FStar_Pervasives_Native.None) in
      FStar_All.pipe_right uu____4791 FStar_Util.must
let (ns_of_lid_equals :
  FStar_Ident.lident -> FStar_Ident.lident -> Prims.bool) =
  fun lid ->
    fun ns ->
      (let uu____4817 =
         let uu____4818 = FStar_Ident.ids_of_lid ns in
         FStar_List.length uu____4818 in
       (FStar_List.length lid.FStar_Ident.ns) = uu____4817) &&
        (let uu____4826 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
         FStar_Ident.lid_equals uu____4826 ns)
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
          let k_global_def source_lid uu___101_4868 =
            match uu___101_4868 with
            | (uu____4875, true) when exclude_interf ->
                FStar_Pervasives_Native.None
            | (se, uu____4877) ->
                (match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_inductive_typ uu____4880 ->
                     let uu____4897 =
                       let uu____4898 =
                         let uu____4907 =
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.Delta_constant
                             FStar_Pervasives_Native.None in
                         (uu____4907, false,
                           (se.FStar_Syntax_Syntax.sigattrs)) in
                       Term_name uu____4898 in
                     FStar_Pervasives_Native.Some uu____4897
                 | FStar_Syntax_Syntax.Sig_datacon uu____4910 ->
                     let uu____4925 =
                       let uu____4926 =
                         let uu____4935 =
                           let uu____4936 = fv_qual_of_se se in
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.Delta_constant uu____4936 in
                         (uu____4935, false,
                           (se.FStar_Syntax_Syntax.sigattrs)) in
                       Term_name uu____4926 in
                     FStar_Pervasives_Native.Some uu____4925
                 | FStar_Syntax_Syntax.Sig_let
                     ((uu____4941, lbs), uu____4943) ->
                     let fv = lb_fv lbs source_lid in
                     let uu____4959 =
                       let uu____4960 =
                         let uu____4969 =
                           FStar_Syntax_Syntax.fvar source_lid
                             fv.FStar_Syntax_Syntax.fv_delta
                             fv.FStar_Syntax_Syntax.fv_qual in
                         (uu____4969, false,
                           (se.FStar_Syntax_Syntax.sigattrs)) in
                       Term_name uu____4960 in
                     FStar_Pervasives_Native.Some uu____4959
                 | FStar_Syntax_Syntax.Sig_declare_typ
                     (lid1, uu____4973, uu____4974) ->
                     let quals = se.FStar_Syntax_Syntax.sigquals in
                     let uu____4978 =
                       any_val ||
                         (FStar_All.pipe_right quals
                            (FStar_Util.for_some
                               (fun uu___97_4982 ->
                                  match uu___97_4982 with
                                  | FStar_Syntax_Syntax.Assumption -> true
                                  | uu____4983 -> false))) in
                     if uu____4978
                     then
                       let lid2 =
                         let uu____4987 = FStar_Ident.range_of_lid source_lid in
                         FStar_Ident.set_lid_range lid1 uu____4987 in
                       let dd =
                         let uu____4989 =
                           (FStar_Syntax_Util.is_primop_lid lid2) ||
                             (FStar_All.pipe_right quals
                                (FStar_Util.for_some
                                   (fun uu___98_4994 ->
                                      match uu___98_4994 with
                                      | FStar_Syntax_Syntax.Projector
                                          uu____4995 -> true
                                      | FStar_Syntax_Syntax.Discriminator
                                          uu____5000 -> true
                                      | uu____5001 -> false))) in
                         if uu____4989
                         then FStar_Syntax_Syntax.Delta_equational
                         else FStar_Syntax_Syntax.Delta_constant in
                       let dd1 =
                         let uu____5004 =
                           FStar_All.pipe_right quals
                             (FStar_Util.for_some
                                (fun uu___99_5008 ->
                                   match uu___99_5008 with
                                   | FStar_Syntax_Syntax.Abstract -> true
                                   | uu____5009 -> false)) in
                         if uu____5004
                         then FStar_Syntax_Syntax.Delta_abstract dd
                         else dd in
                       let uu____5011 =
                         FStar_Util.find_map quals
                           (fun uu___100_5016 ->
                              match uu___100_5016 with
                              | FStar_Syntax_Syntax.Reflectable refl_monad ->
                                  FStar_Pervasives_Native.Some refl_monad
                              | uu____5020 -> FStar_Pervasives_Native.None) in
                       (match uu____5011 with
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
                        | uu____5031 ->
                            let uu____5034 =
                              let uu____5035 =
                                let uu____5044 =
                                  let uu____5045 = fv_qual_of_se se in
                                  FStar_Syntax_Syntax.fvar lid2 dd1
                                    uu____5045 in
                                (uu____5044, false,
                                  (se.FStar_Syntax_Syntax.sigattrs)) in
                              Term_name uu____5035 in
                            FStar_Pervasives_Native.Some uu____5034)
                     else FStar_Pervasives_Native.None
                 | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
                     let uu____5052 =
                       let uu____5053 =
                         let uu____5058 =
                           let uu____5059 =
                             FStar_Ident.range_of_lid source_lid in
                           FStar_Ident.set_lid_range
                             ne.FStar_Syntax_Syntax.mname uu____5059 in
                         (se, uu____5058) in
                       Eff_name uu____5053 in
                     FStar_Pervasives_Native.Some uu____5052
                 | FStar_Syntax_Syntax.Sig_new_effect ne ->
                     let uu____5061 =
                       let uu____5062 =
                         let uu____5067 =
                           let uu____5068 =
                             FStar_Ident.range_of_lid source_lid in
                           FStar_Ident.set_lid_range
                             ne.FStar_Syntax_Syntax.mname uu____5068 in
                         (se, uu____5067) in
                       Eff_name uu____5062 in
                     FStar_Pervasives_Native.Some uu____5061
                 | FStar_Syntax_Syntax.Sig_effect_abbrev uu____5069 ->
                     FStar_Pervasives_Native.Some (Eff_name (se, source_lid))
                 | FStar_Syntax_Syntax.Sig_splice (lids, t) ->
                     let uu____5088 =
                       let uu____5089 =
                         let uu____5098 =
                           FStar_Syntax_Syntax.fvar source_lid
                             (FStar_Syntax_Syntax.Delta_defined_at_level
                                (Prims.parse_int "1"))
                             FStar_Pervasives_Native.None in
                         (uu____5098, false, []) in
                       Term_name uu____5089 in
                     FStar_Pervasives_Native.Some uu____5088
                 | uu____5101 -> FStar_Pervasives_Native.None) in
          let k_local_binding r =
            let uu____5122 =
              let uu____5127 = FStar_Ident.range_of_lid lid in
              found_local_binding uu____5127 r in
            match uu____5122 with
            | (t, mut) ->
                FStar_Pervasives_Native.Some (Term_name (t, mut, [])) in
          let k_rec_binding uu____5147 =
            match uu____5147 with
            | (id1, l, dd) ->
                let uu____5159 =
                  let uu____5160 =
                    let uu____5169 =
                      let uu____5170 =
                        let uu____5171 = FStar_Ident.range_of_lid lid in
                        FStar_Ident.set_lid_range l uu____5171 in
                      FStar_Syntax_Syntax.fvar uu____5170 dd
                        FStar_Pervasives_Native.None in
                    (uu____5169, false, []) in
                  Term_name uu____5160 in
                FStar_Pervasives_Native.Some uu____5159 in
          let found_unmangled =
            match lid.FStar_Ident.ns with
            | [] ->
                let uu____5179 = unmangleOpName lid.FStar_Ident.ident in
                (match uu____5179 with
                 | FStar_Pervasives_Native.Some (t, mut) ->
                     FStar_Pervasives_Native.Some (Term_name (t, mut, []))
                 | uu____5196 -> FStar_Pervasives_Native.None)
            | uu____5203 -> FStar_Pervasives_Native.None in
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
        let uu____5238 = try_lookup_name true exclude_interf env lid in
        match uu____5238 with
        | FStar_Pervasives_Native.Some (Eff_name (o, l)) ->
            FStar_Pervasives_Native.Some (o, l)
        | uu____5253 -> FStar_Pervasives_Native.None
let (try_lookup_effect_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env ->
    fun l ->
      let uu____5272 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____5272 with
      | FStar_Pervasives_Native.Some (o, l1) ->
          FStar_Pervasives_Native.Some l1
      | uu____5287 -> FStar_Pervasives_Native.None
let (try_lookup_effect_name_and_attributes :
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident, FStar_Syntax_Syntax.cflags Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env ->
    fun l ->
      let uu____5312 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____5312 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____5328;
             FStar_Syntax_Syntax.sigquals = uu____5329;
             FStar_Syntax_Syntax.sigmeta = uu____5330;
             FStar_Syntax_Syntax.sigattrs = uu____5331;_},
           l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____5350;
             FStar_Syntax_Syntax.sigquals = uu____5351;
             FStar_Syntax_Syntax.sigmeta = uu____5352;
             FStar_Syntax_Syntax.sigattrs = uu____5353;_},
           l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (uu____5371, uu____5372, uu____5373, uu____5374, cattributes);
             FStar_Syntax_Syntax.sigrng = uu____5376;
             FStar_Syntax_Syntax.sigquals = uu____5377;
             FStar_Syntax_Syntax.sigmeta = uu____5378;
             FStar_Syntax_Syntax.sigattrs = uu____5379;_},
           l1)
          -> FStar_Pervasives_Native.Some (l1, cattributes)
      | uu____5401 -> FStar_Pervasives_Native.None
let (try_lookup_effect_defn :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.eff_decl FStar_Pervasives_Native.option)
  =
  fun env ->
    fun l ->
      let uu____5426 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____5426 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____5436;
             FStar_Syntax_Syntax.sigquals = uu____5437;
             FStar_Syntax_Syntax.sigmeta = uu____5438;
             FStar_Syntax_Syntax.sigattrs = uu____5439;_},
           uu____5440)
          -> FStar_Pervasives_Native.Some ne
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____5450;
             FStar_Syntax_Syntax.sigquals = uu____5451;
             FStar_Syntax_Syntax.sigmeta = uu____5452;
             FStar_Syntax_Syntax.sigattrs = uu____5453;_},
           uu____5454)
          -> FStar_Pervasives_Native.Some ne
      | uu____5463 -> FStar_Pervasives_Native.None
let (is_effect_name : env -> FStar_Ident.lident -> Prims.bool) =
  fun env ->
    fun lid ->
      let uu____5480 = try_lookup_effect_name env lid in
      match uu____5480 with
      | FStar_Pervasives_Native.None -> false
      | FStar_Pervasives_Native.Some uu____5483 -> true
let (try_lookup_root_effect_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env ->
    fun l ->
      let uu____5496 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____5496 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (l', uu____5506, uu____5507, uu____5508, uu____5509);
             FStar_Syntax_Syntax.sigrng = uu____5510;
             FStar_Syntax_Syntax.sigquals = uu____5511;
             FStar_Syntax_Syntax.sigmeta = uu____5512;
             FStar_Syntax_Syntax.sigattrs = uu____5513;_},
           uu____5514)
          ->
          let rec aux new_name =
            let uu____5535 =
              FStar_Util.smap_try_find (sigmap env) new_name.FStar_Ident.str in
            match uu____5535 with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (s, uu____5553) ->
                (match s.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
                     let uu____5561 =
                       let uu____5562 = FStar_Ident.range_of_lid l in
                       FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname
                         uu____5562 in
                     FStar_Pervasives_Native.Some uu____5561
                 | FStar_Syntax_Syntax.Sig_new_effect ne ->
                     let uu____5564 =
                       let uu____5565 = FStar_Ident.range_of_lid l in
                       FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname
                         uu____5565 in
                     FStar_Pervasives_Native.Some uu____5564
                 | FStar_Syntax_Syntax.Sig_effect_abbrev
                     (uu____5566, uu____5567, uu____5568, cmp, uu____5570) ->
                     let l'' = FStar_Syntax_Util.comp_effect_name cmp in
                     aux l''
                 | uu____5576 -> FStar_Pervasives_Native.None) in
          aux l'
      | FStar_Pervasives_Native.Some (uu____5577, l') ->
          FStar_Pervasives_Native.Some l'
      | uu____5583 -> FStar_Pervasives_Native.None
let (lookup_letbinding_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env ->
    fun lid ->
      let k_global_def lid1 uu___102_5620 =
        match uu___102_5620 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____5629, uu____5630, uu____5631);
             FStar_Syntax_Syntax.sigrng = uu____5632;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____5634;
             FStar_Syntax_Syntax.sigattrs = uu____5635;_},
           uu____5636) -> FStar_Pervasives_Native.Some quals
        | uu____5643 -> FStar_Pervasives_Native.None in
      let uu____5650 =
        resolve_in_open_namespaces' env lid
          (fun uu____5658 -> FStar_Pervasives_Native.None)
          (fun uu____5662 -> FStar_Pervasives_Native.None) k_global_def in
      match uu____5650 with
      | FStar_Pervasives_Native.Some quals -> quals
      | uu____5672 -> []
let (try_lookup_module :
  env ->
    FStar_Ident.path ->
      FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option)
  =
  fun env ->
    fun path ->
      let uu____5689 =
        FStar_List.tryFind
          (fun uu____5704 ->
             match uu____5704 with
             | (mlid, modul) ->
                 let uu____5711 = FStar_Ident.path_of_lid mlid in
                 uu____5711 = path) env.modules in
      match uu____5689 with
      | FStar_Pervasives_Native.Some (uu____5714, modul) ->
          FStar_Pervasives_Native.Some modul
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let (try_lookup_let :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env ->
    fun lid ->
      let k_global_def lid1 uu___103_5752 =
        match uu___103_5752 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               ((uu____5759, lbs), uu____5761);
             FStar_Syntax_Syntax.sigrng = uu____5762;
             FStar_Syntax_Syntax.sigquals = uu____5763;
             FStar_Syntax_Syntax.sigmeta = uu____5764;
             FStar_Syntax_Syntax.sigattrs = uu____5765;_},
           uu____5766) ->
            let fv = lb_fv lbs lid1 in
            let uu____5786 =
              FStar_Syntax_Syntax.fvar lid1 fv.FStar_Syntax_Syntax.fv_delta
                fv.FStar_Syntax_Syntax.fv_qual in
            FStar_Pervasives_Native.Some uu____5786
        | uu____5787 -> FStar_Pervasives_Native.None in
      resolve_in_open_namespaces' env lid
        (fun uu____5793 -> FStar_Pervasives_Native.None)
        (fun uu____5795 -> FStar_Pervasives_Native.None) k_global_def
let (try_lookup_definition :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env ->
    fun lid ->
      let k_global_def lid1 uu___104_5826 =
        match uu___104_5826 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               (lbs, uu____5836);
             FStar_Syntax_Syntax.sigrng = uu____5837;
             FStar_Syntax_Syntax.sigquals = uu____5838;
             FStar_Syntax_Syntax.sigmeta = uu____5839;
             FStar_Syntax_Syntax.sigattrs = uu____5840;_},
           uu____5841) ->
            FStar_Util.find_map (FStar_Pervasives_Native.snd lbs)
              (fun lb ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inr fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv lid1 ->
                     FStar_Pervasives_Native.Some
                       (lb.FStar_Syntax_Syntax.lbdef)
                 | uu____5864 -> FStar_Pervasives_Native.None)
        | uu____5871 -> FStar_Pervasives_Native.None in
      resolve_in_open_namespaces' env lid
        (fun uu____5881 -> FStar_Pervasives_Native.None)
        (fun uu____5885 -> FStar_Pervasives_Native.None) k_global_def
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
          let uu____5942 = try_lookup_name any_val exclude_interface env lid in
          match uu____5942 with
          | FStar_Pervasives_Native.Some (Term_name (e, mut, attrs)) ->
              FStar_Pervasives_Native.Some (e, mut, attrs)
          | uu____5972 -> FStar_Pervasives_Native.None
let (drop_attributes :
  (FStar_Syntax_Syntax.term, Prims.bool,
    FStar_Syntax_Syntax.attribute Prims.list) FStar_Pervasives_Native.tuple3
    FStar_Pervasives_Native.option ->
    (FStar_Syntax_Syntax.term, Prims.bool) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option)
  =
  fun x ->
    match x with
    | FStar_Pervasives_Native.Some (t, mut, uu____6028) ->
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
      let uu____6103 = try_lookup_lid_with_attributes env l in
      FStar_All.pipe_right uu____6103 drop_attributes
let (resolve_to_fully_qualified_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env ->
    fun l ->
      let uu____6142 = try_lookup_lid env l in
      match uu____6142 with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (e, uu____6156) ->
          let uu____6161 =
            let uu____6162 = FStar_Syntax_Subst.compress e in
            uu____6162.FStar_Syntax_Syntax.n in
          (match uu____6161 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               FStar_Pervasives_Native.Some
                 ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
           | uu____6168 -> FStar_Pervasives_Native.None)
let (shorten_lid' : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env ->
    fun lid ->
      let uu____6179 = shorten_module_path env lid.FStar_Ident.ns true in
      match uu____6179 with
      | (uu____6188, short) ->
          FStar_Ident.lid_of_ns_and_id short lid.FStar_Ident.ident
let (shorten_lid : env -> FStar_Ident.lid -> FStar_Ident.lid) =
  fun env ->
    fun lid ->
      match env.curmodule with
      | FStar_Pervasives_Native.None -> shorten_lid' env lid
      | uu____6208 ->
          let lid_without_ns =
            FStar_Ident.lid_of_ns_and_id [] lid.FStar_Ident.ident in
          let uu____6212 = resolve_to_fully_qualified_name env lid_without_ns in
          (match uu____6212 with
           | FStar_Pervasives_Native.Some lid' when
               lid'.FStar_Ident.str = lid.FStar_Ident.str -> lid_without_ns
           | uu____6216 -> shorten_lid' env lid)
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
        let uu___124_6250 = env in
        {
          curmodule = (uu___124_6250.curmodule);
          curmonad = (uu___124_6250.curmonad);
          modules = (uu___124_6250.modules);
          scope_mods = [];
          exported_ids = empty_exported_id_smap;
          trans_exported_ids = (uu___124_6250.trans_exported_ids);
          includes = empty_include_smap;
          sigaccum = (uu___124_6250.sigaccum);
          sigmap = (uu___124_6250.sigmap);
          iface = (uu___124_6250.iface);
          admitted_iface = (uu___124_6250.admitted_iface);
          expect_typ = (uu___124_6250.expect_typ);
          docs = (uu___124_6250.docs);
          remaining_iface_decls = (uu___124_6250.remaining_iface_decls);
          syntax_only = (uu___124_6250.syntax_only);
          ds_hooks = (uu___124_6250.ds_hooks)
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
      let uu____6273 = try_lookup_lid_with_attributes_no_resolve env l in
      FStar_All.pipe_right uu____6273 drop_attributes
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
      let k_global_def lid1 se =
        match se with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____6347, uu____6348, uu____6349);
             FStar_Syntax_Syntax.sigrng = uu____6350;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____6352;
             FStar_Syntax_Syntax.sigattrs = uu____6353;_},
           uu____6354) ->
            let uu____6359 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___105_6363 ->
                      match uu___105_6363 with
                      | FStar_Syntax_Syntax.Assumption -> true
                      | uu____6364 -> false)) in
            if uu____6359
            then
              let uu____6367 =
                FStar_Syntax_Syntax.lid_as_fv lid1
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None in
              FStar_Pervasives_Native.Some uu____6367
            else FStar_Pervasives_Native.None
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
               uu____6369;
             FStar_Syntax_Syntax.sigrng = uu____6370;
             FStar_Syntax_Syntax.sigquals = uu____6371;
             FStar_Syntax_Syntax.sigmeta = uu____6372;
             FStar_Syntax_Syntax.sigattrs = uu____6373;_},
           uu____6374) ->
            let qual1 = fv_qual_of_se (FStar_Pervasives_Native.fst se) in
            let uu____6396 =
              FStar_Syntax_Syntax.lid_as_fv lid1
                FStar_Syntax_Syntax.Delta_constant qual1 in
            FStar_Pervasives_Native.Some uu____6396
        | uu____6397 -> FStar_Pervasives_Native.None in
      resolve_in_open_namespaces' env lid
        (fun uu____6403 -> FStar_Pervasives_Native.None)
        (fun uu____6405 -> FStar_Pervasives_Native.None) k_global_def
let (find_all_datacons :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident Prims.list FStar_Pervasives_Native.option)
  =
  fun env ->
    fun lid ->
      let k_global_def lid1 uu___106_6438 =
        match uu___106_6438 with
        | ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_inductive_typ
               (uu____6447, uu____6448, uu____6449, uu____6450, datas,
                uu____6452);
             FStar_Syntax_Syntax.sigrng = uu____6453;
             FStar_Syntax_Syntax.sigquals = uu____6454;
             FStar_Syntax_Syntax.sigmeta = uu____6455;
             FStar_Syntax_Syntax.sigattrs = uu____6456;_},
           uu____6457) -> FStar_Pervasives_Native.Some datas
        | uu____6472 -> FStar_Pervasives_Native.None in
      resolve_in_open_namespaces' env lid
        (fun uu____6482 -> FStar_Pervasives_Native.None)
        (fun uu____6486 -> FStar_Pervasives_Native.None) k_global_def
let (record_cache_aux_with_filter :
  ((unit -> unit, unit -> unit, unit -> record_or_dc Prims.list,
     record_or_dc -> unit) FStar_Pervasives_Native.tuple4,
    unit -> unit) FStar_Pervasives_Native.tuple2)
  =
  let record_cache = FStar_Util.mk_ref [[]] in
  let push1 uu____6538 =
    let uu____6539 =
      let uu____6544 =
        let uu____6547 = FStar_ST.op_Bang record_cache in
        FStar_List.hd uu____6547 in
      let uu____6661 = FStar_ST.op_Bang record_cache in uu____6544 ::
        uu____6661 in
    FStar_ST.op_Colon_Equals record_cache uu____6539 in
  let pop1 uu____6887 =
    let uu____6888 =
      let uu____6893 = FStar_ST.op_Bang record_cache in
      FStar_List.tl uu____6893 in
    FStar_ST.op_Colon_Equals record_cache uu____6888 in
  let peek1 uu____7121 =
    let uu____7122 = FStar_ST.op_Bang record_cache in
    FStar_List.hd uu____7122 in
  let insert r =
    let uu____7242 =
      let uu____7247 = let uu____7250 = peek1 () in r :: uu____7250 in
      let uu____7253 =
        let uu____7258 = FStar_ST.op_Bang record_cache in
        FStar_List.tl uu____7258 in
      uu____7247 :: uu____7253 in
    FStar_ST.op_Colon_Equals record_cache uu____7242 in
  let filter1 uu____7486 =
    let rc = peek1 () in
    let filtered =
      FStar_List.filter (fun r -> Prims.op_Negation r.is_private_or_abstract)
        rc in
    let uu____7495 =
      let uu____7500 =
        let uu____7505 = FStar_ST.op_Bang record_cache in
        FStar_List.tl uu____7505 in
      filtered :: uu____7500 in
    FStar_ST.op_Colon_Equals record_cache uu____7495 in
  let aux = (push1, pop1, peek1, insert) in (aux, filter1)
let (record_cache_aux :
  (unit -> unit, unit -> unit, unit -> record_or_dc Prims.list,
    record_or_dc -> unit) FStar_Pervasives_Native.tuple4)
  =
  let uu____7812 = record_cache_aux_with_filter in
  match uu____7812 with | (aux, uu____7865) -> aux
let (filter_record_cache : unit -> unit) =
  let uu____7920 = record_cache_aux_with_filter in
  match uu____7920 with | (uu____7953, filter1) -> filter1
let (push_record_cache : unit -> unit) =
  let uu____8009 = record_cache_aux in
  match uu____8009 with
  | (push1, uu____8036, uu____8037, uu____8038) -> push1
let (pop_record_cache : unit -> unit) =
  let uu____8071 = record_cache_aux in
  match uu____8071 with | (uu____8097, pop1, uu____8099, uu____8100) -> pop1
let (peek_record_cache : unit -> record_or_dc Prims.list) =
  let uu____8135 = record_cache_aux in
  match uu____8135 with
  | (uu____8163, uu____8164, peek1, uu____8166) -> peek1
let (insert_record_cache : record_or_dc -> unit) =
  let uu____8199 = record_cache_aux in
  match uu____8199 with
  | (uu____8225, uu____8226, uu____8227, insert) -> insert
let (extract_record :
  env ->
    scope_mod Prims.list FStar_ST.ref -> FStar_Syntax_Syntax.sigelt -> unit)
  =
  fun e ->
    fun new_globs ->
      fun se ->
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_bundle (sigs, uu____8351) ->
            let is_record =
              FStar_Util.for_some
                (fun uu___107_8369 ->
                   match uu___107_8369 with
                   | FStar_Syntax_Syntax.RecordType uu____8370 -> true
                   | FStar_Syntax_Syntax.RecordConstructor uu____8379 -> true
                   | uu____8388 -> false) in
            let find_dc dc =
              FStar_All.pipe_right sigs
                (FStar_Util.find_opt
                   (fun uu___108_8412 ->
                      match uu___108_8412 with
                      | {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_datacon
                            (lid, uu____8414, uu____8415, uu____8416,
                             uu____8417, uu____8418);
                          FStar_Syntax_Syntax.sigrng = uu____8419;
                          FStar_Syntax_Syntax.sigquals = uu____8420;
                          FStar_Syntax_Syntax.sigmeta = uu____8421;
                          FStar_Syntax_Syntax.sigattrs = uu____8422;_} ->
                          FStar_Ident.lid_equals dc lid
                      | uu____8431 -> false)) in
            FStar_All.pipe_right sigs
              (FStar_List.iter
                 (fun uu___109_8466 ->
                    match uu___109_8466 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ
                          (typename, univs1, parms, uu____8470, uu____8471,
                           dc::[]);
                        FStar_Syntax_Syntax.sigrng = uu____8473;
                        FStar_Syntax_Syntax.sigquals = typename_quals;
                        FStar_Syntax_Syntax.sigmeta = uu____8475;
                        FStar_Syntax_Syntax.sigattrs = uu____8476;_} ->
                        let uu____8487 =
                          let uu____8488 = find_dc dc in
                          FStar_All.pipe_left FStar_Util.must uu____8488 in
                        (match uu____8487 with
                         | {
                             FStar_Syntax_Syntax.sigel =
                               FStar_Syntax_Syntax.Sig_datacon
                               (constrname, uu____8494, t, uu____8496,
                                uu____8497, uu____8498);
                             FStar_Syntax_Syntax.sigrng = uu____8499;
                             FStar_Syntax_Syntax.sigquals = uu____8500;
                             FStar_Syntax_Syntax.sigmeta = uu____8501;
                             FStar_Syntax_Syntax.sigattrs = uu____8502;_} ->
                             let uu____8511 =
                               FStar_Syntax_Util.arrow_formals t in
                             (match uu____8511 with
                              | (formals, uu____8525) ->
                                  let is_rec = is_record typename_quals in
                                  let formals' =
                                    FStar_All.pipe_right formals
                                      (FStar_List.collect
                                         (fun uu____8574 ->
                                            match uu____8574 with
                                            | (x, q) ->
                                                let uu____8587 =
                                                  (FStar_Syntax_Syntax.is_null_bv
                                                     x)
                                                    ||
                                                    (is_rec &&
                                                       (FStar_Syntax_Syntax.is_implicit
                                                          q)) in
                                                if uu____8587
                                                then []
                                                else [(x, q)])) in
                                  let fields' =
                                    FStar_All.pipe_right formals'
                                      (FStar_List.map
                                         (fun uu____8644 ->
                                            match uu____8644 with
                                            | (x, q) ->
                                                let uu____8657 =
                                                  if is_rec
                                                  then
                                                    FStar_Syntax_Util.unmangle_field_name
                                                      x.FStar_Syntax_Syntax.ppname
                                                  else
                                                    x.FStar_Syntax_Syntax.ppname in
                                                (uu____8657,
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
                                  ((let uu____8672 =
                                      let uu____8675 =
                                        FStar_ST.op_Bang new_globs in
                                      (Record_or_dc record) :: uu____8675 in
                                    FStar_ST.op_Colon_Equals new_globs
                                      uu____8672);
                                   (match () with
                                    | () ->
                                        ((let add_field uu____8896 =
                                            match uu____8896 with
                                            | (id1, uu____8904) ->
                                                let modul =
                                                  let uu____8910 =
                                                    FStar_Ident.lid_of_ids
                                                      constrname.FStar_Ident.ns in
                                                  uu____8910.FStar_Ident.str in
                                                let uu____8911 =
                                                  get_exported_id_set e modul in
                                                (match uu____8911 with
                                                 | FStar_Pervasives_Native.Some
                                                     my_ex ->
                                                     let my_exported_ids =
                                                       my_ex
                                                         Exported_id_field in
                                                     ((let uu____8969 =
                                                         let uu____8970 =
                                                           FStar_ST.op_Bang
                                                             my_exported_ids in
                                                         FStar_Util.set_add
                                                           id1.FStar_Ident.idText
                                                           uu____8970 in
                                                       FStar_ST.op_Colon_Equals
                                                         my_exported_ids
                                                         uu____8969);
                                                      (match () with
                                                       | () ->
                                                           let projname =
                                                             let uu____9172 =
                                                               let uu____9173
                                                                 =
                                                                 FStar_Syntax_Util.mk_field_projector_name_from_ident
                                                                   constrname
                                                                   id1 in
                                                               uu____9173.FStar_Ident.ident in
                                                             uu____9172.FStar_Ident.idText in
                                                           let uu____9175 =
                                                             let uu____9176 =
                                                               FStar_ST.op_Bang
                                                                 my_exported_ids in
                                                             FStar_Util.set_add
                                                               projname
                                                               uu____9176 in
                                                           FStar_ST.op_Colon_Equals
                                                             my_exported_ids
                                                             uu____9175))
                                                 | FStar_Pervasives_Native.None
                                                     -> ()) in
                                          FStar_List.iter add_field fields');
                                         (match () with
                                          | () -> insert_record_cache record)))))
                         | uu____9388 -> ())
                    | uu____9389 -> ()))
        | uu____9390 -> ()
let (try_lookup_record_or_dc_by_field_name :
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option) =
  fun env ->
    fun fieldname ->
      let find_in_cache fieldname1 =
        let uu____9411 =
          ((fieldname1.FStar_Ident.ns), (fieldname1.FStar_Ident.ident)) in
        match uu____9411 with
        | (ns, id1) ->
            let uu____9428 = peek_record_cache () in
            FStar_Util.find_map uu____9428
              (fun record ->
                 let uu____9434 =
                   find_in_record ns id1 record (fun r -> Cont_ok r) in
                 option_of_cont
                   (fun uu____9440 -> FStar_Pervasives_Native.None)
                   uu____9434) in
      resolve_in_open_namespaces'' env fieldname Exported_id_field
        (fun uu____9442 -> Cont_ignore) (fun uu____9444 -> Cont_ignore)
        (fun r -> Cont_ok r)
        (fun fn ->
           let uu____9450 = find_in_cache fn in
           cont_of_option Cont_ignore uu____9450)
        (fun k -> fun uu____9456 -> k)
let (try_lookup_record_by_field_name :
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option) =
  fun env ->
    fun fieldname ->
      let uu____9471 = try_lookup_record_or_dc_by_field_name env fieldname in
      match uu____9471 with
      | FStar_Pervasives_Native.Some r when r.is_record ->
          FStar_Pervasives_Native.Some r
      | uu____9477 -> FStar_Pervasives_Native.None
let (belongs_to_record :
  env -> FStar_Ident.lident -> record_or_dc -> Prims.bool) =
  fun env ->
    fun lid ->
      fun record ->
        let uu____9495 = try_lookup_record_by_field_name env lid in
        match uu____9495 with
        | FStar_Pervasives_Native.Some record' when
            let uu____9499 =
              let uu____9500 =
                FStar_Ident.path_of_ns (record.typename).FStar_Ident.ns in
              FStar_Ident.text_of_path uu____9500 in
            let uu____9501 =
              let uu____9502 =
                FStar_Ident.path_of_ns (record'.typename).FStar_Ident.ns in
              FStar_Ident.text_of_path uu____9502 in
            uu____9499 = uu____9501 ->
            let uu____9503 =
              find_in_record (record.typename).FStar_Ident.ns
                lid.FStar_Ident.ident record (fun uu____9507 -> Cont_ok ()) in
            (match uu____9503 with
             | Cont_ok uu____9508 -> true
             | uu____9509 -> false)
        | uu____9512 -> false
let (try_lookup_dc_by_field_name :
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident, Prims.bool) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option)
  =
  fun env ->
    fun fieldname ->
      let uu____9531 = try_lookup_record_or_dc_by_field_name env fieldname in
      match uu____9531 with
      | FStar_Pervasives_Native.Some r ->
          let uu____9541 =
            let uu____9546 =
              let uu____9547 =
                FStar_Ident.lid_of_ids
                  (FStar_List.append (r.typename).FStar_Ident.ns
                     [r.constrname]) in
              let uu____9548 = FStar_Ident.range_of_lid fieldname in
              FStar_Ident.set_lid_range uu____9547 uu____9548 in
            (uu____9546, (r.is_record)) in
          FStar_Pervasives_Native.Some uu____9541
      | uu____9553 -> FStar_Pervasives_Native.None
let (string_set_ref_new : unit -> Prims.string FStar_Util.set FStar_ST.ref) =
  fun uu____9603 ->
    let uu____9604 = FStar_Util.new_set FStar_Util.compare in
    FStar_Util.mk_ref uu____9604
let (exported_id_set_new :
  unit -> exported_id_kind -> Prims.string FStar_Util.set FStar_ST.ref) =
  fun uu____9655 ->
    let term_type_set = string_set_ref_new () in
    let field_set = string_set_ref_new () in
    fun uu___110_9666 ->
      match uu___110_9666 with
      | Exported_id_term_type -> term_type_set
      | Exported_id_field -> field_set
let (unique :
  Prims.bool -> Prims.bool -> env -> FStar_Ident.lident -> Prims.bool) =
  fun any_val ->
    fun exclude_interface ->
      fun env ->
        fun lid ->
          let filter_scope_mods uu___111_9766 =
            match uu___111_9766 with
            | Rec_binding uu____9767 -> true
            | uu____9768 -> false in
          let this_env =
            let uu___125_9770 = env in
            let uu____9771 =
              FStar_List.filter filter_scope_mods env.scope_mods in
            {
              curmodule = (uu___125_9770.curmodule);
              curmonad = (uu___125_9770.curmonad);
              modules = (uu___125_9770.modules);
              scope_mods = uu____9771;
              exported_ids = empty_exported_id_smap;
              trans_exported_ids = (uu___125_9770.trans_exported_ids);
              includes = empty_include_smap;
              sigaccum = (uu___125_9770.sigaccum);
              sigmap = (uu___125_9770.sigmap);
              iface = (uu___125_9770.iface);
              admitted_iface = (uu___125_9770.admitted_iface);
              expect_typ = (uu___125_9770.expect_typ);
              docs = (uu___125_9770.docs);
              remaining_iface_decls = (uu___125_9770.remaining_iface_decls);
              syntax_only = (uu___125_9770.syntax_only);
              ds_hooks = (uu___125_9770.ds_hooks)
            } in
          let uu____9774 =
            try_lookup_lid' any_val exclude_interface this_env lid in
          match uu____9774 with
          | FStar_Pervasives_Native.None -> true
          | FStar_Pervasives_Native.Some uu____9793 -> false
let (push_scope_mod : env -> scope_mod -> env) =
  fun env ->
    fun scope_mod ->
      let uu___126_9820 = env in
      {
        curmodule = (uu___126_9820.curmodule);
        curmonad = (uu___126_9820.curmonad);
        modules = (uu___126_9820.modules);
        scope_mods = (scope_mod :: (env.scope_mods));
        exported_ids = (uu___126_9820.exported_ids);
        trans_exported_ids = (uu___126_9820.trans_exported_ids);
        includes = (uu___126_9820.includes);
        sigaccum = (uu___126_9820.sigaccum);
        sigmap = (uu___126_9820.sigmap);
        iface = (uu___126_9820.iface);
        admitted_iface = (uu___126_9820.admitted_iface);
        expect_typ = (uu___126_9820.expect_typ);
        docs = (uu___126_9820.docs);
        remaining_iface_decls = (uu___126_9820.remaining_iface_decls);
        syntax_only = (uu___126_9820.syntax_only);
        ds_hooks = (uu___126_9820.ds_hooks)
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
        let uu____9885 =
          (unique false true env l) || (FStar_Options.interactive ()) in
        if uu____9885
        then push_scope_mod env (Rec_binding (x, l, dd))
        else
          (let uu____9887 = FStar_Ident.range_of_lid l in
           FStar_Errors.raise_error
             (FStar_Errors.Fatal_DuplicateTopLevelNames,
               (Prims.strcat "Duplicate top-level names " l.FStar_Ident.str))
             uu____9887)
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env ->
    fun s ->
      let err l =
        let sopt = FStar_Util.smap_try_find (sigmap env) l.FStar_Ident.str in
        let r =
          match sopt with
          | FStar_Pervasives_Native.Some (se, uu____9917) ->
              let uu____9922 =
                FStar_Util.find_opt (FStar_Ident.lid_equals l)
                  (FStar_Syntax_Util.lids_of_sigelt se) in
              (match uu____9922 with
               | FStar_Pervasives_Native.Some l1 ->
                   let uu____9926 = FStar_Ident.range_of_lid l1 in
                   FStar_All.pipe_left FStar_Range.string_of_range uu____9926
               | FStar_Pervasives_Native.None -> "<unknown>")
          | FStar_Pervasives_Native.None -> "<unknown>" in
        let uu____9931 =
          let uu____9936 =
            let uu____9937 = FStar_Ident.text_of_lid l in
            FStar_Util.format2
              "Duplicate top-level names [%s]; previously declared at %s"
              uu____9937 r in
          (FStar_Errors.Fatal_DuplicateTopLevelNames, uu____9936) in
        let uu____9938 = FStar_Ident.range_of_lid l in
        FStar_Errors.raise_error uu____9931 uu____9938 in
      let globals = FStar_Util.mk_ref env.scope_mods in
      let env1 =
        let uu____9947 =
          match s.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let uu____9956 -> (false, true)
          | FStar_Syntax_Syntax.Sig_bundle uu____9963 -> (false, true)
          | uu____9972 -> (false, false) in
        match uu____9947 with
        | (any_val, exclude_interface) ->
            let lids = FStar_Syntax_Util.lids_of_sigelt s in
            let uu____9978 =
              FStar_Util.find_map lids
                (fun l ->
                   let uu____9984 =
                     let uu____9985 = unique any_val exclude_interface env l in
                     Prims.op_Negation uu____9985 in
                   if uu____9984
                   then FStar_Pervasives_Native.Some l
                   else FStar_Pervasives_Native.None) in
            (match uu____9978 with
             | FStar_Pervasives_Native.Some l -> err l
             | uu____9990 ->
                 (extract_record env globals s;
                  (let uu___127_10064 = env in
                   {
                     curmodule = (uu___127_10064.curmodule);
                     curmonad = (uu___127_10064.curmonad);
                     modules = (uu___127_10064.modules);
                     scope_mods = (uu___127_10064.scope_mods);
                     exported_ids = (uu___127_10064.exported_ids);
                     trans_exported_ids = (uu___127_10064.trans_exported_ids);
                     includes = (uu___127_10064.includes);
                     sigaccum = (s :: (env.sigaccum));
                     sigmap = (uu___127_10064.sigmap);
                     iface = (uu___127_10064.iface);
                     admitted_iface = (uu___127_10064.admitted_iface);
                     expect_typ = (uu___127_10064.expect_typ);
                     docs = (uu___127_10064.docs);
                     remaining_iface_decls =
                       (uu___127_10064.remaining_iface_decls);
                     syntax_only = (uu___127_10064.syntax_only);
                     ds_hooks = (uu___127_10064.ds_hooks)
                   }))) in
      let env2 =
        let uu___128_10066 = env1 in
        let uu____10067 = FStar_ST.op_Bang globals in
        {
          curmodule = (uu___128_10066.curmodule);
          curmonad = (uu___128_10066.curmonad);
          modules = (uu___128_10066.modules);
          scope_mods = uu____10067;
          exported_ids = (uu___128_10066.exported_ids);
          trans_exported_ids = (uu___128_10066.trans_exported_ids);
          includes = (uu___128_10066.includes);
          sigaccum = (uu___128_10066.sigaccum);
          sigmap = (uu___128_10066.sigmap);
          iface = (uu___128_10066.iface);
          admitted_iface = (uu___128_10066.admitted_iface);
          expect_typ = (uu___128_10066.expect_typ);
          docs = (uu___128_10066.docs);
          remaining_iface_decls = (uu___128_10066.remaining_iface_decls);
          syntax_only = (uu___128_10066.syntax_only);
          ds_hooks = (uu___128_10066.ds_hooks)
        } in
      let uu____10173 =
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_bundle (ses, uu____10199) ->
            let uu____10208 =
              FStar_List.map
                (fun se -> ((FStar_Syntax_Util.lids_of_sigelt se), se)) ses in
            (env2, uu____10208)
        | uu____10235 -> (env2, [((FStar_Syntax_Util.lids_of_sigelt s), s)]) in
      match uu____10173 with
      | (env3, lss) ->
          (FStar_All.pipe_right lss
             (FStar_List.iter
                (fun uu____10294 ->
                   match uu____10294 with
                   | (lids, se) ->
                       FStar_All.pipe_right lids
                         (FStar_List.iter
                            (fun lid ->
                               (let uu____10316 =
                                  let uu____10319 = FStar_ST.op_Bang globals in
                                  (Top_level_def (lid.FStar_Ident.ident)) ::
                                    uu____10319 in
                                FStar_ST.op_Colon_Equals globals uu____10316);
                               (match () with
                                | () ->
                                    let modul =
                                      let uu____10529 =
                                        FStar_Ident.lid_of_ids
                                          lid.FStar_Ident.ns in
                                      uu____10529.FStar_Ident.str in
                                    ((let uu____10531 =
                                        get_exported_id_set env3 modul in
                                      match uu____10531 with
                                      | FStar_Pervasives_Native.Some f ->
                                          let my_exported_ids =
                                            f Exported_id_term_type in
                                          let uu____10588 =
                                            let uu____10589 =
                                              FStar_ST.op_Bang
                                                my_exported_ids in
                                            FStar_Util.set_add
                                              (lid.FStar_Ident.ident).FStar_Ident.idText
                                              uu____10589 in
                                          FStar_ST.op_Colon_Equals
                                            my_exported_ids uu____10588
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
              let uu___129_10801 = env3 in
              let uu____10802 = FStar_ST.op_Bang globals in
              {
                curmodule = (uu___129_10801.curmodule);
                curmonad = (uu___129_10801.curmonad);
                modules = (uu___129_10801.modules);
                scope_mods = uu____10802;
                exported_ids = (uu___129_10801.exported_ids);
                trans_exported_ids = (uu___129_10801.trans_exported_ids);
                includes = (uu___129_10801.includes);
                sigaccum = (uu___129_10801.sigaccum);
                sigmap = (uu___129_10801.sigmap);
                iface = (uu___129_10801.iface);
                admitted_iface = (uu___129_10801.admitted_iface);
                expect_typ = (uu___129_10801.expect_typ);
                docs = (uu___129_10801.docs);
                remaining_iface_decls =
                  (uu___129_10801.remaining_iface_decls);
                syntax_only = (uu___129_10801.syntax_only);
                ds_hooks = (uu___129_10801.ds_hooks)
              } in
            env4))
let (push_namespace : env -> FStar_Ident.lident -> env) =
  fun env ->
    fun ns ->
      let uu____10918 =
        let uu____10923 = resolve_module_name env ns false in
        match uu____10923 with
        | FStar_Pervasives_Native.None ->
            let modules = env.modules in
            let uu____10937 =
              FStar_All.pipe_right modules
                (FStar_Util.for_some
                   (fun uu____10953 ->
                      match uu____10953 with
                      | (m, uu____10959) ->
                          let uu____10960 =
                            let uu____10961 = FStar_Ident.text_of_lid m in
                            Prims.strcat uu____10961 "." in
                          let uu____10962 =
                            let uu____10963 = FStar_Ident.text_of_lid ns in
                            Prims.strcat uu____10963 "." in
                          FStar_Util.starts_with uu____10960 uu____10962)) in
            if uu____10937
            then (ns, Open_namespace)
            else
              (let uu____10969 =
                 let uu____10974 =
                   let uu____10975 = FStar_Ident.text_of_lid ns in
                   FStar_Util.format1 "Namespace %s cannot be found"
                     uu____10975 in
                 (FStar_Errors.Fatal_NameSpaceNotFound, uu____10974) in
               let uu____10976 = FStar_Ident.range_of_lid ns in
               FStar_Errors.raise_error uu____10969 uu____10976)
        | FStar_Pervasives_Native.Some ns' ->
            (fail_if_curmodule env ns ns'; (ns', Open_module)) in
      match uu____10918 with
      | (ns', kd) ->
          ((env.ds_hooks).ds_push_open_hook env (ns', kd);
           push_scope_mod env (Open_module_or_namespace (ns', kd)))
let (push_include : env -> FStar_Ident.lident -> env) =
  fun env ->
    fun ns ->
      let ns0 = ns in
      let uu____10997 = resolve_module_name env ns false in
      match uu____10997 with
      | FStar_Pervasives_Native.Some ns1 ->
          ((env.ds_hooks).ds_push_include_hook env ns1;
           fail_if_curmodule env ns0 ns1;
           (let env1 =
              push_scope_mod env
                (Open_module_or_namespace (ns1, Open_module)) in
            let curmod =
              let uu____11005 = current_module env1 in
              uu____11005.FStar_Ident.str in
            (let uu____11007 = FStar_Util.smap_try_find env1.includes curmod in
             match uu____11007 with
             | FStar_Pervasives_Native.None -> ()
             | FStar_Pervasives_Native.Some incl ->
                 let uu____11031 =
                   let uu____11034 = FStar_ST.op_Bang incl in ns1 ::
                     uu____11034 in
                 FStar_ST.op_Colon_Equals incl uu____11031);
            (match () with
             | () ->
                 let uu____11243 =
                   get_trans_exported_id_set env1 ns1.FStar_Ident.str in
                 (match uu____11243 with
                  | FStar_Pervasives_Native.Some ns_trans_exports ->
                      ((let uu____11263 =
                          let uu____11282 = get_exported_id_set env1 curmod in
                          let uu____11290 =
                            get_trans_exported_id_set env1 curmod in
                          (uu____11282, uu____11290) in
                        match uu____11263 with
                        | (FStar_Pervasives_Native.Some cur_exports,
                           FStar_Pervasives_Native.Some cur_trans_exports) ->
                            let update_exports k =
                              let ns_ex =
                                let uu____11355 = ns_trans_exports k in
                                FStar_ST.op_Bang uu____11355 in
                              let ex = cur_exports k in
                              (let uu____11579 =
                                 let uu____11580 = FStar_ST.op_Bang ex in
                                 FStar_Util.set_difference uu____11580 ns_ex in
                               FStar_ST.op_Colon_Equals ex uu____11579);
                              (match () with
                               | () ->
                                   let trans_ex = cur_trans_exports k in
                                   let uu____11820 =
                                     let uu____11821 =
                                       FStar_ST.op_Bang trans_ex in
                                     FStar_Util.set_union uu____11821 ns_ex in
                                   FStar_ST.op_Colon_Equals trans_ex
                                     uu____11820) in
                            FStar_List.iter update_exports
                              all_exported_id_kinds
                        | uu____12022 -> ());
                       (match () with | () -> env1))
                  | FStar_Pervasives_Native.None ->
                      let uu____12046 =
                        let uu____12051 =
                          FStar_Util.format1
                            "include: Module %s was not prepared"
                            ns1.FStar_Ident.str in
                        (FStar_Errors.Fatal_IncludeModuleNotPrepared,
                          uu____12051) in
                      let uu____12052 = FStar_Ident.range_of_lid ns1 in
                      FStar_Errors.raise_error uu____12046 uu____12052))))
      | uu____12053 ->
          let uu____12056 =
            let uu____12061 =
              FStar_Util.format1 "include: Module %s cannot be found"
                ns.FStar_Ident.str in
            (FStar_Errors.Fatal_ModuleNotFound, uu____12061) in
          let uu____12062 = FStar_Ident.range_of_lid ns in
          FStar_Errors.raise_error uu____12056 uu____12062
let (push_module_abbrev :
  env -> FStar_Ident.ident -> FStar_Ident.lident -> env) =
  fun env ->
    fun x ->
      fun l ->
        let uu____12078 = module_is_defined env l in
        if uu____12078
        then
          (fail_if_curmodule env l l;
           (env.ds_hooks).ds_push_module_abbrev_hook env x l;
           push_scope_mod env (Module_abbrev (x, l)))
        else
          (let uu____12082 =
             let uu____12087 =
               let uu____12088 = FStar_Ident.text_of_lid l in
               FStar_Util.format1 "Module %s cannot be found" uu____12088 in
             (FStar_Errors.Fatal_ModuleNotFound, uu____12087) in
           let uu____12089 = FStar_Ident.range_of_lid l in
           FStar_Errors.raise_error uu____12082 uu____12089)
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
            ((let uu____12111 =
                FStar_Util.smap_try_find env.docs l.FStar_Ident.str in
              match uu____12111 with
              | FStar_Pervasives_Native.None -> ()
              | FStar_Pervasives_Native.Some old_doc ->
                  let uu____12115 = FStar_Ident.range_of_lid l in
                  let uu____12116 =
                    let uu____12121 =
                      let uu____12122 = FStar_Ident.string_of_lid l in
                      let uu____12123 =
                        FStar_Parser_AST.string_of_fsdoc old_doc in
                      let uu____12124 = FStar_Parser_AST.string_of_fsdoc doc1 in
                      FStar_Util.format3
                        "Overwriting doc of %s; old doc was [%s]; new doc are [%s]"
                        uu____12122 uu____12123 uu____12124 in
                    (FStar_Errors.Warning_DocOverwrite, uu____12121) in
                  FStar_Errors.log_issue uu____12115 uu____12116);
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
                      let uu____12164 =
                        FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption) in
                      Prims.op_Negation uu____12164 ->
                      let uu____12167 =
                        FStar_Util.smap_try_find (sigmap env)
                          l.FStar_Ident.str in
                      (match uu____12167 with
                       | FStar_Pervasives_Native.Some
                           ({
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_let uu____12180;
                              FStar_Syntax_Syntax.sigrng = uu____12181;
                              FStar_Syntax_Syntax.sigquals = uu____12182;
                              FStar_Syntax_Syntax.sigmeta = uu____12183;
                              FStar_Syntax_Syntax.sigattrs = uu____12184;_},
                            uu____12185)
                           -> lids
                       | FStar_Pervasives_Native.Some
                           ({
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_inductive_typ
                                uu____12200;
                              FStar_Syntax_Syntax.sigrng = uu____12201;
                              FStar_Syntax_Syntax.sigquals = uu____12202;
                              FStar_Syntax_Syntax.sigmeta = uu____12203;
                              FStar_Syntax_Syntax.sigattrs = uu____12204;_},
                            uu____12205)
                           -> lids
                       | uu____12230 ->
                           ((let uu____12238 =
                               let uu____12239 = FStar_Options.interactive () in
                               Prims.op_Negation uu____12239 in
                             if uu____12238
                             then
                               let uu____12240 = FStar_Ident.range_of_lid l in
                               let uu____12241 =
                                 let uu____12246 =
                                   let uu____12247 =
                                     FStar_Ident.string_of_lid l in
                                   FStar_Util.format1
                                     "Admitting %s without a definition"
                                     uu____12247 in
                                 (FStar_Errors.Warning_AdmitWithoutDefinition,
                                   uu____12246) in
                               FStar_Errors.log_issue uu____12240 uu____12241
                             else ());
                            (let quals = FStar_Syntax_Syntax.Assumption ::
                               (se.FStar_Syntax_Syntax.sigquals) in
                             FStar_Util.smap_add (sigmap env)
                               l.FStar_Ident.str
                               ((let uu___130_12258 = se in
                                 {
                                   FStar_Syntax_Syntax.sigel =
                                     (uu___130_12258.FStar_Syntax_Syntax.sigel);
                                   FStar_Syntax_Syntax.sigrng =
                                     (uu___130_12258.FStar_Syntax_Syntax.sigrng);
                                   FStar_Syntax_Syntax.sigquals = quals;
                                   FStar_Syntax_Syntax.sigmeta =
                                     (uu___130_12258.FStar_Syntax_Syntax.sigmeta);
                                   FStar_Syntax_Syntax.sigattrs =
                                     (uu___130_12258.FStar_Syntax_Syntax.sigattrs)
                                 }), false);
                             l
                             ::
                             lids)))
                  | uu____12259 -> lids) []) in
      let uu___131_12260 = m in
      let uu____12261 =
        FStar_All.pipe_right m.FStar_Syntax_Syntax.declarations
          (FStar_List.map
             (fun s ->
                match s.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_declare_typ
                    (lid, uu____12271, uu____12272) when
                    FStar_List.existsb
                      (fun l -> FStar_Ident.lid_equals l lid)
                      admitted_sig_lids
                    ->
                    let uu___132_12275 = s in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___132_12275.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___132_12275.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals =
                        (FStar_Syntax_Syntax.Assumption ::
                        (s.FStar_Syntax_Syntax.sigquals));
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___132_12275.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___132_12275.FStar_Syntax_Syntax.sigattrs)
                    }
                | uu____12276 -> s)) in
      {
        FStar_Syntax_Syntax.name = (uu___131_12260.FStar_Syntax_Syntax.name);
        FStar_Syntax_Syntax.declarations = uu____12261;
        FStar_Syntax_Syntax.exports =
          (uu___131_12260.FStar_Syntax_Syntax.exports);
        FStar_Syntax_Syntax.is_interface =
          (uu___131_12260.FStar_Syntax_Syntax.is_interface)
      }
let (finish : env -> FStar_Syntax_Syntax.modul -> env) =
  fun env ->
    fun modul ->
      FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations
        (FStar_List.iter
           (fun se ->
              let quals = se.FStar_Syntax_Syntax.sigquals in
              match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_bundle (ses, uu____12297) ->
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
                                (lid, uu____12317, uu____12318, uu____12319,
                                 uu____12320, uu____12321)
                                ->
                                FStar_Util.smap_remove (sigmap env)
                                  lid.FStar_Ident.str
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (lid, univ_names, binders, typ, uu____12334,
                                 uu____12335)
                                ->
                                (FStar_Util.smap_remove (sigmap env)
                                   lid.FStar_Ident.str;
                                 if
                                   Prims.op_Negation
                                     (FStar_List.contains
                                        FStar_Syntax_Syntax.Private quals)
                                 then
                                   (let sigel =
                                      let uu____12350 =
                                        let uu____12357 =
                                          let uu____12360 =
                                            FStar_Ident.range_of_lid lid in
                                          let uu____12361 =
                                            let uu____12368 =
                                              let uu____12369 =
                                                let uu____12382 =
                                                  FStar_Syntax_Syntax.mk_Total
                                                    typ in
                                                (binders, uu____12382) in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____12369 in
                                            FStar_Syntax_Syntax.mk
                                              uu____12368 in
                                          uu____12361
                                            FStar_Pervasives_Native.None
                                            uu____12360 in
                                        (lid, univ_names, uu____12357) in
                                      FStar_Syntax_Syntax.Sig_declare_typ
                                        uu____12350 in
                                    let se2 =
                                      let uu___133_12389 = se1 in
                                      {
                                        FStar_Syntax_Syntax.sigel = sigel;
                                        FStar_Syntax_Syntax.sigrng =
                                          (uu___133_12389.FStar_Syntax_Syntax.sigrng);
                                        FStar_Syntax_Syntax.sigquals =
                                          (FStar_Syntax_Syntax.Assumption ::
                                          quals);
                                        FStar_Syntax_Syntax.sigmeta =
                                          (uu___133_12389.FStar_Syntax_Syntax.sigmeta);
                                        FStar_Syntax_Syntax.sigattrs =
                                          (uu___133_12389.FStar_Syntax_Syntax.sigattrs)
                                      } in
                                    FStar_Util.smap_add (sigmap env)
                                      lid.FStar_Ident.str (se2, false))
                                 else ())
                            | uu____12395 -> ()))
                  else ()
              | FStar_Syntax_Syntax.Sig_declare_typ
                  (lid, uu____12398, uu____12399) ->
                  if FStar_List.contains FStar_Syntax_Syntax.Private quals
                  then
                    FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str
                  else ()
              | FStar_Syntax_Syntax.Sig_let ((uu____12405, lbs), uu____12407)
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
                             let uu____12428 =
                               let uu____12429 =
                                 let uu____12430 =
                                   let uu____12433 =
                                     FStar_Util.right
                                       lb.FStar_Syntax_Syntax.lbname in
                                   uu____12433.FStar_Syntax_Syntax.fv_name in
                                 uu____12430.FStar_Syntax_Syntax.v in
                               uu____12429.FStar_Ident.str in
                             FStar_Util.smap_remove (sigmap env) uu____12428))
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
                               let uu____12447 =
                                 let uu____12450 =
                                   FStar_Util.right
                                     lb.FStar_Syntax_Syntax.lbname in
                                 uu____12450.FStar_Syntax_Syntax.fv_name in
                               uu____12447.FStar_Syntax_Syntax.v in
                             let quals1 = FStar_Syntax_Syntax.Assumption ::
                               quals in
                             let decl =
                               let uu___134_12455 = se in
                               {
                                 FStar_Syntax_Syntax.sigel =
                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                      (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                        (lb.FStar_Syntax_Syntax.lbtyp)));
                                 FStar_Syntax_Syntax.sigrng =
                                   (uu___134_12455.FStar_Syntax_Syntax.sigrng);
                                 FStar_Syntax_Syntax.sigquals = quals1;
                                 FStar_Syntax_Syntax.sigmeta =
                                   (uu___134_12455.FStar_Syntax_Syntax.sigmeta);
                                 FStar_Syntax_Syntax.sigattrs =
                                   (uu___134_12455.FStar_Syntax_Syntax.sigattrs)
                               } in
                             FStar_Util.smap_add (sigmap env)
                               lid.FStar_Ident.str (decl, false)))
                   else ())
              | uu____12465 -> ()));
      (let curmod =
         let uu____12467 = current_module env in uu____12467.FStar_Ident.str in
       (let uu____12469 =
          let uu____12488 = get_exported_id_set env curmod in
          let uu____12496 = get_trans_exported_id_set env curmod in
          (uu____12488, uu____12496) in
        match uu____12469 with
        | (FStar_Pervasives_Native.Some cur_ex, FStar_Pervasives_Native.Some
           cur_trans_ex) ->
            let update_exports eikind =
              let cur_ex_set =
                let uu____12561 = cur_ex eikind in
                FStar_ST.op_Bang uu____12561 in
              let cur_trans_ex_set_ref = cur_trans_ex eikind in
              let uu____12784 =
                let uu____12785 = FStar_ST.op_Bang cur_trans_ex_set_ref in
                FStar_Util.set_union cur_ex_set uu____12785 in
              FStar_ST.op_Colon_Equals cur_trans_ex_set_ref uu____12784 in
            FStar_List.iter update_exports all_exported_id_kinds
        | uu____12986 -> ());
       (match () with
        | () ->
            (filter_record_cache ();
             (match () with
              | () ->
                  let uu___135_13006 = env in
                  {
                    curmodule = FStar_Pervasives_Native.None;
                    curmonad = (uu___135_13006.curmonad);
                    modules = (((modul.FStar_Syntax_Syntax.name), modul) ::
                      (env.modules));
                    scope_mods = [];
                    exported_ids = (uu___135_13006.exported_ids);
                    trans_exported_ids = (uu___135_13006.trans_exported_ids);
                    includes = (uu___135_13006.includes);
                    sigaccum = [];
                    sigmap = (uu___135_13006.sigmap);
                    iface = (uu___135_13006.iface);
                    admitted_iface = (uu___135_13006.admitted_iface);
                    expect_typ = (uu___135_13006.expect_typ);
                    docs = (uu___135_13006.docs);
                    remaining_iface_decls =
                      (uu___135_13006.remaining_iface_decls);
                    syntax_only = (uu___135_13006.syntax_only);
                    ds_hooks = (uu___135_13006.ds_hooks)
                  }))))
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref []
let (push : env -> env) =
  fun env ->
    push_record_cache ();
    (let uu____13059 =
       let uu____13062 = FStar_ST.op_Bang stack in env :: uu____13062 in
     FStar_ST.op_Colon_Equals stack uu____13059);
    (let uu___136_13131 = env in
     let uu____13132 = FStar_Util.smap_copy (sigmap env) in
     let uu____13143 = FStar_Util.smap_copy env.docs in
     {
       curmodule = (uu___136_13131.curmodule);
       curmonad = (uu___136_13131.curmonad);
       modules = (uu___136_13131.modules);
       scope_mods = (uu___136_13131.scope_mods);
       exported_ids = (uu___136_13131.exported_ids);
       trans_exported_ids = (uu___136_13131.trans_exported_ids);
       includes = (uu___136_13131.includes);
       sigaccum = (uu___136_13131.sigaccum);
       sigmap = uu____13132;
       iface = (uu___136_13131.iface);
       admitted_iface = (uu___136_13131.admitted_iface);
       expect_typ = (uu___136_13131.expect_typ);
       docs = uu____13143;
       remaining_iface_decls = (uu___136_13131.remaining_iface_decls);
       syntax_only = (uu___136_13131.syntax_only);
       ds_hooks = (uu___136_13131.ds_hooks)
     })
let (pop : unit -> env) =
  fun uu____13150 ->
    let uu____13151 = FStar_ST.op_Bang stack in
    match uu____13151 with
    | env::tl1 ->
        (pop_record_cache (); FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____13226 -> failwith "Impossible: Too many pops"
let (export_interface : FStar_Ident.lident -> env -> env) =
  fun m ->
    fun env ->
      let sigelt_in_m se =
        match FStar_Syntax_Util.lids_of_sigelt se with
        | l::uu____13246 -> l.FStar_Ident.nsstr = m.FStar_Ident.str
        | uu____13249 -> false in
      let sm = sigmap env in
      let env1 = pop () in
      let keys = FStar_Util.smap_keys sm in
      let sm' = sigmap env1 in
      FStar_All.pipe_right keys
        (FStar_List.iter
           (fun k ->
              let uu____13283 = FStar_Util.smap_try_find sm' k in
              match uu____13283 with
              | FStar_Pervasives_Native.Some (se, true) when sigelt_in_m se
                  ->
                  (FStar_Util.smap_remove sm' k;
                   (let se1 =
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_declare_typ (l, u, t) ->
                          let uu___137_13308 = se in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (uu___137_13308.FStar_Syntax_Syntax.sigel);
                            FStar_Syntax_Syntax.sigrng =
                              (uu___137_13308.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (FStar_Syntax_Syntax.Assumption ::
                              (se.FStar_Syntax_Syntax.sigquals));
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___137_13308.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___137_13308.FStar_Syntax_Syntax.sigattrs)
                          }
                      | uu____13309 -> se in
                    FStar_Util.smap_add sm' k (se1, false)))
              | uu____13314 -> ()));
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
      let uu____13337 = finish env modul1 in (uu____13337, modul1)
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
      let uu____13497 =
        let uu____13500 = e Exported_id_term_type in
        FStar_ST.op_Bang uu____13500 in
      FStar_Util.set_elements uu____13497 in
    let fields =
      let uu____13688 =
        let uu____13691 = e Exported_id_field in FStar_ST.op_Bang uu____13691 in
      FStar_Util.set_elements uu____13688 in
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
          let uu____13940 =
            FStar_Util.as_set e1.exported_id_terms FStar_Util.compare in
          FStar_Util.mk_ref uu____13940 in
        let fields =
          let uu____13950 =
            FStar_Util.as_set e1.exported_id_fields FStar_Util.compare in
          FStar_Util.mk_ref uu____13950 in
        (fun uu___112_13955 ->
           match uu___112_13955 with
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
  'Auu____14158 .
    'Auu____14158 Prims.list FStar_Pervasives_Native.option ->
      'Auu____14158 Prims.list FStar_ST.ref
  =
  fun uu___113_14171 ->
    match uu___113_14171 with
    | FStar_Pervasives_Native.None -> FStar_Util.mk_ref []
    | FStar_Pervasives_Native.Some l -> FStar_Util.mk_ref l
let (inclusion_info : env -> FStar_Ident.lident -> module_inclusion_info) =
  fun env ->
    fun l ->
      let mname = FStar_Ident.string_of_lid l in
      let as_ids_opt m =
        let uu____14212 = FStar_Util.smap_try_find m mname in
        FStar_Util.map_opt uu____14212 as_exported_ids in
      let uu____14218 = as_ids_opt env.exported_ids in
      let uu____14221 = as_ids_opt env.trans_exported_ids in
      let uu____14224 =
        let uu____14229 = FStar_Util.smap_try_find env.includes mname in
        FStar_Util.map_opt uu____14229 (fun r -> FStar_ST.op_Bang r) in
      {
        mii_exported_ids = uu____14218;
        mii_trans_exported_ids = uu____14221;
        mii_includes = uu____14224
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
                let uu____14426 = FStar_Ident.text_of_lid mname in
                FStar_Util.strcat uu____14426 ".fst" in
              let auto_open =
                FStar_Parser_Dep.hard_coded_dependencies filename in
              let auto_open1 =
                let convert_kind uu___114_14446 =
                  match uu___114_14446 with
                  | FStar_Parser_Dep.Open_namespace -> Open_namespace
                  | FStar_Parser_Dep.Open_module -> Open_module in
                FStar_List.map
                  (fun uu____14458 ->
                     match uu____14458 with
                     | (lid, kind) -> (lid, (convert_kind kind))) auto_open in
              let namespace_of_module =
                if
                  (FStar_List.length mname.FStar_Ident.ns) >
                    (Prims.parse_int "0")
                then
                  let uu____14482 =
                    let uu____14487 =
                      FStar_Ident.lid_of_ids mname.FStar_Ident.ns in
                    (uu____14487, Open_namespace) in
                  [uu____14482]
                else [] in
              let auto_open2 =
                FStar_List.append namespace_of_module
                  (FStar_List.rev auto_open1) in
              (let uu____14517 = as_exported_id_set mii.mii_exported_ids in
               FStar_Util.smap_add env1.exported_ids mname.FStar_Ident.str
                 uu____14517);
              (match () with
               | () ->
                   ((let uu____14592 =
                       as_exported_id_set mii.mii_trans_exported_ids in
                     FStar_Util.smap_add env1.trans_exported_ids
                       mname.FStar_Ident.str uu____14592);
                    (match () with
                     | () ->
                         ((let uu____14667 = as_includes mii.mii_includes in
                           FStar_Util.smap_add env1.includes
                             mname.FStar_Ident.str uu____14667);
                          (match () with
                           | () ->
                               let env' =
                                 let uu___138_14747 = env1 in
                                 let uu____14748 =
                                   FStar_List.map
                                     (fun x -> Open_module_or_namespace x)
                                     auto_open2 in
                                 {
                                   curmodule =
                                     (FStar_Pervasives_Native.Some mname);
                                   curmonad = (uu___138_14747.curmonad);
                                   modules = (uu___138_14747.modules);
                                   scope_mods = uu____14748;
                                   exported_ids =
                                     (uu___138_14747.exported_ids);
                                   trans_exported_ids =
                                     (uu___138_14747.trans_exported_ids);
                                   includes = (uu___138_14747.includes);
                                   sigaccum = (uu___138_14747.sigaccum);
                                   sigmap = (env1.sigmap);
                                   iface = intf;
                                   admitted_iface = admitted;
                                   expect_typ = (uu___138_14747.expect_typ);
                                   docs = (uu___138_14747.docs);
                                   remaining_iface_decls =
                                     (uu___138_14747.remaining_iface_decls);
                                   syntax_only = (uu___138_14747.syntax_only);
                                   ds_hooks = (uu___138_14747.ds_hooks)
                                 } in
                               (FStar_List.iter
                                  (fun op ->
                                     (env1.ds_hooks).ds_push_open_hook env'
                                       op) (FStar_List.rev auto_open2);
                                env')))))) in
            let uu____14760 =
              FStar_All.pipe_right env.modules
                (FStar_Util.find_opt
                   (fun uu____14786 ->
                      match uu____14786 with
                      | (l, uu____14792) -> FStar_Ident.lid_equals l mname)) in
            match uu____14760 with
            | FStar_Pervasives_Native.None ->
                let uu____14801 = prep env in (uu____14801, false)
            | FStar_Pervasives_Native.Some (uu____14802, m) ->
                ((let uu____14809 =
                    (let uu____14812 = FStar_Options.interactive () in
                     Prims.op_Negation uu____14812) &&
                      ((Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)
                         || intf) in
                  if uu____14809
                  then
                    let uu____14813 =
                      let uu____14818 =
                        FStar_Util.format1
                          "Duplicate module or interface name: %s"
                          mname.FStar_Ident.str in
                      (FStar_Errors.Fatal_DuplicateModuleOrInterface,
                        uu____14818) in
                    let uu____14819 = FStar_Ident.range_of_lid mname in
                    FStar_Errors.raise_error uu____14813 uu____14819
                  else ());
                 (let uu____14821 =
                    let uu____14822 = push env in prep uu____14822 in
                  (uu____14821, true)))
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
          let uu___139_14834 = env in
          {
            curmodule = (uu___139_14834.curmodule);
            curmonad = (FStar_Pervasives_Native.Some mname);
            modules = (uu___139_14834.modules);
            scope_mods = (uu___139_14834.scope_mods);
            exported_ids = (uu___139_14834.exported_ids);
            trans_exported_ids = (uu___139_14834.trans_exported_ids);
            includes = (uu___139_14834.includes);
            sigaccum = (uu___139_14834.sigaccum);
            sigmap = (uu___139_14834.sigmap);
            iface = (uu___139_14834.iface);
            admitted_iface = (uu___139_14834.admitted_iface);
            expect_typ = (uu___139_14834.expect_typ);
            docs = (uu___139_14834.docs);
            remaining_iface_decls = (uu___139_14834.remaining_iface_decls);
            syntax_only = (uu___139_14834.syntax_only);
            ds_hooks = (uu___139_14834.ds_hooks)
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
        let uu____14868 = lookup1 lid in
        match uu____14868 with
        | FStar_Pervasives_Native.None ->
            let opened_modules =
              FStar_List.map
                (fun uu____14881 ->
                   match uu____14881 with
                   | (lid1, uu____14887) -> FStar_Ident.text_of_lid lid1)
                env.modules in
            let msg =
              let uu____14889 = FStar_Ident.text_of_lid lid in
              FStar_Util.format1 "Identifier not found: [%s]" uu____14889 in
            let msg1 =
              if
                (FStar_List.length lid.FStar_Ident.ns) =
                  (Prims.parse_int "0")
              then msg
              else
                (let modul =
                   let uu____14893 =
                     FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
                   let uu____14894 = FStar_Ident.range_of_lid lid in
                   FStar_Ident.set_lid_range uu____14893 uu____14894 in
                 let uu____14895 = resolve_module_name env modul true in
                 match uu____14895 with
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
            let uu____14904 = FStar_Ident.range_of_lid lid in
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_IdentifierNotFound, msg1) uu____14904
        | FStar_Pervasives_Native.Some r -> r
let fail_or2 :
  'a .
    (FStar_Ident.ident -> 'a FStar_Pervasives_Native.option) ->
      FStar_Ident.ident -> 'a
  =
  fun lookup1 ->
    fun id1 ->
      let uu____14932 = lookup1 id1 in
      match uu____14932 with
      | FStar_Pervasives_Native.None ->
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_IdentifierNotFound,
              (Prims.strcat "Identifier not found ["
                 (Prims.strcat id1.FStar_Ident.idText "]")))
            id1.FStar_Ident.idRange
      | FStar_Pervasives_Native.Some r -> r
let (mk_copy : env -> env) =
  fun en ->
    let uu___140_14941 = en in
    let uu____14942 = FStar_Util.smap_copy en.exported_ids in
    let uu____14947 = FStar_Util.smap_copy en.trans_exported_ids in
    let uu____14952 = FStar_Util.smap_copy en.sigmap in
    let uu____14963 = FStar_Util.smap_copy en.docs in
    {
      curmodule = (uu___140_14941.curmodule);
      curmonad = (uu___140_14941.curmonad);
      modules = (uu___140_14941.modules);
      scope_mods = (uu___140_14941.scope_mods);
      exported_ids = uu____14942;
      trans_exported_ids = uu____14947;
      includes = (uu___140_14941.includes);
      sigaccum = (uu___140_14941.sigaccum);
      sigmap = uu____14952;
      iface = (uu___140_14941.iface);
      admitted_iface = (uu___140_14941.admitted_iface);
      expect_typ = (uu___140_14941.expect_typ);
      docs = uu____14963;
      remaining_iface_decls = (uu___140_14941.remaining_iface_decls);
      syntax_only = (uu___140_14941.syntax_only);
      ds_hooks = (uu___140_14941.ds_hooks)
    }