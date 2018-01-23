open Prims
type local_binding =
  (FStar_Ident.ident,FStar_Syntax_Syntax.bv,Prims.bool)
    FStar_Pervasives_Native.tuple3[@@deriving show]
type rec_binding =
  (FStar_Ident.ident,FStar_Ident.lid,FStar_Syntax_Syntax.delta_depth)
    FStar_Pervasives_Native.tuple3[@@deriving show]
type module_abbrev =
  (FStar_Ident.ident,FStar_Ident.lident) FStar_Pervasives_Native.tuple2
[@@deriving show]
type open_kind =
  | Open_module
  | Open_namespace[@@deriving show]
let uu___is_Open_module: open_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | Open_module  -> true | uu____20 -> false
let uu___is_Open_namespace: open_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | Open_namespace  -> true | uu____24 -> false
type open_module_or_namespace =
  (FStar_Ident.lident,open_kind) FStar_Pervasives_Native.tuple2[@@deriving
                                                                 show]
type record_or_dc =
  {
  typename: FStar_Ident.lident;
  constrname: FStar_Ident.ident;
  parms: FStar_Syntax_Syntax.binders;
  fields:
    (FStar_Ident.ident,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple2 Prims.list;
  is_private_or_abstract: Prims.bool;
  is_record: Prims.bool;}[@@deriving show]
let __proj__Mkrecord_or_dc__item__typename:
  record_or_dc -> FStar_Ident.lident =
  fun projectee  ->
    match projectee with
    | { typename = __fname__typename; constrname = __fname__constrname;
        parms = __fname__parms; fields = __fname__fields;
        is_private_or_abstract = __fname__is_private_or_abstract;
        is_record = __fname__is_record;_} -> __fname__typename
let __proj__Mkrecord_or_dc__item__constrname:
  record_or_dc -> FStar_Ident.ident =
  fun projectee  ->
    match projectee with
    | { typename = __fname__typename; constrname = __fname__constrname;
        parms = __fname__parms; fields = __fname__fields;
        is_private_or_abstract = __fname__is_private_or_abstract;
        is_record = __fname__is_record;_} -> __fname__constrname
let __proj__Mkrecord_or_dc__item__parms:
  record_or_dc -> FStar_Syntax_Syntax.binders =
  fun projectee  ->
    match projectee with
    | { typename = __fname__typename; constrname = __fname__constrname;
        parms = __fname__parms; fields = __fname__fields;
        is_private_or_abstract = __fname__is_private_or_abstract;
        is_record = __fname__is_record;_} -> __fname__parms
let __proj__Mkrecord_or_dc__item__fields:
  record_or_dc ->
    (FStar_Ident.ident,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun projectee  ->
    match projectee with
    | { typename = __fname__typename; constrname = __fname__constrname;
        parms = __fname__parms; fields = __fname__fields;
        is_private_or_abstract = __fname__is_private_or_abstract;
        is_record = __fname__is_record;_} -> __fname__fields
let __proj__Mkrecord_or_dc__item__is_private_or_abstract:
  record_or_dc -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { typename = __fname__typename; constrname = __fname__constrname;
        parms = __fname__parms; fields = __fname__fields;
        is_private_or_abstract = __fname__is_private_or_abstract;
        is_record = __fname__is_record;_} -> __fname__is_private_or_abstract
let __proj__Mkrecord_or_dc__item__is_record: record_or_dc -> Prims.bool =
  fun projectee  ->
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
  | Record_or_dc of record_or_dc[@@deriving show]
let uu___is_Local_binding: scope_mod -> Prims.bool =
  fun projectee  ->
    match projectee with | Local_binding _0 -> true | uu____189 -> false
let __proj__Local_binding__item___0: scope_mod -> local_binding =
  fun projectee  -> match projectee with | Local_binding _0 -> _0
let uu___is_Rec_binding: scope_mod -> Prims.bool =
  fun projectee  ->
    match projectee with | Rec_binding _0 -> true | uu____201 -> false
let __proj__Rec_binding__item___0: scope_mod -> rec_binding =
  fun projectee  -> match projectee with | Rec_binding _0 -> _0
let uu___is_Module_abbrev: scope_mod -> Prims.bool =
  fun projectee  ->
    match projectee with | Module_abbrev _0 -> true | uu____213 -> false
let __proj__Module_abbrev__item___0: scope_mod -> module_abbrev =
  fun projectee  -> match projectee with | Module_abbrev _0 -> _0
let uu___is_Open_module_or_namespace: scope_mod -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Open_module_or_namespace _0 -> true
    | uu____225 -> false
let __proj__Open_module_or_namespace__item___0:
  scope_mod -> open_module_or_namespace =
  fun projectee  -> match projectee with | Open_module_or_namespace _0 -> _0
let uu___is_Top_level_def: scope_mod -> Prims.bool =
  fun projectee  ->
    match projectee with | Top_level_def _0 -> true | uu____237 -> false
let __proj__Top_level_def__item___0: scope_mod -> FStar_Ident.ident =
  fun projectee  -> match projectee with | Top_level_def _0 -> _0
let uu___is_Record_or_dc: scope_mod -> Prims.bool =
  fun projectee  ->
    match projectee with | Record_or_dc _0 -> true | uu____249 -> false
let __proj__Record_or_dc__item___0: scope_mod -> record_or_dc =
  fun projectee  -> match projectee with | Record_or_dc _0 -> _0
type string_set = Prims.string FStar_Util.set[@@deriving show]
type exported_id_kind =
  | Exported_id_term_type
  | Exported_id_field[@@deriving show]
let uu___is_Exported_id_term_type: exported_id_kind -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Exported_id_term_type  -> true
    | uu____262 -> false
let uu___is_Exported_id_field: exported_id_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | Exported_id_field  -> true | uu____266 -> false
type exported_id_set = exported_id_kind -> string_set FStar_ST.ref[@@deriving
                                                                    show]
type env =
  {
  curmodule: FStar_Ident.lident FStar_Pervasives_Native.option;
  curmonad: FStar_Ident.ident FStar_Pervasives_Native.option;
  modules:
    (FStar_Ident.lident,FStar_Syntax_Syntax.modul)
      FStar_Pervasives_Native.tuple2 Prims.list;
  scope_mods: scope_mod Prims.list;
  exported_ids: exported_id_set FStar_Util.smap;
  trans_exported_ids: exported_id_set FStar_Util.smap;
  includes: FStar_Ident.lident Prims.list FStar_ST.ref FStar_Util.smap;
  sigaccum: FStar_Syntax_Syntax.sigelts;
  sigmap:
    (FStar_Syntax_Syntax.sigelt,Prims.bool) FStar_Pervasives_Native.tuple2
      FStar_Util.smap;
  iface: Prims.bool;
  admitted_iface: Prims.bool;
  expect_typ: Prims.bool;
  docs: FStar_Parser_AST.fsdoc FStar_Util.smap;
  remaining_iface_decls:
    (FStar_Ident.lident,FStar_Parser_AST.decl Prims.list)
      FStar_Pervasives_Native.tuple2 Prims.list;
  syntax_only: Prims.bool;
  ds_hooks: dsenv_hooks;}[@@deriving show]
and dsenv_hooks =
  {
  ds_push_open_hook: env -> open_module_or_namespace -> Prims.unit;
  ds_push_include_hook: env -> FStar_Ident.lident -> Prims.unit;
  ds_push_module_abbrev_hook:
    env -> FStar_Ident.ident -> FStar_Ident.lident -> Prims.unit;}[@@deriving
                                                                    show]
let __proj__Mkenv__item__curmodule:
  env -> FStar_Ident.lident FStar_Pervasives_Native.option =
  fun projectee  ->
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
let __proj__Mkenv__item__curmonad:
  env -> FStar_Ident.ident FStar_Pervasives_Native.option =
  fun projectee  ->
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
let __proj__Mkenv__item__modules:
  env ->
    (FStar_Ident.lident,FStar_Syntax_Syntax.modul)
      FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun projectee  ->
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
let __proj__Mkenv__item__scope_mods: env -> scope_mod Prims.list =
  fun projectee  ->
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
let __proj__Mkenv__item__exported_ids: env -> exported_id_set FStar_Util.smap
  =
  fun projectee  ->
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
let __proj__Mkenv__item__trans_exported_ids:
  env -> exported_id_set FStar_Util.smap =
  fun projectee  ->
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
let __proj__Mkenv__item__includes:
  env -> FStar_Ident.lident Prims.list FStar_ST.ref FStar_Util.smap =
  fun projectee  ->
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
let __proj__Mkenv__item__sigaccum: env -> FStar_Syntax_Syntax.sigelts =
  fun projectee  ->
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
let __proj__Mkenv__item__sigmap:
  env ->
    (FStar_Syntax_Syntax.sigelt,Prims.bool) FStar_Pervasives_Native.tuple2
      FStar_Util.smap
  =
  fun projectee  ->
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
let __proj__Mkenv__item__iface: env -> Prims.bool =
  fun projectee  ->
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
let __proj__Mkenv__item__admitted_iface: env -> Prims.bool =
  fun projectee  ->
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
let __proj__Mkenv__item__expect_typ: env -> Prims.bool =
  fun projectee  ->
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
let __proj__Mkenv__item__docs: env -> FStar_Parser_AST.fsdoc FStar_Util.smap
  =
  fun projectee  ->
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
let __proj__Mkenv__item__remaining_iface_decls:
  env ->
    (FStar_Ident.lident,FStar_Parser_AST.decl Prims.list)
      FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun projectee  ->
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
let __proj__Mkenv__item__syntax_only: env -> Prims.bool =
  fun projectee  ->
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
let __proj__Mkenv__item__ds_hooks: env -> dsenv_hooks =
  fun projectee  ->
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
let __proj__Mkdsenv_hooks__item__ds_push_open_hook:
  dsenv_hooks -> env -> open_module_or_namespace -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { ds_push_open_hook = __fname__ds_push_open_hook;
        ds_push_include_hook = __fname__ds_push_include_hook;
        ds_push_module_abbrev_hook = __fname__ds_push_module_abbrev_hook;_}
        -> __fname__ds_push_open_hook
let __proj__Mkdsenv_hooks__item__ds_push_include_hook:
  dsenv_hooks -> env -> FStar_Ident.lident -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { ds_push_open_hook = __fname__ds_push_open_hook;
        ds_push_include_hook = __fname__ds_push_include_hook;
        ds_push_module_abbrev_hook = __fname__ds_push_module_abbrev_hook;_}
        -> __fname__ds_push_include_hook
let __proj__Mkdsenv_hooks__item__ds_push_module_abbrev_hook:
  dsenv_hooks -> env -> FStar_Ident.ident -> FStar_Ident.lident -> Prims.unit
  =
  fun projectee  ->
    match projectee with
    | { ds_push_open_hook = __fname__ds_push_open_hook;
        ds_push_include_hook = __fname__ds_push_include_hook;
        ds_push_module_abbrev_hook = __fname__ds_push_module_abbrev_hook;_}
        -> __fname__ds_push_module_abbrev_hook
type 'a withenv = env -> ('a,env) FStar_Pervasives_Native.tuple2[@@deriving
                                                                  show]
let default_ds_hooks: dsenv_hooks =
  {
    ds_push_open_hook = (fun uu____1535  -> fun uu____1536  -> ());
    ds_push_include_hook = (fun uu____1539  -> fun uu____1540  -> ());
    ds_push_module_abbrev_hook =
      (fun uu____1544  -> fun uu____1545  -> fun uu____1546  -> ())
  }
type foundname =
  | Term_name of (FStar_Syntax_Syntax.typ,Prims.bool)
  FStar_Pervasives_Native.tuple2
  | Eff_name of (FStar_Syntax_Syntax.sigelt,FStar_Ident.lident)
  FStar_Pervasives_Native.tuple2[@@deriving show]
let uu___is_Term_name: foundname -> Prims.bool =
  fun projectee  ->
    match projectee with | Term_name _0 -> true | uu____1571 -> false
let __proj__Term_name__item___0:
  foundname ->
    (FStar_Syntax_Syntax.typ,Prims.bool) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Term_name _0 -> _0
let uu___is_Eff_name: foundname -> Prims.bool =
  fun projectee  ->
    match projectee with | Eff_name _0 -> true | uu____1599 -> false
let __proj__Eff_name__item___0:
  foundname ->
    (FStar_Syntax_Syntax.sigelt,FStar_Ident.lident)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Eff_name _0 -> _0
let set_iface: env -> Prims.bool -> env =
  fun env  ->
    fun b  ->
      let uu___111_1625 = env in
      {
        curmodule = (uu___111_1625.curmodule);
        curmonad = (uu___111_1625.curmonad);
        modules = (uu___111_1625.modules);
        scope_mods = (uu___111_1625.scope_mods);
        exported_ids = (uu___111_1625.exported_ids);
        trans_exported_ids = (uu___111_1625.trans_exported_ids);
        includes = (uu___111_1625.includes);
        sigaccum = (uu___111_1625.sigaccum);
        sigmap = (uu___111_1625.sigmap);
        iface = b;
        admitted_iface = (uu___111_1625.admitted_iface);
        expect_typ = (uu___111_1625.expect_typ);
        docs = (uu___111_1625.docs);
        remaining_iface_decls = (uu___111_1625.remaining_iface_decls);
        syntax_only = (uu___111_1625.syntax_only);
        ds_hooks = (uu___111_1625.ds_hooks)
      }
let iface: env -> Prims.bool = fun e  -> e.iface
let set_admitted_iface: env -> Prims.bool -> env =
  fun e  ->
    fun b  ->
      let uu___112_1635 = e in
      {
        curmodule = (uu___112_1635.curmodule);
        curmonad = (uu___112_1635.curmonad);
        modules = (uu___112_1635.modules);
        scope_mods = (uu___112_1635.scope_mods);
        exported_ids = (uu___112_1635.exported_ids);
        trans_exported_ids = (uu___112_1635.trans_exported_ids);
        includes = (uu___112_1635.includes);
        sigaccum = (uu___112_1635.sigaccum);
        sigmap = (uu___112_1635.sigmap);
        iface = (uu___112_1635.iface);
        admitted_iface = b;
        expect_typ = (uu___112_1635.expect_typ);
        docs = (uu___112_1635.docs);
        remaining_iface_decls = (uu___112_1635.remaining_iface_decls);
        syntax_only = (uu___112_1635.syntax_only);
        ds_hooks = (uu___112_1635.ds_hooks)
      }
let admitted_iface: env -> Prims.bool = fun e  -> e.admitted_iface
let set_expect_typ: env -> Prims.bool -> env =
  fun e  ->
    fun b  ->
      let uu___113_1645 = e in
      {
        curmodule = (uu___113_1645.curmodule);
        curmonad = (uu___113_1645.curmonad);
        modules = (uu___113_1645.modules);
        scope_mods = (uu___113_1645.scope_mods);
        exported_ids = (uu___113_1645.exported_ids);
        trans_exported_ids = (uu___113_1645.trans_exported_ids);
        includes = (uu___113_1645.includes);
        sigaccum = (uu___113_1645.sigaccum);
        sigmap = (uu___113_1645.sigmap);
        iface = (uu___113_1645.iface);
        admitted_iface = (uu___113_1645.admitted_iface);
        expect_typ = b;
        docs = (uu___113_1645.docs);
        remaining_iface_decls = (uu___113_1645.remaining_iface_decls);
        syntax_only = (uu___113_1645.syntax_only);
        ds_hooks = (uu___113_1645.ds_hooks)
      }
let expect_typ: env -> Prims.bool = fun e  -> e.expect_typ
let all_exported_id_kinds: exported_id_kind Prims.list =
  [Exported_id_field; Exported_id_term_type]
let transitive_exported_ids:
  env -> FStar_Ident.lident -> Prims.string Prims.list =
  fun env  ->
    fun lid  ->
      let module_name = FStar_Ident.string_of_lid lid in
      let uu____1660 =
        FStar_Util.smap_try_find env.trans_exported_ids module_name in
      match uu____1660 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some exported_id_set ->
          let uu____1666 =
            let uu____1667 = exported_id_set Exported_id_term_type in
            FStar_ST.op_Bang uu____1667 in
          FStar_All.pipe_right uu____1666 FStar_Util.set_elements
let open_modules:
  env ->
    (FStar_Ident.lident,FStar_Syntax_Syntax.modul)
      FStar_Pervasives_Native.tuple2 Prims.list
  = fun e  -> e.modules
let open_modules_and_namespaces: env -> FStar_Ident.lident Prims.list =
  fun env  ->
    FStar_List.filter_map
      (fun uu___79_1797  ->
         match uu___79_1797 with
         | Open_module_or_namespace (lid,_info) ->
             FStar_Pervasives_Native.Some lid
         | uu____1802 -> FStar_Pervasives_Native.None) env.scope_mods
let set_current_module: env -> FStar_Ident.lident -> env =
  fun e  ->
    fun l  ->
      let uu___114_1809 = e in
      {
        curmodule = (FStar_Pervasives_Native.Some l);
        curmonad = (uu___114_1809.curmonad);
        modules = (uu___114_1809.modules);
        scope_mods = (uu___114_1809.scope_mods);
        exported_ids = (uu___114_1809.exported_ids);
        trans_exported_ids = (uu___114_1809.trans_exported_ids);
        includes = (uu___114_1809.includes);
        sigaccum = (uu___114_1809.sigaccum);
        sigmap = (uu___114_1809.sigmap);
        iface = (uu___114_1809.iface);
        admitted_iface = (uu___114_1809.admitted_iface);
        expect_typ = (uu___114_1809.expect_typ);
        docs = (uu___114_1809.docs);
        remaining_iface_decls = (uu___114_1809.remaining_iface_decls);
        syntax_only = (uu___114_1809.syntax_only);
        ds_hooks = (uu___114_1809.ds_hooks)
      }
let current_module: env -> FStar_Ident.lident =
  fun env  ->
    match env.curmodule with
    | FStar_Pervasives_Native.None  -> failwith "Unset current module"
    | FStar_Pervasives_Native.Some m -> m
let iface_decls:
  env ->
    FStar_Ident.lident ->
      FStar_Parser_AST.decl Prims.list FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____1824 =
        FStar_All.pipe_right env.remaining_iface_decls
          (FStar_List.tryFind
             (fun uu____1858  ->
                match uu____1858 with
                | (m,uu____1866) -> FStar_Ident.lid_equals l m)) in
      match uu____1824 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (uu____1883,decls) ->
          FStar_Pervasives_Native.Some decls
let set_iface_decls:
  env -> FStar_Ident.lident -> FStar_Parser_AST.decl Prims.list -> env =
  fun env  ->
    fun l  ->
      fun ds  ->
        let uu____1910 =
          FStar_List.partition
            (fun uu____1940  ->
               match uu____1940 with
               | (m,uu____1948) -> FStar_Ident.lid_equals l m)
            env.remaining_iface_decls in
        match uu____1910 with
        | (uu____1953,rest) ->
            let uu___115_1987 = env in
            {
              curmodule = (uu___115_1987.curmodule);
              curmonad = (uu___115_1987.curmonad);
              modules = (uu___115_1987.modules);
              scope_mods = (uu___115_1987.scope_mods);
              exported_ids = (uu___115_1987.exported_ids);
              trans_exported_ids = (uu___115_1987.trans_exported_ids);
              includes = (uu___115_1987.includes);
              sigaccum = (uu___115_1987.sigaccum);
              sigmap = (uu___115_1987.sigmap);
              iface = (uu___115_1987.iface);
              admitted_iface = (uu___115_1987.admitted_iface);
              expect_typ = (uu___115_1987.expect_typ);
              docs = (uu___115_1987.docs);
              remaining_iface_decls = ((l, ds) :: rest);
              syntax_only = (uu___115_1987.syntax_only);
              ds_hooks = (uu___115_1987.ds_hooks)
            }
let qual: FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident =
  FStar_Syntax_Util.qual_id
let qualify: env -> FStar_Ident.ident -> FStar_Ident.lident =
  fun env  ->
    fun id1  ->
      match env.curmonad with
      | FStar_Pervasives_Native.None  ->
          let uu____2006 = current_module env in qual uu____2006 id1
      | FStar_Pervasives_Native.Some monad ->
          let uu____2008 =
            let uu____2009 = current_module env in qual uu____2009 monad in
          FStar_Syntax_Util.mk_field_projector_name_from_ident uu____2008 id1
let syntax_only: env -> Prims.bool = fun env  -> env.syntax_only
let set_syntax_only: env -> Prims.bool -> env =
  fun env  ->
    fun b  ->
      let uu___116_2019 = env in
      {
        curmodule = (uu___116_2019.curmodule);
        curmonad = (uu___116_2019.curmonad);
        modules = (uu___116_2019.modules);
        scope_mods = (uu___116_2019.scope_mods);
        exported_ids = (uu___116_2019.exported_ids);
        trans_exported_ids = (uu___116_2019.trans_exported_ids);
        includes = (uu___116_2019.includes);
        sigaccum = (uu___116_2019.sigaccum);
        sigmap = (uu___116_2019.sigmap);
        iface = (uu___116_2019.iface);
        admitted_iface = (uu___116_2019.admitted_iface);
        expect_typ = (uu___116_2019.expect_typ);
        docs = (uu___116_2019.docs);
        remaining_iface_decls = (uu___116_2019.remaining_iface_decls);
        syntax_only = b;
        ds_hooks = (uu___116_2019.ds_hooks)
      }
let ds_hooks: env -> dsenv_hooks = fun env  -> env.ds_hooks
let set_ds_hooks: env -> dsenv_hooks -> env =
  fun env  ->
    fun hooks  ->
      let uu___117_2029 = env in
      {
        curmodule = (uu___117_2029.curmodule);
        curmonad = (uu___117_2029.curmonad);
        modules = (uu___117_2029.modules);
        scope_mods = (uu___117_2029.scope_mods);
        exported_ids = (uu___117_2029.exported_ids);
        trans_exported_ids = (uu___117_2029.trans_exported_ids);
        includes = (uu___117_2029.includes);
        sigaccum = (uu___117_2029.sigaccum);
        sigmap = (uu___117_2029.sigmap);
        iface = (uu___117_2029.iface);
        admitted_iface = (uu___117_2029.admitted_iface);
        expect_typ = (uu___117_2029.expect_typ);
        docs = (uu___117_2029.docs);
        remaining_iface_decls = (uu___117_2029.remaining_iface_decls);
        syntax_only = (uu___117_2029.syntax_only);
        ds_hooks = hooks
      }
let new_sigmap: 'Auu____2032 . Prims.unit -> 'Auu____2032 FStar_Util.smap =
  fun uu____2038  -> FStar_Util.smap_create (Prims.parse_int "100")
let empty_env: Prims.unit -> env =
  fun uu____2041  ->
    let uu____2042 = new_sigmap () in
    let uu____2045 = new_sigmap () in
    let uu____2048 = new_sigmap () in
    let uu____2059 = new_sigmap () in
    let uu____2070 = new_sigmap () in
    {
      curmodule = FStar_Pervasives_Native.None;
      curmonad = FStar_Pervasives_Native.None;
      modules = [];
      scope_mods = [];
      exported_ids = uu____2042;
      trans_exported_ids = uu____2045;
      includes = uu____2048;
      sigaccum = [];
      sigmap = uu____2059;
      iface = false;
      admitted_iface = false;
      expect_typ = false;
      docs = uu____2070;
      remaining_iface_decls = [];
      syntax_only = false;
      ds_hooks = default_ds_hooks
    }
let sigmap:
  env ->
    (FStar_Syntax_Syntax.sigelt,Prims.bool) FStar_Pervasives_Native.tuple2
      FStar_Util.smap
  = fun env  -> env.sigmap
let has_all_in_scope: env -> Prims.bool =
  fun env  ->
    FStar_List.existsb
      (fun uu____2102  ->
         match uu____2102 with
         | (m,uu____2108) ->
             FStar_Ident.lid_equals m FStar_Parser_Const.all_lid) env.modules
let set_bv_range:
  FStar_Syntax_Syntax.bv -> FStar_Range.range -> FStar_Syntax_Syntax.bv =
  fun bv  ->
    fun r  ->
      let id1 =
        let uu___118_2116 = bv.FStar_Syntax_Syntax.ppname in
        {
          FStar_Ident.idText = (uu___118_2116.FStar_Ident.idText);
          FStar_Ident.idRange = r
        } in
      let uu___119_2117 = bv in
      {
        FStar_Syntax_Syntax.ppname = id1;
        FStar_Syntax_Syntax.index = (uu___119_2117.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = (uu___119_2117.FStar_Syntax_Syntax.sort)
      }
let bv_to_name:
  FStar_Syntax_Syntax.bv -> FStar_Range.range -> FStar_Syntax_Syntax.term =
  fun bv  -> fun r  -> FStar_Syntax_Syntax.bv_to_name (set_bv_range bv r)
let unmangleMap:
  (Prims.string,Prims.string,FStar_Syntax_Syntax.delta_depth,FStar_Syntax_Syntax.fv_qual
                                                               FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple4 Prims.list
  =
  [("op_ColonColon", "Cons", FStar_Syntax_Syntax.Delta_constant,
     (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor));
  ("not", "op_Negation", FStar_Syntax_Syntax.Delta_equational,
    FStar_Pervasives_Native.None)]
let unmangleOpName:
  FStar_Ident.ident ->
    (FStar_Syntax_Syntax.term,Prims.bool) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option
  =
  fun id1  ->
    let t =
      FStar_Util.find_map unmangleMap
        (fun uu____2204  ->
           match uu____2204 with
           | (x,y,dd,dq) ->
               if id1.FStar_Ident.idText = x
               then
                 let uu____2227 =
                   let uu____2228 =
                     FStar_Ident.lid_of_path ["Prims"; y]
                       id1.FStar_Ident.idRange in
                   FStar_Syntax_Syntax.fvar uu____2228 dd dq in
                 FStar_Pervasives_Native.Some uu____2227
               else FStar_Pervasives_Native.None) in
    match t with
    | FStar_Pervasives_Native.Some v1 ->
        FStar_Pervasives_Native.Some (v1, false)
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
type 'a cont_t =
  | Cont_ok of 'a
  | Cont_fail
  | Cont_ignore[@@deriving show]
let uu___is_Cont_ok: 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_ok _0 -> true | uu____2271 -> false
let __proj__Cont_ok__item___0: 'a . 'a cont_t -> 'a =
  fun projectee  -> match projectee with | Cont_ok _0 -> _0
let uu___is_Cont_fail: 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_fail  -> true | uu____2300 -> false
let uu___is_Cont_ignore: 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_ignore  -> true | uu____2314 -> false
let option_of_cont:
  'a .
    (Prims.unit -> 'a FStar_Pervasives_Native.option) ->
      'a cont_t -> 'a FStar_Pervasives_Native.option
  =
  fun k_ignore  ->
    fun uu___80_2337  ->
      match uu___80_2337 with
      | Cont_ok a -> FStar_Pervasives_Native.Some a
      | Cont_fail  -> FStar_Pervasives_Native.None
      | Cont_ignore  -> k_ignore ()
let find_in_record:
  'Auu____2350 .
    FStar_Ident.ident Prims.list ->
      FStar_Ident.ident ->
        record_or_dc ->
          (record_or_dc -> 'Auu____2350 cont_t) -> 'Auu____2350 cont_t
  =
  fun ns  ->
    fun id1  ->
      fun record  ->
        fun cont  ->
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
                (fun uu____2396  ->
                   match uu____2396 with
                   | (f,uu____2404) ->
                       if id1.FStar_Ident.idText = f.FStar_Ident.idText
                       then FStar_Pervasives_Native.Some record
                       else FStar_Pervasives_Native.None) in
            match find1 with
            | FStar_Pervasives_Native.Some r -> cont r
            | FStar_Pervasives_Native.None  -> Cont_ignore
          else Cont_ignore
let get_exported_id_set:
  env ->
    Prims.string ->
      (exported_id_kind -> string_set FStar_ST.ref)
        FStar_Pervasives_Native.option
  = fun e  -> fun mname  -> FStar_Util.smap_try_find e.exported_ids mname
let get_trans_exported_id_set:
  env ->
    Prims.string ->
      (exported_id_kind -> string_set FStar_ST.ref)
        FStar_Pervasives_Native.option
  =
  fun e  -> fun mname  -> FStar_Util.smap_try_find e.trans_exported_ids mname
let string_of_exported_id_kind: exported_id_kind -> Prims.string =
  fun uu___81_2450  ->
    match uu___81_2450 with
    | Exported_id_field  -> "field"
    | Exported_id_term_type  -> "term/type"
let find_in_module_with_includes:
  'a .
    exported_id_kind ->
      (FStar_Ident.lident -> 'a cont_t) ->
        'a cont_t ->
          env -> FStar_Ident.lident -> FStar_Ident.ident -> 'a cont_t
  =
  fun eikind  ->
    fun find_in_module  ->
      fun find_in_module_default  ->
        fun env  ->
          fun ns  ->
            fun id1  ->
              let idstr = id1.FStar_Ident.idText in
              let rec aux uu___82_2506 =
                match uu___82_2506 with
                | [] -> find_in_module_default
                | modul::q ->
                    let mname = modul.FStar_Ident.str in
                    let not_shadowed =
                      let uu____2517 = get_exported_id_set env mname in
                      match uu____2517 with
                      | FStar_Pervasives_Native.None  -> true
                      | FStar_Pervasives_Native.Some mex ->
                          let mexports =
                            let uu____2538 = mex eikind in
                            FStar_ST.op_Bang uu____2538 in
                          FStar_Util.set_mem idstr mexports in
                    let mincludes =
                      let uu____2652 =
                        FStar_Util.smap_try_find env.includes mname in
                      match uu____2652 with
                      | FStar_Pervasives_Native.None  -> []
                      | FStar_Pervasives_Native.Some minc ->
                          FStar_ST.op_Bang minc in
                    let look_into =
                      if not_shadowed
                      then
                        let uu____2728 = qual modul id1 in
                        find_in_module uu____2728
                      else Cont_ignore in
                    (match look_into with
                     | Cont_ignore  -> aux (FStar_List.append mincludes q)
                     | uu____2732 -> look_into) in
              aux [ns]
let is_exported_id_field: exported_id_kind -> Prims.bool =
  fun uu___83_2737  ->
    match uu___83_2737 with
    | Exported_id_field  -> true
    | uu____2738 -> false
let try_lookup_id'':
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
  fun env  ->
    fun id1  ->
      fun eikind  ->
        fun k_local_binding  ->
          fun k_rec_binding  ->
            fun k_record  ->
              fun find_in_module  ->
                fun lookup_default_id  ->
                  let check_local_binding_id uu___84_2840 =
                    match uu___84_2840 with
                    | (id',uu____2842,uu____2843) ->
                        id'.FStar_Ident.idText = id1.FStar_Ident.idText in
                  let check_rec_binding_id uu___85_2847 =
                    match uu___85_2847 with
                    | (id',uu____2849,uu____2850) ->
                        id'.FStar_Ident.idText = id1.FStar_Ident.idText in
                  let curmod_ns =
                    let uu____2854 = current_module env in
                    FStar_Ident.ids_of_lid uu____2854 in
                  let proc uu___86_2860 =
                    match uu___86_2860 with
                    | Local_binding l when check_local_binding_id l ->
                        k_local_binding l
                    | Rec_binding r when check_rec_binding_id r ->
                        k_rec_binding r
                    | Open_module_or_namespace (ns,Open_module ) ->
                        find_in_module_with_includes eikind find_in_module
                          Cont_ignore env ns id1
                    | Top_level_def id' when
                        id'.FStar_Ident.idText = id1.FStar_Ident.idText ->
                        lookup_default_id Cont_ignore id1
                    | Record_or_dc r when is_exported_id_field eikind ->
                        let uu____2868 = FStar_Ident.lid_of_ids curmod_ns in
                        find_in_module_with_includes Exported_id_field
                          (fun lid  ->
                             let id2 = lid.FStar_Ident.ident in
                             find_in_record lid.FStar_Ident.ns id2 r k_record)
                          Cont_ignore env uu____2868 id1
                    | uu____2873 -> Cont_ignore in
                  let rec aux uu___87_2881 =
                    match uu___87_2881 with
                    | a::q ->
                        let uu____2890 = proc a in
                        option_of_cont (fun uu____2894  -> aux q) uu____2890
                    | [] ->
                        let uu____2895 = lookup_default_id Cont_fail id1 in
                        option_of_cont
                          (fun uu____2899  -> FStar_Pervasives_Native.None)
                          uu____2895 in
                  aux env.scope_mods
let found_local_binding:
  'Auu____2904 'Auu____2905 .
    FStar_Range.range ->
      ('Auu____2905,FStar_Syntax_Syntax.bv,'Auu____2904)
        FStar_Pervasives_Native.tuple3 ->
        (FStar_Syntax_Syntax.term,'Auu____2904)
          FStar_Pervasives_Native.tuple2
  =
  fun r  ->
    fun uu____2923  ->
      match uu____2923 with
      | (id',x,mut) -> let uu____2933 = bv_to_name x r in (uu____2933, mut)
let find_in_module:
  'Auu____2939 .
    env ->
      FStar_Ident.lident ->
        (FStar_Ident.lident ->
           (FStar_Syntax_Syntax.sigelt,Prims.bool)
             FStar_Pervasives_Native.tuple2 -> 'Auu____2939)
          -> 'Auu____2939 -> 'Auu____2939
  =
  fun env  ->
    fun lid  ->
      fun k_global_def  ->
        fun k_not_found  ->
          let uu____2974 =
            FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str in
          match uu____2974 with
          | FStar_Pervasives_Native.Some sb -> k_global_def lid sb
          | FStar_Pervasives_Native.None  -> k_not_found
let try_lookup_id:
  env ->
    FStar_Ident.ident ->
      (FStar_Syntax_Syntax.term,Prims.bool) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option
  =
  fun env  ->
    fun id1  ->
      let uu____3010 = unmangleOpName id1 in
      match uu____3010 with
      | FStar_Pervasives_Native.Some f -> FStar_Pervasives_Native.Some f
      | uu____3036 ->
          try_lookup_id'' env id1 Exported_id_term_type
            (fun r  ->
               let uu____3050 = found_local_binding id1.FStar_Ident.idRange r in
               Cont_ok uu____3050) (fun uu____3060  -> Cont_fail)
            (fun uu____3066  -> Cont_ignore)
            (fun i  ->
               find_in_module env i
                 (fun uu____3081  -> fun uu____3082  -> Cont_fail)
                 Cont_ignore)
            (fun uu____3097  -> fun uu____3098  -> Cont_fail)
let lookup_default_id:
  'a .
    env ->
      FStar_Ident.ident ->
        (FStar_Ident.lident ->
           (FStar_Syntax_Syntax.sigelt,Prims.bool)
             FStar_Pervasives_Native.tuple2 -> 'a cont_t)
          -> 'a cont_t -> 'a cont_t
  =
  fun env  ->
    fun id1  ->
      fun k_global_def  ->
        fun k_not_found  ->
          let find_in_monad =
            match env.curmonad with
            | FStar_Pervasives_Native.Some uu____3168 ->
                let lid = qualify env id1 in
                let uu____3170 =
                  FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str in
                (match uu____3170 with
                 | FStar_Pervasives_Native.Some r ->
                     let uu____3194 = k_global_def lid r in
                     FStar_Pervasives_Native.Some uu____3194
                 | FStar_Pervasives_Native.None  ->
                     FStar_Pervasives_Native.None)
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None in
          match find_in_monad with
          | FStar_Pervasives_Native.Some v1 -> v1
          | FStar_Pervasives_Native.None  ->
              let lid =
                let uu____3217 = current_module env in qual uu____3217 id1 in
              find_in_module env lid k_global_def k_not_found
let module_is_defined: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      (match env.curmodule with
       | FStar_Pervasives_Native.None  -> false
       | FStar_Pervasives_Native.Some m ->
           let uu____3227 = current_module env in
           FStar_Ident.lid_equals lid uu____3227)
        ||
        (FStar_List.existsb
           (fun x  ->
              FStar_Ident.lid_equals lid (FStar_Pervasives_Native.fst x))
           env.modules)
let resolve_module_name:
  env ->
    FStar_Ident.lident ->
      Prims.bool -> FStar_Ident.lident FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      fun honor_ns  ->
        let nslen = FStar_List.length lid.FStar_Ident.ns in
        let rec aux uu___88_3259 =
          match uu___88_3259 with
          | [] ->
              let uu____3264 = module_is_defined env lid in
              if uu____3264
              then FStar_Pervasives_Native.Some lid
              else FStar_Pervasives_Native.None
          | (Open_module_or_namespace (ns,Open_namespace ))::q when honor_ns
              ->
              let new_lid =
                let uu____3273 =
                  let uu____3276 = FStar_Ident.path_of_lid ns in
                  let uu____3279 = FStar_Ident.path_of_lid lid in
                  FStar_List.append uu____3276 uu____3279 in
                FStar_Ident.lid_of_path uu____3273
                  (FStar_Ident.range_of_lid lid) in
              let uu____3282 = module_is_defined env new_lid in
              if uu____3282
              then FStar_Pervasives_Native.Some new_lid
              else aux q
          | (Module_abbrev (name,modul))::uu____3288 when
              (nslen = (Prims.parse_int "0")) &&
                (name.FStar_Ident.idText =
                   (lid.FStar_Ident.ident).FStar_Ident.idText)
              -> FStar_Pervasives_Native.Some modul
          | uu____3295::q -> aux q in
        aux env.scope_mods
let fail_if_curmodule:
  env -> FStar_Ident.lident -> FStar_Ident.lident -> Prims.unit =
  fun env  ->
    fun ns_original  ->
      fun ns_resolved  ->
        let uu____3308 =
          let uu____3309 = current_module env in
          FStar_Ident.lid_equals ns_resolved uu____3309 in
        if uu____3308
        then
          (if FStar_Ident.lid_equals ns_resolved FStar_Parser_Const.prims_lid
           then ()
           else
             (let uu____3311 =
                let uu____3316 =
                  FStar_Util.format1
                    "Reference %s to current module is forbidden (see GitHub issue #451)"
                    ns_original.FStar_Ident.str in
                (FStar_Errors.Fatal_ForbiddenReferenceToCurrentModule,
                  uu____3316) in
              FStar_Errors.raise_error uu____3311
                (FStar_Ident.range_of_lid ns_original)))
        else ()
let fail_if_qualified_by_curmodule: env -> FStar_Ident.lident -> Prims.unit =
  fun env  ->
    fun lid  ->
      match lid.FStar_Ident.ns with
      | [] -> ()
      | uu____3324 ->
          let modul_orig = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          let uu____3328 = resolve_module_name env modul_orig true in
          (match uu____3328 with
           | FStar_Pervasives_Native.Some modul_res ->
               fail_if_curmodule env modul_orig modul_res
           | uu____3332 -> ())
let namespace_is_open: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      FStar_List.existsb
        (fun uu___89_3343  ->
           match uu___89_3343 with
           | Open_module_or_namespace (ns,Open_namespace ) ->
               FStar_Ident.lid_equals lid ns
           | uu____3345 -> false) env.scope_mods
let shorten_module_path:
  env ->
    FStar_Ident.ident Prims.list ->
      Prims.bool ->
        (FStar_Ident.ident Prims.list,FStar_Ident.ident Prims.list)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun ids  ->
      fun is_full_path  ->
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
                 let uu____3434 = aux rev_ns_prefix ns_last_id in
                 FStar_All.pipe_right uu____3434
                   (FStar_Util.map_option
                      (fun uu____3484  ->
                         match uu____3484 with
                         | (stripped_ids,rev_kept_ids) ->
                             (stripped_ids, (id1 :: rev_kept_ids))))) in
        let uu____3515 =
          is_full_path &&
            (let uu____3517 = FStar_Ident.lid_of_ids ids in
             module_is_defined env uu____3517) in
        if uu____3515
        then (ids, [])
        else
          (match FStar_List.rev ids with
           | [] -> ([], [])
           | ns_last_id::ns_rev_prefix ->
               let uu____3547 = aux ns_rev_prefix ns_last_id in
               (match uu____3547 with
                | FStar_Pervasives_Native.None  -> ([], ids)
                | FStar_Pervasives_Native.Some (stripped_ids,rev_kept_ids) ->
                    (stripped_ids, (FStar_List.rev rev_kept_ids))))
let shorten_lid: env -> FStar_Ident.lid -> FStar_Ident.lid =
  fun env  ->
    fun lid  ->
      let uu____3606 = shorten_module_path env lid.FStar_Ident.ns true in
      match uu____3606 with
      | (uu____3615,short) ->
          FStar_Ident.lid_of_ns_and_id short lid.FStar_Ident.ident
let resolve_in_open_namespaces'':
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
  fun env  ->
    fun lid  ->
      fun eikind  ->
        fun k_local_binding  ->
          fun k_rec_binding  ->
            fun k_record  ->
              fun f_module  ->
                fun l_default  ->
                  match lid.FStar_Ident.ns with
                  | uu____3723::uu____3724 ->
                      let uu____3727 =
                        let uu____3730 =
                          let uu____3731 =
                            FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
                          FStar_Ident.set_lid_range uu____3731
                            (FStar_Ident.range_of_lid lid) in
                        resolve_module_name env uu____3730 true in
                      (match uu____3727 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some modul ->
                           let uu____3735 =
                             find_in_module_with_includes eikind f_module
                               Cont_fail env modul lid.FStar_Ident.ident in
                           option_of_cont
                             (fun uu____3739  -> FStar_Pervasives_Native.None)
                             uu____3735)
                  | [] ->
                      try_lookup_id'' env lid.FStar_Ident.ident eikind
                        k_local_binding k_rec_binding k_record f_module
                        l_default
let cont_of_option:
  'a . 'a cont_t -> 'a FStar_Pervasives_Native.option -> 'a cont_t =
  fun k_none  ->
    fun uu___90_3757  ->
      match uu___90_3757 with
      | FStar_Pervasives_Native.Some v1 -> Cont_ok v1
      | FStar_Pervasives_Native.None  -> k_none
let resolve_in_open_namespaces':
  'a .
    env ->
      FStar_Ident.lident ->
        (local_binding -> 'a FStar_Pervasives_Native.option) ->
          (rec_binding -> 'a FStar_Pervasives_Native.option) ->
            (FStar_Ident.lident ->
               (FStar_Syntax_Syntax.sigelt,Prims.bool)
                 FStar_Pervasives_Native.tuple2 ->
                 'a FStar_Pervasives_Native.option)
              -> 'a FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      fun k_local_binding  ->
        fun k_rec_binding  ->
          fun k_global_def  ->
            let k_global_def' k lid1 def =
              let uu____3856 = k_global_def lid1 def in
              cont_of_option k uu____3856 in
            let f_module lid' =
              let k = Cont_ignore in
              find_in_module env lid' (k_global_def' k) k in
            let l_default k i = lookup_default_id env i (k_global_def' k) k in
            resolve_in_open_namespaces'' env lid Exported_id_term_type
              (fun l  ->
                 let uu____3886 = k_local_binding l in
                 cont_of_option Cont_fail uu____3886)
              (fun r  ->
                 let uu____3892 = k_rec_binding r in
                 cont_of_option Cont_fail uu____3892)
              (fun uu____3896  -> Cont_ignore) f_module l_default
let fv_qual_of_se:
  FStar_Syntax_Syntax.sigelt ->
    FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____3904,uu____3905,uu____3906,l,uu____3908,uu____3909) ->
        let qopt =
          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
            (fun uu___91_3920  ->
               match uu___91_3920 with
               | FStar_Syntax_Syntax.RecordConstructor (uu____3923,fs) ->
                   FStar_Pervasives_Native.Some
                     (FStar_Syntax_Syntax.Record_ctor (l, fs))
               | uu____3935 -> FStar_Pervasives_Native.None) in
        (match qopt with
         | FStar_Pervasives_Native.None  ->
             FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor
         | x -> x)
    | FStar_Syntax_Syntax.Sig_declare_typ (uu____3941,uu____3942,uu____3943)
        -> FStar_Pervasives_Native.None
    | uu____3944 -> FStar_Pervasives_Native.None
let lb_fv:
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Ident.lident -> FStar_Syntax_Syntax.fv
  =
  fun lbs  ->
    fun lid  ->
      let uu____3955 =
        FStar_Util.find_map lbs
          (fun lb  ->
             let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
             let uu____3963 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
             if uu____3963
             then FStar_Pervasives_Native.Some fv
             else FStar_Pervasives_Native.None) in
      FStar_All.pipe_right uu____3955 FStar_Util.must
let ns_of_lid_equals: FStar_Ident.lident -> FStar_Ident.lident -> Prims.bool
  =
  fun lid  ->
    fun ns  ->
      ((FStar_List.length lid.FStar_Ident.ns) =
         (FStar_List.length (FStar_Ident.ids_of_lid ns)))
        &&
        (let uu____3976 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
         FStar_Ident.lid_equals uu____3976 ns)
let try_lookup_name:
  Prims.bool ->
    Prims.bool ->
      env -> FStar_Ident.lident -> foundname FStar_Pervasives_Native.option
  =
  fun any_val  ->
    fun exclude_interf  ->
      fun env  ->
        fun lid  ->
          let occurrence_range = FStar_Ident.range_of_lid lid in
          let k_global_def source_lid uu___96_4006 =
            match uu___96_4006 with
            | (uu____4013,true ) when exclude_interf ->
                FStar_Pervasives_Native.None
            | (se,uu____4015) ->
                (match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_inductive_typ uu____4018 ->
                     let uu____4035 =
                       let uu____4036 =
                         let uu____4041 =
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.Delta_constant
                             FStar_Pervasives_Native.None in
                         (uu____4041, false) in
                       Term_name uu____4036 in
                     FStar_Pervasives_Native.Some uu____4035
                 | FStar_Syntax_Syntax.Sig_datacon uu____4042 ->
                     let uu____4057 =
                       let uu____4058 =
                         let uu____4063 =
                           let uu____4064 = fv_qual_of_se se in
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.Delta_constant uu____4064 in
                         (uu____4063, false) in
                       Term_name uu____4058 in
                     FStar_Pervasives_Native.Some uu____4057
                 | FStar_Syntax_Syntax.Sig_let ((uu____4067,lbs),uu____4069)
                     ->
                     let fv = lb_fv lbs source_lid in
                     let uu____4085 =
                       let uu____4086 =
                         let uu____4091 =
                           FStar_Syntax_Syntax.fvar source_lid
                             fv.FStar_Syntax_Syntax.fv_delta
                             fv.FStar_Syntax_Syntax.fv_qual in
                         (uu____4091, false) in
                       Term_name uu____4086 in
                     FStar_Pervasives_Native.Some uu____4085
                 | FStar_Syntax_Syntax.Sig_declare_typ
                     (lid1,uu____4093,uu____4094) ->
                     let quals = se.FStar_Syntax_Syntax.sigquals in
                     let uu____4098 =
                       any_val ||
                         (FStar_All.pipe_right quals
                            (FStar_Util.for_some
                               (fun uu___92_4102  ->
                                  match uu___92_4102 with
                                  | FStar_Syntax_Syntax.Assumption  -> true
                                  | uu____4103 -> false))) in
                     if uu____4098
                     then
                       let lid2 =
                         FStar_Ident.set_lid_range lid1
                           (FStar_Ident.range_of_lid source_lid) in
                       let dd =
                         let uu____4108 =
                           (FStar_Syntax_Util.is_primop_lid lid2) ||
                             (FStar_All.pipe_right quals
                                (FStar_Util.for_some
                                   (fun uu___93_4113  ->
                                      match uu___93_4113 with
                                      | FStar_Syntax_Syntax.Projector
                                          uu____4114 -> true
                                      | FStar_Syntax_Syntax.Discriminator
                                          uu____4119 -> true
                                      | uu____4120 -> false))) in
                         if uu____4108
                         then FStar_Syntax_Syntax.Delta_equational
                         else FStar_Syntax_Syntax.Delta_constant in
                       let dd1 =
                         let uu____4123 =
                           FStar_All.pipe_right quals
                             (FStar_Util.for_some
                                (fun uu___94_4127  ->
                                   match uu___94_4127 with
                                   | FStar_Syntax_Syntax.Abstract  -> true
                                   | uu____4128 -> false)) in
                         if uu____4123
                         then FStar_Syntax_Syntax.Delta_abstract dd
                         else dd in
                       let uu____4130 =
                         FStar_Util.find_map quals
                           (fun uu___95_4135  ->
                              match uu___95_4135 with
                              | FStar_Syntax_Syntax.Reflectable refl_monad ->
                                  FStar_Pervasives_Native.Some refl_monad
                              | uu____4139 -> FStar_Pervasives_Native.None) in
                       (match uu____4130 with
                        | FStar_Pervasives_Native.Some refl_monad ->
                            let refl_const =
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_constant
                                   (FStar_Const.Const_reflect refl_monad))
                                FStar_Pervasives_Native.None occurrence_range in
                            FStar_Pervasives_Native.Some
                              (Term_name (refl_const, false))
                        | uu____4148 ->
                            let uu____4151 =
                              let uu____4152 =
                                let uu____4157 =
                                  let uu____4158 = fv_qual_of_se se in
                                  FStar_Syntax_Syntax.fvar lid2 dd1
                                    uu____4158 in
                                (uu____4157, false) in
                              Term_name uu____4152 in
                            FStar_Pervasives_Native.Some uu____4151)
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
                 | FStar_Syntax_Syntax.Sig_effect_abbrev uu____4164 ->
                     FStar_Pervasives_Native.Some (Eff_name (se, source_lid))
                 | uu____4177 -> FStar_Pervasives_Native.None) in
          let k_local_binding r =
            let uu____4196 =
              let uu____4197 =
                found_local_binding (FStar_Ident.range_of_lid lid) r in
              Term_name uu____4197 in
            FStar_Pervasives_Native.Some uu____4196 in
          let k_rec_binding uu____4213 =
            match uu____4213 with
            | (id1,l,dd) ->
                let uu____4225 =
                  let uu____4226 =
                    let uu____4231 =
                      FStar_Syntax_Syntax.fvar
                        (FStar_Ident.set_lid_range l
                           (FStar_Ident.range_of_lid lid)) dd
                        FStar_Pervasives_Native.None in
                    (uu____4231, false) in
                  Term_name uu____4226 in
                FStar_Pervasives_Native.Some uu____4225 in
          let found_unmangled =
            match lid.FStar_Ident.ns with
            | [] ->
                let uu____4237 = unmangleOpName lid.FStar_Ident.ident in
                (match uu____4237 with
                 | FStar_Pervasives_Native.Some f ->
                     FStar_Pervasives_Native.Some (Term_name f)
                 | uu____4255 -> FStar_Pervasives_Native.None)
            | uu____4262 -> FStar_Pervasives_Native.None in
          match found_unmangled with
          | FStar_Pervasives_Native.None  ->
              resolve_in_open_namespaces' env lid k_local_binding
                k_rec_binding k_global_def
          | x -> x
let try_lookup_effect_name':
  Prims.bool ->
    env ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.sigelt,FStar_Ident.lident)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun exclude_interf  ->
    fun env  ->
      fun lid  ->
        let uu____4291 = try_lookup_name true exclude_interf env lid in
        match uu____4291 with
        | FStar_Pervasives_Native.Some (Eff_name (o,l)) ->
            FStar_Pervasives_Native.Some (o, l)
        | uu____4306 -> FStar_Pervasives_Native.None
let try_lookup_effect_name:
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____4321 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____4321 with
      | FStar_Pervasives_Native.Some (o,l1) ->
          FStar_Pervasives_Native.Some l1
      | uu____4336 -> FStar_Pervasives_Native.None
let try_lookup_effect_name_and_attributes:
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident,FStar_Syntax_Syntax.cflags Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____4357 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____4357 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____4373;
             FStar_Syntax_Syntax.sigquals = uu____4374;
             FStar_Syntax_Syntax.sigmeta = uu____4375;
             FStar_Syntax_Syntax.sigattrs = uu____4376;_},l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____4395;
             FStar_Syntax_Syntax.sigquals = uu____4396;
             FStar_Syntax_Syntax.sigmeta = uu____4397;
             FStar_Syntax_Syntax.sigattrs = uu____4398;_},l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (uu____4416,uu____4417,uu____4418,uu____4419,cattributes);
             FStar_Syntax_Syntax.sigrng = uu____4421;
             FStar_Syntax_Syntax.sigquals = uu____4422;
             FStar_Syntax_Syntax.sigmeta = uu____4423;
             FStar_Syntax_Syntax.sigattrs = uu____4424;_},l1)
          -> FStar_Pervasives_Native.Some (l1, cattributes)
      | uu____4446 -> FStar_Pervasives_Native.None
let try_lookup_effect_defn:
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.eff_decl FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____4467 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____4467 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____4477;
             FStar_Syntax_Syntax.sigquals = uu____4478;
             FStar_Syntax_Syntax.sigmeta = uu____4479;
             FStar_Syntax_Syntax.sigattrs = uu____4480;_},uu____4481)
          -> FStar_Pervasives_Native.Some ne
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____4491;
             FStar_Syntax_Syntax.sigquals = uu____4492;
             FStar_Syntax_Syntax.sigmeta = uu____4493;
             FStar_Syntax_Syntax.sigattrs = uu____4494;_},uu____4495)
          -> FStar_Pervasives_Native.Some ne
      | uu____4504 -> FStar_Pervasives_Native.None
let is_effect_name: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____4517 = try_lookup_effect_name env lid in
      match uu____4517 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____4520 -> true
let try_lookup_root_effect_name:
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____4529 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____4529 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (l',uu____4539,uu____4540,uu____4541,uu____4542);
             FStar_Syntax_Syntax.sigrng = uu____4543;
             FStar_Syntax_Syntax.sigquals = uu____4544;
             FStar_Syntax_Syntax.sigmeta = uu____4545;
             FStar_Syntax_Syntax.sigattrs = uu____4546;_},uu____4547)
          ->
          let rec aux new_name =
            let uu____4566 =
              FStar_Util.smap_try_find (sigmap env) new_name.FStar_Ident.str in
            match uu____4566 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (s,uu____4584) ->
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
                     (uu____4593,uu____4594,uu____4595,cmp,uu____4597) ->
                     let l'' = FStar_Syntax_Util.comp_effect_name cmp in
                     aux l''
                 | uu____4603 -> FStar_Pervasives_Native.None) in
          aux l'
      | FStar_Pervasives_Native.Some (uu____4604,l') ->
          FStar_Pervasives_Native.Some l'
      | uu____4610 -> FStar_Pervasives_Native.None
let lookup_letbinding_quals:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___97_4639 =
        match uu___97_4639 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____4648,uu____4649,uu____4650);
             FStar_Syntax_Syntax.sigrng = uu____4651;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____4653;
             FStar_Syntax_Syntax.sigattrs = uu____4654;_},uu____4655)
            -> FStar_Pervasives_Native.Some quals
        | uu____4662 -> FStar_Pervasives_Native.None in
      let uu____4669 =
        resolve_in_open_namespaces' env lid
          (fun uu____4677  -> FStar_Pervasives_Native.None)
          (fun uu____4681  -> FStar_Pervasives_Native.None) k_global_def in
      match uu____4669 with
      | FStar_Pervasives_Native.Some quals -> quals
      | uu____4691 -> []
let try_lookup_module:
  env ->
    Prims.string Prims.list ->
      FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option
  =
  fun env  ->
    fun path  ->
      let uu____4708 =
        FStar_List.tryFind
          (fun uu____4723  ->
             match uu____4723 with
             | (mlid,modul) ->
                 let uu____4730 = FStar_Ident.path_of_lid mlid in
                 uu____4730 = path) env.modules in
      match uu____4708 with
      | FStar_Pervasives_Native.Some (uu____4737,modul) ->
          FStar_Pervasives_Native.Some modul
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
let try_lookup_let:
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___98_4767 =
        match uu___98_4767 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               ((uu____4774,lbs),uu____4776);
             FStar_Syntax_Syntax.sigrng = uu____4777;
             FStar_Syntax_Syntax.sigquals = uu____4778;
             FStar_Syntax_Syntax.sigmeta = uu____4779;
             FStar_Syntax_Syntax.sigattrs = uu____4780;_},uu____4781)
            ->
            let fv = lb_fv lbs lid1 in
            let uu____4801 =
              FStar_Syntax_Syntax.fvar lid1 fv.FStar_Syntax_Syntax.fv_delta
                fv.FStar_Syntax_Syntax.fv_qual in
            FStar_Pervasives_Native.Some uu____4801
        | uu____4802 -> FStar_Pervasives_Native.None in
      resolve_in_open_namespaces' env lid
        (fun uu____4808  -> FStar_Pervasives_Native.None)
        (fun uu____4810  -> FStar_Pervasives_Native.None) k_global_def
let try_lookup_definition:
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___99_4833 =
        match uu___99_4833 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               (lbs,uu____4843);
             FStar_Syntax_Syntax.sigrng = uu____4844;
             FStar_Syntax_Syntax.sigquals = uu____4845;
             FStar_Syntax_Syntax.sigmeta = uu____4846;
             FStar_Syntax_Syntax.sigattrs = uu____4847;_},uu____4848)
            ->
            FStar_Util.find_map (FStar_Pervasives_Native.snd lbs)
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inr fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv lid1 ->
                     FStar_Pervasives_Native.Some
                       (lb.FStar_Syntax_Syntax.lbdef)
                 | uu____4871 -> FStar_Pervasives_Native.None)
        | uu____4878 -> FStar_Pervasives_Native.None in
      resolve_in_open_namespaces' env lid
        (fun uu____4888  -> FStar_Pervasives_Native.None)
        (fun uu____4892  -> FStar_Pervasives_Native.None) k_global_def
let empty_include_smap:
  FStar_Ident.lident Prims.list FStar_ST.ref FStar_Util.smap = new_sigmap ()
let empty_exported_id_smap: exported_id_set FStar_Util.smap = new_sigmap ()
let try_lookup_lid':
  Prims.bool ->
    Prims.bool ->
      env ->
        FStar_Ident.lident ->
          (FStar_Syntax_Syntax.term,Prims.bool)
            FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun any_val  ->
    fun exclude_interface  ->
      fun env  ->
        fun lid  ->
          let uu____4931 = try_lookup_name any_val exclude_interface env lid in
          match uu____4931 with
          | FStar_Pervasives_Native.Some (Term_name (e,mut)) ->
              FStar_Pervasives_Native.Some (e, mut)
          | uu____4946 -> FStar_Pervasives_Native.None
let try_lookup_lid:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term,Prims.bool) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option
  = fun env  -> fun l  -> try_lookup_lid' env.iface false env l
let resolve_to_fully_qualified_name:
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____4973 = try_lookup_lid env l in
      match uu____4973 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (e,uu____4987) ->
          let uu____4992 =
            let uu____4993 = FStar_Syntax_Subst.compress e in
            uu____4993.FStar_Syntax_Syntax.n in
          (match uu____4992 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               FStar_Pervasives_Native.Some
                 ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
           | uu____4999 -> FStar_Pervasives_Native.None)
let try_lookup_lid_no_resolve:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term,Prims.bool) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let env' =
        let uu___120_5013 = env in
        {
          curmodule = (uu___120_5013.curmodule);
          curmonad = (uu___120_5013.curmonad);
          modules = (uu___120_5013.modules);
          scope_mods = [];
          exported_ids = empty_exported_id_smap;
          trans_exported_ids = (uu___120_5013.trans_exported_ids);
          includes = empty_include_smap;
          sigaccum = (uu___120_5013.sigaccum);
          sigmap = (uu___120_5013.sigmap);
          iface = (uu___120_5013.iface);
          admitted_iface = (uu___120_5013.admitted_iface);
          expect_typ = (uu___120_5013.expect_typ);
          docs = (uu___120_5013.docs);
          remaining_iface_decls = (uu___120_5013.remaining_iface_decls);
          syntax_only = (uu___120_5013.syntax_only);
          ds_hooks = (uu___120_5013.ds_hooks)
        } in
      try_lookup_lid env' l
let try_lookup_doc:
  env ->
    FStar_Ident.lid -> FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option
  = fun env  -> fun l  -> FStar_Util.smap_try_find env.docs l.FStar_Ident.str
let try_lookup_datacon:
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.fv FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___101_5042 =
        match uu___101_5042 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____5049,uu____5050,uu____5051);
             FStar_Syntax_Syntax.sigrng = uu____5052;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____5054;
             FStar_Syntax_Syntax.sigattrs = uu____5055;_},uu____5056)
            ->
            let uu____5061 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___100_5065  ->
                      match uu___100_5065 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | uu____5066 -> false)) in
            if uu____5061
            then
              let uu____5069 =
                FStar_Syntax_Syntax.lid_as_fv lid1
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None in
              FStar_Pervasives_Native.Some uu____5069
            else FStar_Pervasives_Native.None
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
               uu____5071;
             FStar_Syntax_Syntax.sigrng = uu____5072;
             FStar_Syntax_Syntax.sigquals = uu____5073;
             FStar_Syntax_Syntax.sigmeta = uu____5074;
             FStar_Syntax_Syntax.sigattrs = uu____5075;_},uu____5076)
            ->
            let uu____5095 =
              FStar_Syntax_Syntax.lid_as_fv lid1
                FStar_Syntax_Syntax.Delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor) in
            FStar_Pervasives_Native.Some uu____5095
        | uu____5096 -> FStar_Pervasives_Native.None in
      resolve_in_open_namespaces' env lid
        (fun uu____5102  -> FStar_Pervasives_Native.None)
        (fun uu____5104  -> FStar_Pervasives_Native.None) k_global_def
let find_all_datacons:
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident Prims.list FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___102_5129 =
        match uu___102_5129 with
        | ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_inductive_typ
               (uu____5138,uu____5139,uu____5140,uu____5141,datas,uu____5143);
             FStar_Syntax_Syntax.sigrng = uu____5144;
             FStar_Syntax_Syntax.sigquals = uu____5145;
             FStar_Syntax_Syntax.sigmeta = uu____5146;
             FStar_Syntax_Syntax.sigattrs = uu____5147;_},uu____5148)
            -> FStar_Pervasives_Native.Some datas
        | uu____5163 -> FStar_Pervasives_Native.None in
      resolve_in_open_namespaces' env lid
        (fun uu____5173  -> FStar_Pervasives_Native.None)
        (fun uu____5177  -> FStar_Pervasives_Native.None) k_global_def
let record_cache_aux_with_filter:
  ((Prims.unit -> Prims.unit,Prims.unit -> Prims.unit,Prims.unit ->
                                                        record_or_dc
                                                          Prims.list,
     record_or_dc -> Prims.unit) FStar_Pervasives_Native.tuple4,Prims.unit ->
                                                                  Prims.unit)
    FStar_Pervasives_Native.tuple2
  =
  let record_cache = FStar_Util.mk_ref [[]] in
  let push1 uu____5222 =
    let uu____5223 =
      let uu____5228 =
        let uu____5231 = FStar_ST.op_Bang record_cache in
        FStar_List.hd uu____5231 in
      let uu____5287 = FStar_ST.op_Bang record_cache in uu____5228 ::
        uu____5287 in
    FStar_ST.op_Colon_Equals record_cache uu____5223 in
  let pop1 uu____5395 =
    let uu____5396 =
      let uu____5401 = FStar_ST.op_Bang record_cache in
      FStar_List.tl uu____5401 in
    FStar_ST.op_Colon_Equals record_cache uu____5396 in
  let peek1 uu____5511 =
    let uu____5512 = FStar_ST.op_Bang record_cache in
    FStar_List.hd uu____5512 in
  let insert r =
    let uu____5572 =
      let uu____5577 = let uu____5580 = peek1 () in r :: uu____5580 in
      let uu____5583 =
        let uu____5588 = FStar_ST.op_Bang record_cache in
        FStar_List.tl uu____5588 in
      uu____5577 :: uu____5583 in
    FStar_ST.op_Colon_Equals record_cache uu____5572 in
  let filter1 uu____5698 =
    let rc = peek1 () in
    let filtered =
      FStar_List.filter
        (fun r  -> Prims.op_Negation r.is_private_or_abstract) rc in
    let uu____5707 =
      let uu____5712 =
        let uu____5717 = FStar_ST.op_Bang record_cache in
        FStar_List.tl uu____5717 in
      filtered :: uu____5712 in
    FStar_ST.op_Colon_Equals record_cache uu____5707 in
  let aux = (push1, pop1, peek1, insert) in (aux, filter1)
let record_cache_aux:
  (Prims.unit -> Prims.unit,Prims.unit -> Prims.unit,Prims.unit ->
                                                       record_or_dc
                                                         Prims.list,record_or_dc
                                                                    ->
                                                                    Prims.unit)
    FStar_Pervasives_Native.tuple4
  =
  let uu____5891 = record_cache_aux_with_filter in
  match uu____5891 with | (aux,uu____5935) -> aux
let filter_record_cache: Prims.unit -> Prims.unit =
  let uu____5978 = record_cache_aux_with_filter in
  match uu____5978 with | (uu____6005,filter1) -> filter1
let push_record_cache: Prims.unit -> Prims.unit =
  let uu____6049 = record_cache_aux in
  match uu____6049 with | (push1,uu____6071,uu____6072,uu____6073) -> push1
let pop_record_cache: Prims.unit -> Prims.unit =
  let uu____6096 = record_cache_aux in
  match uu____6096 with | (uu____6117,pop1,uu____6119,uu____6120) -> pop1
let peek_record_cache: Prims.unit -> record_or_dc Prims.list =
  let uu____6145 = record_cache_aux in
  match uu____6145 with | (uu____6168,uu____6169,peek1,uu____6171) -> peek1
let insert_record_cache: record_or_dc -> Prims.unit =
  let uu____6194 = record_cache_aux in
  match uu____6194 with | (uu____6215,uu____6216,uu____6217,insert) -> insert
let extract_record:
  env ->
    scope_mod Prims.list FStar_ST.ref ->
      FStar_Syntax_Syntax.sigelt -> Prims.unit
  =
  fun e  ->
    fun new_globs  ->
      fun se  ->
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_bundle (sigs,uu____6279) ->
            let is_record =
              FStar_Util.for_some
                (fun uu___103_6295  ->
                   match uu___103_6295 with
                   | FStar_Syntax_Syntax.RecordType uu____6296 -> true
                   | FStar_Syntax_Syntax.RecordConstructor uu____6305 -> true
                   | uu____6314 -> false) in
            let find_dc dc =
              FStar_All.pipe_right sigs
                (FStar_Util.find_opt
                   (fun uu___104_6336  ->
                      match uu___104_6336 with
                      | {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_datacon
                            (lid,uu____6338,uu____6339,uu____6340,uu____6341,uu____6342);
                          FStar_Syntax_Syntax.sigrng = uu____6343;
                          FStar_Syntax_Syntax.sigquals = uu____6344;
                          FStar_Syntax_Syntax.sigmeta = uu____6345;
                          FStar_Syntax_Syntax.sigattrs = uu____6346;_} ->
                          FStar_Ident.lid_equals dc lid
                      | uu____6355 -> false)) in
            FStar_All.pipe_right sigs
              (FStar_List.iter
                 (fun uu___105_6390  ->
                    match uu___105_6390 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ
                          (typename,univs1,parms,uu____6394,uu____6395,dc::[]);
                        FStar_Syntax_Syntax.sigrng = uu____6397;
                        FStar_Syntax_Syntax.sigquals = typename_quals;
                        FStar_Syntax_Syntax.sigmeta = uu____6399;
                        FStar_Syntax_Syntax.sigattrs = uu____6400;_} ->
                        let uu____6411 =
                          let uu____6412 = find_dc dc in
                          FStar_All.pipe_left FStar_Util.must uu____6412 in
                        (match uu____6411 with
                         | {
                             FStar_Syntax_Syntax.sigel =
                               FStar_Syntax_Syntax.Sig_datacon
                               (constrname,uu____6418,t,uu____6420,uu____6421,uu____6422);
                             FStar_Syntax_Syntax.sigrng = uu____6423;
                             FStar_Syntax_Syntax.sigquals = uu____6424;
                             FStar_Syntax_Syntax.sigmeta = uu____6425;
                             FStar_Syntax_Syntax.sigattrs = uu____6426;_} ->
                             let uu____6435 =
                               FStar_Syntax_Util.arrow_formals t in
                             (match uu____6435 with
                              | (formals,uu____6449) ->
                                  let is_rec = is_record typename_quals in
                                  let formals' =
                                    FStar_All.pipe_right formals
                                      (FStar_List.collect
                                         (fun uu____6498  ->
                                            match uu____6498 with
                                            | (x,q) ->
                                                let uu____6511 =
                                                  (FStar_Syntax_Syntax.is_null_bv
                                                     x)
                                                    ||
                                                    (is_rec &&
                                                       (FStar_Syntax_Syntax.is_implicit
                                                          q)) in
                                                if uu____6511
                                                then []
                                                else [(x, q)])) in
                                  let fields' =
                                    FStar_All.pipe_right formals'
                                      (FStar_List.map
                                         (fun uu____6568  ->
                                            match uu____6568 with
                                            | (x,q) ->
                                                let uu____6581 =
                                                  if is_rec
                                                  then
                                                    FStar_Syntax_Util.unmangle_field_name
                                                      x.FStar_Syntax_Syntax.ppname
                                                  else
                                                    x.FStar_Syntax_Syntax.ppname in
                                                (uu____6581,
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
                                  ((let uu____6596 =
                                      let uu____6599 =
                                        FStar_ST.op_Bang new_globs in
                                      (Record_or_dc record) :: uu____6599 in
                                    FStar_ST.op_Colon_Equals new_globs
                                      uu____6596);
                                   (match () with
                                    | () ->
                                        ((let add_field uu____6702 =
                                            match uu____6702 with
                                            | (id1,uu____6710) ->
                                                let modul =
                                                  let uu____6716 =
                                                    FStar_Ident.lid_of_ids
                                                      constrname.FStar_Ident.ns in
                                                  uu____6716.FStar_Ident.str in
                                                let uu____6717 =
                                                  get_exported_id_set e modul in
                                                (match uu____6717 with
                                                 | FStar_Pervasives_Native.Some
                                                     my_ex ->
                                                     let my_exported_ids =
                                                       my_ex
                                                         Exported_id_field in
                                                     ((let uu____6748 =
                                                         let uu____6749 =
                                                           FStar_ST.op_Bang
                                                             my_exported_ids in
                                                         FStar_Util.set_add
                                                           id1.FStar_Ident.idText
                                                           uu____6749 in
                                                       FStar_ST.op_Colon_Equals
                                                         my_exported_ids
                                                         uu____6748);
                                                      (match () with
                                                       | () ->
                                                           let projname =
                                                             let uu____6835 =
                                                               let uu____6836
                                                                 =
                                                                 FStar_Syntax_Util.mk_field_projector_name_from_ident
                                                                   constrname
                                                                   id1 in
                                                               uu____6836.FStar_Ident.ident in
                                                             uu____6835.FStar_Ident.idText in
                                                           let uu____6838 =
                                                             let uu____6839 =
                                                               FStar_ST.op_Bang
                                                                 my_exported_ids in
                                                             FStar_Util.set_add
                                                               projname
                                                               uu____6839 in
                                                           FStar_ST.op_Colon_Equals
                                                             my_exported_ids
                                                             uu____6838))
                                                 | FStar_Pervasives_Native.None
                                                      -> ()) in
                                          FStar_List.iter add_field fields');
                                         (match () with
                                          | () -> insert_record_cache record)))))
                         | uu____6934 -> ())
                    | uu____6935 -> ()))
        | uu____6936 -> ()
let try_lookup_record_or_dc_by_field_name:
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option =
  fun env  ->
    fun fieldname  ->
      let find_in_cache fieldname1 =
        let uu____6951 =
          ((fieldname1.FStar_Ident.ns), (fieldname1.FStar_Ident.ident)) in
        match uu____6951 with
        | (ns,id1) ->
            let uu____6968 = peek_record_cache () in
            FStar_Util.find_map uu____6968
              (fun record  ->
                 let uu____6974 =
                   find_in_record ns id1 record (fun r  -> Cont_ok r) in
                 option_of_cont
                   (fun uu____6980  -> FStar_Pervasives_Native.None)
                   uu____6974) in
      resolve_in_open_namespaces'' env fieldname Exported_id_field
        (fun uu____6982  -> Cont_ignore) (fun uu____6984  -> Cont_ignore)
        (fun r  -> Cont_ok r)
        (fun fn  ->
           let uu____6990 = find_in_cache fn in
           cont_of_option Cont_ignore uu____6990)
        (fun k  -> fun uu____6996  -> k)
let try_lookup_record_by_field_name:
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option =
  fun env  ->
    fun fieldname  ->
      let uu____7007 = try_lookup_record_or_dc_by_field_name env fieldname in
      match uu____7007 with
      | FStar_Pervasives_Native.Some r when r.is_record ->
          FStar_Pervasives_Native.Some r
      | uu____7013 -> FStar_Pervasives_Native.None
let belongs_to_record:
  env -> FStar_Ident.lident -> record_or_dc -> Prims.bool =
  fun env  ->
    fun lid  ->
      fun record  ->
        let uu____7025 = try_lookup_record_by_field_name env lid in
        match uu____7025 with
        | FStar_Pervasives_Native.Some record' when
            let uu____7029 =
              let uu____7030 =
                FStar_Ident.path_of_ns (record.typename).FStar_Ident.ns in
              FStar_Ident.text_of_path uu____7030 in
            let uu____7033 =
              let uu____7034 =
                FStar_Ident.path_of_ns (record'.typename).FStar_Ident.ns in
              FStar_Ident.text_of_path uu____7034 in
            uu____7029 = uu____7033 ->
            let uu____7037 =
              find_in_record (record.typename).FStar_Ident.ns
                lid.FStar_Ident.ident record (fun uu____7041  -> Cont_ok ()) in
            (match uu____7037 with
             | Cont_ok uu____7042 -> true
             | uu____7043 -> false)
        | uu____7046 -> false
let try_lookup_dc_by_field_name:
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident,Prims.bool) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option
  =
  fun env  ->
    fun fieldname  ->
      let uu____7061 = try_lookup_record_or_dc_by_field_name env fieldname in
      match uu____7061 with
      | FStar_Pervasives_Native.Some r ->
          let uu____7071 =
            let uu____7076 =
              let uu____7077 =
                FStar_Ident.lid_of_ids
                  (FStar_List.append (r.typename).FStar_Ident.ns
                     [r.constrname]) in
              FStar_Ident.set_lid_range uu____7077
                (FStar_Ident.range_of_lid fieldname) in
            (uu____7076, (r.is_record)) in
          FStar_Pervasives_Native.Some uu____7071
      | uu____7082 -> FStar_Pervasives_Native.None
let string_set_ref_new:
  Prims.unit -> Prims.string FStar_Util.set FStar_ST.ref =
  fun uu____7106  ->
    let uu____7107 = FStar_Util.new_set FStar_Util.compare in
    FStar_Util.mk_ref uu____7107
let exported_id_set_new:
  Prims.unit -> exported_id_kind -> Prims.string FStar_Util.set FStar_ST.ref
  =
  fun uu____7131  ->
    let term_type_set = string_set_ref_new () in
    let field_set = string_set_ref_new () in
    fun uu___106_7142  ->
      match uu___106_7142 with
      | Exported_id_term_type  -> term_type_set
      | Exported_id_field  -> field_set
let unique:
  Prims.bool -> Prims.bool -> env -> FStar_Ident.lident -> Prims.bool =
  fun any_val  ->
    fun exclude_interface  ->
      fun env  ->
        fun lid  ->
          let filter_scope_mods uu___107_7184 =
            match uu___107_7184 with
            | Rec_binding uu____7185 -> true
            | uu____7186 -> false in
          let this_env =
            let uu___121_7188 = env in
            let uu____7189 =
              FStar_List.filter filter_scope_mods env.scope_mods in
            {
              curmodule = (uu___121_7188.curmodule);
              curmonad = (uu___121_7188.curmonad);
              modules = (uu___121_7188.modules);
              scope_mods = uu____7189;
              exported_ids = empty_exported_id_smap;
              trans_exported_ids = (uu___121_7188.trans_exported_ids);
              includes = empty_include_smap;
              sigaccum = (uu___121_7188.sigaccum);
              sigmap = (uu___121_7188.sigmap);
              iface = (uu___121_7188.iface);
              admitted_iface = (uu___121_7188.admitted_iface);
              expect_typ = (uu___121_7188.expect_typ);
              docs = (uu___121_7188.docs);
              remaining_iface_decls = (uu___121_7188.remaining_iface_decls);
              syntax_only = (uu___121_7188.syntax_only);
              ds_hooks = (uu___121_7188.ds_hooks)
            } in
          let uu____7192 =
            try_lookup_lid' any_val exclude_interface this_env lid in
          match uu____7192 with
          | FStar_Pervasives_Native.None  -> true
          | FStar_Pervasives_Native.Some uu____7203 -> false
let push_scope_mod: env -> scope_mod -> env =
  fun env  ->
    fun scope_mod  ->
      let uu___122_7218 = env in
      {
        curmodule = (uu___122_7218.curmodule);
        curmonad = (uu___122_7218.curmonad);
        modules = (uu___122_7218.modules);
        scope_mods = (scope_mod :: (env.scope_mods));
        exported_ids = (uu___122_7218.exported_ids);
        trans_exported_ids = (uu___122_7218.trans_exported_ids);
        includes = (uu___122_7218.includes);
        sigaccum = (uu___122_7218.sigaccum);
        sigmap = (uu___122_7218.sigmap);
        iface = (uu___122_7218.iface);
        admitted_iface = (uu___122_7218.admitted_iface);
        expect_typ = (uu___122_7218.expect_typ);
        docs = (uu___122_7218.docs);
        remaining_iface_decls = (uu___122_7218.remaining_iface_decls);
        syntax_only = (uu___122_7218.syntax_only);
        ds_hooks = (uu___122_7218.ds_hooks)
      }
let push_bv':
  env ->
    FStar_Ident.ident ->
      Prims.bool ->
        (env,FStar_Syntax_Syntax.bv) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun x  ->
      fun is_mutable  ->
        let bv =
          FStar_Syntax_Syntax.gen_bv x.FStar_Ident.idText
            (FStar_Pervasives_Native.Some (x.FStar_Ident.idRange))
            FStar_Syntax_Syntax.tun in
        ((push_scope_mod env (Local_binding (x, bv, is_mutable))), bv)
let push_bv_mutable:
  env ->
    FStar_Ident.ident ->
      (env,FStar_Syntax_Syntax.bv) FStar_Pervasives_Native.tuple2
  = fun env  -> fun x  -> push_bv' env x true
let push_bv:
  env ->
    FStar_Ident.ident ->
      (env,FStar_Syntax_Syntax.bv) FStar_Pervasives_Native.tuple2
  = fun env  -> fun x  -> push_bv' env x false
let push_top_level_rec_binding:
  env -> FStar_Ident.ident -> FStar_Syntax_Syntax.delta_depth -> env =
  fun env  ->
    fun x  ->
      fun dd  ->
        let l = qualify env x in
        let uu____7263 =
          (unique false true env l) || (FStar_Options.interactive ()) in
        if uu____7263
        then push_scope_mod env (Rec_binding (x, l, dd))
        else
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_DuplicateTopLevelNames,
              (Prims.strcat "Duplicate top-level names " l.FStar_Ident.str))
            (FStar_Ident.range_of_lid l)
let push_sigelt: env -> FStar_Syntax_Syntax.sigelt -> env =
  fun env  ->
    fun s  ->
      let err l =
        let sopt = FStar_Util.smap_try_find (sigmap env) l.FStar_Ident.str in
        let r =
          match sopt with
          | FStar_Pervasives_Native.Some (se,uu____7288) ->
              let uu____7293 =
                FStar_Util.find_opt (FStar_Ident.lid_equals l)
                  (FStar_Syntax_Util.lids_of_sigelt se) in
              (match uu____7293 with
               | FStar_Pervasives_Native.Some l1 ->
                   FStar_All.pipe_left FStar_Range.string_of_range
                     (FStar_Ident.range_of_lid l1)
               | FStar_Pervasives_Native.None  -> "<unknown>")
          | FStar_Pervasives_Native.None  -> "<unknown>" in
        let uu____7301 =
          let uu____7306 =
            FStar_Util.format2
              "Duplicate top-level names [%s]; previously declared at %s"
              (FStar_Ident.text_of_lid l) r in
          (FStar_Errors.Fatal_DuplicateTopLevelNames, uu____7306) in
        FStar_Errors.raise_error uu____7301 (FStar_Ident.range_of_lid l) in
      let globals = FStar_Util.mk_ref env.scope_mods in
      let env1 =
        let uu____7315 =
          match s.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let uu____7324 -> (false, true)
          | FStar_Syntax_Syntax.Sig_bundle uu____7331 -> (false, true)
          | uu____7340 -> (false, false) in
        match uu____7315 with
        | (any_val,exclude_interface) ->
            let lids = FStar_Syntax_Util.lids_of_sigelt s in
            let uu____7346 =
              FStar_Util.find_map lids
                (fun l  ->
                   let uu____7352 =
                     let uu____7353 = unique any_val exclude_interface env l in
                     Prims.op_Negation uu____7353 in
                   if uu____7352
                   then FStar_Pervasives_Native.Some l
                   else FStar_Pervasives_Native.None) in
            (match uu____7346 with
             | FStar_Pervasives_Native.Some l -> err l
             | uu____7358 ->
                 (extract_record env globals s;
                  (let uu___123_7384 = env in
                   {
                     curmodule = (uu___123_7384.curmodule);
                     curmonad = (uu___123_7384.curmonad);
                     modules = (uu___123_7384.modules);
                     scope_mods = (uu___123_7384.scope_mods);
                     exported_ids = (uu___123_7384.exported_ids);
                     trans_exported_ids = (uu___123_7384.trans_exported_ids);
                     includes = (uu___123_7384.includes);
                     sigaccum = (s :: (env.sigaccum));
                     sigmap = (uu___123_7384.sigmap);
                     iface = (uu___123_7384.iface);
                     admitted_iface = (uu___123_7384.admitted_iface);
                     expect_typ = (uu___123_7384.expect_typ);
                     docs = (uu___123_7384.docs);
                     remaining_iface_decls =
                       (uu___123_7384.remaining_iface_decls);
                     syntax_only = (uu___123_7384.syntax_only);
                     ds_hooks = (uu___123_7384.ds_hooks)
                   }))) in
      let env2 =
        let uu___124_7386 = env1 in
        let uu____7387 = FStar_ST.op_Bang globals in
        {
          curmodule = (uu___124_7386.curmodule);
          curmonad = (uu___124_7386.curmonad);
          modules = (uu___124_7386.modules);
          scope_mods = uu____7387;
          exported_ids = (uu___124_7386.exported_ids);
          trans_exported_ids = (uu___124_7386.trans_exported_ids);
          includes = (uu___124_7386.includes);
          sigaccum = (uu___124_7386.sigaccum);
          sigmap = (uu___124_7386.sigmap);
          iface = (uu___124_7386.iface);
          admitted_iface = (uu___124_7386.admitted_iface);
          expect_typ = (uu___124_7386.expect_typ);
          docs = (uu___124_7386.docs);
          remaining_iface_decls = (uu___124_7386.remaining_iface_decls);
          syntax_only = (uu___124_7386.syntax_only);
          ds_hooks = (uu___124_7386.ds_hooks)
        } in
      let uu____7435 =
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_bundle (ses,uu____7461) ->
            let uu____7470 =
              FStar_List.map
                (fun se  -> ((FStar_Syntax_Util.lids_of_sigelt se), se)) ses in
            (env2, uu____7470)
        | uu____7497 -> (env2, [((FStar_Syntax_Util.lids_of_sigelt s), s)]) in
      match uu____7435 with
      | (env3,lss) ->
          (FStar_All.pipe_right lss
             (FStar_List.iter
                (fun uu____7556  ->
                   match uu____7556 with
                   | (lids,se) ->
                       FStar_All.pipe_right lids
                         (FStar_List.iter
                            (fun lid  ->
                               (let uu____7578 =
                                  let uu____7581 = FStar_ST.op_Bang globals in
                                  (Top_level_def (lid.FStar_Ident.ident)) ::
                                    uu____7581 in
                                FStar_ST.op_Colon_Equals globals uu____7578);
                               (match () with
                                | () ->
                                    let modul =
                                      let uu____7675 =
                                        FStar_Ident.lid_of_ids
                                          lid.FStar_Ident.ns in
                                      uu____7675.FStar_Ident.str in
                                    ((let uu____7677 =
                                        get_exported_id_set env3 modul in
                                      match uu____7677 with
                                      | FStar_Pervasives_Native.Some f ->
                                          let my_exported_ids =
                                            f Exported_id_term_type in
                                          let uu____7707 =
                                            let uu____7708 =
                                              FStar_ST.op_Bang
                                                my_exported_ids in
                                            FStar_Util.set_add
                                              (lid.FStar_Ident.ident).FStar_Ident.idText
                                              uu____7708 in
                                          FStar_ST.op_Colon_Equals
                                            my_exported_ids uu____7707
                                      | FStar_Pervasives_Native.None  -> ());
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
              let uu___125_7803 = env3 in
              let uu____7804 = FStar_ST.op_Bang globals in
              {
                curmodule = (uu___125_7803.curmodule);
                curmonad = (uu___125_7803.curmonad);
                modules = (uu___125_7803.modules);
                scope_mods = uu____7804;
                exported_ids = (uu___125_7803.exported_ids);
                trans_exported_ids = (uu___125_7803.trans_exported_ids);
                includes = (uu___125_7803.includes);
                sigaccum = (uu___125_7803.sigaccum);
                sigmap = (uu___125_7803.sigmap);
                iface = (uu___125_7803.iface);
                admitted_iface = (uu___125_7803.admitted_iface);
                expect_typ = (uu___125_7803.expect_typ);
                docs = (uu___125_7803.docs);
                remaining_iface_decls = (uu___125_7803.remaining_iface_decls);
                syntax_only = (uu___125_7803.syntax_only);
                ds_hooks = (uu___125_7803.ds_hooks)
              } in
            env4))
let push_namespace: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun ns  ->
      let uu____7858 =
        let uu____7863 = resolve_module_name env ns false in
        match uu____7863 with
        | FStar_Pervasives_Native.None  ->
            let modules = env.modules in
            let uu____7877 =
              FStar_All.pipe_right modules
                (FStar_Util.for_some
                   (fun uu____7891  ->
                      match uu____7891 with
                      | (m,uu____7897) ->
                          FStar_Util.starts_with
                            (Prims.strcat (FStar_Ident.text_of_lid m) ".")
                            (Prims.strcat (FStar_Ident.text_of_lid ns) "."))) in
            if uu____7877
            then (ns, Open_namespace)
            else
              (let uu____7903 =
                 let uu____7908 =
                   FStar_Util.format1 "Namespace %s cannot be found"
                     (FStar_Ident.text_of_lid ns) in
                 (FStar_Errors.Fatal_NameSpaceNotFound, uu____7908) in
               FStar_Errors.raise_error uu____7903
                 (FStar_Ident.range_of_lid ns))
        | FStar_Pervasives_Native.Some ns' ->
            (fail_if_curmodule env ns ns'; (ns', Open_module)) in
      match uu____7858 with
      | (ns',kd) ->
          ((env.ds_hooks).ds_push_open_hook env (ns', kd);
           push_scope_mod env (Open_module_or_namespace (ns', kd)))
let push_include: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun ns  ->
      let ns0 = ns in
      let uu____7925 = resolve_module_name env ns false in
      match uu____7925 with
      | FStar_Pervasives_Native.Some ns1 ->
          ((env.ds_hooks).ds_push_include_hook env ns1;
           fail_if_curmodule env ns0 ns1;
           (let env1 =
              push_scope_mod env
                (Open_module_or_namespace (ns1, Open_module)) in
            let curmod =
              let uu____7933 = current_module env1 in
              uu____7933.FStar_Ident.str in
            (let uu____7935 = FStar_Util.smap_try_find env1.includes curmod in
             match uu____7935 with
             | FStar_Pervasives_Native.None  -> ()
             | FStar_Pervasives_Native.Some incl ->
                 let uu____7959 =
                   let uu____7962 = FStar_ST.op_Bang incl in ns1 ::
                     uu____7962 in
                 FStar_ST.op_Colon_Equals incl uu____7959);
            (match () with
             | () ->
                 let uu____8055 =
                   get_trans_exported_id_set env1 ns1.FStar_Ident.str in
                 (match uu____8055 with
                  | FStar_Pervasives_Native.Some ns_trans_exports ->
                      ((let uu____8072 =
                          let uu____8089 = get_exported_id_set env1 curmod in
                          let uu____8096 =
                            get_trans_exported_id_set env1 curmod in
                          (uu____8089, uu____8096) in
                        match uu____8072 with
                        | (FStar_Pervasives_Native.Some
                           cur_exports,FStar_Pervasives_Native.Some
                           cur_trans_exports) ->
                            let update_exports k =
                              let ns_ex =
                                let uu____8150 = ns_trans_exports k in
                                FStar_ST.op_Bang uu____8150 in
                              let ex = cur_exports k in
                              (let uu____8276 =
                                 let uu____8277 = FStar_ST.op_Bang ex in
                                 FStar_Util.set_difference uu____8277 ns_ex in
                               FStar_ST.op_Colon_Equals ex uu____8276);
                              (match () with
                               | () ->
                                   let trans_ex = cur_trans_exports k in
                                   let uu____8377 =
                                     let uu____8378 =
                                       FStar_ST.op_Bang trans_ex in
                                     FStar_Util.set_union uu____8378 ns_ex in
                                   FStar_ST.op_Colon_Equals trans_ex
                                     uu____8377) in
                            FStar_List.iter update_exports
                              all_exported_id_kinds
                        | uu____8463 -> ());
                       (match () with | () -> env1))
                  | FStar_Pervasives_Native.None  ->
                      let uu____8484 =
                        let uu____8489 =
                          FStar_Util.format1
                            "include: Module %s was not prepared"
                            ns1.FStar_Ident.str in
                        (FStar_Errors.Fatal_IncludeModuleNotPrepared,
                          uu____8489) in
                      FStar_Errors.raise_error uu____8484
                        (FStar_Ident.range_of_lid ns1)))))
      | uu____8490 ->
          let uu____8493 =
            let uu____8498 =
              FStar_Util.format1 "include: Module %s cannot be found"
                ns.FStar_Ident.str in
            (FStar_Errors.Fatal_ModuleNotFound, uu____8498) in
          FStar_Errors.raise_error uu____8493 (FStar_Ident.range_of_lid ns)
let push_module_abbrev: env -> FStar_Ident.ident -> FStar_Ident.lident -> env
  =
  fun env  ->
    fun x  ->
      fun l  ->
        let uu____8508 = module_is_defined env l in
        if uu____8508
        then
          (fail_if_curmodule env l l;
           (env.ds_hooks).ds_push_module_abbrev_hook env x l;
           push_scope_mod env (Module_abbrev (x, l)))
        else
          (let uu____8512 =
             let uu____8517 =
               FStar_Util.format1 "Module %s cannot be found"
                 (FStar_Ident.text_of_lid l) in
             (FStar_Errors.Fatal_ModuleNotFound, uu____8517) in
           FStar_Errors.raise_error uu____8512 (FStar_Ident.range_of_lid l))
let push_doc:
  env ->
    FStar_Ident.lident ->
      FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option -> env
  =
  fun env  ->
    fun l  ->
      fun doc_opt  ->
        match doc_opt with
        | FStar_Pervasives_Native.None  -> env
        | FStar_Pervasives_Native.Some doc1 ->
            ((let uu____8533 =
                FStar_Util.smap_try_find env.docs l.FStar_Ident.str in
              match uu____8533 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some old_doc ->
                  let uu____8537 =
                    let uu____8542 =
                      let uu____8543 = FStar_Ident.string_of_lid l in
                      let uu____8544 =
                        FStar_Parser_AST.string_of_fsdoc old_doc in
                      let uu____8545 = FStar_Parser_AST.string_of_fsdoc doc1 in
                      FStar_Util.format3
                        "Overwriting doc of %s; old doc was [%s]; new doc are [%s]"
                        uu____8543 uu____8544 uu____8545 in
                    (FStar_Errors.Warning_DocOverwrite, uu____8542) in
                  FStar_Errors.log_issue (FStar_Ident.range_of_lid l)
                    uu____8537);
             FStar_Util.smap_add env.docs l.FStar_Ident.str doc1;
             env)
let check_admits: env -> Prims.unit =
  fun env  ->
    FStar_All.pipe_right env.sigaccum
      (FStar_List.iter
         (fun se  ->
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t) ->
                let uu____8561 = try_lookup_lid env l in
                (match uu____8561 with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____8573 =
                         let uu____8574 = FStar_Options.interactive () in
                         Prims.op_Negation uu____8574 in
                       if uu____8573
                       then
                         let uu____8575 =
                           let uu____8580 =
                             let uu____8581 =
                               FStar_Syntax_Print.lid_to_string l in
                             FStar_Util.format1
                               "Admitting %s without a definition" uu____8581 in
                           (FStar_Errors.Warning_AdmitWithoutDefinition,
                             uu____8580) in
                         FStar_Errors.log_issue (FStar_Ident.range_of_lid l)
                           uu____8575
                       else ());
                      (let quals = FStar_Syntax_Syntax.Assumption ::
                         (se.FStar_Syntax_Syntax.sigquals) in
                       FStar_Util.smap_add (sigmap env) l.FStar_Ident.str
                         ((let uu___126_8591 = se in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (uu___126_8591.FStar_Syntax_Syntax.sigel);
                             FStar_Syntax_Syntax.sigrng =
                               (uu___126_8591.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals = quals;
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___126_8591.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___126_8591.FStar_Syntax_Syntax.sigattrs)
                           }), false)))
                 | FStar_Pervasives_Native.Some uu____8592 -> ())
            | uu____8601 -> ()))
let finish: env -> FStar_Syntax_Syntax.modul -> env =
  fun env  ->
    fun modul  ->
      FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations
        (FStar_List.iter
           (fun se  ->
              let quals = se.FStar_Syntax_Syntax.sigquals in
              match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_bundle (ses,uu____8618) ->
                  if
                    (FStar_List.contains FStar_Syntax_Syntax.Private quals)
                      ||
                      (FStar_List.contains FStar_Syntax_Syntax.Abstract quals)
                  then
                    FStar_All.pipe_right ses
                      (FStar_List.iter
                         (fun se1  ->
                            match se1.FStar_Syntax_Syntax.sigel with
                            | FStar_Syntax_Syntax.Sig_datacon
                                (lid,uu____8638,uu____8639,uu____8640,uu____8641,uu____8642)
                                ->
                                FStar_Util.smap_remove (sigmap env)
                                  lid.FStar_Ident.str
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (lid,univ_names,binders,typ,uu____8655,uu____8656)
                                ->
                                (FStar_Util.smap_remove (sigmap env)
                                   lid.FStar_Ident.str;
                                 if
                                   Prims.op_Negation
                                     (FStar_List.contains
                                        FStar_Syntax_Syntax.Private quals)
                                 then
                                   (let sigel =
                                      let uu____8671 =
                                        let uu____8678 =
                                          let uu____8681 =
                                            let uu____8684 =
                                              let uu____8685 =
                                                let uu____8698 =
                                                  FStar_Syntax_Syntax.mk_Total
                                                    typ in
                                                (binders, uu____8698) in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____8685 in
                                            FStar_Syntax_Syntax.mk uu____8684 in
                                          uu____8681
                                            FStar_Pervasives_Native.None
                                            (FStar_Ident.range_of_lid lid) in
                                        (lid, univ_names, uu____8678) in
                                      FStar_Syntax_Syntax.Sig_declare_typ
                                        uu____8671 in
                                    let se2 =
                                      let uu___127_8705 = se1 in
                                      {
                                        FStar_Syntax_Syntax.sigel = sigel;
                                        FStar_Syntax_Syntax.sigrng =
                                          (uu___127_8705.FStar_Syntax_Syntax.sigrng);
                                        FStar_Syntax_Syntax.sigquals =
                                          (FStar_Syntax_Syntax.Assumption ::
                                          quals);
                                        FStar_Syntax_Syntax.sigmeta =
                                          (uu___127_8705.FStar_Syntax_Syntax.sigmeta);
                                        FStar_Syntax_Syntax.sigattrs =
                                          (uu___127_8705.FStar_Syntax_Syntax.sigattrs)
                                      } in
                                    FStar_Util.smap_add (sigmap env)
                                      lid.FStar_Ident.str (se2, false))
                                 else ())
                            | uu____8711 -> ()))
                  else ()
              | FStar_Syntax_Syntax.Sig_declare_typ
                  (lid,uu____8714,uu____8715) ->
                  if FStar_List.contains FStar_Syntax_Syntax.Private quals
                  then
                    FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str
                  else ()
              | FStar_Syntax_Syntax.Sig_let ((uu____8721,lbs),uu____8723) ->
                  (if
                     (FStar_List.contains FStar_Syntax_Syntax.Private quals)
                       ||
                       (FStar_List.contains FStar_Syntax_Syntax.Abstract
                          quals)
                   then
                     FStar_All.pipe_right lbs
                       (FStar_List.iter
                          (fun lb  ->
                             let uu____8744 =
                               let uu____8745 =
                                 let uu____8746 =
                                   let uu____8749 =
                                     FStar_Util.right
                                       lb.FStar_Syntax_Syntax.lbname in
                                   uu____8749.FStar_Syntax_Syntax.fv_name in
                                 uu____8746.FStar_Syntax_Syntax.v in
                               uu____8745.FStar_Ident.str in
                             FStar_Util.smap_remove (sigmap env) uu____8744))
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
                          (fun lb  ->
                             let lid =
                               let uu____8763 =
                                 let uu____8766 =
                                   FStar_Util.right
                                     lb.FStar_Syntax_Syntax.lbname in
                                 uu____8766.FStar_Syntax_Syntax.fv_name in
                               uu____8763.FStar_Syntax_Syntax.v in
                             let quals1 = FStar_Syntax_Syntax.Assumption ::
                               quals in
                             let decl =
                               let uu___128_8771 = se in
                               {
                                 FStar_Syntax_Syntax.sigel =
                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                      (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                        (lb.FStar_Syntax_Syntax.lbtyp)));
                                 FStar_Syntax_Syntax.sigrng =
                                   (uu___128_8771.FStar_Syntax_Syntax.sigrng);
                                 FStar_Syntax_Syntax.sigquals = quals1;
                                 FStar_Syntax_Syntax.sigmeta =
                                   (uu___128_8771.FStar_Syntax_Syntax.sigmeta);
                                 FStar_Syntax_Syntax.sigattrs =
                                   (uu___128_8771.FStar_Syntax_Syntax.sigattrs)
                               } in
                             FStar_Util.smap_add (sigmap env)
                               lid.FStar_Ident.str (decl, false)))
                   else ())
              | uu____8781 -> ()));
      (let curmod =
         let uu____8783 = current_module env in uu____8783.FStar_Ident.str in
       (let uu____8785 =
          let uu____8802 = get_exported_id_set env curmod in
          let uu____8809 = get_trans_exported_id_set env curmod in
          (uu____8802, uu____8809) in
        match uu____8785 with
        | (FStar_Pervasives_Native.Some cur_ex,FStar_Pervasives_Native.Some
           cur_trans_ex) ->
            let update_exports eikind =
              let cur_ex_set =
                let uu____8863 = cur_ex eikind in FStar_ST.op_Bang uu____8863 in
              let cur_trans_ex_set_ref = cur_trans_ex eikind in
              let uu____8988 =
                let uu____8989 = FStar_ST.op_Bang cur_trans_ex_set_ref in
                FStar_Util.set_union cur_ex_set uu____8989 in
              FStar_ST.op_Colon_Equals cur_trans_ex_set_ref uu____8988 in
            FStar_List.iter update_exports all_exported_id_kinds
        | uu____9074 -> ());
       (match () with
        | () ->
            (filter_record_cache ();
             (match () with
              | () ->
                  let uu___129_9092 = env in
                  {
                    curmodule = FStar_Pervasives_Native.None;
                    curmonad = (uu___129_9092.curmonad);
                    modules = (((modul.FStar_Syntax_Syntax.name), modul) ::
                      (env.modules));
                    scope_mods = [];
                    exported_ids = (uu___129_9092.exported_ids);
                    trans_exported_ids = (uu___129_9092.trans_exported_ids);
                    includes = (uu___129_9092.includes);
                    sigaccum = [];
                    sigmap = (uu___129_9092.sigmap);
                    iface = (uu___129_9092.iface);
                    admitted_iface = (uu___129_9092.admitted_iface);
                    expect_typ = (uu___129_9092.expect_typ);
                    docs = (uu___129_9092.docs);
                    remaining_iface_decls =
                      (uu___129_9092.remaining_iface_decls);
                    syntax_only = (uu___129_9092.syntax_only);
                    ds_hooks = (uu___129_9092.ds_hooks)
                  }))))
let stack: env Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let push: env -> env =
  fun env  ->
    push_record_cache ();
    (let uu____9119 =
       let uu____9122 = FStar_ST.op_Bang stack in env :: uu____9122 in
     FStar_ST.op_Colon_Equals stack uu____9119);
    (let uu___130_9171 = env in
     let uu____9172 = FStar_Util.smap_copy (sigmap env) in
     let uu____9183 = FStar_Util.smap_copy env.docs in
     {
       curmodule = (uu___130_9171.curmodule);
       curmonad = (uu___130_9171.curmonad);
       modules = (uu___130_9171.modules);
       scope_mods = (uu___130_9171.scope_mods);
       exported_ids = (uu___130_9171.exported_ids);
       trans_exported_ids = (uu___130_9171.trans_exported_ids);
       includes = (uu___130_9171.includes);
       sigaccum = (uu___130_9171.sigaccum);
       sigmap = uu____9172;
       iface = (uu___130_9171.iface);
       admitted_iface = (uu___130_9171.admitted_iface);
       expect_typ = (uu___130_9171.expect_typ);
       docs = uu____9183;
       remaining_iface_decls = (uu___130_9171.remaining_iface_decls);
       syntax_only = (uu___130_9171.syntax_only);
       ds_hooks = (uu___130_9171.ds_hooks)
     })
let pop: Prims.unit -> env =
  fun uu____9188  ->
    let uu____9189 = FStar_ST.op_Bang stack in
    match uu____9189 with
    | env::tl1 ->
        (pop_record_cache (); FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____9244 -> failwith "Impossible: Too many pops"
let export_interface: FStar_Ident.lident -> env -> env =
  fun m  ->
    fun env  ->
      let sigelt_in_m se =
        match FStar_Syntax_Util.lids_of_sigelt se with
        | l::uu____9258 -> l.FStar_Ident.nsstr = m.FStar_Ident.str
        | uu____9261 -> false in
      let sm = sigmap env in
      let env1 = pop () in
      let keys = FStar_Util.smap_keys sm in
      let sm' = sigmap env1 in
      FStar_All.pipe_right keys
        (FStar_List.iter
           (fun k  ->
              let uu____9295 = FStar_Util.smap_try_find sm' k in
              match uu____9295 with
              | FStar_Pervasives_Native.Some (se,true ) when sigelt_in_m se
                  ->
                  (FStar_Util.smap_remove sm' k;
                   (let se1 =
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t) ->
                          let uu___131_9320 = se in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (uu___131_9320.FStar_Syntax_Syntax.sigel);
                            FStar_Syntax_Syntax.sigrng =
                              (uu___131_9320.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (FStar_Syntax_Syntax.Assumption ::
                              (se.FStar_Syntax_Syntax.sigquals));
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___131_9320.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___131_9320.FStar_Syntax_Syntax.sigattrs)
                          }
                      | uu____9321 -> se in
                    FStar_Util.smap_add sm' k (se1, false)))
              | uu____9326 -> ()));
      env1
let finish_module_or_interface: env -> FStar_Syntax_Syntax.modul -> env =
  fun env  ->
    fun modul  ->
      if Prims.op_Negation modul.FStar_Syntax_Syntax.is_interface
      then check_admits env
      else ();
      finish env modul
type exported_ids =
  {
  exported_id_terms: Prims.string Prims.list;
  exported_id_fields: Prims.string Prims.list;}[@@deriving show]
let __proj__Mkexported_ids__item__exported_id_terms:
  exported_ids -> Prims.string Prims.list =
  fun projectee  ->
    match projectee with
    | { exported_id_terms = __fname__exported_id_terms;
        exported_id_fields = __fname__exported_id_fields;_} ->
        __fname__exported_id_terms
let __proj__Mkexported_ids__item__exported_id_fields:
  exported_ids -> Prims.string Prims.list =
  fun projectee  ->
    match projectee with
    | { exported_id_terms = __fname__exported_id_terms;
        exported_id_fields = __fname__exported_id_fields;_} ->
        __fname__exported_id_fields
let as_exported_ids: exported_id_set -> exported_ids =
  fun e  ->
    let terms =
      let uu____9418 =
        let uu____9421 = e Exported_id_term_type in
        FStar_ST.op_Bang uu____9421 in
      FStar_Util.set_elements uu____9418 in
    let fields =
      let uu____9535 =
        let uu____9538 = e Exported_id_field in FStar_ST.op_Bang uu____9538 in
      FStar_Util.set_elements uu____9535 in
    { exported_id_terms = terms; exported_id_fields = fields }
let as_exported_id_set:
  exported_ids FStar_Pervasives_Native.option ->
    exported_id_kind -> Prims.string FStar_Util.set FStar_ST.ref
  =
  fun e  ->
    match e with
    | FStar_Pervasives_Native.None  -> exported_id_set_new ()
    | FStar_Pervasives_Native.Some e1 ->
        let terms =
          let uu____9685 =
            FStar_Util.as_set e1.exported_id_terms FStar_Util.compare in
          FStar_Util.mk_ref uu____9685 in
        let fields =
          let uu____9695 =
            FStar_Util.as_set e1.exported_id_fields FStar_Util.compare in
          FStar_Util.mk_ref uu____9695 in
        (fun uu___108_9700  ->
           match uu___108_9700 with
           | Exported_id_term_type  -> terms
           | Exported_id_field  -> fields)
type module_inclusion_info =
  {
  mii_exported_ids: exported_ids FStar_Pervasives_Native.option;
  mii_trans_exported_ids: exported_ids FStar_Pervasives_Native.option;
  mii_includes: FStar_Ident.lident Prims.list FStar_Pervasives_Native.option;}
[@@deriving show]
let __proj__Mkmodule_inclusion_info__item__mii_exported_ids:
  module_inclusion_info -> exported_ids FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { mii_exported_ids = __fname__mii_exported_ids;
        mii_trans_exported_ids = __fname__mii_trans_exported_ids;
        mii_includes = __fname__mii_includes;_} -> __fname__mii_exported_ids
let __proj__Mkmodule_inclusion_info__item__mii_trans_exported_ids:
  module_inclusion_info -> exported_ids FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { mii_exported_ids = __fname__mii_exported_ids;
        mii_trans_exported_ids = __fname__mii_trans_exported_ids;
        mii_includes = __fname__mii_includes;_} ->
        __fname__mii_trans_exported_ids
let __proj__Mkmodule_inclusion_info__item__mii_includes:
  module_inclusion_info ->
    FStar_Ident.lident Prims.list FStar_Pervasives_Native.option
  =
  fun projectee  ->
    match projectee with
    | { mii_exported_ids = __fname__mii_exported_ids;
        mii_trans_exported_ids = __fname__mii_trans_exported_ids;
        mii_includes = __fname__mii_includes;_} -> __fname__mii_includes
let default_mii: module_inclusion_info =
  {
    mii_exported_ids = FStar_Pervasives_Native.None;
    mii_trans_exported_ids = FStar_Pervasives_Native.None;
    mii_includes = FStar_Pervasives_Native.None
  }
let as_includes:
  'Auu____9820 .
    'Auu____9820 Prims.list FStar_Pervasives_Native.option ->
      'Auu____9820 Prims.list FStar_ST.ref
  =
  fun uu___109_9832  ->
    match uu___109_9832 with
    | FStar_Pervasives_Native.None  -> FStar_Util.mk_ref []
    | FStar_Pervasives_Native.Some l -> FStar_Util.mk_ref l
let inclusion_info: env -> FStar_Ident.lident -> module_inclusion_info =
  fun env  ->
    fun l  ->
      let mname = FStar_Ident.string_of_lid l in
      let as_ids_opt m =
        let uu____9865 = FStar_Util.smap_try_find m mname in
        FStar_Util.map_opt uu____9865 as_exported_ids in
      let uu____9868 = as_ids_opt env.exported_ids in
      let uu____9871 = as_ids_opt env.trans_exported_ids in
      let uu____9874 =
        let uu____9879 = FStar_Util.smap_try_find env.includes mname in
        FStar_Util.map_opt uu____9879 (fun r  -> FStar_ST.op_Bang r) in
      {
        mii_exported_ids = uu____9868;
        mii_trans_exported_ids = uu____9871;
        mii_includes = uu____9874
      }
let prepare_module_or_interface:
  Prims.bool ->
    Prims.bool ->
      env ->
        FStar_Ident.lident ->
          module_inclusion_info ->
            (env,Prims.bool) FStar_Pervasives_Native.tuple2
  =
  fun intf  ->
    fun admitted  ->
      fun env  ->
        fun mname  ->
          fun mii  ->
            let prep env1 =
              let filename =
                FStar_Util.strcat (FStar_Ident.text_of_lid mname) ".fst" in
              let auto_open =
                FStar_Parser_Dep.hard_coded_dependencies filename in
              let auto_open1 =
                let convert_kind uu___110_9999 =
                  match uu___110_9999 with
                  | FStar_Parser_Dep.Open_namespace  -> Open_namespace
                  | FStar_Parser_Dep.Open_module  -> Open_module in
                FStar_List.map
                  (fun uu____10011  ->
                     match uu____10011 with
                     | (lid,kind) -> (lid, (convert_kind kind))) auto_open in
              let namespace_of_module =
                if
                  (FStar_List.length mname.FStar_Ident.ns) >
                    (Prims.parse_int "0")
                then
                  let uu____10035 =
                    let uu____10040 =
                      FStar_Ident.lid_of_ids mname.FStar_Ident.ns in
                    (uu____10040, Open_namespace) in
                  [uu____10035]
                else [] in
              let auto_open2 =
                FStar_List.append namespace_of_module
                  (FStar_List.rev auto_open1) in
              (let uu____10070 = as_exported_id_set mii.mii_exported_ids in
               FStar_Util.smap_add env1.exported_ids mname.FStar_Ident.str
                 uu____10070);
              (match () with
               | () ->
                   ((let uu____10094 =
                       as_exported_id_set mii.mii_trans_exported_ids in
                     FStar_Util.smap_add env1.trans_exported_ids
                       mname.FStar_Ident.str uu____10094);
                    (match () with
                     | () ->
                         ((let uu____10118 = as_includes mii.mii_includes in
                           FStar_Util.smap_add env1.includes
                             mname.FStar_Ident.str uu____10118);
                          (match () with
                           | () ->
                               let env' =
                                 let uu___132_10150 = env1 in
                                 let uu____10151 =
                                   FStar_List.map
                                     (fun x  -> Open_module_or_namespace x)
                                     auto_open2 in
                                 {
                                   curmodule =
                                     (FStar_Pervasives_Native.Some mname);
                                   curmonad = (uu___132_10150.curmonad);
                                   modules = (uu___132_10150.modules);
                                   scope_mods = uu____10151;
                                   exported_ids =
                                     (uu___132_10150.exported_ids);
                                   trans_exported_ids =
                                     (uu___132_10150.trans_exported_ids);
                                   includes = (uu___132_10150.includes);
                                   sigaccum = (uu___132_10150.sigaccum);
                                   sigmap = (env1.sigmap);
                                   iface = intf;
                                   admitted_iface = admitted;
                                   expect_typ = (uu___132_10150.expect_typ);
                                   docs = (uu___132_10150.docs);
                                   remaining_iface_decls =
                                     (uu___132_10150.remaining_iface_decls);
                                   syntax_only = (uu___132_10150.syntax_only);
                                   ds_hooks = (uu___132_10150.ds_hooks)
                                 } in
                               (FStar_List.iter
                                  (fun op  ->
                                     (env1.ds_hooks).ds_push_open_hook env'
                                       op) (FStar_List.rev auto_open2);
                                env')))))) in
            let uu____10163 =
              FStar_All.pipe_right env.modules
                (FStar_Util.find_opt
                   (fun uu____10189  ->
                      match uu____10189 with
                      | (l,uu____10195) -> FStar_Ident.lid_equals l mname)) in
            match uu____10163 with
            | FStar_Pervasives_Native.None  ->
                let uu____10204 = prep env in (uu____10204, false)
            | FStar_Pervasives_Native.Some (uu____10205,m) ->
                ((let uu____10212 =
                    (let uu____10215 = FStar_Options.interactive () in
                     Prims.op_Negation uu____10215) &&
                      ((Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)
                         || intf) in
                  if uu____10212
                  then
                    let uu____10216 =
                      let uu____10221 =
                        FStar_Util.format1
                          "Duplicate module or interface name: %s"
                          mname.FStar_Ident.str in
                      (FStar_Errors.Fatal_DuplicateModuleOrInterface,
                        uu____10221) in
                    FStar_Errors.raise_error uu____10216
                      (FStar_Ident.range_of_lid mname)
                  else ());
                 (let uu____10223 =
                    let uu____10224 = push env in prep uu____10224 in
                  (uu____10223, true)))
let enter_monad_scope: env -> FStar_Ident.ident -> env =
  fun env  ->
    fun mname  ->
      match env.curmonad with
      | FStar_Pervasives_Native.Some mname' ->
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_MonadAlreadyDefined,
              (Prims.strcat "Trying to define monad "
                 (Prims.strcat mname.FStar_Ident.idText
                    (Prims.strcat ", but already in monad scope "
                       mname'.FStar_Ident.idText))))
            mname.FStar_Ident.idRange
      | FStar_Pervasives_Native.None  ->
          let uu___133_10232 = env in
          {
            curmodule = (uu___133_10232.curmodule);
            curmonad = (FStar_Pervasives_Native.Some mname);
            modules = (uu___133_10232.modules);
            scope_mods = (uu___133_10232.scope_mods);
            exported_ids = (uu___133_10232.exported_ids);
            trans_exported_ids = (uu___133_10232.trans_exported_ids);
            includes = (uu___133_10232.includes);
            sigaccum = (uu___133_10232.sigaccum);
            sigmap = (uu___133_10232.sigmap);
            iface = (uu___133_10232.iface);
            admitted_iface = (uu___133_10232.admitted_iface);
            expect_typ = (uu___133_10232.expect_typ);
            docs = (uu___133_10232.docs);
            remaining_iface_decls = (uu___133_10232.remaining_iface_decls);
            syntax_only = (uu___133_10232.syntax_only);
            ds_hooks = (uu___133_10232.ds_hooks)
          }
let fail_or:
  'a .
    env ->
      (FStar_Ident.lident -> 'a FStar_Pervasives_Native.option) ->
        FStar_Ident.lident -> 'a
  =
  fun env  ->
    fun lookup  ->
      fun lid  ->
        let uu____10259 = lookup lid in
        match uu____10259 with
        | FStar_Pervasives_Native.None  ->
            let opened_modules =
              FStar_List.map
                (fun uu____10272  ->
                   match uu____10272 with
                   | (lid1,uu____10278) -> FStar_Ident.text_of_lid lid1)
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
                   let uu____10283 =
                     FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
                   FStar_Ident.set_lid_range uu____10283
                     (FStar_Ident.range_of_lid lid) in
                 let uu____10284 = resolve_module_name env modul true in
                 match uu____10284 with
                 | FStar_Pervasives_Native.None  ->
                     let opened_modules1 =
                       FStar_String.concat ", " opened_modules in
                     FStar_Util.format3
                       "%s\nModule %s does not belong to the list of modules in scope, namely %s"
                       msg modul.FStar_Ident.str opened_modules1
                 | FStar_Pervasives_Native.Some modul' when
                     Prims.op_Negation
                       (FStar_List.existsb
                          (fun m  -> m = modul'.FStar_Ident.str)
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
let fail_or2:
  'a .
    (FStar_Ident.ident -> 'a FStar_Pervasives_Native.option) ->
      FStar_Ident.ident -> 'a
  =
  fun lookup  ->
    fun id1  ->
      let uu____10315 = lookup id1 in
      match uu____10315 with
      | FStar_Pervasives_Native.None  ->
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_IdentifierNotFound,
              (Prims.strcat "Identifier not found ["
                 (Prims.strcat id1.FStar_Ident.idText "]")))
            id1.FStar_Ident.idRange
      | FStar_Pervasives_Native.Some r -> r