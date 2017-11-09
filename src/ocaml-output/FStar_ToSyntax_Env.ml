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
    ds_push_open_hook = (fun uu____1523  -> fun uu____1524  -> ());
    ds_push_include_hook = (fun uu____1527  -> fun uu____1528  -> ());
    ds_push_module_abbrev_hook =
      (fun uu____1532  -> fun uu____1533  -> fun uu____1534  -> ())
  }
type foundname =
  | Term_name of (FStar_Syntax_Syntax.typ,Prims.bool)
  FStar_Pervasives_Native.tuple2
  | Eff_name of (FStar_Syntax_Syntax.sigelt,FStar_Ident.lident)
  FStar_Pervasives_Native.tuple2[@@deriving show]
let uu___is_Term_name: foundname -> Prims.bool =
  fun projectee  ->
    match projectee with | Term_name _0 -> true | uu____1559 -> false
let __proj__Term_name__item___0:
  foundname ->
    (FStar_Syntax_Syntax.typ,Prims.bool) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Term_name _0 -> _0
let uu___is_Eff_name: foundname -> Prims.bool =
  fun projectee  ->
    match projectee with | Eff_name _0 -> true | uu____1587 -> false
let __proj__Eff_name__item___0:
  foundname ->
    (FStar_Syntax_Syntax.sigelt,FStar_Ident.lident)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Eff_name _0 -> _0
let set_iface: env -> Prims.bool -> env =
  fun env  ->
    fun b  ->
      let uu___274_1613 = env in
      {
        curmodule = (uu___274_1613.curmodule);
        curmonad = (uu___274_1613.curmonad);
        modules = (uu___274_1613.modules);
        scope_mods = (uu___274_1613.scope_mods);
        exported_ids = (uu___274_1613.exported_ids);
        trans_exported_ids = (uu___274_1613.trans_exported_ids);
        includes = (uu___274_1613.includes);
        sigaccum = (uu___274_1613.sigaccum);
        sigmap = (uu___274_1613.sigmap);
        iface = b;
        admitted_iface = (uu___274_1613.admitted_iface);
        expect_typ = (uu___274_1613.expect_typ);
        docs = (uu___274_1613.docs);
        remaining_iface_decls = (uu___274_1613.remaining_iface_decls);
        syntax_only = (uu___274_1613.syntax_only);
        ds_hooks = (uu___274_1613.ds_hooks)
      }
let iface: env -> Prims.bool = fun e  -> e.iface
let set_admitted_iface: env -> Prims.bool -> env =
  fun e  ->
    fun b  ->
      let uu___275_1623 = e in
      {
        curmodule = (uu___275_1623.curmodule);
        curmonad = (uu___275_1623.curmonad);
        modules = (uu___275_1623.modules);
        scope_mods = (uu___275_1623.scope_mods);
        exported_ids = (uu___275_1623.exported_ids);
        trans_exported_ids = (uu___275_1623.trans_exported_ids);
        includes = (uu___275_1623.includes);
        sigaccum = (uu___275_1623.sigaccum);
        sigmap = (uu___275_1623.sigmap);
        iface = (uu___275_1623.iface);
        admitted_iface = b;
        expect_typ = (uu___275_1623.expect_typ);
        docs = (uu___275_1623.docs);
        remaining_iface_decls = (uu___275_1623.remaining_iface_decls);
        syntax_only = (uu___275_1623.syntax_only);
        ds_hooks = (uu___275_1623.ds_hooks)
      }
let admitted_iface: env -> Prims.bool = fun e  -> e.admitted_iface
let set_expect_typ: env -> Prims.bool -> env =
  fun e  ->
    fun b  ->
      let uu___276_1633 = e in
      {
        curmodule = (uu___276_1633.curmodule);
        curmonad = (uu___276_1633.curmonad);
        modules = (uu___276_1633.modules);
        scope_mods = (uu___276_1633.scope_mods);
        exported_ids = (uu___276_1633.exported_ids);
        trans_exported_ids = (uu___276_1633.trans_exported_ids);
        includes = (uu___276_1633.includes);
        sigaccum = (uu___276_1633.sigaccum);
        sigmap = (uu___276_1633.sigmap);
        iface = (uu___276_1633.iface);
        admitted_iface = (uu___276_1633.admitted_iface);
        expect_typ = b;
        docs = (uu___276_1633.docs);
        remaining_iface_decls = (uu___276_1633.remaining_iface_decls);
        syntax_only = (uu___276_1633.syntax_only);
        ds_hooks = (uu___276_1633.ds_hooks)
      }
let expect_typ: env -> Prims.bool = fun e  -> e.expect_typ
let all_exported_id_kinds: exported_id_kind Prims.list =
  [Exported_id_field; Exported_id_term_type]
let transitive_exported_ids:
  env -> FStar_Ident.lident -> Prims.string Prims.list =
  fun env  ->
    fun lid  ->
      let module_name = FStar_Ident.string_of_lid lid in
      let uu____1648 =
        FStar_Util.smap_try_find env.trans_exported_ids module_name in
      match uu____1648 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some exported_id_set ->
          let uu____1654 =
            let uu____1655 = exported_id_set Exported_id_term_type in
            FStar_ST.op_Bang uu____1655 in
          FStar_All.pipe_right uu____1654 FStar_Util.set_elements
let open_modules:
  env ->
    (FStar_Ident.lident,FStar_Syntax_Syntax.modul)
      FStar_Pervasives_Native.tuple2 Prims.list
  = fun e  -> e.modules
let open_modules_and_namespaces: env -> FStar_Ident.lident Prims.list =
  fun env  ->
    FStar_List.filter_map
      (fun uu___242_1918  ->
         match uu___242_1918 with
         | Open_module_or_namespace (lid,_info) ->
             FStar_Pervasives_Native.Some lid
         | uu____1923 -> FStar_Pervasives_Native.None) env.scope_mods
let set_current_module: env -> FStar_Ident.lident -> env =
  fun e  ->
    fun l  ->
      let uu___277_1930 = e in
      {
        curmodule = (FStar_Pervasives_Native.Some l);
        curmonad = (uu___277_1930.curmonad);
        modules = (uu___277_1930.modules);
        scope_mods = (uu___277_1930.scope_mods);
        exported_ids = (uu___277_1930.exported_ids);
        trans_exported_ids = (uu___277_1930.trans_exported_ids);
        includes = (uu___277_1930.includes);
        sigaccum = (uu___277_1930.sigaccum);
        sigmap = (uu___277_1930.sigmap);
        iface = (uu___277_1930.iface);
        admitted_iface = (uu___277_1930.admitted_iface);
        expect_typ = (uu___277_1930.expect_typ);
        docs = (uu___277_1930.docs);
        remaining_iface_decls = (uu___277_1930.remaining_iface_decls);
        syntax_only = (uu___277_1930.syntax_only);
        ds_hooks = (uu___277_1930.ds_hooks)
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
      let uu____1945 =
        FStar_All.pipe_right env.remaining_iface_decls
          (FStar_List.tryFind
             (fun uu____1979  ->
                match uu____1979 with
                | (m,uu____1987) -> FStar_Ident.lid_equals l m)) in
      match uu____1945 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (uu____2004,decls) ->
          FStar_Pervasives_Native.Some decls
let set_iface_decls:
  env -> FStar_Ident.lident -> FStar_Parser_AST.decl Prims.list -> env =
  fun env  ->
    fun l  ->
      fun ds  ->
        let uu____2031 =
          FStar_List.partition
            (fun uu____2061  ->
               match uu____2061 with
               | (m,uu____2069) -> FStar_Ident.lid_equals l m)
            env.remaining_iface_decls in
        match uu____2031 with
        | (uu____2074,rest) ->
            let uu___278_2108 = env in
            {
              curmodule = (uu___278_2108.curmodule);
              curmonad = (uu___278_2108.curmonad);
              modules = (uu___278_2108.modules);
              scope_mods = (uu___278_2108.scope_mods);
              exported_ids = (uu___278_2108.exported_ids);
              trans_exported_ids = (uu___278_2108.trans_exported_ids);
              includes = (uu___278_2108.includes);
              sigaccum = (uu___278_2108.sigaccum);
              sigmap = (uu___278_2108.sigmap);
              iface = (uu___278_2108.iface);
              admitted_iface = (uu___278_2108.admitted_iface);
              expect_typ = (uu___278_2108.expect_typ);
              docs = (uu___278_2108.docs);
              remaining_iface_decls = ((l, ds) :: rest);
              syntax_only = (uu___278_2108.syntax_only);
              ds_hooks = (uu___278_2108.ds_hooks)
            }
let qual: FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident =
  FStar_Syntax_Util.qual_id
let qualify: env -> FStar_Ident.ident -> FStar_Ident.lident =
  fun env  ->
    fun id  ->
      match env.curmonad with
      | FStar_Pervasives_Native.None  ->
          let uu____2127 = current_module env in qual uu____2127 id
      | FStar_Pervasives_Native.Some monad ->
          let uu____2129 =
            let uu____2130 = current_module env in qual uu____2130 monad in
          FStar_Syntax_Util.mk_field_projector_name_from_ident uu____2129 id
let syntax_only: env -> Prims.bool = fun env  -> env.syntax_only
let set_syntax_only: env -> Prims.bool -> env =
  fun env  ->
    fun b  ->
      let uu___279_2140 = env in
      {
        curmodule = (uu___279_2140.curmodule);
        curmonad = (uu___279_2140.curmonad);
        modules = (uu___279_2140.modules);
        scope_mods = (uu___279_2140.scope_mods);
        exported_ids = (uu___279_2140.exported_ids);
        trans_exported_ids = (uu___279_2140.trans_exported_ids);
        includes = (uu___279_2140.includes);
        sigaccum = (uu___279_2140.sigaccum);
        sigmap = (uu___279_2140.sigmap);
        iface = (uu___279_2140.iface);
        admitted_iface = (uu___279_2140.admitted_iface);
        expect_typ = (uu___279_2140.expect_typ);
        docs = (uu___279_2140.docs);
        remaining_iface_decls = (uu___279_2140.remaining_iface_decls);
        syntax_only = b;
        ds_hooks = (uu___279_2140.ds_hooks)
      }
let ds_hooks: env -> dsenv_hooks = fun env  -> env.ds_hooks
let set_ds_hooks: env -> dsenv_hooks -> env =
  fun env  ->
    fun hooks  ->
      let uu___280_2150 = env in
      {
        curmodule = (uu___280_2150.curmodule);
        curmonad = (uu___280_2150.curmonad);
        modules = (uu___280_2150.modules);
        scope_mods = (uu___280_2150.scope_mods);
        exported_ids = (uu___280_2150.exported_ids);
        trans_exported_ids = (uu___280_2150.trans_exported_ids);
        includes = (uu___280_2150.includes);
        sigaccum = (uu___280_2150.sigaccum);
        sigmap = (uu___280_2150.sigmap);
        iface = (uu___280_2150.iface);
        admitted_iface = (uu___280_2150.admitted_iface);
        expect_typ = (uu___280_2150.expect_typ);
        docs = (uu___280_2150.docs);
        remaining_iface_decls = (uu___280_2150.remaining_iface_decls);
        syntax_only = (uu___280_2150.syntax_only);
        ds_hooks = hooks
      }
let new_sigmap: 'Auu____2153 . Prims.unit -> 'Auu____2153 FStar_Util.smap =
  fun uu____2159  -> FStar_Util.smap_create (Prims.parse_int "100")
let empty_env: Prims.unit -> env =
  fun uu____2162  ->
    let uu____2163 = new_sigmap () in
    let uu____2166 = new_sigmap () in
    let uu____2169 = new_sigmap () in
    let uu____2180 = new_sigmap () in
    let uu____2191 = new_sigmap () in
    {
      curmodule = FStar_Pervasives_Native.None;
      curmonad = FStar_Pervasives_Native.None;
      modules = [];
      scope_mods = [];
      exported_ids = uu____2163;
      trans_exported_ids = uu____2166;
      includes = uu____2169;
      sigaccum = [];
      sigmap = uu____2180;
      iface = false;
      admitted_iface = false;
      expect_typ = false;
      docs = uu____2191;
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
      (fun uu____2223  ->
         match uu____2223 with
         | (m,uu____2229) ->
             FStar_Ident.lid_equals m FStar_Parser_Const.all_lid) env.modules
let set_bv_range:
  FStar_Syntax_Syntax.bv -> FStar_Range.range -> FStar_Syntax_Syntax.bv =
  fun bv  ->
    fun r  ->
      let id =
        let uu___281_2237 = bv.FStar_Syntax_Syntax.ppname in
        {
          FStar_Ident.idText = (uu___281_2237.FStar_Ident.idText);
          FStar_Ident.idRange = r
        } in
      let uu___282_2238 = bv in
      {
        FStar_Syntax_Syntax.ppname = id;
        FStar_Syntax_Syntax.index = (uu___282_2238.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = (uu___282_2238.FStar_Syntax_Syntax.sort)
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
  fun id  ->
    let t =
      FStar_Util.find_map unmangleMap
        (fun uu____2325  ->
           match uu____2325 with
           | (x,y,dd,dq) ->
               if id.FStar_Ident.idText = x
               then
                 let uu____2348 =
                   let uu____2349 =
                     FStar_Ident.lid_of_path ["Prims"; y]
                       id.FStar_Ident.idRange in
                   FStar_Syntax_Syntax.fvar uu____2349 dd dq in
                 FStar_Pervasives_Native.Some uu____2348
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
    match projectee with | Cont_ok _0 -> true | uu____2392 -> false
let __proj__Cont_ok__item___0: 'a . 'a cont_t -> 'a =
  fun projectee  -> match projectee with | Cont_ok _0 -> _0
let uu___is_Cont_fail: 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_fail  -> true | uu____2421 -> false
let uu___is_Cont_ignore: 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_ignore  -> true | uu____2435 -> false
let option_of_cont:
  'a .
    (Prims.unit -> 'a FStar_Pervasives_Native.option) ->
      'a cont_t -> 'a FStar_Pervasives_Native.option
  =
  fun k_ignore  ->
    fun uu___243_2458  ->
      match uu___243_2458 with
      | Cont_ok a -> FStar_Pervasives_Native.Some a
      | Cont_fail  -> FStar_Pervasives_Native.None
      | Cont_ignore  -> k_ignore ()
let find_in_record:
  'Auu____2471 .
    FStar_Ident.ident Prims.list ->
      FStar_Ident.ident ->
        record_or_dc ->
          (record_or_dc -> 'Auu____2471 cont_t) -> 'Auu____2471 cont_t
  =
  fun ns  ->
    fun id  ->
      fun record  ->
        fun cont  ->
          let typename' =
            FStar_Ident.lid_of_ids
              (FStar_List.append ns [(record.typename).FStar_Ident.ident]) in
          if FStar_Ident.lid_equals typename' record.typename
          then
            let fname =
              FStar_Ident.lid_of_ids
                (FStar_List.append (record.typename).FStar_Ident.ns [id]) in
            let find1 =
              FStar_Util.find_map record.fields
                (fun uu____2517  ->
                   match uu____2517 with
                   | (f,uu____2525) ->
                       if id.FStar_Ident.idText = f.FStar_Ident.idText
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
  fun uu___244_2571  ->
    match uu___244_2571 with
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
            fun id  ->
              let idstr = id.FStar_Ident.idText in
              let rec aux uu___245_2627 =
                match uu___245_2627 with
                | [] -> find_in_module_default
                | modul::q ->
                    let mname = modul.FStar_Ident.str in
                    let not_shadowed =
                      let uu____2638 = get_exported_id_set env mname in
                      match uu____2638 with
                      | FStar_Pervasives_Native.None  -> true
                      | FStar_Pervasives_Native.Some mex ->
                          let mexports =
                            let uu____2659 = mex eikind in
                            FStar_ST.op_Bang uu____2659 in
                          FStar_Util.set_mem idstr mexports in
                    let mincludes =
                      let uu____2906 =
                        FStar_Util.smap_try_find env.includes mname in
                      match uu____2906 with
                      | FStar_Pervasives_Native.None  -> []
                      | FStar_Pervasives_Native.Some minc ->
                          FStar_ST.op_Bang minc in
                    let look_into =
                      if not_shadowed
                      then
                        let uu____3001 = qual modul id in
                        find_in_module uu____3001
                      else Cont_ignore in
                    (match look_into with
                     | Cont_ignore  -> aux (FStar_List.append mincludes q)
                     | uu____3005 -> look_into) in
              aux [ns]
let is_exported_id_field: exported_id_kind -> Prims.bool =
  fun uu___246_3010  ->
    match uu___246_3010 with
    | Exported_id_field  -> true
    | uu____3011 -> false
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
    fun id  ->
      fun eikind  ->
        fun k_local_binding  ->
          fun k_rec_binding  ->
            fun k_record  ->
              fun find_in_module  ->
                fun lookup_default_id  ->
                  let check_local_binding_id uu___247_3113 =
                    match uu___247_3113 with
                    | (id',uu____3115,uu____3116) ->
                        id'.FStar_Ident.idText = id.FStar_Ident.idText in
                  let check_rec_binding_id uu___248_3120 =
                    match uu___248_3120 with
                    | (id',uu____3122,uu____3123) ->
                        id'.FStar_Ident.idText = id.FStar_Ident.idText in
                  let curmod_ns =
                    let uu____3127 = current_module env in
                    FStar_Ident.ids_of_lid uu____3127 in
                  let proc uu___249_3133 =
                    match uu___249_3133 with
                    | Local_binding l when check_local_binding_id l ->
                        k_local_binding l
                    | Rec_binding r when check_rec_binding_id r ->
                        k_rec_binding r
                    | Open_module_or_namespace (ns,Open_module ) ->
                        find_in_module_with_includes eikind find_in_module
                          Cont_ignore env ns id
                    | Top_level_def id' when
                        id'.FStar_Ident.idText = id.FStar_Ident.idText ->
                        lookup_default_id Cont_ignore id
                    | Record_or_dc r when is_exported_id_field eikind ->
                        let uu____3141 = FStar_Ident.lid_of_ids curmod_ns in
                        find_in_module_with_includes Exported_id_field
                          (fun lid  ->
                             let id1 = lid.FStar_Ident.ident in
                             find_in_record lid.FStar_Ident.ns id1 r k_record)
                          Cont_ignore env uu____3141 id
                    | uu____3146 -> Cont_ignore in
                  let rec aux uu___250_3154 =
                    match uu___250_3154 with
                    | a::q ->
                        let uu____3163 = proc a in
                        option_of_cont (fun uu____3167  -> aux q) uu____3163
                    | [] ->
                        let uu____3168 = lookup_default_id Cont_fail id in
                        option_of_cont
                          (fun uu____3172  -> FStar_Pervasives_Native.None)
                          uu____3168 in
                  aux env.scope_mods
let found_local_binding:
  'Auu____3177 'Auu____3178 .
    FStar_Range.range ->
      ('Auu____3178,FStar_Syntax_Syntax.bv,'Auu____3177)
        FStar_Pervasives_Native.tuple3 ->
        (FStar_Syntax_Syntax.term,'Auu____3177)
          FStar_Pervasives_Native.tuple2
  =
  fun r  ->
    fun uu____3196  ->
      match uu____3196 with
      | (id',x,mut) -> let uu____3206 = bv_to_name x r in (uu____3206, mut)
let find_in_module:
  'Auu____3212 .
    env ->
      FStar_Ident.lident ->
        (FStar_Ident.lident ->
           (FStar_Syntax_Syntax.sigelt,Prims.bool)
             FStar_Pervasives_Native.tuple2 -> 'Auu____3212)
          -> 'Auu____3212 -> 'Auu____3212
  =
  fun env  ->
    fun lid  ->
      fun k_global_def  ->
        fun k_not_found  ->
          let uu____3247 =
            FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str in
          match uu____3247 with
          | FStar_Pervasives_Native.Some sb -> k_global_def lid sb
          | FStar_Pervasives_Native.None  -> k_not_found
let try_lookup_id:
  env ->
    FStar_Ident.ident ->
      (FStar_Syntax_Syntax.term,Prims.bool) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option
  =
  fun env  ->
    fun id  ->
      let uu____3283 = unmangleOpName id in
      match uu____3283 with
      | FStar_Pervasives_Native.Some f -> FStar_Pervasives_Native.Some f
      | uu____3309 ->
          try_lookup_id'' env id Exported_id_term_type
            (fun r  ->
               let uu____3323 = found_local_binding id.FStar_Ident.idRange r in
               Cont_ok uu____3323) (fun uu____3333  -> Cont_fail)
            (fun uu____3339  -> Cont_ignore)
            (fun i  ->
               find_in_module env i
                 (fun uu____3354  -> fun uu____3355  -> Cont_fail)
                 Cont_ignore)
            (fun uu____3370  -> fun uu____3371  -> Cont_fail)
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
    fun id  ->
      fun k_global_def  ->
        fun k_not_found  ->
          let find_in_monad =
            match env.curmonad with
            | FStar_Pervasives_Native.Some uu____3441 ->
                let lid = qualify env id in
                let uu____3443 =
                  FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str in
                (match uu____3443 with
                 | FStar_Pervasives_Native.Some r ->
                     let uu____3467 = k_global_def lid r in
                     FStar_Pervasives_Native.Some uu____3467
                 | FStar_Pervasives_Native.None  ->
                     FStar_Pervasives_Native.None)
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None in
          match find_in_monad with
          | FStar_Pervasives_Native.Some v1 -> v1
          | FStar_Pervasives_Native.None  ->
              let lid =
                let uu____3490 = current_module env in qual uu____3490 id in
              find_in_module env lid k_global_def k_not_found
let module_is_defined: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      (match env.curmodule with
       | FStar_Pervasives_Native.None  -> false
       | FStar_Pervasives_Native.Some m ->
           let uu____3500 = current_module env in
           FStar_Ident.lid_equals lid uu____3500)
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
        let rec aux uu___251_3532 =
          match uu___251_3532 with
          | [] ->
              let uu____3537 = module_is_defined env lid in
              if uu____3537
              then FStar_Pervasives_Native.Some lid
              else FStar_Pervasives_Native.None
          | (Open_module_or_namespace (ns,Open_namespace ))::q when honor_ns
              ->
              let new_lid =
                let uu____3546 =
                  let uu____3549 = FStar_Ident.path_of_lid ns in
                  let uu____3552 = FStar_Ident.path_of_lid lid in
                  FStar_List.append uu____3549 uu____3552 in
                FStar_Ident.lid_of_path uu____3546
                  (FStar_Ident.range_of_lid lid) in
              let uu____3555 = module_is_defined env new_lid in
              if uu____3555
              then FStar_Pervasives_Native.Some new_lid
              else aux q
          | (Module_abbrev (name,modul))::uu____3561 when
              (nslen = (Prims.parse_int "0")) &&
                (name.FStar_Ident.idText =
                   (lid.FStar_Ident.ident).FStar_Ident.idText)
              -> FStar_Pervasives_Native.Some modul
          | uu____3568::q -> aux q in
        aux env.scope_mods
let fail_if_curmodule:
  env -> FStar_Ident.lident -> FStar_Ident.lident -> Prims.unit =
  fun env  ->
    fun ns_original  ->
      fun ns_resolved  ->
        let uu____3581 =
          let uu____3582 = current_module env in
          FStar_Ident.lid_equals ns_resolved uu____3582 in
        if uu____3581
        then
          (if FStar_Ident.lid_equals ns_resolved FStar_Parser_Const.prims_lid
           then ()
           else
             (let uu____3584 =
                let uu____3585 =
                  let uu____3590 =
                    FStar_Util.format1
                      "Reference %s to current module is forbidden (see GitHub issue #451)"
                      ns_original.FStar_Ident.str in
                  (uu____3590, (FStar_Ident.range_of_lid ns_original)) in
                FStar_Errors.Error uu____3585 in
              FStar_Exn.raise uu____3584))
        else ()
let fail_if_qualified_by_curmodule: env -> FStar_Ident.lident -> Prims.unit =
  fun env  ->
    fun lid  ->
      match lid.FStar_Ident.ns with
      | [] -> ()
      | uu____3598 ->
          let modul_orig = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          let uu____3602 = resolve_module_name env modul_orig true in
          (match uu____3602 with
           | FStar_Pervasives_Native.Some modul_res ->
               fail_if_curmodule env modul_orig modul_res
           | uu____3606 -> ())
let namespace_is_open: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      FStar_List.existsb
        (fun uu___252_3617  ->
           match uu___252_3617 with
           | Open_module_or_namespace (ns,Open_namespace ) ->
               FStar_Ident.lid_equals lid ns
           | uu____3619 -> false) env.scope_mods
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
        let rec aux revns id =
          let lid = FStar_Ident.lid_of_ns_and_id (FStar_List.rev revns) id in
          if namespace_is_open env lid
          then
            FStar_Pervasives_Native.Some ((FStar_List.rev (id :: revns)), [])
          else
            (match revns with
             | [] -> FStar_Pervasives_Native.None
             | ns_last_id::rev_ns_prefix ->
                 let uu____3708 = aux rev_ns_prefix ns_last_id in
                 FStar_All.pipe_right uu____3708
                   (FStar_Util.map_option
                      (fun uu____3758  ->
                         match uu____3758 with
                         | (stripped_ids,rev_kept_ids) ->
                             (stripped_ids, (id :: rev_kept_ids))))) in
        let uu____3789 =
          is_full_path &&
            (let uu____3791 = FStar_Ident.lid_of_ids ids in
             module_is_defined env uu____3791) in
        if uu____3789
        then (ids, [])
        else
          (match FStar_List.rev ids with
           | [] -> ([], [])
           | ns_last_id::ns_rev_prefix ->
               let uu____3821 = aux ns_rev_prefix ns_last_id in
               (match uu____3821 with
                | FStar_Pervasives_Native.None  -> ([], ids)
                | FStar_Pervasives_Native.Some (stripped_ids,rev_kept_ids) ->
                    (stripped_ids, (FStar_List.rev rev_kept_ids))))
let shorten_lid: env -> FStar_Ident.lid -> FStar_Ident.lid =
  fun env  ->
    fun lid  ->
      let uu____3880 = shorten_module_path env lid.FStar_Ident.ns true in
      match uu____3880 with
      | (uu____3889,short) ->
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
                  | uu____3997::uu____3998 ->
                      let uu____4001 =
                        let uu____4004 =
                          let uu____4005 =
                            FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
                          FStar_Ident.set_lid_range uu____4005
                            (FStar_Ident.range_of_lid lid) in
                        resolve_module_name env uu____4004 true in
                      (match uu____4001 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some modul ->
                           let uu____4009 =
                             find_in_module_with_includes eikind f_module
                               Cont_fail env modul lid.FStar_Ident.ident in
                           option_of_cont
                             (fun uu____4013  -> FStar_Pervasives_Native.None)
                             uu____4009)
                  | [] ->
                      try_lookup_id'' env lid.FStar_Ident.ident eikind
                        k_local_binding k_rec_binding k_record f_module
                        l_default
let cont_of_option:
  'a . 'a cont_t -> 'a FStar_Pervasives_Native.option -> 'a cont_t =
  fun k_none  ->
    fun uu___253_4031  ->
      match uu___253_4031 with
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
              let uu____4130 = k_global_def lid1 def in
              cont_of_option k uu____4130 in
            let f_module lid' =
              let k = Cont_ignore in
              find_in_module env lid' (k_global_def' k) k in
            let l_default k i = lookup_default_id env i (k_global_def' k) k in
            resolve_in_open_namespaces'' env lid Exported_id_term_type
              (fun l  ->
                 let uu____4160 = k_local_binding l in
                 cont_of_option Cont_fail uu____4160)
              (fun r  ->
                 let uu____4166 = k_rec_binding r in
                 cont_of_option Cont_fail uu____4166)
              (fun uu____4170  -> Cont_ignore) f_module l_default
let fv_qual_of_se:
  FStar_Syntax_Syntax.sigelt ->
    FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____4178,uu____4179,uu____4180,l,uu____4182,uu____4183) ->
        let qopt =
          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
            (fun uu___254_4194  ->
               match uu___254_4194 with
               | FStar_Syntax_Syntax.RecordConstructor (uu____4197,fs) ->
                   FStar_Pervasives_Native.Some
                     (FStar_Syntax_Syntax.Record_ctor (l, fs))
               | uu____4209 -> FStar_Pervasives_Native.None) in
        (match qopt with
         | FStar_Pervasives_Native.None  ->
             FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor
         | x -> x)
    | FStar_Syntax_Syntax.Sig_declare_typ (uu____4215,uu____4216,uu____4217)
        -> FStar_Pervasives_Native.None
    | uu____4218 -> FStar_Pervasives_Native.None
let lb_fv:
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Ident.lident -> FStar_Syntax_Syntax.fv
  =
  fun lbs  ->
    fun lid  ->
      let uu____4229 =
        FStar_Util.find_map lbs
          (fun lb  ->
             let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
             let uu____4237 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
             if uu____4237
             then FStar_Pervasives_Native.Some fv
             else FStar_Pervasives_Native.None) in
      FStar_All.pipe_right uu____4229 FStar_Util.must
let ns_of_lid_equals: FStar_Ident.lident -> FStar_Ident.lident -> Prims.bool
  =
  fun lid  ->
    fun ns  ->
      ((FStar_List.length lid.FStar_Ident.ns) =
         (FStar_List.length (FStar_Ident.ids_of_lid ns)))
        &&
        (let uu____4250 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
         FStar_Ident.lid_equals uu____4250 ns)
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
          let k_global_def source_lid uu___259_4280 =
            match uu___259_4280 with
            | (uu____4287,true ) when exclude_interf ->
                FStar_Pervasives_Native.None
            | (se,uu____4289) ->
                (match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_inductive_typ uu____4292 ->
                     let uu____4309 =
                       let uu____4310 =
                         let uu____4315 =
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.Delta_constant
                             FStar_Pervasives_Native.None in
                         (uu____4315, false) in
                       Term_name uu____4310 in
                     FStar_Pervasives_Native.Some uu____4309
                 | FStar_Syntax_Syntax.Sig_datacon uu____4316 ->
                     let uu____4331 =
                       let uu____4332 =
                         let uu____4337 =
                           let uu____4338 = fv_qual_of_se se in
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.Delta_constant uu____4338 in
                         (uu____4337, false) in
                       Term_name uu____4332 in
                     FStar_Pervasives_Native.Some uu____4331
                 | FStar_Syntax_Syntax.Sig_let ((uu____4341,lbs),uu____4343)
                     ->
                     let fv = lb_fv lbs source_lid in
                     let uu____4359 =
                       let uu____4360 =
                         let uu____4365 =
                           FStar_Syntax_Syntax.fvar source_lid
                             fv.FStar_Syntax_Syntax.fv_delta
                             fv.FStar_Syntax_Syntax.fv_qual in
                         (uu____4365, false) in
                       Term_name uu____4360 in
                     FStar_Pervasives_Native.Some uu____4359
                 | FStar_Syntax_Syntax.Sig_declare_typ
                     (lid1,uu____4367,uu____4368) ->
                     let quals = se.FStar_Syntax_Syntax.sigquals in
                     let uu____4372 =
                       any_val ||
                         (FStar_All.pipe_right quals
                            (FStar_Util.for_some
                               (fun uu___255_4376  ->
                                  match uu___255_4376 with
                                  | FStar_Syntax_Syntax.Assumption  -> true
                                  | uu____4377 -> false))) in
                     if uu____4372
                     then
                       let lid2 =
                         FStar_Ident.set_lid_range lid1
                           (FStar_Ident.range_of_lid source_lid) in
                       let dd =
                         let uu____4382 =
                           (FStar_Syntax_Util.is_primop_lid lid2) ||
                             (FStar_All.pipe_right quals
                                (FStar_Util.for_some
                                   (fun uu___256_4387  ->
                                      match uu___256_4387 with
                                      | FStar_Syntax_Syntax.Projector
                                          uu____4388 -> true
                                      | FStar_Syntax_Syntax.Discriminator
                                          uu____4393 -> true
                                      | uu____4394 -> false))) in
                         if uu____4382
                         then FStar_Syntax_Syntax.Delta_equational
                         else FStar_Syntax_Syntax.Delta_constant in
                       let dd1 =
                         let uu____4397 =
                           FStar_All.pipe_right quals
                             (FStar_Util.for_some
                                (fun uu___257_4401  ->
                                   match uu___257_4401 with
                                   | FStar_Syntax_Syntax.Abstract  -> true
                                   | uu____4402 -> false)) in
                         if uu____4397
                         then FStar_Syntax_Syntax.Delta_abstract dd
                         else dd in
                       let uu____4404 =
                         FStar_Util.find_map quals
                           (fun uu___258_4409  ->
                              match uu___258_4409 with
                              | FStar_Syntax_Syntax.Reflectable refl_monad ->
                                  FStar_Pervasives_Native.Some refl_monad
                              | uu____4413 -> FStar_Pervasives_Native.None) in
                       (match uu____4404 with
                        | FStar_Pervasives_Native.Some refl_monad ->
                            let refl_const =
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_constant
                                   (FStar_Const.Const_reflect refl_monad))
                                FStar_Pervasives_Native.None occurrence_range in
                            FStar_Pervasives_Native.Some
                              (Term_name (refl_const, false))
                        | uu____4422 ->
                            let uu____4425 =
                              let uu____4426 =
                                let uu____4431 =
                                  let uu____4432 = fv_qual_of_se se in
                                  FStar_Syntax_Syntax.fvar lid2 dd1
                                    uu____4432 in
                                (uu____4431, false) in
                              Term_name uu____4426 in
                            FStar_Pervasives_Native.Some uu____4425)
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
                 | FStar_Syntax_Syntax.Sig_effect_abbrev uu____4438 ->
                     FStar_Pervasives_Native.Some (Eff_name (se, source_lid))
                 | uu____4451 -> FStar_Pervasives_Native.None) in
          let k_local_binding r =
            let uu____4470 =
              let uu____4471 =
                found_local_binding (FStar_Ident.range_of_lid lid) r in
              Term_name uu____4471 in
            FStar_Pervasives_Native.Some uu____4470 in
          let k_rec_binding uu____4487 =
            match uu____4487 with
            | (id,l,dd) ->
                let uu____4499 =
                  let uu____4500 =
                    let uu____4505 =
                      FStar_Syntax_Syntax.fvar
                        (FStar_Ident.set_lid_range l
                           (FStar_Ident.range_of_lid lid)) dd
                        FStar_Pervasives_Native.None in
                    (uu____4505, false) in
                  Term_name uu____4500 in
                FStar_Pervasives_Native.Some uu____4499 in
          let found_unmangled =
            match lid.FStar_Ident.ns with
            | [] ->
                let uu____4511 = unmangleOpName lid.FStar_Ident.ident in
                (match uu____4511 with
                 | FStar_Pervasives_Native.Some f ->
                     FStar_Pervasives_Native.Some (Term_name f)
                 | uu____4529 -> FStar_Pervasives_Native.None)
            | uu____4536 -> FStar_Pervasives_Native.None in
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
        let uu____4565 = try_lookup_name true exclude_interf env lid in
        match uu____4565 with
        | FStar_Pervasives_Native.Some (Eff_name (o,l)) ->
            FStar_Pervasives_Native.Some (o, l)
        | uu____4580 -> FStar_Pervasives_Native.None
let try_lookup_effect_name:
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____4595 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____4595 with
      | FStar_Pervasives_Native.Some (o,l1) ->
          FStar_Pervasives_Native.Some l1
      | uu____4610 -> FStar_Pervasives_Native.None
let try_lookup_effect_name_and_attributes:
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident,FStar_Syntax_Syntax.cflags Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____4631 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____4631 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____4647;
             FStar_Syntax_Syntax.sigquals = uu____4648;
             FStar_Syntax_Syntax.sigmeta = uu____4649;
             FStar_Syntax_Syntax.sigattrs = uu____4650;_},l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____4669;
             FStar_Syntax_Syntax.sigquals = uu____4670;
             FStar_Syntax_Syntax.sigmeta = uu____4671;
             FStar_Syntax_Syntax.sigattrs = uu____4672;_},l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (uu____4690,uu____4691,uu____4692,uu____4693,cattributes);
             FStar_Syntax_Syntax.sigrng = uu____4695;
             FStar_Syntax_Syntax.sigquals = uu____4696;
             FStar_Syntax_Syntax.sigmeta = uu____4697;
             FStar_Syntax_Syntax.sigattrs = uu____4698;_},l1)
          -> FStar_Pervasives_Native.Some (l1, cattributes)
      | uu____4720 -> FStar_Pervasives_Native.None
let try_lookup_effect_defn:
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.eff_decl FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____4741 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____4741 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____4751;
             FStar_Syntax_Syntax.sigquals = uu____4752;
             FStar_Syntax_Syntax.sigmeta = uu____4753;
             FStar_Syntax_Syntax.sigattrs = uu____4754;_},uu____4755)
          -> FStar_Pervasives_Native.Some ne
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____4765;
             FStar_Syntax_Syntax.sigquals = uu____4766;
             FStar_Syntax_Syntax.sigmeta = uu____4767;
             FStar_Syntax_Syntax.sigattrs = uu____4768;_},uu____4769)
          -> FStar_Pervasives_Native.Some ne
      | uu____4778 -> FStar_Pervasives_Native.None
let is_effect_name: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____4791 = try_lookup_effect_name env lid in
      match uu____4791 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____4794 -> true
let try_lookup_root_effect_name:
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____4803 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____4803 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (l',uu____4813,uu____4814,uu____4815,uu____4816);
             FStar_Syntax_Syntax.sigrng = uu____4817;
             FStar_Syntax_Syntax.sigquals = uu____4818;
             FStar_Syntax_Syntax.sigmeta = uu____4819;
             FStar_Syntax_Syntax.sigattrs = uu____4820;_},uu____4821)
          ->
          let rec aux new_name =
            let uu____4840 =
              FStar_Util.smap_try_find (sigmap env) new_name.FStar_Ident.str in
            match uu____4840 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (s,uu____4858) ->
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
                     (uu____4867,uu____4868,uu____4869,cmp,uu____4871) ->
                     let l'' = FStar_Syntax_Util.comp_effect_name cmp in
                     aux l''
                 | uu____4877 -> FStar_Pervasives_Native.None) in
          aux l'
      | FStar_Pervasives_Native.Some (uu____4878,l') ->
          FStar_Pervasives_Native.Some l'
      | uu____4884 -> FStar_Pervasives_Native.None
let lookup_letbinding_quals:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___260_4913 =
        match uu___260_4913 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____4922,uu____4923,uu____4924);
             FStar_Syntax_Syntax.sigrng = uu____4925;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____4927;
             FStar_Syntax_Syntax.sigattrs = uu____4928;_},uu____4929)
            -> FStar_Pervasives_Native.Some quals
        | uu____4936 -> FStar_Pervasives_Native.None in
      let uu____4943 =
        resolve_in_open_namespaces' env lid
          (fun uu____4951  -> FStar_Pervasives_Native.None)
          (fun uu____4955  -> FStar_Pervasives_Native.None) k_global_def in
      match uu____4943 with
      | FStar_Pervasives_Native.Some quals -> quals
      | uu____4965 -> []
let try_lookup_module:
  env ->
    Prims.string Prims.list ->
      FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option
  =
  fun env  ->
    fun path  ->
      let uu____4982 =
        FStar_List.tryFind
          (fun uu____4997  ->
             match uu____4997 with
             | (mlid,modul) ->
                 let uu____5004 = FStar_Ident.path_of_lid mlid in
                 uu____5004 = path) env.modules in
      match uu____4982 with
      | FStar_Pervasives_Native.Some (uu____5011,modul) ->
          FStar_Pervasives_Native.Some modul
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
let try_lookup_let:
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___261_5041 =
        match uu___261_5041 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               ((uu____5048,lbs),uu____5050);
             FStar_Syntax_Syntax.sigrng = uu____5051;
             FStar_Syntax_Syntax.sigquals = uu____5052;
             FStar_Syntax_Syntax.sigmeta = uu____5053;
             FStar_Syntax_Syntax.sigattrs = uu____5054;_},uu____5055)
            ->
            let fv = lb_fv lbs lid1 in
            let uu____5075 =
              FStar_Syntax_Syntax.fvar lid1 fv.FStar_Syntax_Syntax.fv_delta
                fv.FStar_Syntax_Syntax.fv_qual in
            FStar_Pervasives_Native.Some uu____5075
        | uu____5076 -> FStar_Pervasives_Native.None in
      resolve_in_open_namespaces' env lid
        (fun uu____5082  -> FStar_Pervasives_Native.None)
        (fun uu____5084  -> FStar_Pervasives_Native.None) k_global_def
let try_lookup_definition:
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___262_5107 =
        match uu___262_5107 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               (lbs,uu____5117);
             FStar_Syntax_Syntax.sigrng = uu____5118;
             FStar_Syntax_Syntax.sigquals = uu____5119;
             FStar_Syntax_Syntax.sigmeta = uu____5120;
             FStar_Syntax_Syntax.sigattrs = uu____5121;_},uu____5122)
            ->
            FStar_Util.find_map (FStar_Pervasives_Native.snd lbs)
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inr fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv lid1 ->
                     FStar_Pervasives_Native.Some
                       (lb.FStar_Syntax_Syntax.lbdef)
                 | uu____5145 -> FStar_Pervasives_Native.None)
        | uu____5152 -> FStar_Pervasives_Native.None in
      resolve_in_open_namespaces' env lid
        (fun uu____5162  -> FStar_Pervasives_Native.None)
        (fun uu____5166  -> FStar_Pervasives_Native.None) k_global_def
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
          let uu____5205 = try_lookup_name any_val exclude_interface env lid in
          match uu____5205 with
          | FStar_Pervasives_Native.Some (Term_name (e,mut)) ->
              FStar_Pervasives_Native.Some (e, mut)
          | uu____5220 -> FStar_Pervasives_Native.None
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
      let uu____5247 = try_lookup_lid env l in
      match uu____5247 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (e,uu____5261) ->
          let uu____5266 =
            let uu____5267 = FStar_Syntax_Subst.compress e in
            uu____5267.FStar_Syntax_Syntax.n in
          (match uu____5266 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               FStar_Pervasives_Native.Some
                 ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
           | uu____5273 -> FStar_Pervasives_Native.None)
let try_lookup_lid_no_resolve:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term,Prims.bool) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let env' =
        let uu___283_5287 = env in
        {
          curmodule = (uu___283_5287.curmodule);
          curmonad = (uu___283_5287.curmonad);
          modules = (uu___283_5287.modules);
          scope_mods = [];
          exported_ids = empty_exported_id_smap;
          trans_exported_ids = (uu___283_5287.trans_exported_ids);
          includes = empty_include_smap;
          sigaccum = (uu___283_5287.sigaccum);
          sigmap = (uu___283_5287.sigmap);
          iface = (uu___283_5287.iface);
          admitted_iface = (uu___283_5287.admitted_iface);
          expect_typ = (uu___283_5287.expect_typ);
          docs = (uu___283_5287.docs);
          remaining_iface_decls = (uu___283_5287.remaining_iface_decls);
          syntax_only = (uu___283_5287.syntax_only);
          ds_hooks = (uu___283_5287.ds_hooks)
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
      let k_global_def lid1 uu___264_5316 =
        match uu___264_5316 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____5323,uu____5324,uu____5325);
             FStar_Syntax_Syntax.sigrng = uu____5326;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____5328;
             FStar_Syntax_Syntax.sigattrs = uu____5329;_},uu____5330)
            ->
            let uu____5335 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___263_5339  ->
                      match uu___263_5339 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | uu____5340 -> false)) in
            if uu____5335
            then
              let uu____5343 =
                FStar_Syntax_Syntax.lid_as_fv lid1
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None in
              FStar_Pervasives_Native.Some uu____5343
            else FStar_Pervasives_Native.None
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
               uu____5345;
             FStar_Syntax_Syntax.sigrng = uu____5346;
             FStar_Syntax_Syntax.sigquals = uu____5347;
             FStar_Syntax_Syntax.sigmeta = uu____5348;
             FStar_Syntax_Syntax.sigattrs = uu____5349;_},uu____5350)
            ->
            let uu____5369 =
              FStar_Syntax_Syntax.lid_as_fv lid1
                FStar_Syntax_Syntax.Delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor) in
            FStar_Pervasives_Native.Some uu____5369
        | uu____5370 -> FStar_Pervasives_Native.None in
      resolve_in_open_namespaces' env lid
        (fun uu____5376  -> FStar_Pervasives_Native.None)
        (fun uu____5378  -> FStar_Pervasives_Native.None) k_global_def
let find_all_datacons:
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident Prims.list FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___265_5403 =
        match uu___265_5403 with
        | ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_inductive_typ
               (uu____5412,uu____5413,uu____5414,uu____5415,datas,uu____5417);
             FStar_Syntax_Syntax.sigrng = uu____5418;
             FStar_Syntax_Syntax.sigquals = uu____5419;
             FStar_Syntax_Syntax.sigmeta = uu____5420;
             FStar_Syntax_Syntax.sigattrs = uu____5421;_},uu____5422)
            -> FStar_Pervasives_Native.Some datas
        | uu____5437 -> FStar_Pervasives_Native.None in
      resolve_in_open_namespaces' env lid
        (fun uu____5447  -> FStar_Pervasives_Native.None)
        (fun uu____5451  -> FStar_Pervasives_Native.None) k_global_def
let record_cache_aux_with_filter:
  ((Prims.unit -> Prims.unit,Prims.unit -> Prims.unit,Prims.unit ->
                                                        record_or_dc
                                                          Prims.list,
     record_or_dc -> Prims.unit) FStar_Pervasives_Native.tuple4,Prims.unit ->
                                                                  Prims.unit)
    FStar_Pervasives_Native.tuple2
  =
  let record_cache = FStar_Util.mk_ref [[]] in
  let push1 uu____5496 =
    let uu____5497 =
      let uu____5502 =
        let uu____5505 = FStar_ST.op_Bang record_cache in
        FStar_List.hd uu____5505 in
      let uu____5580 = FStar_ST.op_Bang record_cache in uu____5502 ::
        uu____5580 in
    FStar_ST.op_Colon_Equals record_cache uu____5497 in
  let pop1 uu____5726 =
    let uu____5727 =
      let uu____5732 = FStar_ST.op_Bang record_cache in
      FStar_List.tl uu____5732 in
    FStar_ST.op_Colon_Equals record_cache uu____5727 in
  let peek1 uu____5880 =
    let uu____5881 = FStar_ST.op_Bang record_cache in
    FStar_List.hd uu____5881 in
  let insert r =
    let uu____5960 =
      let uu____5965 = let uu____5968 = peek1 () in r :: uu____5968 in
      let uu____5971 =
        let uu____5976 = FStar_ST.op_Bang record_cache in
        FStar_List.tl uu____5976 in
      uu____5965 :: uu____5971 in
    FStar_ST.op_Colon_Equals record_cache uu____5960 in
  let filter1 uu____6124 =
    let rc = peek1 () in
    let filtered =
      FStar_List.filter
        (fun r  -> Prims.op_Negation r.is_private_or_abstract) rc in
    let uu____6133 =
      let uu____6138 =
        let uu____6143 = FStar_ST.op_Bang record_cache in
        FStar_List.tl uu____6143 in
      filtered :: uu____6138 in
    FStar_ST.op_Colon_Equals record_cache uu____6133 in
  let aux = (push1, pop1, peek1, insert) in (aux, filter1)
let record_cache_aux:
  (Prims.unit -> Prims.unit,Prims.unit -> Prims.unit,Prims.unit ->
                                                       record_or_dc
                                                         Prims.list,record_or_dc
                                                                    ->
                                                                    Prims.unit)
    FStar_Pervasives_Native.tuple4
  =
  let uu____6355 = record_cache_aux_with_filter in
  match uu____6355 with | (aux,uu____6399) -> aux
let filter_record_cache: Prims.unit -> Prims.unit =
  let uu____6442 = record_cache_aux_with_filter in
  match uu____6442 with | (uu____6469,filter1) -> filter1
let push_record_cache: Prims.unit -> Prims.unit =
  let uu____6513 = record_cache_aux in
  match uu____6513 with | (push1,uu____6535,uu____6536,uu____6537) -> push1
let pop_record_cache: Prims.unit -> Prims.unit =
  let uu____6560 = record_cache_aux in
  match uu____6560 with | (uu____6581,pop1,uu____6583,uu____6584) -> pop1
let peek_record_cache: Prims.unit -> record_or_dc Prims.list =
  let uu____6609 = record_cache_aux in
  match uu____6609 with | (uu____6632,uu____6633,peek1,uu____6635) -> peek1
let insert_record_cache: record_or_dc -> Prims.unit =
  let uu____6658 = record_cache_aux in
  match uu____6658 with | (uu____6679,uu____6680,uu____6681,insert) -> insert
let extract_record:
  env ->
    scope_mod Prims.list FStar_ST.ref ->
      FStar_Syntax_Syntax.sigelt -> Prims.unit
  =
  fun e  ->
    fun new_globs  ->
      fun se  ->
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_bundle (sigs,uu____6735) ->
            let is_record =
              FStar_Util.for_some
                (fun uu___266_6751  ->
                   match uu___266_6751 with
                   | FStar_Syntax_Syntax.RecordType uu____6752 -> true
                   | FStar_Syntax_Syntax.RecordConstructor uu____6761 -> true
                   | uu____6770 -> false) in
            let find_dc dc =
              FStar_All.pipe_right sigs
                (FStar_Util.find_opt
                   (fun uu___267_6792  ->
                      match uu___267_6792 with
                      | {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_datacon
                            (lid,uu____6794,uu____6795,uu____6796,uu____6797,uu____6798);
                          FStar_Syntax_Syntax.sigrng = uu____6799;
                          FStar_Syntax_Syntax.sigquals = uu____6800;
                          FStar_Syntax_Syntax.sigmeta = uu____6801;
                          FStar_Syntax_Syntax.sigattrs = uu____6802;_} ->
                          FStar_Ident.lid_equals dc lid
                      | uu____6811 -> false)) in
            FStar_All.pipe_right sigs
              (FStar_List.iter
                 (fun uu___268_6846  ->
                    match uu___268_6846 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ
                          (typename,univs1,parms,uu____6850,uu____6851,dc::[]);
                        FStar_Syntax_Syntax.sigrng = uu____6853;
                        FStar_Syntax_Syntax.sigquals = typename_quals;
                        FStar_Syntax_Syntax.sigmeta = uu____6855;
                        FStar_Syntax_Syntax.sigattrs = uu____6856;_} ->
                        let uu____6867 =
                          let uu____6868 = find_dc dc in
                          FStar_All.pipe_left FStar_Util.must uu____6868 in
                        (match uu____6867 with
                         | {
                             FStar_Syntax_Syntax.sigel =
                               FStar_Syntax_Syntax.Sig_datacon
                               (constrname,uu____6874,t,uu____6876,uu____6877,uu____6878);
                             FStar_Syntax_Syntax.sigrng = uu____6879;
                             FStar_Syntax_Syntax.sigquals = uu____6880;
                             FStar_Syntax_Syntax.sigmeta = uu____6881;
                             FStar_Syntax_Syntax.sigattrs = uu____6882;_} ->
                             let uu____6891 =
                               FStar_Syntax_Util.arrow_formals t in
                             (match uu____6891 with
                              | (formals,uu____6905) ->
                                  let is_rec = is_record typename_quals in
                                  let formals' =
                                    FStar_All.pipe_right formals
                                      (FStar_List.collect
                                         (fun uu____6954  ->
                                            match uu____6954 with
                                            | (x,q) ->
                                                let uu____6967 =
                                                  (FStar_Syntax_Syntax.is_null_bv
                                                     x)
                                                    ||
                                                    (is_rec &&
                                                       (FStar_Syntax_Syntax.is_implicit
                                                          q)) in
                                                if uu____6967
                                                then []
                                                else [(x, q)])) in
                                  let fields' =
                                    FStar_All.pipe_right formals'
                                      (FStar_List.map
                                         (fun uu____7024  ->
                                            match uu____7024 with
                                            | (x,q) ->
                                                let uu____7037 =
                                                  if is_rec
                                                  then
                                                    FStar_Syntax_Util.unmangle_field_name
                                                      x.FStar_Syntax_Syntax.ppname
                                                  else
                                                    x.FStar_Syntax_Syntax.ppname in
                                                (uu____7037,
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
                                  ((let uu____7052 =
                                      let uu____7055 =
                                        FStar_ST.op_Bang new_globs in
                                      (Record_or_dc record) :: uu____7055 in
                                    FStar_ST.op_Colon_Equals new_globs
                                      uu____7052);
                                   (match () with
                                    | () ->
                                        ((let add_field uu____7196 =
                                            match uu____7196 with
                                            | (id,uu____7204) ->
                                                let modul =
                                                  let uu____7210 =
                                                    FStar_Ident.lid_of_ids
                                                      constrname.FStar_Ident.ns in
                                                  uu____7210.FStar_Ident.str in
                                                let uu____7211 =
                                                  get_exported_id_set e modul in
                                                (match uu____7211 with
                                                 | FStar_Pervasives_Native.Some
                                                     my_ex ->
                                                     let my_exported_ids =
                                                       my_ex
                                                         Exported_id_field in
                                                     ((let uu____7238 =
                                                         let uu____7239 =
                                                           FStar_ST.op_Bang
                                                             my_exported_ids in
                                                         FStar_Util.set_add
                                                           id.FStar_Ident.idText
                                                           uu____7239 in
                                                       FStar_ST.op_Colon_Equals
                                                         my_exported_ids
                                                         uu____7238);
                                                      (match () with
                                                       | () ->
                                                           let projname =
                                                             let uu____7363 =
                                                               let uu____7364
                                                                 =
                                                                 FStar_Syntax_Util.mk_field_projector_name_from_ident
                                                                   constrname
                                                                   id in
                                                               uu____7364.FStar_Ident.ident in
                                                             uu____7363.FStar_Ident.idText in
                                                           let uu____7366 =
                                                             let uu____7367 =
                                                               FStar_ST.op_Bang
                                                                 my_exported_ids in
                                                             FStar_Util.set_add
                                                               projname
                                                               uu____7367 in
                                                           FStar_ST.op_Colon_Equals
                                                             my_exported_ids
                                                             uu____7366))
                                                 | FStar_Pervasives_Native.None
                                                      -> ()) in
                                          FStar_List.iter add_field fields');
                                         (match () with
                                          | () -> insert_record_cache record)))))
                         | uu____7500 -> ())
                    | uu____7501 -> ()))
        | uu____7502 -> ()
let try_lookup_record_or_dc_by_field_name:
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option =
  fun env  ->
    fun fieldname  ->
      let find_in_cache fieldname1 =
        let uu____7517 =
          ((fieldname1.FStar_Ident.ns), (fieldname1.FStar_Ident.ident)) in
        match uu____7517 with
        | (ns,id) ->
            let uu____7534 = peek_record_cache () in
            FStar_Util.find_map uu____7534
              (fun record  ->
                 let uu____7540 =
                   find_in_record ns id record (fun r  -> Cont_ok r) in
                 option_of_cont
                   (fun uu____7546  -> FStar_Pervasives_Native.None)
                   uu____7540) in
      resolve_in_open_namespaces'' env fieldname Exported_id_field
        (fun uu____7548  -> Cont_ignore) (fun uu____7550  -> Cont_ignore)
        (fun r  -> Cont_ok r)
        (fun fn  ->
           let uu____7556 = find_in_cache fn in
           cont_of_option Cont_ignore uu____7556)
        (fun k  -> fun uu____7562  -> k)
let try_lookup_record_by_field_name:
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option =
  fun env  ->
    fun fieldname  ->
      let uu____7573 = try_lookup_record_or_dc_by_field_name env fieldname in
      match uu____7573 with
      | FStar_Pervasives_Native.Some r when r.is_record ->
          FStar_Pervasives_Native.Some r
      | uu____7579 -> FStar_Pervasives_Native.None
let belongs_to_record:
  env -> FStar_Ident.lident -> record_or_dc -> Prims.bool =
  fun env  ->
    fun lid  ->
      fun record  ->
        let uu____7591 = try_lookup_record_by_field_name env lid in
        match uu____7591 with
        | FStar_Pervasives_Native.Some record' when
            let uu____7595 =
              let uu____7596 =
                FStar_Ident.path_of_ns (record.typename).FStar_Ident.ns in
              FStar_Ident.text_of_path uu____7596 in
            let uu____7599 =
              let uu____7600 =
                FStar_Ident.path_of_ns (record'.typename).FStar_Ident.ns in
              FStar_Ident.text_of_path uu____7600 in
            uu____7595 = uu____7599 ->
            let uu____7603 =
              find_in_record (record.typename).FStar_Ident.ns
                lid.FStar_Ident.ident record (fun uu____7607  -> Cont_ok ()) in
            (match uu____7603 with
             | Cont_ok uu____7608 -> true
             | uu____7609 -> false)
        | uu____7612 -> false
let try_lookup_dc_by_field_name:
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident,Prims.bool) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option
  =
  fun env  ->
    fun fieldname  ->
      let uu____7627 = try_lookup_record_or_dc_by_field_name env fieldname in
      match uu____7627 with
      | FStar_Pervasives_Native.Some r ->
          let uu____7637 =
            let uu____7642 =
              let uu____7643 =
                FStar_Ident.lid_of_ids
                  (FStar_List.append (r.typename).FStar_Ident.ns
                     [r.constrname]) in
              FStar_Ident.set_lid_range uu____7643
                (FStar_Ident.range_of_lid fieldname) in
            (uu____7642, (r.is_record)) in
          FStar_Pervasives_Native.Some uu____7637
      | uu____7648 -> FStar_Pervasives_Native.None
let string_set_ref_new:
  Prims.unit -> Prims.string FStar_Util.set FStar_ST.ref =
  fun uu____7668  ->
    let uu____7669 = FStar_Util.new_set FStar_Util.compare in
    FStar_Util.mk_ref uu____7669
let exported_id_set_new:
  Prims.unit -> exported_id_kind -> Prims.string FStar_Util.set FStar_ST.ref
  =
  fun uu____7689  ->
    let term_type_set = string_set_ref_new () in
    let field_set = string_set_ref_new () in
    fun uu___269_7700  ->
      match uu___269_7700 with
      | Exported_id_term_type  -> term_type_set
      | Exported_id_field  -> field_set
let unique:
  Prims.bool -> Prims.bool -> env -> FStar_Ident.lident -> Prims.bool =
  fun any_val  ->
    fun exclude_interface  ->
      fun env  ->
        fun lid  ->
          let filter_scope_mods uu___270_7734 =
            match uu___270_7734 with
            | Rec_binding uu____7735 -> true
            | uu____7736 -> false in
          let this_env =
            let uu___284_7738 = env in
            let uu____7739 =
              FStar_List.filter filter_scope_mods env.scope_mods in
            {
              curmodule = (uu___284_7738.curmodule);
              curmonad = (uu___284_7738.curmonad);
              modules = (uu___284_7738.modules);
              scope_mods = uu____7739;
              exported_ids = empty_exported_id_smap;
              trans_exported_ids = (uu___284_7738.trans_exported_ids);
              includes = empty_include_smap;
              sigaccum = (uu___284_7738.sigaccum);
              sigmap = (uu___284_7738.sigmap);
              iface = (uu___284_7738.iface);
              admitted_iface = (uu___284_7738.admitted_iface);
              expect_typ = (uu___284_7738.expect_typ);
              docs = (uu___284_7738.docs);
              remaining_iface_decls = (uu___284_7738.remaining_iface_decls);
              syntax_only = (uu___284_7738.syntax_only);
              ds_hooks = (uu___284_7738.ds_hooks)
            } in
          let uu____7742 =
            try_lookup_lid' any_val exclude_interface this_env lid in
          match uu____7742 with
          | FStar_Pervasives_Native.None  -> true
          | FStar_Pervasives_Native.Some uu____7753 -> false
let push_scope_mod: env -> scope_mod -> env =
  fun env  ->
    fun scope_mod  ->
      let uu___285_7768 = env in
      {
        curmodule = (uu___285_7768.curmodule);
        curmonad = (uu___285_7768.curmonad);
        modules = (uu___285_7768.modules);
        scope_mods = (scope_mod :: (env.scope_mods));
        exported_ids = (uu___285_7768.exported_ids);
        trans_exported_ids = (uu___285_7768.trans_exported_ids);
        includes = (uu___285_7768.includes);
        sigaccum = (uu___285_7768.sigaccum);
        sigmap = (uu___285_7768.sigmap);
        iface = (uu___285_7768.iface);
        admitted_iface = (uu___285_7768.admitted_iface);
        expect_typ = (uu___285_7768.expect_typ);
        docs = (uu___285_7768.docs);
        remaining_iface_decls = (uu___285_7768.remaining_iface_decls);
        syntax_only = (uu___285_7768.syntax_only);
        ds_hooks = (uu___285_7768.ds_hooks)
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
        let uu____7813 =
          (unique false true env l) || (FStar_Options.interactive ()) in
        if uu____7813
        then push_scope_mod env (Rec_binding (x, l, dd))
        else
          FStar_Exn.raise
            (FStar_Errors.Error
               ((Prims.strcat "Duplicate top-level names " l.FStar_Ident.str),
                 (FStar_Ident.range_of_lid l)))
let push_sigelt: env -> FStar_Syntax_Syntax.sigelt -> env =
  fun env  ->
    fun s  ->
      let err1 l =
        let sopt = FStar_Util.smap_try_find (sigmap env) l.FStar_Ident.str in
        let r =
          match sopt with
          | FStar_Pervasives_Native.Some (se,uu____7838) ->
              let uu____7843 =
                FStar_Util.find_opt (FStar_Ident.lid_equals l)
                  (FStar_Syntax_Util.lids_of_sigelt se) in
              (match uu____7843 with
               | FStar_Pervasives_Native.Some l1 ->
                   FStar_All.pipe_left FStar_Range.string_of_range
                     (FStar_Ident.range_of_lid l1)
               | FStar_Pervasives_Native.None  -> "<unknown>")
          | FStar_Pervasives_Native.None  -> "<unknown>" in
        let uu____7851 =
          let uu____7852 =
            let uu____7857 =
              FStar_Util.format2
                "Duplicate top-level names [%s]; previously declared at %s"
                (FStar_Ident.text_of_lid l) r in
            (uu____7857, (FStar_Ident.range_of_lid l)) in
          FStar_Errors.Error uu____7852 in
        FStar_Exn.raise uu____7851 in
      let globals = FStar_Util.mk_ref env.scope_mods in
      let env1 =
        let uu____7866 =
          match s.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let uu____7875 -> (false, true)
          | FStar_Syntax_Syntax.Sig_bundle uu____7882 -> (false, true)
          | uu____7891 -> (false, false) in
        match uu____7866 with
        | (any_val,exclude_interface) ->
            let lids = FStar_Syntax_Util.lids_of_sigelt s in
            let uu____7897 =
              FStar_Util.find_map lids
                (fun l  ->
                   let uu____7903 =
                     let uu____7904 = unique any_val exclude_interface env l in
                     Prims.op_Negation uu____7904 in
                   if uu____7903
                   then FStar_Pervasives_Native.Some l
                   else FStar_Pervasives_Native.None) in
            (match uu____7897 with
             | FStar_Pervasives_Native.Some l -> err1 l
             | uu____7909 ->
                 (extract_record env globals s;
                  (let uu___286_7927 = env in
                   {
                     curmodule = (uu___286_7927.curmodule);
                     curmonad = (uu___286_7927.curmonad);
                     modules = (uu___286_7927.modules);
                     scope_mods = (uu___286_7927.scope_mods);
                     exported_ids = (uu___286_7927.exported_ids);
                     trans_exported_ids = (uu___286_7927.trans_exported_ids);
                     includes = (uu___286_7927.includes);
                     sigaccum = (s :: (env.sigaccum));
                     sigmap = (uu___286_7927.sigmap);
                     iface = (uu___286_7927.iface);
                     admitted_iface = (uu___286_7927.admitted_iface);
                     expect_typ = (uu___286_7927.expect_typ);
                     docs = (uu___286_7927.docs);
                     remaining_iface_decls =
                       (uu___286_7927.remaining_iface_decls);
                     syntax_only = (uu___286_7927.syntax_only);
                     ds_hooks = (uu___286_7927.ds_hooks)
                   }))) in
      let env2 =
        let uu___287_7929 = env1 in
        let uu____7930 = FStar_ST.op_Bang globals in
        {
          curmodule = (uu___287_7929.curmodule);
          curmonad = (uu___287_7929.curmonad);
          modules = (uu___287_7929.modules);
          scope_mods = uu____7930;
          exported_ids = (uu___287_7929.exported_ids);
          trans_exported_ids = (uu___287_7929.trans_exported_ids);
          includes = (uu___287_7929.includes);
          sigaccum = (uu___287_7929.sigaccum);
          sigmap = (uu___287_7929.sigmap);
          iface = (uu___287_7929.iface);
          admitted_iface = (uu___287_7929.admitted_iface);
          expect_typ = (uu___287_7929.expect_typ);
          docs = (uu___287_7929.docs);
          remaining_iface_decls = (uu___287_7929.remaining_iface_decls);
          syntax_only = (uu___287_7929.syntax_only);
          ds_hooks = (uu___287_7929.ds_hooks)
        } in
      let uu____7997 =
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_bundle (ses,uu____8023) ->
            let uu____8032 =
              FStar_List.map
                (fun se  -> ((FStar_Syntax_Util.lids_of_sigelt se), se)) ses in
            (env2, uu____8032)
        | uu____8059 -> (env2, [((FStar_Syntax_Util.lids_of_sigelt s), s)]) in
      match uu____7997 with
      | (env3,lss) ->
          (FStar_All.pipe_right lss
             (FStar_List.iter
                (fun uu____8118  ->
                   match uu____8118 with
                   | (lids,se) ->
                       FStar_All.pipe_right lids
                         (FStar_List.iter
                            (fun lid  ->
                               (let uu____8140 =
                                  let uu____8143 = FStar_ST.op_Bang globals in
                                  (Top_level_def (lid.FStar_Ident.ident)) ::
                                    uu____8143 in
                                FStar_ST.op_Colon_Equals globals uu____8140);
                               (match () with
                                | () ->
                                    let modul =
                                      let uu____8275 =
                                        FStar_Ident.lid_of_ids
                                          lid.FStar_Ident.ns in
                                      uu____8275.FStar_Ident.str in
                                    ((let uu____8277 =
                                        get_exported_id_set env3 modul in
                                      match uu____8277 with
                                      | FStar_Pervasives_Native.Some f ->
                                          let my_exported_ids =
                                            f Exported_id_term_type in
                                          let uu____8303 =
                                            let uu____8304 =
                                              FStar_ST.op_Bang
                                                my_exported_ids in
                                            FStar_Util.set_add
                                              (lid.FStar_Ident.ident).FStar_Ident.idText
                                              uu____8304 in
                                          FStar_ST.op_Colon_Equals
                                            my_exported_ids uu____8303
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
              let uu___288_8437 = env3 in
              let uu____8438 = FStar_ST.op_Bang globals in
              {
                curmodule = (uu___288_8437.curmodule);
                curmonad = (uu___288_8437.curmonad);
                modules = (uu___288_8437.modules);
                scope_mods = uu____8438;
                exported_ids = (uu___288_8437.exported_ids);
                trans_exported_ids = (uu___288_8437.trans_exported_ids);
                includes = (uu___288_8437.includes);
                sigaccum = (uu___288_8437.sigaccum);
                sigmap = (uu___288_8437.sigmap);
                iface = (uu___288_8437.iface);
                admitted_iface = (uu___288_8437.admitted_iface);
                expect_typ = (uu___288_8437.expect_typ);
                docs = (uu___288_8437.docs);
                remaining_iface_decls = (uu___288_8437.remaining_iface_decls);
                syntax_only = (uu___288_8437.syntax_only);
                ds_hooks = (uu___288_8437.ds_hooks)
              } in
            env4))
let push_namespace: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun ns  ->
      let uu____8511 =
        let uu____8516 = resolve_module_name env ns false in
        match uu____8516 with
        | FStar_Pervasives_Native.None  ->
            let modules = env.modules in
            let uu____8530 =
              FStar_All.pipe_right modules
                (FStar_Util.for_some
                   (fun uu____8544  ->
                      match uu____8544 with
                      | (m,uu____8550) ->
                          FStar_Util.starts_with
                            (Prims.strcat (FStar_Ident.text_of_lid m) ".")
                            (Prims.strcat (FStar_Ident.text_of_lid ns) "."))) in
            if uu____8530
            then (ns, Open_namespace)
            else
              (let uu____8556 =
                 let uu____8557 =
                   let uu____8562 =
                     FStar_Util.format1 "Namespace %s cannot be found"
                       (FStar_Ident.text_of_lid ns) in
                   (uu____8562, (FStar_Ident.range_of_lid ns)) in
                 FStar_Errors.Error uu____8557 in
               FStar_Exn.raise uu____8556)
        | FStar_Pervasives_Native.Some ns' ->
            (fail_if_curmodule env ns ns'; (ns', Open_module)) in
      match uu____8511 with
      | (ns',kd) ->
          ((env.ds_hooks).ds_push_open_hook env (ns', kd);
           push_scope_mod env (Open_module_or_namespace (ns', kd)))
let push_include: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun ns  ->
      let ns0 = ns in
      let uu____8579 = resolve_module_name env ns false in
      match uu____8579 with
      | FStar_Pervasives_Native.Some ns1 ->
          ((env.ds_hooks).ds_push_include_hook env ns1;
           fail_if_curmodule env ns0 ns1;
           (let env1 =
              push_scope_mod env
                (Open_module_or_namespace (ns1, Open_module)) in
            let curmod =
              let uu____8587 = current_module env1 in
              uu____8587.FStar_Ident.str in
            (let uu____8589 = FStar_Util.smap_try_find env1.includes curmod in
             match uu____8589 with
             | FStar_Pervasives_Native.None  -> ()
             | FStar_Pervasives_Native.Some incl ->
                 let uu____8613 =
                   let uu____8616 = FStar_ST.op_Bang incl in ns1 ::
                     uu____8616 in
                 FStar_ST.op_Colon_Equals incl uu____8613);
            (match () with
             | () ->
                 let uu____8747 =
                   get_trans_exported_id_set env1 ns1.FStar_Ident.str in
                 (match uu____8747 with
                  | FStar_Pervasives_Native.Some ns_trans_exports ->
                      ((let uu____8764 =
                          let uu____8781 = get_exported_id_set env1 curmod in
                          let uu____8788 =
                            get_trans_exported_id_set env1 curmod in
                          (uu____8781, uu____8788) in
                        match uu____8764 with
                        | (FStar_Pervasives_Native.Some
                           cur_exports,FStar_Pervasives_Native.Some
                           cur_trans_exports) ->
                            let update_exports k =
                              let ns_ex =
                                let uu____8842 = ns_trans_exports k in
                                FStar_ST.op_Bang uu____8842 in
                              let ex = cur_exports k in
                              (let uu____9097 =
                                 let uu____9098 = FStar_ST.op_Bang ex in
                                 FStar_Util.set_difference uu____9098 ns_ex in
                               FStar_ST.op_Colon_Equals ex uu____9097);
                              (match () with
                               | () ->
                                   let trans_ex = cur_trans_exports k in
                                   let uu____9232 =
                                     let uu____9233 =
                                       FStar_ST.op_Bang trans_ex in
                                     FStar_Util.set_union uu____9233 ns_ex in
                                   FStar_ST.op_Colon_Equals trans_ex
                                     uu____9232) in
                            FStar_List.iter update_exports
                              all_exported_id_kinds
                        | uu____9356 -> ());
                       (match () with | () -> env1))
                  | FStar_Pervasives_Native.None  ->
                      let uu____9377 =
                        let uu____9378 =
                          let uu____9383 =
                            FStar_Util.format1
                              "include: Module %s was not prepared"
                              ns1.FStar_Ident.str in
                          (uu____9383, (FStar_Ident.range_of_lid ns1)) in
                        FStar_Errors.Error uu____9378 in
                      FStar_Exn.raise uu____9377))))
      | uu____9384 ->
          let uu____9387 =
            let uu____9388 =
              let uu____9393 =
                FStar_Util.format1 "include: Module %s cannot be found"
                  ns.FStar_Ident.str in
              (uu____9393, (FStar_Ident.range_of_lid ns)) in
            FStar_Errors.Error uu____9388 in
          FStar_Exn.raise uu____9387
let push_module_abbrev: env -> FStar_Ident.ident -> FStar_Ident.lident -> env
  =
  fun env  ->
    fun x  ->
      fun l  ->
        let uu____9403 = module_is_defined env l in
        if uu____9403
        then
          (fail_if_curmodule env l l;
           (env.ds_hooks).ds_push_module_abbrev_hook env x l;
           push_scope_mod env (Module_abbrev (x, l)))
        else
          (let uu____9407 =
             let uu____9408 =
               let uu____9413 =
                 FStar_Util.format1 "Module %s cannot be found"
                   (FStar_Ident.text_of_lid l) in
               (uu____9413, (FStar_Ident.range_of_lid l)) in
             FStar_Errors.Error uu____9408 in
           FStar_Exn.raise uu____9407)
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
            ((let uu____9429 =
                FStar_Util.smap_try_find env.docs l.FStar_Ident.str in
              match uu____9429 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some old_doc ->
                  let uu____9433 =
                    let uu____9434 = FStar_Ident.string_of_lid l in
                    let uu____9435 = FStar_Parser_AST.string_of_fsdoc old_doc in
                    let uu____9436 = FStar_Parser_AST.string_of_fsdoc doc1 in
                    FStar_Util.format3
                      "Overwriting doc of %s; old doc was [%s]; new doc are [%s]"
                      uu____9434 uu____9435 uu____9436 in
                  FStar_Errors.warn (FStar_Ident.range_of_lid l) uu____9433);
             FStar_Util.smap_add env.docs l.FStar_Ident.str doc1;
             env)
let check_admits: env -> Prims.unit =
  fun env  ->
    FStar_All.pipe_right env.sigaccum
      (FStar_List.iter
         (fun se  ->
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t) ->
                let uu____9452 = try_lookup_lid env l in
                (match uu____9452 with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____9464 =
                         let uu____9465 = FStar_Options.interactive () in
                         Prims.op_Negation uu____9465 in
                       if uu____9464
                       then
                         let uu____9466 =
                           let uu____9467 =
                             FStar_Syntax_Print.lid_to_string l in
                           FStar_Util.format1
                             "Admitting %s without a definition" uu____9467 in
                         FStar_Errors.warn (FStar_Ident.range_of_lid l)
                           uu____9466
                       else ());
                      (let quals = FStar_Syntax_Syntax.Assumption ::
                         (se.FStar_Syntax_Syntax.sigquals) in
                       FStar_Util.smap_add (sigmap env) l.FStar_Ident.str
                         ((let uu___289_9477 = se in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (uu___289_9477.FStar_Syntax_Syntax.sigel);
                             FStar_Syntax_Syntax.sigrng =
                               (uu___289_9477.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals = quals;
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___289_9477.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___289_9477.FStar_Syntax_Syntax.sigattrs)
                           }), false)))
                 | FStar_Pervasives_Native.Some uu____9478 -> ())
            | uu____9487 -> ()))
let finish: env -> FStar_Syntax_Syntax.modul -> env =
  fun env  ->
    fun modul  ->
      FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations
        (FStar_List.iter
           (fun se  ->
              let quals = se.FStar_Syntax_Syntax.sigquals in
              match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_bundle (ses,uu____9504) ->
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
                                (lid,uu____9524,uu____9525,uu____9526,uu____9527,uu____9528)
                                ->
                                FStar_Util.smap_remove (sigmap env)
                                  lid.FStar_Ident.str
                            | uu____9537 -> ()))
                  else ()
              | FStar_Syntax_Syntax.Sig_declare_typ
                  (lid,uu____9540,uu____9541) ->
                  if FStar_List.contains FStar_Syntax_Syntax.Private quals
                  then
                    FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str
                  else ()
              | FStar_Syntax_Syntax.Sig_let ((uu____9547,lbs),uu____9549) ->
                  (if
                     (FStar_List.contains FStar_Syntax_Syntax.Private quals)
                       ||
                       (FStar_List.contains FStar_Syntax_Syntax.Abstract
                          quals)
                   then
                     FStar_All.pipe_right lbs
                       (FStar_List.iter
                          (fun lb  ->
                             let uu____9570 =
                               let uu____9571 =
                                 let uu____9572 =
                                   let uu____9575 =
                                     FStar_Util.right
                                       lb.FStar_Syntax_Syntax.lbname in
                                   uu____9575.FStar_Syntax_Syntax.fv_name in
                                 uu____9572.FStar_Syntax_Syntax.v in
                               uu____9571.FStar_Ident.str in
                             FStar_Util.smap_remove (sigmap env) uu____9570))
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
                               let uu____9589 =
                                 let uu____9592 =
                                   FStar_Util.right
                                     lb.FStar_Syntax_Syntax.lbname in
                                 uu____9592.FStar_Syntax_Syntax.fv_name in
                               uu____9589.FStar_Syntax_Syntax.v in
                             let quals1 = FStar_Syntax_Syntax.Assumption ::
                               quals in
                             let decl =
                               let uu___290_9597 = se in
                               {
                                 FStar_Syntax_Syntax.sigel =
                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                      (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                        (lb.FStar_Syntax_Syntax.lbtyp)));
                                 FStar_Syntax_Syntax.sigrng =
                                   (uu___290_9597.FStar_Syntax_Syntax.sigrng);
                                 FStar_Syntax_Syntax.sigquals = quals1;
                                 FStar_Syntax_Syntax.sigmeta =
                                   (uu___290_9597.FStar_Syntax_Syntax.sigmeta);
                                 FStar_Syntax_Syntax.sigattrs =
                                   (uu___290_9597.FStar_Syntax_Syntax.sigattrs)
                               } in
                             FStar_Util.smap_add (sigmap env)
                               lid.FStar_Ident.str (decl, false)))
                   else ())
              | uu____9607 -> ()));
      (let curmod =
         let uu____9609 = current_module env in uu____9609.FStar_Ident.str in
       (let uu____9611 =
          let uu____9628 = get_exported_id_set env curmod in
          let uu____9635 = get_trans_exported_id_set env curmod in
          (uu____9628, uu____9635) in
        match uu____9611 with
        | (FStar_Pervasives_Native.Some cur_ex,FStar_Pervasives_Native.Some
           cur_trans_ex) ->
            let update_exports eikind =
              let cur_ex_set =
                let uu____9689 = cur_ex eikind in FStar_ST.op_Bang uu____9689 in
              let cur_trans_ex_set_ref = cur_trans_ex eikind in
              let uu____9943 =
                let uu____9944 = FStar_ST.op_Bang cur_trans_ex_set_ref in
                FStar_Util.set_union cur_ex_set uu____9944 in
              FStar_ST.op_Colon_Equals cur_trans_ex_set_ref uu____9943 in
            FStar_List.iter update_exports all_exported_id_kinds
        | uu____10067 -> ());
       (match () with
        | () ->
            (filter_record_cache ();
             (match () with
              | () ->
                  let uu___291_10085 = env in
                  {
                    curmodule = FStar_Pervasives_Native.None;
                    curmonad = (uu___291_10085.curmonad);
                    modules = (((modul.FStar_Syntax_Syntax.name), modul) ::
                      (env.modules));
                    scope_mods = [];
                    exported_ids = (uu___291_10085.exported_ids);
                    trans_exported_ids = (uu___291_10085.trans_exported_ids);
                    includes = (uu___291_10085.includes);
                    sigaccum = [];
                    sigmap = (uu___291_10085.sigmap);
                    iface = (uu___291_10085.iface);
                    admitted_iface = (uu___291_10085.admitted_iface);
                    expect_typ = (uu___291_10085.expect_typ);
                    docs = (uu___291_10085.docs);
                    remaining_iface_decls =
                      (uu___291_10085.remaining_iface_decls);
                    syntax_only = (uu___291_10085.syntax_only);
                    ds_hooks = (uu___291_10085.ds_hooks)
                  }))))
let stack: env Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let push: env -> env =
  fun env  ->
    push_record_cache ();
    (let uu____10108 =
       let uu____10111 = FStar_ST.op_Bang stack in env :: uu____10111 in
     FStar_ST.op_Colon_Equals stack uu____10108);
    (let uu___292_10214 = env in
     let uu____10215 = FStar_Util.smap_copy (sigmap env) in
     let uu____10226 = FStar_Util.smap_copy env.docs in
     {
       curmodule = (uu___292_10214.curmodule);
       curmonad = (uu___292_10214.curmonad);
       modules = (uu___292_10214.modules);
       scope_mods = (uu___292_10214.scope_mods);
       exported_ids = (uu___292_10214.exported_ids);
       trans_exported_ids = (uu___292_10214.trans_exported_ids);
       includes = (uu___292_10214.includes);
       sigaccum = (uu___292_10214.sigaccum);
       sigmap = uu____10215;
       iface = (uu___292_10214.iface);
       admitted_iface = (uu___292_10214.admitted_iface);
       expect_typ = (uu___292_10214.expect_typ);
       docs = uu____10226;
       remaining_iface_decls = (uu___292_10214.remaining_iface_decls);
       syntax_only = (uu___292_10214.syntax_only);
       ds_hooks = (uu___292_10214.ds_hooks)
     })
let pop: Prims.unit -> env =
  fun uu____10231  ->
    let uu____10232 = FStar_ST.op_Bang stack in
    match uu____10232 with
    | env::tl1 ->
        (pop_record_cache (); FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____10341 -> failwith "Impossible: Too many pops"
let export_interface: FStar_Ident.lident -> env -> env =
  fun m  ->
    fun env  ->
      let sigelt_in_m se =
        match FStar_Syntax_Util.lids_of_sigelt se with
        | l::uu____10355 -> l.FStar_Ident.nsstr = m.FStar_Ident.str
        | uu____10358 -> false in
      let sm = sigmap env in
      let env1 = pop () in
      let keys = FStar_Util.smap_keys sm in
      let sm' = sigmap env1 in
      FStar_All.pipe_right keys
        (FStar_List.iter
           (fun k  ->
              let uu____10392 = FStar_Util.smap_try_find sm' k in
              match uu____10392 with
              | FStar_Pervasives_Native.Some (se,true ) when sigelt_in_m se
                  ->
                  (FStar_Util.smap_remove sm' k;
                   (let se1 =
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t) ->
                          let uu___293_10417 = se in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (uu___293_10417.FStar_Syntax_Syntax.sigel);
                            FStar_Syntax_Syntax.sigrng =
                              (uu___293_10417.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (FStar_Syntax_Syntax.Assumption ::
                              (se.FStar_Syntax_Syntax.sigquals));
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___293_10417.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___293_10417.FStar_Syntax_Syntax.sigattrs)
                          }
                      | uu____10418 -> se in
                    FStar_Util.smap_add sm' k (se1, false)))
              | uu____10423 -> ()));
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
      let uu____10503 =
        let uu____10506 = e Exported_id_term_type in
        FStar_ST.op_Bang uu____10506 in
      FStar_Util.set_elements uu____10503 in
    let fields =
      let uu____10753 =
        let uu____10756 = e Exported_id_field in FStar_ST.op_Bang uu____10756 in
      FStar_Util.set_elements uu____10753 in
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
          let uu____11032 =
            FStar_Util.as_set e1.exported_id_terms FStar_Util.compare in
          FStar_Util.mk_ref uu____11032 in
        let fields =
          let uu____11042 =
            FStar_Util.as_set e1.exported_id_fields FStar_Util.compare in
          FStar_Util.mk_ref uu____11042 in
        (fun uu___271_11047  ->
           match uu___271_11047 with
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
  'Auu____11155 .
    'Auu____11155 Prims.list FStar_Pervasives_Native.option ->
      'Auu____11155 Prims.list FStar_ST.ref
  =
  fun uu___272_11167  ->
    match uu___272_11167 with
    | FStar_Pervasives_Native.None  -> FStar_Util.mk_ref []
    | FStar_Pervasives_Native.Some l -> FStar_Util.mk_ref l
let inclusion_info: env -> FStar_Ident.lident -> module_inclusion_info =
  fun env  ->
    fun l  ->
      let mname = FStar_Ident.string_of_lid l in
      let as_ids_opt m =
        let uu____11200 = FStar_Util.smap_try_find m mname in
        FStar_Util.map_opt uu____11200 as_exported_ids in
      let uu____11203 = as_ids_opt env.exported_ids in
      let uu____11206 = as_ids_opt env.trans_exported_ids in
      let uu____11209 =
        let uu____11214 = FStar_Util.smap_try_find env.includes mname in
        FStar_Util.map_opt uu____11214 (fun r  -> FStar_ST.op_Bang r) in
      {
        mii_exported_ids = uu____11203;
        mii_trans_exported_ids = uu____11206;
        mii_includes = uu____11209
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
                let convert_kind uu___273_11349 =
                  match uu___273_11349 with
                  | FStar_Parser_Dep.Open_namespace  -> Open_namespace
                  | FStar_Parser_Dep.Open_module  -> Open_module in
                FStar_List.map
                  (fun uu____11361  ->
                     match uu____11361 with
                     | (lid,kind) -> (lid, (convert_kind kind))) auto_open in
              let namespace_of_module =
                if
                  (FStar_List.length mname.FStar_Ident.ns) >
                    (Prims.parse_int "0")
                then
                  let uu____11385 =
                    let uu____11390 =
                      FStar_Ident.lid_of_ids mname.FStar_Ident.ns in
                    (uu____11390, Open_namespace) in
                  [uu____11385]
                else [] in
              let auto_open2 =
                FStar_List.append namespace_of_module
                  (FStar_List.rev auto_open1) in
              (let uu____11420 = as_exported_id_set mii.mii_exported_ids in
               FStar_Util.smap_add env1.exported_ids mname.FStar_Ident.str
                 uu____11420);
              (match () with
               | () ->
                   ((let uu____11436 =
                       as_exported_id_set mii.mii_trans_exported_ids in
                     FStar_Util.smap_add env1.trans_exported_ids
                       mname.FStar_Ident.str uu____11436);
                    (match () with
                     | () ->
                         ((let uu____11452 = as_includes mii.mii_includes in
                           FStar_Util.smap_add env1.includes
                             mname.FStar_Ident.str uu____11452);
                          (match () with
                           | () ->
                               let env' =
                                 let uu___294_11476 = env1 in
                                 let uu____11477 =
                                   FStar_List.map
                                     (fun x  -> Open_module_or_namespace x)
                                     auto_open2 in
                                 {
                                   curmodule =
                                     (FStar_Pervasives_Native.Some mname);
                                   curmonad = (uu___294_11476.curmonad);
                                   modules = (uu___294_11476.modules);
                                   scope_mods = uu____11477;
                                   exported_ids =
                                     (uu___294_11476.exported_ids);
                                   trans_exported_ids =
                                     (uu___294_11476.trans_exported_ids);
                                   includes = (uu___294_11476.includes);
                                   sigaccum = (uu___294_11476.sigaccum);
                                   sigmap = (env1.sigmap);
                                   iface = intf;
                                   admitted_iface = admitted;
                                   expect_typ = (uu___294_11476.expect_typ);
                                   docs = (uu___294_11476.docs);
                                   remaining_iface_decls =
                                     (uu___294_11476.remaining_iface_decls);
                                   syntax_only = (uu___294_11476.syntax_only);
                                   ds_hooks = (uu___294_11476.ds_hooks)
                                 } in
                               (FStar_List.iter
                                  (fun op  ->
                                     (env1.ds_hooks).ds_push_open_hook env'
                                       op) (FStar_List.rev auto_open2);
                                env')))))) in
            let uu____11489 =
              FStar_All.pipe_right env.modules
                (FStar_Util.find_opt
                   (fun uu____11515  ->
                      match uu____11515 with
                      | (l,uu____11521) -> FStar_Ident.lid_equals l mname)) in
            match uu____11489 with
            | FStar_Pervasives_Native.None  ->
                let uu____11530 = prep env in (uu____11530, false)
            | FStar_Pervasives_Native.Some (uu____11531,m) ->
                ((let uu____11538 =
                    (let uu____11541 = FStar_Options.interactive () in
                     Prims.op_Negation uu____11541) &&
                      ((Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)
                         || intf) in
                  if uu____11538
                  then
                    let uu____11542 =
                      let uu____11543 =
                        let uu____11548 =
                          FStar_Util.format1
                            "Duplicate module or interface name: %s"
                            mname.FStar_Ident.str in
                        (uu____11548, (FStar_Ident.range_of_lid mname)) in
                      FStar_Errors.Error uu____11543 in
                    FStar_Exn.raise uu____11542
                  else ());
                 (let uu____11550 =
                    let uu____11551 = push env in prep uu____11551 in
                  (uu____11550, true)))
let enter_monad_scope: env -> FStar_Ident.ident -> env =
  fun env  ->
    fun mname  ->
      match env.curmonad with
      | FStar_Pervasives_Native.Some mname' ->
          FStar_Exn.raise
            (FStar_Errors.Error
               ((Prims.strcat "Trying to define monad "
                   (Prims.strcat mname.FStar_Ident.idText
                      (Prims.strcat ", but already in monad scope "
                         mname'.FStar_Ident.idText))),
                 (mname.FStar_Ident.idRange)))
      | FStar_Pervasives_Native.None  ->
          let uu___295_11559 = env in
          {
            curmodule = (uu___295_11559.curmodule);
            curmonad = (FStar_Pervasives_Native.Some mname);
            modules = (uu___295_11559.modules);
            scope_mods = (uu___295_11559.scope_mods);
            exported_ids = (uu___295_11559.exported_ids);
            trans_exported_ids = (uu___295_11559.trans_exported_ids);
            includes = (uu___295_11559.includes);
            sigaccum = (uu___295_11559.sigaccum);
            sigmap = (uu___295_11559.sigmap);
            iface = (uu___295_11559.iface);
            admitted_iface = (uu___295_11559.admitted_iface);
            expect_typ = (uu___295_11559.expect_typ);
            docs = (uu___295_11559.docs);
            remaining_iface_decls = (uu___295_11559.remaining_iface_decls);
            syntax_only = (uu___295_11559.syntax_only);
            ds_hooks = (uu___295_11559.ds_hooks)
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
        let uu____11586 = lookup lid in
        match uu____11586 with
        | FStar_Pervasives_Native.None  ->
            let opened_modules =
              FStar_List.map
                (fun uu____11599  ->
                   match uu____11599 with
                   | (lid1,uu____11605) -> FStar_Ident.text_of_lid lid1)
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
                   let uu____11610 =
                     FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
                   FStar_Ident.set_lid_range uu____11610
                     (FStar_Ident.range_of_lid lid) in
                 let uu____11611 = resolve_module_name env modul true in
                 match uu____11611 with
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
            FStar_Exn.raise
              (FStar_Errors.Error (msg1, (FStar_Ident.range_of_lid lid)))
        | FStar_Pervasives_Native.Some r -> r
let fail_or2:
  'a .
    (FStar_Ident.ident -> 'a FStar_Pervasives_Native.option) ->
      FStar_Ident.ident -> 'a
  =
  fun lookup  ->
    fun id  ->
      let uu____11642 = lookup id in
      match uu____11642 with
      | FStar_Pervasives_Native.None  ->
          FStar_Exn.raise
            (FStar_Errors.Error
               ((Prims.strcat "Identifier not found ["
                   (Prims.strcat id.FStar_Ident.idText "]")),
                 (id.FStar_Ident.idRange)))
      | FStar_Pervasives_Native.Some r -> r