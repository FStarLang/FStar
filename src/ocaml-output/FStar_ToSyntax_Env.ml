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
      let uu___192_1613 = env in
      {
        curmodule = (uu___192_1613.curmodule);
        curmonad = (uu___192_1613.curmonad);
        modules = (uu___192_1613.modules);
        scope_mods = (uu___192_1613.scope_mods);
        exported_ids = (uu___192_1613.exported_ids);
        trans_exported_ids = (uu___192_1613.trans_exported_ids);
        includes = (uu___192_1613.includes);
        sigaccum = (uu___192_1613.sigaccum);
        sigmap = (uu___192_1613.sigmap);
        iface = b;
        admitted_iface = (uu___192_1613.admitted_iface);
        expect_typ = (uu___192_1613.expect_typ);
        docs = (uu___192_1613.docs);
        remaining_iface_decls = (uu___192_1613.remaining_iface_decls);
        syntax_only = (uu___192_1613.syntax_only);
        ds_hooks = (uu___192_1613.ds_hooks)
      }
let iface: env -> Prims.bool = fun e  -> e.iface
let set_admitted_iface: env -> Prims.bool -> env =
  fun e  ->
    fun b  ->
      let uu___193_1623 = e in
      {
        curmodule = (uu___193_1623.curmodule);
        curmonad = (uu___193_1623.curmonad);
        modules = (uu___193_1623.modules);
        scope_mods = (uu___193_1623.scope_mods);
        exported_ids = (uu___193_1623.exported_ids);
        trans_exported_ids = (uu___193_1623.trans_exported_ids);
        includes = (uu___193_1623.includes);
        sigaccum = (uu___193_1623.sigaccum);
        sigmap = (uu___193_1623.sigmap);
        iface = (uu___193_1623.iface);
        admitted_iface = b;
        expect_typ = (uu___193_1623.expect_typ);
        docs = (uu___193_1623.docs);
        remaining_iface_decls = (uu___193_1623.remaining_iface_decls);
        syntax_only = (uu___193_1623.syntax_only);
        ds_hooks = (uu___193_1623.ds_hooks)
      }
let admitted_iface: env -> Prims.bool = fun e  -> e.admitted_iface
let set_expect_typ: env -> Prims.bool -> env =
  fun e  ->
    fun b  ->
      let uu___194_1633 = e in
      {
        curmodule = (uu___194_1633.curmodule);
        curmonad = (uu___194_1633.curmonad);
        modules = (uu___194_1633.modules);
        scope_mods = (uu___194_1633.scope_mods);
        exported_ids = (uu___194_1633.exported_ids);
        trans_exported_ids = (uu___194_1633.trans_exported_ids);
        includes = (uu___194_1633.includes);
        sigaccum = (uu___194_1633.sigaccum);
        sigmap = (uu___194_1633.sigmap);
        iface = (uu___194_1633.iface);
        admitted_iface = (uu___194_1633.admitted_iface);
        expect_typ = b;
        docs = (uu___194_1633.docs);
        remaining_iface_decls = (uu___194_1633.remaining_iface_decls);
        syntax_only = (uu___194_1633.syntax_only);
        ds_hooks = (uu___194_1633.ds_hooks)
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
      (fun uu___160_1922  ->
         match uu___160_1922 with
         | Open_module_or_namespace (lid,_info) ->
             FStar_Pervasives_Native.Some lid
         | uu____1927 -> FStar_Pervasives_Native.None) env.scope_mods
let set_current_module: env -> FStar_Ident.lident -> env =
  fun e  ->
    fun l  ->
      let uu___195_1934 = e in
      {
        curmodule = (FStar_Pervasives_Native.Some l);
        curmonad = (uu___195_1934.curmonad);
        modules = (uu___195_1934.modules);
        scope_mods = (uu___195_1934.scope_mods);
        exported_ids = (uu___195_1934.exported_ids);
        trans_exported_ids = (uu___195_1934.trans_exported_ids);
        includes = (uu___195_1934.includes);
        sigaccum = (uu___195_1934.sigaccum);
        sigmap = (uu___195_1934.sigmap);
        iface = (uu___195_1934.iface);
        admitted_iface = (uu___195_1934.admitted_iface);
        expect_typ = (uu___195_1934.expect_typ);
        docs = (uu___195_1934.docs);
        remaining_iface_decls = (uu___195_1934.remaining_iface_decls);
        syntax_only = (uu___195_1934.syntax_only);
        ds_hooks = (uu___195_1934.ds_hooks)
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
      let uu____1949 =
        FStar_All.pipe_right env.remaining_iface_decls
          (FStar_List.tryFind
             (fun uu____1983  ->
                match uu____1983 with
                | (m,uu____1991) -> FStar_Ident.lid_equals l m)) in
      match uu____1949 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (uu____2008,decls) ->
          FStar_Pervasives_Native.Some decls
let set_iface_decls:
  env -> FStar_Ident.lident -> FStar_Parser_AST.decl Prims.list -> env =
  fun env  ->
    fun l  ->
      fun ds  ->
        let uu____2035 =
          FStar_List.partition
            (fun uu____2065  ->
               match uu____2065 with
               | (m,uu____2073) -> FStar_Ident.lid_equals l m)
            env.remaining_iface_decls in
        match uu____2035 with
        | (uu____2078,rest) ->
            let uu___196_2112 = env in
            {
              curmodule = (uu___196_2112.curmodule);
              curmonad = (uu___196_2112.curmonad);
              modules = (uu___196_2112.modules);
              scope_mods = (uu___196_2112.scope_mods);
              exported_ids = (uu___196_2112.exported_ids);
              trans_exported_ids = (uu___196_2112.trans_exported_ids);
              includes = (uu___196_2112.includes);
              sigaccum = (uu___196_2112.sigaccum);
              sigmap = (uu___196_2112.sigmap);
              iface = (uu___196_2112.iface);
              admitted_iface = (uu___196_2112.admitted_iface);
              expect_typ = (uu___196_2112.expect_typ);
              docs = (uu___196_2112.docs);
              remaining_iface_decls = ((l, ds) :: rest);
              syntax_only = (uu___196_2112.syntax_only);
              ds_hooks = (uu___196_2112.ds_hooks)
            }
let qual: FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident =
  FStar_Syntax_Util.qual_id
let qualify: env -> FStar_Ident.ident -> FStar_Ident.lident =
  fun env  ->
    fun id1  ->
      match env.curmonad with
      | FStar_Pervasives_Native.None  ->
          let uu____2131 = current_module env in qual uu____2131 id1
      | FStar_Pervasives_Native.Some monad ->
          let uu____2133 =
            let uu____2134 = current_module env in qual uu____2134 monad in
          FStar_Syntax_Util.mk_field_projector_name_from_ident uu____2133 id1
let syntax_only: env -> Prims.bool = fun env  -> env.syntax_only
let set_syntax_only: env -> Prims.bool -> env =
  fun env  ->
    fun b  ->
      let uu___197_2144 = env in
      {
        curmodule = (uu___197_2144.curmodule);
        curmonad = (uu___197_2144.curmonad);
        modules = (uu___197_2144.modules);
        scope_mods = (uu___197_2144.scope_mods);
        exported_ids = (uu___197_2144.exported_ids);
        trans_exported_ids = (uu___197_2144.trans_exported_ids);
        includes = (uu___197_2144.includes);
        sigaccum = (uu___197_2144.sigaccum);
        sigmap = (uu___197_2144.sigmap);
        iface = (uu___197_2144.iface);
        admitted_iface = (uu___197_2144.admitted_iface);
        expect_typ = (uu___197_2144.expect_typ);
        docs = (uu___197_2144.docs);
        remaining_iface_decls = (uu___197_2144.remaining_iface_decls);
        syntax_only = b;
        ds_hooks = (uu___197_2144.ds_hooks)
      }
let ds_hooks: env -> dsenv_hooks = fun env  -> env.ds_hooks
let set_ds_hooks: env -> dsenv_hooks -> env =
  fun env  ->
    fun hooks  ->
      let uu___198_2154 = env in
      {
        curmodule = (uu___198_2154.curmodule);
        curmonad = (uu___198_2154.curmonad);
        modules = (uu___198_2154.modules);
        scope_mods = (uu___198_2154.scope_mods);
        exported_ids = (uu___198_2154.exported_ids);
        trans_exported_ids = (uu___198_2154.trans_exported_ids);
        includes = (uu___198_2154.includes);
        sigaccum = (uu___198_2154.sigaccum);
        sigmap = (uu___198_2154.sigmap);
        iface = (uu___198_2154.iface);
        admitted_iface = (uu___198_2154.admitted_iface);
        expect_typ = (uu___198_2154.expect_typ);
        docs = (uu___198_2154.docs);
        remaining_iface_decls = (uu___198_2154.remaining_iface_decls);
        syntax_only = (uu___198_2154.syntax_only);
        ds_hooks = hooks
      }
let new_sigmap: 'Auu____2157 . Prims.unit -> 'Auu____2157 FStar_Util.smap =
  fun uu____2163  -> FStar_Util.smap_create (Prims.parse_int "100")
let empty_env: Prims.unit -> env =
  fun uu____2166  ->
    let uu____2167 = new_sigmap () in
    let uu____2170 = new_sigmap () in
    let uu____2173 = new_sigmap () in
    let uu____2184 = new_sigmap () in
    let uu____2195 = new_sigmap () in
    {
      curmodule = FStar_Pervasives_Native.None;
      curmonad = FStar_Pervasives_Native.None;
      modules = [];
      scope_mods = [];
      exported_ids = uu____2167;
      trans_exported_ids = uu____2170;
      includes = uu____2173;
      sigaccum = [];
      sigmap = uu____2184;
      iface = false;
      admitted_iface = false;
      expect_typ = false;
      docs = uu____2195;
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
      (fun uu____2227  ->
         match uu____2227 with
         | (m,uu____2233) ->
             FStar_Ident.lid_equals m FStar_Parser_Const.all_lid) env.modules
let set_bv_range:
  FStar_Syntax_Syntax.bv -> FStar_Range.range -> FStar_Syntax_Syntax.bv =
  fun bv  ->
    fun r  ->
      let id1 =
        let uu___199_2241 = bv.FStar_Syntax_Syntax.ppname in
        {
          FStar_Ident.idText = (uu___199_2241.FStar_Ident.idText);
          FStar_Ident.idRange = r
        } in
      let uu___200_2242 = bv in
      {
        FStar_Syntax_Syntax.ppname = id1;
        FStar_Syntax_Syntax.index = (uu___200_2242.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = (uu___200_2242.FStar_Syntax_Syntax.sort)
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
        (fun uu____2329  ->
           match uu____2329 with
           | (x,y,dd,dq) ->
               if id1.FStar_Ident.idText = x
               then
                 let uu____2352 =
                   let uu____2353 =
                     FStar_Ident.lid_of_path ["Prims"; y]
                       id1.FStar_Ident.idRange in
                   FStar_Syntax_Syntax.fvar uu____2353 dd dq in
                 FStar_Pervasives_Native.Some uu____2352
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
    match projectee with | Cont_ok _0 -> true | uu____2396 -> false
let __proj__Cont_ok__item___0: 'a . 'a cont_t -> 'a =
  fun projectee  -> match projectee with | Cont_ok _0 -> _0
let uu___is_Cont_fail: 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_fail  -> true | uu____2425 -> false
let uu___is_Cont_ignore: 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_ignore  -> true | uu____2439 -> false
let option_of_cont:
  'a .
    (Prims.unit -> 'a FStar_Pervasives_Native.option) ->
      'a cont_t -> 'a FStar_Pervasives_Native.option
  =
  fun k_ignore  ->
    fun uu___161_2462  ->
      match uu___161_2462 with
      | Cont_ok a -> FStar_Pervasives_Native.Some a
      | Cont_fail  -> FStar_Pervasives_Native.None
      | Cont_ignore  -> k_ignore ()
let find_in_record:
  'Auu____2475 .
    FStar_Ident.ident Prims.list ->
      FStar_Ident.ident ->
        record_or_dc ->
          (record_or_dc -> 'Auu____2475 cont_t) -> 'Auu____2475 cont_t
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
                (fun uu____2521  ->
                   match uu____2521 with
                   | (f,uu____2529) ->
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
  fun uu___162_2575  ->
    match uu___162_2575 with
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
              let rec aux uu___163_2631 =
                match uu___163_2631 with
                | [] -> find_in_module_default
                | modul::q ->
                    let mname = modul.FStar_Ident.str in
                    let not_shadowed =
                      let uu____2642 = get_exported_id_set env mname in
                      match uu____2642 with
                      | FStar_Pervasives_Native.None  -> true
                      | FStar_Pervasives_Native.Some mex ->
                          let mexports =
                            let uu____2663 = mex eikind in
                            FStar_ST.op_Bang uu____2663 in
                          FStar_Util.set_mem idstr mexports in
                    let mincludes =
                      let uu____2914 =
                        FStar_Util.smap_try_find env.includes mname in
                      match uu____2914 with
                      | FStar_Pervasives_Native.None  -> []
                      | FStar_Pervasives_Native.Some minc ->
                          FStar_ST.op_Bang minc in
                    let look_into =
                      if not_shadowed
                      then
                        let uu____3011 = qual modul id1 in
                        find_in_module uu____3011
                      else Cont_ignore in
                    (match look_into with
                     | Cont_ignore  -> aux (FStar_List.append mincludes q)
                     | uu____3015 -> look_into) in
              aux [ns]
let is_exported_id_field: exported_id_kind -> Prims.bool =
  fun uu___164_3020  ->
    match uu___164_3020 with
    | Exported_id_field  -> true
    | uu____3021 -> false
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
                  let check_local_binding_id uu___165_3123 =
                    match uu___165_3123 with
                    | (id',uu____3125,uu____3126) ->
                        id'.FStar_Ident.idText = id1.FStar_Ident.idText in
                  let check_rec_binding_id uu___166_3130 =
                    match uu___166_3130 with
                    | (id',uu____3132,uu____3133) ->
                        id'.FStar_Ident.idText = id1.FStar_Ident.idText in
                  let curmod_ns =
                    let uu____3137 = current_module env in
                    FStar_Ident.ids_of_lid uu____3137 in
                  let proc uu___167_3143 =
                    match uu___167_3143 with
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
                        let uu____3151 = FStar_Ident.lid_of_ids curmod_ns in
                        find_in_module_with_includes Exported_id_field
                          (fun lid  ->
                             let id2 = lid.FStar_Ident.ident in
                             find_in_record lid.FStar_Ident.ns id2 r k_record)
                          Cont_ignore env uu____3151 id1
                    | uu____3156 -> Cont_ignore in
                  let rec aux uu___168_3164 =
                    match uu___168_3164 with
                    | a::q ->
                        let uu____3173 = proc a in
                        option_of_cont (fun uu____3177  -> aux q) uu____3173
                    | [] ->
                        let uu____3178 = lookup_default_id Cont_fail id1 in
                        option_of_cont
                          (fun uu____3182  -> FStar_Pervasives_Native.None)
                          uu____3178 in
                  aux env.scope_mods
let found_local_binding:
  'Auu____3187 'Auu____3188 .
    FStar_Range.range ->
      ('Auu____3188,FStar_Syntax_Syntax.bv,'Auu____3187)
        FStar_Pervasives_Native.tuple3 ->
        (FStar_Syntax_Syntax.term,'Auu____3187)
          FStar_Pervasives_Native.tuple2
  =
  fun r  ->
    fun uu____3206  ->
      match uu____3206 with
      | (id',x,mut) -> let uu____3216 = bv_to_name x r in (uu____3216, mut)
let find_in_module:
  'Auu____3222 .
    env ->
      FStar_Ident.lident ->
        (FStar_Ident.lident ->
           (FStar_Syntax_Syntax.sigelt,Prims.bool)
             FStar_Pervasives_Native.tuple2 -> 'Auu____3222)
          -> 'Auu____3222 -> 'Auu____3222
  =
  fun env  ->
    fun lid  ->
      fun k_global_def  ->
        fun k_not_found  ->
          let uu____3257 =
            FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str in
          match uu____3257 with
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
      let uu____3293 = unmangleOpName id1 in
      match uu____3293 with
      | FStar_Pervasives_Native.Some f -> FStar_Pervasives_Native.Some f
      | uu____3319 ->
          try_lookup_id'' env id1 Exported_id_term_type
            (fun r  ->
               let uu____3333 = found_local_binding id1.FStar_Ident.idRange r in
               Cont_ok uu____3333) (fun uu____3343  -> Cont_fail)
            (fun uu____3349  -> Cont_ignore)
            (fun i  ->
               find_in_module env i
                 (fun uu____3364  -> fun uu____3365  -> Cont_fail)
                 Cont_ignore)
            (fun uu____3380  -> fun uu____3381  -> Cont_fail)
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
            | FStar_Pervasives_Native.Some uu____3451 ->
                let lid = qualify env id1 in
                let uu____3453 =
                  FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str in
                (match uu____3453 with
                 | FStar_Pervasives_Native.Some r ->
                     let uu____3477 = k_global_def lid r in
                     FStar_Pervasives_Native.Some uu____3477
                 | FStar_Pervasives_Native.None  ->
                     FStar_Pervasives_Native.None)
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None in
          match find_in_monad with
          | FStar_Pervasives_Native.Some v1 -> v1
          | FStar_Pervasives_Native.None  ->
              let lid =
                let uu____3500 = current_module env in qual uu____3500 id1 in
              find_in_module env lid k_global_def k_not_found
let module_is_defined: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      (match env.curmodule with
       | FStar_Pervasives_Native.None  -> false
       | FStar_Pervasives_Native.Some m ->
           let uu____3510 = current_module env in
           FStar_Ident.lid_equals lid uu____3510)
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
        let rec aux uu___169_3542 =
          match uu___169_3542 with
          | [] ->
              let uu____3547 = module_is_defined env lid in
              if uu____3547
              then FStar_Pervasives_Native.Some lid
              else FStar_Pervasives_Native.None
          | (Open_module_or_namespace (ns,Open_namespace ))::q when honor_ns
              ->
              let new_lid =
                let uu____3556 =
                  let uu____3559 = FStar_Ident.path_of_lid ns in
                  let uu____3562 = FStar_Ident.path_of_lid lid in
                  FStar_List.append uu____3559 uu____3562 in
                FStar_Ident.lid_of_path uu____3556
                  (FStar_Ident.range_of_lid lid) in
              let uu____3565 = module_is_defined env new_lid in
              if uu____3565
              then FStar_Pervasives_Native.Some new_lid
              else aux q
          | (Module_abbrev (name,modul))::uu____3571 when
              (nslen = (Prims.parse_int "0")) &&
                (name.FStar_Ident.idText =
                   (lid.FStar_Ident.ident).FStar_Ident.idText)
              -> FStar_Pervasives_Native.Some modul
          | uu____3578::q -> aux q in
        aux env.scope_mods
let fail_if_curmodule:
  env -> FStar_Ident.lident -> FStar_Ident.lident -> Prims.unit =
  fun env  ->
    fun ns_original  ->
      fun ns_resolved  ->
        let uu____3591 =
          let uu____3592 = current_module env in
          FStar_Ident.lid_equals ns_resolved uu____3592 in
        if uu____3591
        then
          (if FStar_Ident.lid_equals ns_resolved FStar_Parser_Const.prims_lid
           then ()
           else
             (let uu____3594 =
                let uu____3599 =
                  FStar_Util.format1
                    "Reference %s to current module is forbidden (see GitHub issue #451)"
                    ns_original.FStar_Ident.str in
                (FStar_Errors.Fatal_ForbiddenReferenceToCurrentModule,
                  uu____3599) in
              FStar_Errors.raise_error uu____3594
                (FStar_Ident.range_of_lid ns_original)))
        else ()
let fail_if_qualified_by_curmodule: env -> FStar_Ident.lident -> Prims.unit =
  fun env  ->
    fun lid  ->
      match lid.FStar_Ident.ns with
      | [] -> ()
      | uu____3607 ->
          let modul_orig = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          let uu____3611 = resolve_module_name env modul_orig true in
          (match uu____3611 with
           | FStar_Pervasives_Native.Some modul_res ->
               fail_if_curmodule env modul_orig modul_res
           | uu____3615 -> ())
let namespace_is_open: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      FStar_List.existsb
        (fun uu___170_3626  ->
           match uu___170_3626 with
           | Open_module_or_namespace (ns,Open_namespace ) ->
               FStar_Ident.lid_equals lid ns
           | uu____3628 -> false) env.scope_mods
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
                 let uu____3717 = aux rev_ns_prefix ns_last_id in
                 FStar_All.pipe_right uu____3717
                   (FStar_Util.map_option
                      (fun uu____3767  ->
                         match uu____3767 with
                         | (stripped_ids,rev_kept_ids) ->
                             (stripped_ids, (id1 :: rev_kept_ids))))) in
        let uu____3798 =
          is_full_path &&
            (let uu____3800 = FStar_Ident.lid_of_ids ids in
             module_is_defined env uu____3800) in
        if uu____3798
        then (ids, [])
        else
          (match FStar_List.rev ids with
           | [] -> ([], [])
           | ns_last_id::ns_rev_prefix ->
               let uu____3830 = aux ns_rev_prefix ns_last_id in
               (match uu____3830 with
                | FStar_Pervasives_Native.None  -> ([], ids)
                | FStar_Pervasives_Native.Some (stripped_ids,rev_kept_ids) ->
                    (stripped_ids, (FStar_List.rev rev_kept_ids))))
let shorten_lid: env -> FStar_Ident.lid -> FStar_Ident.lid =
  fun env  ->
    fun lid  ->
      let uu____3889 = shorten_module_path env lid.FStar_Ident.ns true in
      match uu____3889 with
      | (uu____3898,short) ->
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
                  | uu____4006::uu____4007 ->
                      let uu____4010 =
                        let uu____4013 =
                          let uu____4014 =
                            FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
                          FStar_Ident.set_lid_range uu____4014
                            (FStar_Ident.range_of_lid lid) in
                        resolve_module_name env uu____4013 true in
                      (match uu____4010 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some modul ->
                           let uu____4018 =
                             find_in_module_with_includes eikind f_module
                               Cont_fail env modul lid.FStar_Ident.ident in
                           option_of_cont
                             (fun uu____4022  -> FStar_Pervasives_Native.None)
                             uu____4018)
                  | [] ->
                      try_lookup_id'' env lid.FStar_Ident.ident eikind
                        k_local_binding k_rec_binding k_record f_module
                        l_default
let cont_of_option:
  'a . 'a cont_t -> 'a FStar_Pervasives_Native.option -> 'a cont_t =
  fun k_none  ->
    fun uu___171_4040  ->
      match uu___171_4040 with
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
              let uu____4139 = k_global_def lid1 def in
              cont_of_option k uu____4139 in
            let f_module lid' =
              let k = Cont_ignore in
              find_in_module env lid' (k_global_def' k) k in
            let l_default k i = lookup_default_id env i (k_global_def' k) k in
            resolve_in_open_namespaces'' env lid Exported_id_term_type
              (fun l  ->
                 let uu____4169 = k_local_binding l in
                 cont_of_option Cont_fail uu____4169)
              (fun r  ->
                 let uu____4175 = k_rec_binding r in
                 cont_of_option Cont_fail uu____4175)
              (fun uu____4179  -> Cont_ignore) f_module l_default
let fv_qual_of_se:
  FStar_Syntax_Syntax.sigelt ->
    FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____4187,uu____4188,uu____4189,l,uu____4191,uu____4192) ->
        let qopt =
          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
            (fun uu___172_4203  ->
               match uu___172_4203 with
               | FStar_Syntax_Syntax.RecordConstructor (uu____4206,fs) ->
                   FStar_Pervasives_Native.Some
                     (FStar_Syntax_Syntax.Record_ctor (l, fs))
               | uu____4218 -> FStar_Pervasives_Native.None) in
        (match qopt with
         | FStar_Pervasives_Native.None  ->
             FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor
         | x -> x)
    | FStar_Syntax_Syntax.Sig_declare_typ (uu____4224,uu____4225,uu____4226)
        -> FStar_Pervasives_Native.None
    | uu____4227 -> FStar_Pervasives_Native.None
let lb_fv:
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Ident.lident -> FStar_Syntax_Syntax.fv
  =
  fun lbs  ->
    fun lid  ->
      let uu____4238 =
        FStar_Util.find_map lbs
          (fun lb  ->
             let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
             let uu____4246 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
             if uu____4246
             then FStar_Pervasives_Native.Some fv
             else FStar_Pervasives_Native.None) in
      FStar_All.pipe_right uu____4238 FStar_Util.must
let ns_of_lid_equals: FStar_Ident.lident -> FStar_Ident.lident -> Prims.bool
  =
  fun lid  ->
    fun ns  ->
      ((FStar_List.length lid.FStar_Ident.ns) =
         (FStar_List.length (FStar_Ident.ids_of_lid ns)))
        &&
        (let uu____4259 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
         FStar_Ident.lid_equals uu____4259 ns)
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
          let k_global_def source_lid uu___177_4289 =
            match uu___177_4289 with
            | (uu____4296,true ) when exclude_interf ->
                FStar_Pervasives_Native.None
            | (se,uu____4298) ->
                (match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_inductive_typ uu____4301 ->
                     let uu____4318 =
                       let uu____4319 =
                         let uu____4324 =
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.Delta_constant
                             FStar_Pervasives_Native.None in
                         (uu____4324, false) in
                       Term_name uu____4319 in
                     FStar_Pervasives_Native.Some uu____4318
                 | FStar_Syntax_Syntax.Sig_datacon uu____4325 ->
                     let uu____4340 =
                       let uu____4341 =
                         let uu____4346 =
                           let uu____4347 = fv_qual_of_se se in
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.Delta_constant uu____4347 in
                         (uu____4346, false) in
                       Term_name uu____4341 in
                     FStar_Pervasives_Native.Some uu____4340
                 | FStar_Syntax_Syntax.Sig_let ((uu____4350,lbs),uu____4352)
                     ->
                     let fv = lb_fv lbs source_lid in
                     let uu____4368 =
                       let uu____4369 =
                         let uu____4374 =
                           FStar_Syntax_Syntax.fvar source_lid
                             fv.FStar_Syntax_Syntax.fv_delta
                             fv.FStar_Syntax_Syntax.fv_qual in
                         (uu____4374, false) in
                       Term_name uu____4369 in
                     FStar_Pervasives_Native.Some uu____4368
                 | FStar_Syntax_Syntax.Sig_declare_typ
                     (lid1,uu____4376,uu____4377) ->
                     let quals = se.FStar_Syntax_Syntax.sigquals in
                     let uu____4381 =
                       any_val ||
                         (FStar_All.pipe_right quals
                            (FStar_Util.for_some
                               (fun uu___173_4385  ->
                                  match uu___173_4385 with
                                  | FStar_Syntax_Syntax.Assumption  -> true
                                  | uu____4386 -> false))) in
                     if uu____4381
                     then
                       let lid2 =
                         FStar_Ident.set_lid_range lid1
                           (FStar_Ident.range_of_lid source_lid) in
                       let dd =
                         let uu____4391 =
                           (FStar_Syntax_Util.is_primop_lid lid2) ||
                             (FStar_All.pipe_right quals
                                (FStar_Util.for_some
                                   (fun uu___174_4396  ->
                                      match uu___174_4396 with
                                      | FStar_Syntax_Syntax.Projector
                                          uu____4397 -> true
                                      | FStar_Syntax_Syntax.Discriminator
                                          uu____4402 -> true
                                      | uu____4403 -> false))) in
                         if uu____4391
                         then FStar_Syntax_Syntax.Delta_equational
                         else FStar_Syntax_Syntax.Delta_constant in
                       let dd1 =
                         let uu____4406 =
                           FStar_All.pipe_right quals
                             (FStar_Util.for_some
                                (fun uu___175_4410  ->
                                   match uu___175_4410 with
                                   | FStar_Syntax_Syntax.Abstract  -> true
                                   | uu____4411 -> false)) in
                         if uu____4406
                         then FStar_Syntax_Syntax.Delta_abstract dd
                         else dd in
                       let uu____4413 =
                         FStar_Util.find_map quals
                           (fun uu___176_4418  ->
                              match uu___176_4418 with
                              | FStar_Syntax_Syntax.Reflectable refl_monad ->
                                  FStar_Pervasives_Native.Some refl_monad
                              | uu____4422 -> FStar_Pervasives_Native.None) in
                       (match uu____4413 with
                        | FStar_Pervasives_Native.Some refl_monad ->
                            let refl_const =
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_constant
                                   (FStar_Const.Const_reflect refl_monad))
                                FStar_Pervasives_Native.None occurrence_range in
                            FStar_Pervasives_Native.Some
                              (Term_name (refl_const, false))
                        | uu____4431 ->
                            let uu____4434 =
                              let uu____4435 =
                                let uu____4440 =
                                  let uu____4441 = fv_qual_of_se se in
                                  FStar_Syntax_Syntax.fvar lid2 dd1
                                    uu____4441 in
                                (uu____4440, false) in
                              Term_name uu____4435 in
                            FStar_Pervasives_Native.Some uu____4434)
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
                 | FStar_Syntax_Syntax.Sig_effect_abbrev uu____4447 ->
                     FStar_Pervasives_Native.Some (Eff_name (se, source_lid))
                 | uu____4460 -> FStar_Pervasives_Native.None) in
          let k_local_binding r =
            let uu____4479 =
              let uu____4480 =
                found_local_binding (FStar_Ident.range_of_lid lid) r in
              Term_name uu____4480 in
            FStar_Pervasives_Native.Some uu____4479 in
          let k_rec_binding uu____4496 =
            match uu____4496 with
            | (id1,l,dd) ->
                let uu____4508 =
                  let uu____4509 =
                    let uu____4514 =
                      FStar_Syntax_Syntax.fvar
                        (FStar_Ident.set_lid_range l
                           (FStar_Ident.range_of_lid lid)) dd
                        FStar_Pervasives_Native.None in
                    (uu____4514, false) in
                  Term_name uu____4509 in
                FStar_Pervasives_Native.Some uu____4508 in
          let found_unmangled =
            match lid.FStar_Ident.ns with
            | [] ->
                let uu____4520 = unmangleOpName lid.FStar_Ident.ident in
                (match uu____4520 with
                 | FStar_Pervasives_Native.Some f ->
                     FStar_Pervasives_Native.Some (Term_name f)
                 | uu____4538 -> FStar_Pervasives_Native.None)
            | uu____4545 -> FStar_Pervasives_Native.None in
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
        let uu____4574 = try_lookup_name true exclude_interf env lid in
        match uu____4574 with
        | FStar_Pervasives_Native.Some (Eff_name (o,l)) ->
            FStar_Pervasives_Native.Some (o, l)
        | uu____4589 -> FStar_Pervasives_Native.None
let try_lookup_effect_name:
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____4604 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____4604 with
      | FStar_Pervasives_Native.Some (o,l1) ->
          FStar_Pervasives_Native.Some l1
      | uu____4619 -> FStar_Pervasives_Native.None
let try_lookup_effect_name_and_attributes:
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident,FStar_Syntax_Syntax.cflags Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____4640 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____4640 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____4656;
             FStar_Syntax_Syntax.sigquals = uu____4657;
             FStar_Syntax_Syntax.sigmeta = uu____4658;
             FStar_Syntax_Syntax.sigattrs = uu____4659;_},l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____4678;
             FStar_Syntax_Syntax.sigquals = uu____4679;
             FStar_Syntax_Syntax.sigmeta = uu____4680;
             FStar_Syntax_Syntax.sigattrs = uu____4681;_},l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (uu____4699,uu____4700,uu____4701,uu____4702,cattributes);
             FStar_Syntax_Syntax.sigrng = uu____4704;
             FStar_Syntax_Syntax.sigquals = uu____4705;
             FStar_Syntax_Syntax.sigmeta = uu____4706;
             FStar_Syntax_Syntax.sigattrs = uu____4707;_},l1)
          -> FStar_Pervasives_Native.Some (l1, cattributes)
      | uu____4729 -> FStar_Pervasives_Native.None
let try_lookup_effect_defn:
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.eff_decl FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____4750 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____4750 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____4760;
             FStar_Syntax_Syntax.sigquals = uu____4761;
             FStar_Syntax_Syntax.sigmeta = uu____4762;
             FStar_Syntax_Syntax.sigattrs = uu____4763;_},uu____4764)
          -> FStar_Pervasives_Native.Some ne
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____4774;
             FStar_Syntax_Syntax.sigquals = uu____4775;
             FStar_Syntax_Syntax.sigmeta = uu____4776;
             FStar_Syntax_Syntax.sigattrs = uu____4777;_},uu____4778)
          -> FStar_Pervasives_Native.Some ne
      | uu____4787 -> FStar_Pervasives_Native.None
let is_effect_name: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____4800 = try_lookup_effect_name env lid in
      match uu____4800 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____4803 -> true
let try_lookup_root_effect_name:
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____4812 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____4812 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (l',uu____4822,uu____4823,uu____4824,uu____4825);
             FStar_Syntax_Syntax.sigrng = uu____4826;
             FStar_Syntax_Syntax.sigquals = uu____4827;
             FStar_Syntax_Syntax.sigmeta = uu____4828;
             FStar_Syntax_Syntax.sigattrs = uu____4829;_},uu____4830)
          ->
          let rec aux new_name =
            let uu____4849 =
              FStar_Util.smap_try_find (sigmap env) new_name.FStar_Ident.str in
            match uu____4849 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (s,uu____4867) ->
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
                     (uu____4876,uu____4877,uu____4878,cmp,uu____4880) ->
                     let l'' = FStar_Syntax_Util.comp_effect_name cmp in
                     aux l''
                 | uu____4886 -> FStar_Pervasives_Native.None) in
          aux l'
      | FStar_Pervasives_Native.Some (uu____4887,l') ->
          FStar_Pervasives_Native.Some l'
      | uu____4893 -> FStar_Pervasives_Native.None
let lookup_letbinding_quals:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___178_4922 =
        match uu___178_4922 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____4931,uu____4932,uu____4933);
             FStar_Syntax_Syntax.sigrng = uu____4934;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____4936;
             FStar_Syntax_Syntax.sigattrs = uu____4937;_},uu____4938)
            -> FStar_Pervasives_Native.Some quals
        | uu____4945 -> FStar_Pervasives_Native.None in
      let uu____4952 =
        resolve_in_open_namespaces' env lid
          (fun uu____4960  -> FStar_Pervasives_Native.None)
          (fun uu____4964  -> FStar_Pervasives_Native.None) k_global_def in
      match uu____4952 with
      | FStar_Pervasives_Native.Some quals -> quals
      | uu____4974 -> []
let try_lookup_module:
  env ->
    Prims.string Prims.list ->
      FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option
  =
  fun env  ->
    fun path  ->
      let uu____4991 =
        FStar_List.tryFind
          (fun uu____5006  ->
             match uu____5006 with
             | (mlid,modul) ->
                 let uu____5013 = FStar_Ident.path_of_lid mlid in
                 uu____5013 = path) env.modules in
      match uu____4991 with
      | FStar_Pervasives_Native.Some (uu____5020,modul) ->
          FStar_Pervasives_Native.Some modul
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
let try_lookup_let:
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___179_5050 =
        match uu___179_5050 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               ((uu____5057,lbs),uu____5059);
             FStar_Syntax_Syntax.sigrng = uu____5060;
             FStar_Syntax_Syntax.sigquals = uu____5061;
             FStar_Syntax_Syntax.sigmeta = uu____5062;
             FStar_Syntax_Syntax.sigattrs = uu____5063;_},uu____5064)
            ->
            let fv = lb_fv lbs lid1 in
            let uu____5084 =
              FStar_Syntax_Syntax.fvar lid1 fv.FStar_Syntax_Syntax.fv_delta
                fv.FStar_Syntax_Syntax.fv_qual in
            FStar_Pervasives_Native.Some uu____5084
        | uu____5085 -> FStar_Pervasives_Native.None in
      resolve_in_open_namespaces' env lid
        (fun uu____5091  -> FStar_Pervasives_Native.None)
        (fun uu____5093  -> FStar_Pervasives_Native.None) k_global_def
let try_lookup_definition:
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___180_5116 =
        match uu___180_5116 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               (lbs,uu____5126);
             FStar_Syntax_Syntax.sigrng = uu____5127;
             FStar_Syntax_Syntax.sigquals = uu____5128;
             FStar_Syntax_Syntax.sigmeta = uu____5129;
             FStar_Syntax_Syntax.sigattrs = uu____5130;_},uu____5131)
            ->
            FStar_Util.find_map (FStar_Pervasives_Native.snd lbs)
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inr fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv lid1 ->
                     FStar_Pervasives_Native.Some
                       (lb.FStar_Syntax_Syntax.lbdef)
                 | uu____5154 -> FStar_Pervasives_Native.None)
        | uu____5161 -> FStar_Pervasives_Native.None in
      resolve_in_open_namespaces' env lid
        (fun uu____5171  -> FStar_Pervasives_Native.None)
        (fun uu____5175  -> FStar_Pervasives_Native.None) k_global_def
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
          let uu____5214 = try_lookup_name any_val exclude_interface env lid in
          match uu____5214 with
          | FStar_Pervasives_Native.Some (Term_name (e,mut)) ->
              FStar_Pervasives_Native.Some (e, mut)
          | uu____5229 -> FStar_Pervasives_Native.None
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
      let uu____5256 = try_lookup_lid env l in
      match uu____5256 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (e,uu____5270) ->
          let uu____5275 =
            let uu____5276 = FStar_Syntax_Subst.compress e in
            uu____5276.FStar_Syntax_Syntax.n in
          (match uu____5275 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               FStar_Pervasives_Native.Some
                 ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
           | uu____5282 -> FStar_Pervasives_Native.None)
let try_lookup_lid_no_resolve:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term,Prims.bool) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let env' =
        let uu___201_5296 = env in
        {
          curmodule = (uu___201_5296.curmodule);
          curmonad = (uu___201_5296.curmonad);
          modules = (uu___201_5296.modules);
          scope_mods = [];
          exported_ids = empty_exported_id_smap;
          trans_exported_ids = (uu___201_5296.trans_exported_ids);
          includes = empty_include_smap;
          sigaccum = (uu___201_5296.sigaccum);
          sigmap = (uu___201_5296.sigmap);
          iface = (uu___201_5296.iface);
          admitted_iface = (uu___201_5296.admitted_iface);
          expect_typ = (uu___201_5296.expect_typ);
          docs = (uu___201_5296.docs);
          remaining_iface_decls = (uu___201_5296.remaining_iface_decls);
          syntax_only = (uu___201_5296.syntax_only);
          ds_hooks = (uu___201_5296.ds_hooks)
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
      let k_global_def lid1 uu___182_5325 =
        match uu___182_5325 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____5332,uu____5333,uu____5334);
             FStar_Syntax_Syntax.sigrng = uu____5335;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____5337;
             FStar_Syntax_Syntax.sigattrs = uu____5338;_},uu____5339)
            ->
            let uu____5344 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___181_5348  ->
                      match uu___181_5348 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | uu____5349 -> false)) in
            if uu____5344
            then
              let uu____5352 =
                FStar_Syntax_Syntax.lid_as_fv lid1
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None in
              FStar_Pervasives_Native.Some uu____5352
            else FStar_Pervasives_Native.None
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
               uu____5354;
             FStar_Syntax_Syntax.sigrng = uu____5355;
             FStar_Syntax_Syntax.sigquals = uu____5356;
             FStar_Syntax_Syntax.sigmeta = uu____5357;
             FStar_Syntax_Syntax.sigattrs = uu____5358;_},uu____5359)
            ->
            let uu____5378 =
              FStar_Syntax_Syntax.lid_as_fv lid1
                FStar_Syntax_Syntax.Delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor) in
            FStar_Pervasives_Native.Some uu____5378
        | uu____5379 -> FStar_Pervasives_Native.None in
      resolve_in_open_namespaces' env lid
        (fun uu____5385  -> FStar_Pervasives_Native.None)
        (fun uu____5387  -> FStar_Pervasives_Native.None) k_global_def
let find_all_datacons:
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident Prims.list FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___183_5412 =
        match uu___183_5412 with
        | ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_inductive_typ
               (uu____5421,uu____5422,uu____5423,uu____5424,datas,uu____5426);
             FStar_Syntax_Syntax.sigrng = uu____5427;
             FStar_Syntax_Syntax.sigquals = uu____5428;
             FStar_Syntax_Syntax.sigmeta = uu____5429;
             FStar_Syntax_Syntax.sigattrs = uu____5430;_},uu____5431)
            -> FStar_Pervasives_Native.Some datas
        | uu____5446 -> FStar_Pervasives_Native.None in
      resolve_in_open_namespaces' env lid
        (fun uu____5456  -> FStar_Pervasives_Native.None)
        (fun uu____5460  -> FStar_Pervasives_Native.None) k_global_def
let record_cache_aux_with_filter:
  ((Prims.unit -> Prims.unit,Prims.unit -> Prims.unit,Prims.unit ->
                                                        record_or_dc
                                                          Prims.list,
     record_or_dc -> Prims.unit) FStar_Pervasives_Native.tuple4,Prims.unit ->
                                                                  Prims.unit)
    FStar_Pervasives_Native.tuple2
  =
  let record_cache = FStar_Util.mk_ref [[]] in
  let push1 uu____5505 =
    let uu____5506 =
      let uu____5511 =
        let uu____5514 = FStar_ST.op_Bang record_cache in
        FStar_List.hd uu____5514 in
      let uu____5591 = FStar_ST.op_Bang record_cache in uu____5511 ::
        uu____5591 in
    FStar_ST.op_Colon_Equals record_cache uu____5506 in
  let pop1 uu____5741 =
    let uu____5742 =
      let uu____5747 = FStar_ST.op_Bang record_cache in
      FStar_List.tl uu____5747 in
    FStar_ST.op_Colon_Equals record_cache uu____5742 in
  let peek1 uu____5899 =
    let uu____5900 = FStar_ST.op_Bang record_cache in
    FStar_List.hd uu____5900 in
  let insert r =
    let uu____5981 =
      let uu____5986 = let uu____5989 = peek1 () in r :: uu____5989 in
      let uu____5992 =
        let uu____5997 = FStar_ST.op_Bang record_cache in
        FStar_List.tl uu____5997 in
      uu____5986 :: uu____5992 in
    FStar_ST.op_Colon_Equals record_cache uu____5981 in
  let filter1 uu____6149 =
    let rc = peek1 () in
    let filtered =
      FStar_List.filter
        (fun r  -> Prims.op_Negation r.is_private_or_abstract) rc in
    let uu____6158 =
      let uu____6163 =
        let uu____6168 = FStar_ST.op_Bang record_cache in
        FStar_List.tl uu____6168 in
      filtered :: uu____6163 in
    FStar_ST.op_Colon_Equals record_cache uu____6158 in
  let aux = (push1, pop1, peek1, insert) in (aux, filter1)
let record_cache_aux:
  (Prims.unit -> Prims.unit,Prims.unit -> Prims.unit,Prims.unit ->
                                                       record_or_dc
                                                         Prims.list,record_or_dc
                                                                    ->
                                                                    Prims.unit)
    FStar_Pervasives_Native.tuple4
  =
  let uu____6384 = record_cache_aux_with_filter in
  match uu____6384 with | (aux,uu____6428) -> aux
let filter_record_cache: Prims.unit -> Prims.unit =
  let uu____6471 = record_cache_aux_with_filter in
  match uu____6471 with | (uu____6498,filter1) -> filter1
let push_record_cache: Prims.unit -> Prims.unit =
  let uu____6542 = record_cache_aux in
  match uu____6542 with | (push1,uu____6564,uu____6565,uu____6566) -> push1
let pop_record_cache: Prims.unit -> Prims.unit =
  let uu____6589 = record_cache_aux in
  match uu____6589 with | (uu____6610,pop1,uu____6612,uu____6613) -> pop1
let peek_record_cache: Prims.unit -> record_or_dc Prims.list =
  let uu____6638 = record_cache_aux in
  match uu____6638 with | (uu____6661,uu____6662,peek1,uu____6664) -> peek1
let insert_record_cache: record_or_dc -> Prims.unit =
  let uu____6687 = record_cache_aux in
  match uu____6687 with | (uu____6708,uu____6709,uu____6710,insert) -> insert
let extract_record:
  env ->
    scope_mod Prims.list FStar_ST.ref ->
      FStar_Syntax_Syntax.sigelt -> Prims.unit
  =
  fun e  ->
    fun new_globs  ->
      fun se  ->
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_bundle (sigs,uu____6764) ->
            let is_record =
              FStar_Util.for_some
                (fun uu___184_6780  ->
                   match uu___184_6780 with
                   | FStar_Syntax_Syntax.RecordType uu____6781 -> true
                   | FStar_Syntax_Syntax.RecordConstructor uu____6790 -> true
                   | uu____6799 -> false) in
            let find_dc dc =
              FStar_All.pipe_right sigs
                (FStar_Util.find_opt
                   (fun uu___185_6821  ->
                      match uu___185_6821 with
                      | {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_datacon
                            (lid,uu____6823,uu____6824,uu____6825,uu____6826,uu____6827);
                          FStar_Syntax_Syntax.sigrng = uu____6828;
                          FStar_Syntax_Syntax.sigquals = uu____6829;
                          FStar_Syntax_Syntax.sigmeta = uu____6830;
                          FStar_Syntax_Syntax.sigattrs = uu____6831;_} ->
                          FStar_Ident.lid_equals dc lid
                      | uu____6840 -> false)) in
            FStar_All.pipe_right sigs
              (FStar_List.iter
                 (fun uu___186_6875  ->
                    match uu___186_6875 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ
                          (typename,univs1,parms,uu____6879,uu____6880,dc::[]);
                        FStar_Syntax_Syntax.sigrng = uu____6882;
                        FStar_Syntax_Syntax.sigquals = typename_quals;
                        FStar_Syntax_Syntax.sigmeta = uu____6884;
                        FStar_Syntax_Syntax.sigattrs = uu____6885;_} ->
                        let uu____6896 =
                          let uu____6897 = find_dc dc in
                          FStar_All.pipe_left FStar_Util.must uu____6897 in
                        (match uu____6896 with
                         | {
                             FStar_Syntax_Syntax.sigel =
                               FStar_Syntax_Syntax.Sig_datacon
                               (constrname,uu____6903,t,uu____6905,uu____6906,uu____6907);
                             FStar_Syntax_Syntax.sigrng = uu____6908;
                             FStar_Syntax_Syntax.sigquals = uu____6909;
                             FStar_Syntax_Syntax.sigmeta = uu____6910;
                             FStar_Syntax_Syntax.sigattrs = uu____6911;_} ->
                             let uu____6920 =
                               FStar_Syntax_Util.arrow_formals t in
                             (match uu____6920 with
                              | (formals,uu____6934) ->
                                  let is_rec = is_record typename_quals in
                                  let formals' =
                                    FStar_All.pipe_right formals
                                      (FStar_List.collect
                                         (fun uu____6983  ->
                                            match uu____6983 with
                                            | (x,q) ->
                                                let uu____6996 =
                                                  (FStar_Syntax_Syntax.is_null_bv
                                                     x)
                                                    ||
                                                    (is_rec &&
                                                       (FStar_Syntax_Syntax.is_implicit
                                                          q)) in
                                                if uu____6996
                                                then []
                                                else [(x, q)])) in
                                  let fields' =
                                    FStar_All.pipe_right formals'
                                      (FStar_List.map
                                         (fun uu____7053  ->
                                            match uu____7053 with
                                            | (x,q) ->
                                                let uu____7066 =
                                                  if is_rec
                                                  then
                                                    FStar_Syntax_Util.unmangle_field_name
                                                      x.FStar_Syntax_Syntax.ppname
                                                  else
                                                    x.FStar_Syntax_Syntax.ppname in
                                                (uu____7066,
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
                                  ((let uu____7081 =
                                      let uu____7084 =
                                        FStar_ST.op_Bang new_globs in
                                      (Record_or_dc record) :: uu____7084 in
                                    FStar_ST.op_Colon_Equals new_globs
                                      uu____7081);
                                   (match () with
                                    | () ->
                                        ((let add_field uu____7229 =
                                            match uu____7229 with
                                            | (id1,uu____7237) ->
                                                let modul =
                                                  let uu____7243 =
                                                    FStar_Ident.lid_of_ids
                                                      constrname.FStar_Ident.ns in
                                                  uu____7243.FStar_Ident.str in
                                                let uu____7244 =
                                                  get_exported_id_set e modul in
                                                (match uu____7244 with
                                                 | FStar_Pervasives_Native.Some
                                                     my_ex ->
                                                     let my_exported_ids =
                                                       my_ex
                                                         Exported_id_field in
                                                     ((let uu____7271 =
                                                         let uu____7272 =
                                                           FStar_ST.op_Bang
                                                             my_exported_ids in
                                                         FStar_Util.set_add
                                                           id1.FStar_Ident.idText
                                                           uu____7272 in
                                                       FStar_ST.op_Colon_Equals
                                                         my_exported_ids
                                                         uu____7271);
                                                      (match () with
                                                       | () ->
                                                           let projname =
                                                             let uu____7400 =
                                                               let uu____7401
                                                                 =
                                                                 FStar_Syntax_Util.mk_field_projector_name_from_ident
                                                                   constrname
                                                                   id1 in
                                                               uu____7401.FStar_Ident.ident in
                                                             uu____7400.FStar_Ident.idText in
                                                           let uu____7403 =
                                                             let uu____7404 =
                                                               FStar_ST.op_Bang
                                                                 my_exported_ids in
                                                             FStar_Util.set_add
                                                               projname
                                                               uu____7404 in
                                                           FStar_ST.op_Colon_Equals
                                                             my_exported_ids
                                                             uu____7403))
                                                 | FStar_Pervasives_Native.None
                                                      -> ()) in
                                          FStar_List.iter add_field fields');
                                         (match () with
                                          | () -> insert_record_cache record)))))
                         | uu____7541 -> ())
                    | uu____7542 -> ()))
        | uu____7543 -> ()
let try_lookup_record_or_dc_by_field_name:
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option =
  fun env  ->
    fun fieldname  ->
      let find_in_cache fieldname1 =
        let uu____7558 =
          ((fieldname1.FStar_Ident.ns), (fieldname1.FStar_Ident.ident)) in
        match uu____7558 with
        | (ns,id1) ->
            let uu____7575 = peek_record_cache () in
            FStar_Util.find_map uu____7575
              (fun record  ->
                 let uu____7581 =
                   find_in_record ns id1 record (fun r  -> Cont_ok r) in
                 option_of_cont
                   (fun uu____7587  -> FStar_Pervasives_Native.None)
                   uu____7581) in
      resolve_in_open_namespaces'' env fieldname Exported_id_field
        (fun uu____7589  -> Cont_ignore) (fun uu____7591  -> Cont_ignore)
        (fun r  -> Cont_ok r)
        (fun fn  ->
           let uu____7597 = find_in_cache fn in
           cont_of_option Cont_ignore uu____7597)
        (fun k  -> fun uu____7603  -> k)
let try_lookup_record_by_field_name:
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option =
  fun env  ->
    fun fieldname  ->
      let uu____7614 = try_lookup_record_or_dc_by_field_name env fieldname in
      match uu____7614 with
      | FStar_Pervasives_Native.Some r when r.is_record ->
          FStar_Pervasives_Native.Some r
      | uu____7620 -> FStar_Pervasives_Native.None
let belongs_to_record:
  env -> FStar_Ident.lident -> record_or_dc -> Prims.bool =
  fun env  ->
    fun lid  ->
      fun record  ->
        let uu____7632 = try_lookup_record_by_field_name env lid in
        match uu____7632 with
        | FStar_Pervasives_Native.Some record' when
            let uu____7636 =
              let uu____7637 =
                FStar_Ident.path_of_ns (record.typename).FStar_Ident.ns in
              FStar_Ident.text_of_path uu____7637 in
            let uu____7640 =
              let uu____7641 =
                FStar_Ident.path_of_ns (record'.typename).FStar_Ident.ns in
              FStar_Ident.text_of_path uu____7641 in
            uu____7636 = uu____7640 ->
            let uu____7644 =
              find_in_record (record.typename).FStar_Ident.ns
                lid.FStar_Ident.ident record (fun uu____7648  -> Cont_ok ()) in
            (match uu____7644 with
             | Cont_ok uu____7649 -> true
             | uu____7650 -> false)
        | uu____7653 -> false
let try_lookup_dc_by_field_name:
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident,Prims.bool) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option
  =
  fun env  ->
    fun fieldname  ->
      let uu____7668 = try_lookup_record_or_dc_by_field_name env fieldname in
      match uu____7668 with
      | FStar_Pervasives_Native.Some r ->
          let uu____7678 =
            let uu____7683 =
              let uu____7684 =
                FStar_Ident.lid_of_ids
                  (FStar_List.append (r.typename).FStar_Ident.ns
                     [r.constrname]) in
              FStar_Ident.set_lid_range uu____7684
                (FStar_Ident.range_of_lid fieldname) in
            (uu____7683, (r.is_record)) in
          FStar_Pervasives_Native.Some uu____7678
      | uu____7689 -> FStar_Pervasives_Native.None
let string_set_ref_new:
  Prims.unit -> Prims.string FStar_Util.set FStar_ST.ref =
  fun uu____7709  ->
    let uu____7710 = FStar_Util.new_set FStar_Util.compare in
    FStar_Util.mk_ref uu____7710
let exported_id_set_new:
  Prims.unit -> exported_id_kind -> Prims.string FStar_Util.set FStar_ST.ref
  =
  fun uu____7730  ->
    let term_type_set = string_set_ref_new () in
    let field_set = string_set_ref_new () in
    fun uu___187_7741  ->
      match uu___187_7741 with
      | Exported_id_term_type  -> term_type_set
      | Exported_id_field  -> field_set
let unique:
  Prims.bool -> Prims.bool -> env -> FStar_Ident.lident -> Prims.bool =
  fun any_val  ->
    fun exclude_interface  ->
      fun env  ->
        fun lid  ->
          let filter_scope_mods uu___188_7775 =
            match uu___188_7775 with
            | Rec_binding uu____7776 -> true
            | uu____7777 -> false in
          let this_env =
            let uu___202_7779 = env in
            let uu____7780 =
              FStar_List.filter filter_scope_mods env.scope_mods in
            {
              curmodule = (uu___202_7779.curmodule);
              curmonad = (uu___202_7779.curmonad);
              modules = (uu___202_7779.modules);
              scope_mods = uu____7780;
              exported_ids = empty_exported_id_smap;
              trans_exported_ids = (uu___202_7779.trans_exported_ids);
              includes = empty_include_smap;
              sigaccum = (uu___202_7779.sigaccum);
              sigmap = (uu___202_7779.sigmap);
              iface = (uu___202_7779.iface);
              admitted_iface = (uu___202_7779.admitted_iface);
              expect_typ = (uu___202_7779.expect_typ);
              docs = (uu___202_7779.docs);
              remaining_iface_decls = (uu___202_7779.remaining_iface_decls);
              syntax_only = (uu___202_7779.syntax_only);
              ds_hooks = (uu___202_7779.ds_hooks)
            } in
          let uu____7783 =
            try_lookup_lid' any_val exclude_interface this_env lid in
          match uu____7783 with
          | FStar_Pervasives_Native.None  -> true
          | FStar_Pervasives_Native.Some uu____7794 -> false
let push_scope_mod: env -> scope_mod -> env =
  fun env  ->
    fun scope_mod  ->
      let uu___203_7809 = env in
      {
        curmodule = (uu___203_7809.curmodule);
        curmonad = (uu___203_7809.curmonad);
        modules = (uu___203_7809.modules);
        scope_mods = (scope_mod :: (env.scope_mods));
        exported_ids = (uu___203_7809.exported_ids);
        trans_exported_ids = (uu___203_7809.trans_exported_ids);
        includes = (uu___203_7809.includes);
        sigaccum = (uu___203_7809.sigaccum);
        sigmap = (uu___203_7809.sigmap);
        iface = (uu___203_7809.iface);
        admitted_iface = (uu___203_7809.admitted_iface);
        expect_typ = (uu___203_7809.expect_typ);
        docs = (uu___203_7809.docs);
        remaining_iface_decls = (uu___203_7809.remaining_iface_decls);
        syntax_only = (uu___203_7809.syntax_only);
        ds_hooks = (uu___203_7809.ds_hooks)
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
        let uu____7854 =
          (unique false true env l) || (FStar_Options.interactive ()) in
        if uu____7854
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
          | FStar_Pervasives_Native.Some (se,uu____7879) ->
              let uu____7884 =
                FStar_Util.find_opt (FStar_Ident.lid_equals l)
                  (FStar_Syntax_Util.lids_of_sigelt se) in
              (match uu____7884 with
               | FStar_Pervasives_Native.Some l1 ->
                   FStar_All.pipe_left FStar_Range.string_of_range
                     (FStar_Ident.range_of_lid l1)
               | FStar_Pervasives_Native.None  -> "<unknown>")
          | FStar_Pervasives_Native.None  -> "<unknown>" in
        let uu____7892 =
          let uu____7897 =
            FStar_Util.format2
              "Duplicate top-level names [%s]; previously declared at %s"
              (FStar_Ident.text_of_lid l) r in
          (FStar_Errors.Fatal_DuplicateTopLevelNames, uu____7897) in
        FStar_Errors.raise_error uu____7892 (FStar_Ident.range_of_lid l) in
      let globals = FStar_Util.mk_ref env.scope_mods in
      let env1 =
        let uu____7906 =
          match s.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let uu____7915 -> (false, true)
          | FStar_Syntax_Syntax.Sig_bundle uu____7922 -> (false, true)
          | uu____7931 -> (false, false) in
        match uu____7906 with
        | (any_val,exclude_interface) ->
            let lids = FStar_Syntax_Util.lids_of_sigelt s in
            let uu____7937 =
              FStar_Util.find_map lids
                (fun l  ->
                   let uu____7943 =
                     let uu____7944 = unique any_val exclude_interface env l in
                     Prims.op_Negation uu____7944 in
                   if uu____7943
                   then FStar_Pervasives_Native.Some l
                   else FStar_Pervasives_Native.None) in
            (match uu____7937 with
             | FStar_Pervasives_Native.Some l -> err l
             | uu____7949 ->
                 (extract_record env globals s;
                  (let uu___204_7967 = env in
                   {
                     curmodule = (uu___204_7967.curmodule);
                     curmonad = (uu___204_7967.curmonad);
                     modules = (uu___204_7967.modules);
                     scope_mods = (uu___204_7967.scope_mods);
                     exported_ids = (uu___204_7967.exported_ids);
                     trans_exported_ids = (uu___204_7967.trans_exported_ids);
                     includes = (uu___204_7967.includes);
                     sigaccum = (s :: (env.sigaccum));
                     sigmap = (uu___204_7967.sigmap);
                     iface = (uu___204_7967.iface);
                     admitted_iface = (uu___204_7967.admitted_iface);
                     expect_typ = (uu___204_7967.expect_typ);
                     docs = (uu___204_7967.docs);
                     remaining_iface_decls =
                       (uu___204_7967.remaining_iface_decls);
                     syntax_only = (uu___204_7967.syntax_only);
                     ds_hooks = (uu___204_7967.ds_hooks)
                   }))) in
      let env2 =
        let uu___205_7969 = env1 in
        let uu____7970 = FStar_ST.op_Bang globals in
        {
          curmodule = (uu___205_7969.curmodule);
          curmonad = (uu___205_7969.curmonad);
          modules = (uu___205_7969.modules);
          scope_mods = uu____7970;
          exported_ids = (uu___205_7969.exported_ids);
          trans_exported_ids = (uu___205_7969.trans_exported_ids);
          includes = (uu___205_7969.includes);
          sigaccum = (uu___205_7969.sigaccum);
          sigmap = (uu___205_7969.sigmap);
          iface = (uu___205_7969.iface);
          admitted_iface = (uu___205_7969.admitted_iface);
          expect_typ = (uu___205_7969.expect_typ);
          docs = (uu___205_7969.docs);
          remaining_iface_decls = (uu___205_7969.remaining_iface_decls);
          syntax_only = (uu___205_7969.syntax_only);
          ds_hooks = (uu___205_7969.ds_hooks)
        } in
      let uu____8039 =
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_bundle (ses,uu____8065) ->
            let uu____8074 =
              FStar_List.map
                (fun se  -> ((FStar_Syntax_Util.lids_of_sigelt se), se)) ses in
            (env2, uu____8074)
        | uu____8101 -> (env2, [((FStar_Syntax_Util.lids_of_sigelt s), s)]) in
      match uu____8039 with
      | (env3,lss) ->
          (FStar_All.pipe_right lss
             (FStar_List.iter
                (fun uu____8160  ->
                   match uu____8160 with
                   | (lids,se) ->
                       FStar_All.pipe_right lids
                         (FStar_List.iter
                            (fun lid  ->
                               (let uu____8182 =
                                  let uu____8185 = FStar_ST.op_Bang globals in
                                  (Top_level_def (lid.FStar_Ident.ident)) ::
                                    uu____8185 in
                                FStar_ST.op_Colon_Equals globals uu____8182);
                               (match () with
                                | () ->
                                    let modul =
                                      let uu____8321 =
                                        FStar_Ident.lid_of_ids
                                          lid.FStar_Ident.ns in
                                      uu____8321.FStar_Ident.str in
                                    ((let uu____8323 =
                                        get_exported_id_set env3 modul in
                                      match uu____8323 with
                                      | FStar_Pervasives_Native.Some f ->
                                          let my_exported_ids =
                                            f Exported_id_term_type in
                                          let uu____8349 =
                                            let uu____8350 =
                                              FStar_ST.op_Bang
                                                my_exported_ids in
                                            FStar_Util.set_add
                                              (lid.FStar_Ident.ident).FStar_Ident.idText
                                              uu____8350 in
                                          FStar_ST.op_Colon_Equals
                                            my_exported_ids uu____8349
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
              let uu___206_8487 = env3 in
              let uu____8488 = FStar_ST.op_Bang globals in
              {
                curmodule = (uu___206_8487.curmodule);
                curmonad = (uu___206_8487.curmonad);
                modules = (uu___206_8487.modules);
                scope_mods = uu____8488;
                exported_ids = (uu___206_8487.exported_ids);
                trans_exported_ids = (uu___206_8487.trans_exported_ids);
                includes = (uu___206_8487.includes);
                sigaccum = (uu___206_8487.sigaccum);
                sigmap = (uu___206_8487.sigmap);
                iface = (uu___206_8487.iface);
                admitted_iface = (uu___206_8487.admitted_iface);
                expect_typ = (uu___206_8487.expect_typ);
                docs = (uu___206_8487.docs);
                remaining_iface_decls = (uu___206_8487.remaining_iface_decls);
                syntax_only = (uu___206_8487.syntax_only);
                ds_hooks = (uu___206_8487.ds_hooks)
              } in
            env4))
let push_namespace: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun ns  ->
      let uu____8563 =
        let uu____8568 = resolve_module_name env ns false in
        match uu____8568 with
        | FStar_Pervasives_Native.None  ->
            let modules = env.modules in
            let uu____8582 =
              FStar_All.pipe_right modules
                (FStar_Util.for_some
                   (fun uu____8596  ->
                      match uu____8596 with
                      | (m,uu____8602) ->
                          FStar_Util.starts_with
                            (Prims.strcat (FStar_Ident.text_of_lid m) ".")
                            (Prims.strcat (FStar_Ident.text_of_lid ns) "."))) in
            if uu____8582
            then (ns, Open_namespace)
            else
              (let uu____8608 =
                 let uu____8613 =
                   FStar_Util.format1 "Namespace %s cannot be found"
                     (FStar_Ident.text_of_lid ns) in
                 (FStar_Errors.Fatal_NameSpaceNotFound, uu____8613) in
               FStar_Errors.raise_error uu____8608
                 (FStar_Ident.range_of_lid ns))
        | FStar_Pervasives_Native.Some ns' ->
            (fail_if_curmodule env ns ns'; (ns', Open_module)) in
      match uu____8563 with
      | (ns',kd) ->
          ((env.ds_hooks).ds_push_open_hook env (ns', kd);
           push_scope_mod env (Open_module_or_namespace (ns', kd)))
let push_include: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun ns  ->
      let ns0 = ns in
      let uu____8630 = resolve_module_name env ns false in
      match uu____8630 with
      | FStar_Pervasives_Native.Some ns1 ->
          ((env.ds_hooks).ds_push_include_hook env ns1;
           fail_if_curmodule env ns0 ns1;
           (let env1 =
              push_scope_mod env
                (Open_module_or_namespace (ns1, Open_module)) in
            let curmod =
              let uu____8638 = current_module env1 in
              uu____8638.FStar_Ident.str in
            (let uu____8640 = FStar_Util.smap_try_find env1.includes curmod in
             match uu____8640 with
             | FStar_Pervasives_Native.None  -> ()
             | FStar_Pervasives_Native.Some incl ->
                 let uu____8664 =
                   let uu____8667 = FStar_ST.op_Bang incl in ns1 ::
                     uu____8667 in
                 FStar_ST.op_Colon_Equals incl uu____8664);
            (match () with
             | () ->
                 let uu____8802 =
                   get_trans_exported_id_set env1 ns1.FStar_Ident.str in
                 (match uu____8802 with
                  | FStar_Pervasives_Native.Some ns_trans_exports ->
                      ((let uu____8819 =
                          let uu____8836 = get_exported_id_set env1 curmod in
                          let uu____8843 =
                            get_trans_exported_id_set env1 curmod in
                          (uu____8836, uu____8843) in
                        match uu____8819 with
                        | (FStar_Pervasives_Native.Some
                           cur_exports,FStar_Pervasives_Native.Some
                           cur_trans_exports) ->
                            let update_exports k =
                              let ns_ex =
                                let uu____8897 = ns_trans_exports k in
                                FStar_ST.op_Bang uu____8897 in
                              let ex = cur_exports k in
                              (let uu____9156 =
                                 let uu____9157 = FStar_ST.op_Bang ex in
                                 FStar_Util.set_difference uu____9157 ns_ex in
                               FStar_ST.op_Colon_Equals ex uu____9156);
                              (match () with
                               | () ->
                                   let trans_ex = cur_trans_exports k in
                                   let uu____9295 =
                                     let uu____9296 =
                                       FStar_ST.op_Bang trans_ex in
                                     FStar_Util.set_union uu____9296 ns_ex in
                                   FStar_ST.op_Colon_Equals trans_ex
                                     uu____9295) in
                            FStar_List.iter update_exports
                              all_exported_id_kinds
                        | uu____9423 -> ());
                       (match () with | () -> env1))
                  | FStar_Pervasives_Native.None  ->
                      let uu____9444 =
                        let uu____9449 =
                          FStar_Util.format1
                            "include: Module %s was not prepared"
                            ns1.FStar_Ident.str in
                        (FStar_Errors.Fatal_IncludeModuleNotPrepared,
                          uu____9449) in
                      FStar_Errors.raise_error uu____9444
                        (FStar_Ident.range_of_lid ns1)))))
      | uu____9450 ->
          let uu____9453 =
            let uu____9458 =
              FStar_Util.format1 "include: Module %s cannot be found"
                ns.FStar_Ident.str in
            (FStar_Errors.Fatal_ModuleNotFound, uu____9458) in
          FStar_Errors.raise_error uu____9453 (FStar_Ident.range_of_lid ns)
let push_module_abbrev: env -> FStar_Ident.ident -> FStar_Ident.lident -> env
  =
  fun env  ->
    fun x  ->
      fun l  ->
        let uu____9468 = module_is_defined env l in
        if uu____9468
        then
          (fail_if_curmodule env l l;
           (env.ds_hooks).ds_push_module_abbrev_hook env x l;
           push_scope_mod env (Module_abbrev (x, l)))
        else
          (let uu____9472 =
             let uu____9477 =
               FStar_Util.format1 "Module %s cannot be found"
                 (FStar_Ident.text_of_lid l) in
             (FStar_Errors.Fatal_ModuleNotFound, uu____9477) in
           FStar_Errors.raise_error uu____9472 (FStar_Ident.range_of_lid l))
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
            ((let uu____9493 =
                FStar_Util.smap_try_find env.docs l.FStar_Ident.str in
              match uu____9493 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some old_doc ->
                  let uu____9497 =
                    let uu____9502 =
                      let uu____9503 = FStar_Ident.string_of_lid l in
                      let uu____9504 =
                        FStar_Parser_AST.string_of_fsdoc old_doc in
                      let uu____9505 = FStar_Parser_AST.string_of_fsdoc doc1 in
                      FStar_Util.format3
                        "Overwriting doc of %s; old doc was [%s]; new doc are [%s]"
                        uu____9503 uu____9504 uu____9505 in
                    (FStar_Errors.Warning_DocOverwrite, uu____9502) in
                  FStar_Errors.log_issue (FStar_Ident.range_of_lid l)
                    uu____9497);
             FStar_Util.smap_add env.docs l.FStar_Ident.str doc1;
             env)
let check_admits: env -> Prims.unit =
  fun env  ->
    FStar_All.pipe_right env.sigaccum
      (FStar_List.iter
         (fun se  ->
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t) ->
                let uu____9521 = try_lookup_lid env l in
                (match uu____9521 with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____9533 =
                         let uu____9534 = FStar_Options.interactive () in
                         Prims.op_Negation uu____9534 in
                       if uu____9533
                       then
                         let uu____9535 =
                           let uu____9540 =
                             let uu____9541 =
                               FStar_Syntax_Print.lid_to_string l in
                             FStar_Util.format1
                               "Admitting %s without a definition" uu____9541 in
                           (FStar_Errors.Warning_AdmitWithoutDefinition,
                             uu____9540) in
                         FStar_Errors.log_issue (FStar_Ident.range_of_lid l)
                           uu____9535
                       else ());
                      (let quals = FStar_Syntax_Syntax.Assumption ::
                         (se.FStar_Syntax_Syntax.sigquals) in
                       FStar_Util.smap_add (sigmap env) l.FStar_Ident.str
                         ((let uu___207_9551 = se in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (uu___207_9551.FStar_Syntax_Syntax.sigel);
                             FStar_Syntax_Syntax.sigrng =
                               (uu___207_9551.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals = quals;
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___207_9551.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___207_9551.FStar_Syntax_Syntax.sigattrs)
                           }), false)))
                 | FStar_Pervasives_Native.Some uu____9552 -> ())
            | uu____9561 -> ()))
let finish: env -> FStar_Syntax_Syntax.modul -> env =
  fun env  ->
    fun modul  ->
      FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations
        (FStar_List.iter
           (fun se  ->
              let quals = se.FStar_Syntax_Syntax.sigquals in
              match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_bundle (ses,uu____9578) ->
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
                                (lid,uu____9598,uu____9599,uu____9600,uu____9601,uu____9602)
                                ->
                                FStar_Util.smap_remove (sigmap env)
                                  lid.FStar_Ident.str
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (lid,univ_names,binders,typ,uu____9615,uu____9616)
                                ->
                                (FStar_Util.smap_remove (sigmap env)
                                   lid.FStar_Ident.str;
                                 if
                                   Prims.op_Negation
                                     (FStar_List.contains
                                        FStar_Syntax_Syntax.Private quals)
                                 then
                                   (let sigel =
                                      let uu____9631 =
                                        let uu____9638 =
                                          let uu____9641 =
                                            let uu____9644 =
                                              let uu____9645 =
                                                let uu____9658 =
                                                  FStar_Syntax_Syntax.mk_Total
                                                    typ in
                                                (binders, uu____9658) in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____9645 in
                                            FStar_Syntax_Syntax.mk uu____9644 in
                                          uu____9641
                                            FStar_Pervasives_Native.None
                                            (FStar_Ident.range_of_lid lid) in
                                        (lid, univ_names, uu____9638) in
                                      FStar_Syntax_Syntax.Sig_declare_typ
                                        uu____9631 in
                                    let se2 =
                                      let uu___208_9665 = se1 in
                                      {
                                        FStar_Syntax_Syntax.sigel = sigel;
                                        FStar_Syntax_Syntax.sigrng =
                                          (uu___208_9665.FStar_Syntax_Syntax.sigrng);
                                        FStar_Syntax_Syntax.sigquals =
                                          (FStar_Syntax_Syntax.Assumption ::
                                          quals);
                                        FStar_Syntax_Syntax.sigmeta =
                                          (uu___208_9665.FStar_Syntax_Syntax.sigmeta);
                                        FStar_Syntax_Syntax.sigattrs =
                                          (uu___208_9665.FStar_Syntax_Syntax.sigattrs)
                                      } in
                                    FStar_Util.smap_add (sigmap env)
                                      lid.FStar_Ident.str (se2, false))
                                 else ())
                            | uu____9671 -> ()))
                  else ()
              | FStar_Syntax_Syntax.Sig_declare_typ
                  (lid,uu____9674,uu____9675) ->
                  if FStar_List.contains FStar_Syntax_Syntax.Private quals
                  then
                    FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str
                  else ()
              | FStar_Syntax_Syntax.Sig_let ((uu____9681,lbs),uu____9683) ->
                  (if
                     (FStar_List.contains FStar_Syntax_Syntax.Private quals)
                       ||
                       (FStar_List.contains FStar_Syntax_Syntax.Abstract
                          quals)
                   then
                     FStar_All.pipe_right lbs
                       (FStar_List.iter
                          (fun lb  ->
                             let uu____9704 =
                               let uu____9705 =
                                 let uu____9706 =
                                   let uu____9709 =
                                     FStar_Util.right
                                       lb.FStar_Syntax_Syntax.lbname in
                                   uu____9709.FStar_Syntax_Syntax.fv_name in
                                 uu____9706.FStar_Syntax_Syntax.v in
                               uu____9705.FStar_Ident.str in
                             FStar_Util.smap_remove (sigmap env) uu____9704))
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
                               let uu____9723 =
                                 let uu____9726 =
                                   FStar_Util.right
                                     lb.FStar_Syntax_Syntax.lbname in
                                 uu____9726.FStar_Syntax_Syntax.fv_name in
                               uu____9723.FStar_Syntax_Syntax.v in
                             let quals1 = FStar_Syntax_Syntax.Assumption ::
                               quals in
                             let decl =
                               let uu___209_9731 = se in
                               {
                                 FStar_Syntax_Syntax.sigel =
                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                      (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                        (lb.FStar_Syntax_Syntax.lbtyp)));
                                 FStar_Syntax_Syntax.sigrng =
                                   (uu___209_9731.FStar_Syntax_Syntax.sigrng);
                                 FStar_Syntax_Syntax.sigquals = quals1;
                                 FStar_Syntax_Syntax.sigmeta =
                                   (uu___209_9731.FStar_Syntax_Syntax.sigmeta);
                                 FStar_Syntax_Syntax.sigattrs =
                                   (uu___209_9731.FStar_Syntax_Syntax.sigattrs)
                               } in
                             FStar_Util.smap_add (sigmap env)
                               lid.FStar_Ident.str (decl, false)))
                   else ())
              | uu____9741 -> ()));
      (let curmod =
         let uu____9743 = current_module env in uu____9743.FStar_Ident.str in
       (let uu____9745 =
          let uu____9762 = get_exported_id_set env curmod in
          let uu____9769 = get_trans_exported_id_set env curmod in
          (uu____9762, uu____9769) in
        match uu____9745 with
        | (FStar_Pervasives_Native.Some cur_ex,FStar_Pervasives_Native.Some
           cur_trans_ex) ->
            let update_exports eikind =
              let cur_ex_set =
                let uu____9823 = cur_ex eikind in FStar_ST.op_Bang uu____9823 in
              let cur_trans_ex_set_ref = cur_trans_ex eikind in
              let uu____10081 =
                let uu____10082 = FStar_ST.op_Bang cur_trans_ex_set_ref in
                FStar_Util.set_union cur_ex_set uu____10082 in
              FStar_ST.op_Colon_Equals cur_trans_ex_set_ref uu____10081 in
            FStar_List.iter update_exports all_exported_id_kinds
        | uu____10209 -> ());
       (match () with
        | () ->
            (filter_record_cache ();
             (match () with
              | () ->
                  let uu___210_10227 = env in
                  {
                    curmodule = FStar_Pervasives_Native.None;
                    curmonad = (uu___210_10227.curmonad);
                    modules = (((modul.FStar_Syntax_Syntax.name), modul) ::
                      (env.modules));
                    scope_mods = [];
                    exported_ids = (uu___210_10227.exported_ids);
                    trans_exported_ids = (uu___210_10227.trans_exported_ids);
                    includes = (uu___210_10227.includes);
                    sigaccum = [];
                    sigmap = (uu___210_10227.sigmap);
                    iface = (uu___210_10227.iface);
                    admitted_iface = (uu___210_10227.admitted_iface);
                    expect_typ = (uu___210_10227.expect_typ);
                    docs = (uu___210_10227.docs);
                    remaining_iface_decls =
                      (uu___210_10227.remaining_iface_decls);
                    syntax_only = (uu___210_10227.syntax_only);
                    ds_hooks = (uu___210_10227.ds_hooks)
                  }))))
let stack: env Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let push: env -> env =
  fun env  ->
    push_record_cache ();
    (let uu____10250 =
       let uu____10253 = FStar_ST.op_Bang stack in env :: uu____10253 in
     FStar_ST.op_Colon_Equals stack uu____10250);
    (let uu___211_10360 = env in
     let uu____10361 = FStar_Util.smap_copy (sigmap env) in
     let uu____10372 = FStar_Util.smap_copy env.docs in
     {
       curmodule = (uu___211_10360.curmodule);
       curmonad = (uu___211_10360.curmonad);
       modules = (uu___211_10360.modules);
       scope_mods = (uu___211_10360.scope_mods);
       exported_ids = (uu___211_10360.exported_ids);
       trans_exported_ids = (uu___211_10360.trans_exported_ids);
       includes = (uu___211_10360.includes);
       sigaccum = (uu___211_10360.sigaccum);
       sigmap = uu____10361;
       iface = (uu___211_10360.iface);
       admitted_iface = (uu___211_10360.admitted_iface);
       expect_typ = (uu___211_10360.expect_typ);
       docs = uu____10372;
       remaining_iface_decls = (uu___211_10360.remaining_iface_decls);
       syntax_only = (uu___211_10360.syntax_only);
       ds_hooks = (uu___211_10360.ds_hooks)
     })
let pop: Prims.unit -> env =
  fun uu____10377  ->
    let uu____10378 = FStar_ST.op_Bang stack in
    match uu____10378 with
    | env::tl1 ->
        (pop_record_cache (); FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____10491 -> failwith "Impossible: Too many pops"
let export_interface: FStar_Ident.lident -> env -> env =
  fun m  ->
    fun env  ->
      let sigelt_in_m se =
        match FStar_Syntax_Util.lids_of_sigelt se with
        | l::uu____10505 -> l.FStar_Ident.nsstr = m.FStar_Ident.str
        | uu____10508 -> false in
      let sm = sigmap env in
      let env1 = pop () in
      let keys = FStar_Util.smap_keys sm in
      let sm' = sigmap env1 in
      FStar_All.pipe_right keys
        (FStar_List.iter
           (fun k  ->
              let uu____10542 = FStar_Util.smap_try_find sm' k in
              match uu____10542 with
              | FStar_Pervasives_Native.Some (se,true ) when sigelt_in_m se
                  ->
                  (FStar_Util.smap_remove sm' k;
                   (let se1 =
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t) ->
                          let uu___212_10567 = se in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (uu___212_10567.FStar_Syntax_Syntax.sigel);
                            FStar_Syntax_Syntax.sigrng =
                              (uu___212_10567.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (FStar_Syntax_Syntax.Assumption ::
                              (se.FStar_Syntax_Syntax.sigquals));
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___212_10567.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___212_10567.FStar_Syntax_Syntax.sigattrs)
                          }
                      | uu____10568 -> se in
                    FStar_Util.smap_add sm' k (se1, false)))
              | uu____10573 -> ()));
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
      let uu____10653 =
        let uu____10656 = e Exported_id_term_type in
        FStar_ST.op_Bang uu____10656 in
      FStar_Util.set_elements uu____10653 in
    let fields =
      let uu____10907 =
        let uu____10910 = e Exported_id_field in FStar_ST.op_Bang uu____10910 in
      FStar_Util.set_elements uu____10907 in
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
          let uu____11190 =
            FStar_Util.as_set e1.exported_id_terms FStar_Util.compare in
          FStar_Util.mk_ref uu____11190 in
        let fields =
          let uu____11200 =
            FStar_Util.as_set e1.exported_id_fields FStar_Util.compare in
          FStar_Util.mk_ref uu____11200 in
        (fun uu___189_11205  ->
           match uu___189_11205 with
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
  'Auu____11313 .
    'Auu____11313 Prims.list FStar_Pervasives_Native.option ->
      'Auu____11313 Prims.list FStar_ST.ref
  =
  fun uu___190_11325  ->
    match uu___190_11325 with
    | FStar_Pervasives_Native.None  -> FStar_Util.mk_ref []
    | FStar_Pervasives_Native.Some l -> FStar_Util.mk_ref l
let inclusion_info: env -> FStar_Ident.lident -> module_inclusion_info =
  fun env  ->
    fun l  ->
      let mname = FStar_Ident.string_of_lid l in
      let as_ids_opt m =
        let uu____11358 = FStar_Util.smap_try_find m mname in
        FStar_Util.map_opt uu____11358 as_exported_ids in
      let uu____11361 = as_ids_opt env.exported_ids in
      let uu____11364 = as_ids_opt env.trans_exported_ids in
      let uu____11367 =
        let uu____11372 = FStar_Util.smap_try_find env.includes mname in
        FStar_Util.map_opt uu____11372 (fun r  -> FStar_ST.op_Bang r) in
      {
        mii_exported_ids = uu____11361;
        mii_trans_exported_ids = uu____11364;
        mii_includes = uu____11367
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
                let convert_kind uu___191_11509 =
                  match uu___191_11509 with
                  | FStar_Parser_Dep.Open_namespace  -> Open_namespace
                  | FStar_Parser_Dep.Open_module  -> Open_module in
                FStar_List.map
                  (fun uu____11521  ->
                     match uu____11521 with
                     | (lid,kind) -> (lid, (convert_kind kind))) auto_open in
              let namespace_of_module =
                if
                  (FStar_List.length mname.FStar_Ident.ns) >
                    (Prims.parse_int "0")
                then
                  let uu____11545 =
                    let uu____11550 =
                      FStar_Ident.lid_of_ids mname.FStar_Ident.ns in
                    (uu____11550, Open_namespace) in
                  [uu____11545]
                else [] in
              let auto_open2 =
                FStar_List.append namespace_of_module
                  (FStar_List.rev auto_open1) in
              (let uu____11580 = as_exported_id_set mii.mii_exported_ids in
               FStar_Util.smap_add env1.exported_ids mname.FStar_Ident.str
                 uu____11580);
              (match () with
               | () ->
                   ((let uu____11596 =
                       as_exported_id_set mii.mii_trans_exported_ids in
                     FStar_Util.smap_add env1.trans_exported_ids
                       mname.FStar_Ident.str uu____11596);
                    (match () with
                     | () ->
                         ((let uu____11612 = as_includes mii.mii_includes in
                           FStar_Util.smap_add env1.includes
                             mname.FStar_Ident.str uu____11612);
                          (match () with
                           | () ->
                               let env' =
                                 let uu___213_11636 = env1 in
                                 let uu____11637 =
                                   FStar_List.map
                                     (fun x  -> Open_module_or_namespace x)
                                     auto_open2 in
                                 {
                                   curmodule =
                                     (FStar_Pervasives_Native.Some mname);
                                   curmonad = (uu___213_11636.curmonad);
                                   modules = (uu___213_11636.modules);
                                   scope_mods = uu____11637;
                                   exported_ids =
                                     (uu___213_11636.exported_ids);
                                   trans_exported_ids =
                                     (uu___213_11636.trans_exported_ids);
                                   includes = (uu___213_11636.includes);
                                   sigaccum = (uu___213_11636.sigaccum);
                                   sigmap = (env1.sigmap);
                                   iface = intf;
                                   admitted_iface = admitted;
                                   expect_typ = (uu___213_11636.expect_typ);
                                   docs = (uu___213_11636.docs);
                                   remaining_iface_decls =
                                     (uu___213_11636.remaining_iface_decls);
                                   syntax_only = (uu___213_11636.syntax_only);
                                   ds_hooks = (uu___213_11636.ds_hooks)
                                 } in
                               (FStar_List.iter
                                  (fun op  ->
                                     (env1.ds_hooks).ds_push_open_hook env'
                                       op) (FStar_List.rev auto_open2);
                                env')))))) in
            let uu____11649 =
              FStar_All.pipe_right env.modules
                (FStar_Util.find_opt
                   (fun uu____11675  ->
                      match uu____11675 with
                      | (l,uu____11681) -> FStar_Ident.lid_equals l mname)) in
            match uu____11649 with
            | FStar_Pervasives_Native.None  ->
                let uu____11690 = prep env in (uu____11690, false)
            | FStar_Pervasives_Native.Some (uu____11691,m) ->
                ((let uu____11698 =
                    (let uu____11701 = FStar_Options.interactive () in
                     Prims.op_Negation uu____11701) &&
                      ((Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)
                         || intf) in
                  if uu____11698
                  then
                    let uu____11702 =
                      let uu____11707 =
                        FStar_Util.format1
                          "Duplicate module or interface name: %s"
                          mname.FStar_Ident.str in
                      (FStar_Errors.Fatal_DuplicateModuleOrInterface,
                        uu____11707) in
                    FStar_Errors.raise_error uu____11702
                      (FStar_Ident.range_of_lid mname)
                  else ());
                 (let uu____11709 =
                    let uu____11710 = push env in prep uu____11710 in
                  (uu____11709, true)))
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
          let uu___214_11718 = env in
          {
            curmodule = (uu___214_11718.curmodule);
            curmonad = (FStar_Pervasives_Native.Some mname);
            modules = (uu___214_11718.modules);
            scope_mods = (uu___214_11718.scope_mods);
            exported_ids = (uu___214_11718.exported_ids);
            trans_exported_ids = (uu___214_11718.trans_exported_ids);
            includes = (uu___214_11718.includes);
            sigaccum = (uu___214_11718.sigaccum);
            sigmap = (uu___214_11718.sigmap);
            iface = (uu___214_11718.iface);
            admitted_iface = (uu___214_11718.admitted_iface);
            expect_typ = (uu___214_11718.expect_typ);
            docs = (uu___214_11718.docs);
            remaining_iface_decls = (uu___214_11718.remaining_iface_decls);
            syntax_only = (uu___214_11718.syntax_only);
            ds_hooks = (uu___214_11718.ds_hooks)
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
        let uu____11745 = lookup lid in
        match uu____11745 with
        | FStar_Pervasives_Native.None  ->
            let opened_modules =
              FStar_List.map
                (fun uu____11758  ->
                   match uu____11758 with
                   | (lid1,uu____11764) -> FStar_Ident.text_of_lid lid1)
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
                   let uu____11769 =
                     FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
                   FStar_Ident.set_lid_range uu____11769
                     (FStar_Ident.range_of_lid lid) in
                 let uu____11770 = resolve_module_name env modul true in
                 match uu____11770 with
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
      let uu____11801 = lookup id1 in
      match uu____11801 with
      | FStar_Pervasives_Native.None  ->
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_IdentifierNotFound,
              (Prims.strcat "Identifier not found ["
                 (Prims.strcat id1.FStar_Ident.idText "]")))
            id1.FStar_Ident.idRange
      | FStar_Pervasives_Native.Some r -> r