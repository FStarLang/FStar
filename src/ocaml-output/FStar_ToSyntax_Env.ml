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
    match projectee with | Open_module  -> true | uu____21 -> false
let uu___is_Open_namespace: open_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | Open_namespace  -> true | uu____26 -> false
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
    match projectee with | Local_binding _0 -> true | uu____198 -> false
let __proj__Local_binding__item___0: scope_mod -> local_binding =
  fun projectee  -> match projectee with | Local_binding _0 -> _0
let uu___is_Rec_binding: scope_mod -> Prims.bool =
  fun projectee  ->
    match projectee with | Rec_binding _0 -> true | uu____212 -> false
let __proj__Rec_binding__item___0: scope_mod -> rec_binding =
  fun projectee  -> match projectee with | Rec_binding _0 -> _0
let uu___is_Module_abbrev: scope_mod -> Prims.bool =
  fun projectee  ->
    match projectee with | Module_abbrev _0 -> true | uu____226 -> false
let __proj__Module_abbrev__item___0: scope_mod -> module_abbrev =
  fun projectee  -> match projectee with | Module_abbrev _0 -> _0
let uu___is_Open_module_or_namespace: scope_mod -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Open_module_or_namespace _0 -> true
    | uu____240 -> false
let __proj__Open_module_or_namespace__item___0:
  scope_mod -> open_module_or_namespace =
  fun projectee  -> match projectee with | Open_module_or_namespace _0 -> _0
let uu___is_Top_level_def: scope_mod -> Prims.bool =
  fun projectee  ->
    match projectee with | Top_level_def _0 -> true | uu____254 -> false
let __proj__Top_level_def__item___0: scope_mod -> FStar_Ident.ident =
  fun projectee  -> match projectee with | Top_level_def _0 -> _0
let uu___is_Record_or_dc: scope_mod -> Prims.bool =
  fun projectee  ->
    match projectee with | Record_or_dc _0 -> true | uu____268 -> false
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
    | uu____283 -> false
let uu___is_Exported_id_field: exported_id_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | Exported_id_field  -> true | uu____288 -> false
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
let default_ds_hooks: dsenv_hooks =
  {
    ds_push_open_hook = (fun uu____1561  -> fun uu____1562  -> ());
    ds_push_include_hook = (fun uu____1565  -> fun uu____1566  -> ());
    ds_push_module_abbrev_hook =
      (fun uu____1570  -> fun uu____1571  -> fun uu____1572  -> ())
  }
type foundname =
  | Term_name of (FStar_Syntax_Syntax.typ,Prims.bool)
  FStar_Pervasives_Native.tuple2
  | Eff_name of (FStar_Syntax_Syntax.sigelt,FStar_Ident.lident)
  FStar_Pervasives_Native.tuple2[@@deriving show]
let uu___is_Term_name: foundname -> Prims.bool =
  fun projectee  ->
    match projectee with | Term_name _0 -> true | uu____1598 -> false
let __proj__Term_name__item___0:
  foundname ->
    (FStar_Syntax_Syntax.typ,Prims.bool) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Term_name _0 -> _0
let uu___is_Eff_name: foundname -> Prims.bool =
  fun projectee  ->
    match projectee with | Eff_name _0 -> true | uu____1628 -> false
let __proj__Eff_name__item___0:
  foundname ->
    (FStar_Syntax_Syntax.sigelt,FStar_Ident.lident)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Eff_name _0 -> _0
let set_iface: env -> Prims.bool -> env =
  fun env  ->
    fun b  ->
      let uu___186_1657 = env in
      {
        curmodule = (uu___186_1657.curmodule);
        curmonad = (uu___186_1657.curmonad);
        modules = (uu___186_1657.modules);
        scope_mods = (uu___186_1657.scope_mods);
        exported_ids = (uu___186_1657.exported_ids);
        trans_exported_ids = (uu___186_1657.trans_exported_ids);
        includes = (uu___186_1657.includes);
        sigaccum = (uu___186_1657.sigaccum);
        sigmap = (uu___186_1657.sigmap);
        iface = b;
        admitted_iface = (uu___186_1657.admitted_iface);
        expect_typ = (uu___186_1657.expect_typ);
        docs = (uu___186_1657.docs);
        remaining_iface_decls = (uu___186_1657.remaining_iface_decls);
        syntax_only = (uu___186_1657.syntax_only);
        ds_hooks = (uu___186_1657.ds_hooks)
      }
let iface: env -> Prims.bool = fun e  -> e.iface
let set_admitted_iface: env -> Prims.bool -> env =
  fun e  ->
    fun b  ->
      let uu___187_1670 = e in
      {
        curmodule = (uu___187_1670.curmodule);
        curmonad = (uu___187_1670.curmonad);
        modules = (uu___187_1670.modules);
        scope_mods = (uu___187_1670.scope_mods);
        exported_ids = (uu___187_1670.exported_ids);
        trans_exported_ids = (uu___187_1670.trans_exported_ids);
        includes = (uu___187_1670.includes);
        sigaccum = (uu___187_1670.sigaccum);
        sigmap = (uu___187_1670.sigmap);
        iface = (uu___187_1670.iface);
        admitted_iface = b;
        expect_typ = (uu___187_1670.expect_typ);
        docs = (uu___187_1670.docs);
        remaining_iface_decls = (uu___187_1670.remaining_iface_decls);
        syntax_only = (uu___187_1670.syntax_only);
        ds_hooks = (uu___187_1670.ds_hooks)
      }
let admitted_iface: env -> Prims.bool = fun e  -> e.admitted_iface
let set_expect_typ: env -> Prims.bool -> env =
  fun e  ->
    fun b  ->
      let uu___188_1683 = e in
      {
        curmodule = (uu___188_1683.curmodule);
        curmonad = (uu___188_1683.curmonad);
        modules = (uu___188_1683.modules);
        scope_mods = (uu___188_1683.scope_mods);
        exported_ids = (uu___188_1683.exported_ids);
        trans_exported_ids = (uu___188_1683.trans_exported_ids);
        includes = (uu___188_1683.includes);
        sigaccum = (uu___188_1683.sigaccum);
        sigmap = (uu___188_1683.sigmap);
        iface = (uu___188_1683.iface);
        admitted_iface = (uu___188_1683.admitted_iface);
        expect_typ = b;
        docs = (uu___188_1683.docs);
        remaining_iface_decls = (uu___188_1683.remaining_iface_decls);
        syntax_only = (uu___188_1683.syntax_only);
        ds_hooks = (uu___188_1683.ds_hooks)
      }
let expect_typ: env -> Prims.bool = fun e  -> e.expect_typ
let all_exported_id_kinds: exported_id_kind Prims.list =
  [Exported_id_field; Exported_id_term_type]
let transitive_exported_ids:
  env -> FStar_Ident.lident -> Prims.string Prims.list =
  fun env  ->
    fun lid  ->
      let module_name = FStar_Ident.string_of_lid lid in
      let uu____1701 =
        FStar_Util.smap_try_find env.trans_exported_ids module_name in
      match uu____1701 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some exported_id_set ->
          let uu____1707 =
            let uu____1708 = exported_id_set Exported_id_term_type in
            FStar_ST.op_Bang uu____1708 in
          FStar_All.pipe_right uu____1707 FStar_Util.set_elements
let open_modules:
  env ->
    (FStar_Ident.lident,FStar_Syntax_Syntax.modul)
      FStar_Pervasives_Native.tuple2 Prims.list
  = fun e  -> e.modules
let open_modules_and_namespaces: env -> FStar_Ident.lident Prims.list =
  fun env  ->
    FStar_List.filter_map
      (fun uu___154_1973  ->
         match uu___154_1973 with
         | Open_module_or_namespace (lid,_info) ->
             FStar_Pervasives_Native.Some lid
         | uu____1978 -> FStar_Pervasives_Native.None) env.scope_mods
let set_current_module: env -> FStar_Ident.lident -> env =
  fun e  ->
    fun l  ->
      let uu___189_1987 = e in
      {
        curmodule = (FStar_Pervasives_Native.Some l);
        curmonad = (uu___189_1987.curmonad);
        modules = (uu___189_1987.modules);
        scope_mods = (uu___189_1987.scope_mods);
        exported_ids = (uu___189_1987.exported_ids);
        trans_exported_ids = (uu___189_1987.trans_exported_ids);
        includes = (uu___189_1987.includes);
        sigaccum = (uu___189_1987.sigaccum);
        sigmap = (uu___189_1987.sigmap);
        iface = (uu___189_1987.iface);
        admitted_iface = (uu___189_1987.admitted_iface);
        expect_typ = (uu___189_1987.expect_typ);
        docs = (uu___189_1987.docs);
        remaining_iface_decls = (uu___189_1987.remaining_iface_decls);
        syntax_only = (uu___189_1987.syntax_only);
        ds_hooks = (uu___189_1987.ds_hooks)
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
      let uu____2005 =
        FStar_All.pipe_right env.remaining_iface_decls
          (FStar_List.tryFind
             (fun uu____2039  ->
                match uu____2039 with
                | (m,uu____2047) -> FStar_Ident.lid_equals l m)) in
      match uu____2005 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (uu____2064,decls) ->
          FStar_Pervasives_Native.Some decls
let set_iface_decls:
  env -> FStar_Ident.lident -> FStar_Parser_AST.decl Prims.list -> env =
  fun env  ->
    fun l  ->
      fun ds  ->
        let uu____2094 =
          FStar_List.partition
            (fun uu____2124  ->
               match uu____2124 with
               | (m,uu____2132) -> FStar_Ident.lid_equals l m)
            env.remaining_iface_decls in
        match uu____2094 with
        | (uu____2137,rest) ->
            let uu___190_2171 = env in
            {
              curmodule = (uu___190_2171.curmodule);
              curmonad = (uu___190_2171.curmonad);
              modules = (uu___190_2171.modules);
              scope_mods = (uu___190_2171.scope_mods);
              exported_ids = (uu___190_2171.exported_ids);
              trans_exported_ids = (uu___190_2171.trans_exported_ids);
              includes = (uu___190_2171.includes);
              sigaccum = (uu___190_2171.sigaccum);
              sigmap = (uu___190_2171.sigmap);
              iface = (uu___190_2171.iface);
              admitted_iface = (uu___190_2171.admitted_iface);
              expect_typ = (uu___190_2171.expect_typ);
              docs = (uu___190_2171.docs);
              remaining_iface_decls = ((l, ds) :: rest);
              syntax_only = (uu___190_2171.syntax_only);
              ds_hooks = (uu___190_2171.ds_hooks)
            }
let qual: FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident =
  FStar_Syntax_Util.qual_id
let qualify: env -> FStar_Ident.ident -> FStar_Ident.lident =
  fun env  ->
    fun id  ->
      match env.curmonad with
      | FStar_Pervasives_Native.None  ->
          let uu____2194 = current_module env in qual uu____2194 id
      | FStar_Pervasives_Native.Some monad ->
          let uu____2196 =
            let uu____2197 = current_module env in qual uu____2197 monad in
          FStar_Syntax_Util.mk_field_projector_name_from_ident uu____2196 id
let syntax_only: env -> Prims.bool = fun env  -> env.syntax_only
let set_syntax_only: env -> Prims.bool -> env =
  fun env  ->
    fun b  ->
      let uu___191_2210 = env in
      {
        curmodule = (uu___191_2210.curmodule);
        curmonad = (uu___191_2210.curmonad);
        modules = (uu___191_2210.modules);
        scope_mods = (uu___191_2210.scope_mods);
        exported_ids = (uu___191_2210.exported_ids);
        trans_exported_ids = (uu___191_2210.trans_exported_ids);
        includes = (uu___191_2210.includes);
        sigaccum = (uu___191_2210.sigaccum);
        sigmap = (uu___191_2210.sigmap);
        iface = (uu___191_2210.iface);
        admitted_iface = (uu___191_2210.admitted_iface);
        expect_typ = (uu___191_2210.expect_typ);
        docs = (uu___191_2210.docs);
        remaining_iface_decls = (uu___191_2210.remaining_iface_decls);
        syntax_only = b;
        ds_hooks = (uu___191_2210.ds_hooks)
      }
let ds_hooks: env -> dsenv_hooks = fun env  -> env.ds_hooks
let set_ds_hooks: env -> dsenv_hooks -> env =
  fun env  ->
    fun hooks  ->
      let uu___192_2223 = env in
      {
        curmodule = (uu___192_2223.curmodule);
        curmonad = (uu___192_2223.curmonad);
        modules = (uu___192_2223.modules);
        scope_mods = (uu___192_2223.scope_mods);
        exported_ids = (uu___192_2223.exported_ids);
        trans_exported_ids = (uu___192_2223.trans_exported_ids);
        includes = (uu___192_2223.includes);
        sigaccum = (uu___192_2223.sigaccum);
        sigmap = (uu___192_2223.sigmap);
        iface = (uu___192_2223.iface);
        admitted_iface = (uu___192_2223.admitted_iface);
        expect_typ = (uu___192_2223.expect_typ);
        docs = (uu___192_2223.docs);
        remaining_iface_decls = (uu___192_2223.remaining_iface_decls);
        syntax_only = (uu___192_2223.syntax_only);
        ds_hooks = hooks
      }
let new_sigmap: 'Auu____2228 . Prims.unit -> 'Auu____2228 FStar_Util.smap =
  fun uu____2234  -> FStar_Util.smap_create (Prims.parse_int "100")
let empty_env: Prims.unit -> env =
  fun uu____2238  ->
    let uu____2239 = new_sigmap () in
    let uu____2242 = new_sigmap () in
    let uu____2245 = new_sigmap () in
    let uu____2256 = new_sigmap () in
    let uu____2267 = new_sigmap () in
    {
      curmodule = FStar_Pervasives_Native.None;
      curmonad = FStar_Pervasives_Native.None;
      modules = [];
      scope_mods = [];
      exported_ids = uu____2239;
      trans_exported_ids = uu____2242;
      includes = uu____2245;
      sigaccum = [];
      sigmap = uu____2256;
      iface = false;
      admitted_iface = false;
      expect_typ = false;
      docs = uu____2267;
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
      (fun uu____2301  ->
         match uu____2301 with
         | (m,uu____2307) ->
             FStar_Ident.lid_equals m FStar_Parser_Const.all_lid) env.modules
let set_bv_range:
  FStar_Syntax_Syntax.bv -> FStar_Range.range -> FStar_Syntax_Syntax.bv =
  fun bv  ->
    fun r  ->
      let id =
        let uu___193_2317 = bv.FStar_Syntax_Syntax.ppname in
        {
          FStar_Ident.idText = (uu___193_2317.FStar_Ident.idText);
          FStar_Ident.idRange = r
        } in
      let uu___194_2318 = bv in
      {
        FStar_Syntax_Syntax.ppname = id;
        FStar_Syntax_Syntax.index = (uu___194_2318.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = (uu___194_2318.FStar_Syntax_Syntax.sort)
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
        (fun uu____2408  ->
           match uu____2408 with
           | (x,y,dd,dq) ->
               if id.FStar_Ident.idText = x
               then
                 let uu____2431 =
                   let uu____2432 =
                     FStar_Ident.lid_of_path ["Prims"; y]
                       id.FStar_Ident.idRange in
                   FStar_Syntax_Syntax.fvar uu____2432 dd dq in
                 FStar_Pervasives_Native.Some uu____2431
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
    match projectee with | Cont_ok _0 -> true | uu____2477 -> false
let __proj__Cont_ok__item___0: 'a . 'a cont_t -> 'a =
  fun projectee  -> match projectee with | Cont_ok _0 -> _0
let uu___is_Cont_fail: 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_fail  -> true | uu____2510 -> false
let uu___is_Cont_ignore: 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_ignore  -> true | uu____2526 -> false
let option_of_cont:
  'a .
    (Prims.unit -> 'a FStar_Pervasives_Native.option) ->
      'a cont_t -> 'a FStar_Pervasives_Native.option
  =
  fun k_ignore  ->
    fun uu___155_2552  ->
      match uu___155_2552 with
      | Cont_ok a -> FStar_Pervasives_Native.Some a
      | Cont_fail  -> FStar_Pervasives_Native.None
      | Cont_ignore  -> k_ignore ()
let find_in_record:
  'Auu____2570 .
    FStar_Ident.ident Prims.list ->
      FStar_Ident.ident ->
        record_or_dc ->
          (record_or_dc -> 'Auu____2570 cont_t) -> 'Auu____2570 cont_t
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
                (fun uu____2616  ->
                   match uu____2616 with
                   | (f,uu____2624) ->
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
  fun uu___156_2675  ->
    match uu___156_2675 with
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
              let rec aux uu___157_2738 =
                match uu___157_2738 with
                | [] -> find_in_module_default
                | modul::q ->
                    let mname = modul.FStar_Ident.str in
                    let not_shadowed =
                      let uu____2749 = get_exported_id_set env mname in
                      match uu____2749 with
                      | FStar_Pervasives_Native.None  -> true
                      | FStar_Pervasives_Native.Some mex ->
                          let mexports =
                            let uu____2770 = mex eikind in
                            FStar_ST.op_Bang uu____2770 in
                          FStar_Util.set_mem idstr mexports in
                    let mincludes =
                      let uu____3017 =
                        FStar_Util.smap_try_find env.includes mname in
                      match uu____3017 with
                      | FStar_Pervasives_Native.None  -> []
                      | FStar_Pervasives_Native.Some minc ->
                          FStar_ST.op_Bang minc in
                    let look_into =
                      if not_shadowed
                      then
                        let uu____3112 = qual modul id in
                        find_in_module uu____3112
                      else Cont_ignore in
                    (match look_into with
                     | Cont_ignore  -> aux (FStar_List.append mincludes q)
                     | uu____3116 -> look_into) in
              aux [ns]
let is_exported_id_field: exported_id_kind -> Prims.bool =
  fun uu___158_3122  ->
    match uu___158_3122 with
    | Exported_id_field  -> true
    | uu____3123 -> false
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
                  let check_local_binding_id uu___159_3234 =
                    match uu___159_3234 with
                    | (id',uu____3236,uu____3237) ->
                        id'.FStar_Ident.idText = id.FStar_Ident.idText in
                  let check_rec_binding_id uu___160_3241 =
                    match uu___160_3241 with
                    | (id',uu____3243,uu____3244) ->
                        id'.FStar_Ident.idText = id.FStar_Ident.idText in
                  let curmod_ns =
                    let uu____3248 = current_module env in
                    FStar_Ident.ids_of_lid uu____3248 in
                  let proc uu___161_3254 =
                    match uu___161_3254 with
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
                        let uu____3262 = FStar_Ident.lid_of_ids curmod_ns in
                        find_in_module_with_includes Exported_id_field
                          (fun lid  ->
                             let id1 = lid.FStar_Ident.ident in
                             find_in_record lid.FStar_Ident.ns id1 r k_record)
                          Cont_ignore env uu____3262 id
                    | uu____3267 -> Cont_ignore in
                  let rec aux uu___162_3275 =
                    match uu___162_3275 with
                    | a::q ->
                        let uu____3284 = proc a in
                        option_of_cont (fun uu____3288  -> aux q) uu____3284
                    | [] ->
                        let uu____3289 = lookup_default_id Cont_fail id in
                        option_of_cont
                          (fun uu____3293  -> FStar_Pervasives_Native.None)
                          uu____3289 in
                  aux env.scope_mods
let found_local_binding:
  'Auu____3302 'Auu____3303 .
    FStar_Range.range ->
      ('Auu____3303,FStar_Syntax_Syntax.bv,'Auu____3302)
        FStar_Pervasives_Native.tuple3 ->
        (FStar_Syntax_Syntax.term,'Auu____3302)
          FStar_Pervasives_Native.tuple2
  =
  fun r  ->
    fun uu____3321  ->
      match uu____3321 with
      | (id',x,mut) -> let uu____3331 = bv_to_name x r in (uu____3331, mut)
let find_in_module:
  'Auu____3342 .
    env ->
      FStar_Ident.lident ->
        (FStar_Ident.lident ->
           (FStar_Syntax_Syntax.sigelt,Prims.bool)
             FStar_Pervasives_Native.tuple2 -> 'Auu____3342)
          -> 'Auu____3342 -> 'Auu____3342
  =
  fun env  ->
    fun lid  ->
      fun k_global_def  ->
        fun k_not_found  ->
          let uu____3377 =
            FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str in
          match uu____3377 with
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
      let uu____3415 = unmangleOpName id in
      match uu____3415 with
      | FStar_Pervasives_Native.Some f -> FStar_Pervasives_Native.Some f
      | uu____3441 ->
          try_lookup_id'' env id Exported_id_term_type
            (fun r  ->
               let uu____3455 = found_local_binding id.FStar_Ident.idRange r in
               Cont_ok uu____3455) (fun uu____3465  -> Cont_fail)
            (fun uu____3471  -> Cont_ignore)
            (fun i  ->
               find_in_module env i
                 (fun uu____3486  -> fun uu____3487  -> Cont_fail)
                 Cont_ignore)
            (fun uu____3502  -> fun uu____3503  -> Cont_fail)
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
            | FStar_Pervasives_Native.Some uu____3578 ->
                let lid = qualify env id in
                let uu____3580 =
                  FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str in
                (match uu____3580 with
                 | FStar_Pervasives_Native.Some r ->
                     let uu____3604 = k_global_def lid r in
                     FStar_Pervasives_Native.Some uu____3604
                 | FStar_Pervasives_Native.None  ->
                     FStar_Pervasives_Native.None)
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None in
          match find_in_monad with
          | FStar_Pervasives_Native.Some v1 -> v1
          | FStar_Pervasives_Native.None  ->
              let lid =
                let uu____3627 = current_module env in qual uu____3627 id in
              find_in_module env lid k_global_def k_not_found
let module_is_defined: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      (match env.curmodule with
       | FStar_Pervasives_Native.None  -> false
       | FStar_Pervasives_Native.Some m ->
           let uu____3639 = current_module env in
           FStar_Ident.lid_equals lid uu____3639)
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
        let rec aux uu___163_3674 =
          match uu___163_3674 with
          | [] ->
              let uu____3679 = module_is_defined env lid in
              if uu____3679
              then FStar_Pervasives_Native.Some lid
              else FStar_Pervasives_Native.None
          | (Open_module_or_namespace (ns,Open_namespace ))::q when honor_ns
              ->
              let new_lid =
                let uu____3688 =
                  let uu____3691 = FStar_Ident.path_of_lid ns in
                  let uu____3694 = FStar_Ident.path_of_lid lid in
                  FStar_List.append uu____3691 uu____3694 in
                FStar_Ident.lid_of_path uu____3688
                  (FStar_Ident.range_of_lid lid) in
              let uu____3697 = module_is_defined env new_lid in
              if uu____3697
              then FStar_Pervasives_Native.Some new_lid
              else aux q
          | (Module_abbrev (name,modul))::uu____3703 when
              (nslen = (Prims.parse_int "0")) &&
                (name.FStar_Ident.idText =
                   (lid.FStar_Ident.ident).FStar_Ident.idText)
              -> FStar_Pervasives_Native.Some modul
          | uu____3710::q -> aux q in
        aux env.scope_mods
let fail_if_curmodule:
  env -> FStar_Ident.lident -> FStar_Ident.lident -> Prims.unit =
  fun env  ->
    fun ns_original  ->
      fun ns_resolved  ->
        let uu____3726 =
          let uu____3727 = current_module env in
          FStar_Ident.lid_equals ns_resolved uu____3727 in
        if uu____3726
        then
          (if FStar_Ident.lid_equals ns_resolved FStar_Parser_Const.prims_lid
           then ()
           else
             (let uu____3729 =
                let uu____3730 =
                  let uu____3735 =
                    FStar_Util.format1
                      "Reference %s to current module is forbidden (see GitHub issue #451)"
                      ns_original.FStar_Ident.str in
                  (uu____3735, (FStar_Ident.range_of_lid ns_original)) in
                FStar_Errors.Error uu____3730 in
              FStar_Exn.raise uu____3729))
        else ()
let fail_if_qualified_by_curmodule: env -> FStar_Ident.lident -> Prims.unit =
  fun env  ->
    fun lid  ->
      match lid.FStar_Ident.ns with
      | [] -> ()
      | uu____3745 ->
          let modul_orig = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          let uu____3749 = resolve_module_name env modul_orig true in
          (match uu____3749 with
           | FStar_Pervasives_Native.Some modul_res ->
               fail_if_curmodule env modul_orig modul_res
           | uu____3753 -> ())
let namespace_is_open: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      FStar_List.existsb
        (fun uu___164_3766  ->
           match uu___164_3766 with
           | Open_module_or_namespace (ns,Open_namespace ) ->
               FStar_Ident.lid_equals lid ns
           | uu____3768 -> false) env.scope_mods
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
                 let uu____3860 = aux rev_ns_prefix ns_last_id in
                 FStar_All.pipe_right uu____3860
                   (FStar_Util.map_option
                      (fun uu____3910  ->
                         match uu____3910 with
                         | (stripped_ids,rev_kept_ids) ->
                             (stripped_ids, (id :: rev_kept_ids))))) in
        let uu____3941 =
          is_full_path &&
            (let uu____3943 = FStar_Ident.lid_of_ids ids in
             module_is_defined env uu____3943) in
        if uu____3941
        then (ids, [])
        else
          (match FStar_List.rev ids with
           | [] -> ([], [])
           | ns_last_id::ns_rev_prefix ->
               let uu____3973 = aux ns_rev_prefix ns_last_id in
               (match uu____3973 with
                | FStar_Pervasives_Native.None  -> ([], ids)
                | FStar_Pervasives_Native.Some (stripped_ids,rev_kept_ids) ->
                    (stripped_ids, (FStar_List.rev rev_kept_ids))))
let shorten_lid: env -> FStar_Ident.lid -> FStar_Ident.lid =
  fun env  ->
    fun lid  ->
      let uu____4034 = shorten_module_path env lid.FStar_Ident.ns true in
      match uu____4034 with
      | (uu____4043,short) ->
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
                  | uu____4160::uu____4161 ->
                      let uu____4164 =
                        let uu____4167 =
                          let uu____4168 =
                            FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
                          FStar_Ident.set_lid_range uu____4168
                            (FStar_Ident.range_of_lid lid) in
                        resolve_module_name env uu____4167 true in
                      (match uu____4164 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some modul ->
                           let uu____4172 =
                             find_in_module_with_includes eikind f_module
                               Cont_fail env modul lid.FStar_Ident.ident in
                           option_of_cont
                             (fun uu____4176  -> FStar_Pervasives_Native.None)
                             uu____4172)
                  | [] ->
                      try_lookup_id'' env lid.FStar_Ident.ident eikind
                        k_local_binding k_rec_binding k_record f_module
                        l_default
let cont_of_option:
  'a . 'a cont_t -> 'a FStar_Pervasives_Native.option -> 'a cont_t =
  fun k_none  ->
    fun uu___165_4197  ->
      match uu___165_4197 with
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
              let uu____4302 = k_global_def lid1 def in
              cont_of_option k uu____4302 in
            let f_module lid' =
              let k = Cont_ignore in
              find_in_module env lid' (k_global_def' k) k in
            let l_default k i = lookup_default_id env i (k_global_def' k) k in
            resolve_in_open_namespaces'' env lid Exported_id_term_type
              (fun l  ->
                 let uu____4332 = k_local_binding l in
                 cont_of_option Cont_fail uu____4332)
              (fun r  ->
                 let uu____4338 = k_rec_binding r in
                 cont_of_option Cont_fail uu____4338)
              (fun uu____4342  -> Cont_ignore) f_module l_default
let fv_qual_of_se:
  FStar_Syntax_Syntax.sigelt ->
    FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____4351,uu____4352,uu____4353,l,uu____4355,uu____4356) ->
        let qopt =
          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
            (fun uu___166_4367  ->
               match uu___166_4367 with
               | FStar_Syntax_Syntax.RecordConstructor (uu____4370,fs) ->
                   FStar_Pervasives_Native.Some
                     (FStar_Syntax_Syntax.Record_ctor (l, fs))
               | uu____4382 -> FStar_Pervasives_Native.None) in
        (match qopt with
         | FStar_Pervasives_Native.None  ->
             FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor
         | x -> x)
    | FStar_Syntax_Syntax.Sig_declare_typ (uu____4388,uu____4389,uu____4390)
        -> FStar_Pervasives_Native.None
    | uu____4391 -> FStar_Pervasives_Native.None
let lb_fv:
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Ident.lident -> FStar_Syntax_Syntax.fv
  =
  fun lbs  ->
    fun lid  ->
      let uu____4404 =
        FStar_Util.find_map lbs
          (fun lb  ->
             let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
             let uu____4412 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
             if uu____4412
             then FStar_Pervasives_Native.Some fv
             else FStar_Pervasives_Native.None) in
      FStar_All.pipe_right uu____4404 FStar_Util.must
let ns_of_lid_equals: FStar_Ident.lident -> FStar_Ident.lident -> Prims.bool
  =
  fun lid  ->
    fun ns  ->
      ((FStar_List.length lid.FStar_Ident.ns) =
         (FStar_List.length (FStar_Ident.ids_of_lid ns)))
        &&
        (let uu____4427 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
         FStar_Ident.lid_equals uu____4427 ns)
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
          let k_global_def source_lid uu___171_4461 =
            match uu___171_4461 with
            | (uu____4468,true ) when exclude_interf ->
                FStar_Pervasives_Native.None
            | (se,uu____4470) ->
                (match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_inductive_typ uu____4473 ->
                     let uu____4490 =
                       let uu____4491 =
                         let uu____4496 =
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.Delta_constant
                             FStar_Pervasives_Native.None in
                         (uu____4496, false) in
                       Term_name uu____4491 in
                     FStar_Pervasives_Native.Some uu____4490
                 | FStar_Syntax_Syntax.Sig_datacon uu____4497 ->
                     let uu____4512 =
                       let uu____4513 =
                         let uu____4518 =
                           let uu____4519 = fv_qual_of_se se in
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.Delta_constant uu____4519 in
                         (uu____4518, false) in
                       Term_name uu____4513 in
                     FStar_Pervasives_Native.Some uu____4512
                 | FStar_Syntax_Syntax.Sig_let ((uu____4522,lbs),uu____4524)
                     ->
                     let fv = lb_fv lbs source_lid in
                     let uu____4540 =
                       let uu____4541 =
                         let uu____4546 =
                           FStar_Syntax_Syntax.fvar source_lid
                             fv.FStar_Syntax_Syntax.fv_delta
                             fv.FStar_Syntax_Syntax.fv_qual in
                         (uu____4546, false) in
                       Term_name uu____4541 in
                     FStar_Pervasives_Native.Some uu____4540
                 | FStar_Syntax_Syntax.Sig_declare_typ
                     (lid1,uu____4548,uu____4549) ->
                     let quals = se.FStar_Syntax_Syntax.sigquals in
                     let uu____4553 =
                       any_val ||
                         (FStar_All.pipe_right quals
                            (FStar_Util.for_some
                               (fun uu___167_4557  ->
                                  match uu___167_4557 with
                                  | FStar_Syntax_Syntax.Assumption  -> true
                                  | uu____4558 -> false))) in
                     if uu____4553
                     then
                       let lid2 =
                         FStar_Ident.set_lid_range lid1
                           (FStar_Ident.range_of_lid source_lid) in
                       let dd =
                         let uu____4563 =
                           (FStar_Syntax_Util.is_primop_lid lid2) ||
                             (FStar_All.pipe_right quals
                                (FStar_Util.for_some
                                   (fun uu___168_4568  ->
                                      match uu___168_4568 with
                                      | FStar_Syntax_Syntax.Projector
                                          uu____4569 -> true
                                      | FStar_Syntax_Syntax.Discriminator
                                          uu____4574 -> true
                                      | uu____4575 -> false))) in
                         if uu____4563
                         then FStar_Syntax_Syntax.Delta_equational
                         else FStar_Syntax_Syntax.Delta_constant in
                       let dd1 =
                         let uu____4578 =
                           FStar_All.pipe_right quals
                             (FStar_Util.for_some
                                (fun uu___169_4582  ->
                                   match uu___169_4582 with
                                   | FStar_Syntax_Syntax.Abstract  -> true
                                   | uu____4583 -> false)) in
                         if uu____4578
                         then FStar_Syntax_Syntax.Delta_abstract dd
                         else dd in
                       let uu____4585 =
                         FStar_Util.find_map quals
                           (fun uu___170_4590  ->
                              match uu___170_4590 with
                              | FStar_Syntax_Syntax.Reflectable refl_monad ->
                                  FStar_Pervasives_Native.Some refl_monad
                              | uu____4594 -> FStar_Pervasives_Native.None) in
                       (match uu____4585 with
                        | FStar_Pervasives_Native.Some refl_monad ->
                            let refl_const =
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_constant
                                   (FStar_Const.Const_reflect refl_monad))
                                FStar_Pervasives_Native.None occurrence_range in
                            FStar_Pervasives_Native.Some
                              (Term_name (refl_const, false))
                        | uu____4603 ->
                            let uu____4606 =
                              let uu____4607 =
                                let uu____4612 =
                                  let uu____4613 = fv_qual_of_se se in
                                  FStar_Syntax_Syntax.fvar lid2 dd1
                                    uu____4613 in
                                (uu____4612, false) in
                              Term_name uu____4607 in
                            FStar_Pervasives_Native.Some uu____4606)
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
                 | FStar_Syntax_Syntax.Sig_effect_abbrev uu____4619 ->
                     FStar_Pervasives_Native.Some (Eff_name (se, source_lid))
                 | uu____4632 -> FStar_Pervasives_Native.None) in
          let k_local_binding r =
            let uu____4651 =
              let uu____4652 =
                found_local_binding (FStar_Ident.range_of_lid lid) r in
              Term_name uu____4652 in
            FStar_Pervasives_Native.Some uu____4651 in
          let k_rec_binding uu____4668 =
            match uu____4668 with
            | (id,l,dd) ->
                let uu____4680 =
                  let uu____4681 =
                    let uu____4686 =
                      FStar_Syntax_Syntax.fvar
                        (FStar_Ident.set_lid_range l
                           (FStar_Ident.range_of_lid lid)) dd
                        FStar_Pervasives_Native.None in
                    (uu____4686, false) in
                  Term_name uu____4681 in
                FStar_Pervasives_Native.Some uu____4680 in
          let found_unmangled =
            match lid.FStar_Ident.ns with
            | [] ->
                let uu____4692 = unmangleOpName lid.FStar_Ident.ident in
                (match uu____4692 with
                 | FStar_Pervasives_Native.Some f ->
                     FStar_Pervasives_Native.Some (Term_name f)
                 | uu____4710 -> FStar_Pervasives_Native.None)
            | uu____4717 -> FStar_Pervasives_Native.None in
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
        let uu____4749 = try_lookup_name true exclude_interf env lid in
        match uu____4749 with
        | FStar_Pervasives_Native.Some (Eff_name (o,l)) ->
            FStar_Pervasives_Native.Some (o, l)
        | uu____4764 -> FStar_Pervasives_Native.None
let try_lookup_effect_name:
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____4781 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____4781 with
      | FStar_Pervasives_Native.Some (o,l1) ->
          FStar_Pervasives_Native.Some l1
      | uu____4796 -> FStar_Pervasives_Native.None
let try_lookup_effect_name_and_attributes:
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident,FStar_Syntax_Syntax.cflags Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____4819 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____4819 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____4835;
             FStar_Syntax_Syntax.sigquals = uu____4836;
             FStar_Syntax_Syntax.sigmeta = uu____4837;
             FStar_Syntax_Syntax.sigattrs = uu____4838;_},l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____4857;
             FStar_Syntax_Syntax.sigquals = uu____4858;
             FStar_Syntax_Syntax.sigmeta = uu____4859;
             FStar_Syntax_Syntax.sigattrs = uu____4860;_},l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (uu____4878,uu____4879,uu____4880,uu____4881,cattributes);
             FStar_Syntax_Syntax.sigrng = uu____4883;
             FStar_Syntax_Syntax.sigquals = uu____4884;
             FStar_Syntax_Syntax.sigmeta = uu____4885;
             FStar_Syntax_Syntax.sigattrs = uu____4886;_},l1)
          -> FStar_Pervasives_Native.Some (l1, cattributes)
      | uu____4908 -> FStar_Pervasives_Native.None
let try_lookup_effect_defn:
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.eff_decl FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____4931 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____4931 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____4941;
             FStar_Syntax_Syntax.sigquals = uu____4942;
             FStar_Syntax_Syntax.sigmeta = uu____4943;
             FStar_Syntax_Syntax.sigattrs = uu____4944;_},uu____4945)
          -> FStar_Pervasives_Native.Some ne
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____4955;
             FStar_Syntax_Syntax.sigquals = uu____4956;
             FStar_Syntax_Syntax.sigmeta = uu____4957;
             FStar_Syntax_Syntax.sigattrs = uu____4958;_},uu____4959)
          -> FStar_Pervasives_Native.Some ne
      | uu____4968 -> FStar_Pervasives_Native.None
let is_effect_name: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____4983 = try_lookup_effect_name env lid in
      match uu____4983 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____4986 -> true
let try_lookup_root_effect_name:
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____4997 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____4997 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (l',uu____5007,uu____5008,uu____5009,uu____5010);
             FStar_Syntax_Syntax.sigrng = uu____5011;
             FStar_Syntax_Syntax.sigquals = uu____5012;
             FStar_Syntax_Syntax.sigmeta = uu____5013;
             FStar_Syntax_Syntax.sigattrs = uu____5014;_},uu____5015)
          ->
          let rec aux new_name =
            let uu____5034 =
              FStar_Util.smap_try_find (sigmap env) new_name.FStar_Ident.str in
            match uu____5034 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (s,uu____5052) ->
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
                     (uu____5061,uu____5062,uu____5063,cmp,uu____5065) ->
                     let l'' = FStar_Syntax_Util.comp_effect_name cmp in
                     aux l''
                 | uu____5071 -> FStar_Pervasives_Native.None) in
          aux l'
      | FStar_Pervasives_Native.Some (uu____5072,l') ->
          FStar_Pervasives_Native.Some l'
      | uu____5078 -> FStar_Pervasives_Native.None
let lookup_letbinding_quals:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___172_5109 =
        match uu___172_5109 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____5118,uu____5119,uu____5120);
             FStar_Syntax_Syntax.sigrng = uu____5121;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____5123;
             FStar_Syntax_Syntax.sigattrs = uu____5124;_},uu____5125)
            -> FStar_Pervasives_Native.Some quals
        | uu____5132 -> FStar_Pervasives_Native.None in
      let uu____5139 =
        resolve_in_open_namespaces' env lid
          (fun uu____5147  -> FStar_Pervasives_Native.None)
          (fun uu____5151  -> FStar_Pervasives_Native.None) k_global_def in
      match uu____5139 with
      | FStar_Pervasives_Native.Some quals -> quals
      | uu____5161 -> []
let try_lookup_module:
  env ->
    Prims.string Prims.list ->
      FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option
  =
  fun env  ->
    fun path  ->
      let uu____5180 =
        FStar_List.tryFind
          (fun uu____5195  ->
             match uu____5195 with
             | (mlid,modul) ->
                 let uu____5202 = FStar_Ident.path_of_lid mlid in
                 uu____5202 = path) env.modules in
      match uu____5180 with
      | FStar_Pervasives_Native.Some (uu____5209,modul) ->
          FStar_Pervasives_Native.Some modul
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
let try_lookup_let:
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___173_5241 =
        match uu___173_5241 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               ((uu____5248,lbs),uu____5250);
             FStar_Syntax_Syntax.sigrng = uu____5251;
             FStar_Syntax_Syntax.sigquals = uu____5252;
             FStar_Syntax_Syntax.sigmeta = uu____5253;
             FStar_Syntax_Syntax.sigattrs = uu____5254;_},uu____5255)
            ->
            let fv = lb_fv lbs lid1 in
            let uu____5275 =
              FStar_Syntax_Syntax.fvar lid1 fv.FStar_Syntax_Syntax.fv_delta
                fv.FStar_Syntax_Syntax.fv_qual in
            FStar_Pervasives_Native.Some uu____5275
        | uu____5276 -> FStar_Pervasives_Native.None in
      resolve_in_open_namespaces' env lid
        (fun uu____5282  -> FStar_Pervasives_Native.None)
        (fun uu____5284  -> FStar_Pervasives_Native.None) k_global_def
let try_lookup_definition:
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___174_5309 =
        match uu___174_5309 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               (lbs,uu____5319);
             FStar_Syntax_Syntax.sigrng = uu____5320;
             FStar_Syntax_Syntax.sigquals = uu____5321;
             FStar_Syntax_Syntax.sigmeta = uu____5322;
             FStar_Syntax_Syntax.sigattrs = uu____5323;_},uu____5324)
            ->
            FStar_Util.find_map (FStar_Pervasives_Native.snd lbs)
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inr fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv lid1 ->
                     FStar_Pervasives_Native.Some
                       (lb.FStar_Syntax_Syntax.lbdef)
                 | uu____5347 -> FStar_Pervasives_Native.None)
        | uu____5354 -> FStar_Pervasives_Native.None in
      resolve_in_open_namespaces' env lid
        (fun uu____5364  -> FStar_Pervasives_Native.None)
        (fun uu____5368  -> FStar_Pervasives_Native.None) k_global_def
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
    fun exclude_interf  ->
      fun env  ->
        fun lid  ->
          let uu____5411 = try_lookup_name any_val exclude_interf env lid in
          match uu____5411 with
          | FStar_Pervasives_Native.Some (Term_name (e,mut)) ->
              FStar_Pervasives_Native.Some (e, mut)
          | uu____5426 -> FStar_Pervasives_Native.None
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
      let uu____5457 = try_lookup_lid env l in
      match uu____5457 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (e,uu____5471) ->
          let uu____5476 =
            let uu____5477 = FStar_Syntax_Subst.compress e in
            uu____5477.FStar_Syntax_Syntax.n in
          (match uu____5476 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               FStar_Pervasives_Native.Some
                 ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
           | uu____5483 -> FStar_Pervasives_Native.None)
let try_lookup_lid_no_resolve:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term,Prims.bool) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let env' =
        let uu___195_5499 = env in
        {
          curmodule = (uu___195_5499.curmodule);
          curmonad = (uu___195_5499.curmonad);
          modules = (uu___195_5499.modules);
          scope_mods = [];
          exported_ids = empty_exported_id_smap;
          trans_exported_ids = (uu___195_5499.trans_exported_ids);
          includes = empty_include_smap;
          sigaccum = (uu___195_5499.sigaccum);
          sigmap = (uu___195_5499.sigmap);
          iface = (uu___195_5499.iface);
          admitted_iface = (uu___195_5499.admitted_iface);
          expect_typ = (uu___195_5499.expect_typ);
          docs = (uu___195_5499.docs);
          remaining_iface_decls = (uu___195_5499.remaining_iface_decls);
          syntax_only = (uu___195_5499.syntax_only);
          ds_hooks = (uu___195_5499.ds_hooks)
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
      let k_global_def lid1 uu___176_5532 =
        match uu___176_5532 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____5539,uu____5540,uu____5541);
             FStar_Syntax_Syntax.sigrng = uu____5542;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____5544;
             FStar_Syntax_Syntax.sigattrs = uu____5545;_},uu____5546)
            ->
            let uu____5551 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___175_5555  ->
                      match uu___175_5555 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | uu____5556 -> false)) in
            if uu____5551
            then
              let uu____5559 =
                FStar_Syntax_Syntax.lid_as_fv lid1
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None in
              FStar_Pervasives_Native.Some uu____5559
            else FStar_Pervasives_Native.None
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
               uu____5561;
             FStar_Syntax_Syntax.sigrng = uu____5562;
             FStar_Syntax_Syntax.sigquals = uu____5563;
             FStar_Syntax_Syntax.sigmeta = uu____5564;
             FStar_Syntax_Syntax.sigattrs = uu____5565;_},uu____5566)
            ->
            let uu____5585 =
              FStar_Syntax_Syntax.lid_as_fv lid1
                FStar_Syntax_Syntax.Delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor) in
            FStar_Pervasives_Native.Some uu____5585
        | uu____5586 -> FStar_Pervasives_Native.None in
      resolve_in_open_namespaces' env lid
        (fun uu____5592  -> FStar_Pervasives_Native.None)
        (fun uu____5594  -> FStar_Pervasives_Native.None) k_global_def
let find_all_datacons:
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident Prims.list FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___177_5621 =
        match uu___177_5621 with
        | ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_inductive_typ
               (uu____5630,uu____5631,uu____5632,uu____5633,datas,uu____5635);
             FStar_Syntax_Syntax.sigrng = uu____5636;
             FStar_Syntax_Syntax.sigquals = uu____5637;
             FStar_Syntax_Syntax.sigmeta = uu____5638;
             FStar_Syntax_Syntax.sigattrs = uu____5639;_},uu____5640)
            -> FStar_Pervasives_Native.Some datas
        | uu____5655 -> FStar_Pervasives_Native.None in
      resolve_in_open_namespaces' env lid
        (fun uu____5665  -> FStar_Pervasives_Native.None)
        (fun uu____5669  -> FStar_Pervasives_Native.None) k_global_def
let record_cache_aux_with_filter:
  ((Prims.unit -> Prims.unit,Prims.unit -> Prims.unit,Prims.unit ->
                                                        record_or_dc
                                                          Prims.list,
     record_or_dc -> Prims.unit) FStar_Pervasives_Native.tuple4,Prims.unit ->
                                                                  Prims.unit)
    FStar_Pervasives_Native.tuple2
  =
  let record_cache = FStar_Util.mk_ref [[]] in
  let push1 uu____5714 =
    let uu____5715 =
      let uu____5720 =
        let uu____5723 = FStar_ST.op_Bang record_cache in
        FStar_List.hd uu____5723 in
      let uu____5798 = FStar_ST.op_Bang record_cache in uu____5720 ::
        uu____5798 in
    FStar_ST.op_Colon_Equals record_cache uu____5715 in
  let pop1 uu____5944 =
    let uu____5945 =
      let uu____5950 = FStar_ST.op_Bang record_cache in
      FStar_List.tl uu____5950 in
    FStar_ST.op_Colon_Equals record_cache uu____5945 in
  let peek1 uu____6098 =
    let uu____6099 = FStar_ST.op_Bang record_cache in
    FStar_List.hd uu____6099 in
  let insert r =
    let uu____6178 =
      let uu____6183 = let uu____6186 = peek1 () in r :: uu____6186 in
      let uu____6189 =
        let uu____6194 = FStar_ST.op_Bang record_cache in
        FStar_List.tl uu____6194 in
      uu____6183 :: uu____6189 in
    FStar_ST.op_Colon_Equals record_cache uu____6178 in
  let filter1 uu____6342 =
    let rc = peek1 () in
    let filtered =
      FStar_List.filter
        (fun r  -> Prims.op_Negation r.is_private_or_abstract) rc in
    let uu____6351 =
      let uu____6356 =
        let uu____6361 = FStar_ST.op_Bang record_cache in
        FStar_List.tl uu____6361 in
      filtered :: uu____6356 in
    FStar_ST.op_Colon_Equals record_cache uu____6351 in
  let aux = (push1, pop1, peek1, insert) in (aux, filter1)
let record_cache_aux:
  (Prims.unit -> Prims.unit,Prims.unit -> Prims.unit,Prims.unit ->
                                                       record_or_dc
                                                         Prims.list,record_or_dc
                                                                    ->
                                                                    Prims.unit)
    FStar_Pervasives_Native.tuple4
  =
  let uu____6573 = record_cache_aux_with_filter in
  match uu____6573 with | (aux,uu____6617) -> aux
let filter_record_cache: Prims.unit -> Prims.unit =
  let uu____6661 = record_cache_aux_with_filter in
  match uu____6661 with | (uu____6688,filter1) -> filter1
let push_record_cache: Prims.unit -> Prims.unit =
  let uu____6733 = record_cache_aux in
  match uu____6733 with | (push1,uu____6755,uu____6756,uu____6757) -> push1
let pop_record_cache: Prims.unit -> Prims.unit =
  let uu____6781 = record_cache_aux in
  match uu____6781 with | (uu____6802,pop1,uu____6804,uu____6805) -> pop1
let peek_record_cache: Prims.unit -> record_or_dc Prims.list =
  let uu____6831 = record_cache_aux in
  match uu____6831 with | (uu____6854,uu____6855,peek1,uu____6857) -> peek1
let insert_record_cache: record_or_dc -> Prims.unit =
  let uu____6881 = record_cache_aux in
  match uu____6881 with | (uu____6902,uu____6903,uu____6904,insert) -> insert
let extract_record:
  env ->
    scope_mod Prims.list FStar_ST.ref ->
      FStar_Syntax_Syntax.sigelt -> Prims.unit
  =
  fun e  ->
    fun new_globs  ->
      fun se  ->
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_bundle (sigs,uu____6961) ->
            let is_record =
              FStar_Util.for_some
                (fun uu___178_6977  ->
                   match uu___178_6977 with
                   | FStar_Syntax_Syntax.RecordType uu____6978 -> true
                   | FStar_Syntax_Syntax.RecordConstructor uu____6987 -> true
                   | uu____6996 -> false) in
            let find_dc dc =
              FStar_All.pipe_right sigs
                (FStar_Util.find_opt
                   (fun uu___179_7018  ->
                      match uu___179_7018 with
                      | {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_datacon
                            (lid,uu____7020,uu____7021,uu____7022,uu____7023,uu____7024);
                          FStar_Syntax_Syntax.sigrng = uu____7025;
                          FStar_Syntax_Syntax.sigquals = uu____7026;
                          FStar_Syntax_Syntax.sigmeta = uu____7027;
                          FStar_Syntax_Syntax.sigattrs = uu____7028;_} ->
                          FStar_Ident.lid_equals dc lid
                      | uu____7037 -> false)) in
            FStar_All.pipe_right sigs
              (FStar_List.iter
                 (fun uu___180_7072  ->
                    match uu___180_7072 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ
                          (typename,univs1,parms,uu____7076,uu____7077,dc::[]);
                        FStar_Syntax_Syntax.sigrng = uu____7079;
                        FStar_Syntax_Syntax.sigquals = typename_quals;
                        FStar_Syntax_Syntax.sigmeta = uu____7081;
                        FStar_Syntax_Syntax.sigattrs = uu____7082;_} ->
                        let uu____7093 =
                          let uu____7094 = find_dc dc in
                          FStar_All.pipe_left FStar_Util.must uu____7094 in
                        (match uu____7093 with
                         | {
                             FStar_Syntax_Syntax.sigel =
                               FStar_Syntax_Syntax.Sig_datacon
                               (constrname,uu____7100,t,uu____7102,uu____7103,uu____7104);
                             FStar_Syntax_Syntax.sigrng = uu____7105;
                             FStar_Syntax_Syntax.sigquals = uu____7106;
                             FStar_Syntax_Syntax.sigmeta = uu____7107;
                             FStar_Syntax_Syntax.sigattrs = uu____7108;_} ->
                             let uu____7117 =
                               FStar_Syntax_Util.arrow_formals t in
                             (match uu____7117 with
                              | (formals,uu____7131) ->
                                  let is_rec = is_record typename_quals in
                                  let formals' =
                                    FStar_All.pipe_right formals
                                      (FStar_List.collect
                                         (fun uu____7180  ->
                                            match uu____7180 with
                                            | (x,q) ->
                                                let uu____7193 =
                                                  (FStar_Syntax_Syntax.is_null_bv
                                                     x)
                                                    ||
                                                    (is_rec &&
                                                       (FStar_Syntax_Syntax.is_implicit
                                                          q)) in
                                                if uu____7193
                                                then []
                                                else [(x, q)])) in
                                  let fields' =
                                    FStar_All.pipe_right formals'
                                      (FStar_List.map
                                         (fun uu____7250  ->
                                            match uu____7250 with
                                            | (x,q) ->
                                                let uu____7263 =
                                                  if is_rec
                                                  then
                                                    FStar_Syntax_Util.unmangle_field_name
                                                      x.FStar_Syntax_Syntax.ppname
                                                  else
                                                    x.FStar_Syntax_Syntax.ppname in
                                                (uu____7263,
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
                                  ((let uu____7278 =
                                      let uu____7281 =
                                        FStar_ST.op_Bang new_globs in
                                      (Record_or_dc record) :: uu____7281 in
                                    FStar_ST.op_Colon_Equals new_globs
                                      uu____7278);
                                   (match () with
                                    | () ->
                                        ((let add_field uu____7422 =
                                            match uu____7422 with
                                            | (id,uu____7430) ->
                                                let modul =
                                                  let uu____7436 =
                                                    FStar_Ident.lid_of_ids
                                                      constrname.FStar_Ident.ns in
                                                  uu____7436.FStar_Ident.str in
                                                let uu____7437 =
                                                  get_exported_id_set e modul in
                                                (match uu____7437 with
                                                 | FStar_Pervasives_Native.Some
                                                     my_ex ->
                                                     let my_exported_ids =
                                                       my_ex
                                                         Exported_id_field in
                                                     ((let uu____7464 =
                                                         let uu____7465 =
                                                           FStar_ST.op_Bang
                                                             my_exported_ids in
                                                         FStar_Util.set_add
                                                           id.FStar_Ident.idText
                                                           uu____7465 in
                                                       FStar_ST.op_Colon_Equals
                                                         my_exported_ids
                                                         uu____7464);
                                                      (match () with
                                                       | () ->
                                                           let projname =
                                                             let uu____7589 =
                                                               let uu____7590
                                                                 =
                                                                 FStar_Syntax_Util.mk_field_projector_name_from_ident
                                                                   constrname
                                                                   id in
                                                               uu____7590.FStar_Ident.ident in
                                                             uu____7589.FStar_Ident.idText in
                                                           let uu____7592 =
                                                             let uu____7593 =
                                                               FStar_ST.op_Bang
                                                                 my_exported_ids in
                                                             FStar_Util.set_add
                                                               projname
                                                               uu____7593 in
                                                           FStar_ST.op_Colon_Equals
                                                             my_exported_ids
                                                             uu____7592))
                                                 | FStar_Pervasives_Native.None
                                                      -> ()) in
                                          FStar_List.iter add_field fields');
                                         (match () with
                                          | () -> insert_record_cache record)))))
                         | uu____7726 -> ())
                    | uu____7727 -> ()))
        | uu____7728 -> ()
let try_lookup_record_or_dc_by_field_name:
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option =
  fun env  ->
    fun fieldname  ->
      let find_in_cache fieldname1 =
        let uu____7745 =
          ((fieldname1.FStar_Ident.ns), (fieldname1.FStar_Ident.ident)) in
        match uu____7745 with
        | (ns,id) ->
            let uu____7762 = peek_record_cache () in
            FStar_Util.find_map uu____7762
              (fun record  ->
                 let uu____7768 =
                   find_in_record ns id record (fun r  -> Cont_ok r) in
                 option_of_cont
                   (fun uu____7774  -> FStar_Pervasives_Native.None)
                   uu____7768) in
      resolve_in_open_namespaces'' env fieldname Exported_id_field
        (fun uu____7776  -> Cont_ignore) (fun uu____7778  -> Cont_ignore)
        (fun r  -> Cont_ok r)
        (fun fn  ->
           let uu____7784 = find_in_cache fn in
           cont_of_option Cont_ignore uu____7784)
        (fun k  -> fun uu____7790  -> k)
let try_lookup_record_by_field_name:
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option =
  fun env  ->
    fun fieldname  ->
      let uu____7803 = try_lookup_record_or_dc_by_field_name env fieldname in
      match uu____7803 with
      | FStar_Pervasives_Native.Some r when r.is_record ->
          FStar_Pervasives_Native.Some r
      | uu____7809 -> FStar_Pervasives_Native.None
let belongs_to_record:
  env -> FStar_Ident.lident -> record_or_dc -> Prims.bool =
  fun env  ->
    fun lid  ->
      fun record  ->
        let uu____7824 = try_lookup_record_by_field_name env lid in
        match uu____7824 with
        | FStar_Pervasives_Native.Some record' when
            let uu____7828 =
              let uu____7829 =
                FStar_Ident.path_of_ns (record.typename).FStar_Ident.ns in
              FStar_Ident.text_of_path uu____7829 in
            let uu____7832 =
              let uu____7833 =
                FStar_Ident.path_of_ns (record'.typename).FStar_Ident.ns in
              FStar_Ident.text_of_path uu____7833 in
            uu____7828 = uu____7832 ->
            let uu____7836 =
              find_in_record (record.typename).FStar_Ident.ns
                lid.FStar_Ident.ident record (fun uu____7840  -> Cont_ok ()) in
            (match uu____7836 with
             | Cont_ok uu____7841 -> true
             | uu____7842 -> false)
        | uu____7845 -> false
let try_lookup_dc_by_field_name:
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident,Prims.bool) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option
  =
  fun env  ->
    fun fieldname  ->
      let uu____7862 = try_lookup_record_or_dc_by_field_name env fieldname in
      match uu____7862 with
      | FStar_Pervasives_Native.Some r ->
          let uu____7872 =
            let uu____7877 =
              let uu____7878 =
                FStar_Ident.lid_of_ids
                  (FStar_List.append (r.typename).FStar_Ident.ns
                     [r.constrname]) in
              FStar_Ident.set_lid_range uu____7878
                (FStar_Ident.range_of_lid fieldname) in
            (uu____7877, (r.is_record)) in
          FStar_Pervasives_Native.Some uu____7872
      | uu____7883 -> FStar_Pervasives_Native.None
let string_set_ref_new:
  Prims.unit -> Prims.string FStar_Util.set FStar_ST.ref =
  fun uu____7904  ->
    let uu____7905 = FStar_Util.new_set FStar_Util.compare in
    FStar_Util.mk_ref uu____7905
let exported_id_set_new:
  Prims.unit -> exported_id_kind -> Prims.string FStar_Util.set FStar_ST.ref
  =
  fun uu____7926  ->
    let term_type_set = string_set_ref_new () in
    let field_set = string_set_ref_new () in
    fun uu___181_7937  ->
      match uu___181_7937 with
      | Exported_id_term_type  -> term_type_set
      | Exported_id_field  -> field_set
let unique:
  Prims.bool -> Prims.bool -> env -> FStar_Ident.lident -> Prims.bool =
  fun any_val  ->
    fun exclude_if  ->
      fun env  ->
        fun lid  ->
          let filter_scope_mods uu___182_7975 =
            match uu___182_7975 with
            | Rec_binding uu____7976 -> true
            | uu____7977 -> false in
          let this_env =
            let uu___196_7979 = env in
            let uu____7980 =
              FStar_List.filter filter_scope_mods env.scope_mods in
            {
              curmodule = (uu___196_7979.curmodule);
              curmonad = (uu___196_7979.curmonad);
              modules = (uu___196_7979.modules);
              scope_mods = uu____7980;
              exported_ids = empty_exported_id_smap;
              trans_exported_ids = (uu___196_7979.trans_exported_ids);
              includes = empty_include_smap;
              sigaccum = (uu___196_7979.sigaccum);
              sigmap = (uu___196_7979.sigmap);
              iface = (uu___196_7979.iface);
              admitted_iface = (uu___196_7979.admitted_iface);
              expect_typ = (uu___196_7979.expect_typ);
              docs = (uu___196_7979.docs);
              remaining_iface_decls = (uu___196_7979.remaining_iface_decls);
              syntax_only = (uu___196_7979.syntax_only);
              ds_hooks = (uu___196_7979.ds_hooks)
            } in
          let uu____7983 = try_lookup_lid' any_val exclude_if this_env lid in
          match uu____7983 with
          | FStar_Pervasives_Native.None  -> true
          | FStar_Pervasives_Native.Some uu____7994 -> false
let push_scope_mod: env -> scope_mod -> env =
  fun env  ->
    fun scope_mod  ->
      let uu___197_8011 = env in
      {
        curmodule = (uu___197_8011.curmodule);
        curmonad = (uu___197_8011.curmonad);
        modules = (uu___197_8011.modules);
        scope_mods = (scope_mod :: (env.scope_mods));
        exported_ids = (uu___197_8011.exported_ids);
        trans_exported_ids = (uu___197_8011.trans_exported_ids);
        includes = (uu___197_8011.includes);
        sigaccum = (uu___197_8011.sigaccum);
        sigmap = (uu___197_8011.sigmap);
        iface = (uu___197_8011.iface);
        admitted_iface = (uu___197_8011.admitted_iface);
        expect_typ = (uu___197_8011.expect_typ);
        docs = (uu___197_8011.docs);
        remaining_iface_decls = (uu___197_8011.remaining_iface_decls);
        syntax_only = (uu___197_8011.syntax_only);
        ds_hooks = (uu___197_8011.ds_hooks)
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
        let uu____8066 =
          (unique false true env l) || (FStar_Options.interactive ()) in
        if uu____8066
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
          | FStar_Pervasives_Native.Some (se,uu____8093) ->
              let uu____8098 =
                FStar_Util.find_opt (FStar_Ident.lid_equals l)
                  (FStar_Syntax_Util.lids_of_sigelt se) in
              (match uu____8098 with
               | FStar_Pervasives_Native.Some l1 ->
                   FStar_All.pipe_left FStar_Range.string_of_range
                     (FStar_Ident.range_of_lid l1)
               | FStar_Pervasives_Native.None  -> "<unknown>")
          | FStar_Pervasives_Native.None  -> "<unknown>" in
        let uu____8106 =
          let uu____8107 =
            let uu____8112 =
              FStar_Util.format2
                "Duplicate top-level names [%s]; previously declared at %s"
                (FStar_Ident.text_of_lid l) r in
            (uu____8112, (FStar_Ident.range_of_lid l)) in
          FStar_Errors.Error uu____8107 in
        FStar_Exn.raise uu____8106 in
      let globals = FStar_Util.mk_ref env.scope_mods in
      let env1 =
        let uu____8121 =
          match s.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let uu____8130 -> (false, true)
          | FStar_Syntax_Syntax.Sig_bundle uu____8137 -> (true, true)
          | uu____8146 -> (false, false) in
        match uu____8121 with
        | (any_val,exclude_if) ->
            let lids = FStar_Syntax_Util.lids_of_sigelt s in
            let uu____8152 =
              FStar_Util.find_map lids
                (fun l  ->
                   let uu____8158 =
                     let uu____8159 = unique any_val exclude_if env l in
                     Prims.op_Negation uu____8159 in
                   if uu____8158
                   then FStar_Pervasives_Native.Some l
                   else FStar_Pervasives_Native.None) in
            (match uu____8152 with
             | FStar_Pervasives_Native.Some l when
                 let uu____8164 = FStar_Options.interactive () in
                 Prims.op_Negation uu____8164 -> err1 l
             | uu____8165 ->
                 (extract_record env globals s;
                  (let uu___198_8183 = env in
                   {
                     curmodule = (uu___198_8183.curmodule);
                     curmonad = (uu___198_8183.curmonad);
                     modules = (uu___198_8183.modules);
                     scope_mods = (uu___198_8183.scope_mods);
                     exported_ids = (uu___198_8183.exported_ids);
                     trans_exported_ids = (uu___198_8183.trans_exported_ids);
                     includes = (uu___198_8183.includes);
                     sigaccum = (s :: (env.sigaccum));
                     sigmap = (uu___198_8183.sigmap);
                     iface = (uu___198_8183.iface);
                     admitted_iface = (uu___198_8183.admitted_iface);
                     expect_typ = (uu___198_8183.expect_typ);
                     docs = (uu___198_8183.docs);
                     remaining_iface_decls =
                       (uu___198_8183.remaining_iface_decls);
                     syntax_only = (uu___198_8183.syntax_only);
                     ds_hooks = (uu___198_8183.ds_hooks)
                   }))) in
      let env2 =
        let uu___199_8185 = env1 in
        let uu____8186 = FStar_ST.op_Bang globals in
        {
          curmodule = (uu___199_8185.curmodule);
          curmonad = (uu___199_8185.curmonad);
          modules = (uu___199_8185.modules);
          scope_mods = uu____8186;
          exported_ids = (uu___199_8185.exported_ids);
          trans_exported_ids = (uu___199_8185.trans_exported_ids);
          includes = (uu___199_8185.includes);
          sigaccum = (uu___199_8185.sigaccum);
          sigmap = (uu___199_8185.sigmap);
          iface = (uu___199_8185.iface);
          admitted_iface = (uu___199_8185.admitted_iface);
          expect_typ = (uu___199_8185.expect_typ);
          docs = (uu___199_8185.docs);
          remaining_iface_decls = (uu___199_8185.remaining_iface_decls);
          syntax_only = (uu___199_8185.syntax_only);
          ds_hooks = (uu___199_8185.ds_hooks)
        } in
      let uu____8253 =
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_bundle (ses,uu____8279) ->
            let uu____8288 =
              FStar_List.map
                (fun se  -> ((FStar_Syntax_Util.lids_of_sigelt se), se)) ses in
            (env2, uu____8288)
        | uu____8315 -> (env2, [((FStar_Syntax_Util.lids_of_sigelt s), s)]) in
      match uu____8253 with
      | (env3,lss) ->
          (FStar_All.pipe_right lss
             (FStar_List.iter
                (fun uu____8374  ->
                   match uu____8374 with
                   | (lids,se) ->
                       FStar_All.pipe_right lids
                         (FStar_List.iter
                            (fun lid  ->
                               (let uu____8395 =
                                  let uu____8398 = FStar_ST.op_Bang globals in
                                  (Top_level_def (lid.FStar_Ident.ident)) ::
                                    uu____8398 in
                                FStar_ST.op_Colon_Equals globals uu____8395);
                               (match () with
                                | () ->
                                    let modul =
                                      let uu____8530 =
                                        FStar_Ident.lid_of_ids
                                          lid.FStar_Ident.ns in
                                      uu____8530.FStar_Ident.str in
                                    ((let uu____8532 =
                                        get_exported_id_set env3 modul in
                                      match uu____8532 with
                                      | FStar_Pervasives_Native.Some f ->
                                          let my_exported_ids =
                                            f Exported_id_term_type in
                                          let uu____8558 =
                                            let uu____8559 =
                                              FStar_ST.op_Bang
                                                my_exported_ids in
                                            FStar_Util.set_add
                                              (lid.FStar_Ident.ident).FStar_Ident.idText
                                              uu____8559 in
                                          FStar_ST.op_Colon_Equals
                                            my_exported_ids uu____8558
                                      | FStar_Pervasives_Native.None  -> ());
                                     (match () with
                                      | () ->
                                          FStar_Util.smap_add (sigmap env3)
                                            lid.FStar_Ident.str
                                            (se,
                                              (env3.iface &&
                                                 (Prims.op_Negation
                                                    env3.admitted_iface))))))))));
           (let env4 =
              let uu___200_8691 = env3 in
              let uu____8692 = FStar_ST.op_Bang globals in
              {
                curmodule = (uu___200_8691.curmodule);
                curmonad = (uu___200_8691.curmonad);
                modules = (uu___200_8691.modules);
                scope_mods = uu____8692;
                exported_ids = (uu___200_8691.exported_ids);
                trans_exported_ids = (uu___200_8691.trans_exported_ids);
                includes = (uu___200_8691.includes);
                sigaccum = (uu___200_8691.sigaccum);
                sigmap = (uu___200_8691.sigmap);
                iface = (uu___200_8691.iface);
                admitted_iface = (uu___200_8691.admitted_iface);
                expect_typ = (uu___200_8691.expect_typ);
                docs = (uu___200_8691.docs);
                remaining_iface_decls = (uu___200_8691.remaining_iface_decls);
                syntax_only = (uu___200_8691.syntax_only);
                ds_hooks = (uu___200_8691.ds_hooks)
              } in
            env4))
let push_namespace: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun ns  ->
      let uu____8767 =
        let uu____8772 = resolve_module_name env ns false in
        match uu____8772 with
        | FStar_Pervasives_Native.None  ->
            let modules = env.modules in
            let uu____8786 =
              FStar_All.pipe_right modules
                (FStar_Util.for_some
                   (fun uu____8800  ->
                      match uu____8800 with
                      | (m,uu____8806) ->
                          FStar_Util.starts_with
                            (Prims.strcat (FStar_Ident.text_of_lid m) ".")
                            (Prims.strcat (FStar_Ident.text_of_lid ns) "."))) in
            if uu____8786
            then (ns, Open_namespace)
            else
              (let uu____8812 =
                 let uu____8813 =
                   let uu____8818 =
                     FStar_Util.format1 "Namespace %s cannot be found"
                       (FStar_Ident.text_of_lid ns) in
                   (uu____8818, (FStar_Ident.range_of_lid ns)) in
                 FStar_Errors.Error uu____8813 in
               FStar_Exn.raise uu____8812)
        | FStar_Pervasives_Native.Some ns' ->
            (fail_if_curmodule env ns ns'; (ns', Open_module)) in
      match uu____8767 with
      | (ns',kd) ->
          ((env.ds_hooks).ds_push_open_hook env (ns', kd);
           push_scope_mod env (Open_module_or_namespace (ns', kd)))
let push_include: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun ns  ->
      let ns0 = ns in
      let uu____8837 = resolve_module_name env ns false in
      match uu____8837 with
      | FStar_Pervasives_Native.Some ns1 ->
          ((env.ds_hooks).ds_push_include_hook env ns1;
           fail_if_curmodule env ns0 ns1;
           (let env1 =
              push_scope_mod env
                (Open_module_or_namespace (ns1, Open_module)) in
            let curmod =
              let uu____8845 = current_module env1 in
              uu____8845.FStar_Ident.str in
            (let uu____8847 = FStar_Util.smap_try_find env1.includes curmod in
             match uu____8847 with
             | FStar_Pervasives_Native.None  -> ()
             | FStar_Pervasives_Native.Some incl ->
                 let uu____8871 =
                   let uu____8874 = FStar_ST.op_Bang incl in ns1 ::
                     uu____8874 in
                 FStar_ST.op_Colon_Equals incl uu____8871);
            (match () with
             | () ->
                 let uu____9005 =
                   get_trans_exported_id_set env1 ns1.FStar_Ident.str in
                 (match uu____9005 with
                  | FStar_Pervasives_Native.Some ns_trans_exports ->
                      ((let uu____9022 =
                          let uu____9039 = get_exported_id_set env1 curmod in
                          let uu____9046 =
                            get_trans_exported_id_set env1 curmod in
                          (uu____9039, uu____9046) in
                        match uu____9022 with
                        | (FStar_Pervasives_Native.Some
                           cur_exports,FStar_Pervasives_Native.Some
                           cur_trans_exports) ->
                            let update_exports k =
                              let ns_ex =
                                let uu____9100 = ns_trans_exports k in
                                FStar_ST.op_Bang uu____9100 in
                              let ex = cur_exports k in
                              (let uu____9355 =
                                 let uu____9356 = FStar_ST.op_Bang ex in
                                 FStar_Util.set_difference uu____9356 ns_ex in
                               FStar_ST.op_Colon_Equals ex uu____9355);
                              (match () with
                               | () ->
                                   let trans_ex = cur_trans_exports k in
                                   let uu____9490 =
                                     let uu____9491 =
                                       FStar_ST.op_Bang trans_ex in
                                     FStar_Util.set_union uu____9491 ns_ex in
                                   FStar_ST.op_Colon_Equals trans_ex
                                     uu____9490) in
                            FStar_List.iter update_exports
                              all_exported_id_kinds
                        | uu____9614 -> ());
                       (match () with | () -> env1))
                  | FStar_Pervasives_Native.None  ->
                      let uu____9635 =
                        let uu____9636 =
                          let uu____9641 =
                            FStar_Util.format1
                              "include: Module %s was not prepared"
                              ns1.FStar_Ident.str in
                          (uu____9641, (FStar_Ident.range_of_lid ns1)) in
                        FStar_Errors.Error uu____9636 in
                      FStar_Exn.raise uu____9635))))
      | uu____9642 ->
          let uu____9645 =
            let uu____9646 =
              let uu____9651 =
                FStar_Util.format1 "include: Module %s cannot be found"
                  ns.FStar_Ident.str in
              (uu____9651, (FStar_Ident.range_of_lid ns)) in
            FStar_Errors.Error uu____9646 in
          FStar_Exn.raise uu____9645
let push_module_abbrev: env -> FStar_Ident.ident -> FStar_Ident.lident -> env
  =
  fun env  ->
    fun x  ->
      fun l  ->
        let uu____9664 = module_is_defined env l in
        if uu____9664
        then
          (fail_if_curmodule env l l;
           (env.ds_hooks).ds_push_module_abbrev_hook env x l;
           push_scope_mod env (Module_abbrev (x, l)))
        else
          (let uu____9668 =
             let uu____9669 =
               let uu____9674 =
                 FStar_Util.format1 "Module %s cannot be found"
                   (FStar_Ident.text_of_lid l) in
               (uu____9674, (FStar_Ident.range_of_lid l)) in
             FStar_Errors.Error uu____9669 in
           FStar_Exn.raise uu____9668)
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
            ((let uu____9693 =
                FStar_Util.smap_try_find env.docs l.FStar_Ident.str in
              match uu____9693 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some old_doc ->
                  let uu____9697 =
                    let uu____9698 = FStar_Ident.string_of_lid l in
                    let uu____9699 = FStar_Parser_AST.string_of_fsdoc old_doc in
                    let uu____9700 = FStar_Parser_AST.string_of_fsdoc doc1 in
                    FStar_Util.format3
                      "Overwriting doc of %s; old doc was [%s]; new doc are [%s]"
                      uu____9698 uu____9699 uu____9700 in
                  FStar_Errors.warn (FStar_Ident.range_of_lid l) uu____9697);
             FStar_Util.smap_add env.docs l.FStar_Ident.str doc1;
             env)
let check_admits: env -> Prims.unit =
  fun env  ->
    FStar_All.pipe_right env.sigaccum
      (FStar_List.iter
         (fun se  ->
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t) ->
                let uu____9717 = try_lookup_lid env l in
                (match uu____9717 with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____9729 =
                         let uu____9730 = FStar_Options.interactive () in
                         Prims.op_Negation uu____9730 in
                       if uu____9729
                       then
                         let uu____9731 =
                           let uu____9732 =
                             FStar_Syntax_Print.lid_to_string l in
                           FStar_Util.format1
                             "Admitting %s without a definition" uu____9732 in
                         FStar_Errors.warn (FStar_Ident.range_of_lid l)
                           uu____9731
                       else ());
                      (let quals = FStar_Syntax_Syntax.Assumption ::
                         (se.FStar_Syntax_Syntax.sigquals) in
                       FStar_Util.smap_add (sigmap env) l.FStar_Ident.str
                         ((let uu___201_9742 = se in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (uu___201_9742.FStar_Syntax_Syntax.sigel);
                             FStar_Syntax_Syntax.sigrng =
                               (uu___201_9742.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals = quals;
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___201_9742.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___201_9742.FStar_Syntax_Syntax.sigattrs)
                           }), false)))
                 | FStar_Pervasives_Native.Some uu____9743 -> ())
            | uu____9752 -> ()))
let finish: env -> FStar_Syntax_Syntax.modul -> env =
  fun env  ->
    fun modul  ->
      FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations
        (FStar_List.iter
           (fun se  ->
              let quals = se.FStar_Syntax_Syntax.sigquals in
              match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_bundle (ses,uu____9771) ->
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
                                (lid,uu____9791,uu____9792,uu____9793,uu____9794,uu____9795)
                                ->
                                FStar_Util.smap_remove (sigmap env)
                                  lid.FStar_Ident.str
                            | uu____9804 -> ()))
                  else ()
              | FStar_Syntax_Syntax.Sig_declare_typ
                  (lid,uu____9807,uu____9808) ->
                  if FStar_List.contains FStar_Syntax_Syntax.Private quals
                  then
                    FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str
                  else ()
              | FStar_Syntax_Syntax.Sig_let ((uu____9814,lbs),uu____9816) ->
                  (if
                     (FStar_List.contains FStar_Syntax_Syntax.Private quals)
                       ||
                       (FStar_List.contains FStar_Syntax_Syntax.Abstract
                          quals)
                   then
                     FStar_All.pipe_right lbs
                       (FStar_List.iter
                          (fun lb  ->
                             let uu____9837 =
                               let uu____9838 =
                                 let uu____9839 =
                                   let uu____9842 =
                                     FStar_Util.right
                                       lb.FStar_Syntax_Syntax.lbname in
                                   uu____9842.FStar_Syntax_Syntax.fv_name in
                                 uu____9839.FStar_Syntax_Syntax.v in
                               uu____9838.FStar_Ident.str in
                             FStar_Util.smap_remove (sigmap env) uu____9837))
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
                               let uu____9856 =
                                 let uu____9859 =
                                   FStar_Util.right
                                     lb.FStar_Syntax_Syntax.lbname in
                                 uu____9859.FStar_Syntax_Syntax.fv_name in
                               uu____9856.FStar_Syntax_Syntax.v in
                             let quals1 = FStar_Syntax_Syntax.Assumption ::
                               quals in
                             let decl =
                               let uu___202_9864 = se in
                               {
                                 FStar_Syntax_Syntax.sigel =
                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                      (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                        (lb.FStar_Syntax_Syntax.lbtyp)));
                                 FStar_Syntax_Syntax.sigrng =
                                   (uu___202_9864.FStar_Syntax_Syntax.sigrng);
                                 FStar_Syntax_Syntax.sigquals = quals1;
                                 FStar_Syntax_Syntax.sigmeta =
                                   (uu___202_9864.FStar_Syntax_Syntax.sigmeta);
                                 FStar_Syntax_Syntax.sigattrs =
                                   (uu___202_9864.FStar_Syntax_Syntax.sigattrs)
                               } in
                             FStar_Util.smap_add (sigmap env)
                               lid.FStar_Ident.str (decl, false)))
                   else ())
              | uu____9874 -> ()));
      (let curmod =
         let uu____9876 = current_module env in uu____9876.FStar_Ident.str in
       (let uu____9878 =
          let uu____9895 = get_exported_id_set env curmod in
          let uu____9902 = get_trans_exported_id_set env curmod in
          (uu____9895, uu____9902) in
        match uu____9878 with
        | (FStar_Pervasives_Native.Some cur_ex,FStar_Pervasives_Native.Some
           cur_trans_ex) ->
            let update_exports eikind =
              let cur_ex_set =
                let uu____9956 = cur_ex eikind in FStar_ST.op_Bang uu____9956 in
              let cur_trans_ex_set_ref = cur_trans_ex eikind in
              let uu____10210 =
                let uu____10211 = FStar_ST.op_Bang cur_trans_ex_set_ref in
                FStar_Util.set_union cur_ex_set uu____10211 in
              FStar_ST.op_Colon_Equals cur_trans_ex_set_ref uu____10210 in
            FStar_List.iter update_exports all_exported_id_kinds
        | uu____10334 -> ());
       (match () with
        | () ->
            (filter_record_cache ();
             (match () with
              | () ->
                  let uu___203_10352 = env in
                  {
                    curmodule = FStar_Pervasives_Native.None;
                    curmonad = (uu___203_10352.curmonad);
                    modules = (((modul.FStar_Syntax_Syntax.name), modul) ::
                      (env.modules));
                    scope_mods = [];
                    exported_ids = (uu___203_10352.exported_ids);
                    trans_exported_ids = (uu___203_10352.trans_exported_ids);
                    includes = (uu___203_10352.includes);
                    sigaccum = [];
                    sigmap = (uu___203_10352.sigmap);
                    iface = (uu___203_10352.iface);
                    admitted_iface = (uu___203_10352.admitted_iface);
                    expect_typ = (uu___203_10352.expect_typ);
                    docs = (uu___203_10352.docs);
                    remaining_iface_decls =
                      (uu___203_10352.remaining_iface_decls);
                    syntax_only = (uu___203_10352.syntax_only);
                    ds_hooks = (uu___203_10352.ds_hooks)
                  }))))
let stack: env Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let push: env -> env =
  fun env  ->
    push_record_cache ();
    (let uu____10376 =
       let uu____10379 = FStar_ST.op_Bang stack in env :: uu____10379 in
     FStar_ST.op_Colon_Equals stack uu____10376);
    (let uu___204_10482 = env in
     let uu____10483 = FStar_Util.smap_copy (sigmap env) in
     let uu____10494 = FStar_Util.smap_copy env.docs in
     {
       curmodule = (uu___204_10482.curmodule);
       curmonad = (uu___204_10482.curmonad);
       modules = (uu___204_10482.modules);
       scope_mods = (uu___204_10482.scope_mods);
       exported_ids = (uu___204_10482.exported_ids);
       trans_exported_ids = (uu___204_10482.trans_exported_ids);
       includes = (uu___204_10482.includes);
       sigaccum = (uu___204_10482.sigaccum);
       sigmap = uu____10483;
       iface = (uu___204_10482.iface);
       admitted_iface = (uu___204_10482.admitted_iface);
       expect_typ = (uu___204_10482.expect_typ);
       docs = uu____10494;
       remaining_iface_decls = (uu___204_10482.remaining_iface_decls);
       syntax_only = (uu___204_10482.syntax_only);
       ds_hooks = (uu___204_10482.ds_hooks)
     })
let pop: Prims.unit -> env =
  fun uu____10500  ->
    let uu____10501 = FStar_ST.op_Bang stack in
    match uu____10501 with
    | env::tl1 ->
        (pop_record_cache (); FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____10610 -> failwith "Impossible: Too many pops"
let export_interface: FStar_Ident.lident -> env -> env =
  fun m  ->
    fun env  ->
      let sigelt_in_m se =
        match FStar_Syntax_Util.lids_of_sigelt se with
        | l::uu____10626 -> l.FStar_Ident.nsstr = m.FStar_Ident.str
        | uu____10629 -> false in
      let sm = sigmap env in
      let env1 = pop () in
      let keys = FStar_Util.smap_keys sm in
      let sm' = sigmap env1 in
      FStar_All.pipe_right keys
        (FStar_List.iter
           (fun k  ->
              let uu____10663 = FStar_Util.smap_try_find sm' k in
              match uu____10663 with
              | FStar_Pervasives_Native.Some (se,true ) when sigelt_in_m se
                  ->
                  (FStar_Util.smap_remove sm' k;
                   (let se1 =
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t) ->
                          let uu___205_10688 = se in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (uu___205_10688.FStar_Syntax_Syntax.sigel);
                            FStar_Syntax_Syntax.sigrng =
                              (uu___205_10688.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (FStar_Syntax_Syntax.Assumption ::
                              (se.FStar_Syntax_Syntax.sigquals));
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___205_10688.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___205_10688.FStar_Syntax_Syntax.sigattrs)
                          }
                      | uu____10689 -> se in
                    FStar_Util.smap_add sm' k (se1, false)))
              | uu____10694 -> ()));
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
      let uu____10779 =
        let uu____10782 = e Exported_id_term_type in
        FStar_ST.op_Bang uu____10782 in
      FStar_Util.set_elements uu____10779 in
    let fields =
      let uu____11029 =
        let uu____11032 = e Exported_id_field in FStar_ST.op_Bang uu____11032 in
      FStar_Util.set_elements uu____11029 in
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
          let uu____11309 =
            FStar_Util.as_set e1.exported_id_terms FStar_Util.compare in
          FStar_Util.mk_ref uu____11309 in
        let fields =
          let uu____11319 =
            FStar_Util.as_set e1.exported_id_fields FStar_Util.compare in
          FStar_Util.mk_ref uu____11319 in
        (fun uu___183_11324  ->
           match uu___183_11324 with
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
  'Auu____11437 .
    'Auu____11437 Prims.list FStar_Pervasives_Native.option ->
      'Auu____11437 Prims.list FStar_ST.ref
  =
  fun uu___184_11449  ->
    match uu___184_11449 with
    | FStar_Pervasives_Native.None  -> FStar_Util.mk_ref []
    | FStar_Pervasives_Native.Some l -> FStar_Util.mk_ref l
let inclusion_info: env -> FStar_Ident.lident -> module_inclusion_info =
  fun env  ->
    fun l  ->
      let mname = FStar_Ident.string_of_lid l in
      let as_ids_opt m =
        let uu____11484 = FStar_Util.smap_try_find m mname in
        FStar_Util.map_opt uu____11484 as_exported_ids in
      let uu____11487 = as_ids_opt env.exported_ids in
      let uu____11490 = as_ids_opt env.trans_exported_ids in
      let uu____11493 =
        let uu____11498 = FStar_Util.smap_try_find env.includes mname in
        FStar_Util.map_opt uu____11498 (fun r  -> FStar_ST.op_Bang r) in
      {
        mii_exported_ids = uu____11487;
        mii_trans_exported_ids = uu____11490;
        mii_includes = uu____11493
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
                let convert_kind uu___185_11638 =
                  match uu___185_11638 with
                  | FStar_Parser_Dep.Open_namespace  -> Open_namespace
                  | FStar_Parser_Dep.Open_module  -> Open_module in
                FStar_List.map
                  (fun uu____11650  ->
                     match uu____11650 with
                     | (lid,kind) -> (lid, (convert_kind kind))) auto_open in
              let namespace_of_module =
                if
                  (FStar_List.length mname.FStar_Ident.ns) >
                    (Prims.parse_int "0")
                then
                  let uu____11674 =
                    let uu____11679 =
                      FStar_Ident.lid_of_ids mname.FStar_Ident.ns in
                    (uu____11679, Open_namespace) in
                  [uu____11674]
                else [] in
              let auto_open2 =
                FStar_List.append namespace_of_module
                  (FStar_List.rev auto_open1) in
              (let uu____11709 = as_exported_id_set mii.mii_exported_ids in
               FStar_Util.smap_add env1.exported_ids mname.FStar_Ident.str
                 uu____11709);
              (match () with
               | () ->
                   ((let uu____11725 =
                       as_exported_id_set mii.mii_trans_exported_ids in
                     FStar_Util.smap_add env1.trans_exported_ids
                       mname.FStar_Ident.str uu____11725);
                    (match () with
                     | () ->
                         ((let uu____11741 = as_includes mii.mii_includes in
                           FStar_Util.smap_add env1.includes
                             mname.FStar_Ident.str uu____11741);
                          (match () with
                           | () ->
                               let env' =
                                 let uu___206_11765 = env1 in
                                 let uu____11766 =
                                   FStar_List.map
                                     (fun x  -> Open_module_or_namespace x)
                                     auto_open2 in
                                 {
                                   curmodule =
                                     (FStar_Pervasives_Native.Some mname);
                                   curmonad = (uu___206_11765.curmonad);
                                   modules = (uu___206_11765.modules);
                                   scope_mods = uu____11766;
                                   exported_ids =
                                     (uu___206_11765.exported_ids);
                                   trans_exported_ids =
                                     (uu___206_11765.trans_exported_ids);
                                   includes = (uu___206_11765.includes);
                                   sigaccum = (uu___206_11765.sigaccum);
                                   sigmap = (env1.sigmap);
                                   iface = intf;
                                   admitted_iface = admitted;
                                   expect_typ = (uu___206_11765.expect_typ);
                                   docs = (uu___206_11765.docs);
                                   remaining_iface_decls =
                                     (uu___206_11765.remaining_iface_decls);
                                   syntax_only = (uu___206_11765.syntax_only);
                                   ds_hooks = (uu___206_11765.ds_hooks)
                                 } in
                               (FStar_List.iter
                                  (fun op  ->
                                     (env1.ds_hooks).ds_push_open_hook env'
                                       op) (FStar_List.rev auto_open2);
                                env')))))) in
            let uu____11778 =
              FStar_All.pipe_right env.modules
                (FStar_Util.find_opt
                   (fun uu____11804  ->
                      match uu____11804 with
                      | (l,uu____11810) -> FStar_Ident.lid_equals l mname)) in
            match uu____11778 with
            | FStar_Pervasives_Native.None  ->
                let uu____11819 = prep env in (uu____11819, false)
            | FStar_Pervasives_Native.Some (uu____11820,m) ->
                ((let uu____11827 =
                    (let uu____11830 = FStar_Options.interactive () in
                     Prims.op_Negation uu____11830) &&
                      ((Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)
                         || intf) in
                  if uu____11827
                  then
                    let uu____11831 =
                      let uu____11832 =
                        let uu____11837 =
                          FStar_Util.format1
                            "Duplicate module or interface name: %s"
                            mname.FStar_Ident.str in
                        (uu____11837, (FStar_Ident.range_of_lid mname)) in
                      FStar_Errors.Error uu____11832 in
                    FStar_Exn.raise uu____11831
                  else ());
                 (let uu____11839 =
                    let uu____11840 = push env in prep uu____11840 in
                  (uu____11839, true)))
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
          let uu___207_11850 = env in
          {
            curmodule = (uu___207_11850.curmodule);
            curmonad = (FStar_Pervasives_Native.Some mname);
            modules = (uu___207_11850.modules);
            scope_mods = (uu___207_11850.scope_mods);
            exported_ids = (uu___207_11850.exported_ids);
            trans_exported_ids = (uu___207_11850.trans_exported_ids);
            includes = (uu___207_11850.includes);
            sigaccum = (uu___207_11850.sigaccum);
            sigmap = (uu___207_11850.sigmap);
            iface = (uu___207_11850.iface);
            admitted_iface = (uu___207_11850.admitted_iface);
            expect_typ = (uu___207_11850.expect_typ);
            docs = (uu___207_11850.docs);
            remaining_iface_decls = (uu___207_11850.remaining_iface_decls);
            syntax_only = (uu___207_11850.syntax_only);
            ds_hooks = (uu___207_11850.ds_hooks)
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
        let uu____11881 = lookup lid in
        match uu____11881 with
        | FStar_Pervasives_Native.None  ->
            let opened_modules =
              FStar_List.map
                (fun uu____11894  ->
                   match uu____11894 with
                   | (lid1,uu____11900) -> FStar_Ident.text_of_lid lid1)
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
                   let uu____11905 =
                     FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
                   FStar_Ident.set_lid_range uu____11905
                     (FStar_Ident.range_of_lid lid) in
                 let uu____11906 = resolve_module_name env modul true in
                 match uu____11906 with
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
      let uu____11940 = lookup id in
      match uu____11940 with
      | FStar_Pervasives_Native.None  ->
          FStar_Exn.raise
            (FStar_Errors.Error
               ((Prims.strcat "Identifier not found ["
                   (Prims.strcat id.FStar_Ident.idText "]")),
                 (id.FStar_Ident.idRange)))
      | FStar_Pervasives_Native.Some r -> r