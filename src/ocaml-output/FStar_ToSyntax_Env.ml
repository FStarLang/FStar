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
type 'a withenv = env -> ('a,env) FStar_Pervasives_Native.tuple2[@@deriving
                                                                  show]
let default_ds_hooks: dsenv_hooks =
  {
    ds_push_open_hook = (fun uu____1571  -> fun uu____1572  -> ());
    ds_push_include_hook = (fun uu____1575  -> fun uu____1576  -> ());
    ds_push_module_abbrev_hook =
      (fun uu____1580  -> fun uu____1581  -> fun uu____1582  -> ())
  }
type foundname =
  | Term_name of (FStar_Syntax_Syntax.typ,Prims.bool)
  FStar_Pervasives_Native.tuple2
  | Eff_name of (FStar_Syntax_Syntax.sigelt,FStar_Ident.lident)
  FStar_Pervasives_Native.tuple2[@@deriving show]
let uu___is_Term_name: foundname -> Prims.bool =
  fun projectee  ->
    match projectee with | Term_name _0 -> true | uu____1608 -> false
let __proj__Term_name__item___0:
  foundname ->
    (FStar_Syntax_Syntax.typ,Prims.bool) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Term_name _0 -> _0
let uu___is_Eff_name: foundname -> Prims.bool =
  fun projectee  ->
    match projectee with | Eff_name _0 -> true | uu____1638 -> false
let __proj__Eff_name__item___0:
  foundname ->
    (FStar_Syntax_Syntax.sigelt,FStar_Ident.lident)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Eff_name _0 -> _0
let set_iface: env -> Prims.bool -> env =
  fun env  ->
    fun b  ->
      let uu___194_1667 = env in
      {
        curmodule = (uu___194_1667.curmodule);
        curmonad = (uu___194_1667.curmonad);
        modules = (uu___194_1667.modules);
        scope_mods = (uu___194_1667.scope_mods);
        exported_ids = (uu___194_1667.exported_ids);
        trans_exported_ids = (uu___194_1667.trans_exported_ids);
        includes = (uu___194_1667.includes);
        sigaccum = (uu___194_1667.sigaccum);
        sigmap = (uu___194_1667.sigmap);
        iface = b;
        admitted_iface = (uu___194_1667.admitted_iface);
        expect_typ = (uu___194_1667.expect_typ);
        docs = (uu___194_1667.docs);
        remaining_iface_decls = (uu___194_1667.remaining_iface_decls);
        syntax_only = (uu___194_1667.syntax_only);
        ds_hooks = (uu___194_1667.ds_hooks)
      }
let iface: env -> Prims.bool = fun e  -> e.iface
let set_admitted_iface: env -> Prims.bool -> env =
  fun e  ->
    fun b  ->
      let uu___195_1680 = e in
      {
        curmodule = (uu___195_1680.curmodule);
        curmonad = (uu___195_1680.curmonad);
        modules = (uu___195_1680.modules);
        scope_mods = (uu___195_1680.scope_mods);
        exported_ids = (uu___195_1680.exported_ids);
        trans_exported_ids = (uu___195_1680.trans_exported_ids);
        includes = (uu___195_1680.includes);
        sigaccum = (uu___195_1680.sigaccum);
        sigmap = (uu___195_1680.sigmap);
        iface = (uu___195_1680.iface);
        admitted_iface = b;
        expect_typ = (uu___195_1680.expect_typ);
        docs = (uu___195_1680.docs);
        remaining_iface_decls = (uu___195_1680.remaining_iface_decls);
        syntax_only = (uu___195_1680.syntax_only);
        ds_hooks = (uu___195_1680.ds_hooks)
      }
let admitted_iface: env -> Prims.bool = fun e  -> e.admitted_iface
let set_expect_typ: env -> Prims.bool -> env =
  fun e  ->
    fun b  ->
      let uu___196_1693 = e in
      {
        curmodule = (uu___196_1693.curmodule);
        curmonad = (uu___196_1693.curmonad);
        modules = (uu___196_1693.modules);
        scope_mods = (uu___196_1693.scope_mods);
        exported_ids = (uu___196_1693.exported_ids);
        trans_exported_ids = (uu___196_1693.trans_exported_ids);
        includes = (uu___196_1693.includes);
        sigaccum = (uu___196_1693.sigaccum);
        sigmap = (uu___196_1693.sigmap);
        iface = (uu___196_1693.iface);
        admitted_iface = (uu___196_1693.admitted_iface);
        expect_typ = b;
        docs = (uu___196_1693.docs);
        remaining_iface_decls = (uu___196_1693.remaining_iface_decls);
        syntax_only = (uu___196_1693.syntax_only);
        ds_hooks = (uu___196_1693.ds_hooks)
      }
let expect_typ: env -> Prims.bool = fun e  -> e.expect_typ
let all_exported_id_kinds: exported_id_kind Prims.list =
  [Exported_id_field; Exported_id_term_type]
let transitive_exported_ids:
  env -> FStar_Ident.lident -> Prims.string Prims.list =
  fun env  ->
    fun lid  ->
      let module_name = FStar_Ident.string_of_lid lid in
      let uu____1711 =
        FStar_Util.smap_try_find env.trans_exported_ids module_name in
      match uu____1711 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some exported_id_set ->
          let uu____1717 =
            let uu____1718 = exported_id_set Exported_id_term_type in
            FStar_ST.op_Bang uu____1718 in
          FStar_All.pipe_right uu____1717 FStar_Util.set_elements
let open_modules:
  env ->
    (FStar_Ident.lident,FStar_Syntax_Syntax.modul)
      FStar_Pervasives_Native.tuple2 Prims.list
  = fun e  -> e.modules
let open_modules_and_namespaces: env -> FStar_Ident.lident Prims.list =
  fun env  ->
    FStar_List.filter_map
      (fun uu___162_1983  ->
         match uu___162_1983 with
         | Open_module_or_namespace (lid,_info) ->
             FStar_Pervasives_Native.Some lid
         | uu____1988 -> FStar_Pervasives_Native.None) env.scope_mods
let set_current_module: env -> FStar_Ident.lident -> env =
  fun e  ->
    fun l  ->
      let uu___197_1997 = e in
      {
        curmodule = (FStar_Pervasives_Native.Some l);
        curmonad = (uu___197_1997.curmonad);
        modules = (uu___197_1997.modules);
        scope_mods = (uu___197_1997.scope_mods);
        exported_ids = (uu___197_1997.exported_ids);
        trans_exported_ids = (uu___197_1997.trans_exported_ids);
        includes = (uu___197_1997.includes);
        sigaccum = (uu___197_1997.sigaccum);
        sigmap = (uu___197_1997.sigmap);
        iface = (uu___197_1997.iface);
        admitted_iface = (uu___197_1997.admitted_iface);
        expect_typ = (uu___197_1997.expect_typ);
        docs = (uu___197_1997.docs);
        remaining_iface_decls = (uu___197_1997.remaining_iface_decls);
        syntax_only = (uu___197_1997.syntax_only);
        ds_hooks = (uu___197_1997.ds_hooks)
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
      let uu____2015 =
        FStar_All.pipe_right env.remaining_iface_decls
          (FStar_List.tryFind
             (fun uu____2049  ->
                match uu____2049 with
                | (m,uu____2057) -> FStar_Ident.lid_equals l m)) in
      match uu____2015 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (uu____2074,decls) ->
          FStar_Pervasives_Native.Some decls
let set_iface_decls:
  env -> FStar_Ident.lident -> FStar_Parser_AST.decl Prims.list -> env =
  fun env  ->
    fun l  ->
      fun ds  ->
        let uu____2104 =
          FStar_List.partition
            (fun uu____2134  ->
               match uu____2134 with
               | (m,uu____2142) -> FStar_Ident.lid_equals l m)
            env.remaining_iface_decls in
        match uu____2104 with
        | (uu____2147,rest) ->
            let uu___198_2181 = env in
            {
              curmodule = (uu___198_2181.curmodule);
              curmonad = (uu___198_2181.curmonad);
              modules = (uu___198_2181.modules);
              scope_mods = (uu___198_2181.scope_mods);
              exported_ids = (uu___198_2181.exported_ids);
              trans_exported_ids = (uu___198_2181.trans_exported_ids);
              includes = (uu___198_2181.includes);
              sigaccum = (uu___198_2181.sigaccum);
              sigmap = (uu___198_2181.sigmap);
              iface = (uu___198_2181.iface);
              admitted_iface = (uu___198_2181.admitted_iface);
              expect_typ = (uu___198_2181.expect_typ);
              docs = (uu___198_2181.docs);
              remaining_iface_decls = ((l, ds) :: rest);
              syntax_only = (uu___198_2181.syntax_only);
              ds_hooks = (uu___198_2181.ds_hooks)
            }
let qual: FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident =
  FStar_Syntax_Util.qual_id
let qualify: env -> FStar_Ident.ident -> FStar_Ident.lident =
  fun env  ->
    fun id  ->
      match env.curmonad with
      | FStar_Pervasives_Native.None  ->
          let uu____2204 = current_module env in qual uu____2204 id
      | FStar_Pervasives_Native.Some monad ->
          let uu____2206 =
            let uu____2207 = current_module env in qual uu____2207 monad in
          FStar_Syntax_Util.mk_field_projector_name_from_ident uu____2206 id
let syntax_only: env -> Prims.bool = fun env  -> env.syntax_only
let set_syntax_only: env -> Prims.bool -> env =
  fun env  ->
    fun b  ->
      let uu___199_2220 = env in
      {
        curmodule = (uu___199_2220.curmodule);
        curmonad = (uu___199_2220.curmonad);
        modules = (uu___199_2220.modules);
        scope_mods = (uu___199_2220.scope_mods);
        exported_ids = (uu___199_2220.exported_ids);
        trans_exported_ids = (uu___199_2220.trans_exported_ids);
        includes = (uu___199_2220.includes);
        sigaccum = (uu___199_2220.sigaccum);
        sigmap = (uu___199_2220.sigmap);
        iface = (uu___199_2220.iface);
        admitted_iface = (uu___199_2220.admitted_iface);
        expect_typ = (uu___199_2220.expect_typ);
        docs = (uu___199_2220.docs);
        remaining_iface_decls = (uu___199_2220.remaining_iface_decls);
        syntax_only = b;
        ds_hooks = (uu___199_2220.ds_hooks)
      }
let ds_hooks: env -> dsenv_hooks = fun env  -> env.ds_hooks
let set_ds_hooks: env -> dsenv_hooks -> env =
  fun env  ->
    fun hooks  ->
      let uu___200_2233 = env in
      {
        curmodule = (uu___200_2233.curmodule);
        curmonad = (uu___200_2233.curmonad);
        modules = (uu___200_2233.modules);
        scope_mods = (uu___200_2233.scope_mods);
        exported_ids = (uu___200_2233.exported_ids);
        trans_exported_ids = (uu___200_2233.trans_exported_ids);
        includes = (uu___200_2233.includes);
        sigaccum = (uu___200_2233.sigaccum);
        sigmap = (uu___200_2233.sigmap);
        iface = (uu___200_2233.iface);
        admitted_iface = (uu___200_2233.admitted_iface);
        expect_typ = (uu___200_2233.expect_typ);
        docs = (uu___200_2233.docs);
        remaining_iface_decls = (uu___200_2233.remaining_iface_decls);
        syntax_only = (uu___200_2233.syntax_only);
        ds_hooks = hooks
      }
let new_sigmap: 'Auu____2238 . Prims.unit -> 'Auu____2238 FStar_Util.smap =
  fun uu____2244  -> FStar_Util.smap_create (Prims.parse_int "100")
let empty_env: Prims.unit -> env =
  fun uu____2248  ->
    let uu____2249 = new_sigmap () in
    let uu____2252 = new_sigmap () in
    let uu____2255 = new_sigmap () in
    let uu____2266 = new_sigmap () in
    let uu____2277 = new_sigmap () in
    {
      curmodule = FStar_Pervasives_Native.None;
      curmonad = FStar_Pervasives_Native.None;
      modules = [];
      scope_mods = [];
      exported_ids = uu____2249;
      trans_exported_ids = uu____2252;
      includes = uu____2255;
      sigaccum = [];
      sigmap = uu____2266;
      iface = false;
      admitted_iface = false;
      expect_typ = false;
      docs = uu____2277;
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
      (fun uu____2311  ->
         match uu____2311 with
         | (m,uu____2317) ->
             FStar_Ident.lid_equals m FStar_Parser_Const.all_lid) env.modules
let set_bv_range:
  FStar_Syntax_Syntax.bv -> FStar_Range.range -> FStar_Syntax_Syntax.bv =
  fun bv  ->
    fun r  ->
      let id =
        let uu___201_2327 = bv.FStar_Syntax_Syntax.ppname in
        {
          FStar_Ident.idText = (uu___201_2327.FStar_Ident.idText);
          FStar_Ident.idRange = r
        } in
      let uu___202_2328 = bv in
      {
        FStar_Syntax_Syntax.ppname = id;
        FStar_Syntax_Syntax.index = (uu___202_2328.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = (uu___202_2328.FStar_Syntax_Syntax.sort)
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
        (fun uu____2418  ->
           match uu____2418 with
           | (x,y,dd,dq) ->
               if id.FStar_Ident.idText = x
               then
                 let uu____2441 =
                   let uu____2442 =
                     FStar_Ident.lid_of_path ["Prims"; y]
                       id.FStar_Ident.idRange in
                   FStar_Syntax_Syntax.fvar uu____2442 dd dq in
                 FStar_Pervasives_Native.Some uu____2441
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
    match projectee with | Cont_ok _0 -> true | uu____2487 -> false
let __proj__Cont_ok__item___0: 'a . 'a cont_t -> 'a =
  fun projectee  -> match projectee with | Cont_ok _0 -> _0
let uu___is_Cont_fail: 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_fail  -> true | uu____2520 -> false
let uu___is_Cont_ignore: 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_ignore  -> true | uu____2536 -> false
let option_of_cont:
  'a .
    (Prims.unit -> 'a FStar_Pervasives_Native.option) ->
      'a cont_t -> 'a FStar_Pervasives_Native.option
  =
  fun k_ignore  ->
    fun uu___163_2562  ->
      match uu___163_2562 with
      | Cont_ok a -> FStar_Pervasives_Native.Some a
      | Cont_fail  -> FStar_Pervasives_Native.None
      | Cont_ignore  -> k_ignore ()
let find_in_record:
  'Auu____2580 .
    FStar_Ident.ident Prims.list ->
      FStar_Ident.ident ->
        record_or_dc ->
          (record_or_dc -> 'Auu____2580 cont_t) -> 'Auu____2580 cont_t
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
                (fun uu____2626  ->
                   match uu____2626 with
                   | (f,uu____2634) ->
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
  fun uu___164_2685  ->
    match uu___164_2685 with
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
              let rec aux uu___165_2748 =
                match uu___165_2748 with
                | [] -> find_in_module_default
                | modul::q ->
                    let mname = modul.FStar_Ident.str in
                    let not_shadowed =
                      let uu____2759 = get_exported_id_set env mname in
                      match uu____2759 with
                      | FStar_Pervasives_Native.None  -> true
                      | FStar_Pervasives_Native.Some mex ->
                          let mexports =
                            let uu____2780 = mex eikind in
                            FStar_ST.op_Bang uu____2780 in
                          FStar_Util.set_mem idstr mexports in
                    let mincludes =
                      let uu____3027 =
                        FStar_Util.smap_try_find env.includes mname in
                      match uu____3027 with
                      | FStar_Pervasives_Native.None  -> []
                      | FStar_Pervasives_Native.Some minc ->
                          FStar_ST.op_Bang minc in
                    let look_into =
                      if not_shadowed
                      then
                        let uu____3122 = qual modul id in
                        find_in_module uu____3122
                      else Cont_ignore in
                    (match look_into with
                     | Cont_ignore  -> aux (FStar_List.append mincludes q)
                     | uu____3126 -> look_into) in
              aux [ns]
let is_exported_id_field: exported_id_kind -> Prims.bool =
  fun uu___166_3132  ->
    match uu___166_3132 with
    | Exported_id_field  -> true
    | uu____3133 -> false
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
                  let check_local_binding_id uu___167_3244 =
                    match uu___167_3244 with
                    | (id',uu____3246,uu____3247) ->
                        id'.FStar_Ident.idText = id.FStar_Ident.idText in
                  let check_rec_binding_id uu___168_3251 =
                    match uu___168_3251 with
                    | (id',uu____3253,uu____3254) ->
                        id'.FStar_Ident.idText = id.FStar_Ident.idText in
                  let curmod_ns =
                    let uu____3258 = current_module env in
                    FStar_Ident.ids_of_lid uu____3258 in
                  let proc uu___169_3264 =
                    match uu___169_3264 with
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
                        let uu____3272 = FStar_Ident.lid_of_ids curmod_ns in
                        find_in_module_with_includes Exported_id_field
                          (fun lid  ->
                             let id1 = lid.FStar_Ident.ident in
                             find_in_record lid.FStar_Ident.ns id1 r k_record)
                          Cont_ignore env uu____3272 id
                    | uu____3277 -> Cont_ignore in
                  let rec aux uu___170_3285 =
                    match uu___170_3285 with
                    | a::q ->
                        let uu____3294 = proc a in
                        option_of_cont (fun uu____3298  -> aux q) uu____3294
                    | [] ->
                        let uu____3299 = lookup_default_id Cont_fail id in
                        option_of_cont
                          (fun uu____3303  -> FStar_Pervasives_Native.None)
                          uu____3299 in
                  aux env.scope_mods
let found_local_binding:
  'Auu____3312 'Auu____3313 .
    FStar_Range.range ->
      ('Auu____3313,FStar_Syntax_Syntax.bv,'Auu____3312)
        FStar_Pervasives_Native.tuple3 ->
        (FStar_Syntax_Syntax.term,'Auu____3312)
          FStar_Pervasives_Native.tuple2
  =
  fun r  ->
    fun uu____3331  ->
      match uu____3331 with
      | (id',x,mut) -> let uu____3341 = bv_to_name x r in (uu____3341, mut)
let find_in_module:
  'Auu____3352 .
    env ->
      FStar_Ident.lident ->
        (FStar_Ident.lident ->
           (FStar_Syntax_Syntax.sigelt,Prims.bool)
             FStar_Pervasives_Native.tuple2 -> 'Auu____3352)
          -> 'Auu____3352 -> 'Auu____3352
  =
  fun env  ->
    fun lid  ->
      fun k_global_def  ->
        fun k_not_found  ->
          let uu____3387 =
            FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str in
          match uu____3387 with
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
      let uu____3425 = unmangleOpName id in
      match uu____3425 with
      | FStar_Pervasives_Native.Some f -> FStar_Pervasives_Native.Some f
      | uu____3451 ->
          try_lookup_id'' env id Exported_id_term_type
            (fun r  ->
               let uu____3465 = found_local_binding id.FStar_Ident.idRange r in
               Cont_ok uu____3465) (fun uu____3475  -> Cont_fail)
            (fun uu____3481  -> Cont_ignore)
            (fun i  ->
               find_in_module env i
                 (fun uu____3496  -> fun uu____3497  -> Cont_fail)
                 Cont_ignore)
            (fun uu____3512  -> fun uu____3513  -> Cont_fail)
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
            | FStar_Pervasives_Native.Some uu____3588 ->
                let lid = qualify env id in
                let uu____3590 =
                  FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str in
                (match uu____3590 with
                 | FStar_Pervasives_Native.Some r ->
                     let uu____3614 = k_global_def lid r in
                     FStar_Pervasives_Native.Some uu____3614
                 | FStar_Pervasives_Native.None  ->
                     FStar_Pervasives_Native.None)
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None in
          match find_in_monad with
          | FStar_Pervasives_Native.Some v1 -> v1
          | FStar_Pervasives_Native.None  ->
              let lid =
                let uu____3637 = current_module env in qual uu____3637 id in
              find_in_module env lid k_global_def k_not_found
let module_is_defined: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      (match env.curmodule with
       | FStar_Pervasives_Native.None  -> false
       | FStar_Pervasives_Native.Some m ->
           let uu____3649 = current_module env in
           FStar_Ident.lid_equals lid uu____3649)
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
        let rec aux uu___171_3684 =
          match uu___171_3684 with
          | [] ->
              let uu____3689 = module_is_defined env lid in
              if uu____3689
              then FStar_Pervasives_Native.Some lid
              else FStar_Pervasives_Native.None
          | (Open_module_or_namespace (ns,Open_namespace ))::q when honor_ns
              ->
              let new_lid =
                let uu____3698 =
                  let uu____3701 = FStar_Ident.path_of_lid ns in
                  let uu____3704 = FStar_Ident.path_of_lid lid in
                  FStar_List.append uu____3701 uu____3704 in
                FStar_Ident.lid_of_path uu____3698
                  (FStar_Ident.range_of_lid lid) in
              let uu____3707 = module_is_defined env new_lid in
              if uu____3707
              then FStar_Pervasives_Native.Some new_lid
              else aux q
          | (Module_abbrev (name,modul))::uu____3713 when
              (nslen = (Prims.parse_int "0")) &&
                (name.FStar_Ident.idText =
                   (lid.FStar_Ident.ident).FStar_Ident.idText)
              -> FStar_Pervasives_Native.Some modul
          | uu____3720::q -> aux q in
        aux env.scope_mods
let fail_if_curmodule:
  env -> FStar_Ident.lident -> FStar_Ident.lident -> Prims.unit =
  fun env  ->
    fun ns_original  ->
      fun ns_resolved  ->
        let uu____3736 =
          let uu____3737 = current_module env in
          FStar_Ident.lid_equals ns_resolved uu____3737 in
        if uu____3736
        then
          (if FStar_Ident.lid_equals ns_resolved FStar_Parser_Const.prims_lid
           then ()
           else
             (let uu____3739 =
                let uu____3740 =
                  let uu____3745 =
                    FStar_Util.format1
                      "Reference %s to current module is forbidden (see GitHub issue #451)"
                      ns_original.FStar_Ident.str in
                  (uu____3745, (FStar_Ident.range_of_lid ns_original)) in
                FStar_Errors.Error uu____3740 in
              FStar_Exn.raise uu____3739))
        else ()
let fail_if_qualified_by_curmodule: env -> FStar_Ident.lident -> Prims.unit =
  fun env  ->
    fun lid  ->
      match lid.FStar_Ident.ns with
      | [] -> ()
      | uu____3755 ->
          let modul_orig = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          let uu____3759 = resolve_module_name env modul_orig true in
          (match uu____3759 with
           | FStar_Pervasives_Native.Some modul_res ->
               fail_if_curmodule env modul_orig modul_res
           | uu____3763 -> ())
let namespace_is_open: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      FStar_List.existsb
        (fun uu___172_3776  ->
           match uu___172_3776 with
           | Open_module_or_namespace (ns,Open_namespace ) ->
               FStar_Ident.lid_equals lid ns
           | uu____3778 -> false) env.scope_mods
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
                 let uu____3870 = aux rev_ns_prefix ns_last_id in
                 FStar_All.pipe_right uu____3870
                   (FStar_Util.map_option
                      (fun uu____3920  ->
                         match uu____3920 with
                         | (stripped_ids,rev_kept_ids) ->
                             (stripped_ids, (id :: rev_kept_ids))))) in
        let uu____3951 =
          is_full_path &&
            (let uu____3953 = FStar_Ident.lid_of_ids ids in
             module_is_defined env uu____3953) in
        if uu____3951
        then (ids, [])
        else
          (match FStar_List.rev ids with
           | [] -> ([], [])
           | ns_last_id::ns_rev_prefix ->
               let uu____3983 = aux ns_rev_prefix ns_last_id in
               (match uu____3983 with
                | FStar_Pervasives_Native.None  -> ([], ids)
                | FStar_Pervasives_Native.Some (stripped_ids,rev_kept_ids) ->
                    (stripped_ids, (FStar_List.rev rev_kept_ids))))
let shorten_lid: env -> FStar_Ident.lid -> FStar_Ident.lid =
  fun env  ->
    fun lid  ->
      let uu____4044 = shorten_module_path env lid.FStar_Ident.ns true in
      match uu____4044 with
      | (uu____4053,short) ->
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
                  | uu____4170::uu____4171 ->
                      let uu____4174 =
                        let uu____4177 =
                          let uu____4178 =
                            FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
                          FStar_Ident.set_lid_range uu____4178
                            (FStar_Ident.range_of_lid lid) in
                        resolve_module_name env uu____4177 true in
                      (match uu____4174 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some modul ->
                           let uu____4182 =
                             find_in_module_with_includes eikind f_module
                               Cont_fail env modul lid.FStar_Ident.ident in
                           option_of_cont
                             (fun uu____4186  -> FStar_Pervasives_Native.None)
                             uu____4182)
                  | [] ->
                      try_lookup_id'' env lid.FStar_Ident.ident eikind
                        k_local_binding k_rec_binding k_record f_module
                        l_default
let cont_of_option:
  'a . 'a cont_t -> 'a FStar_Pervasives_Native.option -> 'a cont_t =
  fun k_none  ->
    fun uu___173_4207  ->
      match uu___173_4207 with
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
              let uu____4312 = k_global_def lid1 def in
              cont_of_option k uu____4312 in
            let f_module lid' =
              let k = Cont_ignore in
              find_in_module env lid' (k_global_def' k) k in
            let l_default k i = lookup_default_id env i (k_global_def' k) k in
            resolve_in_open_namespaces'' env lid Exported_id_term_type
              (fun l  ->
                 let uu____4342 = k_local_binding l in
                 cont_of_option Cont_fail uu____4342)
              (fun r  ->
                 let uu____4348 = k_rec_binding r in
                 cont_of_option Cont_fail uu____4348)
              (fun uu____4352  -> Cont_ignore) f_module l_default
let fv_qual_of_se:
  FStar_Syntax_Syntax.sigelt ->
    FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____4361,uu____4362,uu____4363,l,uu____4365,uu____4366) ->
        let qopt =
          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
            (fun uu___174_4377  ->
               match uu___174_4377 with
               | FStar_Syntax_Syntax.RecordConstructor (uu____4380,fs) ->
                   FStar_Pervasives_Native.Some
                     (FStar_Syntax_Syntax.Record_ctor (l, fs))
               | uu____4392 -> FStar_Pervasives_Native.None) in
        (match qopt with
         | FStar_Pervasives_Native.None  ->
             FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor
         | x -> x)
    | FStar_Syntax_Syntax.Sig_declare_typ (uu____4398,uu____4399,uu____4400)
        -> FStar_Pervasives_Native.None
    | uu____4401 -> FStar_Pervasives_Native.None
let lb_fv:
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Ident.lident -> FStar_Syntax_Syntax.fv
  =
  fun lbs  ->
    fun lid  ->
      let uu____4414 =
        FStar_Util.find_map lbs
          (fun lb  ->
             let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
             let uu____4422 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
             if uu____4422
             then FStar_Pervasives_Native.Some fv
             else FStar_Pervasives_Native.None) in
      FStar_All.pipe_right uu____4414 FStar_Util.must
let ns_of_lid_equals: FStar_Ident.lident -> FStar_Ident.lident -> Prims.bool
  =
  fun lid  ->
    fun ns  ->
      ((FStar_List.length lid.FStar_Ident.ns) =
         (FStar_List.length (FStar_Ident.ids_of_lid ns)))
        &&
        (let uu____4437 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
         FStar_Ident.lid_equals uu____4437 ns)
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
          let k_global_def source_lid uu___179_4471 =
            match uu___179_4471 with
            | (uu____4478,true ) when exclude_interf ->
                FStar_Pervasives_Native.None
            | (se,uu____4480) ->
                (match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_inductive_typ uu____4483 ->
                     let uu____4500 =
                       let uu____4501 =
                         let uu____4506 =
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.Delta_constant
                             FStar_Pervasives_Native.None in
                         (uu____4506, false) in
                       Term_name uu____4501 in
                     FStar_Pervasives_Native.Some uu____4500
                 | FStar_Syntax_Syntax.Sig_datacon uu____4507 ->
                     let uu____4522 =
                       let uu____4523 =
                         let uu____4528 =
                           let uu____4529 = fv_qual_of_se se in
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.Delta_constant uu____4529 in
                         (uu____4528, false) in
                       Term_name uu____4523 in
                     FStar_Pervasives_Native.Some uu____4522
                 | FStar_Syntax_Syntax.Sig_let ((uu____4532,lbs),uu____4534)
                     ->
                     let fv = lb_fv lbs source_lid in
                     let uu____4550 =
                       let uu____4551 =
                         let uu____4556 =
                           FStar_Syntax_Syntax.fvar source_lid
                             fv.FStar_Syntax_Syntax.fv_delta
                             fv.FStar_Syntax_Syntax.fv_qual in
                         (uu____4556, false) in
                       Term_name uu____4551 in
                     FStar_Pervasives_Native.Some uu____4550
                 | FStar_Syntax_Syntax.Sig_declare_typ
                     (lid1,uu____4558,uu____4559) ->
                     let quals = se.FStar_Syntax_Syntax.sigquals in
                     let uu____4563 =
                       any_val ||
                         (FStar_All.pipe_right quals
                            (FStar_Util.for_some
                               (fun uu___175_4567  ->
                                  match uu___175_4567 with
                                  | FStar_Syntax_Syntax.Assumption  -> true
                                  | uu____4568 -> false))) in
                     if uu____4563
                     then
                       let lid2 =
                         FStar_Ident.set_lid_range lid1
                           (FStar_Ident.range_of_lid source_lid) in
                       let dd =
                         let uu____4573 =
                           (FStar_Syntax_Util.is_primop_lid lid2) ||
                             (FStar_All.pipe_right quals
                                (FStar_Util.for_some
                                   (fun uu___176_4578  ->
                                      match uu___176_4578 with
                                      | FStar_Syntax_Syntax.Projector
                                          uu____4579 -> true
                                      | FStar_Syntax_Syntax.Discriminator
                                          uu____4584 -> true
                                      | uu____4585 -> false))) in
                         if uu____4573
                         then FStar_Syntax_Syntax.Delta_equational
                         else FStar_Syntax_Syntax.Delta_constant in
                       let dd1 =
                         let uu____4588 =
                           FStar_All.pipe_right quals
                             (FStar_Util.for_some
                                (fun uu___177_4592  ->
                                   match uu___177_4592 with
                                   | FStar_Syntax_Syntax.Abstract  -> true
                                   | uu____4593 -> false)) in
                         if uu____4588
                         then FStar_Syntax_Syntax.Delta_abstract dd
                         else dd in
                       let uu____4595 =
                         FStar_Util.find_map quals
                           (fun uu___178_4600  ->
                              match uu___178_4600 with
                              | FStar_Syntax_Syntax.Reflectable refl_monad ->
                                  FStar_Pervasives_Native.Some refl_monad
                              | uu____4604 -> FStar_Pervasives_Native.None) in
                       (match uu____4595 with
                        | FStar_Pervasives_Native.Some refl_monad ->
                            let refl_const =
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_constant
                                   (FStar_Const.Const_reflect refl_monad))
                                FStar_Pervasives_Native.None occurrence_range in
                            FStar_Pervasives_Native.Some
                              (Term_name (refl_const, false))
                        | uu____4613 ->
                            let uu____4616 =
                              let uu____4617 =
                                let uu____4622 =
                                  let uu____4623 = fv_qual_of_se se in
                                  FStar_Syntax_Syntax.fvar lid2 dd1
                                    uu____4623 in
                                (uu____4622, false) in
                              Term_name uu____4617 in
                            FStar_Pervasives_Native.Some uu____4616)
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
                 | FStar_Syntax_Syntax.Sig_effect_abbrev uu____4629 ->
                     FStar_Pervasives_Native.Some (Eff_name (se, source_lid))
                 | uu____4642 -> FStar_Pervasives_Native.None) in
          let k_local_binding r =
            let uu____4661 =
              let uu____4662 =
                found_local_binding (FStar_Ident.range_of_lid lid) r in
              Term_name uu____4662 in
            FStar_Pervasives_Native.Some uu____4661 in
          let k_rec_binding uu____4678 =
            match uu____4678 with
            | (id,l,dd) ->
                let uu____4690 =
                  let uu____4691 =
                    let uu____4696 =
                      FStar_Syntax_Syntax.fvar
                        (FStar_Ident.set_lid_range l
                           (FStar_Ident.range_of_lid lid)) dd
                        FStar_Pervasives_Native.None in
                    (uu____4696, false) in
                  Term_name uu____4691 in
                FStar_Pervasives_Native.Some uu____4690 in
          let found_unmangled =
            match lid.FStar_Ident.ns with
            | [] ->
                let uu____4702 = unmangleOpName lid.FStar_Ident.ident in
                (match uu____4702 with
                 | FStar_Pervasives_Native.Some f ->
                     FStar_Pervasives_Native.Some (Term_name f)
                 | uu____4720 -> FStar_Pervasives_Native.None)
            | uu____4727 -> FStar_Pervasives_Native.None in
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
        let uu____4759 = try_lookup_name true exclude_interf env lid in
        match uu____4759 with
        | FStar_Pervasives_Native.Some (Eff_name (o,l)) ->
            FStar_Pervasives_Native.Some (o, l)
        | uu____4774 -> FStar_Pervasives_Native.None
let try_lookup_effect_name:
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____4791 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____4791 with
      | FStar_Pervasives_Native.Some (o,l1) ->
          FStar_Pervasives_Native.Some l1
      | uu____4806 -> FStar_Pervasives_Native.None
let try_lookup_effect_name_and_attributes:
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident,FStar_Syntax_Syntax.cflags Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____4829 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____4829 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____4845;
             FStar_Syntax_Syntax.sigquals = uu____4846;
             FStar_Syntax_Syntax.sigmeta = uu____4847;
             FStar_Syntax_Syntax.sigattrs = uu____4848;_},l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____4867;
             FStar_Syntax_Syntax.sigquals = uu____4868;
             FStar_Syntax_Syntax.sigmeta = uu____4869;
             FStar_Syntax_Syntax.sigattrs = uu____4870;_},l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (uu____4888,uu____4889,uu____4890,uu____4891,cattributes);
             FStar_Syntax_Syntax.sigrng = uu____4893;
             FStar_Syntax_Syntax.sigquals = uu____4894;
             FStar_Syntax_Syntax.sigmeta = uu____4895;
             FStar_Syntax_Syntax.sigattrs = uu____4896;_},l1)
          -> FStar_Pervasives_Native.Some (l1, cattributes)
      | uu____4918 -> FStar_Pervasives_Native.None
let try_lookup_effect_defn:
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.eff_decl FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____4941 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____4941 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____4951;
             FStar_Syntax_Syntax.sigquals = uu____4952;
             FStar_Syntax_Syntax.sigmeta = uu____4953;
             FStar_Syntax_Syntax.sigattrs = uu____4954;_},uu____4955)
          -> FStar_Pervasives_Native.Some ne
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____4965;
             FStar_Syntax_Syntax.sigquals = uu____4966;
             FStar_Syntax_Syntax.sigmeta = uu____4967;
             FStar_Syntax_Syntax.sigattrs = uu____4968;_},uu____4969)
          -> FStar_Pervasives_Native.Some ne
      | uu____4978 -> FStar_Pervasives_Native.None
let is_effect_name: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____4993 = try_lookup_effect_name env lid in
      match uu____4993 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____4996 -> true
let try_lookup_root_effect_name:
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____5007 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____5007 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (l',uu____5017,uu____5018,uu____5019,uu____5020);
             FStar_Syntax_Syntax.sigrng = uu____5021;
             FStar_Syntax_Syntax.sigquals = uu____5022;
             FStar_Syntax_Syntax.sigmeta = uu____5023;
             FStar_Syntax_Syntax.sigattrs = uu____5024;_},uu____5025)
          ->
          let rec aux new_name =
            let uu____5044 =
              FStar_Util.smap_try_find (sigmap env) new_name.FStar_Ident.str in
            match uu____5044 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (s,uu____5062) ->
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
                     (uu____5071,uu____5072,uu____5073,cmp,uu____5075) ->
                     let l'' = FStar_Syntax_Util.comp_effect_name cmp in
                     aux l''
                 | uu____5081 -> FStar_Pervasives_Native.None) in
          aux l'
      | FStar_Pervasives_Native.Some (uu____5082,l') ->
          FStar_Pervasives_Native.Some l'
      | uu____5088 -> FStar_Pervasives_Native.None
let lookup_letbinding_quals:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___180_5119 =
        match uu___180_5119 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____5128,uu____5129,uu____5130);
             FStar_Syntax_Syntax.sigrng = uu____5131;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____5133;
             FStar_Syntax_Syntax.sigattrs = uu____5134;_},uu____5135)
            -> FStar_Pervasives_Native.Some quals
        | uu____5142 -> FStar_Pervasives_Native.None in
      let uu____5149 =
        resolve_in_open_namespaces' env lid
          (fun uu____5157  -> FStar_Pervasives_Native.None)
          (fun uu____5161  -> FStar_Pervasives_Native.None) k_global_def in
      match uu____5149 with
      | FStar_Pervasives_Native.Some quals -> quals
      | uu____5171 -> []
let try_lookup_module:
  env ->
    Prims.string Prims.list ->
      FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option
  =
  fun env  ->
    fun path  ->
      let uu____5190 =
        FStar_List.tryFind
          (fun uu____5205  ->
             match uu____5205 with
             | (mlid,modul) ->
                 let uu____5212 = FStar_Ident.path_of_lid mlid in
                 uu____5212 = path) env.modules in
      match uu____5190 with
      | FStar_Pervasives_Native.Some (uu____5219,modul) ->
          FStar_Pervasives_Native.Some modul
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
let try_lookup_let:
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___181_5251 =
        match uu___181_5251 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               ((uu____5258,lbs),uu____5260);
             FStar_Syntax_Syntax.sigrng = uu____5261;
             FStar_Syntax_Syntax.sigquals = uu____5262;
             FStar_Syntax_Syntax.sigmeta = uu____5263;
             FStar_Syntax_Syntax.sigattrs = uu____5264;_},uu____5265)
            ->
            let fv = lb_fv lbs lid1 in
            let uu____5285 =
              FStar_Syntax_Syntax.fvar lid1 fv.FStar_Syntax_Syntax.fv_delta
                fv.FStar_Syntax_Syntax.fv_qual in
            FStar_Pervasives_Native.Some uu____5285
        | uu____5286 -> FStar_Pervasives_Native.None in
      resolve_in_open_namespaces' env lid
        (fun uu____5292  -> FStar_Pervasives_Native.None)
        (fun uu____5294  -> FStar_Pervasives_Native.None) k_global_def
let try_lookup_definition:
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___182_5319 =
        match uu___182_5319 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               (lbs,uu____5329);
             FStar_Syntax_Syntax.sigrng = uu____5330;
             FStar_Syntax_Syntax.sigquals = uu____5331;
             FStar_Syntax_Syntax.sigmeta = uu____5332;
             FStar_Syntax_Syntax.sigattrs = uu____5333;_},uu____5334)
            ->
            FStar_Util.find_map (FStar_Pervasives_Native.snd lbs)
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inr fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv lid1 ->
                     FStar_Pervasives_Native.Some
                       (lb.FStar_Syntax_Syntax.lbdef)
                 | uu____5357 -> FStar_Pervasives_Native.None)
        | uu____5364 -> FStar_Pervasives_Native.None in
      resolve_in_open_namespaces' env lid
        (fun uu____5374  -> FStar_Pervasives_Native.None)
        (fun uu____5378  -> FStar_Pervasives_Native.None) k_global_def
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
          let uu____5421 = try_lookup_name any_val exclude_interf env lid in
          match uu____5421 with
          | FStar_Pervasives_Native.Some (Term_name (e,mut)) ->
              FStar_Pervasives_Native.Some (e, mut)
          | uu____5436 -> FStar_Pervasives_Native.None
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
      let uu____5467 = try_lookup_lid env l in
      match uu____5467 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (e,uu____5481) ->
          let uu____5486 =
            let uu____5487 = FStar_Syntax_Subst.compress e in
            uu____5487.FStar_Syntax_Syntax.n in
          (match uu____5486 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               FStar_Pervasives_Native.Some
                 ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
           | uu____5493 -> FStar_Pervasives_Native.None)
let try_lookup_lid_no_resolve:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term,Prims.bool) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let env' =
        let uu___203_5509 = env in
        {
          curmodule = (uu___203_5509.curmodule);
          curmonad = (uu___203_5509.curmonad);
          modules = (uu___203_5509.modules);
          scope_mods = [];
          exported_ids = empty_exported_id_smap;
          trans_exported_ids = (uu___203_5509.trans_exported_ids);
          includes = empty_include_smap;
          sigaccum = (uu___203_5509.sigaccum);
          sigmap = (uu___203_5509.sigmap);
          iface = (uu___203_5509.iface);
          admitted_iface = (uu___203_5509.admitted_iface);
          expect_typ = (uu___203_5509.expect_typ);
          docs = (uu___203_5509.docs);
          remaining_iface_decls = (uu___203_5509.remaining_iface_decls);
          syntax_only = (uu___203_5509.syntax_only);
          ds_hooks = (uu___203_5509.ds_hooks)
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
      let k_global_def lid1 uu___184_5542 =
        match uu___184_5542 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____5549,uu____5550,uu____5551);
             FStar_Syntax_Syntax.sigrng = uu____5552;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____5554;
             FStar_Syntax_Syntax.sigattrs = uu____5555;_},uu____5556)
            ->
            let uu____5561 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___183_5565  ->
                      match uu___183_5565 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | uu____5566 -> false)) in
            if uu____5561
            then
              let uu____5569 =
                FStar_Syntax_Syntax.lid_as_fv lid1
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None in
              FStar_Pervasives_Native.Some uu____5569
            else FStar_Pervasives_Native.None
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
               uu____5571;
             FStar_Syntax_Syntax.sigrng = uu____5572;
             FStar_Syntax_Syntax.sigquals = uu____5573;
             FStar_Syntax_Syntax.sigmeta = uu____5574;
             FStar_Syntax_Syntax.sigattrs = uu____5575;_},uu____5576)
            ->
            let uu____5595 =
              FStar_Syntax_Syntax.lid_as_fv lid1
                FStar_Syntax_Syntax.Delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor) in
            FStar_Pervasives_Native.Some uu____5595
        | uu____5596 -> FStar_Pervasives_Native.None in
      resolve_in_open_namespaces' env lid
        (fun uu____5602  -> FStar_Pervasives_Native.None)
        (fun uu____5604  -> FStar_Pervasives_Native.None) k_global_def
let find_all_datacons:
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident Prims.list FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___185_5631 =
        match uu___185_5631 with
        | ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_inductive_typ
               (uu____5640,uu____5641,uu____5642,uu____5643,datas,uu____5645);
             FStar_Syntax_Syntax.sigrng = uu____5646;
             FStar_Syntax_Syntax.sigquals = uu____5647;
             FStar_Syntax_Syntax.sigmeta = uu____5648;
             FStar_Syntax_Syntax.sigattrs = uu____5649;_},uu____5650)
            -> FStar_Pervasives_Native.Some datas
        | uu____5665 -> FStar_Pervasives_Native.None in
      resolve_in_open_namespaces' env lid
        (fun uu____5675  -> FStar_Pervasives_Native.None)
        (fun uu____5679  -> FStar_Pervasives_Native.None) k_global_def
let record_cache_aux_with_filter:
  ((Prims.unit -> Prims.unit,Prims.unit -> Prims.unit,Prims.unit ->
                                                        record_or_dc
                                                          Prims.list,
     record_or_dc -> Prims.unit) FStar_Pervasives_Native.tuple4,Prims.unit ->
                                                                  Prims.unit)
    FStar_Pervasives_Native.tuple2
  =
  let record_cache = FStar_Util.mk_ref [[]] in
  let push1 uu____5724 =
    let uu____5725 =
      let uu____5730 =
        let uu____5733 = FStar_ST.op_Bang record_cache in
        FStar_List.hd uu____5733 in
      let uu____5808 = FStar_ST.op_Bang record_cache in uu____5730 ::
        uu____5808 in
    FStar_ST.op_Colon_Equals record_cache uu____5725 in
  let pop1 uu____5954 =
    let uu____5955 =
      let uu____5960 = FStar_ST.op_Bang record_cache in
      FStar_List.tl uu____5960 in
    FStar_ST.op_Colon_Equals record_cache uu____5955 in
  let peek1 uu____6108 =
    let uu____6109 = FStar_ST.op_Bang record_cache in
    FStar_List.hd uu____6109 in
  let insert r =
    let uu____6188 =
      let uu____6193 = let uu____6196 = peek1 () in r :: uu____6196 in
      let uu____6199 =
        let uu____6204 = FStar_ST.op_Bang record_cache in
        FStar_List.tl uu____6204 in
      uu____6193 :: uu____6199 in
    FStar_ST.op_Colon_Equals record_cache uu____6188 in
  let filter1 uu____6352 =
    let rc = peek1 () in
    let filtered =
      FStar_List.filter
        (fun r  -> Prims.op_Negation r.is_private_or_abstract) rc in
    let uu____6361 =
      let uu____6366 =
        let uu____6371 = FStar_ST.op_Bang record_cache in
        FStar_List.tl uu____6371 in
      filtered :: uu____6366 in
    FStar_ST.op_Colon_Equals record_cache uu____6361 in
  let aux = (push1, pop1, peek1, insert) in (aux, filter1)
let record_cache_aux:
  (Prims.unit -> Prims.unit,Prims.unit -> Prims.unit,Prims.unit ->
                                                       record_or_dc
                                                         Prims.list,record_or_dc
                                                                    ->
                                                                    Prims.unit)
    FStar_Pervasives_Native.tuple4
  =
  let uu____6583 = record_cache_aux_with_filter in
  match uu____6583 with | (aux,uu____6627) -> aux
let filter_record_cache: Prims.unit -> Prims.unit =
  let uu____6671 = record_cache_aux_with_filter in
  match uu____6671 with | (uu____6698,filter1) -> filter1
let push_record_cache: Prims.unit -> Prims.unit =
  let uu____6743 = record_cache_aux in
  match uu____6743 with | (push1,uu____6765,uu____6766,uu____6767) -> push1
let pop_record_cache: Prims.unit -> Prims.unit =
  let uu____6791 = record_cache_aux in
  match uu____6791 with | (uu____6812,pop1,uu____6814,uu____6815) -> pop1
let peek_record_cache: Prims.unit -> record_or_dc Prims.list =
  let uu____6841 = record_cache_aux in
  match uu____6841 with | (uu____6864,uu____6865,peek1,uu____6867) -> peek1
let insert_record_cache: record_or_dc -> Prims.unit =
  let uu____6891 = record_cache_aux in
  match uu____6891 with | (uu____6912,uu____6913,uu____6914,insert) -> insert
let extract_record:
  env ->
    scope_mod Prims.list FStar_ST.ref ->
      FStar_Syntax_Syntax.sigelt -> Prims.unit
  =
  fun e  ->
    fun new_globs  ->
      fun se  ->
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_bundle (sigs,uu____6971) ->
            let is_record =
              FStar_Util.for_some
                (fun uu___186_6987  ->
                   match uu___186_6987 with
                   | FStar_Syntax_Syntax.RecordType uu____6988 -> true
                   | FStar_Syntax_Syntax.RecordConstructor uu____6997 -> true
                   | uu____7006 -> false) in
            let find_dc dc =
              FStar_All.pipe_right sigs
                (FStar_Util.find_opt
                   (fun uu___187_7028  ->
                      match uu___187_7028 with
                      | {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_datacon
                            (lid,uu____7030,uu____7031,uu____7032,uu____7033,uu____7034);
                          FStar_Syntax_Syntax.sigrng = uu____7035;
                          FStar_Syntax_Syntax.sigquals = uu____7036;
                          FStar_Syntax_Syntax.sigmeta = uu____7037;
                          FStar_Syntax_Syntax.sigattrs = uu____7038;_} ->
                          FStar_Ident.lid_equals dc lid
                      | uu____7047 -> false)) in
            FStar_All.pipe_right sigs
              (FStar_List.iter
                 (fun uu___188_7082  ->
                    match uu___188_7082 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ
                          (typename,univs1,parms,uu____7086,uu____7087,dc::[]);
                        FStar_Syntax_Syntax.sigrng = uu____7089;
                        FStar_Syntax_Syntax.sigquals = typename_quals;
                        FStar_Syntax_Syntax.sigmeta = uu____7091;
                        FStar_Syntax_Syntax.sigattrs = uu____7092;_} ->
                        let uu____7103 =
                          let uu____7104 = find_dc dc in
                          FStar_All.pipe_left FStar_Util.must uu____7104 in
                        (match uu____7103 with
                         | {
                             FStar_Syntax_Syntax.sigel =
                               FStar_Syntax_Syntax.Sig_datacon
                               (constrname,uu____7110,t,uu____7112,uu____7113,uu____7114);
                             FStar_Syntax_Syntax.sigrng = uu____7115;
                             FStar_Syntax_Syntax.sigquals = uu____7116;
                             FStar_Syntax_Syntax.sigmeta = uu____7117;
                             FStar_Syntax_Syntax.sigattrs = uu____7118;_} ->
                             let uu____7127 =
                               FStar_Syntax_Util.arrow_formals t in
                             (match uu____7127 with
                              | (formals,uu____7141) ->
                                  let is_rec = is_record typename_quals in
                                  let formals' =
                                    FStar_All.pipe_right formals
                                      (FStar_List.collect
                                         (fun uu____7190  ->
                                            match uu____7190 with
                                            | (x,q) ->
                                                let uu____7203 =
                                                  (FStar_Syntax_Syntax.is_null_bv
                                                     x)
                                                    ||
                                                    (is_rec &&
                                                       (FStar_Syntax_Syntax.is_implicit
                                                          q)) in
                                                if uu____7203
                                                then []
                                                else [(x, q)])) in
                                  let fields' =
                                    FStar_All.pipe_right formals'
                                      (FStar_List.map
                                         (fun uu____7260  ->
                                            match uu____7260 with
                                            | (x,q) ->
                                                let uu____7273 =
                                                  if is_rec
                                                  then
                                                    FStar_Syntax_Util.unmangle_field_name
                                                      x.FStar_Syntax_Syntax.ppname
                                                  else
                                                    x.FStar_Syntax_Syntax.ppname in
                                                (uu____7273,
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
                                  ((let uu____7288 =
                                      let uu____7291 =
                                        FStar_ST.op_Bang new_globs in
                                      (Record_or_dc record) :: uu____7291 in
                                    FStar_ST.op_Colon_Equals new_globs
                                      uu____7288);
                                   (match () with
                                    | () ->
                                        ((let add_field uu____7432 =
                                            match uu____7432 with
                                            | (id,uu____7440) ->
                                                let modul =
                                                  let uu____7446 =
                                                    FStar_Ident.lid_of_ids
                                                      constrname.FStar_Ident.ns in
                                                  uu____7446.FStar_Ident.str in
                                                let uu____7447 =
                                                  get_exported_id_set e modul in
                                                (match uu____7447 with
                                                 | FStar_Pervasives_Native.Some
                                                     my_ex ->
                                                     let my_exported_ids =
                                                       my_ex
                                                         Exported_id_field in
                                                     ((let uu____7474 =
                                                         let uu____7475 =
                                                           FStar_ST.op_Bang
                                                             my_exported_ids in
                                                         FStar_Util.set_add
                                                           id.FStar_Ident.idText
                                                           uu____7475 in
                                                       FStar_ST.op_Colon_Equals
                                                         my_exported_ids
                                                         uu____7474);
                                                      (match () with
                                                       | () ->
                                                           let projname =
                                                             let uu____7599 =
                                                               let uu____7600
                                                                 =
                                                                 FStar_Syntax_Util.mk_field_projector_name_from_ident
                                                                   constrname
                                                                   id in
                                                               uu____7600.FStar_Ident.ident in
                                                             uu____7599.FStar_Ident.idText in
                                                           let uu____7602 =
                                                             let uu____7603 =
                                                               FStar_ST.op_Bang
                                                                 my_exported_ids in
                                                             FStar_Util.set_add
                                                               projname
                                                               uu____7603 in
                                                           FStar_ST.op_Colon_Equals
                                                             my_exported_ids
                                                             uu____7602))
                                                 | FStar_Pervasives_Native.None
                                                      -> ()) in
                                          FStar_List.iter add_field fields');
                                         (match () with
                                          | () -> insert_record_cache record)))))
                         | uu____7736 -> ())
                    | uu____7737 -> ()))
        | uu____7738 -> ()
let try_lookup_record_or_dc_by_field_name:
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option =
  fun env  ->
    fun fieldname  ->
      let find_in_cache fieldname1 =
        let uu____7755 =
          ((fieldname1.FStar_Ident.ns), (fieldname1.FStar_Ident.ident)) in
        match uu____7755 with
        | (ns,id) ->
            let uu____7772 = peek_record_cache () in
            FStar_Util.find_map uu____7772
              (fun record  ->
                 let uu____7778 =
                   find_in_record ns id record (fun r  -> Cont_ok r) in
                 option_of_cont
                   (fun uu____7784  -> FStar_Pervasives_Native.None)
                   uu____7778) in
      resolve_in_open_namespaces'' env fieldname Exported_id_field
        (fun uu____7786  -> Cont_ignore) (fun uu____7788  -> Cont_ignore)
        (fun r  -> Cont_ok r)
        (fun fn  ->
           let uu____7794 = find_in_cache fn in
           cont_of_option Cont_ignore uu____7794)
        (fun k  -> fun uu____7800  -> k)
let try_lookup_record_by_field_name:
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option =
  fun env  ->
    fun fieldname  ->
      let uu____7813 = try_lookup_record_or_dc_by_field_name env fieldname in
      match uu____7813 with
      | FStar_Pervasives_Native.Some r when r.is_record ->
          FStar_Pervasives_Native.Some r
      | uu____7819 -> FStar_Pervasives_Native.None
let belongs_to_record:
  env -> FStar_Ident.lident -> record_or_dc -> Prims.bool =
  fun env  ->
    fun lid  ->
      fun record  ->
        let uu____7834 = try_lookup_record_by_field_name env lid in
        match uu____7834 with
        | FStar_Pervasives_Native.Some record' when
            let uu____7838 =
              let uu____7839 =
                FStar_Ident.path_of_ns (record.typename).FStar_Ident.ns in
              FStar_Ident.text_of_path uu____7839 in
            let uu____7842 =
              let uu____7843 =
                FStar_Ident.path_of_ns (record'.typename).FStar_Ident.ns in
              FStar_Ident.text_of_path uu____7843 in
            uu____7838 = uu____7842 ->
            let uu____7846 =
              find_in_record (record.typename).FStar_Ident.ns
                lid.FStar_Ident.ident record (fun uu____7850  -> Cont_ok ()) in
            (match uu____7846 with
             | Cont_ok uu____7851 -> true
             | uu____7852 -> false)
        | uu____7855 -> false
let try_lookup_dc_by_field_name:
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident,Prims.bool) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option
  =
  fun env  ->
    fun fieldname  ->
      let uu____7872 = try_lookup_record_or_dc_by_field_name env fieldname in
      match uu____7872 with
      | FStar_Pervasives_Native.Some r ->
          let uu____7882 =
            let uu____7887 =
              let uu____7888 =
                FStar_Ident.lid_of_ids
                  (FStar_List.append (r.typename).FStar_Ident.ns
                     [r.constrname]) in
              FStar_Ident.set_lid_range uu____7888
                (FStar_Ident.range_of_lid fieldname) in
            (uu____7887, (r.is_record)) in
          FStar_Pervasives_Native.Some uu____7882
      | uu____7893 -> FStar_Pervasives_Native.None
let string_set_ref_new:
  Prims.unit -> Prims.string FStar_Util.set FStar_ST.ref =
  fun uu____7914  ->
    let uu____7915 = FStar_Util.new_set FStar_Util.compare in
    FStar_Util.mk_ref uu____7915
let exported_id_set_new:
  Prims.unit -> exported_id_kind -> Prims.string FStar_Util.set FStar_ST.ref
  =
  fun uu____7936  ->
    let term_type_set = string_set_ref_new () in
    let field_set = string_set_ref_new () in
    fun uu___189_7947  ->
      match uu___189_7947 with
      | Exported_id_term_type  -> term_type_set
      | Exported_id_field  -> field_set
let unique:
  Prims.bool -> Prims.bool -> env -> FStar_Ident.lident -> Prims.bool =
  fun any_val  ->
    fun exclude_if  ->
      fun env  ->
        fun lid  ->
          let filter_scope_mods uu___190_7985 =
            match uu___190_7985 with
            | Rec_binding uu____7986 -> true
            | uu____7987 -> false in
          let this_env =
            let uu___204_7989 = env in
            let uu____7990 =
              FStar_List.filter filter_scope_mods env.scope_mods in
            {
              curmodule = (uu___204_7989.curmodule);
              curmonad = (uu___204_7989.curmonad);
              modules = (uu___204_7989.modules);
              scope_mods = uu____7990;
              exported_ids = empty_exported_id_smap;
              trans_exported_ids = (uu___204_7989.trans_exported_ids);
              includes = empty_include_smap;
              sigaccum = (uu___204_7989.sigaccum);
              sigmap = (uu___204_7989.sigmap);
              iface = (uu___204_7989.iface);
              admitted_iface = (uu___204_7989.admitted_iface);
              expect_typ = (uu___204_7989.expect_typ);
              docs = (uu___204_7989.docs);
              remaining_iface_decls = (uu___204_7989.remaining_iface_decls);
              syntax_only = (uu___204_7989.syntax_only);
              ds_hooks = (uu___204_7989.ds_hooks)
            } in
          let uu____7993 = try_lookup_lid' any_val exclude_if this_env lid in
          match uu____7993 with
          | FStar_Pervasives_Native.None  -> true
          | FStar_Pervasives_Native.Some uu____8004 -> false
let push_scope_mod: env -> scope_mod -> env =
  fun env  ->
    fun scope_mod  ->
      let uu___205_8021 = env in
      {
        curmodule = (uu___205_8021.curmodule);
        curmonad = (uu___205_8021.curmonad);
        modules = (uu___205_8021.modules);
        scope_mods = (scope_mod :: (env.scope_mods));
        exported_ids = (uu___205_8021.exported_ids);
        trans_exported_ids = (uu___205_8021.trans_exported_ids);
        includes = (uu___205_8021.includes);
        sigaccum = (uu___205_8021.sigaccum);
        sigmap = (uu___205_8021.sigmap);
        iface = (uu___205_8021.iface);
        admitted_iface = (uu___205_8021.admitted_iface);
        expect_typ = (uu___205_8021.expect_typ);
        docs = (uu___205_8021.docs);
        remaining_iface_decls = (uu___205_8021.remaining_iface_decls);
        syntax_only = (uu___205_8021.syntax_only);
        ds_hooks = (uu___205_8021.ds_hooks)
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
        let uu____8076 =
          (unique false true env l) || (FStar_Options.interactive ()) in
        if uu____8076
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
          | FStar_Pervasives_Native.Some (se,uu____8103) ->
              let uu____8108 =
                FStar_Util.find_opt (FStar_Ident.lid_equals l)
                  (FStar_Syntax_Util.lids_of_sigelt se) in
              (match uu____8108 with
               | FStar_Pervasives_Native.Some l1 ->
                   FStar_All.pipe_left FStar_Range.string_of_range
                     (FStar_Ident.range_of_lid l1)
               | FStar_Pervasives_Native.None  -> "<unknown>")
          | FStar_Pervasives_Native.None  -> "<unknown>" in
        let uu____8116 =
          let uu____8117 =
            let uu____8122 =
              FStar_Util.format2
                "Duplicate top-level names [%s]; previously declared at %s"
                (FStar_Ident.text_of_lid l) r in
            (uu____8122, (FStar_Ident.range_of_lid l)) in
          FStar_Errors.Error uu____8117 in
        FStar_Exn.raise uu____8116 in
      let globals = FStar_Util.mk_ref env.scope_mods in
      let env1 =
        let uu____8131 =
          match s.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let uu____8140 -> (false, true)
          | FStar_Syntax_Syntax.Sig_bundle uu____8147 -> (true, true)
          | uu____8156 -> (false, false) in
        match uu____8131 with
        | (any_val,exclude_if) ->
            let lids = FStar_Syntax_Util.lids_of_sigelt s in
            let uu____8162 =
              FStar_Util.find_map lids
                (fun l  ->
                   let uu____8168 =
                     let uu____8169 = unique any_val exclude_if env l in
                     Prims.op_Negation uu____8169 in
                   if uu____8168
                   then FStar_Pervasives_Native.Some l
                   else FStar_Pervasives_Native.None) in
            (match uu____8162 with
             | FStar_Pervasives_Native.Some l when
                 let uu____8174 = FStar_Options.interactive () in
                 Prims.op_Negation uu____8174 -> err1 l
             | uu____8175 ->
                 (extract_record env globals s;
                  (let uu___206_8193 = env in
                   {
                     curmodule = (uu___206_8193.curmodule);
                     curmonad = (uu___206_8193.curmonad);
                     modules = (uu___206_8193.modules);
                     scope_mods = (uu___206_8193.scope_mods);
                     exported_ids = (uu___206_8193.exported_ids);
                     trans_exported_ids = (uu___206_8193.trans_exported_ids);
                     includes = (uu___206_8193.includes);
                     sigaccum = (s :: (env.sigaccum));
                     sigmap = (uu___206_8193.sigmap);
                     iface = (uu___206_8193.iface);
                     admitted_iface = (uu___206_8193.admitted_iface);
                     expect_typ = (uu___206_8193.expect_typ);
                     docs = (uu___206_8193.docs);
                     remaining_iface_decls =
                       (uu___206_8193.remaining_iface_decls);
                     syntax_only = (uu___206_8193.syntax_only);
                     ds_hooks = (uu___206_8193.ds_hooks)
                   }))) in
      let env2 =
        let uu___207_8195 = env1 in
        let uu____8196 = FStar_ST.op_Bang globals in
        {
          curmodule = (uu___207_8195.curmodule);
          curmonad = (uu___207_8195.curmonad);
          modules = (uu___207_8195.modules);
          scope_mods = uu____8196;
          exported_ids = (uu___207_8195.exported_ids);
          trans_exported_ids = (uu___207_8195.trans_exported_ids);
          includes = (uu___207_8195.includes);
          sigaccum = (uu___207_8195.sigaccum);
          sigmap = (uu___207_8195.sigmap);
          iface = (uu___207_8195.iface);
          admitted_iface = (uu___207_8195.admitted_iface);
          expect_typ = (uu___207_8195.expect_typ);
          docs = (uu___207_8195.docs);
          remaining_iface_decls = (uu___207_8195.remaining_iface_decls);
          syntax_only = (uu___207_8195.syntax_only);
          ds_hooks = (uu___207_8195.ds_hooks)
        } in
      let uu____8263 =
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_bundle (ses,uu____8289) ->
            let uu____8298 =
              FStar_List.map
                (fun se  -> ((FStar_Syntax_Util.lids_of_sigelt se), se)) ses in
            (env2, uu____8298)
        | uu____8325 -> (env2, [((FStar_Syntax_Util.lids_of_sigelt s), s)]) in
      match uu____8263 with
      | (env3,lss) ->
          (FStar_All.pipe_right lss
             (FStar_List.iter
                (fun uu____8384  ->
                   match uu____8384 with
                   | (lids,se) ->
                       FStar_All.pipe_right lids
                         (FStar_List.iter
                            (fun lid  ->
                               (let uu____8405 =
                                  let uu____8408 = FStar_ST.op_Bang globals in
                                  (Top_level_def (lid.FStar_Ident.ident)) ::
                                    uu____8408 in
                                FStar_ST.op_Colon_Equals globals uu____8405);
                               (match () with
                                | () ->
                                    let modul =
                                      let uu____8540 =
                                        FStar_Ident.lid_of_ids
                                          lid.FStar_Ident.ns in
                                      uu____8540.FStar_Ident.str in
                                    ((let uu____8542 =
                                        get_exported_id_set env3 modul in
                                      match uu____8542 with
                                      | FStar_Pervasives_Native.Some f ->
                                          let my_exported_ids =
                                            f Exported_id_term_type in
                                          let uu____8568 =
                                            let uu____8569 =
                                              FStar_ST.op_Bang
                                                my_exported_ids in
                                            FStar_Util.set_add
                                              (lid.FStar_Ident.ident).FStar_Ident.idText
                                              uu____8569 in
                                          FStar_ST.op_Colon_Equals
                                            my_exported_ids uu____8568
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
              let uu___208_8701 = env3 in
              let uu____8702 = FStar_ST.op_Bang globals in
              {
                curmodule = (uu___208_8701.curmodule);
                curmonad = (uu___208_8701.curmonad);
                modules = (uu___208_8701.modules);
                scope_mods = uu____8702;
                exported_ids = (uu___208_8701.exported_ids);
                trans_exported_ids = (uu___208_8701.trans_exported_ids);
                includes = (uu___208_8701.includes);
                sigaccum = (uu___208_8701.sigaccum);
                sigmap = (uu___208_8701.sigmap);
                iface = (uu___208_8701.iface);
                admitted_iface = (uu___208_8701.admitted_iface);
                expect_typ = (uu___208_8701.expect_typ);
                docs = (uu___208_8701.docs);
                remaining_iface_decls = (uu___208_8701.remaining_iface_decls);
                syntax_only = (uu___208_8701.syntax_only);
                ds_hooks = (uu___208_8701.ds_hooks)
              } in
            env4))
let push_namespace: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun ns  ->
      let uu____8777 =
        let uu____8782 = resolve_module_name env ns false in
        match uu____8782 with
        | FStar_Pervasives_Native.None  ->
            let modules = env.modules in
            let uu____8796 =
              FStar_All.pipe_right modules
                (FStar_Util.for_some
                   (fun uu____8810  ->
                      match uu____8810 with
                      | (m,uu____8816) ->
                          FStar_Util.starts_with
                            (Prims.strcat (FStar_Ident.text_of_lid m) ".")
                            (Prims.strcat (FStar_Ident.text_of_lid ns) "."))) in
            if uu____8796
            then (ns, Open_namespace)
            else
              (let uu____8822 =
                 let uu____8823 =
                   let uu____8828 =
                     FStar_Util.format1 "Namespace %s cannot be found"
                       (FStar_Ident.text_of_lid ns) in
                   (uu____8828, (FStar_Ident.range_of_lid ns)) in
                 FStar_Errors.Error uu____8823 in
               FStar_Exn.raise uu____8822)
        | FStar_Pervasives_Native.Some ns' ->
            (fail_if_curmodule env ns ns'; (ns', Open_module)) in
      match uu____8777 with
      | (ns',kd) ->
          ((env.ds_hooks).ds_push_open_hook env (ns', kd);
           push_scope_mod env (Open_module_or_namespace (ns', kd)))
let push_include: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun ns  ->
      let ns0 = ns in
      let uu____8847 = resolve_module_name env ns false in
      match uu____8847 with
      | FStar_Pervasives_Native.Some ns1 ->
          ((env.ds_hooks).ds_push_include_hook env ns1;
           fail_if_curmodule env ns0 ns1;
           (let env1 =
              push_scope_mod env
                (Open_module_or_namespace (ns1, Open_module)) in
            let curmod =
              let uu____8855 = current_module env1 in
              uu____8855.FStar_Ident.str in
            (let uu____8857 = FStar_Util.smap_try_find env1.includes curmod in
             match uu____8857 with
             | FStar_Pervasives_Native.None  -> ()
             | FStar_Pervasives_Native.Some incl ->
                 let uu____8881 =
                   let uu____8884 = FStar_ST.op_Bang incl in ns1 ::
                     uu____8884 in
                 FStar_ST.op_Colon_Equals incl uu____8881);
            (match () with
             | () ->
                 let uu____9015 =
                   get_trans_exported_id_set env1 ns1.FStar_Ident.str in
                 (match uu____9015 with
                  | FStar_Pervasives_Native.Some ns_trans_exports ->
                      ((let uu____9032 =
                          let uu____9049 = get_exported_id_set env1 curmod in
                          let uu____9056 =
                            get_trans_exported_id_set env1 curmod in
                          (uu____9049, uu____9056) in
                        match uu____9032 with
                        | (FStar_Pervasives_Native.Some
                           cur_exports,FStar_Pervasives_Native.Some
                           cur_trans_exports) ->
                            let update_exports k =
                              let ns_ex =
                                let uu____9110 = ns_trans_exports k in
                                FStar_ST.op_Bang uu____9110 in
                              let ex = cur_exports k in
                              (let uu____9365 =
                                 let uu____9366 = FStar_ST.op_Bang ex in
                                 FStar_Util.set_difference uu____9366 ns_ex in
                               FStar_ST.op_Colon_Equals ex uu____9365);
                              (match () with
                               | () ->
                                   let trans_ex = cur_trans_exports k in
                                   let uu____9500 =
                                     let uu____9501 =
                                       FStar_ST.op_Bang trans_ex in
                                     FStar_Util.set_union uu____9501 ns_ex in
                                   FStar_ST.op_Colon_Equals trans_ex
                                     uu____9500) in
                            FStar_List.iter update_exports
                              all_exported_id_kinds
                        | uu____9624 -> ());
                       (match () with | () -> env1))
                  | FStar_Pervasives_Native.None  ->
                      let uu____9645 =
                        let uu____9646 =
                          let uu____9651 =
                            FStar_Util.format1
                              "include: Module %s was not prepared"
                              ns1.FStar_Ident.str in
                          (uu____9651, (FStar_Ident.range_of_lid ns1)) in
                        FStar_Errors.Error uu____9646 in
                      FStar_Exn.raise uu____9645))))
      | uu____9652 ->
          let uu____9655 =
            let uu____9656 =
              let uu____9661 =
                FStar_Util.format1 "include: Module %s cannot be found"
                  ns.FStar_Ident.str in
              (uu____9661, (FStar_Ident.range_of_lid ns)) in
            FStar_Errors.Error uu____9656 in
          FStar_Exn.raise uu____9655
let push_module_abbrev: env -> FStar_Ident.ident -> FStar_Ident.lident -> env
  =
  fun env  ->
    fun x  ->
      fun l  ->
        let uu____9674 = module_is_defined env l in
        if uu____9674
        then
          (fail_if_curmodule env l l;
           (env.ds_hooks).ds_push_module_abbrev_hook env x l;
           push_scope_mod env (Module_abbrev (x, l)))
        else
          (let uu____9678 =
             let uu____9679 =
               let uu____9684 =
                 FStar_Util.format1 "Module %s cannot be found"
                   (FStar_Ident.text_of_lid l) in
               (uu____9684, (FStar_Ident.range_of_lid l)) in
             FStar_Errors.Error uu____9679 in
           FStar_Exn.raise uu____9678)
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
            ((let uu____9703 =
                FStar_Util.smap_try_find env.docs l.FStar_Ident.str in
              match uu____9703 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some old_doc ->
                  let uu____9707 =
                    let uu____9708 = FStar_Ident.string_of_lid l in
                    let uu____9709 = FStar_Parser_AST.string_of_fsdoc old_doc in
                    let uu____9710 = FStar_Parser_AST.string_of_fsdoc doc1 in
                    FStar_Util.format3
                      "Overwriting doc of %s; old doc was [%s]; new doc are [%s]"
                      uu____9708 uu____9709 uu____9710 in
                  FStar_Errors.warn (FStar_Ident.range_of_lid l) uu____9707);
             FStar_Util.smap_add env.docs l.FStar_Ident.str doc1;
             env)
let check_admits: env -> Prims.unit =
  fun env  ->
    FStar_All.pipe_right env.sigaccum
      (FStar_List.iter
         (fun se  ->
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t) ->
                let uu____9727 = try_lookup_lid env l in
                (match uu____9727 with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____9739 =
                         let uu____9740 = FStar_Options.interactive () in
                         Prims.op_Negation uu____9740 in
                       if uu____9739
                       then
                         let uu____9741 =
                           let uu____9742 =
                             FStar_Syntax_Print.lid_to_string l in
                           FStar_Util.format1
                             "Admitting %s without a definition" uu____9742 in
                         FStar_Errors.warn (FStar_Ident.range_of_lid l)
                           uu____9741
                       else ());
                      (let quals = FStar_Syntax_Syntax.Assumption ::
                         (se.FStar_Syntax_Syntax.sigquals) in
                       FStar_Util.smap_add (sigmap env) l.FStar_Ident.str
                         ((let uu___209_9752 = se in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (uu___209_9752.FStar_Syntax_Syntax.sigel);
                             FStar_Syntax_Syntax.sigrng =
                               (uu___209_9752.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals = quals;
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___209_9752.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___209_9752.FStar_Syntax_Syntax.sigattrs)
                           }), false)))
                 | FStar_Pervasives_Native.Some uu____9753 -> ())
            | uu____9762 -> ()))
let finish: env -> FStar_Syntax_Syntax.modul -> env =
  fun env  ->
    fun modul  ->
      FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations
        (FStar_List.iter
           (fun se  ->
              let quals = se.FStar_Syntax_Syntax.sigquals in
              match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_bundle (ses,uu____9781) ->
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
                                (lid,uu____9801,uu____9802,uu____9803,uu____9804,uu____9805)
                                ->
                                FStar_Util.smap_remove (sigmap env)
                                  lid.FStar_Ident.str
                            | uu____9814 -> ()))
                  else ()
              | FStar_Syntax_Syntax.Sig_declare_typ
                  (lid,uu____9817,uu____9818) ->
                  if FStar_List.contains FStar_Syntax_Syntax.Private quals
                  then
                    FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str
                  else ()
              | FStar_Syntax_Syntax.Sig_let ((uu____9824,lbs),uu____9826) ->
                  (if
                     (FStar_List.contains FStar_Syntax_Syntax.Private quals)
                       ||
                       (FStar_List.contains FStar_Syntax_Syntax.Abstract
                          quals)
                   then
                     FStar_All.pipe_right lbs
                       (FStar_List.iter
                          (fun lb  ->
                             let uu____9847 =
                               let uu____9848 =
                                 let uu____9849 =
                                   let uu____9852 =
                                     FStar_Util.right
                                       lb.FStar_Syntax_Syntax.lbname in
                                   uu____9852.FStar_Syntax_Syntax.fv_name in
                                 uu____9849.FStar_Syntax_Syntax.v in
                               uu____9848.FStar_Ident.str in
                             FStar_Util.smap_remove (sigmap env) uu____9847))
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
                               let uu____9866 =
                                 let uu____9869 =
                                   FStar_Util.right
                                     lb.FStar_Syntax_Syntax.lbname in
                                 uu____9869.FStar_Syntax_Syntax.fv_name in
                               uu____9866.FStar_Syntax_Syntax.v in
                             let quals1 = FStar_Syntax_Syntax.Assumption ::
                               quals in
                             let decl =
                               let uu___210_9874 = se in
                               {
                                 FStar_Syntax_Syntax.sigel =
                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                      (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                        (lb.FStar_Syntax_Syntax.lbtyp)));
                                 FStar_Syntax_Syntax.sigrng =
                                   (uu___210_9874.FStar_Syntax_Syntax.sigrng);
                                 FStar_Syntax_Syntax.sigquals = quals1;
                                 FStar_Syntax_Syntax.sigmeta =
                                   (uu___210_9874.FStar_Syntax_Syntax.sigmeta);
                                 FStar_Syntax_Syntax.sigattrs =
                                   (uu___210_9874.FStar_Syntax_Syntax.sigattrs)
                               } in
                             FStar_Util.smap_add (sigmap env)
                               lid.FStar_Ident.str (decl, false)))
                   else ())
              | uu____9884 -> ()));
      (let curmod =
         let uu____9886 = current_module env in uu____9886.FStar_Ident.str in
       (let uu____9888 =
          let uu____9905 = get_exported_id_set env curmod in
          let uu____9912 = get_trans_exported_id_set env curmod in
          (uu____9905, uu____9912) in
        match uu____9888 with
        | (FStar_Pervasives_Native.Some cur_ex,FStar_Pervasives_Native.Some
           cur_trans_ex) ->
            let update_exports eikind =
              let cur_ex_set =
                let uu____9966 = cur_ex eikind in FStar_ST.op_Bang uu____9966 in
              let cur_trans_ex_set_ref = cur_trans_ex eikind in
              let uu____10220 =
                let uu____10221 = FStar_ST.op_Bang cur_trans_ex_set_ref in
                FStar_Util.set_union cur_ex_set uu____10221 in
              FStar_ST.op_Colon_Equals cur_trans_ex_set_ref uu____10220 in
            FStar_List.iter update_exports all_exported_id_kinds
        | uu____10344 -> ());
       (match () with
        | () ->
            (filter_record_cache ();
             (match () with
              | () ->
                  let uu___211_10362 = env in
                  {
                    curmodule = FStar_Pervasives_Native.None;
                    curmonad = (uu___211_10362.curmonad);
                    modules = (((modul.FStar_Syntax_Syntax.name), modul) ::
                      (env.modules));
                    scope_mods = [];
                    exported_ids = (uu___211_10362.exported_ids);
                    trans_exported_ids = (uu___211_10362.trans_exported_ids);
                    includes = (uu___211_10362.includes);
                    sigaccum = [];
                    sigmap = (uu___211_10362.sigmap);
                    iface = (uu___211_10362.iface);
                    admitted_iface = (uu___211_10362.admitted_iface);
                    expect_typ = (uu___211_10362.expect_typ);
                    docs = (uu___211_10362.docs);
                    remaining_iface_decls =
                      (uu___211_10362.remaining_iface_decls);
                    syntax_only = (uu___211_10362.syntax_only);
                    ds_hooks = (uu___211_10362.ds_hooks)
                  }))))
let stack: env Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let push: env -> env =
  fun env  ->
    push_record_cache ();
    (let uu____10386 =
       let uu____10389 = FStar_ST.op_Bang stack in env :: uu____10389 in
     FStar_ST.op_Colon_Equals stack uu____10386);
    (let uu___212_10492 = env in
     let uu____10493 = FStar_Util.smap_copy (sigmap env) in
     let uu____10504 = FStar_Util.smap_copy env.docs in
     {
       curmodule = (uu___212_10492.curmodule);
       curmonad = (uu___212_10492.curmonad);
       modules = (uu___212_10492.modules);
       scope_mods = (uu___212_10492.scope_mods);
       exported_ids = (uu___212_10492.exported_ids);
       trans_exported_ids = (uu___212_10492.trans_exported_ids);
       includes = (uu___212_10492.includes);
       sigaccum = (uu___212_10492.sigaccum);
       sigmap = uu____10493;
       iface = (uu___212_10492.iface);
       admitted_iface = (uu___212_10492.admitted_iface);
       expect_typ = (uu___212_10492.expect_typ);
       docs = uu____10504;
       remaining_iface_decls = (uu___212_10492.remaining_iface_decls);
       syntax_only = (uu___212_10492.syntax_only);
       ds_hooks = (uu___212_10492.ds_hooks)
     })
let pop: Prims.unit -> env =
  fun uu____10510  ->
    let uu____10511 = FStar_ST.op_Bang stack in
    match uu____10511 with
    | env::tl1 ->
        (pop_record_cache (); FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____10620 -> failwith "Impossible: Too many pops"
let export_interface: FStar_Ident.lident -> env -> env =
  fun m  ->
    fun env  ->
      let sigelt_in_m se =
        match FStar_Syntax_Util.lids_of_sigelt se with
        | l::uu____10636 -> l.FStar_Ident.nsstr = m.FStar_Ident.str
        | uu____10639 -> false in
      let sm = sigmap env in
      let env1 = pop () in
      let keys = FStar_Util.smap_keys sm in
      let sm' = sigmap env1 in
      FStar_All.pipe_right keys
        (FStar_List.iter
           (fun k  ->
              let uu____10673 = FStar_Util.smap_try_find sm' k in
              match uu____10673 with
              | FStar_Pervasives_Native.Some (se,true ) when sigelt_in_m se
                  ->
                  (FStar_Util.smap_remove sm' k;
                   (let se1 =
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t) ->
                          let uu___213_10698 = se in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (uu___213_10698.FStar_Syntax_Syntax.sigel);
                            FStar_Syntax_Syntax.sigrng =
                              (uu___213_10698.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (FStar_Syntax_Syntax.Assumption ::
                              (se.FStar_Syntax_Syntax.sigquals));
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___213_10698.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___213_10698.FStar_Syntax_Syntax.sigattrs)
                          }
                      | uu____10699 -> se in
                    FStar_Util.smap_add sm' k (se1, false)))
              | uu____10704 -> ()));
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
      let uu____10789 =
        let uu____10792 = e Exported_id_term_type in
        FStar_ST.op_Bang uu____10792 in
      FStar_Util.set_elements uu____10789 in
    let fields =
      let uu____11039 =
        let uu____11042 = e Exported_id_field in FStar_ST.op_Bang uu____11042 in
      FStar_Util.set_elements uu____11039 in
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
          let uu____11319 =
            FStar_Util.as_set e1.exported_id_terms FStar_Util.compare in
          FStar_Util.mk_ref uu____11319 in
        let fields =
          let uu____11329 =
            FStar_Util.as_set e1.exported_id_fields FStar_Util.compare in
          FStar_Util.mk_ref uu____11329 in
        (fun uu___191_11334  ->
           match uu___191_11334 with
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
  'Auu____11447 .
    'Auu____11447 Prims.list FStar_Pervasives_Native.option ->
      'Auu____11447 Prims.list FStar_ST.ref
  =
  fun uu___192_11459  ->
    match uu___192_11459 with
    | FStar_Pervasives_Native.None  -> FStar_Util.mk_ref []
    | FStar_Pervasives_Native.Some l -> FStar_Util.mk_ref l
let inclusion_info: env -> FStar_Ident.lident -> module_inclusion_info =
  fun env  ->
    fun l  ->
      let mname = FStar_Ident.string_of_lid l in
      let as_ids_opt m =
        let uu____11494 = FStar_Util.smap_try_find m mname in
        FStar_Util.map_opt uu____11494 as_exported_ids in
      let uu____11497 = as_ids_opt env.exported_ids in
      let uu____11500 = as_ids_opt env.trans_exported_ids in
      let uu____11503 =
        let uu____11508 = FStar_Util.smap_try_find env.includes mname in
        FStar_Util.map_opt uu____11508 (fun r  -> FStar_ST.op_Bang r) in
      {
        mii_exported_ids = uu____11497;
        mii_trans_exported_ids = uu____11500;
        mii_includes = uu____11503
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
                let convert_kind uu___193_11648 =
                  match uu___193_11648 with
                  | FStar_Parser_Dep.Open_namespace  -> Open_namespace
                  | FStar_Parser_Dep.Open_module  -> Open_module in
                FStar_List.map
                  (fun uu____11660  ->
                     match uu____11660 with
                     | (lid,kind) -> (lid, (convert_kind kind))) auto_open in
              let namespace_of_module =
                if
                  (FStar_List.length mname.FStar_Ident.ns) >
                    (Prims.parse_int "0")
                then
                  let uu____11684 =
                    let uu____11689 =
                      FStar_Ident.lid_of_ids mname.FStar_Ident.ns in
                    (uu____11689, Open_namespace) in
                  [uu____11684]
                else [] in
              let auto_open2 =
                FStar_List.append namespace_of_module
                  (FStar_List.rev auto_open1) in
              (let uu____11719 = as_exported_id_set mii.mii_exported_ids in
               FStar_Util.smap_add env1.exported_ids mname.FStar_Ident.str
                 uu____11719);
              (match () with
               | () ->
                   ((let uu____11735 =
                       as_exported_id_set mii.mii_trans_exported_ids in
                     FStar_Util.smap_add env1.trans_exported_ids
                       mname.FStar_Ident.str uu____11735);
                    (match () with
                     | () ->
                         ((let uu____11751 = as_includes mii.mii_includes in
                           FStar_Util.smap_add env1.includes
                             mname.FStar_Ident.str uu____11751);
                          (match () with
                           | () ->
                               let env' =
                                 let uu___214_11775 = env1 in
                                 let uu____11776 =
                                   FStar_List.map
                                     (fun x  -> Open_module_or_namespace x)
                                     auto_open2 in
                                 {
                                   curmodule =
                                     (FStar_Pervasives_Native.Some mname);
                                   curmonad = (uu___214_11775.curmonad);
                                   modules = (uu___214_11775.modules);
                                   scope_mods = uu____11776;
                                   exported_ids =
                                     (uu___214_11775.exported_ids);
                                   trans_exported_ids =
                                     (uu___214_11775.trans_exported_ids);
                                   includes = (uu___214_11775.includes);
                                   sigaccum = (uu___214_11775.sigaccum);
                                   sigmap = (env1.sigmap);
                                   iface = intf;
                                   admitted_iface = admitted;
                                   expect_typ = (uu___214_11775.expect_typ);
                                   docs = (uu___214_11775.docs);
                                   remaining_iface_decls =
                                     (uu___214_11775.remaining_iface_decls);
                                   syntax_only = (uu___214_11775.syntax_only);
                                   ds_hooks = (uu___214_11775.ds_hooks)
                                 } in
                               (FStar_List.iter
                                  (fun op  ->
                                     (env1.ds_hooks).ds_push_open_hook env'
                                       op) (FStar_List.rev auto_open2);
                                env')))))) in
            let uu____11788 =
              FStar_All.pipe_right env.modules
                (FStar_Util.find_opt
                   (fun uu____11814  ->
                      match uu____11814 with
                      | (l,uu____11820) -> FStar_Ident.lid_equals l mname)) in
            match uu____11788 with
            | FStar_Pervasives_Native.None  ->
                let uu____11829 = prep env in (uu____11829, false)
            | FStar_Pervasives_Native.Some (uu____11830,m) ->
                ((let uu____11837 =
                    (let uu____11840 = FStar_Options.interactive () in
                     Prims.op_Negation uu____11840) &&
                      ((Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)
                         || intf) in
                  if uu____11837
                  then
                    let uu____11841 =
                      let uu____11842 =
                        let uu____11847 =
                          FStar_Util.format1
                            "Duplicate module or interface name: %s"
                            mname.FStar_Ident.str in
                        (uu____11847, (FStar_Ident.range_of_lid mname)) in
                      FStar_Errors.Error uu____11842 in
                    FStar_Exn.raise uu____11841
                  else ());
                 (let uu____11849 =
                    let uu____11850 = push env in prep uu____11850 in
                  (uu____11849, true)))
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
          let uu___215_11860 = env in
          {
            curmodule = (uu___215_11860.curmodule);
            curmonad = (FStar_Pervasives_Native.Some mname);
            modules = (uu___215_11860.modules);
            scope_mods = (uu___215_11860.scope_mods);
            exported_ids = (uu___215_11860.exported_ids);
            trans_exported_ids = (uu___215_11860.trans_exported_ids);
            includes = (uu___215_11860.includes);
            sigaccum = (uu___215_11860.sigaccum);
            sigmap = (uu___215_11860.sigmap);
            iface = (uu___215_11860.iface);
            admitted_iface = (uu___215_11860.admitted_iface);
            expect_typ = (uu___215_11860.expect_typ);
            docs = (uu___215_11860.docs);
            remaining_iface_decls = (uu___215_11860.remaining_iface_decls);
            syntax_only = (uu___215_11860.syntax_only);
            ds_hooks = (uu___215_11860.ds_hooks)
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
        let uu____11891 = lookup lid in
        match uu____11891 with
        | FStar_Pervasives_Native.None  ->
            let opened_modules =
              FStar_List.map
                (fun uu____11904  ->
                   match uu____11904 with
                   | (lid1,uu____11910) -> FStar_Ident.text_of_lid lid1)
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
                   let uu____11915 =
                     FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
                   FStar_Ident.set_lid_range uu____11915
                     (FStar_Ident.range_of_lid lid) in
                 let uu____11916 = resolve_module_name env modul true in
                 match uu____11916 with
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
      let uu____11950 = lookup id in
      match uu____11950 with
      | FStar_Pervasives_Native.None  ->
          FStar_Exn.raise
            (FStar_Errors.Error
               ((Prims.strcat "Identifier not found ["
                   (Prims.strcat id.FStar_Ident.idText "]")),
                 (id.FStar_Ident.idRange)))
      | FStar_Pervasives_Native.Some r -> r