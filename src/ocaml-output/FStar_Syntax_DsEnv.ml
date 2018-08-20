open Prims
type local_binding =
  (FStar_Ident.ident, FStar_Syntax_Syntax.bv, Prims.bool)
    FStar_Pervasives_Native.tuple3
type rec_binding =
  (FStar_Ident.ident, FStar_Ident.lid, FStar_Syntax_Syntax.delta_depth)
    FStar_Pervasives_Native.tuple3
type module_abbrev =
  (FStar_Ident.ident, FStar_Ident.lident) FStar_Pervasives_Native.tuple2
type open_kind =
  | Open_module 
  | Open_namespace 
let (uu___is_Open_module : open_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | Open_module -> true | uu____22 -> false
let (uu___is_Open_namespace : open_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | Open_namespace -> true | uu____28 -> false
type open_module_or_namespace =
  (FStar_Ident.lident, open_kind) FStar_Pervasives_Native.tuple2
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
  is_record: Prims.bool }
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
  | Record_or_dc of record_or_dc 
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
type string_set = Prims.string FStar_Util.set
type exported_id_kind =
  | Exported_id_term_type 
  | Exported_id_field 
let (uu___is_Exported_id_term_type : exported_id_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | Exported_id_term_type -> true | uu____304 -> false
let (uu___is_Exported_id_field : exported_id_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | Exported_id_field -> true | uu____310 -> false
type exported_id_set = exported_id_kind -> string_set FStar_ST.ref
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
  ds_hooks: dsenv_hooks ;
  dep_graph: FStar_Parser_Dep.deps }
and dsenv_hooks =
  {
  ds_push_open_hook: env -> open_module_or_namespace -> unit ;
  ds_push_include_hook: env -> FStar_Ident.lident -> unit ;
  ds_push_module_abbrev_hook:
    env -> FStar_Ident.ident -> FStar_Ident.lident -> unit }
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
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;
        dep_graph = __fname__dep_graph;_} -> __fname__curmodule
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
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;
        dep_graph = __fname__dep_graph;_} -> __fname__curmonad
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
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;
        dep_graph = __fname__dep_graph;_} -> __fname__modules
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
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;
        dep_graph = __fname__dep_graph;_} -> __fname__scope_mods
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
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;
        dep_graph = __fname__dep_graph;_} -> __fname__exported_ids
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
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;
        dep_graph = __fname__dep_graph;_} -> __fname__trans_exported_ids
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
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;
        dep_graph = __fname__dep_graph;_} -> __fname__includes
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
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;
        dep_graph = __fname__dep_graph;_} -> __fname__sigaccum
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
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;
        dep_graph = __fname__dep_graph;_} -> __fname__sigmap
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
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;
        dep_graph = __fname__dep_graph;_} -> __fname__iface
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
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;
        dep_graph = __fname__dep_graph;_} -> __fname__admitted_iface
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
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;
        dep_graph = __fname__dep_graph;_} -> __fname__expect_typ
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
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;
        dep_graph = __fname__dep_graph;_} -> __fname__docs
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
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;
        dep_graph = __fname__dep_graph;_} -> __fname__remaining_iface_decls
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
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;
        dep_graph = __fname__dep_graph;_} -> __fname__syntax_only
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
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;
        dep_graph = __fname__dep_graph;_} -> __fname__ds_hooks
let (__proj__Mkenv__item__dep_graph : env -> FStar_Parser_Dep.deps) =
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
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;
        dep_graph = __fname__dep_graph;_} -> __fname__dep_graph
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
type 'a withenv = env -> ('a, env) FStar_Pervasives_Native.tuple2
let (default_ds_hooks : dsenv_hooks) =
  {
    ds_push_open_hook = (fun uu____1808 -> fun uu____1809 -> ());
    ds_push_include_hook = (fun uu____1812 -> fun uu____1813 -> ());
    ds_push_module_abbrev_hook =
      (fun uu____1817 -> fun uu____1818 -> fun uu____1819 -> ())
  }
type foundname =
  | Term_name of (FStar_Syntax_Syntax.typ, Prims.bool,
  FStar_Syntax_Syntax.attribute Prims.list) FStar_Pervasives_Native.tuple3 
  | Eff_name of (FStar_Syntax_Syntax.sigelt, FStar_Ident.lident)
  FStar_Pervasives_Native.tuple2 
let (uu___is_Term_name : foundname -> Prims.bool) =
  fun projectee ->
    match projectee with | Term_name _0 -> true | uu____1856 -> false
let (__proj__Term_name__item___0 :
  foundname ->
    (FStar_Syntax_Syntax.typ, Prims.bool,
      FStar_Syntax_Syntax.attribute Prims.list)
      FStar_Pervasives_Native.tuple3)
  = fun projectee -> match projectee with | Term_name _0 -> _0
let (uu___is_Eff_name : foundname -> Prims.bool) =
  fun projectee ->
    match projectee with | Eff_name _0 -> true | uu____1898 -> false
let (__proj__Eff_name__item___0 :
  foundname ->
    (FStar_Syntax_Syntax.sigelt, FStar_Ident.lident)
      FStar_Pervasives_Native.tuple2)
  = fun projectee -> match projectee with | Eff_name _0 -> _0
let (set_iface : env -> Prims.bool -> env) =
  fun env ->
    fun b ->
      let uu___198_1928 = env in
      {
        curmodule = (uu___198_1928.curmodule);
        curmonad = (uu___198_1928.curmonad);
        modules = (uu___198_1928.modules);
        scope_mods = (uu___198_1928.scope_mods);
        exported_ids = (uu___198_1928.exported_ids);
        trans_exported_ids = (uu___198_1928.trans_exported_ids);
        includes = (uu___198_1928.includes);
        sigaccum = (uu___198_1928.sigaccum);
        sigmap = (uu___198_1928.sigmap);
        iface = b;
        admitted_iface = (uu___198_1928.admitted_iface);
        expect_typ = (uu___198_1928.expect_typ);
        docs = (uu___198_1928.docs);
        remaining_iface_decls = (uu___198_1928.remaining_iface_decls);
        syntax_only = (uu___198_1928.syntax_only);
        ds_hooks = (uu___198_1928.ds_hooks);
        dep_graph = (uu___198_1928.dep_graph)
      }
let (iface : env -> Prims.bool) = fun e -> e.iface
let (set_admitted_iface : env -> Prims.bool -> env) =
  fun e ->
    fun b ->
      let uu___199_1944 = e in
      {
        curmodule = (uu___199_1944.curmodule);
        curmonad = (uu___199_1944.curmonad);
        modules = (uu___199_1944.modules);
        scope_mods = (uu___199_1944.scope_mods);
        exported_ids = (uu___199_1944.exported_ids);
        trans_exported_ids = (uu___199_1944.trans_exported_ids);
        includes = (uu___199_1944.includes);
        sigaccum = (uu___199_1944.sigaccum);
        sigmap = (uu___199_1944.sigmap);
        iface = (uu___199_1944.iface);
        admitted_iface = b;
        expect_typ = (uu___199_1944.expect_typ);
        docs = (uu___199_1944.docs);
        remaining_iface_decls = (uu___199_1944.remaining_iface_decls);
        syntax_only = (uu___199_1944.syntax_only);
        ds_hooks = (uu___199_1944.ds_hooks);
        dep_graph = (uu___199_1944.dep_graph)
      }
let (admitted_iface : env -> Prims.bool) = fun e -> e.admitted_iface
let (set_expect_typ : env -> Prims.bool -> env) =
  fun e ->
    fun b ->
      let uu___200_1960 = e in
      {
        curmodule = (uu___200_1960.curmodule);
        curmonad = (uu___200_1960.curmonad);
        modules = (uu___200_1960.modules);
        scope_mods = (uu___200_1960.scope_mods);
        exported_ids = (uu___200_1960.exported_ids);
        trans_exported_ids = (uu___200_1960.trans_exported_ids);
        includes = (uu___200_1960.includes);
        sigaccum = (uu___200_1960.sigaccum);
        sigmap = (uu___200_1960.sigmap);
        iface = (uu___200_1960.iface);
        admitted_iface = (uu___200_1960.admitted_iface);
        expect_typ = b;
        docs = (uu___200_1960.docs);
        remaining_iface_decls = (uu___200_1960.remaining_iface_decls);
        syntax_only = (uu___200_1960.syntax_only);
        ds_hooks = (uu___200_1960.ds_hooks);
        dep_graph = (uu___200_1960.dep_graph)
      }
let (expect_typ : env -> Prims.bool) = fun e -> e.expect_typ
let (all_exported_id_kinds : exported_id_kind Prims.list) =
  [Exported_id_field; Exported_id_term_type]
let (transitive_exported_ids :
  env -> FStar_Ident.lident -> Prims.string Prims.list) =
  fun env ->
    fun lid ->
      let module_name = FStar_Ident.string_of_lid lid in
      let uu____1981 =
        FStar_Util.smap_try_find env.trans_exported_ids module_name in
      match uu____1981 with
      | FStar_Pervasives_Native.None -> []
      | FStar_Pervasives_Native.Some exported_id_set ->
          let uu____1992 =
            let uu____1995 = exported_id_set Exported_id_term_type in
            FStar_ST.op_Bang uu____1995 in
          FStar_All.pipe_right uu____1992 FStar_Util.set_elements
let (open_modules :
  env ->
    (FStar_Ident.lident, FStar_Syntax_Syntax.modul)
      FStar_Pervasives_Native.tuple2 Prims.list)
  = fun e -> e.modules
let (open_modules_and_namespaces : env -> FStar_Ident.lident Prims.list) =
  fun env ->
    FStar_List.filter_map
      (fun uu___165_2131 ->
         match uu___165_2131 with
         | Open_module_or_namespace (lid, _info) ->
             FStar_Pervasives_Native.Some lid
         | uu____2136 -> FStar_Pervasives_Native.None) env.scope_mods
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun e ->
    fun l ->
      let uu___201_2147 = e in
      {
        curmodule = (FStar_Pervasives_Native.Some l);
        curmonad = (uu___201_2147.curmonad);
        modules = (uu___201_2147.modules);
        scope_mods = (uu___201_2147.scope_mods);
        exported_ids = (uu___201_2147.exported_ids);
        trans_exported_ids = (uu___201_2147.trans_exported_ids);
        includes = (uu___201_2147.includes);
        sigaccum = (uu___201_2147.sigaccum);
        sigmap = (uu___201_2147.sigmap);
        iface = (uu___201_2147.iface);
        admitted_iface = (uu___201_2147.admitted_iface);
        expect_typ = (uu___201_2147.expect_typ);
        docs = (uu___201_2147.docs);
        remaining_iface_decls = (uu___201_2147.remaining_iface_decls);
        syntax_only = (uu___201_2147.syntax_only);
        ds_hooks = (uu___201_2147.ds_hooks);
        dep_graph = (uu___201_2147.dep_graph)
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
      let uu____2168 =
        FStar_All.pipe_right env.remaining_iface_decls
          (FStar_List.tryFind
             (fun uu____2202 ->
                match uu____2202 with
                | (m, uu____2210) -> FStar_Ident.lid_equals l m)) in
      match uu____2168 with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (uu____2227, decls) ->
          FStar_Pervasives_Native.Some decls
let (set_iface_decls :
  env -> FStar_Ident.lident -> FStar_Parser_AST.decl Prims.list -> env) =
  fun env ->
    fun l ->
      fun ds ->
        let uu____2260 =
          FStar_List.partition
            (fun uu____2290 ->
               match uu____2290 with
               | (m, uu____2298) -> FStar_Ident.lid_equals l m)
            env.remaining_iface_decls in
        match uu____2260 with
        | (uu____2303, rest) ->
            let uu___202_2337 = env in
            {
              curmodule = (uu___202_2337.curmodule);
              curmonad = (uu___202_2337.curmonad);
              modules = (uu___202_2337.modules);
              scope_mods = (uu___202_2337.scope_mods);
              exported_ids = (uu___202_2337.exported_ids);
              trans_exported_ids = (uu___202_2337.trans_exported_ids);
              includes = (uu___202_2337.includes);
              sigaccum = (uu___202_2337.sigaccum);
              sigmap = (uu___202_2337.sigmap);
              iface = (uu___202_2337.iface);
              admitted_iface = (uu___202_2337.admitted_iface);
              expect_typ = (uu___202_2337.expect_typ);
              docs = (uu___202_2337.docs);
              remaining_iface_decls = ((l, ds) :: rest);
              syntax_only = (uu___202_2337.syntax_only);
              ds_hooks = (uu___202_2337.ds_hooks);
              dep_graph = (uu___202_2337.dep_graph)
            }
let (qual : FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident) =
  FStar_Syntax_Util.qual_id
let (qualify : env -> FStar_Ident.ident -> FStar_Ident.lident) =
  fun env ->
    fun id1 ->
      match env.curmonad with
      | FStar_Pervasives_Native.None ->
          let uu____2364 = current_module env in qual uu____2364 id1
      | FStar_Pervasives_Native.Some monad ->
          let uu____2366 =
            let uu____2367 = current_module env in qual uu____2367 monad in
          FStar_Syntax_Util.mk_field_projector_name_from_ident uu____2366 id1
let (syntax_only : env -> Prims.bool) = fun env -> env.syntax_only
let (set_syntax_only : env -> Prims.bool -> env) =
  fun env ->
    fun b ->
      let uu___203_2383 = env in
      {
        curmodule = (uu___203_2383.curmodule);
        curmonad = (uu___203_2383.curmonad);
        modules = (uu___203_2383.modules);
        scope_mods = (uu___203_2383.scope_mods);
        exported_ids = (uu___203_2383.exported_ids);
        trans_exported_ids = (uu___203_2383.trans_exported_ids);
        includes = (uu___203_2383.includes);
        sigaccum = (uu___203_2383.sigaccum);
        sigmap = (uu___203_2383.sigmap);
        iface = (uu___203_2383.iface);
        admitted_iface = (uu___203_2383.admitted_iface);
        expect_typ = (uu___203_2383.expect_typ);
        docs = (uu___203_2383.docs);
        remaining_iface_decls = (uu___203_2383.remaining_iface_decls);
        syntax_only = b;
        ds_hooks = (uu___203_2383.ds_hooks);
        dep_graph = (uu___203_2383.dep_graph)
      }
let (ds_hooks : env -> dsenv_hooks) = fun env -> env.ds_hooks
let (set_ds_hooks : env -> dsenv_hooks -> env) =
  fun env ->
    fun hooks ->
      let uu___204_2399 = env in
      {
        curmodule = (uu___204_2399.curmodule);
        curmonad = (uu___204_2399.curmonad);
        modules = (uu___204_2399.modules);
        scope_mods = (uu___204_2399.scope_mods);
        exported_ids = (uu___204_2399.exported_ids);
        trans_exported_ids = (uu___204_2399.trans_exported_ids);
        includes = (uu___204_2399.includes);
        sigaccum = (uu___204_2399.sigaccum);
        sigmap = (uu___204_2399.sigmap);
        iface = (uu___204_2399.iface);
        admitted_iface = (uu___204_2399.admitted_iface);
        expect_typ = (uu___204_2399.expect_typ);
        docs = (uu___204_2399.docs);
        remaining_iface_decls = (uu___204_2399.remaining_iface_decls);
        syntax_only = (uu___204_2399.syntax_only);
        ds_hooks = hooks;
        dep_graph = (uu___204_2399.dep_graph)
      }
let new_sigmap : 'Auu____2404 . unit -> 'Auu____2404 FStar_Util.smap =
  fun uu____2411 -> FStar_Util.smap_create (Prims.parse_int "100")
let (empty_env : FStar_Parser_Dep.deps -> env) =
  fun deps ->
    let uu____2417 = new_sigmap () in
    let uu____2422 = new_sigmap () in
    let uu____2427 = new_sigmap () in
    let uu____2438 = new_sigmap () in
    let uu____2449 = new_sigmap () in
    {
      curmodule = FStar_Pervasives_Native.None;
      curmonad = FStar_Pervasives_Native.None;
      modules = [];
      scope_mods = [];
      exported_ids = uu____2417;
      trans_exported_ids = uu____2422;
      includes = uu____2427;
      sigaccum = [];
      sigmap = uu____2438;
      iface = false;
      admitted_iface = false;
      expect_typ = false;
      docs = uu____2449;
      remaining_iface_decls = [];
      syntax_only = false;
      ds_hooks = default_ds_hooks;
      dep_graph = deps
    }
let (dep_graph : env -> FStar_Parser_Dep.deps) = fun env -> env.dep_graph
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun env ->
    fun ds ->
      let uu___205_2477 = env in
      {
        curmodule = (uu___205_2477.curmodule);
        curmonad = (uu___205_2477.curmonad);
        modules = (uu___205_2477.modules);
        scope_mods = (uu___205_2477.scope_mods);
        exported_ids = (uu___205_2477.exported_ids);
        trans_exported_ids = (uu___205_2477.trans_exported_ids);
        includes = (uu___205_2477.includes);
        sigaccum = (uu___205_2477.sigaccum);
        sigmap = (uu___205_2477.sigmap);
        iface = (uu___205_2477.iface);
        admitted_iface = (uu___205_2477.admitted_iface);
        expect_typ = (uu___205_2477.expect_typ);
        docs = (uu___205_2477.docs);
        remaining_iface_decls = (uu___205_2477.remaining_iface_decls);
        syntax_only = (uu___205_2477.syntax_only);
        ds_hooks = (uu___205_2477.ds_hooks);
        dep_graph = ds
      }
let (sigmap :
  env ->
    (FStar_Syntax_Syntax.sigelt, Prims.bool) FStar_Pervasives_Native.tuple2
      FStar_Util.smap)
  = fun env -> env.sigmap
let (has_all_in_scope : env -> Prims.bool) =
  fun env ->
    FStar_List.existsb
      (fun uu____2501 ->
         match uu____2501 with
         | (m, uu____2507) ->
             FStar_Ident.lid_equals m FStar_Parser_Const.all_lid) env.modules
let (set_bv_range :
  FStar_Syntax_Syntax.bv -> FStar_Range.range -> FStar_Syntax_Syntax.bv) =
  fun bv ->
    fun r ->
      let id1 =
        let uu___206_2519 = bv.FStar_Syntax_Syntax.ppname in
        {
          FStar_Ident.idText = (uu___206_2519.FStar_Ident.idText);
          FStar_Ident.idRange = r
        } in
      let uu___207_2520 = bv in
      {
        FStar_Syntax_Syntax.ppname = id1;
        FStar_Syntax_Syntax.index = (uu___207_2520.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = (uu___207_2520.FStar_Syntax_Syntax.sort)
      }
let (bv_to_name :
  FStar_Syntax_Syntax.bv -> FStar_Range.range -> FStar_Syntax_Syntax.term) =
  fun bv -> fun r -> FStar_Syntax_Syntax.bv_to_name (set_bv_range bv r)
let (unmangleMap :
  (Prims.string, Prims.string, FStar_Syntax_Syntax.delta_depth,
    FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple4 Prims.list)
  =
  [("op_ColonColon", "Cons", FStar_Syntax_Syntax.delta_constant,
     (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor));
  ("not", "op_Negation", FStar_Syntax_Syntax.delta_equational,
    FStar_Pervasives_Native.None)]
let (unmangleOpName :
  FStar_Ident.ident ->
    (FStar_Syntax_Syntax.term, Prims.bool) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option)
  =
  fun id1 ->
    let t =
      FStar_Util.find_map unmangleMap
        (fun uu____2613 ->
           match uu____2613 with
           | (x, y, dd, dq) ->
               if id1.FStar_Ident.idText = x
               then
                 let uu____2636 =
                   let uu____2637 =
                     FStar_Ident.lid_of_path ["Prims"; y]
                       id1.FStar_Ident.idRange in
                   FStar_Syntax_Syntax.fvar uu____2637 dd dq in
                 FStar_Pervasives_Native.Some uu____2636
               else FStar_Pervasives_Native.None) in
    match t with
    | FStar_Pervasives_Native.Some v1 ->
        FStar_Pervasives_Native.Some (v1, false)
    | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
type 'a cont_t =
  | Cont_ok of 'a 
  | Cont_fail 
  | Cont_ignore 
let uu___is_Cont_ok : 'a . 'a cont_t -> Prims.bool =
  fun projectee ->
    match projectee with | Cont_ok _0 -> true | uu____2684 -> false
let __proj__Cont_ok__item___0 : 'a . 'a cont_t -> 'a =
  fun projectee -> match projectee with | Cont_ok _0 -> _0
let uu___is_Cont_fail : 'a . 'a cont_t -> Prims.bool =
  fun projectee ->
    match projectee with | Cont_fail -> true | uu____2717 -> false
let uu___is_Cont_ignore : 'a . 'a cont_t -> Prims.bool =
  fun projectee ->
    match projectee with | Cont_ignore -> true | uu____2734 -> false
let option_of_cont :
  'a .
    (unit -> 'a FStar_Pervasives_Native.option) ->
      'a cont_t -> 'a FStar_Pervasives_Native.option
  =
  fun k_ignore ->
    fun uu___166_2762 ->
      match uu___166_2762 with
      | Cont_ok a -> FStar_Pervasives_Native.Some a
      | Cont_fail -> FStar_Pervasives_Native.None
      | Cont_ignore -> k_ignore ()
let find_in_record :
  'Auu____2780 .
    FStar_Ident.ident Prims.list ->
      FStar_Ident.ident ->
        record_or_dc ->
          (record_or_dc -> 'Auu____2780 cont_t) -> 'Auu____2780 cont_t
  =
  fun ns ->
    fun id1 ->
      fun record ->
        fun cont ->
          let typename' =
            FStar_Ident.lid_of_ids
              (FStar_List.append ns [(record.typename).FStar_Ident.ident]) in
          let uu____2817 = FStar_Ident.lid_equals typename' record.typename in
          if uu____2817
          then
            let fname =
              FStar_Ident.lid_of_ids
                (FStar_List.append (record.typename).FStar_Ident.ns [id1]) in
            let find1 =
              FStar_Util.find_map record.fields
                (fun uu____2831 ->
                   match uu____2831 with
                   | (f, uu____2839) ->
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
  fun uu___167_2901 ->
    match uu___167_2901 with
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
              let rec aux uu___168_2972 =
                match uu___168_2972 with
                | [] -> find_in_module_default
                | modul::q ->
                    let mname = modul.FStar_Ident.str in
                    let not_shadowed =
                      let uu____2983 = get_exported_id_set env mname in
                      match uu____2983 with
                      | FStar_Pervasives_Native.None -> true
                      | FStar_Pervasives_Native.Some mex ->
                          let mexports =
                            let uu____3008 = mex eikind in
                            FStar_ST.op_Bang uu____3008 in
                          FStar_Util.set_mem idstr mexports in
                    let mincludes =
                      let uu____3122 =
                        FStar_Util.smap_try_find env.includes mname in
                      match uu____3122 with
                      | FStar_Pervasives_Native.None -> []
                      | FStar_Pervasives_Native.Some minc ->
                          FStar_ST.op_Bang minc in
                    let look_into =
                      if not_shadowed
                      then
                        let uu____3198 = qual modul id1 in
                        find_in_module uu____3198
                      else Cont_ignore in
                    (match look_into with
                     | Cont_ignore -> aux (FStar_List.append mincludes q)
                     | uu____3202 -> look_into) in
              aux [ns]
let (is_exported_id_field : exported_id_kind -> Prims.bool) =
  fun uu___169_3209 ->
    match uu___169_3209 with
    | Exported_id_field -> true
    | uu____3210 -> false
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
                  let check_local_binding_id uu___170_3331 =
                    match uu___170_3331 with
                    | (id', uu____3333, uu____3334) ->
                        id'.FStar_Ident.idText = id1.FStar_Ident.idText in
                  let check_rec_binding_id uu___171_3340 =
                    match uu___171_3340 with
                    | (id', uu____3342, uu____3343) ->
                        id'.FStar_Ident.idText = id1.FStar_Ident.idText in
                  let curmod_ns =
                    let uu____3347 = current_module env in
                    FStar_Ident.ids_of_lid uu____3347 in
                  let proc uu___172_3355 =
                    match uu___172_3355 with
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
                        let uu____3363 = FStar_Ident.lid_of_ids curmod_ns in
                        find_in_module_with_includes Exported_id_field
                          (fun lid ->
                             let id2 = lid.FStar_Ident.ident in
                             find_in_record lid.FStar_Ident.ns id2 r k_record)
                          Cont_ignore env uu____3363 id1
                    | uu____3368 -> Cont_ignore in
                  let rec aux uu___173_3378 =
                    match uu___173_3378 with
                    | a::q ->
                        let uu____3387 = proc a in
                        option_of_cont (fun uu____3391 -> aux q) uu____3387
                    | [] ->
                        let uu____3392 = lookup_default_id Cont_fail id1 in
                        option_of_cont
                          (fun uu____3396 -> FStar_Pervasives_Native.None)
                          uu____3392 in
                  aux env.scope_mods
let found_local_binding :
  'Auu____3405 'Auu____3406 .
    FStar_Range.range ->
      ('Auu____3405, FStar_Syntax_Syntax.bv, 'Auu____3406)
        FStar_Pervasives_Native.tuple3 ->
        (FStar_Syntax_Syntax.term, 'Auu____3406)
          FStar_Pervasives_Native.tuple2
  =
  fun r ->
    fun uu____3426 ->
      match uu____3426 with
      | (id', x, mut) -> let uu____3436 = bv_to_name x r in (uu____3436, mut)
let find_in_module :
  'Auu____3447 .
    env ->
      FStar_Ident.lident ->
        (FStar_Ident.lident ->
           (FStar_Syntax_Syntax.sigelt, Prims.bool)
             FStar_Pervasives_Native.tuple2 -> 'Auu____3447)
          -> 'Auu____3447 -> 'Auu____3447
  =
  fun env ->
    fun lid ->
      fun k_global_def ->
        fun k_not_found ->
          let uu____3486 =
            FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str in
          match uu____3486 with
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
      let uu____3526 = unmangleOpName id1 in
      match uu____3526 with
      | FStar_Pervasives_Native.Some f -> FStar_Pervasives_Native.Some f
      | uu____3552 ->
          try_lookup_id'' env id1 Exported_id_term_type
            (fun r ->
               let uu____3566 = found_local_binding id1.FStar_Ident.idRange r in
               Cont_ok uu____3566) (fun uu____3576 -> Cont_fail)
            (fun uu____3582 -> Cont_ignore)
            (fun i ->
               find_in_module env i
                 (fun uu____3597 -> fun uu____3598 -> Cont_fail) Cont_ignore)
            (fun uu____3613 -> fun uu____3614 -> Cont_fail)
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
            | FStar_Pervasives_Native.Some uu____3693 ->
                let lid = qualify env id1 in
                let uu____3695 =
                  FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str in
                (match uu____3695 with
                 | FStar_Pervasives_Native.Some r ->
                     let uu____3719 = k_global_def lid r in
                     FStar_Pervasives_Native.Some uu____3719
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None)
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None in
          match find_in_monad with
          | FStar_Pervasives_Native.Some v1 -> v1
          | FStar_Pervasives_Native.None ->
              let lid =
                let uu____3742 = current_module env in qual uu____3742 id1 in
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
        let rec aux uu___174_3805 =
          match uu___174_3805 with
          | [] ->
              let uu____3810 = module_is_defined env lid in
              if uu____3810
              then FStar_Pervasives_Native.Some lid
              else FStar_Pervasives_Native.None
          | (Open_module_or_namespace (ns, Open_namespace))::q when honor_ns
              ->
              let new_lid =
                let uu____3819 =
                  let uu____3820 = FStar_Ident.path_of_lid ns in
                  let uu____3823 = FStar_Ident.path_of_lid lid in
                  FStar_List.append uu____3820 uu____3823 in
                let uu____3826 = FStar_Ident.range_of_lid lid in
                FStar_Ident.lid_of_path uu____3819 uu____3826 in
              let uu____3827 = module_is_defined env new_lid in
              if uu____3827
              then FStar_Pervasives_Native.Some new_lid
              else aux q
          | (Module_abbrev (name, modul))::uu____3833 when
              (nslen = (Prims.parse_int "0")) &&
                (name.FStar_Ident.idText =
                   (lid.FStar_Ident.ident).FStar_Ident.idText)
              -> FStar_Pervasives_Native.Some modul
          | uu____3840::q -> aux q in
        aux env.scope_mods
let (fail_if_curmodule :
  env -> FStar_Ident.lident -> FStar_Ident.lident -> unit) =
  fun env ->
    fun ns_original ->
      fun ns_resolved ->
        let uu____3859 =
          let uu____3860 = current_module env in
          FStar_Ident.lid_equals ns_resolved uu____3860 in
        if uu____3859
        then
          let uu____3861 =
            FStar_Ident.lid_equals ns_resolved FStar_Parser_Const.prims_lid in
          (if uu____3861
           then ()
           else
             (let uu____3863 =
                let uu____3868 =
                  FStar_Util.format1
                    "Reference %s to current module is forbidden (see GitHub issue #451)"
                    ns_original.FStar_Ident.str in
                (FStar_Errors.Fatal_ForbiddenReferenceToCurrentModule,
                  uu____3868) in
              let uu____3869 = FStar_Ident.range_of_lid ns_original in
              FStar_Errors.raise_error uu____3863 uu____3869))
        else ()
let (fail_if_qualified_by_curmodule : env -> FStar_Ident.lident -> unit) =
  fun env ->
    fun lid ->
      match lid.FStar_Ident.ns with
      | [] -> ()
      | uu____3881 ->
          let modul_orig = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          let uu____3885 = resolve_module_name env modul_orig true in
          (match uu____3885 with
           | FStar_Pervasives_Native.Some modul_res ->
               fail_if_curmodule env modul_orig modul_res
           | uu____3889 -> ())
let (is_open : env -> FStar_Ident.lident -> open_kind -> Prims.bool) =
  fun env ->
    fun lid ->
      fun open_kind ->
        FStar_List.existsb
          (fun uu___175_3910 ->
             match uu___175_3910 with
             | Open_module_or_namespace (ns, k) ->
                 (k = open_kind) && (FStar_Ident.lid_equals lid ns)
             | uu____3913 -> false) env.scope_mods
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
                 let uu____4032 = aux rev_ns_prefix ns_last_id in
                 FStar_All.pipe_right uu____4032
                   (FStar_Util.map_option
                      (fun uu____4082 ->
                         match uu____4082 with
                         | (stripped_ids, rev_kept_ids) ->
                             (stripped_ids, (id1 :: rev_kept_ids))))) in
        let do_shorten env1 ids1 =
          match FStar_List.rev ids1 with
          | [] -> ([], [])
          | ns_last_id::ns_rev_prefix ->
              let uu____4152 = aux ns_rev_prefix ns_last_id in
              (match uu____4152 with
               | FStar_Pervasives_Native.None -> ([], ids1)
               | FStar_Pervasives_Native.Some (stripped_ids, rev_kept_ids) ->
                   (stripped_ids, (FStar_List.rev rev_kept_ids))) in
        if is_full_path && ((FStar_List.length ids) > (Prims.parse_int "0"))
        then
          let uu____4213 =
            let uu____4216 = FStar_Ident.lid_of_ids ids in
            resolve_module_name env uu____4216 true in
          match uu____4213 with
          | FStar_Pervasives_Native.Some m when module_is_open env m ->
              (ids, [])
          | uu____4230 -> do_shorten env ids
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
                  | uu____4349::uu____4350 ->
                      let uu____4353 =
                        let uu____4356 =
                          let uu____4357 =
                            FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
                          let uu____4358 = FStar_Ident.range_of_lid lid in
                          FStar_Ident.set_lid_range uu____4357 uu____4358 in
                        resolve_module_name env uu____4356 true in
                      (match uu____4353 with
                       | FStar_Pervasives_Native.None ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some modul ->
                           let uu____4362 =
                             find_in_module_with_includes eikind f_module
                               Cont_fail env modul lid.FStar_Ident.ident in
                           option_of_cont
                             (fun uu____4366 -> FStar_Pervasives_Native.None)
                             uu____4362)
                  | [] ->
                      try_lookup_id'' env lid.FStar_Ident.ident eikind
                        k_local_binding k_rec_binding k_record f_module
                        l_default
let cont_of_option :
  'a . 'a cont_t -> 'a FStar_Pervasives_Native.option -> 'a cont_t =
  fun k_none ->
    fun uu___176_4389 ->
      match uu___176_4389 with
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
              let uu____4505 = k_global_def lid1 def in
              cont_of_option k uu____4505 in
            let f_module lid' =
              let k = Cont_ignore in
              find_in_module env lid' (k_global_def' k) k in
            let l_default k i = lookup_default_id env i (k_global_def' k) k in
            resolve_in_open_namespaces'' env lid Exported_id_term_type
              (fun l ->
                 let uu____4541 = k_local_binding l in
                 cont_of_option Cont_fail uu____4541)
              (fun r ->
                 let uu____4547 = k_rec_binding r in
                 cont_of_option Cont_fail uu____4547)
              (fun uu____4551 -> Cont_ignore) f_module l_default
let (fv_qual_of_se :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option)
  =
  fun se ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____4561, uu____4562, uu____4563, l, uu____4565, uu____4566) ->
        let qopt =
          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
            (fun uu___177_4577 ->
               match uu___177_4577 with
               | FStar_Syntax_Syntax.RecordConstructor (uu____4580, fs) ->
                   FStar_Pervasives_Native.Some
                     (FStar_Syntax_Syntax.Record_ctor (l, fs))
               | uu____4592 -> FStar_Pervasives_Native.None) in
        (match qopt with
         | FStar_Pervasives_Native.None ->
             FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor
         | x -> x)
    | FStar_Syntax_Syntax.Sig_declare_typ
        (uu____4598, uu____4599, uu____4600) -> FStar_Pervasives_Native.None
    | uu____4601 -> FStar_Pervasives_Native.None
let (lb_fv :
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Ident.lident -> FStar_Syntax_Syntax.fv)
  =
  fun lbs ->
    fun lid ->
      let uu____4616 =
        FStar_Util.find_map lbs
          (fun lb ->
             let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
             let uu____4624 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
             if uu____4624
             then FStar_Pervasives_Native.Some fv
             else FStar_Pervasives_Native.None) in
      FStar_All.pipe_right uu____4616 FStar_Util.must
let (ns_of_lid_equals :
  FStar_Ident.lident -> FStar_Ident.lident -> Prims.bool) =
  fun lid ->
    fun ns ->
      (let uu____4642 =
         let uu____4643 = FStar_Ident.ids_of_lid ns in
         FStar_List.length uu____4643 in
       (FStar_List.length lid.FStar_Ident.ns) = uu____4642) &&
        (let uu____4651 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
         FStar_Ident.lid_equals uu____4651 ns)
let (delta_depth_of_declaration :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Syntax_Syntax.delta_depth)
  =
  fun lid ->
    fun quals ->
      let dd =
        let uu____4667 =
          (FStar_Syntax_Util.is_primop_lid lid) ||
            (FStar_All.pipe_right quals
               (FStar_Util.for_some
                  (fun uu___178_4672 ->
                     match uu___178_4672 with
                     | FStar_Syntax_Syntax.Projector uu____4673 -> true
                     | FStar_Syntax_Syntax.Discriminator uu____4678 -> true
                     | uu____4679 -> false))) in
        if uu____4667
        then FStar_Syntax_Syntax.delta_equational
        else FStar_Syntax_Syntax.delta_constant in
      let uu____4681 =
        (FStar_All.pipe_right quals
           (FStar_Util.for_some
              (fun uu___179_4685 ->
                 match uu___179_4685 with
                 | FStar_Syntax_Syntax.Abstract -> true
                 | uu____4686 -> false)))
          ||
          ((FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___180_4690 ->
                    match uu___180_4690 with
                    | FStar_Syntax_Syntax.Assumption -> true
                    | uu____4691 -> false)))
             &&
             (let uu____4693 =
                FStar_All.pipe_right quals
                  (FStar_Util.for_some
                     (fun uu___181_4697 ->
                        match uu___181_4697 with
                        | FStar_Syntax_Syntax.New -> true
                        | uu____4698 -> false)) in
              Prims.op_Negation uu____4693)) in
      if uu____4681 then FStar_Syntax_Syntax.Delta_abstract dd else dd
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
          let k_global_def source_lid uu___184_4741 =
            match uu___184_4741 with
            | (uu____4748, true) when exclude_interf ->
                FStar_Pervasives_Native.None
            | (se, uu____4750) ->
                (match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_inductive_typ uu____4753 ->
                     let uu____4770 =
                       let uu____4771 =
                         let uu____4780 =
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None in
                         (uu____4780, false,
                           (se.FStar_Syntax_Syntax.sigattrs)) in
                       Term_name uu____4771 in
                     FStar_Pervasives_Native.Some uu____4770
                 | FStar_Syntax_Syntax.Sig_datacon uu____4783 ->
                     let uu____4798 =
                       let uu____4799 =
                         let uu____4808 =
                           let uu____4809 = fv_qual_of_se se in
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.delta_constant uu____4809 in
                         (uu____4808, false,
                           (se.FStar_Syntax_Syntax.sigattrs)) in
                       Term_name uu____4799 in
                     FStar_Pervasives_Native.Some uu____4798
                 | FStar_Syntax_Syntax.Sig_let
                     ((uu____4814, lbs), uu____4816) ->
                     let fv = lb_fv lbs source_lid in
                     let uu____4826 =
                       let uu____4827 =
                         let uu____4836 =
                           FStar_Syntax_Syntax.fvar source_lid
                             fv.FStar_Syntax_Syntax.fv_delta
                             fv.FStar_Syntax_Syntax.fv_qual in
                         (uu____4836, false,
                           (se.FStar_Syntax_Syntax.sigattrs)) in
                       Term_name uu____4827 in
                     FStar_Pervasives_Native.Some uu____4826
                 | FStar_Syntax_Syntax.Sig_declare_typ
                     (lid1, uu____4840, uu____4841) ->
                     let quals = se.FStar_Syntax_Syntax.sigquals in
                     let uu____4845 =
                       any_val ||
                         (FStar_All.pipe_right quals
                            (FStar_Util.for_some
                               (fun uu___182_4849 ->
                                  match uu___182_4849 with
                                  | FStar_Syntax_Syntax.Assumption -> true
                                  | uu____4850 -> false))) in
                     if uu____4845
                     then
                       let lid2 =
                         let uu____4854 = FStar_Ident.range_of_lid source_lid in
                         FStar_Ident.set_lid_range lid1 uu____4854 in
                       let dd = delta_depth_of_declaration lid2 quals in
                       let uu____4856 =
                         FStar_Util.find_map quals
                           (fun uu___183_4861 ->
                              match uu___183_4861 with
                              | FStar_Syntax_Syntax.Reflectable refl_monad ->
                                  FStar_Pervasives_Native.Some refl_monad
                              | uu____4865 -> FStar_Pervasives_Native.None) in
                       (match uu____4856 with
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
                        | uu____4874 ->
                            let uu____4877 =
                              let uu____4878 =
                                let uu____4887 =
                                  let uu____4888 = fv_qual_of_se se in
                                  FStar_Syntax_Syntax.fvar lid2 dd uu____4888 in
                                (uu____4887, false,
                                  (se.FStar_Syntax_Syntax.sigattrs)) in
                              Term_name uu____4878 in
                            FStar_Pervasives_Native.Some uu____4877)
                     else FStar_Pervasives_Native.None
                 | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
                     let uu____4895 =
                       let uu____4896 =
                         let uu____4901 =
                           let uu____4902 =
                             FStar_Ident.range_of_lid source_lid in
                           FStar_Ident.set_lid_range
                             ne.FStar_Syntax_Syntax.mname uu____4902 in
                         (se, uu____4901) in
                       Eff_name uu____4896 in
                     FStar_Pervasives_Native.Some uu____4895
                 | FStar_Syntax_Syntax.Sig_new_effect ne ->
                     let uu____4904 =
                       let uu____4905 =
                         let uu____4910 =
                           let uu____4911 =
                             FStar_Ident.range_of_lid source_lid in
                           FStar_Ident.set_lid_range
                             ne.FStar_Syntax_Syntax.mname uu____4911 in
                         (se, uu____4910) in
                       Eff_name uu____4905 in
                     FStar_Pervasives_Native.Some uu____4904
                 | FStar_Syntax_Syntax.Sig_effect_abbrev uu____4912 ->
                     FStar_Pervasives_Native.Some (Eff_name (se, source_lid))
                 | FStar_Syntax_Syntax.Sig_splice (lids, t) ->
                     let uu____4931 =
                       let uu____4932 =
                         let uu____4941 =
                           FStar_Syntax_Syntax.fvar source_lid
                             (FStar_Syntax_Syntax.Delta_constant_at_level
                                (Prims.parse_int "1"))
                             FStar_Pervasives_Native.None in
                         (uu____4941, false, []) in
                       Term_name uu____4932 in
                     FStar_Pervasives_Native.Some uu____4931
                 | uu____4944 -> FStar_Pervasives_Native.None) in
          let k_local_binding r =
            let uu____4965 =
              let uu____4970 = FStar_Ident.range_of_lid lid in
              found_local_binding uu____4970 r in
            match uu____4965 with
            | (t, mut) ->
                FStar_Pervasives_Native.Some (Term_name (t, mut, [])) in
          let k_rec_binding uu____4990 =
            match uu____4990 with
            | (id1, l, dd) ->
                let uu____5002 =
                  let uu____5003 =
                    let uu____5012 =
                      let uu____5013 =
                        let uu____5014 = FStar_Ident.range_of_lid lid in
                        FStar_Ident.set_lid_range l uu____5014 in
                      FStar_Syntax_Syntax.fvar uu____5013 dd
                        FStar_Pervasives_Native.None in
                    (uu____5012, false, []) in
                  Term_name uu____5003 in
                FStar_Pervasives_Native.Some uu____5002 in
          let found_unmangled =
            match lid.FStar_Ident.ns with
            | [] ->
                let uu____5022 = unmangleOpName lid.FStar_Ident.ident in
                (match uu____5022 with
                 | FStar_Pervasives_Native.Some (t, mut) ->
                     FStar_Pervasives_Native.Some (Term_name (t, mut, []))
                 | uu____5039 -> FStar_Pervasives_Native.None)
            | uu____5046 -> FStar_Pervasives_Native.None in
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
        let uu____5081 = try_lookup_name true exclude_interf env lid in
        match uu____5081 with
        | FStar_Pervasives_Native.Some (Eff_name (o, l)) ->
            FStar_Pervasives_Native.Some (o, l)
        | uu____5096 -> FStar_Pervasives_Native.None
let (try_lookup_effect_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env ->
    fun l ->
      let uu____5115 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____5115 with
      | FStar_Pervasives_Native.Some (o, l1) ->
          FStar_Pervasives_Native.Some l1
      | uu____5130 -> FStar_Pervasives_Native.None
let (try_lookup_effect_name_and_attributes :
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident, FStar_Syntax_Syntax.cflags Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env ->
    fun l ->
      let uu____5155 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____5155 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____5171;
             FStar_Syntax_Syntax.sigquals = uu____5172;
             FStar_Syntax_Syntax.sigmeta = uu____5173;
             FStar_Syntax_Syntax.sigattrs = uu____5174;_},
           l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____5193;
             FStar_Syntax_Syntax.sigquals = uu____5194;
             FStar_Syntax_Syntax.sigmeta = uu____5195;
             FStar_Syntax_Syntax.sigattrs = uu____5196;_},
           l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (uu____5214, uu____5215, uu____5216, uu____5217, cattributes);
             FStar_Syntax_Syntax.sigrng = uu____5219;
             FStar_Syntax_Syntax.sigquals = uu____5220;
             FStar_Syntax_Syntax.sigmeta = uu____5221;
             FStar_Syntax_Syntax.sigattrs = uu____5222;_},
           l1)
          -> FStar_Pervasives_Native.Some (l1, cattributes)
      | uu____5244 -> FStar_Pervasives_Native.None
let (try_lookup_effect_defn :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.eff_decl FStar_Pervasives_Native.option)
  =
  fun env ->
    fun l ->
      let uu____5269 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____5269 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____5279;
             FStar_Syntax_Syntax.sigquals = uu____5280;
             FStar_Syntax_Syntax.sigmeta = uu____5281;
             FStar_Syntax_Syntax.sigattrs = uu____5282;_},
           uu____5283)
          -> FStar_Pervasives_Native.Some ne
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____5293;
             FStar_Syntax_Syntax.sigquals = uu____5294;
             FStar_Syntax_Syntax.sigmeta = uu____5295;
             FStar_Syntax_Syntax.sigattrs = uu____5296;_},
           uu____5297)
          -> FStar_Pervasives_Native.Some ne
      | uu____5306 -> FStar_Pervasives_Native.None
let (is_effect_name : env -> FStar_Ident.lident -> Prims.bool) =
  fun env ->
    fun lid ->
      let uu____5323 = try_lookup_effect_name env lid in
      match uu____5323 with
      | FStar_Pervasives_Native.None -> false
      | FStar_Pervasives_Native.Some uu____5326 -> true
let (try_lookup_root_effect_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env ->
    fun l ->
      let uu____5339 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____5339 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (l', uu____5349, uu____5350, uu____5351, uu____5352);
             FStar_Syntax_Syntax.sigrng = uu____5353;
             FStar_Syntax_Syntax.sigquals = uu____5354;
             FStar_Syntax_Syntax.sigmeta = uu____5355;
             FStar_Syntax_Syntax.sigattrs = uu____5356;_},
           uu____5357)
          ->
          let rec aux new_name =
            let uu____5378 =
              FStar_Util.smap_try_find (sigmap env) new_name.FStar_Ident.str in
            match uu____5378 with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (s, uu____5396) ->
                (match s.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
                     let uu____5404 =
                       let uu____5405 = FStar_Ident.range_of_lid l in
                       FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname
                         uu____5405 in
                     FStar_Pervasives_Native.Some uu____5404
                 | FStar_Syntax_Syntax.Sig_new_effect ne ->
                     let uu____5407 =
                       let uu____5408 = FStar_Ident.range_of_lid l in
                       FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname
                         uu____5408 in
                     FStar_Pervasives_Native.Some uu____5407
                 | FStar_Syntax_Syntax.Sig_effect_abbrev
                     (uu____5409, uu____5410, uu____5411, cmp, uu____5413) ->
                     let l'' = FStar_Syntax_Util.comp_effect_name cmp in
                     aux l''
                 | uu____5419 -> FStar_Pervasives_Native.None) in
          aux l'
      | FStar_Pervasives_Native.Some (uu____5420, l') ->
          FStar_Pervasives_Native.Some l'
      | uu____5426 -> FStar_Pervasives_Native.None
let (lookup_letbinding_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env ->
    fun lid ->
      let k_global_def lid1 uu___185_5463 =
        match uu___185_5463 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____5472, uu____5473, uu____5474);
             FStar_Syntax_Syntax.sigrng = uu____5475;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____5477;
             FStar_Syntax_Syntax.sigattrs = uu____5478;_},
           uu____5479) -> FStar_Pervasives_Native.Some quals
        | uu____5486 -> FStar_Pervasives_Native.None in
      let uu____5493 =
        resolve_in_open_namespaces' env lid
          (fun uu____5501 -> FStar_Pervasives_Native.None)
          (fun uu____5505 -> FStar_Pervasives_Native.None) k_global_def in
      match uu____5493 with
      | FStar_Pervasives_Native.Some quals -> quals
      | uu____5515 -> []
let (try_lookup_module :
  env ->
    FStar_Ident.path ->
      FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option)
  =
  fun env ->
    fun path ->
      let uu____5532 =
        FStar_List.tryFind
          (fun uu____5547 ->
             match uu____5547 with
             | (mlid, modul) ->
                 let uu____5554 = FStar_Ident.path_of_lid mlid in
                 uu____5554 = path) env.modules in
      match uu____5532 with
      | FStar_Pervasives_Native.Some (uu____5557, modul) ->
          FStar_Pervasives_Native.Some modul
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let (try_lookup_let :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env ->
    fun lid ->
      let k_global_def lid1 uu___186_5595 =
        match uu___186_5595 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               ((uu____5602, lbs), uu____5604);
             FStar_Syntax_Syntax.sigrng = uu____5605;
             FStar_Syntax_Syntax.sigquals = uu____5606;
             FStar_Syntax_Syntax.sigmeta = uu____5607;
             FStar_Syntax_Syntax.sigattrs = uu____5608;_},
           uu____5609) ->
            let fv = lb_fv lbs lid1 in
            let uu____5623 =
              FStar_Syntax_Syntax.fvar lid1 fv.FStar_Syntax_Syntax.fv_delta
                fv.FStar_Syntax_Syntax.fv_qual in
            FStar_Pervasives_Native.Some uu____5623
        | uu____5624 -> FStar_Pervasives_Native.None in
      resolve_in_open_namespaces' env lid
        (fun uu____5630 -> FStar_Pervasives_Native.None)
        (fun uu____5632 -> FStar_Pervasives_Native.None) k_global_def
let (try_lookup_definition :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env ->
    fun lid ->
      let k_global_def lid1 uu___187_5663 =
        match uu___187_5663 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               (lbs, uu____5673);
             FStar_Syntax_Syntax.sigrng = uu____5674;
             FStar_Syntax_Syntax.sigquals = uu____5675;
             FStar_Syntax_Syntax.sigmeta = uu____5676;
             FStar_Syntax_Syntax.sigattrs = uu____5677;_},
           uu____5678) ->
            FStar_Util.find_map (FStar_Pervasives_Native.snd lbs)
              (fun lb ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inr fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv lid1 ->
                     FStar_Pervasives_Native.Some
                       (lb.FStar_Syntax_Syntax.lbdef)
                 | uu____5701 -> FStar_Pervasives_Native.None)
        | uu____5708 -> FStar_Pervasives_Native.None in
      resolve_in_open_namespaces' env lid
        (fun uu____5718 -> FStar_Pervasives_Native.None)
        (fun uu____5722 -> FStar_Pervasives_Native.None) k_global_def
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
          let uu____5779 = try_lookup_name any_val exclude_interface env lid in
          match uu____5779 with
          | FStar_Pervasives_Native.Some (Term_name (e, mut, attrs)) ->
              FStar_Pervasives_Native.Some (e, mut, attrs)
          | uu____5809 -> FStar_Pervasives_Native.None
let (drop_attributes :
  (FStar_Syntax_Syntax.term, Prims.bool,
    FStar_Syntax_Syntax.attribute Prims.list) FStar_Pervasives_Native.tuple3
    FStar_Pervasives_Native.option ->
    (FStar_Syntax_Syntax.term, Prims.bool) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option)
  =
  fun x ->
    match x with
    | FStar_Pervasives_Native.Some (t, mut, uu____5865) ->
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
      let uu____5940 = try_lookup_lid_with_attributes env l in
      FStar_All.pipe_right uu____5940 drop_attributes
let (resolve_to_fully_qualified_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env ->
    fun l ->
      let uu____5979 = try_lookup_lid env l in
      match uu____5979 with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (e, uu____5993) ->
          let uu____5998 =
            let uu____5999 = FStar_Syntax_Subst.compress e in
            uu____5999.FStar_Syntax_Syntax.n in
          (match uu____5998 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               FStar_Pervasives_Native.Some
                 ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
           | uu____6005 -> FStar_Pervasives_Native.None)
let (shorten_lid' : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env ->
    fun lid ->
      let uu____6016 = shorten_module_path env lid.FStar_Ident.ns true in
      match uu____6016 with
      | (uu____6025, short) ->
          FStar_Ident.lid_of_ns_and_id short lid.FStar_Ident.ident
let (shorten_lid : env -> FStar_Ident.lid -> FStar_Ident.lid) =
  fun env ->
    fun lid ->
      match env.curmodule with
      | FStar_Pervasives_Native.None -> shorten_lid' env lid
      | uu____6045 ->
          let lid_without_ns =
            FStar_Ident.lid_of_ns_and_id [] lid.FStar_Ident.ident in
          let uu____6049 = resolve_to_fully_qualified_name env lid_without_ns in
          (match uu____6049 with
           | FStar_Pervasives_Native.Some lid' when
               lid'.FStar_Ident.str = lid.FStar_Ident.str -> lid_without_ns
           | uu____6053 -> shorten_lid' env lid)
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
        let uu___208_6087 = env in
        {
          curmodule = (uu___208_6087.curmodule);
          curmonad = (uu___208_6087.curmonad);
          modules = (uu___208_6087.modules);
          scope_mods = [];
          exported_ids = empty_exported_id_smap;
          trans_exported_ids = (uu___208_6087.trans_exported_ids);
          includes = empty_include_smap;
          sigaccum = (uu___208_6087.sigaccum);
          sigmap = (uu___208_6087.sigmap);
          iface = (uu___208_6087.iface);
          admitted_iface = (uu___208_6087.admitted_iface);
          expect_typ = (uu___208_6087.expect_typ);
          docs = (uu___208_6087.docs);
          remaining_iface_decls = (uu___208_6087.remaining_iface_decls);
          syntax_only = (uu___208_6087.syntax_only);
          ds_hooks = (uu___208_6087.ds_hooks);
          dep_graph = (uu___208_6087.dep_graph)
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
      let uu____6110 = try_lookup_lid_with_attributes_no_resolve env l in
      FStar_All.pipe_right uu____6110 drop_attributes
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
               (uu____6184, uu____6185, uu____6186);
             FStar_Syntax_Syntax.sigrng = uu____6187;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____6189;
             FStar_Syntax_Syntax.sigattrs = uu____6190;_},
           uu____6191) ->
            let uu____6196 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___188_6200 ->
                      match uu___188_6200 with
                      | FStar_Syntax_Syntax.Assumption -> true
                      | uu____6201 -> false)) in
            if uu____6196
            then
              let uu____6204 =
                FStar_Syntax_Syntax.lid_as_fv lid1
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None in
              FStar_Pervasives_Native.Some uu____6204
            else FStar_Pervasives_Native.None
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
               uu____6206;
             FStar_Syntax_Syntax.sigrng = uu____6207;
             FStar_Syntax_Syntax.sigquals = uu____6208;
             FStar_Syntax_Syntax.sigmeta = uu____6209;
             FStar_Syntax_Syntax.sigattrs = uu____6210;_},
           uu____6211) ->
            let qual1 = fv_qual_of_se (FStar_Pervasives_Native.fst se) in
            let uu____6233 =
              FStar_Syntax_Syntax.lid_as_fv lid1
                FStar_Syntax_Syntax.delta_constant qual1 in
            FStar_Pervasives_Native.Some uu____6233
        | uu____6234 -> FStar_Pervasives_Native.None in
      resolve_in_open_namespaces' env lid
        (fun uu____6240 -> FStar_Pervasives_Native.None)
        (fun uu____6242 -> FStar_Pervasives_Native.None) k_global_def
let (find_all_datacons :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident Prims.list FStar_Pervasives_Native.option)
  =
  fun env ->
    fun lid ->
      let k_global_def lid1 uu___189_6275 =
        match uu___189_6275 with
        | ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_inductive_typ
               (uu____6284, uu____6285, uu____6286, uu____6287, datas,
                uu____6289);
             FStar_Syntax_Syntax.sigrng = uu____6290;
             FStar_Syntax_Syntax.sigquals = uu____6291;
             FStar_Syntax_Syntax.sigmeta = uu____6292;
             FStar_Syntax_Syntax.sigattrs = uu____6293;_},
           uu____6294) -> FStar_Pervasives_Native.Some datas
        | uu____6309 -> FStar_Pervasives_Native.None in
      resolve_in_open_namespaces' env lid
        (fun uu____6319 -> FStar_Pervasives_Native.None)
        (fun uu____6323 -> FStar_Pervasives_Native.None) k_global_def
let (record_cache_aux_with_filter :
  (((unit -> unit, unit -> unit) FStar_Pervasives_Native.tuple2,
     ((unit -> (Prims.int, unit) FStar_Pervasives_Native.tuple2,
        Prims.int FStar_Pervasives_Native.option -> unit)
        FStar_Pervasives_Native.tuple2,
       (unit -> record_or_dc Prims.list, record_or_dc -> unit)
         FStar_Pervasives_Native.tuple2)
       FStar_Pervasives_Native.tuple2)
     FStar_Pervasives_Native.tuple2,
    unit -> unit) FStar_Pervasives_Native.tuple2)
  =
  let record_cache = FStar_Util.mk_ref [[]] in
  let push1 uu____6399 =
    let uu____6400 =
      let uu____6405 =
        let uu____6408 = FStar_ST.op_Bang record_cache in
        FStar_List.hd uu____6408 in
      let uu____6464 = FStar_ST.op_Bang record_cache in uu____6405 ::
        uu____6464 in
    FStar_ST.op_Colon_Equals record_cache uu____6400 in
  let pop1 uu____6574 =
    let uu____6575 =
      let uu____6580 = FStar_ST.op_Bang record_cache in
      FStar_List.tl uu____6580 in
    FStar_ST.op_Colon_Equals record_cache uu____6575 in
  let snapshot1 uu____6694 = FStar_Common.snapshot push1 record_cache () in
  let rollback1 depth = FStar_Common.rollback pop1 record_cache depth in
  let peek1 uu____6760 =
    let uu____6761 = FStar_ST.op_Bang record_cache in
    FStar_List.hd uu____6761 in
  let insert r =
    let uu____6823 =
      let uu____6828 = let uu____6831 = peek1 () in r :: uu____6831 in
      let uu____6834 =
        let uu____6839 = FStar_ST.op_Bang record_cache in
        FStar_List.tl uu____6839 in
      uu____6828 :: uu____6834 in
    FStar_ST.op_Colon_Equals record_cache uu____6823 in
  let filter1 uu____6951 =
    let rc = peek1 () in
    let filtered =
      FStar_List.filter (fun r -> Prims.op_Negation r.is_private_or_abstract)
        rc in
    let uu____6960 =
      let uu____6965 =
        let uu____6970 = FStar_ST.op_Bang record_cache in
        FStar_List.tl uu____6970 in
      filtered :: uu____6965 in
    FStar_ST.op_Colon_Equals record_cache uu____6960 in
  let aux = ((push1, pop1), ((snapshot1, rollback1), (peek1, insert))) in
  (aux, filter1)
let (record_cache_aux :
  ((unit -> unit, unit -> unit) FStar_Pervasives_Native.tuple2,
    ((unit -> (Prims.int, unit) FStar_Pervasives_Native.tuple2,
       Prims.int FStar_Pervasives_Native.option -> unit)
       FStar_Pervasives_Native.tuple2,
      (unit -> record_or_dc Prims.list, record_or_dc -> unit)
        FStar_Pervasives_Native.tuple2)
      FStar_Pervasives_Native.tuple2)
    FStar_Pervasives_Native.tuple2)
  = FStar_Pervasives_Native.fst record_cache_aux_with_filter
let (filter_record_cache : unit -> unit) =
  FStar_Pervasives_Native.snd record_cache_aux_with_filter
let (push_record_cache : unit -> unit) =
  FStar_Pervasives_Native.fst (FStar_Pervasives_Native.fst record_cache_aux)
let (pop_record_cache : unit -> unit) =
  FStar_Pervasives_Native.snd (FStar_Pervasives_Native.fst record_cache_aux)
let (snapshot_record_cache :
  unit -> (Prims.int, unit) FStar_Pervasives_Native.tuple2) =
  FStar_Pervasives_Native.fst
    (FStar_Pervasives_Native.fst
       (FStar_Pervasives_Native.snd record_cache_aux))
let (rollback_record_cache :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  FStar_Pervasives_Native.snd
    (FStar_Pervasives_Native.fst
       (FStar_Pervasives_Native.snd record_cache_aux))
let (peek_record_cache : unit -> record_or_dc Prims.list) =
  FStar_Pervasives_Native.fst
    (FStar_Pervasives_Native.snd
       (FStar_Pervasives_Native.snd record_cache_aux))
let (insert_record_cache : record_or_dc -> unit) =
  FStar_Pervasives_Native.snd
    (FStar_Pervasives_Native.snd
       (FStar_Pervasives_Native.snd record_cache_aux))
let (extract_record :
  env ->
    scope_mod Prims.list FStar_ST.ref -> FStar_Syntax_Syntax.sigelt -> unit)
  =
  fun e ->
    fun new_globs ->
      fun se ->
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_bundle (sigs, uu____7911) ->
            let is_record =
              FStar_Util.for_some
                (fun uu___190_7929 ->
                   match uu___190_7929 with
                   | FStar_Syntax_Syntax.RecordType uu____7930 -> true
                   | FStar_Syntax_Syntax.RecordConstructor uu____7939 -> true
                   | uu____7948 -> false) in
            let find_dc dc =
              FStar_All.pipe_right sigs
                (FStar_Util.find_opt
                   (fun uu___191_7972 ->
                      match uu___191_7972 with
                      | {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_datacon
                            (lid, uu____7974, uu____7975, uu____7976,
                             uu____7977, uu____7978);
                          FStar_Syntax_Syntax.sigrng = uu____7979;
                          FStar_Syntax_Syntax.sigquals = uu____7980;
                          FStar_Syntax_Syntax.sigmeta = uu____7981;
                          FStar_Syntax_Syntax.sigattrs = uu____7982;_} ->
                          FStar_Ident.lid_equals dc lid
                      | uu____7991 -> false)) in
            FStar_All.pipe_right sigs
              (FStar_List.iter
                 (fun uu___192_8026 ->
                    match uu___192_8026 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ
                          (typename, univs1, parms, uu____8030, uu____8031,
                           dc::[]);
                        FStar_Syntax_Syntax.sigrng = uu____8033;
                        FStar_Syntax_Syntax.sigquals = typename_quals;
                        FStar_Syntax_Syntax.sigmeta = uu____8035;
                        FStar_Syntax_Syntax.sigattrs = uu____8036;_} ->
                        let uu____8047 =
                          let uu____8048 = find_dc dc in
                          FStar_All.pipe_left FStar_Util.must uu____8048 in
                        (match uu____8047 with
                         | {
                             FStar_Syntax_Syntax.sigel =
                               FStar_Syntax_Syntax.Sig_datacon
                               (constrname, uu____8054, t, uu____8056,
                                uu____8057, uu____8058);
                             FStar_Syntax_Syntax.sigrng = uu____8059;
                             FStar_Syntax_Syntax.sigquals = uu____8060;
                             FStar_Syntax_Syntax.sigmeta = uu____8061;
                             FStar_Syntax_Syntax.sigattrs = uu____8062;_} ->
                             let uu____8071 =
                               FStar_Syntax_Util.arrow_formals t in
                             (match uu____8071 with
                              | (formals, uu____8087) ->
                                  let is_rec = is_record typename_quals in
                                  let formals' =
                                    FStar_All.pipe_right formals
                                      (FStar_List.collect
                                         (fun uu____8140 ->
                                            match uu____8140 with
                                            | (x, q) ->
                                                let uu____8153 =
                                                  (FStar_Syntax_Syntax.is_null_bv
                                                     x)
                                                    ||
                                                    (is_rec &&
                                                       (FStar_Syntax_Syntax.is_implicit
                                                          q)) in
                                                if uu____8153
                                                then []
                                                else [(x, q)])) in
                                  let fields' =
                                    FStar_All.pipe_right formals'
                                      (FStar_List.map
                                         (fun uu____8206 ->
                                            match uu____8206 with
                                            | (x, q) ->
                                                let uu____8219 =
                                                  if is_rec
                                                  then
                                                    FStar_Syntax_Util.unmangle_field_name
                                                      x.FStar_Syntax_Syntax.ppname
                                                  else
                                                    x.FStar_Syntax_Syntax.ppname in
                                                (uu____8219,
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
                                  ((let uu____8232 =
                                      let uu____8235 =
                                        FStar_ST.op_Bang new_globs in
                                      (Record_or_dc record) :: uu____8235 in
                                    FStar_ST.op_Colon_Equals new_globs
                                      uu____8232);
                                   (match () with
                                    | () ->
                                        ((let add_field uu____8338 =
                                            match uu____8338 with
                                            | (id1, uu____8344) ->
                                                let modul =
                                                  let uu____8346 =
                                                    FStar_Ident.lid_of_ids
                                                      constrname.FStar_Ident.ns in
                                                  uu____8346.FStar_Ident.str in
                                                let uu____8347 =
                                                  get_exported_id_set e modul in
                                                (match uu____8347 with
                                                 | FStar_Pervasives_Native.Some
                                                     my_ex ->
                                                     let my_exported_ids =
                                                       my_ex
                                                         Exported_id_field in
                                                     ((let uu____8381 =
                                                         let uu____8382 =
                                                           FStar_ST.op_Bang
                                                             my_exported_ids in
                                                         FStar_Util.set_add
                                                           id1.FStar_Ident.idText
                                                           uu____8382 in
                                                       FStar_ST.op_Colon_Equals
                                                         my_exported_ids
                                                         uu____8381);
                                                      (match () with
                                                       | () ->
                                                           let projname =
                                                             let uu____8468 =
                                                               let uu____8469
                                                                 =
                                                                 FStar_Syntax_Util.mk_field_projector_name_from_ident
                                                                   constrname
                                                                   id1 in
                                                               uu____8469.FStar_Ident.ident in
                                                             uu____8468.FStar_Ident.idText in
                                                           let uu____8471 =
                                                             let uu____8472 =
                                                               FStar_ST.op_Bang
                                                                 my_exported_ids in
                                                             FStar_Util.set_add
                                                               projname
                                                               uu____8472 in
                                                           FStar_ST.op_Colon_Equals
                                                             my_exported_ids
                                                             uu____8471))
                                                 | FStar_Pervasives_Native.None
                                                     -> ()) in
                                          FStar_List.iter add_field fields');
                                         (match () with
                                          | () -> insert_record_cache record)))))
                         | uu____8566 -> ())
                    | uu____8567 -> ()))
        | uu____8568 -> ()
let (try_lookup_record_or_dc_by_field_name :
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option) =
  fun env ->
    fun fieldname ->
      let find_in_cache fieldname1 =
        let uu____8589 =
          ((fieldname1.FStar_Ident.ns), (fieldname1.FStar_Ident.ident)) in
        match uu____8589 with
        | (ns, id1) ->
            let uu____8606 = peek_record_cache () in
            FStar_Util.find_map uu____8606
              (fun record ->
                 let uu____8612 =
                   find_in_record ns id1 record (fun r -> Cont_ok r) in
                 option_of_cont
                   (fun uu____8618 -> FStar_Pervasives_Native.None)
                   uu____8612) in
      resolve_in_open_namespaces'' env fieldname Exported_id_field
        (fun uu____8620 -> Cont_ignore) (fun uu____8622 -> Cont_ignore)
        (fun r -> Cont_ok r)
        (fun fn ->
           let uu____8628 = find_in_cache fn in
           cont_of_option Cont_ignore uu____8628)
        (fun k -> fun uu____8634 -> k)
let (try_lookup_record_by_field_name :
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option) =
  fun env ->
    fun fieldname ->
      let uu____8649 = try_lookup_record_or_dc_by_field_name env fieldname in
      match uu____8649 with
      | FStar_Pervasives_Native.Some r when r.is_record ->
          FStar_Pervasives_Native.Some r
      | uu____8655 -> FStar_Pervasives_Native.None
let (belongs_to_record :
  env -> FStar_Ident.lident -> record_or_dc -> Prims.bool) =
  fun env ->
    fun lid ->
      fun record ->
        let uu____8673 = try_lookup_record_by_field_name env lid in
        match uu____8673 with
        | FStar_Pervasives_Native.Some record' when
            let uu____8677 =
              let uu____8678 =
                FStar_Ident.path_of_ns (record.typename).FStar_Ident.ns in
              FStar_Ident.text_of_path uu____8678 in
            let uu____8679 =
              let uu____8680 =
                FStar_Ident.path_of_ns (record'.typename).FStar_Ident.ns in
              FStar_Ident.text_of_path uu____8680 in
            uu____8677 = uu____8679 ->
            let uu____8681 =
              find_in_record (record.typename).FStar_Ident.ns
                lid.FStar_Ident.ident record (fun uu____8685 -> Cont_ok ()) in
            (match uu____8681 with
             | Cont_ok uu____8686 -> true
             | uu____8687 -> false)
        | uu____8690 -> false
let (try_lookup_dc_by_field_name :
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident, Prims.bool) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option)
  =
  fun env ->
    fun fieldname ->
      let uu____8709 = try_lookup_record_or_dc_by_field_name env fieldname in
      match uu____8709 with
      | FStar_Pervasives_Native.Some r ->
          let uu____8719 =
            let uu____8724 =
              let uu____8725 =
                FStar_Ident.lid_of_ids
                  (FStar_List.append (r.typename).FStar_Ident.ns
                     [r.constrname]) in
              let uu____8726 = FStar_Ident.range_of_lid fieldname in
              FStar_Ident.set_lid_range uu____8725 uu____8726 in
            (uu____8724, (r.is_record)) in
          FStar_Pervasives_Native.Some uu____8719
      | uu____8731 -> FStar_Pervasives_Native.None
let (string_set_ref_new : unit -> Prims.string FStar_Util.set FStar_ST.ref) =
  fun uu____8757 ->
    let uu____8758 = FStar_Util.new_set FStar_Util.compare in
    FStar_Util.mk_ref uu____8758
let (exported_id_set_new :
  unit -> exported_id_kind -> Prims.string FStar_Util.set FStar_ST.ref) =
  fun uu____8785 ->
    let term_type_set = string_set_ref_new () in
    let field_set = string_set_ref_new () in
    fun uu___193_8796 ->
      match uu___193_8796 with
      | Exported_id_term_type -> term_type_set
      | Exported_id_field -> field_set
let (unique :
  Prims.bool -> Prims.bool -> env -> FStar_Ident.lident -> Prims.bool) =
  fun any_val ->
    fun exclude_interface ->
      fun env ->
        fun lid ->
          let filter_scope_mods uu___194_8848 =
            match uu___194_8848 with
            | Rec_binding uu____8849 -> true
            | uu____8850 -> false in
          let this_env =
            let uu___209_8852 = env in
            let uu____8853 =
              FStar_List.filter filter_scope_mods env.scope_mods in
            {
              curmodule = (uu___209_8852.curmodule);
              curmonad = (uu___209_8852.curmonad);
              modules = (uu___209_8852.modules);
              scope_mods = uu____8853;
              exported_ids = empty_exported_id_smap;
              trans_exported_ids = (uu___209_8852.trans_exported_ids);
              includes = empty_include_smap;
              sigaccum = (uu___209_8852.sigaccum);
              sigmap = (uu___209_8852.sigmap);
              iface = (uu___209_8852.iface);
              admitted_iface = (uu___209_8852.admitted_iface);
              expect_typ = (uu___209_8852.expect_typ);
              docs = (uu___209_8852.docs);
              remaining_iface_decls = (uu___209_8852.remaining_iface_decls);
              syntax_only = (uu___209_8852.syntax_only);
              ds_hooks = (uu___209_8852.ds_hooks);
              dep_graph = (uu___209_8852.dep_graph)
            } in
          let uu____8856 =
            try_lookup_lid' any_val exclude_interface this_env lid in
          match uu____8856 with
          | FStar_Pervasives_Native.None -> true
          | FStar_Pervasives_Native.Some uu____8875 -> false
let (push_scope_mod : env -> scope_mod -> env) =
  fun env ->
    fun scope_mod ->
      let uu___210_8902 = env in
      {
        curmodule = (uu___210_8902.curmodule);
        curmonad = (uu___210_8902.curmonad);
        modules = (uu___210_8902.modules);
        scope_mods = (scope_mod :: (env.scope_mods));
        exported_ids = (uu___210_8902.exported_ids);
        trans_exported_ids = (uu___210_8902.trans_exported_ids);
        includes = (uu___210_8902.includes);
        sigaccum = (uu___210_8902.sigaccum);
        sigmap = (uu___210_8902.sigmap);
        iface = (uu___210_8902.iface);
        admitted_iface = (uu___210_8902.admitted_iface);
        expect_typ = (uu___210_8902.expect_typ);
        docs = (uu___210_8902.docs);
        remaining_iface_decls = (uu___210_8902.remaining_iface_decls);
        syntax_only = (uu___210_8902.syntax_only);
        ds_hooks = (uu___210_8902.ds_hooks);
        dep_graph = (uu___210_8902.dep_graph)
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
        let uu____8967 =
          (unique false true env l) || (FStar_Options.interactive ()) in
        if uu____8967
        then push_scope_mod env (Rec_binding (x, l, dd))
        else
          (let uu____8969 = FStar_Ident.range_of_lid l in
           FStar_Errors.raise_error
             (FStar_Errors.Fatal_DuplicateTopLevelNames,
               (Prims.strcat "Duplicate top-level names " l.FStar_Ident.str))
             uu____8969)
let (push_sigelt' : Prims.bool -> env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun fail_on_dup ->
    fun env ->
      fun s ->
        let err l =
          let sopt = FStar_Util.smap_try_find (sigmap env) l.FStar_Ident.str in
          let r =
            match sopt with
            | FStar_Pervasives_Native.Some (se, uu____9004) ->
                let uu____9009 =
                  FStar_Util.find_opt (FStar_Ident.lid_equals l)
                    (FStar_Syntax_Util.lids_of_sigelt se) in
                (match uu____9009 with
                 | FStar_Pervasives_Native.Some l1 ->
                     let uu____9013 = FStar_Ident.range_of_lid l1 in
                     FStar_All.pipe_left FStar_Range.string_of_range
                       uu____9013
                 | FStar_Pervasives_Native.None -> "<unknown>")
            | FStar_Pervasives_Native.None -> "<unknown>" in
          let uu____9018 =
            let uu____9023 =
              let uu____9024 = FStar_Ident.text_of_lid l in
              FStar_Util.format2
                "Duplicate top-level names [%s]; previously declared at %s"
                uu____9024 r in
            (FStar_Errors.Fatal_DuplicateTopLevelNames, uu____9023) in
          let uu____9025 = FStar_Ident.range_of_lid l in
          FStar_Errors.raise_error uu____9018 uu____9025 in
        let globals = FStar_Util.mk_ref env.scope_mods in
        let env1 =
          let uu____9034 =
            match s.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_let uu____9043 -> (false, true)
            | FStar_Syntax_Syntax.Sig_bundle uu____9050 -> (false, true)
            | uu____9059 -> (false, false) in
          match uu____9034 with
          | (any_val, exclude_interface) ->
              let lids = FStar_Syntax_Util.lids_of_sigelt s in
              let uu____9065 =
                FStar_Util.find_map lids
                  (fun l ->
                     let uu____9071 =
                       let uu____9072 =
                         unique any_val exclude_interface env l in
                       Prims.op_Negation uu____9072 in
                     if uu____9071
                     then FStar_Pervasives_Native.Some l
                     else FStar_Pervasives_Native.None) in
              (match uu____9065 with
               | FStar_Pervasives_Native.Some l when fail_on_dup -> err l
               | uu____9077 ->
                   (extract_record env globals s;
                    (let uu___211_9103 = env in
                     {
                       curmodule = (uu___211_9103.curmodule);
                       curmonad = (uu___211_9103.curmonad);
                       modules = (uu___211_9103.modules);
                       scope_mods = (uu___211_9103.scope_mods);
                       exported_ids = (uu___211_9103.exported_ids);
                       trans_exported_ids =
                         (uu___211_9103.trans_exported_ids);
                       includes = (uu___211_9103.includes);
                       sigaccum = (s :: (env.sigaccum));
                       sigmap = (uu___211_9103.sigmap);
                       iface = (uu___211_9103.iface);
                       admitted_iface = (uu___211_9103.admitted_iface);
                       expect_typ = (uu___211_9103.expect_typ);
                       docs = (uu___211_9103.docs);
                       remaining_iface_decls =
                         (uu___211_9103.remaining_iface_decls);
                       syntax_only = (uu___211_9103.syntax_only);
                       ds_hooks = (uu___211_9103.ds_hooks);
                       dep_graph = (uu___211_9103.dep_graph)
                     }))) in
        let env2 =
          let uu___212_9105 = env1 in
          let uu____9106 = FStar_ST.op_Bang globals in
          {
            curmodule = (uu___212_9105.curmodule);
            curmonad = (uu___212_9105.curmonad);
            modules = (uu___212_9105.modules);
            scope_mods = uu____9106;
            exported_ids = (uu___212_9105.exported_ids);
            trans_exported_ids = (uu___212_9105.trans_exported_ids);
            includes = (uu___212_9105.includes);
            sigaccum = (uu___212_9105.sigaccum);
            sigmap = (uu___212_9105.sigmap);
            iface = (uu___212_9105.iface);
            admitted_iface = (uu___212_9105.admitted_iface);
            expect_typ = (uu___212_9105.expect_typ);
            docs = (uu___212_9105.docs);
            remaining_iface_decls = (uu___212_9105.remaining_iface_decls);
            syntax_only = (uu___212_9105.syntax_only);
            ds_hooks = (uu___212_9105.ds_hooks);
            dep_graph = (uu___212_9105.dep_graph)
          } in
        let uu____9154 =
          match s.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses, uu____9180) ->
              let uu____9189 =
                FStar_List.map
                  (fun se -> ((FStar_Syntax_Util.lids_of_sigelt se), se)) ses in
              (env2, uu____9189)
          | uu____9216 -> (env2, [((FStar_Syntax_Util.lids_of_sigelt s), s)]) in
        match uu____9154 with
        | (env3, lss) ->
            (FStar_All.pipe_right lss
               (FStar_List.iter
                  (fun uu____9275 ->
                     match uu____9275 with
                     | (lids, se) ->
                         FStar_All.pipe_right lids
                           (FStar_List.iter
                              (fun lid ->
                                 (let uu____9297 =
                                    let uu____9300 = FStar_ST.op_Bang globals in
                                    (Top_level_def (lid.FStar_Ident.ident))
                                      :: uu____9300 in
                                  FStar_ST.op_Colon_Equals globals uu____9297);
                                 (match () with
                                  | () ->
                                      let modul =
                                        let uu____9394 =
                                          FStar_Ident.lid_of_ids
                                            lid.FStar_Ident.ns in
                                        uu____9394.FStar_Ident.str in
                                      ((let uu____9396 =
                                          get_exported_id_set env3 modul in
                                        match uu____9396 with
                                        | FStar_Pervasives_Native.Some f ->
                                            let my_exported_ids =
                                              f Exported_id_term_type in
                                            let uu____9429 =
                                              let uu____9430 =
                                                FStar_ST.op_Bang
                                                  my_exported_ids in
                                              FStar_Util.set_add
                                                (lid.FStar_Ident.ident).FStar_Ident.idText
                                                uu____9430 in
                                            FStar_ST.op_Colon_Equals
                                              my_exported_ids uu____9429
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
                let uu___213_9526 = env3 in
                let uu____9527 = FStar_ST.op_Bang globals in
                {
                  curmodule = (uu___213_9526.curmodule);
                  curmonad = (uu___213_9526.curmonad);
                  modules = (uu___213_9526.modules);
                  scope_mods = uu____9527;
                  exported_ids = (uu___213_9526.exported_ids);
                  trans_exported_ids = (uu___213_9526.trans_exported_ids);
                  includes = (uu___213_9526.includes);
                  sigaccum = (uu___213_9526.sigaccum);
                  sigmap = (uu___213_9526.sigmap);
                  iface = (uu___213_9526.iface);
                  admitted_iface = (uu___213_9526.admitted_iface);
                  expect_typ = (uu___213_9526.expect_typ);
                  docs = (uu___213_9526.docs);
                  remaining_iface_decls =
                    (uu___213_9526.remaining_iface_decls);
                  syntax_only = (uu___213_9526.syntax_only);
                  ds_hooks = (uu___213_9526.ds_hooks);
                  dep_graph = (uu___213_9526.dep_graph)
                } in
              env4))
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env -> fun se -> push_sigelt' true env se
let (push_sigelt_force : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env -> fun se -> push_sigelt' false env se
let (push_namespace : env -> FStar_Ident.lident -> env) =
  fun env ->
    fun ns ->
      let uu____9605 =
        let uu____9610 = resolve_module_name env ns false in
        match uu____9610 with
        | FStar_Pervasives_Native.None ->
            let modules = env.modules in
            let uu____9624 =
              FStar_All.pipe_right modules
                (FStar_Util.for_some
                   (fun uu____9640 ->
                      match uu____9640 with
                      | (m, uu____9646) ->
                          let uu____9647 =
                            let uu____9648 = FStar_Ident.text_of_lid m in
                            Prims.strcat uu____9648 "." in
                          let uu____9649 =
                            let uu____9650 = FStar_Ident.text_of_lid ns in
                            Prims.strcat uu____9650 "." in
                          FStar_Util.starts_with uu____9647 uu____9649)) in
            if uu____9624
            then (ns, Open_namespace)
            else
              (let uu____9656 =
                 let uu____9661 =
                   let uu____9662 = FStar_Ident.text_of_lid ns in
                   FStar_Util.format1 "Namespace %s cannot be found"
                     uu____9662 in
                 (FStar_Errors.Fatal_NameSpaceNotFound, uu____9661) in
               let uu____9663 = FStar_Ident.range_of_lid ns in
               FStar_Errors.raise_error uu____9656 uu____9663)
        | FStar_Pervasives_Native.Some ns' ->
            (fail_if_curmodule env ns ns'; (ns', Open_module)) in
      match uu____9605 with
      | (ns', kd) ->
          ((env.ds_hooks).ds_push_open_hook env (ns', kd);
           push_scope_mod env (Open_module_or_namespace (ns', kd)))
let (push_include : env -> FStar_Ident.lident -> env) =
  fun env ->
    fun ns ->
      let ns0 = ns in
      let uu____9684 = resolve_module_name env ns false in
      match uu____9684 with
      | FStar_Pervasives_Native.Some ns1 ->
          ((env.ds_hooks).ds_push_include_hook env ns1;
           fail_if_curmodule env ns0 ns1;
           (let env1 =
              push_scope_mod env
                (Open_module_or_namespace (ns1, Open_module)) in
            let curmod =
              let uu____9692 = current_module env1 in
              uu____9692.FStar_Ident.str in
            (let uu____9694 = FStar_Util.smap_try_find env1.includes curmod in
             match uu____9694 with
             | FStar_Pervasives_Native.None -> ()
             | FStar_Pervasives_Native.Some incl ->
                 let uu____9718 =
                   let uu____9721 = FStar_ST.op_Bang incl in ns1 ::
                     uu____9721 in
                 FStar_ST.op_Colon_Equals incl uu____9718);
            (match () with
             | () ->
                 let uu____9814 =
                   get_trans_exported_id_set env1 ns1.FStar_Ident.str in
                 (match uu____9814 with
                  | FStar_Pervasives_Native.Some ns_trans_exports ->
                      ((let uu____9834 =
                          let uu____9929 = get_exported_id_set env1 curmod in
                          let uu____9975 =
                            get_trans_exported_id_set env1 curmod in
                          (uu____9929, uu____9975) in
                        match uu____9834 with
                        | (FStar_Pervasives_Native.Some cur_exports,
                           FStar_Pervasives_Native.Some cur_trans_exports) ->
                            let update_exports k =
                              let ns_ex =
                                let uu____10382 = ns_trans_exports k in
                                FStar_ST.op_Bang uu____10382 in
                              let ex = cur_exports k in
                              (let uu____10556 =
                                 let uu____10559 = FStar_ST.op_Bang ex in
                                 FStar_Util.set_difference uu____10559 ns_ex in
                               FStar_ST.op_Colon_Equals ex uu____10556);
                              (match () with
                               | () ->
                                   let trans_ex = cur_trans_exports k in
                                   let uu____10751 =
                                     let uu____10754 =
                                       FStar_ST.op_Bang trans_ex in
                                     FStar_Util.set_union uu____10754 ns_ex in
                                   FStar_ST.op_Colon_Equals trans_ex
                                     uu____10751) in
                            FStar_List.iter update_exports
                              all_exported_id_kinds
                        | uu____10883 -> ());
                       (match () with | () -> env1))
                  | FStar_Pervasives_Native.None ->
                      let uu____10983 =
                        let uu____10988 =
                          FStar_Util.format1
                            "include: Module %s was not prepared"
                            ns1.FStar_Ident.str in
                        (FStar_Errors.Fatal_IncludeModuleNotPrepared,
                          uu____10988) in
                      let uu____10989 = FStar_Ident.range_of_lid ns1 in
                      FStar_Errors.raise_error uu____10983 uu____10989))))
      | uu____10990 ->
          let uu____10993 =
            let uu____10998 =
              FStar_Util.format1 "include: Module %s cannot be found"
                ns.FStar_Ident.str in
            (FStar_Errors.Fatal_ModuleNotFound, uu____10998) in
          let uu____10999 = FStar_Ident.range_of_lid ns in
          FStar_Errors.raise_error uu____10993 uu____10999
let (push_module_abbrev :
  env -> FStar_Ident.ident -> FStar_Ident.lident -> env) =
  fun env ->
    fun x ->
      fun l ->
        let uu____11015 = module_is_defined env l in
        if uu____11015
        then
          (fail_if_curmodule env l l;
           (env.ds_hooks).ds_push_module_abbrev_hook env x l;
           push_scope_mod env (Module_abbrev (x, l)))
        else
          (let uu____11019 =
             let uu____11024 =
               let uu____11025 = FStar_Ident.text_of_lid l in
               FStar_Util.format1 "Module %s cannot be found" uu____11025 in
             (FStar_Errors.Fatal_ModuleNotFound, uu____11024) in
           let uu____11026 = FStar_Ident.range_of_lid l in
           FStar_Errors.raise_error uu____11019 uu____11026)
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
            ((let uu____11048 =
                FStar_Util.smap_try_find env.docs l.FStar_Ident.str in
              match uu____11048 with
              | FStar_Pervasives_Native.None -> ()
              | FStar_Pervasives_Native.Some old_doc ->
                  let uu____11052 = FStar_Ident.range_of_lid l in
                  let uu____11053 =
                    let uu____11058 =
                      let uu____11059 = FStar_Ident.string_of_lid l in
                      let uu____11060 =
                        FStar_Parser_AST.string_of_fsdoc old_doc in
                      let uu____11061 = FStar_Parser_AST.string_of_fsdoc doc1 in
                      FStar_Util.format3
                        "Overwriting doc of %s; old doc was [%s]; new doc are [%s]"
                        uu____11059 uu____11060 uu____11061 in
                    (FStar_Errors.Warning_DocOverwrite, uu____11058) in
                  FStar_Errors.log_issue uu____11052 uu____11053);
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
                      let uu____11103 =
                        FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption) in
                      Prims.op_Negation uu____11103 ->
                      let uu____11106 =
                        FStar_Util.smap_try_find (sigmap env)
                          l.FStar_Ident.str in
                      (match uu____11106 with
                       | FStar_Pervasives_Native.Some
                           ({
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_let uu____11119;
                              FStar_Syntax_Syntax.sigrng = uu____11120;
                              FStar_Syntax_Syntax.sigquals = uu____11121;
                              FStar_Syntax_Syntax.sigmeta = uu____11122;
                              FStar_Syntax_Syntax.sigattrs = uu____11123;_},
                            uu____11124)
                           -> lids
                       | FStar_Pervasives_Native.Some
                           ({
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_inductive_typ
                                uu____11139;
                              FStar_Syntax_Syntax.sigrng = uu____11140;
                              FStar_Syntax_Syntax.sigquals = uu____11141;
                              FStar_Syntax_Syntax.sigmeta = uu____11142;
                              FStar_Syntax_Syntax.sigattrs = uu____11143;_},
                            uu____11144)
                           -> lids
                       | uu____11169 ->
                           ((let uu____11177 =
                               let uu____11178 = FStar_Options.interactive () in
                               Prims.op_Negation uu____11178 in
                             if uu____11177
                             then
                               let uu____11179 = FStar_Ident.range_of_lid l in
                               let uu____11180 =
                                 let uu____11185 =
                                   let uu____11186 =
                                     FStar_Ident.string_of_lid l in
                                   FStar_Util.format1
                                     "Admitting %s without a definition"
                                     uu____11186 in
                                 (FStar_Errors.Warning_AdmitWithoutDefinition,
                                   uu____11185) in
                               FStar_Errors.log_issue uu____11179 uu____11180
                             else ());
                            (let quals = FStar_Syntax_Syntax.Assumption ::
                               (se.FStar_Syntax_Syntax.sigquals) in
                             FStar_Util.smap_add (sigmap env)
                               l.FStar_Ident.str
                               ((let uu___214_11197 = se in
                                 {
                                   FStar_Syntax_Syntax.sigel =
                                     (uu___214_11197.FStar_Syntax_Syntax.sigel);
                                   FStar_Syntax_Syntax.sigrng =
                                     (uu___214_11197.FStar_Syntax_Syntax.sigrng);
                                   FStar_Syntax_Syntax.sigquals = quals;
                                   FStar_Syntax_Syntax.sigmeta =
                                     (uu___214_11197.FStar_Syntax_Syntax.sigmeta);
                                   FStar_Syntax_Syntax.sigattrs =
                                     (uu___214_11197.FStar_Syntax_Syntax.sigattrs)
                                 }), false);
                             l
                             ::
                             lids)))
                  | uu____11198 -> lids) []) in
      let uu___215_11199 = m in
      let uu____11200 =
        FStar_All.pipe_right m.FStar_Syntax_Syntax.declarations
          (FStar_List.map
             (fun s ->
                match s.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_declare_typ
                    (lid, uu____11210, uu____11211) when
                    FStar_List.existsb
                      (fun l -> FStar_Ident.lid_equals l lid)
                      admitted_sig_lids
                    ->
                    let uu___216_11214 = s in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___216_11214.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___216_11214.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals =
                        (FStar_Syntax_Syntax.Assumption ::
                        (s.FStar_Syntax_Syntax.sigquals));
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___216_11214.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___216_11214.FStar_Syntax_Syntax.sigattrs)
                    }
                | uu____11215 -> s)) in
      {
        FStar_Syntax_Syntax.name = (uu___215_11199.FStar_Syntax_Syntax.name);
        FStar_Syntax_Syntax.declarations = uu____11200;
        FStar_Syntax_Syntax.exports =
          (uu___215_11199.FStar_Syntax_Syntax.exports);
        FStar_Syntax_Syntax.is_interface =
          (uu___215_11199.FStar_Syntax_Syntax.is_interface)
      }
let (finish : env -> FStar_Syntax_Syntax.modul -> env) =
  fun env ->
    fun modul ->
      FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations
        (FStar_List.iter
           (fun se ->
              let quals = se.FStar_Syntax_Syntax.sigquals in
              match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_bundle (ses, uu____11238) ->
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
                                (lid, uu____11258, uu____11259, uu____11260,
                                 uu____11261, uu____11262)
                                ->
                                FStar_Util.smap_remove (sigmap env)
                                  lid.FStar_Ident.str
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (lid, univ_names, binders, typ, uu____11275,
                                 uu____11276)
                                ->
                                (FStar_Util.smap_remove (sigmap env)
                                   lid.FStar_Ident.str;
                                 if
                                   Prims.op_Negation
                                     (FStar_List.contains
                                        FStar_Syntax_Syntax.Private quals)
                                 then
                                   (let sigel =
                                      let uu____11291 =
                                        let uu____11298 =
                                          let uu____11299 =
                                            FStar_Ident.range_of_lid lid in
                                          let uu____11300 =
                                            let uu____11307 =
                                              let uu____11308 =
                                                let uu____11323 =
                                                  FStar_Syntax_Syntax.mk_Total
                                                    typ in
                                                (binders, uu____11323) in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____11308 in
                                            FStar_Syntax_Syntax.mk
                                              uu____11307 in
                                          uu____11300
                                            FStar_Pervasives_Native.None
                                            uu____11299 in
                                        (lid, univ_names, uu____11298) in
                                      FStar_Syntax_Syntax.Sig_declare_typ
                                        uu____11291 in
                                    let se2 =
                                      let uu___217_11340 = se1 in
                                      {
                                        FStar_Syntax_Syntax.sigel = sigel;
                                        FStar_Syntax_Syntax.sigrng =
                                          (uu___217_11340.FStar_Syntax_Syntax.sigrng);
                                        FStar_Syntax_Syntax.sigquals =
                                          (FStar_Syntax_Syntax.Assumption ::
                                          quals);
                                        FStar_Syntax_Syntax.sigmeta =
                                          (uu___217_11340.FStar_Syntax_Syntax.sigmeta);
                                        FStar_Syntax_Syntax.sigattrs =
                                          (uu___217_11340.FStar_Syntax_Syntax.sigattrs)
                                      } in
                                    FStar_Util.smap_add (sigmap env)
                                      lid.FStar_Ident.str (se2, false))
                                 else ())
                            | uu____11346 -> ()))
                  else ()
              | FStar_Syntax_Syntax.Sig_declare_typ
                  (lid, uu____11349, uu____11350) ->
                  if FStar_List.contains FStar_Syntax_Syntax.Private quals
                  then
                    FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str
                  else ()
              | FStar_Syntax_Syntax.Sig_let ((uu____11356, lbs), uu____11358)
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
                             let uu____11373 =
                               let uu____11374 =
                                 let uu____11375 =
                                   let uu____11378 =
                                     FStar_Util.right
                                       lb.FStar_Syntax_Syntax.lbname in
                                   uu____11378.FStar_Syntax_Syntax.fv_name in
                                 uu____11375.FStar_Syntax_Syntax.v in
                               uu____11374.FStar_Ident.str in
                             FStar_Util.smap_remove (sigmap env) uu____11373))
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
                               let uu____11392 =
                                 let uu____11395 =
                                   FStar_Util.right
                                     lb.FStar_Syntax_Syntax.lbname in
                                 uu____11395.FStar_Syntax_Syntax.fv_name in
                               uu____11392.FStar_Syntax_Syntax.v in
                             let quals1 = FStar_Syntax_Syntax.Assumption ::
                               quals in
                             let decl =
                               let uu___218_11400 = se in
                               {
                                 FStar_Syntax_Syntax.sigel =
                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                      (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                        (lb.FStar_Syntax_Syntax.lbtyp)));
                                 FStar_Syntax_Syntax.sigrng =
                                   (uu___218_11400.FStar_Syntax_Syntax.sigrng);
                                 FStar_Syntax_Syntax.sigquals = quals1;
                                 FStar_Syntax_Syntax.sigmeta =
                                   (uu___218_11400.FStar_Syntax_Syntax.sigmeta);
                                 FStar_Syntax_Syntax.sigattrs =
                                   (uu___218_11400.FStar_Syntax_Syntax.sigattrs)
                               } in
                             FStar_Util.smap_add (sigmap env)
                               lid.FStar_Ident.str (decl, false)))
                   else ())
              | uu____11406 -> ()));
      (let curmod =
         let uu____11408 = current_module env in uu____11408.FStar_Ident.str in
       (let uu____11410 =
          let uu____11505 = get_exported_id_set env curmod in
          let uu____11551 = get_trans_exported_id_set env curmod in
          (uu____11505, uu____11551) in
        match uu____11410 with
        | (FStar_Pervasives_Native.Some cur_ex, FStar_Pervasives_Native.Some
           cur_trans_ex) ->
            let update_exports eikind =
              let cur_ex_set =
                let uu____11960 = cur_ex eikind in
                FStar_ST.op_Bang uu____11960 in
              let cur_trans_ex_set_ref = cur_trans_ex eikind in
              let uu____12147 =
                let uu____12150 = FStar_ST.op_Bang cur_trans_ex_set_ref in
                FStar_Util.set_union cur_ex_set uu____12150 in
              FStar_ST.op_Colon_Equals cur_trans_ex_set_ref uu____12147 in
            FStar_List.iter update_exports all_exported_id_kinds
        | uu____12279 -> ());
       (match () with
        | () ->
            (filter_record_cache ();
             (match () with
              | () ->
                  let uu___219_12375 = env in
                  {
                    curmodule = FStar_Pervasives_Native.None;
                    curmonad = (uu___219_12375.curmonad);
                    modules = (((modul.FStar_Syntax_Syntax.name), modul) ::
                      (env.modules));
                    scope_mods = [];
                    exported_ids = (uu___219_12375.exported_ids);
                    trans_exported_ids = (uu___219_12375.trans_exported_ids);
                    includes = (uu___219_12375.includes);
                    sigaccum = [];
                    sigmap = (uu___219_12375.sigmap);
                    iface = (uu___219_12375.iface);
                    admitted_iface = (uu___219_12375.admitted_iface);
                    expect_typ = (uu___219_12375.expect_typ);
                    docs = (uu___219_12375.docs);
                    remaining_iface_decls =
                      (uu___219_12375.remaining_iface_decls);
                    syntax_only = (uu___219_12375.syntax_only);
                    ds_hooks = (uu___219_12375.ds_hooks);
                    dep_graph = (uu___219_12375.dep_graph)
                  }))))
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref []
let (push : env -> env) =
  fun env ->
    FStar_Util.atomically
      (fun uu____12411 ->
         push_record_cache ();
         (let uu____12414 =
            let uu____12417 = FStar_ST.op_Bang stack in env :: uu____12417 in
          FStar_ST.op_Colon_Equals stack uu____12414);
         (let uu___220_12466 = env in
          let uu____12467 = FStar_Util.smap_copy env.exported_ids in
          let uu____12472 = FStar_Util.smap_copy env.trans_exported_ids in
          let uu____12477 = FStar_Util.smap_copy env.includes in
          let uu____12488 = FStar_Util.smap_copy env.sigmap in
          let uu____12499 = FStar_Util.smap_copy env.docs in
          {
            curmodule = (uu___220_12466.curmodule);
            curmonad = (uu___220_12466.curmonad);
            modules = (uu___220_12466.modules);
            scope_mods = (uu___220_12466.scope_mods);
            exported_ids = uu____12467;
            trans_exported_ids = uu____12472;
            includes = uu____12477;
            sigaccum = (uu___220_12466.sigaccum);
            sigmap = uu____12488;
            iface = (uu___220_12466.iface);
            admitted_iface = (uu___220_12466.admitted_iface);
            expect_typ = (uu___220_12466.expect_typ);
            docs = uu____12499;
            remaining_iface_decls = (uu___220_12466.remaining_iface_decls);
            syntax_only = (uu___220_12466.syntax_only);
            ds_hooks = (uu___220_12466.ds_hooks);
            dep_graph = (uu___220_12466.dep_graph)
          }))
let (pop : unit -> env) =
  fun uu____12506 ->
    FStar_Util.atomically
      (fun uu____12513 ->
         let uu____12514 = FStar_ST.op_Bang stack in
         match uu____12514 with
         | env::tl1 ->
             (pop_record_cache (); FStar_ST.op_Colon_Equals stack tl1; env)
         | uu____12569 -> failwith "Impossible: Too many pops")
let (snapshot : env -> (Prims.int, env) FStar_Pervasives_Native.tuple2) =
  fun env -> FStar_Common.snapshot push stack env
let (rollback : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth -> FStar_Common.rollback pop stack depth
let (export_interface : FStar_Ident.lident -> env -> env) =
  fun m ->
    fun env ->
      let sigelt_in_m se =
        match FStar_Syntax_Util.lids_of_sigelt se with
        | l::uu____12607 -> l.FStar_Ident.nsstr = m.FStar_Ident.str
        | uu____12610 -> false in
      let sm = sigmap env in
      let env1 = pop () in
      let keys = FStar_Util.smap_keys sm in
      let sm' = sigmap env1 in
      FStar_All.pipe_right keys
        (FStar_List.iter
           (fun k ->
              let uu____12644 = FStar_Util.smap_try_find sm' k in
              match uu____12644 with
              | FStar_Pervasives_Native.Some (se, true) when sigelt_in_m se
                  ->
                  (FStar_Util.smap_remove sm' k;
                   (let se1 =
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_declare_typ (l, u, t) ->
                          let uu___221_12669 = se in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (uu___221_12669.FStar_Syntax_Syntax.sigel);
                            FStar_Syntax_Syntax.sigrng =
                              (uu___221_12669.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (FStar_Syntax_Syntax.Assumption ::
                              (se.FStar_Syntax_Syntax.sigquals));
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___221_12669.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___221_12669.FStar_Syntax_Syntax.sigattrs)
                          }
                      | uu____12670 -> se in
                    FStar_Util.smap_add sm' k (se1, false)))
              | uu____12675 -> ()));
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
      let uu____12698 = finish env modul1 in (uu____12698, modul1)
type exported_ids =
  {
  exported_id_terms: Prims.string Prims.list ;
  exported_id_fields: Prims.string Prims.list }
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
      let uu____12786 =
        let uu____12789 = e Exported_id_term_type in
        FStar_ST.op_Bang uu____12789 in
      FStar_Util.set_elements uu____12786 in
    let fields =
      let uu____12903 =
        let uu____12906 = e Exported_id_field in FStar_ST.op_Bang uu____12906 in
      FStar_Util.set_elements uu____12903 in
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
          let uu____13057 =
            FStar_Util.as_set e1.exported_id_terms FStar_Util.compare in
          FStar_Util.mk_ref uu____13057 in
        let fields =
          let uu____13067 =
            FStar_Util.as_set e1.exported_id_fields FStar_Util.compare in
          FStar_Util.mk_ref uu____13067 in
        (fun uu___195_13072 ->
           match uu___195_13072 with
           | Exported_id_term_type -> terms
           | Exported_id_field -> fields)
type module_inclusion_info =
  {
  mii_exported_ids: exported_ids FStar_Pervasives_Native.option ;
  mii_trans_exported_ids: exported_ids FStar_Pervasives_Native.option ;
  mii_includes: FStar_Ident.lident Prims.list FStar_Pervasives_Native.option }
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
  'Auu____13203 .
    'Auu____13203 Prims.list FStar_Pervasives_Native.option ->
      'Auu____13203 Prims.list FStar_ST.ref
  =
  fun uu___196_13216 ->
    match uu___196_13216 with
    | FStar_Pervasives_Native.None -> FStar_Util.mk_ref []
    | FStar_Pervasives_Native.Some l -> FStar_Util.mk_ref l
let (inclusion_info : env -> FStar_Ident.lident -> module_inclusion_info) =
  fun env ->
    fun l ->
      let mname = FStar_Ident.string_of_lid l in
      let as_ids_opt m =
        let uu____13257 = FStar_Util.smap_try_find m mname in
        FStar_Util.map_opt uu____13257 as_exported_ids in
      let uu____13263 = as_ids_opt env.exported_ids in
      let uu____13266 = as_ids_opt env.trans_exported_ids in
      let uu____13269 =
        let uu____13274 = FStar_Util.smap_try_find env.includes mname in
        FStar_Util.map_opt uu____13274 (fun r -> FStar_ST.op_Bang r) in
      {
        mii_exported_ids = uu____13263;
        mii_trans_exported_ids = uu____13266;
        mii_includes = uu____13269
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
                let uu____13389 = FStar_Ident.text_of_lid mname in
                FStar_Util.strcat uu____13389 ".fst" in
              let auto_open =
                FStar_Parser_Dep.hard_coded_dependencies filename in
              let auto_open1 =
                let convert_kind uu___197_13409 =
                  match uu___197_13409 with
                  | FStar_Parser_Dep.Open_namespace -> Open_namespace
                  | FStar_Parser_Dep.Open_module -> Open_module in
                FStar_List.map
                  (fun uu____13421 ->
                     match uu____13421 with
                     | (lid, kind) -> (lid, (convert_kind kind))) auto_open in
              let namespace_of_module =
                if
                  (FStar_List.length mname.FStar_Ident.ns) >
                    (Prims.parse_int "0")
                then
                  let uu____13445 =
                    let uu____13450 =
                      FStar_Ident.lid_of_ids mname.FStar_Ident.ns in
                    (uu____13450, Open_namespace) in
                  [uu____13445]
                else [] in
              let auto_open2 =
                FStar_List.append namespace_of_module
                  (FStar_List.rev auto_open1) in
              (let uu____13480 = as_exported_id_set mii.mii_exported_ids in
               FStar_Util.smap_add env1.exported_ids mname.FStar_Ident.str
                 uu____13480);
              (match () with
               | () ->
                   ((let uu____13507 =
                       as_exported_id_set mii.mii_trans_exported_ids in
                     FStar_Util.smap_add env1.trans_exported_ids
                       mname.FStar_Ident.str uu____13507);
                    (match () with
                     | () ->
                         ((let uu____13534 = as_includes mii.mii_includes in
                           FStar_Util.smap_add env1.includes
                             mname.FStar_Ident.str uu____13534);
                          (match () with
                           | () ->
                               let env' =
                                 let uu___222_13566 = env1 in
                                 let uu____13567 =
                                   FStar_List.map
                                     (fun x -> Open_module_or_namespace x)
                                     auto_open2 in
                                 {
                                   curmodule =
                                     (FStar_Pervasives_Native.Some mname);
                                   curmonad = (uu___222_13566.curmonad);
                                   modules = (uu___222_13566.modules);
                                   scope_mods = uu____13567;
                                   exported_ids =
                                     (uu___222_13566.exported_ids);
                                   trans_exported_ids =
                                     (uu___222_13566.trans_exported_ids);
                                   includes = (uu___222_13566.includes);
                                   sigaccum = (uu___222_13566.sigaccum);
                                   sigmap = (env1.sigmap);
                                   iface = intf;
                                   admitted_iface = admitted;
                                   expect_typ = (uu___222_13566.expect_typ);
                                   docs = (uu___222_13566.docs);
                                   remaining_iface_decls =
                                     (uu___222_13566.remaining_iface_decls);
                                   syntax_only = (uu___222_13566.syntax_only);
                                   ds_hooks = (uu___222_13566.ds_hooks);
                                   dep_graph = (uu___222_13566.dep_graph)
                                 } in
                               (FStar_List.iter
                                  (fun op ->
                                     (env1.ds_hooks).ds_push_open_hook env'
                                       op) (FStar_List.rev auto_open2);
                                env')))))) in
            let uu____13579 =
              FStar_All.pipe_right env.modules
                (FStar_Util.find_opt
                   (fun uu____13605 ->
                      match uu____13605 with
                      | (l, uu____13611) -> FStar_Ident.lid_equals l mname)) in
            match uu____13579 with
            | FStar_Pervasives_Native.None ->
                let uu____13620 = prep env in (uu____13620, false)
            | FStar_Pervasives_Native.Some (uu____13621, m) ->
                ((let uu____13628 =
                    (let uu____13631 = FStar_Options.interactive () in
                     Prims.op_Negation uu____13631) &&
                      ((Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)
                         || intf) in
                  if uu____13628
                  then
                    let uu____13632 =
                      let uu____13637 =
                        FStar_Util.format1
                          "Duplicate module or interface name: %s"
                          mname.FStar_Ident.str in
                      (FStar_Errors.Fatal_DuplicateModuleOrInterface,
                        uu____13637) in
                    let uu____13638 = FStar_Ident.range_of_lid mname in
                    FStar_Errors.raise_error uu____13632 uu____13638
                  else ());
                 (let uu____13640 =
                    let uu____13641 = push env in prep uu____13641 in
                  (uu____13640, true)))
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
          let uu___223_13653 = env in
          {
            curmodule = (uu___223_13653.curmodule);
            curmonad = (FStar_Pervasives_Native.Some mname);
            modules = (uu___223_13653.modules);
            scope_mods = (uu___223_13653.scope_mods);
            exported_ids = (uu___223_13653.exported_ids);
            trans_exported_ids = (uu___223_13653.trans_exported_ids);
            includes = (uu___223_13653.includes);
            sigaccum = (uu___223_13653.sigaccum);
            sigmap = (uu___223_13653.sigmap);
            iface = (uu___223_13653.iface);
            admitted_iface = (uu___223_13653.admitted_iface);
            expect_typ = (uu___223_13653.expect_typ);
            docs = (uu___223_13653.docs);
            remaining_iface_decls = (uu___223_13653.remaining_iface_decls);
            syntax_only = (uu___223_13653.syntax_only);
            ds_hooks = (uu___223_13653.ds_hooks);
            dep_graph = (uu___223_13653.dep_graph)
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
        let uu____13687 = lookup1 lid in
        match uu____13687 with
        | FStar_Pervasives_Native.None ->
            let opened_modules =
              FStar_List.map
                (fun uu____13700 ->
                   match uu____13700 with
                   | (lid1, uu____13706) -> FStar_Ident.text_of_lid lid1)
                env.modules in
            let msg =
              let uu____13708 = FStar_Ident.text_of_lid lid in
              FStar_Util.format1 "Identifier not found: [%s]" uu____13708 in
            let msg1 =
              if
                (FStar_List.length lid.FStar_Ident.ns) =
                  (Prims.parse_int "0")
              then msg
              else
                (let modul =
                   let uu____13712 =
                     FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
                   let uu____13713 = FStar_Ident.range_of_lid lid in
                   FStar_Ident.set_lid_range uu____13712 uu____13713 in
                 let uu____13714 = resolve_module_name env modul true in
                 match uu____13714 with
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
            let uu____13723 = FStar_Ident.range_of_lid lid in
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_IdentifierNotFound, msg1) uu____13723
        | FStar_Pervasives_Native.Some r -> r
let fail_or2 :
  'a .
    (FStar_Ident.ident -> 'a FStar_Pervasives_Native.option) ->
      FStar_Ident.ident -> 'a
  =
  fun lookup1 ->
    fun id1 ->
      let uu____13751 = lookup1 id1 in
      match uu____13751 with
      | FStar_Pervasives_Native.None ->
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_IdentifierNotFound,
              (Prims.strcat "Identifier not found ["
                 (Prims.strcat id1.FStar_Ident.idText "]")))
            id1.FStar_Ident.idRange
      | FStar_Pervasives_Native.Some r -> r