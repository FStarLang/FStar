open Prims
type local_binding =
  (FStar_Ident.ident,FStar_Syntax_Syntax.bv,Prims.bool)
    FStar_Pervasives_Native.tuple3
type rec_binding =
  (FStar_Ident.ident,FStar_Ident.lid,FStar_Syntax_Syntax.delta_depth)
    FStar_Pervasives_Native.tuple3
type module_abbrev =
  (FStar_Ident.ident,FStar_Ident.lident) FStar_Pervasives_Native.tuple2
type open_kind =
  | Open_module 
  | Open_namespace 
let (uu___is_Open_module : open_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Open_module  -> true | uu____22 -> false
  
let (uu___is_Open_namespace : open_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Open_namespace  -> true | uu____28 -> false
  
type open_module_or_namespace =
  (FStar_Ident.lident,open_kind) FStar_Pervasives_Native.tuple2
type record_or_dc =
  {
  typename: FStar_Ident.lident ;
  constrname: FStar_Ident.ident ;
  parms: FStar_Syntax_Syntax.binders ;
  fields:
    (FStar_Ident.ident,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple2 Prims.list
    ;
  is_private_or_abstract: Prims.bool ;
  is_record: Prims.bool }
let (__proj__Mkrecord_or_dc__item__typename :
  record_or_dc -> FStar_Ident.lident) =
  fun projectee  ->
    match projectee with
    | { typename = __fname__typename; constrname = __fname__constrname;
        parms = __fname__parms; fields = __fname__fields;
        is_private_or_abstract = __fname__is_private_or_abstract;
        is_record = __fname__is_record;_} -> __fname__typename
  
let (__proj__Mkrecord_or_dc__item__constrname :
  record_or_dc -> FStar_Ident.ident) =
  fun projectee  ->
    match projectee with
    | { typename = __fname__typename; constrname = __fname__constrname;
        parms = __fname__parms; fields = __fname__fields;
        is_private_or_abstract = __fname__is_private_or_abstract;
        is_record = __fname__is_record;_} -> __fname__constrname
  
let (__proj__Mkrecord_or_dc__item__parms :
  record_or_dc -> FStar_Syntax_Syntax.binders) =
  fun projectee  ->
    match projectee with
    | { typename = __fname__typename; constrname = __fname__constrname;
        parms = __fname__parms; fields = __fname__fields;
        is_private_or_abstract = __fname__is_private_or_abstract;
        is_record = __fname__is_record;_} -> __fname__parms
  
let (__proj__Mkrecord_or_dc__item__fields :
  record_or_dc ->
    (FStar_Ident.ident,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { typename = __fname__typename; constrname = __fname__constrname;
        parms = __fname__parms; fields = __fname__fields;
        is_private_or_abstract = __fname__is_private_or_abstract;
        is_record = __fname__is_record;_} -> __fname__fields
  
let (__proj__Mkrecord_or_dc__item__is_private_or_abstract :
  record_or_dc -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { typename = __fname__typename; constrname = __fname__constrname;
        parms = __fname__parms; fields = __fname__fields;
        is_private_or_abstract = __fname__is_private_or_abstract;
        is_record = __fname__is_record;_} -> __fname__is_private_or_abstract
  
let (__proj__Mkrecord_or_dc__item__is_record : record_or_dc -> Prims.bool) =
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
  | Record_or_dc of record_or_dc 
let (uu___is_Local_binding : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with | Local_binding _0 -> true | uu____219 -> false
  
let (__proj__Local_binding__item___0 : scope_mod -> local_binding) =
  fun projectee  -> match projectee with | Local_binding _0 -> _0 
let (uu___is_Rec_binding : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with | Rec_binding _0 -> true | uu____233 -> false
  
let (__proj__Rec_binding__item___0 : scope_mod -> rec_binding) =
  fun projectee  -> match projectee with | Rec_binding _0 -> _0 
let (uu___is_Module_abbrev : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with | Module_abbrev _0 -> true | uu____247 -> false
  
let (__proj__Module_abbrev__item___0 : scope_mod -> module_abbrev) =
  fun projectee  -> match projectee with | Module_abbrev _0 -> _0 
let (uu___is_Open_module_or_namespace : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Open_module_or_namespace _0 -> true
    | uu____261 -> false
  
let (__proj__Open_module_or_namespace__item___0 :
  scope_mod -> open_module_or_namespace) =
  fun projectee  -> match projectee with | Open_module_or_namespace _0 -> _0 
let (uu___is_Top_level_def : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with | Top_level_def _0 -> true | uu____275 -> false
  
let (__proj__Top_level_def__item___0 : scope_mod -> FStar_Ident.ident) =
  fun projectee  -> match projectee with | Top_level_def _0 -> _0 
let (uu___is_Record_or_dc : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with | Record_or_dc _0 -> true | uu____289 -> false
  
let (__proj__Record_or_dc__item___0 : scope_mod -> record_or_dc) =
  fun projectee  -> match projectee with | Record_or_dc _0 -> _0 
type string_set = Prims.string FStar_Util.set
type exported_id_kind =
  | Exported_id_term_type 
  | Exported_id_field 
let (uu___is_Exported_id_term_type : exported_id_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Exported_id_term_type  -> true
    | uu____304 -> false
  
let (uu___is_Exported_id_field : exported_id_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exported_id_field  -> true | uu____310 -> false
  
type exported_id_set = exported_id_kind -> string_set FStar_ST.ref
type env =
  {
  curmodule: FStar_Ident.lident FStar_Pervasives_Native.option ;
  curmonad: FStar_Ident.ident FStar_Pervasives_Native.option ;
  modules:
    (FStar_Ident.lident,FStar_Syntax_Syntax.modul)
      FStar_Pervasives_Native.tuple2 Prims.list
    ;
  scope_mods: scope_mod Prims.list ;
  exported_ids: exported_id_set FStar_Util.smap ;
  trans_exported_ids: exported_id_set FStar_Util.smap ;
  includes: FStar_Ident.lident Prims.list FStar_ST.ref FStar_Util.smap ;
  sigaccum: FStar_Syntax_Syntax.sigelts ;
  sigmap:
    (FStar_Syntax_Syntax.sigelt,Prims.bool) FStar_Pervasives_Native.tuple2
      FStar_Util.smap
    ;
  iface: Prims.bool ;
  admitted_iface: Prims.bool ;
  expect_typ: Prims.bool ;
  docs: FStar_Parser_AST.fsdoc FStar_Util.smap ;
  remaining_iface_decls:
    (FStar_Ident.lident,FStar_Parser_AST.decl Prims.list)
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
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;
        dep_graph = __fname__dep_graph;_} -> __fname__curmodule
  
let (__proj__Mkenv__item__curmonad :
  env -> FStar_Ident.ident FStar_Pervasives_Native.option) =
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
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;
        dep_graph = __fname__dep_graph;_} -> __fname__curmonad
  
let (__proj__Mkenv__item__modules :
  env ->
    (FStar_Ident.lident,FStar_Syntax_Syntax.modul)
      FStar_Pervasives_Native.tuple2 Prims.list)
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
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;
        dep_graph = __fname__dep_graph;_} -> __fname__modules
  
let (__proj__Mkenv__item__scope_mods : env -> scope_mod Prims.list) =
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
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;
        dep_graph = __fname__dep_graph;_} -> __fname__scope_mods
  
let (__proj__Mkenv__item__exported_ids :
  env -> exported_id_set FStar_Util.smap) =
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
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;
        dep_graph = __fname__dep_graph;_} -> __fname__exported_ids
  
let (__proj__Mkenv__item__trans_exported_ids :
  env -> exported_id_set FStar_Util.smap) =
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
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;
        dep_graph = __fname__dep_graph;_} -> __fname__trans_exported_ids
  
let (__proj__Mkenv__item__includes :
  env -> FStar_Ident.lident Prims.list FStar_ST.ref FStar_Util.smap) =
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
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;
        dep_graph = __fname__dep_graph;_} -> __fname__includes
  
let (__proj__Mkenv__item__sigaccum : env -> FStar_Syntax_Syntax.sigelts) =
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
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;
        dep_graph = __fname__dep_graph;_} -> __fname__sigaccum
  
let (__proj__Mkenv__item__sigmap :
  env ->
    (FStar_Syntax_Syntax.sigelt,Prims.bool) FStar_Pervasives_Native.tuple2
      FStar_Util.smap)
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
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;
        dep_graph = __fname__dep_graph;_} -> __fname__sigmap
  
let (__proj__Mkenv__item__iface : env -> Prims.bool) =
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
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;
        dep_graph = __fname__dep_graph;_} -> __fname__iface
  
let (__proj__Mkenv__item__admitted_iface : env -> Prims.bool) =
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
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;
        dep_graph = __fname__dep_graph;_} -> __fname__admitted_iface
  
let (__proj__Mkenv__item__expect_typ : env -> Prims.bool) =
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
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;
        dep_graph = __fname__dep_graph;_} -> __fname__expect_typ
  
let (__proj__Mkenv__item__docs :
  env -> FStar_Parser_AST.fsdoc FStar_Util.smap) =
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
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;
        dep_graph = __fname__dep_graph;_} -> __fname__docs
  
let (__proj__Mkenv__item__remaining_iface_decls :
  env ->
    (FStar_Ident.lident,FStar_Parser_AST.decl Prims.list)
      FStar_Pervasives_Native.tuple2 Prims.list)
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
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;
        dep_graph = __fname__dep_graph;_} -> __fname__remaining_iface_decls
  
let (__proj__Mkenv__item__syntax_only : env -> Prims.bool) =
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
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;
        dep_graph = __fname__dep_graph;_} -> __fname__syntax_only
  
let (__proj__Mkenv__item__ds_hooks : env -> dsenv_hooks) =
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
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;
        dep_graph = __fname__dep_graph;_} -> __fname__ds_hooks
  
let (__proj__Mkenv__item__dep_graph : env -> FStar_Parser_Dep.deps) =
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
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;
        dep_graph = __fname__dep_graph;_} -> __fname__dep_graph
  
let (__proj__Mkdsenv_hooks__item__ds_push_open_hook :
  dsenv_hooks -> env -> open_module_or_namespace -> unit) =
  fun projectee  ->
    match projectee with
    | { ds_push_open_hook = __fname__ds_push_open_hook;
        ds_push_include_hook = __fname__ds_push_include_hook;
        ds_push_module_abbrev_hook = __fname__ds_push_module_abbrev_hook;_}
        -> __fname__ds_push_open_hook
  
let (__proj__Mkdsenv_hooks__item__ds_push_include_hook :
  dsenv_hooks -> env -> FStar_Ident.lident -> unit) =
  fun projectee  ->
    match projectee with
    | { ds_push_open_hook = __fname__ds_push_open_hook;
        ds_push_include_hook = __fname__ds_push_include_hook;
        ds_push_module_abbrev_hook = __fname__ds_push_module_abbrev_hook;_}
        -> __fname__ds_push_include_hook
  
let (__proj__Mkdsenv_hooks__item__ds_push_module_abbrev_hook :
  dsenv_hooks -> env -> FStar_Ident.ident -> FStar_Ident.lident -> unit) =
  fun projectee  ->
    match projectee with
    | { ds_push_open_hook = __fname__ds_push_open_hook;
        ds_push_include_hook = __fname__ds_push_include_hook;
        ds_push_module_abbrev_hook = __fname__ds_push_module_abbrev_hook;_}
        -> __fname__ds_push_module_abbrev_hook
  
type 'a withenv = env -> ('a,env) FStar_Pervasives_Native.tuple2
let (default_ds_hooks : dsenv_hooks) =
  {
    ds_push_open_hook = (fun uu____1808  -> fun uu____1809  -> ());
    ds_push_include_hook = (fun uu____1812  -> fun uu____1813  -> ());
    ds_push_module_abbrev_hook =
      (fun uu____1817  -> fun uu____1818  -> fun uu____1819  -> ())
  } 
type foundname =
  | Term_name of
  (FStar_Syntax_Syntax.typ,Prims.bool,FStar_Syntax_Syntax.attribute
                                        Prims.list)
  FStar_Pervasives_Native.tuple3 
  | Eff_name of (FStar_Syntax_Syntax.sigelt,FStar_Ident.lident)
  FStar_Pervasives_Native.tuple2 
let (uu___is_Term_name : foundname -> Prims.bool) =
  fun projectee  ->
    match projectee with | Term_name _0 -> true | uu____1856 -> false
  
let (__proj__Term_name__item___0 :
  foundname ->
    (FStar_Syntax_Syntax.typ,Prims.bool,FStar_Syntax_Syntax.attribute
                                          Prims.list)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Term_name _0 -> _0 
let (uu___is_Eff_name : foundname -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eff_name _0 -> true | uu____1898 -> false
  
let (__proj__Eff_name__item___0 :
  foundname ->
    (FStar_Syntax_Syntax.sigelt,FStar_Ident.lident)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Eff_name _0 -> _0 
let (set_iface : env -> Prims.bool -> env) =
  fun env  ->
    fun b  ->
      let uu___196_1928 = env  in
      {
        curmodule = (uu___196_1928.curmodule);
        curmonad = (uu___196_1928.curmonad);
        modules = (uu___196_1928.modules);
        scope_mods = (uu___196_1928.scope_mods);
        exported_ids = (uu___196_1928.exported_ids);
        trans_exported_ids = (uu___196_1928.trans_exported_ids);
        includes = (uu___196_1928.includes);
        sigaccum = (uu___196_1928.sigaccum);
        sigmap = (uu___196_1928.sigmap);
        iface = b;
        admitted_iface = (uu___196_1928.admitted_iface);
        expect_typ = (uu___196_1928.expect_typ);
        docs = (uu___196_1928.docs);
        remaining_iface_decls = (uu___196_1928.remaining_iface_decls);
        syntax_only = (uu___196_1928.syntax_only);
        ds_hooks = (uu___196_1928.ds_hooks);
        dep_graph = (uu___196_1928.dep_graph)
      }
  
let (iface : env -> Prims.bool) = fun e  -> e.iface 
let (set_admitted_iface : env -> Prims.bool -> env) =
  fun e  ->
    fun b  ->
      let uu___197_1944 = e  in
      {
        curmodule = (uu___197_1944.curmodule);
        curmonad = (uu___197_1944.curmonad);
        modules = (uu___197_1944.modules);
        scope_mods = (uu___197_1944.scope_mods);
        exported_ids = (uu___197_1944.exported_ids);
        trans_exported_ids = (uu___197_1944.trans_exported_ids);
        includes = (uu___197_1944.includes);
        sigaccum = (uu___197_1944.sigaccum);
        sigmap = (uu___197_1944.sigmap);
        iface = (uu___197_1944.iface);
        admitted_iface = b;
        expect_typ = (uu___197_1944.expect_typ);
        docs = (uu___197_1944.docs);
        remaining_iface_decls = (uu___197_1944.remaining_iface_decls);
        syntax_only = (uu___197_1944.syntax_only);
        ds_hooks = (uu___197_1944.ds_hooks);
        dep_graph = (uu___197_1944.dep_graph)
      }
  
let (admitted_iface : env -> Prims.bool) = fun e  -> e.admitted_iface 
let (set_expect_typ : env -> Prims.bool -> env) =
  fun e  ->
    fun b  ->
      let uu___198_1960 = e  in
      {
        curmodule = (uu___198_1960.curmodule);
        curmonad = (uu___198_1960.curmonad);
        modules = (uu___198_1960.modules);
        scope_mods = (uu___198_1960.scope_mods);
        exported_ids = (uu___198_1960.exported_ids);
        trans_exported_ids = (uu___198_1960.trans_exported_ids);
        includes = (uu___198_1960.includes);
        sigaccum = (uu___198_1960.sigaccum);
        sigmap = (uu___198_1960.sigmap);
        iface = (uu___198_1960.iface);
        admitted_iface = (uu___198_1960.admitted_iface);
        expect_typ = b;
        docs = (uu___198_1960.docs);
        remaining_iface_decls = (uu___198_1960.remaining_iface_decls);
        syntax_only = (uu___198_1960.syntax_only);
        ds_hooks = (uu___198_1960.ds_hooks);
        dep_graph = (uu___198_1960.dep_graph)
      }
  
let (expect_typ : env -> Prims.bool) = fun e  -> e.expect_typ 
let (all_exported_id_kinds : exported_id_kind Prims.list) =
  [Exported_id_field; Exported_id_term_type] 
let (transitive_exported_ids :
  env -> FStar_Ident.lident -> Prims.string Prims.list) =
  fun env  ->
    fun lid  ->
      let module_name = FStar_Ident.string_of_lid lid  in
      let uu____1981 =
        FStar_Util.smap_try_find env.trans_exported_ids module_name  in
      match uu____1981 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some exported_id_set ->
          let uu____1992 =
            let uu____1995 = exported_id_set Exported_id_term_type  in
            FStar_ST.op_Bang uu____1995  in
          FStar_All.pipe_right uu____1992 FStar_Util.set_elements
  
let (open_modules :
  env ->
    (FStar_Ident.lident,FStar_Syntax_Syntax.modul)
      FStar_Pervasives_Native.tuple2 Prims.list)
  = fun e  -> e.modules 
let (open_modules_and_namespaces : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    FStar_List.filter_map
      (fun uu___163_2131  ->
         match uu___163_2131 with
         | Open_module_or_namespace (lid,_info) ->
             FStar_Pervasives_Native.Some lid
         | uu____2136 -> FStar_Pervasives_Native.None) env.scope_mods
  
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun e  ->
    fun l  ->
      let uu___199_2147 = e  in
      {
        curmodule = (FStar_Pervasives_Native.Some l);
        curmonad = (uu___199_2147.curmonad);
        modules = (uu___199_2147.modules);
        scope_mods = (uu___199_2147.scope_mods);
        exported_ids = (uu___199_2147.exported_ids);
        trans_exported_ids = (uu___199_2147.trans_exported_ids);
        includes = (uu___199_2147.includes);
        sigaccum = (uu___199_2147.sigaccum);
        sigmap = (uu___199_2147.sigmap);
        iface = (uu___199_2147.iface);
        admitted_iface = (uu___199_2147.admitted_iface);
        expect_typ = (uu___199_2147.expect_typ);
        docs = (uu___199_2147.docs);
        remaining_iface_decls = (uu___199_2147.remaining_iface_decls);
        syntax_only = (uu___199_2147.syntax_only);
        ds_hooks = (uu___199_2147.ds_hooks);
        dep_graph = (uu___199_2147.dep_graph)
      }
  
let (current_module : env -> FStar_Ident.lident) =
  fun env  ->
    match env.curmodule with
    | FStar_Pervasives_Native.None  -> failwith "Unset current module"
    | FStar_Pervasives_Native.Some m -> m
  
let (iface_decls :
  env ->
    FStar_Ident.lident ->
      FStar_Parser_AST.decl Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____2168 =
        FStar_All.pipe_right env.remaining_iface_decls
          (FStar_List.tryFind
             (fun uu____2202  ->
                match uu____2202 with
                | (m,uu____2210) -> FStar_Ident.lid_equals l m))
         in
      match uu____2168 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (uu____2227,decls) ->
          FStar_Pervasives_Native.Some decls
  
let (set_iface_decls :
  env -> FStar_Ident.lident -> FStar_Parser_AST.decl Prims.list -> env) =
  fun env  ->
    fun l  ->
      fun ds  ->
        let uu____2260 =
          FStar_List.partition
            (fun uu____2290  ->
               match uu____2290 with
               | (m,uu____2298) -> FStar_Ident.lid_equals l m)
            env.remaining_iface_decls
           in
        match uu____2260 with
        | (uu____2303,rest) ->
            let uu___200_2337 = env  in
            {
              curmodule = (uu___200_2337.curmodule);
              curmonad = (uu___200_2337.curmonad);
              modules = (uu___200_2337.modules);
              scope_mods = (uu___200_2337.scope_mods);
              exported_ids = (uu___200_2337.exported_ids);
              trans_exported_ids = (uu___200_2337.trans_exported_ids);
              includes = (uu___200_2337.includes);
              sigaccum = (uu___200_2337.sigaccum);
              sigmap = (uu___200_2337.sigmap);
              iface = (uu___200_2337.iface);
              admitted_iface = (uu___200_2337.admitted_iface);
              expect_typ = (uu___200_2337.expect_typ);
              docs = (uu___200_2337.docs);
              remaining_iface_decls = ((l, ds) :: rest);
              syntax_only = (uu___200_2337.syntax_only);
              ds_hooks = (uu___200_2337.ds_hooks);
              dep_graph = (uu___200_2337.dep_graph)
            }
  
let (qual : FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident) =
  FStar_Syntax_Util.qual_id 
let (qualify : env -> FStar_Ident.ident -> FStar_Ident.lident) =
  fun env  ->
    fun id1  ->
      match env.curmonad with
      | FStar_Pervasives_Native.None  ->
          let uu____2364 = current_module env  in qual uu____2364 id1
      | FStar_Pervasives_Native.Some monad ->
          let uu____2366 =
            let uu____2367 = current_module env  in qual uu____2367 monad  in
          FStar_Syntax_Util.mk_field_projector_name_from_ident uu____2366 id1
  
let (syntax_only : env -> Prims.bool) = fun env  -> env.syntax_only 
let (set_syntax_only : env -> Prims.bool -> env) =
  fun env  ->
    fun b  ->
      let uu___201_2383 = env  in
      {
        curmodule = (uu___201_2383.curmodule);
        curmonad = (uu___201_2383.curmonad);
        modules = (uu___201_2383.modules);
        scope_mods = (uu___201_2383.scope_mods);
        exported_ids = (uu___201_2383.exported_ids);
        trans_exported_ids = (uu___201_2383.trans_exported_ids);
        includes = (uu___201_2383.includes);
        sigaccum = (uu___201_2383.sigaccum);
        sigmap = (uu___201_2383.sigmap);
        iface = (uu___201_2383.iface);
        admitted_iface = (uu___201_2383.admitted_iface);
        expect_typ = (uu___201_2383.expect_typ);
        docs = (uu___201_2383.docs);
        remaining_iface_decls = (uu___201_2383.remaining_iface_decls);
        syntax_only = b;
        ds_hooks = (uu___201_2383.ds_hooks);
        dep_graph = (uu___201_2383.dep_graph)
      }
  
let (ds_hooks : env -> dsenv_hooks) = fun env  -> env.ds_hooks 
let (set_ds_hooks : env -> dsenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___202_2399 = env  in
      {
        curmodule = (uu___202_2399.curmodule);
        curmonad = (uu___202_2399.curmonad);
        modules = (uu___202_2399.modules);
        scope_mods = (uu___202_2399.scope_mods);
        exported_ids = (uu___202_2399.exported_ids);
        trans_exported_ids = (uu___202_2399.trans_exported_ids);
        includes = (uu___202_2399.includes);
        sigaccum = (uu___202_2399.sigaccum);
        sigmap = (uu___202_2399.sigmap);
        iface = (uu___202_2399.iface);
        admitted_iface = (uu___202_2399.admitted_iface);
        expect_typ = (uu___202_2399.expect_typ);
        docs = (uu___202_2399.docs);
        remaining_iface_decls = (uu___202_2399.remaining_iface_decls);
        syntax_only = (uu___202_2399.syntax_only);
        ds_hooks = hooks;
        dep_graph = (uu___202_2399.dep_graph)
      }
  
let new_sigmap : 'Auu____2404 . unit -> 'Auu____2404 FStar_Util.smap =
  fun uu____2411  -> FStar_Util.smap_create (Prims.parse_int "100") 
let (empty_env : FStar_Parser_Dep.deps -> env) =
  fun deps  ->
    let uu____2417 = new_sigmap ()  in
    let uu____2422 = new_sigmap ()  in
    let uu____2427 = new_sigmap ()  in
    let uu____2438 = new_sigmap ()  in
    let uu____2449 = new_sigmap ()  in
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
  
let (dep_graph : env -> FStar_Parser_Dep.deps) = fun env  -> env.dep_graph 
let (sigmap :
  env ->
    (FStar_Syntax_Syntax.sigelt,Prims.bool) FStar_Pervasives_Native.tuple2
      FStar_Util.smap)
  = fun env  -> env.sigmap 
let (has_all_in_scope : env -> Prims.bool) =
  fun env  ->
    FStar_List.existsb
      (fun uu____2490  ->
         match uu____2490 with
         | (m,uu____2496) ->
             FStar_Ident.lid_equals m FStar_Parser_Const.all_lid) env.modules
  
let (set_bv_range :
  FStar_Syntax_Syntax.bv -> FStar_Range.range -> FStar_Syntax_Syntax.bv) =
  fun bv  ->
    fun r  ->
      let id1 =
        let uu___203_2508 = bv.FStar_Syntax_Syntax.ppname  in
        {
          FStar_Ident.idText = (uu___203_2508.FStar_Ident.idText);
          FStar_Ident.idRange = r
        }  in
      let uu___204_2509 = bv  in
      {
        FStar_Syntax_Syntax.ppname = id1;
        FStar_Syntax_Syntax.index = (uu___204_2509.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = (uu___204_2509.FStar_Syntax_Syntax.sort)
      }
  
let (bv_to_name :
  FStar_Syntax_Syntax.bv -> FStar_Range.range -> FStar_Syntax_Syntax.term) =
  fun bv  -> fun r  -> FStar_Syntax_Syntax.bv_to_name (set_bv_range bv r) 
let (unmangleMap :
  (Prims.string,Prims.string,FStar_Syntax_Syntax.delta_depth,FStar_Syntax_Syntax.fv_qual
                                                               FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple4 Prims.list)
  =
  [("op_ColonColon", "Cons", FStar_Syntax_Syntax.delta_constant,
     (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor));
  ("not", "op_Negation", FStar_Syntax_Syntax.delta_equational,
    FStar_Pervasives_Native.None)]
  
let (unmangleOpName :
  FStar_Ident.ident ->
    (FStar_Syntax_Syntax.term,Prims.bool) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option)
  =
  fun id1  ->
    let t =
      FStar_Util.find_map unmangleMap
        (fun uu____2602  ->
           match uu____2602 with
           | (x,y,dd,dq) ->
               if id1.FStar_Ident.idText = x
               then
                 let uu____2625 =
                   let uu____2626 =
                     FStar_Ident.lid_of_path ["Prims"; y]
                       id1.FStar_Ident.idRange
                      in
                   FStar_Syntax_Syntax.fvar uu____2626 dd dq  in
                 FStar_Pervasives_Native.Some uu____2625
               else FStar_Pervasives_Native.None)
       in
    match t with
    | FStar_Pervasives_Native.Some v1 ->
        FStar_Pervasives_Native.Some (v1, false)
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
type 'a cont_t =
  | Cont_ok of 'a 
  | Cont_fail 
  | Cont_ignore 
let uu___is_Cont_ok : 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_ok _0 -> true | uu____2673 -> false
  
let __proj__Cont_ok__item___0 : 'a . 'a cont_t -> 'a =
  fun projectee  -> match projectee with | Cont_ok _0 -> _0 
let uu___is_Cont_fail : 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_fail  -> true | uu____2706 -> false
  
let uu___is_Cont_ignore : 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_ignore  -> true | uu____2723 -> false
  
let option_of_cont :
  'a .
    (unit -> 'a FStar_Pervasives_Native.option) ->
      'a cont_t -> 'a FStar_Pervasives_Native.option
  =
  fun k_ignore  ->
    fun uu___164_2751  ->
      match uu___164_2751 with
      | Cont_ok a -> FStar_Pervasives_Native.Some a
      | Cont_fail  -> FStar_Pervasives_Native.None
      | Cont_ignore  -> k_ignore ()
  
let find_in_record :
  'Auu____2769 .
    FStar_Ident.ident Prims.list ->
      FStar_Ident.ident ->
        record_or_dc ->
          (record_or_dc -> 'Auu____2769 cont_t) -> 'Auu____2769 cont_t
  =
  fun ns  ->
    fun id1  ->
      fun record  ->
        fun cont  ->
          let typename' =
            FStar_Ident.lid_of_ids
              (FStar_List.append ns [(record.typename).FStar_Ident.ident])
             in
          let uu____2806 = FStar_Ident.lid_equals typename' record.typename
             in
          if uu____2806
          then
            let fname =
              FStar_Ident.lid_of_ids
                (FStar_List.append (record.typename).FStar_Ident.ns [id1])
               in
            let find1 =
              FStar_Util.find_map record.fields
                (fun uu____2820  ->
                   match uu____2820 with
                   | (f,uu____2828) ->
                       if id1.FStar_Ident.idText = f.FStar_Ident.idText
                       then FStar_Pervasives_Native.Some record
                       else FStar_Pervasives_Native.None)
               in
            match find1 with
            | FStar_Pervasives_Native.Some r -> cont r
            | FStar_Pervasives_Native.None  -> Cont_ignore
          else Cont_ignore
  
let (get_exported_id_set :
  env ->
    Prims.string ->
      (exported_id_kind -> string_set FStar_ST.ref)
        FStar_Pervasives_Native.option)
  = fun e  -> fun mname  -> FStar_Util.smap_try_find e.exported_ids mname 
let (get_trans_exported_id_set :
  env ->
    Prims.string ->
      (exported_id_kind -> string_set FStar_ST.ref)
        FStar_Pervasives_Native.option)
  =
  fun e  -> fun mname  -> FStar_Util.smap_try_find e.trans_exported_ids mname 
let (string_of_exported_id_kind : exported_id_kind -> Prims.string) =
  fun uu___165_2890  ->
    match uu___165_2890 with
    | Exported_id_field  -> "field"
    | Exported_id_term_type  -> "term/type"
  
let find_in_module_with_includes :
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
              let idstr = id1.FStar_Ident.idText  in
              let rec aux uu___166_2961 =
                match uu___166_2961 with
                | [] -> find_in_module_default
                | modul::q ->
                    let mname = modul.FStar_Ident.str  in
                    let not_shadowed =
                      let uu____2972 = get_exported_id_set env mname  in
                      match uu____2972 with
                      | FStar_Pervasives_Native.None  -> true
                      | FStar_Pervasives_Native.Some mex ->
                          let mexports =
                            let uu____2997 = mex eikind  in
                            FStar_ST.op_Bang uu____2997  in
                          FStar_Util.set_mem idstr mexports
                       in
                    let mincludes =
                      let uu____3111 =
                        FStar_Util.smap_try_find env.includes mname  in
                      match uu____3111 with
                      | FStar_Pervasives_Native.None  -> []
                      | FStar_Pervasives_Native.Some minc ->
                          FStar_ST.op_Bang minc
                       in
                    let look_into =
                      if not_shadowed
                      then
                        let uu____3187 = qual modul id1  in
                        find_in_module uu____3187
                      else Cont_ignore  in
                    (match look_into with
                     | Cont_ignore  -> aux (FStar_List.append mincludes q)
                     | uu____3191 -> look_into)
                 in
              aux [ns]
  
let (is_exported_id_field : exported_id_kind -> Prims.bool) =
  fun uu___167_3198  ->
    match uu___167_3198 with
    | Exported_id_field  -> true
    | uu____3199 -> false
  
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
  fun env  ->
    fun id1  ->
      fun eikind  ->
        fun k_local_binding  ->
          fun k_rec_binding  ->
            fun k_record  ->
              fun find_in_module  ->
                fun lookup_default_id  ->
                  let check_local_binding_id uu___168_3320 =
                    match uu___168_3320 with
                    | (id',uu____3322,uu____3323) ->
                        id'.FStar_Ident.idText = id1.FStar_Ident.idText
                     in
                  let check_rec_binding_id uu___169_3329 =
                    match uu___169_3329 with
                    | (id',uu____3331,uu____3332) ->
                        id'.FStar_Ident.idText = id1.FStar_Ident.idText
                     in
                  let curmod_ns =
                    let uu____3336 = current_module env  in
                    FStar_Ident.ids_of_lid uu____3336  in
                  let proc uu___170_3344 =
                    match uu___170_3344 with
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
                        let uu____3352 = FStar_Ident.lid_of_ids curmod_ns  in
                        find_in_module_with_includes Exported_id_field
                          (fun lid  ->
                             let id2 = lid.FStar_Ident.ident  in
                             find_in_record lid.FStar_Ident.ns id2 r k_record)
                          Cont_ignore env uu____3352 id1
                    | uu____3357 -> Cont_ignore  in
                  let rec aux uu___171_3367 =
                    match uu___171_3367 with
                    | a::q ->
                        let uu____3376 = proc a  in
                        option_of_cont (fun uu____3380  -> aux q) uu____3376
                    | [] ->
                        let uu____3381 = lookup_default_id Cont_fail id1  in
                        option_of_cont
                          (fun uu____3385  -> FStar_Pervasives_Native.None)
                          uu____3381
                     in
                  aux env.scope_mods
  
let found_local_binding :
  'Auu____3394 'Auu____3395 .
    FStar_Range.range ->
      ('Auu____3394,FStar_Syntax_Syntax.bv,'Auu____3395)
        FStar_Pervasives_Native.tuple3 ->
        (FStar_Syntax_Syntax.term,'Auu____3395)
          FStar_Pervasives_Native.tuple2
  =
  fun r  ->
    fun uu____3415  ->
      match uu____3415 with
      | (id',x,mut) -> let uu____3425 = bv_to_name x r  in (uu____3425, mut)
  
let find_in_module :
  'Auu____3436 .
    env ->
      FStar_Ident.lident ->
        (FStar_Ident.lident ->
           (FStar_Syntax_Syntax.sigelt,Prims.bool)
             FStar_Pervasives_Native.tuple2 -> 'Auu____3436)
          -> 'Auu____3436 -> 'Auu____3436
  =
  fun env  ->
    fun lid  ->
      fun k_global_def  ->
        fun k_not_found  ->
          let uu____3475 =
            FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str  in
          match uu____3475 with
          | FStar_Pervasives_Native.Some sb -> k_global_def lid sb
          | FStar_Pervasives_Native.None  -> k_not_found
  
let (try_lookup_id :
  env ->
    FStar_Ident.ident ->
      (FStar_Syntax_Syntax.term,Prims.bool) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun id1  ->
      let uu____3515 = unmangleOpName id1  in
      match uu____3515 with
      | FStar_Pervasives_Native.Some f -> FStar_Pervasives_Native.Some f
      | uu____3541 ->
          try_lookup_id'' env id1 Exported_id_term_type
            (fun r  ->
               let uu____3555 = found_local_binding id1.FStar_Ident.idRange r
                  in
               Cont_ok uu____3555) (fun uu____3565  -> Cont_fail)
            (fun uu____3571  -> Cont_ignore)
            (fun i  ->
               find_in_module env i
                 (fun uu____3586  -> fun uu____3587  -> Cont_fail)
                 Cont_ignore)
            (fun uu____3602  -> fun uu____3603  -> Cont_fail)
  
let lookup_default_id :
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
            | FStar_Pervasives_Native.Some uu____3682 ->
                let lid = qualify env id1  in
                let uu____3684 =
                  FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str
                   in
                (match uu____3684 with
                 | FStar_Pervasives_Native.Some r ->
                     let uu____3708 = k_global_def lid r  in
                     FStar_Pervasives_Native.Some uu____3708
                 | FStar_Pervasives_Native.None  ->
                     FStar_Pervasives_Native.None)
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             in
          match find_in_monad with
          | FStar_Pervasives_Native.Some v1 -> v1
          | FStar_Pervasives_Native.None  ->
              let lid =
                let uu____3731 = current_module env  in qual uu____3731 id1
                 in
              find_in_module env lid k_global_def k_not_found
  
let (lid_is_curmod : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      match env.curmodule with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some m -> FStar_Ident.lid_equals lid m
  
let (module_is_defined : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      (lid_is_curmod env lid) ||
        (FStar_List.existsb
           (fun x  ->
              FStar_Ident.lid_equals lid (FStar_Pervasives_Native.fst x))
           env.modules)
  
let (resolve_module_name :
  env ->
    FStar_Ident.lident ->
      Prims.bool -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      fun honor_ns  ->
        let nslen = FStar_List.length lid.FStar_Ident.ns  in
        let rec aux uu___172_3794 =
          match uu___172_3794 with
          | [] ->
              let uu____3799 = module_is_defined env lid  in
              if uu____3799
              then FStar_Pervasives_Native.Some lid
              else FStar_Pervasives_Native.None
          | (Open_module_or_namespace (ns,Open_namespace ))::q when honor_ns
              ->
              let new_lid =
                let uu____3808 =
                  let uu____3809 = FStar_Ident.path_of_lid ns  in
                  let uu____3812 = FStar_Ident.path_of_lid lid  in
                  FStar_List.append uu____3809 uu____3812  in
                let uu____3815 = FStar_Ident.range_of_lid lid  in
                FStar_Ident.lid_of_path uu____3808 uu____3815  in
              let uu____3816 = module_is_defined env new_lid  in
              if uu____3816
              then FStar_Pervasives_Native.Some new_lid
              else aux q
          | (Module_abbrev (name,modul))::uu____3822 when
              (nslen = (Prims.parse_int "0")) &&
                (name.FStar_Ident.idText =
                   (lid.FStar_Ident.ident).FStar_Ident.idText)
              -> FStar_Pervasives_Native.Some modul
          | uu____3829::q -> aux q  in
        aux env.scope_mods
  
let (fail_if_curmodule :
  env -> FStar_Ident.lident -> FStar_Ident.lident -> unit) =
  fun env  ->
    fun ns_original  ->
      fun ns_resolved  ->
        let uu____3848 =
          let uu____3849 = current_module env  in
          FStar_Ident.lid_equals ns_resolved uu____3849  in
        if uu____3848
        then
          let uu____3850 =
            FStar_Ident.lid_equals ns_resolved FStar_Parser_Const.prims_lid
             in
          (if uu____3850
           then ()
           else
             (let uu____3852 =
                let uu____3857 =
                  FStar_Util.format1
                    "Reference %s to current module is forbidden (see GitHub issue #451)"
                    ns_original.FStar_Ident.str
                   in
                (FStar_Errors.Fatal_ForbiddenReferenceToCurrentModule,
                  uu____3857)
                 in
              let uu____3858 = FStar_Ident.range_of_lid ns_original  in
              FStar_Errors.raise_error uu____3852 uu____3858))
        else ()
  
let (fail_if_qualified_by_curmodule : env -> FStar_Ident.lident -> unit) =
  fun env  ->
    fun lid  ->
      match lid.FStar_Ident.ns with
      | [] -> ()
      | uu____3870 ->
          let modul_orig = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          let uu____3874 = resolve_module_name env modul_orig true  in
          (match uu____3874 with
           | FStar_Pervasives_Native.Some modul_res ->
               fail_if_curmodule env modul_orig modul_res
           | uu____3878 -> ())
  
let (is_open : env -> FStar_Ident.lident -> open_kind -> Prims.bool) =
  fun env  ->
    fun lid  ->
      fun open_kind  ->
        FStar_List.existsb
          (fun uu___173_3899  ->
             match uu___173_3899 with
             | Open_module_or_namespace (ns,k) ->
                 (k = open_kind) && (FStar_Ident.lid_equals lid ns)
             | uu____3902 -> false) env.scope_mods
  
let (namespace_is_open : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  -> fun lid  -> is_open env lid Open_namespace 
let (module_is_open : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  -> (lid_is_curmod env lid) || (is_open env lid Open_module)
  
let (shorten_module_path :
  env ->
    FStar_Ident.ident Prims.list ->
      Prims.bool ->
        (FStar_Ident.ident Prims.list,FStar_Ident.ident Prims.list)
          FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun ids  ->
      fun is_full_path  ->
        let rec aux revns id1 =
          let lid = FStar_Ident.lid_of_ns_and_id (FStar_List.rev revns) id1
             in
          if namespace_is_open env lid
          then
            FStar_Pervasives_Native.Some
              ((FStar_List.rev (id1 :: revns)), [])
          else
            (match revns with
             | [] -> FStar_Pervasives_Native.None
             | ns_last_id::rev_ns_prefix ->
                 let uu____4021 = aux rev_ns_prefix ns_last_id  in
                 FStar_All.pipe_right uu____4021
                   (FStar_Util.map_option
                      (fun uu____4071  ->
                         match uu____4071 with
                         | (stripped_ids,rev_kept_ids) ->
                             (stripped_ids, (id1 :: rev_kept_ids)))))
           in
        let do_shorten env1 ids1 =
          match FStar_List.rev ids1 with
          | [] -> ([], [])
          | ns_last_id::ns_rev_prefix ->
              let uu____4141 = aux ns_rev_prefix ns_last_id  in
              (match uu____4141 with
               | FStar_Pervasives_Native.None  -> ([], ids1)
               | FStar_Pervasives_Native.Some (stripped_ids,rev_kept_ids) ->
                   (stripped_ids, (FStar_List.rev rev_kept_ids)))
           in
        if is_full_path && ((FStar_List.length ids) > (Prims.parse_int "0"))
        then
          let uu____4202 =
            let uu____4205 = FStar_Ident.lid_of_ids ids  in
            resolve_module_name env uu____4205 true  in
          match uu____4202 with
          | FStar_Pervasives_Native.Some m when module_is_open env m ->
              (ids, [])
          | uu____4219 -> do_shorten env ids
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
  fun env  ->
    fun lid  ->
      fun eikind  ->
        fun k_local_binding  ->
          fun k_rec_binding  ->
            fun k_record  ->
              fun f_module  ->
                fun l_default  ->
                  match lid.FStar_Ident.ns with
                  | uu____4338::uu____4339 ->
                      let uu____4342 =
                        let uu____4345 =
                          let uu____4346 =
                            FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
                          let uu____4347 = FStar_Ident.range_of_lid lid  in
                          FStar_Ident.set_lid_range uu____4346 uu____4347  in
                        resolve_module_name env uu____4345 true  in
                      (match uu____4342 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some modul ->
                           let uu____4351 =
                             find_in_module_with_includes eikind f_module
                               Cont_fail env modul lid.FStar_Ident.ident
                              in
                           option_of_cont
                             (fun uu____4355  -> FStar_Pervasives_Native.None)
                             uu____4351)
                  | [] ->
                      try_lookup_id'' env lid.FStar_Ident.ident eikind
                        k_local_binding k_rec_binding k_record f_module
                        l_default
  
let cont_of_option :
  'a . 'a cont_t -> 'a FStar_Pervasives_Native.option -> 'a cont_t =
  fun k_none  ->
    fun uu___174_4378  ->
      match uu___174_4378 with
      | FStar_Pervasives_Native.Some v1 -> Cont_ok v1
      | FStar_Pervasives_Native.None  -> k_none
  
let resolve_in_open_namespaces' :
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
              let uu____4494 = k_global_def lid1 def  in
              cont_of_option k uu____4494  in
            let f_module lid' =
              let k = Cont_ignore  in
              find_in_module env lid' (k_global_def' k) k  in
            let l_default k i = lookup_default_id env i (k_global_def' k) k
               in
            resolve_in_open_namespaces'' env lid Exported_id_term_type
              (fun l  ->
                 let uu____4530 = k_local_binding l  in
                 cont_of_option Cont_fail uu____4530)
              (fun r  ->
                 let uu____4536 = k_rec_binding r  in
                 cont_of_option Cont_fail uu____4536)
              (fun uu____4540  -> Cont_ignore) f_module l_default
  
let (fv_qual_of_se :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option)
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____4550,uu____4551,uu____4552,l,uu____4554,uu____4555) ->
        let qopt =
          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
            (fun uu___175_4566  ->
               match uu___175_4566 with
               | FStar_Syntax_Syntax.RecordConstructor (uu____4569,fs) ->
                   FStar_Pervasives_Native.Some
                     (FStar_Syntax_Syntax.Record_ctor (l, fs))
               | uu____4581 -> FStar_Pervasives_Native.None)
           in
        (match qopt with
         | FStar_Pervasives_Native.None  ->
             FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor
         | x -> x)
    | FStar_Syntax_Syntax.Sig_declare_typ (uu____4587,uu____4588,uu____4589)
        -> FStar_Pervasives_Native.None
    | uu____4590 -> FStar_Pervasives_Native.None
  
let (lb_fv :
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Ident.lident -> FStar_Syntax_Syntax.fv)
  =
  fun lbs  ->
    fun lid  ->
      let uu____4605 =
        FStar_Util.find_map lbs
          (fun lb  ->
             let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
             let uu____4613 = FStar_Syntax_Syntax.fv_eq_lid fv lid  in
             if uu____4613
             then FStar_Pervasives_Native.Some fv
             else FStar_Pervasives_Native.None)
         in
      FStar_All.pipe_right uu____4605 FStar_Util.must
  
let (ns_of_lid_equals :
  FStar_Ident.lident -> FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    fun ns  ->
      (let uu____4631 =
         let uu____4632 = FStar_Ident.ids_of_lid ns  in
         FStar_List.length uu____4632  in
       (FStar_List.length lid.FStar_Ident.ns) = uu____4631) &&
        (let uu____4640 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
         FStar_Ident.lid_equals uu____4640 ns)
  
let (try_lookup_name :
  Prims.bool ->
    Prims.bool ->
      env -> FStar_Ident.lident -> foundname FStar_Pervasives_Native.option)
  =
  fun any_val  ->
    fun exclude_interf  ->
      fun env  ->
        fun lid  ->
          let occurrence_range = FStar_Ident.range_of_lid lid  in
          let k_global_def source_lid uu___182_4682 =
            match uu___182_4682 with
            | (uu____4689,true ) when exclude_interf ->
                FStar_Pervasives_Native.None
            | (se,uu____4691) ->
                (match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_inductive_typ uu____4694 ->
                     let uu____4711 =
                       let uu____4712 =
                         let uu____4721 =
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None
                            in
                         (uu____4721, false,
                           (se.FStar_Syntax_Syntax.sigattrs))
                          in
                       Term_name uu____4712  in
                     FStar_Pervasives_Native.Some uu____4711
                 | FStar_Syntax_Syntax.Sig_datacon uu____4724 ->
                     let uu____4739 =
                       let uu____4740 =
                         let uu____4749 =
                           let uu____4750 = fv_qual_of_se se  in
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.delta_constant uu____4750
                            in
                         (uu____4749, false,
                           (se.FStar_Syntax_Syntax.sigattrs))
                          in
                       Term_name uu____4740  in
                     FStar_Pervasives_Native.Some uu____4739
                 | FStar_Syntax_Syntax.Sig_let ((uu____4755,lbs),uu____4757)
                     ->
                     let fv = lb_fv lbs source_lid  in
                     let uu____4767 =
                       let uu____4768 =
                         let uu____4777 =
                           FStar_Syntax_Syntax.fvar source_lid
                             fv.FStar_Syntax_Syntax.fv_delta
                             fv.FStar_Syntax_Syntax.fv_qual
                            in
                         (uu____4777, false,
                           (se.FStar_Syntax_Syntax.sigattrs))
                          in
                       Term_name uu____4768  in
                     FStar_Pervasives_Native.Some uu____4767
                 | FStar_Syntax_Syntax.Sig_declare_typ
                     (lid1,uu____4781,uu____4782) ->
                     let quals = se.FStar_Syntax_Syntax.sigquals  in
                     let uu____4786 =
                       any_val ||
                         (FStar_All.pipe_right quals
                            (FStar_Util.for_some
                               (fun uu___176_4790  ->
                                  match uu___176_4790 with
                                  | FStar_Syntax_Syntax.Assumption  -> true
                                  | uu____4791 -> false)))
                        in
                     if uu____4786
                     then
                       let lid2 =
                         let uu____4795 = FStar_Ident.range_of_lid source_lid
                            in
                         FStar_Ident.set_lid_range lid1 uu____4795  in
                       let dd =
                         let uu____4797 =
                           (FStar_Syntax_Util.is_primop_lid lid2) ||
                             (FStar_All.pipe_right quals
                                (FStar_Util.for_some
                                   (fun uu___177_4802  ->
                                      match uu___177_4802 with
                                      | FStar_Syntax_Syntax.Projector
                                          uu____4803 -> true
                                      | FStar_Syntax_Syntax.Discriminator
                                          uu____4808 -> true
                                      | uu____4809 -> false)))
                            in
                         if uu____4797
                         then FStar_Syntax_Syntax.delta_equational
                         else FStar_Syntax_Syntax.delta_constant  in
                       let dd1 =
                         let uu____4812 =
                           (FStar_All.pipe_right quals
                              (FStar_Util.for_some
                                 (fun uu___178_4816  ->
                                    match uu___178_4816 with
                                    | FStar_Syntax_Syntax.Abstract  -> true
                                    | uu____4817 -> false)))
                             ||
                             ((FStar_All.pipe_right quals
                                 (FStar_Util.for_some
                                    (fun uu___179_4821  ->
                                       match uu___179_4821 with
                                       | FStar_Syntax_Syntax.Assumption  ->
                                           true
                                       | uu____4822 -> false)))
                                &&
                                (let uu____4824 =
                                   FStar_All.pipe_right quals
                                     (FStar_Util.for_some
                                        (fun uu___180_4828  ->
                                           match uu___180_4828 with
                                           | FStar_Syntax_Syntax.New  -> true
                                           | uu____4829 -> false))
                                    in
                                 Prims.op_Negation uu____4824))
                            in
                         if uu____4812
                         then FStar_Syntax_Syntax.Delta_abstract dd
                         else dd  in
                       let uu____4831 =
                         FStar_Util.find_map quals
                           (fun uu___181_4836  ->
                              match uu___181_4836 with
                              | FStar_Syntax_Syntax.Reflectable refl_monad ->
                                  FStar_Pervasives_Native.Some refl_monad
                              | uu____4840 -> FStar_Pervasives_Native.None)
                          in
                       (match uu____4831 with
                        | FStar_Pervasives_Native.Some refl_monad ->
                            let refl_const =
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_constant
                                   (FStar_Const.Const_reflect refl_monad))
                                FStar_Pervasives_Native.None occurrence_range
                               in
                            FStar_Pervasives_Native.Some
                              (Term_name
                                 (refl_const, false,
                                   (se.FStar_Syntax_Syntax.sigattrs)))
                        | uu____4849 ->
                            let uu____4852 =
                              let uu____4853 =
                                let uu____4862 =
                                  let uu____4863 = fv_qual_of_se se  in
                                  FStar_Syntax_Syntax.fvar lid2 dd1
                                    uu____4863
                                   in
                                (uu____4862, false,
                                  (se.FStar_Syntax_Syntax.sigattrs))
                                 in
                              Term_name uu____4853  in
                            FStar_Pervasives_Native.Some uu____4852)
                     else FStar_Pervasives_Native.None
                 | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
                     let uu____4870 =
                       let uu____4871 =
                         let uu____4876 =
                           let uu____4877 =
                             FStar_Ident.range_of_lid source_lid  in
                           FStar_Ident.set_lid_range
                             ne.FStar_Syntax_Syntax.mname uu____4877
                            in
                         (se, uu____4876)  in
                       Eff_name uu____4871  in
                     FStar_Pervasives_Native.Some uu____4870
                 | FStar_Syntax_Syntax.Sig_new_effect ne ->
                     let uu____4879 =
                       let uu____4880 =
                         let uu____4885 =
                           let uu____4886 =
                             FStar_Ident.range_of_lid source_lid  in
                           FStar_Ident.set_lid_range
                             ne.FStar_Syntax_Syntax.mname uu____4886
                            in
                         (se, uu____4885)  in
                       Eff_name uu____4880  in
                     FStar_Pervasives_Native.Some uu____4879
                 | FStar_Syntax_Syntax.Sig_effect_abbrev uu____4887 ->
                     FStar_Pervasives_Native.Some (Eff_name (se, source_lid))
                 | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
                     let uu____4906 =
                       let uu____4907 =
                         let uu____4916 =
                           FStar_Syntax_Syntax.fvar source_lid
                             (FStar_Syntax_Syntax.Delta_constant_at_level
                                (Prims.parse_int "1"))
                             FStar_Pervasives_Native.None
                            in
                         (uu____4916, false, [])  in
                       Term_name uu____4907  in
                     FStar_Pervasives_Native.Some uu____4906
                 | uu____4919 -> FStar_Pervasives_Native.None)
             in
          let k_local_binding r =
            let uu____4940 =
              let uu____4945 = FStar_Ident.range_of_lid lid  in
              found_local_binding uu____4945 r  in
            match uu____4940 with
            | (t,mut) ->
                FStar_Pervasives_Native.Some (Term_name (t, mut, []))
             in
          let k_rec_binding uu____4965 =
            match uu____4965 with
            | (id1,l,dd) ->
                let uu____4977 =
                  let uu____4978 =
                    let uu____4987 =
                      let uu____4988 =
                        let uu____4989 = FStar_Ident.range_of_lid lid  in
                        FStar_Ident.set_lid_range l uu____4989  in
                      FStar_Syntax_Syntax.fvar uu____4988 dd
                        FStar_Pervasives_Native.None
                       in
                    (uu____4987, false, [])  in
                  Term_name uu____4978  in
                FStar_Pervasives_Native.Some uu____4977
             in
          let found_unmangled =
            match lid.FStar_Ident.ns with
            | [] ->
                let uu____4997 = unmangleOpName lid.FStar_Ident.ident  in
                (match uu____4997 with
                 | FStar_Pervasives_Native.Some (t,mut) ->
                     FStar_Pervasives_Native.Some (Term_name (t, mut, []))
                 | uu____5014 -> FStar_Pervasives_Native.None)
            | uu____5021 -> FStar_Pervasives_Native.None  in
          match found_unmangled with
          | FStar_Pervasives_Native.None  ->
              resolve_in_open_namespaces' env lid k_local_binding
                k_rec_binding k_global_def
          | x -> x
  
let (try_lookup_effect_name' :
  Prims.bool ->
    env ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.sigelt,FStar_Ident.lident)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun exclude_interf  ->
    fun env  ->
      fun lid  ->
        let uu____5056 = try_lookup_name true exclude_interf env lid  in
        match uu____5056 with
        | FStar_Pervasives_Native.Some (Eff_name (o,l)) ->
            FStar_Pervasives_Native.Some (o, l)
        | uu____5071 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____5090 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____5090 with
      | FStar_Pervasives_Native.Some (o,l1) ->
          FStar_Pervasives_Native.Some l1
      | uu____5105 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_name_and_attributes :
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident,FStar_Syntax_Syntax.cflags Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____5130 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____5130 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____5146;
             FStar_Syntax_Syntax.sigquals = uu____5147;
             FStar_Syntax_Syntax.sigmeta = uu____5148;
             FStar_Syntax_Syntax.sigattrs = uu____5149;_},l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____5168;
             FStar_Syntax_Syntax.sigquals = uu____5169;
             FStar_Syntax_Syntax.sigmeta = uu____5170;
             FStar_Syntax_Syntax.sigattrs = uu____5171;_},l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (uu____5189,uu____5190,uu____5191,uu____5192,cattributes);
             FStar_Syntax_Syntax.sigrng = uu____5194;
             FStar_Syntax_Syntax.sigquals = uu____5195;
             FStar_Syntax_Syntax.sigmeta = uu____5196;
             FStar_Syntax_Syntax.sigattrs = uu____5197;_},l1)
          -> FStar_Pervasives_Native.Some (l1, cattributes)
      | uu____5219 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_defn :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.eff_decl FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____5244 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____5244 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____5254;
             FStar_Syntax_Syntax.sigquals = uu____5255;
             FStar_Syntax_Syntax.sigmeta = uu____5256;
             FStar_Syntax_Syntax.sigattrs = uu____5257;_},uu____5258)
          -> FStar_Pervasives_Native.Some ne
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____5268;
             FStar_Syntax_Syntax.sigquals = uu____5269;
             FStar_Syntax_Syntax.sigmeta = uu____5270;
             FStar_Syntax_Syntax.sigattrs = uu____5271;_},uu____5272)
          -> FStar_Pervasives_Native.Some ne
      | uu____5281 -> FStar_Pervasives_Native.None
  
let (is_effect_name : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____5298 = try_lookup_effect_name env lid  in
      match uu____5298 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____5301 -> true
  
let (try_lookup_root_effect_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____5314 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____5314 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (l',uu____5324,uu____5325,uu____5326,uu____5327);
             FStar_Syntax_Syntax.sigrng = uu____5328;
             FStar_Syntax_Syntax.sigquals = uu____5329;
             FStar_Syntax_Syntax.sigmeta = uu____5330;
             FStar_Syntax_Syntax.sigattrs = uu____5331;_},uu____5332)
          ->
          let rec aux new_name =
            let uu____5353 =
              FStar_Util.smap_try_find (sigmap env) new_name.FStar_Ident.str
               in
            match uu____5353 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (s,uu____5371) ->
                (match s.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
                     let uu____5379 =
                       let uu____5380 = FStar_Ident.range_of_lid l  in
                       FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname
                         uu____5380
                        in
                     FStar_Pervasives_Native.Some uu____5379
                 | FStar_Syntax_Syntax.Sig_new_effect ne ->
                     let uu____5382 =
                       let uu____5383 = FStar_Ident.range_of_lid l  in
                       FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname
                         uu____5383
                        in
                     FStar_Pervasives_Native.Some uu____5382
                 | FStar_Syntax_Syntax.Sig_effect_abbrev
                     (uu____5384,uu____5385,uu____5386,cmp,uu____5388) ->
                     let l'' = FStar_Syntax_Util.comp_effect_name cmp  in
                     aux l''
                 | uu____5394 -> FStar_Pervasives_Native.None)
             in
          aux l'
      | FStar_Pervasives_Native.Some (uu____5395,l') ->
          FStar_Pervasives_Native.Some l'
      | uu____5401 -> FStar_Pervasives_Native.None
  
let (lookup_letbinding_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___183_5438 =
        match uu___183_5438 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____5447,uu____5448,uu____5449);
             FStar_Syntax_Syntax.sigrng = uu____5450;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____5452;
             FStar_Syntax_Syntax.sigattrs = uu____5453;_},uu____5454)
            -> FStar_Pervasives_Native.Some quals
        | uu____5461 -> FStar_Pervasives_Native.None  in
      let uu____5468 =
        resolve_in_open_namespaces' env lid
          (fun uu____5476  -> FStar_Pervasives_Native.None)
          (fun uu____5480  -> FStar_Pervasives_Native.None) k_global_def
         in
      match uu____5468 with
      | FStar_Pervasives_Native.Some quals -> quals
      | uu____5490 -> []
  
let (try_lookup_module :
  env ->
    FStar_Ident.path ->
      FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun path  ->
      let uu____5507 =
        FStar_List.tryFind
          (fun uu____5522  ->
             match uu____5522 with
             | (mlid,modul) ->
                 let uu____5529 = FStar_Ident.path_of_lid mlid  in
                 uu____5529 = path) env.modules
         in
      match uu____5507 with
      | FStar_Pervasives_Native.Some (uu____5532,modul) ->
          FStar_Pervasives_Native.Some modul
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (try_lookup_let :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___184_5570 =
        match uu___184_5570 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               ((uu____5577,lbs),uu____5579);
             FStar_Syntax_Syntax.sigrng = uu____5580;
             FStar_Syntax_Syntax.sigquals = uu____5581;
             FStar_Syntax_Syntax.sigmeta = uu____5582;
             FStar_Syntax_Syntax.sigattrs = uu____5583;_},uu____5584)
            ->
            let fv = lb_fv lbs lid1  in
            let uu____5598 =
              FStar_Syntax_Syntax.fvar lid1 fv.FStar_Syntax_Syntax.fv_delta
                fv.FStar_Syntax_Syntax.fv_qual
               in
            FStar_Pervasives_Native.Some uu____5598
        | uu____5599 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____5605  -> FStar_Pervasives_Native.None)
        (fun uu____5607  -> FStar_Pervasives_Native.None) k_global_def
  
let (try_lookup_definition :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___185_5638 =
        match uu___185_5638 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               (lbs,uu____5648);
             FStar_Syntax_Syntax.sigrng = uu____5649;
             FStar_Syntax_Syntax.sigquals = uu____5650;
             FStar_Syntax_Syntax.sigmeta = uu____5651;
             FStar_Syntax_Syntax.sigattrs = uu____5652;_},uu____5653)
            ->
            FStar_Util.find_map (FStar_Pervasives_Native.snd lbs)
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inr fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv lid1 ->
                     FStar_Pervasives_Native.Some
                       (lb.FStar_Syntax_Syntax.lbdef)
                 | uu____5676 -> FStar_Pervasives_Native.None)
        | uu____5683 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____5693  -> FStar_Pervasives_Native.None)
        (fun uu____5697  -> FStar_Pervasives_Native.None) k_global_def
  
let (empty_include_smap :
  FStar_Ident.lident Prims.list FStar_ST.ref FStar_Util.smap) = new_sigmap () 
let (empty_exported_id_smap : exported_id_set FStar_Util.smap) =
  new_sigmap () 
let (try_lookup_lid' :
  Prims.bool ->
    Prims.bool ->
      env ->
        FStar_Ident.lident ->
          (FStar_Syntax_Syntax.term,Prims.bool,FStar_Syntax_Syntax.attribute
                                                 Prims.list)
            FStar_Pervasives_Native.tuple3 FStar_Pervasives_Native.option)
  =
  fun any_val  ->
    fun exclude_interface  ->
      fun env  ->
        fun lid  ->
          let uu____5754 = try_lookup_name any_val exclude_interface env lid
             in
          match uu____5754 with
          | FStar_Pervasives_Native.Some (Term_name (e,mut,attrs)) ->
              FStar_Pervasives_Native.Some (e, mut, attrs)
          | uu____5784 -> FStar_Pervasives_Native.None
  
let (drop_attributes :
  (FStar_Syntax_Syntax.term,Prims.bool,FStar_Syntax_Syntax.attribute
                                         Prims.list)
    FStar_Pervasives_Native.tuple3 FStar_Pervasives_Native.option ->
    (FStar_Syntax_Syntax.term,Prims.bool) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option)
  =
  fun x  ->
    match x with
    | FStar_Pervasives_Native.Some (t,mut,uu____5840) ->
        FStar_Pervasives_Native.Some (t, mut)
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (try_lookup_lid_with_attributes :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term,Prims.bool,FStar_Syntax_Syntax.attribute
                                             Prims.list)
        FStar_Pervasives_Native.tuple3 FStar_Pervasives_Native.option)
  = fun env  -> fun l  -> try_lookup_lid' env.iface false env l 
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term,Prims.bool) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____5915 = try_lookup_lid_with_attributes env l  in
      FStar_All.pipe_right uu____5915 drop_attributes
  
let (resolve_to_fully_qualified_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____5954 = try_lookup_lid env l  in
      match uu____5954 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (e,uu____5968) ->
          let uu____5973 =
            let uu____5974 = FStar_Syntax_Subst.compress e  in
            uu____5974.FStar_Syntax_Syntax.n  in
          (match uu____5973 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               FStar_Pervasives_Native.Some
                 ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
           | uu____5980 -> FStar_Pervasives_Native.None)
  
let (shorten_lid' : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____5991 = shorten_module_path env lid.FStar_Ident.ns true  in
      match uu____5991 with
      | (uu____6000,short) ->
          FStar_Ident.lid_of_ns_and_id short lid.FStar_Ident.ident
  
let (shorten_lid : env -> FStar_Ident.lid -> FStar_Ident.lid) =
  fun env  ->
    fun lid  ->
      match env.curmodule with
      | FStar_Pervasives_Native.None  -> shorten_lid' env lid
      | uu____6020 ->
          let lid_without_ns =
            FStar_Ident.lid_of_ns_and_id [] lid.FStar_Ident.ident  in
          let uu____6024 = resolve_to_fully_qualified_name env lid_without_ns
             in
          (match uu____6024 with
           | FStar_Pervasives_Native.Some lid' when
               lid'.FStar_Ident.str = lid.FStar_Ident.str -> lid_without_ns
           | uu____6028 -> shorten_lid' env lid)
  
let (try_lookup_lid_with_attributes_no_resolve :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term,Prims.bool,FStar_Syntax_Syntax.attribute
                                             Prims.list)
        FStar_Pervasives_Native.tuple3 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let env' =
        let uu___205_6062 = env  in
        {
          curmodule = (uu___205_6062.curmodule);
          curmonad = (uu___205_6062.curmonad);
          modules = (uu___205_6062.modules);
          scope_mods = [];
          exported_ids = empty_exported_id_smap;
          trans_exported_ids = (uu___205_6062.trans_exported_ids);
          includes = empty_include_smap;
          sigaccum = (uu___205_6062.sigaccum);
          sigmap = (uu___205_6062.sigmap);
          iface = (uu___205_6062.iface);
          admitted_iface = (uu___205_6062.admitted_iface);
          expect_typ = (uu___205_6062.expect_typ);
          docs = (uu___205_6062.docs);
          remaining_iface_decls = (uu___205_6062.remaining_iface_decls);
          syntax_only = (uu___205_6062.syntax_only);
          ds_hooks = (uu___205_6062.ds_hooks);
          dep_graph = (uu___205_6062.dep_graph)
        }  in
      try_lookup_lid_with_attributes env' l
  
let (try_lookup_lid_no_resolve :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term,Prims.bool) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____6085 = try_lookup_lid_with_attributes_no_resolve env l  in
      FStar_All.pipe_right uu____6085 drop_attributes
  
let (try_lookup_doc :
  env ->
    FStar_Ident.lid -> FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option)
  = fun env  -> fun l  -> FStar_Util.smap_try_find env.docs l.FStar_Ident.str 
let (try_lookup_datacon :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.fv FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 se =
        match se with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____6159,uu____6160,uu____6161);
             FStar_Syntax_Syntax.sigrng = uu____6162;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____6164;
             FStar_Syntax_Syntax.sigattrs = uu____6165;_},uu____6166)
            ->
            let uu____6171 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___186_6175  ->
                      match uu___186_6175 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | uu____6176 -> false))
               in
            if uu____6171
            then
              let uu____6179 =
                FStar_Syntax_Syntax.lid_as_fv lid1
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Pervasives_Native.Some uu____6179
            else FStar_Pervasives_Native.None
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
               uu____6181;
             FStar_Syntax_Syntax.sigrng = uu____6182;
             FStar_Syntax_Syntax.sigquals = uu____6183;
             FStar_Syntax_Syntax.sigmeta = uu____6184;
             FStar_Syntax_Syntax.sigattrs = uu____6185;_},uu____6186)
            ->
            let qual1 = fv_qual_of_se (FStar_Pervasives_Native.fst se)  in
            let uu____6208 =
              FStar_Syntax_Syntax.lid_as_fv lid1
                FStar_Syntax_Syntax.delta_constant qual1
               in
            FStar_Pervasives_Native.Some uu____6208
        | uu____6209 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____6215  -> FStar_Pervasives_Native.None)
        (fun uu____6217  -> FStar_Pervasives_Native.None) k_global_def
  
let (find_all_datacons :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___187_6250 =
        match uu___187_6250 with
        | ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_inductive_typ
               (uu____6259,uu____6260,uu____6261,uu____6262,datas,uu____6264);
             FStar_Syntax_Syntax.sigrng = uu____6265;
             FStar_Syntax_Syntax.sigquals = uu____6266;
             FStar_Syntax_Syntax.sigmeta = uu____6267;
             FStar_Syntax_Syntax.sigattrs = uu____6268;_},uu____6269)
            -> FStar_Pervasives_Native.Some datas
        | uu____6284 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____6294  -> FStar_Pervasives_Native.None)
        (fun uu____6298  -> FStar_Pervasives_Native.None) k_global_def
  
let (record_cache_aux_with_filter :
  (((unit -> unit,unit -> unit) FStar_Pervasives_Native.tuple2,((unit ->
                                                                   (Prims.int,
                                                                    unit)
                                                                    FStar_Pervasives_Native.tuple2,
                                                                  Prims.int
                                                                    FStar_Pervasives_Native.option
                                                                    -> 
                                                                    unit)
                                                                  FStar_Pervasives_Native.tuple2,
                                                                 (unit ->
                                                                    record_or_dc
                                                                    Prims.list,
                                                                   record_or_dc
                                                                    -> 
                                                                    unit)
                                                                   FStar_Pervasives_Native.tuple2)
                                                                 FStar_Pervasives_Native.tuple2)
     FStar_Pervasives_Native.tuple2,unit -> unit)
    FStar_Pervasives_Native.tuple2)
  =
  let record_cache = FStar_Util.mk_ref [[]]  in
  let push1 uu____6374 =
    let uu____6375 =
      let uu____6380 =
        let uu____6383 = FStar_ST.op_Bang record_cache  in
        FStar_List.hd uu____6383  in
      let uu____6439 = FStar_ST.op_Bang record_cache  in uu____6380 ::
        uu____6439
       in
    FStar_ST.op_Colon_Equals record_cache uu____6375  in
  let pop1 uu____6549 =
    let uu____6550 =
      let uu____6555 = FStar_ST.op_Bang record_cache  in
      FStar_List.tl uu____6555  in
    FStar_ST.op_Colon_Equals record_cache uu____6550  in
  let snapshot1 uu____6669 = FStar_Common.snapshot push1 record_cache ()  in
  let rollback1 depth = FStar_Common.rollback pop1 record_cache depth  in
  let peek1 uu____6735 =
    let uu____6736 = FStar_ST.op_Bang record_cache  in
    FStar_List.hd uu____6736  in
  let insert r =
    let uu____6798 =
      let uu____6803 = let uu____6806 = peek1 ()  in r :: uu____6806  in
      let uu____6809 =
        let uu____6814 = FStar_ST.op_Bang record_cache  in
        FStar_List.tl uu____6814  in
      uu____6803 :: uu____6809  in
    FStar_ST.op_Colon_Equals record_cache uu____6798  in
  let filter1 uu____6926 =
    let rc = peek1 ()  in
    let filtered =
      FStar_List.filter
        (fun r  -> Prims.op_Negation r.is_private_or_abstract) rc
       in
    let uu____6935 =
      let uu____6940 =
        let uu____6945 = FStar_ST.op_Bang record_cache  in
        FStar_List.tl uu____6945  in
      filtered :: uu____6940  in
    FStar_ST.op_Colon_Equals record_cache uu____6935  in
  let aux = ((push1, pop1), ((snapshot1, rollback1), (peek1, insert)))  in
  (aux, filter1) 
let (record_cache_aux :
  ((unit -> unit,unit -> unit) FStar_Pervasives_Native.tuple2,((unit ->
                                                                  (Prims.int,
                                                                    unit)
                                                                    FStar_Pervasives_Native.tuple2,
                                                                 Prims.int
                                                                   FStar_Pervasives_Native.option
                                                                   -> 
                                                                   unit)
                                                                 FStar_Pervasives_Native.tuple2,
                                                                (unit ->
                                                                   record_or_dc
                                                                    Prims.list,
                                                                  record_or_dc
                                                                    -> 
                                                                    unit)
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
  unit -> (Prims.int,unit) FStar_Pervasives_Native.tuple2) =
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
  fun e  ->
    fun new_globs  ->
      fun se  ->
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_bundle (sigs,uu____7886) ->
            let is_record =
              FStar_Util.for_some
                (fun uu___188_7904  ->
                   match uu___188_7904 with
                   | FStar_Syntax_Syntax.RecordType uu____7905 -> true
                   | FStar_Syntax_Syntax.RecordConstructor uu____7914 -> true
                   | uu____7923 -> false)
               in
            let find_dc dc =
              FStar_All.pipe_right sigs
                (FStar_Util.find_opt
                   (fun uu___189_7947  ->
                      match uu___189_7947 with
                      | {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_datacon
                            (lid,uu____7949,uu____7950,uu____7951,uu____7952,uu____7953);
                          FStar_Syntax_Syntax.sigrng = uu____7954;
                          FStar_Syntax_Syntax.sigquals = uu____7955;
                          FStar_Syntax_Syntax.sigmeta = uu____7956;
                          FStar_Syntax_Syntax.sigattrs = uu____7957;_} ->
                          FStar_Ident.lid_equals dc lid
                      | uu____7966 -> false))
               in
            FStar_All.pipe_right sigs
              (FStar_List.iter
                 (fun uu___190_8001  ->
                    match uu___190_8001 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ
                          (typename,univs1,parms,uu____8005,uu____8006,dc::[]);
                        FStar_Syntax_Syntax.sigrng = uu____8008;
                        FStar_Syntax_Syntax.sigquals = typename_quals;
                        FStar_Syntax_Syntax.sigmeta = uu____8010;
                        FStar_Syntax_Syntax.sigattrs = uu____8011;_} ->
                        let uu____8022 =
                          let uu____8023 = find_dc dc  in
                          FStar_All.pipe_left FStar_Util.must uu____8023  in
                        (match uu____8022 with
                         | {
                             FStar_Syntax_Syntax.sigel =
                               FStar_Syntax_Syntax.Sig_datacon
                               (constrname,uu____8029,t,uu____8031,uu____8032,uu____8033);
                             FStar_Syntax_Syntax.sigrng = uu____8034;
                             FStar_Syntax_Syntax.sigquals = uu____8035;
                             FStar_Syntax_Syntax.sigmeta = uu____8036;
                             FStar_Syntax_Syntax.sigattrs = uu____8037;_} ->
                             let uu____8046 =
                               FStar_Syntax_Util.arrow_formals t  in
                             (match uu____8046 with
                              | (formals,uu____8062) ->
                                  let is_rec = is_record typename_quals  in
                                  let formals' =
                                    FStar_All.pipe_right formals
                                      (FStar_List.collect
                                         (fun uu____8115  ->
                                            match uu____8115 with
                                            | (x,q) ->
                                                let uu____8128 =
                                                  (FStar_Syntax_Syntax.is_null_bv
                                                     x)
                                                    ||
                                                    (is_rec &&
                                                       (FStar_Syntax_Syntax.is_implicit
                                                          q))
                                                   in
                                                if uu____8128
                                                then []
                                                else [(x, q)]))
                                     in
                                  let fields' =
                                    FStar_All.pipe_right formals'
                                      (FStar_List.map
                                         (fun uu____8181  ->
                                            match uu____8181 with
                                            | (x,q) ->
                                                let uu____8194 =
                                                  if is_rec
                                                  then
                                                    FStar_Syntax_Util.unmangle_field_name
                                                      x.FStar_Syntax_Syntax.ppname
                                                  else
                                                    x.FStar_Syntax_Syntax.ppname
                                                   in
                                                (uu____8194,
                                                  (x.FStar_Syntax_Syntax.sort))))
                                     in
                                  let fields = fields'  in
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
                                    }  in
                                  ((let uu____8207 =
                                      let uu____8210 =
                                        FStar_ST.op_Bang new_globs  in
                                      (Record_or_dc record) :: uu____8210  in
                                    FStar_ST.op_Colon_Equals new_globs
                                      uu____8207);
                                   (match () with
                                    | () ->
                                        ((let add_field uu____8313 =
                                            match uu____8313 with
                                            | (id1,uu____8319) ->
                                                let modul =
                                                  let uu____8321 =
                                                    FStar_Ident.lid_of_ids
                                                      constrname.FStar_Ident.ns
                                                     in
                                                  uu____8321.FStar_Ident.str
                                                   in
                                                let uu____8322 =
                                                  get_exported_id_set e modul
                                                   in
                                                (match uu____8322 with
                                                 | FStar_Pervasives_Native.Some
                                                     my_ex ->
                                                     let my_exported_ids =
                                                       my_ex
                                                         Exported_id_field
                                                        in
                                                     ((let uu____8356 =
                                                         let uu____8357 =
                                                           FStar_ST.op_Bang
                                                             my_exported_ids
                                                            in
                                                         FStar_Util.set_add
                                                           id1.FStar_Ident.idText
                                                           uu____8357
                                                          in
                                                       FStar_ST.op_Colon_Equals
                                                         my_exported_ids
                                                         uu____8356);
                                                      (match () with
                                                       | () ->
                                                           let projname =
                                                             let uu____8443 =
                                                               let uu____8444
                                                                 =
                                                                 FStar_Syntax_Util.mk_field_projector_name_from_ident
                                                                   constrname
                                                                   id1
                                                                  in
                                                               uu____8444.FStar_Ident.ident
                                                                in
                                                             uu____8443.FStar_Ident.idText
                                                              in
                                                           let uu____8446 =
                                                             let uu____8447 =
                                                               FStar_ST.op_Bang
                                                                 my_exported_ids
                                                                in
                                                             FStar_Util.set_add
                                                               projname
                                                               uu____8447
                                                              in
                                                           FStar_ST.op_Colon_Equals
                                                             my_exported_ids
                                                             uu____8446))
                                                 | FStar_Pervasives_Native.None
                                                      -> ())
                                             in
                                          FStar_List.iter add_field fields');
                                         (match () with
                                          | () -> insert_record_cache record)))))
                         | uu____8541 -> ())
                    | uu____8542 -> ()))
        | uu____8543 -> ()
  
let (try_lookup_record_or_dc_by_field_name :
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option) =
  fun env  ->
    fun fieldname  ->
      let find_in_cache fieldname1 =
        let uu____8564 =
          ((fieldname1.FStar_Ident.ns), (fieldname1.FStar_Ident.ident))  in
        match uu____8564 with
        | (ns,id1) ->
            let uu____8581 = peek_record_cache ()  in
            FStar_Util.find_map uu____8581
              (fun record  ->
                 let uu____8587 =
                   find_in_record ns id1 record (fun r  -> Cont_ok r)  in
                 option_of_cont
                   (fun uu____8593  -> FStar_Pervasives_Native.None)
                   uu____8587)
         in
      resolve_in_open_namespaces'' env fieldname Exported_id_field
        (fun uu____8595  -> Cont_ignore) (fun uu____8597  -> Cont_ignore)
        (fun r  -> Cont_ok r)
        (fun fn  ->
           let uu____8603 = find_in_cache fn  in
           cont_of_option Cont_ignore uu____8603)
        (fun k  -> fun uu____8609  -> k)
  
let (try_lookup_record_by_field_name :
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option) =
  fun env  ->
    fun fieldname  ->
      let uu____8624 = try_lookup_record_or_dc_by_field_name env fieldname
         in
      match uu____8624 with
      | FStar_Pervasives_Native.Some r when r.is_record ->
          FStar_Pervasives_Native.Some r
      | uu____8630 -> FStar_Pervasives_Native.None
  
let (belongs_to_record :
  env -> FStar_Ident.lident -> record_or_dc -> Prims.bool) =
  fun env  ->
    fun lid  ->
      fun record  ->
        let uu____8648 = try_lookup_record_by_field_name env lid  in
        match uu____8648 with
        | FStar_Pervasives_Native.Some record' when
            let uu____8652 =
              let uu____8653 =
                FStar_Ident.path_of_ns (record.typename).FStar_Ident.ns  in
              FStar_Ident.text_of_path uu____8653  in
            let uu____8654 =
              let uu____8655 =
                FStar_Ident.path_of_ns (record'.typename).FStar_Ident.ns  in
              FStar_Ident.text_of_path uu____8655  in
            uu____8652 = uu____8654 ->
            let uu____8656 =
              find_in_record (record.typename).FStar_Ident.ns
                lid.FStar_Ident.ident record (fun uu____8660  -> Cont_ok ())
               in
            (match uu____8656 with
             | Cont_ok uu____8661 -> true
             | uu____8662 -> false)
        | uu____8665 -> false
  
let (try_lookup_dc_by_field_name :
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident,Prims.bool) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun fieldname  ->
      let uu____8684 = try_lookup_record_or_dc_by_field_name env fieldname
         in
      match uu____8684 with
      | FStar_Pervasives_Native.Some r ->
          let uu____8694 =
            let uu____8699 =
              let uu____8700 =
                FStar_Ident.lid_of_ids
                  (FStar_List.append (r.typename).FStar_Ident.ns
                     [r.constrname])
                 in
              let uu____8701 = FStar_Ident.range_of_lid fieldname  in
              FStar_Ident.set_lid_range uu____8700 uu____8701  in
            (uu____8699, (r.is_record))  in
          FStar_Pervasives_Native.Some uu____8694
      | uu____8706 -> FStar_Pervasives_Native.None
  
let (string_set_ref_new : unit -> Prims.string FStar_Util.set FStar_ST.ref) =
  fun uu____8732  ->
    let uu____8733 = FStar_Util.new_set FStar_Util.compare  in
    FStar_Util.mk_ref uu____8733
  
let (exported_id_set_new :
  unit -> exported_id_kind -> Prims.string FStar_Util.set FStar_ST.ref) =
  fun uu____8760  ->
    let term_type_set = string_set_ref_new ()  in
    let field_set = string_set_ref_new ()  in
    fun uu___191_8771  ->
      match uu___191_8771 with
      | Exported_id_term_type  -> term_type_set
      | Exported_id_field  -> field_set
  
let (unique :
  Prims.bool -> Prims.bool -> env -> FStar_Ident.lident -> Prims.bool) =
  fun any_val  ->
    fun exclude_interface  ->
      fun env  ->
        fun lid  ->
          let filter_scope_mods uu___192_8823 =
            match uu___192_8823 with
            | Rec_binding uu____8824 -> true
            | uu____8825 -> false  in
          let this_env =
            let uu___206_8827 = env  in
            let uu____8828 =
              FStar_List.filter filter_scope_mods env.scope_mods  in
            {
              curmodule = (uu___206_8827.curmodule);
              curmonad = (uu___206_8827.curmonad);
              modules = (uu___206_8827.modules);
              scope_mods = uu____8828;
              exported_ids = empty_exported_id_smap;
              trans_exported_ids = (uu___206_8827.trans_exported_ids);
              includes = empty_include_smap;
              sigaccum = (uu___206_8827.sigaccum);
              sigmap = (uu___206_8827.sigmap);
              iface = (uu___206_8827.iface);
              admitted_iface = (uu___206_8827.admitted_iface);
              expect_typ = (uu___206_8827.expect_typ);
              docs = (uu___206_8827.docs);
              remaining_iface_decls = (uu___206_8827.remaining_iface_decls);
              syntax_only = (uu___206_8827.syntax_only);
              ds_hooks = (uu___206_8827.ds_hooks);
              dep_graph = (uu___206_8827.dep_graph)
            }  in
          let uu____8831 =
            try_lookup_lid' any_val exclude_interface this_env lid  in
          match uu____8831 with
          | FStar_Pervasives_Native.None  -> true
          | FStar_Pervasives_Native.Some uu____8850 -> false
  
let (push_scope_mod : env -> scope_mod -> env) =
  fun env  ->
    fun scope_mod  ->
      let uu___207_8877 = env  in
      {
        curmodule = (uu___207_8877.curmodule);
        curmonad = (uu___207_8877.curmonad);
        modules = (uu___207_8877.modules);
        scope_mods = (scope_mod :: (env.scope_mods));
        exported_ids = (uu___207_8877.exported_ids);
        trans_exported_ids = (uu___207_8877.trans_exported_ids);
        includes = (uu___207_8877.includes);
        sigaccum = (uu___207_8877.sigaccum);
        sigmap = (uu___207_8877.sigmap);
        iface = (uu___207_8877.iface);
        admitted_iface = (uu___207_8877.admitted_iface);
        expect_typ = (uu___207_8877.expect_typ);
        docs = (uu___207_8877.docs);
        remaining_iface_decls = (uu___207_8877.remaining_iface_decls);
        syntax_only = (uu___207_8877.syntax_only);
        ds_hooks = (uu___207_8877.ds_hooks);
        dep_graph = (uu___207_8877.dep_graph)
      }
  
let (push_bv' :
  env ->
    FStar_Ident.ident ->
      Prims.bool ->
        (env,FStar_Syntax_Syntax.bv) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun x  ->
      fun is_mutable  ->
        let bv =
          FStar_Syntax_Syntax.gen_bv x.FStar_Ident.idText
            (FStar_Pervasives_Native.Some (x.FStar_Ident.idRange))
            FStar_Syntax_Syntax.tun
           in
        ((push_scope_mod env (Local_binding (x, bv, is_mutable))), bv)
  
let (push_bv_mutable :
  env ->
    FStar_Ident.ident ->
      (env,FStar_Syntax_Syntax.bv) FStar_Pervasives_Native.tuple2)
  = fun env  -> fun x  -> push_bv' env x true 
let (push_bv :
  env ->
    FStar_Ident.ident ->
      (env,FStar_Syntax_Syntax.bv) FStar_Pervasives_Native.tuple2)
  = fun env  -> fun x  -> push_bv' env x false 
let (push_top_level_rec_binding :
  env -> FStar_Ident.ident -> FStar_Syntax_Syntax.delta_depth -> env) =
  fun env  ->
    fun x  ->
      fun dd  ->
        let l = qualify env x  in
        let uu____8942 =
          (unique false true env l) || (FStar_Options.interactive ())  in
        if uu____8942
        then push_scope_mod env (Rec_binding (x, l, dd))
        else
          (let uu____8944 = FStar_Ident.range_of_lid l  in
           FStar_Errors.raise_error
             (FStar_Errors.Fatal_DuplicateTopLevelNames,
               (Prims.strcat "Duplicate top-level names " l.FStar_Ident.str))
             uu____8944)
  
let (push_sigelt' : Prims.bool -> env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun fail_on_dup  ->
    fun env  ->
      fun s  ->
        let err l =
          let sopt = FStar_Util.smap_try_find (sigmap env) l.FStar_Ident.str
             in
          let r =
            match sopt with
            | FStar_Pervasives_Native.Some (se,uu____8979) ->
                let uu____8984 =
                  FStar_Util.find_opt (FStar_Ident.lid_equals l)
                    (FStar_Syntax_Util.lids_of_sigelt se)
                   in
                (match uu____8984 with
                 | FStar_Pervasives_Native.Some l1 ->
                     let uu____8988 = FStar_Ident.range_of_lid l1  in
                     FStar_All.pipe_left FStar_Range.string_of_range
                       uu____8988
                 | FStar_Pervasives_Native.None  -> "<unknown>")
            | FStar_Pervasives_Native.None  -> "<unknown>"  in
          let uu____8993 =
            let uu____8998 =
              let uu____8999 = FStar_Ident.text_of_lid l  in
              FStar_Util.format2
                "Duplicate top-level names [%s]; previously declared at %s"
                uu____8999 r
               in
            (FStar_Errors.Fatal_DuplicateTopLevelNames, uu____8998)  in
          let uu____9000 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____8993 uu____9000  in
        let globals = FStar_Util.mk_ref env.scope_mods  in
        let env1 =
          let uu____9009 =
            match s.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_let uu____9018 -> (false, true)
            | FStar_Syntax_Syntax.Sig_bundle uu____9025 -> (false, true)
            | uu____9034 -> (false, false)  in
          match uu____9009 with
          | (any_val,exclude_interface) ->
              let lids = FStar_Syntax_Util.lids_of_sigelt s  in
              let uu____9040 =
                FStar_Util.find_map lids
                  (fun l  ->
                     let uu____9046 =
                       let uu____9047 =
                         unique any_val exclude_interface env l  in
                       Prims.op_Negation uu____9047  in
                     if uu____9046
                     then FStar_Pervasives_Native.Some l
                     else FStar_Pervasives_Native.None)
                 in
              (match uu____9040 with
               | FStar_Pervasives_Native.Some l when fail_on_dup -> err l
               | uu____9052 ->
                   (extract_record env globals s;
                    (let uu___208_9078 = env  in
                     {
                       curmodule = (uu___208_9078.curmodule);
                       curmonad = (uu___208_9078.curmonad);
                       modules = (uu___208_9078.modules);
                       scope_mods = (uu___208_9078.scope_mods);
                       exported_ids = (uu___208_9078.exported_ids);
                       trans_exported_ids =
                         (uu___208_9078.trans_exported_ids);
                       includes = (uu___208_9078.includes);
                       sigaccum = (s :: (env.sigaccum));
                       sigmap = (uu___208_9078.sigmap);
                       iface = (uu___208_9078.iface);
                       admitted_iface = (uu___208_9078.admitted_iface);
                       expect_typ = (uu___208_9078.expect_typ);
                       docs = (uu___208_9078.docs);
                       remaining_iface_decls =
                         (uu___208_9078.remaining_iface_decls);
                       syntax_only = (uu___208_9078.syntax_only);
                       ds_hooks = (uu___208_9078.ds_hooks);
                       dep_graph = (uu___208_9078.dep_graph)
                     })))
           in
        let env2 =
          let uu___209_9080 = env1  in
          let uu____9081 = FStar_ST.op_Bang globals  in
          {
            curmodule = (uu___209_9080.curmodule);
            curmonad = (uu___209_9080.curmonad);
            modules = (uu___209_9080.modules);
            scope_mods = uu____9081;
            exported_ids = (uu___209_9080.exported_ids);
            trans_exported_ids = (uu___209_9080.trans_exported_ids);
            includes = (uu___209_9080.includes);
            sigaccum = (uu___209_9080.sigaccum);
            sigmap = (uu___209_9080.sigmap);
            iface = (uu___209_9080.iface);
            admitted_iface = (uu___209_9080.admitted_iface);
            expect_typ = (uu___209_9080.expect_typ);
            docs = (uu___209_9080.docs);
            remaining_iface_decls = (uu___209_9080.remaining_iface_decls);
            syntax_only = (uu___209_9080.syntax_only);
            ds_hooks = (uu___209_9080.ds_hooks);
            dep_graph = (uu___209_9080.dep_graph)
          }  in
        let uu____9129 =
          match s.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____9155) ->
              let uu____9164 =
                FStar_List.map
                  (fun se  -> ((FStar_Syntax_Util.lids_of_sigelt se), se))
                  ses
                 in
              (env2, uu____9164)
          | uu____9191 -> (env2, [((FStar_Syntax_Util.lids_of_sigelt s), s)])
           in
        match uu____9129 with
        | (env3,lss) ->
            (FStar_All.pipe_right lss
               (FStar_List.iter
                  (fun uu____9250  ->
                     match uu____9250 with
                     | (lids,se) ->
                         FStar_All.pipe_right lids
                           (FStar_List.iter
                              (fun lid  ->
                                 (let uu____9272 =
                                    let uu____9275 = FStar_ST.op_Bang globals
                                       in
                                    (Top_level_def (lid.FStar_Ident.ident))
                                      :: uu____9275
                                     in
                                  FStar_ST.op_Colon_Equals globals uu____9272);
                                 (match () with
                                  | () ->
                                      let modul =
                                        let uu____9369 =
                                          FStar_Ident.lid_of_ids
                                            lid.FStar_Ident.ns
                                           in
                                        uu____9369.FStar_Ident.str  in
                                      ((let uu____9371 =
                                          get_exported_id_set env3 modul  in
                                        match uu____9371 with
                                        | FStar_Pervasives_Native.Some f ->
                                            let my_exported_ids =
                                              f Exported_id_term_type  in
                                            let uu____9404 =
                                              let uu____9405 =
                                                FStar_ST.op_Bang
                                                  my_exported_ids
                                                 in
                                              FStar_Util.set_add
                                                (lid.FStar_Ident.ident).FStar_Ident.idText
                                                uu____9405
                                               in
                                            FStar_ST.op_Colon_Equals
                                              my_exported_ids uu____9404
                                        | FStar_Pervasives_Native.None  -> ());
                                       (match () with
                                        | () ->
                                            let is_iface =
                                              env3.iface &&
                                                (Prims.op_Negation
                                                   env3.admitted_iface)
                                               in
                                            FStar_Util.smap_add (sigmap env3)
                                              lid.FStar_Ident.str
                                              (se,
                                                (env3.iface &&
                                                   (Prims.op_Negation
                                                      env3.admitted_iface))))))))));
             (let env4 =
                let uu___210_9501 = env3  in
                let uu____9502 = FStar_ST.op_Bang globals  in
                {
                  curmodule = (uu___210_9501.curmodule);
                  curmonad = (uu___210_9501.curmonad);
                  modules = (uu___210_9501.modules);
                  scope_mods = uu____9502;
                  exported_ids = (uu___210_9501.exported_ids);
                  trans_exported_ids = (uu___210_9501.trans_exported_ids);
                  includes = (uu___210_9501.includes);
                  sigaccum = (uu___210_9501.sigaccum);
                  sigmap = (uu___210_9501.sigmap);
                  iface = (uu___210_9501.iface);
                  admitted_iface = (uu___210_9501.admitted_iface);
                  expect_typ = (uu___210_9501.expect_typ);
                  docs = (uu___210_9501.docs);
                  remaining_iface_decls =
                    (uu___210_9501.remaining_iface_decls);
                  syntax_only = (uu___210_9501.syntax_only);
                  ds_hooks = (uu___210_9501.ds_hooks);
                  dep_graph = (uu___210_9501.dep_graph)
                }  in
              env4))
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  -> fun se  -> push_sigelt' true env se 
let (push_sigelt_force : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  -> fun se  -> push_sigelt' false env se 
let (push_namespace : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun ns  ->
      let uu____9580 =
        let uu____9585 = resolve_module_name env ns false  in
        match uu____9585 with
        | FStar_Pervasives_Native.None  ->
            let modules = env.modules  in
            let uu____9599 =
              FStar_All.pipe_right modules
                (FStar_Util.for_some
                   (fun uu____9615  ->
                      match uu____9615 with
                      | (m,uu____9621) ->
                          let uu____9622 =
                            let uu____9623 = FStar_Ident.text_of_lid m  in
                            Prims.strcat uu____9623 "."  in
                          let uu____9624 =
                            let uu____9625 = FStar_Ident.text_of_lid ns  in
                            Prims.strcat uu____9625 "."  in
                          FStar_Util.starts_with uu____9622 uu____9624))
               in
            if uu____9599
            then (ns, Open_namespace)
            else
              (let uu____9631 =
                 let uu____9636 =
                   let uu____9637 = FStar_Ident.text_of_lid ns  in
                   FStar_Util.format1 "Namespace %s cannot be found"
                     uu____9637
                    in
                 (FStar_Errors.Fatal_NameSpaceNotFound, uu____9636)  in
               let uu____9638 = FStar_Ident.range_of_lid ns  in
               FStar_Errors.raise_error uu____9631 uu____9638)
        | FStar_Pervasives_Native.Some ns' ->
            (fail_if_curmodule env ns ns'; (ns', Open_module))
         in
      match uu____9580 with
      | (ns',kd) ->
          ((env.ds_hooks).ds_push_open_hook env (ns', kd);
           push_scope_mod env (Open_module_or_namespace (ns', kd)))
  
let (push_include : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun ns  ->
      let ns0 = ns  in
      let uu____9659 = resolve_module_name env ns false  in
      match uu____9659 with
      | FStar_Pervasives_Native.Some ns1 ->
          ((env.ds_hooks).ds_push_include_hook env ns1;
           fail_if_curmodule env ns0 ns1;
           (let env1 =
              push_scope_mod env
                (Open_module_or_namespace (ns1, Open_module))
               in
            let curmod =
              let uu____9667 = current_module env1  in
              uu____9667.FStar_Ident.str  in
            (let uu____9669 = FStar_Util.smap_try_find env1.includes curmod
                in
             match uu____9669 with
             | FStar_Pervasives_Native.None  -> ()
             | FStar_Pervasives_Native.Some incl ->
                 let uu____9693 =
                   let uu____9696 = FStar_ST.op_Bang incl  in ns1 ::
                     uu____9696
                    in
                 FStar_ST.op_Colon_Equals incl uu____9693);
            (match () with
             | () ->
                 let uu____9789 =
                   get_trans_exported_id_set env1 ns1.FStar_Ident.str  in
                 (match uu____9789 with
                  | FStar_Pervasives_Native.Some ns_trans_exports ->
                      ((let uu____9809 =
                          let uu____9904 = get_exported_id_set env1 curmod
                             in
                          let uu____9950 =
                            get_trans_exported_id_set env1 curmod  in
                          (uu____9904, uu____9950)  in
                        match uu____9809 with
                        | (FStar_Pervasives_Native.Some
                           cur_exports,FStar_Pervasives_Native.Some
                           cur_trans_exports) ->
                            let update_exports k =
                              let ns_ex =
                                let uu____10357 = ns_trans_exports k  in
                                FStar_ST.op_Bang uu____10357  in
                              let ex = cur_exports k  in
                              (let uu____10531 =
                                 let uu____10534 = FStar_ST.op_Bang ex  in
                                 FStar_Util.set_difference uu____10534 ns_ex
                                  in
                               FStar_ST.op_Colon_Equals ex uu____10531);
                              (match () with
                               | () ->
                                   let trans_ex = cur_trans_exports k  in
                                   let uu____10726 =
                                     let uu____10729 =
                                       FStar_ST.op_Bang trans_ex  in
                                     FStar_Util.set_union uu____10729 ns_ex
                                      in
                                   FStar_ST.op_Colon_Equals trans_ex
                                     uu____10726)
                               in
                            FStar_List.iter update_exports
                              all_exported_id_kinds
                        | uu____10858 -> ());
                       (match () with | () -> env1))
                  | FStar_Pervasives_Native.None  ->
                      let uu____10958 =
                        let uu____10963 =
                          FStar_Util.format1
                            "include: Module %s was not prepared"
                            ns1.FStar_Ident.str
                           in
                        (FStar_Errors.Fatal_IncludeModuleNotPrepared,
                          uu____10963)
                         in
                      let uu____10964 = FStar_Ident.range_of_lid ns1  in
                      FStar_Errors.raise_error uu____10958 uu____10964))))
      | uu____10965 ->
          let uu____10968 =
            let uu____10973 =
              FStar_Util.format1 "include: Module %s cannot be found"
                ns.FStar_Ident.str
               in
            (FStar_Errors.Fatal_ModuleNotFound, uu____10973)  in
          let uu____10974 = FStar_Ident.range_of_lid ns  in
          FStar_Errors.raise_error uu____10968 uu____10974
  
let (push_module_abbrev :
  env -> FStar_Ident.ident -> FStar_Ident.lident -> env) =
  fun env  ->
    fun x  ->
      fun l  ->
        let uu____10990 = module_is_defined env l  in
        if uu____10990
        then
          (fail_if_curmodule env l l;
           (env.ds_hooks).ds_push_module_abbrev_hook env x l;
           push_scope_mod env (Module_abbrev (x, l)))
        else
          (let uu____10994 =
             let uu____10999 =
               let uu____11000 = FStar_Ident.text_of_lid l  in
               FStar_Util.format1 "Module %s cannot be found" uu____11000  in
             (FStar_Errors.Fatal_ModuleNotFound, uu____10999)  in
           let uu____11001 = FStar_Ident.range_of_lid l  in
           FStar_Errors.raise_error uu____10994 uu____11001)
  
let (push_doc :
  env ->
    FStar_Ident.lident ->
      FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option -> env)
  =
  fun env  ->
    fun l  ->
      fun doc_opt  ->
        match doc_opt with
        | FStar_Pervasives_Native.None  -> env
        | FStar_Pervasives_Native.Some doc1 ->
            ((let uu____11023 =
                FStar_Util.smap_try_find env.docs l.FStar_Ident.str  in
              match uu____11023 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some old_doc ->
                  let uu____11027 = FStar_Ident.range_of_lid l  in
                  let uu____11028 =
                    let uu____11033 =
                      let uu____11034 = FStar_Ident.string_of_lid l  in
                      let uu____11035 =
                        FStar_Parser_AST.string_of_fsdoc old_doc  in
                      let uu____11036 = FStar_Parser_AST.string_of_fsdoc doc1
                         in
                      FStar_Util.format3
                        "Overwriting doc of %s; old doc was [%s]; new doc are [%s]"
                        uu____11034 uu____11035 uu____11036
                       in
                    (FStar_Errors.Warning_DocOverwrite, uu____11033)  in
                  FStar_Errors.log_issue uu____11027 uu____11028);
             FStar_Util.smap_add env.docs l.FStar_Ident.str doc1;
             env)
  
let (check_admits :
  env -> FStar_Syntax_Syntax.modul -> FStar_Syntax_Syntax.modul) =
  fun env  ->
    fun m  ->
      let admitted_sig_lids =
        FStar_All.pipe_right env.sigaccum
          (FStar_List.fold_left
             (fun lids  ->
                fun se  ->
                  match se.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t) when
                      let uu____11078 =
                        FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption)
                         in
                      Prims.op_Negation uu____11078 ->
                      let uu____11081 =
                        FStar_Util.smap_try_find (sigmap env)
                          l.FStar_Ident.str
                         in
                      (match uu____11081 with
                       | FStar_Pervasives_Native.Some
                           ({
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_let uu____11094;
                              FStar_Syntax_Syntax.sigrng = uu____11095;
                              FStar_Syntax_Syntax.sigquals = uu____11096;
                              FStar_Syntax_Syntax.sigmeta = uu____11097;
                              FStar_Syntax_Syntax.sigattrs = uu____11098;_},uu____11099)
                           -> lids
                       | FStar_Pervasives_Native.Some
                           ({
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_inductive_typ
                                uu____11114;
                              FStar_Syntax_Syntax.sigrng = uu____11115;
                              FStar_Syntax_Syntax.sigquals = uu____11116;
                              FStar_Syntax_Syntax.sigmeta = uu____11117;
                              FStar_Syntax_Syntax.sigattrs = uu____11118;_},uu____11119)
                           -> lids
                       | uu____11144 ->
                           ((let uu____11152 =
                               let uu____11153 = FStar_Options.interactive ()
                                  in
                               Prims.op_Negation uu____11153  in
                             if uu____11152
                             then
                               let uu____11154 = FStar_Ident.range_of_lid l
                                  in
                               let uu____11155 =
                                 let uu____11160 =
                                   let uu____11161 =
                                     FStar_Ident.string_of_lid l  in
                                   FStar_Util.format1
                                     "Admitting %s without a definition"
                                     uu____11161
                                    in
                                 (FStar_Errors.Warning_AdmitWithoutDefinition,
                                   uu____11160)
                                  in
                               FStar_Errors.log_issue uu____11154 uu____11155
                             else ());
                            (let quals = FStar_Syntax_Syntax.Assumption ::
                               (se.FStar_Syntax_Syntax.sigquals)  in
                             FStar_Util.smap_add (sigmap env)
                               l.FStar_Ident.str
                               ((let uu___211_11172 = se  in
                                 {
                                   FStar_Syntax_Syntax.sigel =
                                     (uu___211_11172.FStar_Syntax_Syntax.sigel);
                                   FStar_Syntax_Syntax.sigrng =
                                     (uu___211_11172.FStar_Syntax_Syntax.sigrng);
                                   FStar_Syntax_Syntax.sigquals = quals;
                                   FStar_Syntax_Syntax.sigmeta =
                                     (uu___211_11172.FStar_Syntax_Syntax.sigmeta);
                                   FStar_Syntax_Syntax.sigattrs =
                                     (uu___211_11172.FStar_Syntax_Syntax.sigattrs)
                                 }), false);
                             l
                             ::
                             lids)))
                  | uu____11173 -> lids) [])
         in
      let uu___212_11174 = m  in
      let uu____11175 =
        FStar_All.pipe_right m.FStar_Syntax_Syntax.declarations
          (FStar_List.map
             (fun s  ->
                match s.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_declare_typ
                    (lid,uu____11185,uu____11186) when
                    FStar_List.existsb
                      (fun l  -> FStar_Ident.lid_equals l lid)
                      admitted_sig_lids
                    ->
                    let uu___213_11189 = s  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___213_11189.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___213_11189.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals =
                        (FStar_Syntax_Syntax.Assumption ::
                        (s.FStar_Syntax_Syntax.sigquals));
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___213_11189.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___213_11189.FStar_Syntax_Syntax.sigattrs)
                    }
                | uu____11190 -> s))
         in
      {
        FStar_Syntax_Syntax.name = (uu___212_11174.FStar_Syntax_Syntax.name);
        FStar_Syntax_Syntax.declarations = uu____11175;
        FStar_Syntax_Syntax.exports =
          (uu___212_11174.FStar_Syntax_Syntax.exports);
        FStar_Syntax_Syntax.is_interface =
          (uu___212_11174.FStar_Syntax_Syntax.is_interface)
      }
  
let (finish : env -> FStar_Syntax_Syntax.modul -> env) =
  fun env  ->
    fun modul  ->
      FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations
        (FStar_List.iter
           (fun se  ->
              let quals = se.FStar_Syntax_Syntax.sigquals  in
              match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_bundle (ses,uu____11213) ->
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
                                (lid,uu____11233,uu____11234,uu____11235,uu____11236,uu____11237)
                                ->
                                FStar_Util.smap_remove (sigmap env)
                                  lid.FStar_Ident.str
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (lid,univ_names,binders,typ,uu____11250,uu____11251)
                                ->
                                (FStar_Util.smap_remove (sigmap env)
                                   lid.FStar_Ident.str;
                                 if
                                   Prims.op_Negation
                                     (FStar_List.contains
                                        FStar_Syntax_Syntax.Private quals)
                                 then
                                   (let sigel =
                                      let uu____11266 =
                                        let uu____11273 =
                                          let uu____11274 =
                                            FStar_Ident.range_of_lid lid  in
                                          let uu____11275 =
                                            let uu____11282 =
                                              let uu____11283 =
                                                let uu____11298 =
                                                  FStar_Syntax_Syntax.mk_Total
                                                    typ
                                                   in
                                                (binders, uu____11298)  in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____11283
                                               in
                                            FStar_Syntax_Syntax.mk
                                              uu____11282
                                             in
                                          uu____11275
                                            FStar_Pervasives_Native.None
                                            uu____11274
                                           in
                                        (lid, univ_names, uu____11273)  in
                                      FStar_Syntax_Syntax.Sig_declare_typ
                                        uu____11266
                                       in
                                    let se2 =
                                      let uu___214_11315 = se1  in
                                      {
                                        FStar_Syntax_Syntax.sigel = sigel;
                                        FStar_Syntax_Syntax.sigrng =
                                          (uu___214_11315.FStar_Syntax_Syntax.sigrng);
                                        FStar_Syntax_Syntax.sigquals =
                                          (FStar_Syntax_Syntax.Assumption ::
                                          quals);
                                        FStar_Syntax_Syntax.sigmeta =
                                          (uu___214_11315.FStar_Syntax_Syntax.sigmeta);
                                        FStar_Syntax_Syntax.sigattrs =
                                          (uu___214_11315.FStar_Syntax_Syntax.sigattrs)
                                      }  in
                                    FStar_Util.smap_add (sigmap env)
                                      lid.FStar_Ident.str (se2, false))
                                 else ())
                            | uu____11321 -> ()))
                  else ()
              | FStar_Syntax_Syntax.Sig_declare_typ
                  (lid,uu____11324,uu____11325) ->
                  if FStar_List.contains FStar_Syntax_Syntax.Private quals
                  then
                    FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str
                  else ()
              | FStar_Syntax_Syntax.Sig_let ((uu____11331,lbs),uu____11333)
                  ->
                  (if
                     (FStar_List.contains FStar_Syntax_Syntax.Private quals)
                       ||
                       (FStar_List.contains FStar_Syntax_Syntax.Abstract
                          quals)
                   then
                     FStar_All.pipe_right lbs
                       (FStar_List.iter
                          (fun lb  ->
                             let uu____11348 =
                               let uu____11349 =
                                 let uu____11350 =
                                   let uu____11353 =
                                     FStar_Util.right
                                       lb.FStar_Syntax_Syntax.lbname
                                      in
                                   uu____11353.FStar_Syntax_Syntax.fv_name
                                    in
                                 uu____11350.FStar_Syntax_Syntax.v  in
                               uu____11349.FStar_Ident.str  in
                             FStar_Util.smap_remove (sigmap env) uu____11348))
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
                               let uu____11367 =
                                 let uu____11370 =
                                   FStar_Util.right
                                     lb.FStar_Syntax_Syntax.lbname
                                    in
                                 uu____11370.FStar_Syntax_Syntax.fv_name  in
                               uu____11367.FStar_Syntax_Syntax.v  in
                             let quals1 = FStar_Syntax_Syntax.Assumption ::
                               quals  in
                             let decl =
                               let uu___215_11375 = se  in
                               {
                                 FStar_Syntax_Syntax.sigel =
                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                      (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                        (lb.FStar_Syntax_Syntax.lbtyp)));
                                 FStar_Syntax_Syntax.sigrng =
                                   (uu___215_11375.FStar_Syntax_Syntax.sigrng);
                                 FStar_Syntax_Syntax.sigquals = quals1;
                                 FStar_Syntax_Syntax.sigmeta =
                                   (uu___215_11375.FStar_Syntax_Syntax.sigmeta);
                                 FStar_Syntax_Syntax.sigattrs =
                                   (uu___215_11375.FStar_Syntax_Syntax.sigattrs)
                               }  in
                             FStar_Util.smap_add (sigmap env)
                               lid.FStar_Ident.str (decl, false)))
                   else ())
              | uu____11381 -> ()));
      (let curmod =
         let uu____11383 = current_module env  in uu____11383.FStar_Ident.str
          in
       (let uu____11385 =
          let uu____11480 = get_exported_id_set env curmod  in
          let uu____11526 = get_trans_exported_id_set env curmod  in
          (uu____11480, uu____11526)  in
        match uu____11385 with
        | (FStar_Pervasives_Native.Some cur_ex,FStar_Pervasives_Native.Some
           cur_trans_ex) ->
            let update_exports eikind =
              let cur_ex_set =
                let uu____11935 = cur_ex eikind  in
                FStar_ST.op_Bang uu____11935  in
              let cur_trans_ex_set_ref = cur_trans_ex eikind  in
              let uu____12122 =
                let uu____12125 = FStar_ST.op_Bang cur_trans_ex_set_ref  in
                FStar_Util.set_union cur_ex_set uu____12125  in
              FStar_ST.op_Colon_Equals cur_trans_ex_set_ref uu____12122  in
            FStar_List.iter update_exports all_exported_id_kinds
        | uu____12254 -> ());
       (match () with
        | () ->
            (filter_record_cache ();
             (match () with
              | () ->
                  let uu___216_12350 = env  in
                  {
                    curmodule = FStar_Pervasives_Native.None;
                    curmonad = (uu___216_12350.curmonad);
                    modules = (((modul.FStar_Syntax_Syntax.name), modul) ::
                      (env.modules));
                    scope_mods = [];
                    exported_ids = (uu___216_12350.exported_ids);
                    trans_exported_ids = (uu___216_12350.trans_exported_ids);
                    includes = (uu___216_12350.includes);
                    sigaccum = [];
                    sigmap = (uu___216_12350.sigmap);
                    iface = (uu___216_12350.iface);
                    admitted_iface = (uu___216_12350.admitted_iface);
                    expect_typ = (uu___216_12350.expect_typ);
                    docs = (uu___216_12350.docs);
                    remaining_iface_decls =
                      (uu___216_12350.remaining_iface_decls);
                    syntax_only = (uu___216_12350.syntax_only);
                    ds_hooks = (uu___216_12350.ds_hooks);
                    dep_graph = (uu___216_12350.dep_graph)
                  }))))
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push : env -> env) =
  fun env  ->
    FStar_Util.atomically
      (fun uu____12386  ->
         push_record_cache ();
         (let uu____12389 =
            let uu____12392 = FStar_ST.op_Bang stack  in env :: uu____12392
             in
          FStar_ST.op_Colon_Equals stack uu____12389);
         (let uu___217_12441 = env  in
          let uu____12442 = FStar_Util.smap_copy env.exported_ids  in
          let uu____12447 = FStar_Util.smap_copy env.trans_exported_ids  in
          let uu____12452 = FStar_Util.smap_copy env.includes  in
          let uu____12463 = FStar_Util.smap_copy env.sigmap  in
          let uu____12474 = FStar_Util.smap_copy env.docs  in
          {
            curmodule = (uu___217_12441.curmodule);
            curmonad = (uu___217_12441.curmonad);
            modules = (uu___217_12441.modules);
            scope_mods = (uu___217_12441.scope_mods);
            exported_ids = uu____12442;
            trans_exported_ids = uu____12447;
            includes = uu____12452;
            sigaccum = (uu___217_12441.sigaccum);
            sigmap = uu____12463;
            iface = (uu___217_12441.iface);
            admitted_iface = (uu___217_12441.admitted_iface);
            expect_typ = (uu___217_12441.expect_typ);
            docs = uu____12474;
            remaining_iface_decls = (uu___217_12441.remaining_iface_decls);
            syntax_only = (uu___217_12441.syntax_only);
            ds_hooks = (uu___217_12441.ds_hooks);
            dep_graph = (uu___217_12441.dep_graph)
          }))
  
let (pop : unit -> env) =
  fun uu____12481  ->
    FStar_Util.atomically
      (fun uu____12488  ->
         let uu____12489 = FStar_ST.op_Bang stack  in
         match uu____12489 with
         | env::tl1 ->
             (pop_record_cache (); FStar_ST.op_Colon_Equals stack tl1; env)
         | uu____12544 -> failwith "Impossible: Too many pops")
  
let (snapshot : env -> (Prims.int,env) FStar_Pervasives_Native.tuple2) =
  fun env  -> FStar_Common.snapshot push stack env 
let (rollback : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth  -> FStar_Common.rollback pop stack depth 
let (export_interface : FStar_Ident.lident -> env -> env) =
  fun m  ->
    fun env  ->
      let sigelt_in_m se =
        match FStar_Syntax_Util.lids_of_sigelt se with
        | l::uu____12582 -> l.FStar_Ident.nsstr = m.FStar_Ident.str
        | uu____12585 -> false  in
      let sm = sigmap env  in
      let env1 = pop ()  in
      let keys = FStar_Util.smap_keys sm  in
      let sm' = sigmap env1  in
      FStar_All.pipe_right keys
        (FStar_List.iter
           (fun k  ->
              let uu____12619 = FStar_Util.smap_try_find sm' k  in
              match uu____12619 with
              | FStar_Pervasives_Native.Some (se,true ) when sigelt_in_m se
                  ->
                  (FStar_Util.smap_remove sm' k;
                   (let se1 =
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t) ->
                          let uu___218_12644 = se  in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (uu___218_12644.FStar_Syntax_Syntax.sigel);
                            FStar_Syntax_Syntax.sigrng =
                              (uu___218_12644.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (FStar_Syntax_Syntax.Assumption ::
                              (se.FStar_Syntax_Syntax.sigquals));
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___218_12644.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___218_12644.FStar_Syntax_Syntax.sigattrs)
                          }
                      | uu____12645 -> se  in
                    FStar_Util.smap_add sm' k (se1, false)))
              | uu____12650 -> ()));
      env1
  
let (finish_module_or_interface :
  env ->
    FStar_Syntax_Syntax.modul ->
      (env,FStar_Syntax_Syntax.modul) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun modul  ->
      let modul1 =
        if Prims.op_Negation modul.FStar_Syntax_Syntax.is_interface
        then check_admits env modul
        else modul  in
      let uu____12673 = finish env modul1  in (uu____12673, modul1)
  
type exported_ids =
  {
  exported_id_terms: Prims.string Prims.list ;
  exported_id_fields: Prims.string Prims.list }
let (__proj__Mkexported_ids__item__exported_id_terms :
  exported_ids -> Prims.string Prims.list) =
  fun projectee  ->
    match projectee with
    | { exported_id_terms = __fname__exported_id_terms;
        exported_id_fields = __fname__exported_id_fields;_} ->
        __fname__exported_id_terms
  
let (__proj__Mkexported_ids__item__exported_id_fields :
  exported_ids -> Prims.string Prims.list) =
  fun projectee  ->
    match projectee with
    | { exported_id_terms = __fname__exported_id_terms;
        exported_id_fields = __fname__exported_id_fields;_} ->
        __fname__exported_id_fields
  
let (as_exported_ids : exported_id_set -> exported_ids) =
  fun e  ->
    let terms =
      let uu____12761 =
        let uu____12764 = e Exported_id_term_type  in
        FStar_ST.op_Bang uu____12764  in
      FStar_Util.set_elements uu____12761  in
    let fields =
      let uu____12878 =
        let uu____12881 = e Exported_id_field  in
        FStar_ST.op_Bang uu____12881  in
      FStar_Util.set_elements uu____12878  in
    { exported_id_terms = terms; exported_id_fields = fields }
  
let (as_exported_id_set :
  exported_ids FStar_Pervasives_Native.option ->
    exported_id_kind -> Prims.string FStar_Util.set FStar_ST.ref)
  =
  fun e  ->
    match e with
    | FStar_Pervasives_Native.None  -> exported_id_set_new ()
    | FStar_Pervasives_Native.Some e1 ->
        let terms =
          let uu____13032 =
            FStar_Util.as_set e1.exported_id_terms FStar_Util.compare  in
          FStar_Util.mk_ref uu____13032  in
        let fields =
          let uu____13042 =
            FStar_Util.as_set e1.exported_id_fields FStar_Util.compare  in
          FStar_Util.mk_ref uu____13042  in
        (fun uu___193_13047  ->
           match uu___193_13047 with
           | Exported_id_term_type  -> terms
           | Exported_id_field  -> fields)
  
type module_inclusion_info =
  {
  mii_exported_ids: exported_ids FStar_Pervasives_Native.option ;
  mii_trans_exported_ids: exported_ids FStar_Pervasives_Native.option ;
  mii_includes: FStar_Ident.lident Prims.list FStar_Pervasives_Native.option }
let (__proj__Mkmodule_inclusion_info__item__mii_exported_ids :
  module_inclusion_info -> exported_ids FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { mii_exported_ids = __fname__mii_exported_ids;
        mii_trans_exported_ids = __fname__mii_trans_exported_ids;
        mii_includes = __fname__mii_includes;_} -> __fname__mii_exported_ids
  
let (__proj__Mkmodule_inclusion_info__item__mii_trans_exported_ids :
  module_inclusion_info -> exported_ids FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { mii_exported_ids = __fname__mii_exported_ids;
        mii_trans_exported_ids = __fname__mii_trans_exported_ids;
        mii_includes = __fname__mii_includes;_} ->
        __fname__mii_trans_exported_ids
  
let (__proj__Mkmodule_inclusion_info__item__mii_includes :
  module_inclusion_info ->
    FStar_Ident.lident Prims.list FStar_Pervasives_Native.option)
  =
  fun projectee  ->
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
  'Auu____13178 .
    'Auu____13178 Prims.list FStar_Pervasives_Native.option ->
      'Auu____13178 Prims.list FStar_ST.ref
  =
  fun uu___194_13191  ->
    match uu___194_13191 with
    | FStar_Pervasives_Native.None  -> FStar_Util.mk_ref []
    | FStar_Pervasives_Native.Some l -> FStar_Util.mk_ref l
  
let (inclusion_info : env -> FStar_Ident.lident -> module_inclusion_info) =
  fun env  ->
    fun l  ->
      let mname = FStar_Ident.string_of_lid l  in
      let as_ids_opt m =
        let uu____13232 = FStar_Util.smap_try_find m mname  in
        FStar_Util.map_opt uu____13232 as_exported_ids  in
      let uu____13238 = as_ids_opt env.exported_ids  in
      let uu____13241 = as_ids_opt env.trans_exported_ids  in
      let uu____13244 =
        let uu____13249 = FStar_Util.smap_try_find env.includes mname  in
        FStar_Util.map_opt uu____13249 (fun r  -> FStar_ST.op_Bang r)  in
      {
        mii_exported_ids = uu____13238;
        mii_trans_exported_ids = uu____13241;
        mii_includes = uu____13244
      }
  
let (prepare_module_or_interface :
  Prims.bool ->
    Prims.bool ->
      env ->
        FStar_Ident.lident ->
          module_inclusion_info ->
            (env,Prims.bool) FStar_Pervasives_Native.tuple2)
  =
  fun intf  ->
    fun admitted  ->
      fun env  ->
        fun mname  ->
          fun mii  ->
            let prep env1 =
              let filename =
                let uu____13364 = FStar_Ident.text_of_lid mname  in
                FStar_Util.strcat uu____13364 ".fst"  in
              let auto_open =
                FStar_Parser_Dep.hard_coded_dependencies filename  in
              let auto_open1 =
                let convert_kind uu___195_13384 =
                  match uu___195_13384 with
                  | FStar_Parser_Dep.Open_namespace  -> Open_namespace
                  | FStar_Parser_Dep.Open_module  -> Open_module  in
                FStar_List.map
                  (fun uu____13396  ->
                     match uu____13396 with
                     | (lid,kind) -> (lid, (convert_kind kind))) auto_open
                 in
              let namespace_of_module =
                if
                  (FStar_List.length mname.FStar_Ident.ns) >
                    (Prims.parse_int "0")
                then
                  let uu____13420 =
                    let uu____13425 =
                      FStar_Ident.lid_of_ids mname.FStar_Ident.ns  in
                    (uu____13425, Open_namespace)  in
                  [uu____13420]
                else []  in
              let auto_open2 =
                FStar_List.append namespace_of_module
                  (FStar_List.rev auto_open1)
                 in
              (let uu____13455 = as_exported_id_set mii.mii_exported_ids  in
               FStar_Util.smap_add env1.exported_ids mname.FStar_Ident.str
                 uu____13455);
              (match () with
               | () ->
                   ((let uu____13482 =
                       as_exported_id_set mii.mii_trans_exported_ids  in
                     FStar_Util.smap_add env1.trans_exported_ids
                       mname.FStar_Ident.str uu____13482);
                    (match () with
                     | () ->
                         ((let uu____13509 = as_includes mii.mii_includes  in
                           FStar_Util.smap_add env1.includes
                             mname.FStar_Ident.str uu____13509);
                          (match () with
                           | () ->
                               let env' =
                                 let uu___219_13541 = env1  in
                                 let uu____13542 =
                                   FStar_List.map
                                     (fun x  -> Open_module_or_namespace x)
                                     auto_open2
                                    in
                                 {
                                   curmodule =
                                     (FStar_Pervasives_Native.Some mname);
                                   curmonad = (uu___219_13541.curmonad);
                                   modules = (uu___219_13541.modules);
                                   scope_mods = uu____13542;
                                   exported_ids =
                                     (uu___219_13541.exported_ids);
                                   trans_exported_ids =
                                     (uu___219_13541.trans_exported_ids);
                                   includes = (uu___219_13541.includes);
                                   sigaccum = (uu___219_13541.sigaccum);
                                   sigmap = (env1.sigmap);
                                   iface = intf;
                                   admitted_iface = admitted;
                                   expect_typ = (uu___219_13541.expect_typ);
                                   docs = (uu___219_13541.docs);
                                   remaining_iface_decls =
                                     (uu___219_13541.remaining_iface_decls);
                                   syntax_only = (uu___219_13541.syntax_only);
                                   ds_hooks = (uu___219_13541.ds_hooks);
                                   dep_graph = (uu___219_13541.dep_graph)
                                 }  in
                               (FStar_List.iter
                                  (fun op  ->
                                     (env1.ds_hooks).ds_push_open_hook env'
                                       op) (FStar_List.rev auto_open2);
                                env'))))))
               in
            let uu____13554 =
              FStar_All.pipe_right env.modules
                (FStar_Util.find_opt
                   (fun uu____13580  ->
                      match uu____13580 with
                      | (l,uu____13586) -> FStar_Ident.lid_equals l mname))
               in
            match uu____13554 with
            | FStar_Pervasives_Native.None  ->
                let uu____13595 = prep env  in (uu____13595, false)
            | FStar_Pervasives_Native.Some (uu____13596,m) ->
                ((let uu____13603 =
                    (let uu____13606 = FStar_Options.interactive ()  in
                     Prims.op_Negation uu____13606) &&
                      ((Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)
                         || intf)
                     in
                  if uu____13603
                  then
                    let uu____13607 =
                      let uu____13612 =
                        FStar_Util.format1
                          "Duplicate module or interface name: %s"
                          mname.FStar_Ident.str
                         in
                      (FStar_Errors.Fatal_DuplicateModuleOrInterface,
                        uu____13612)
                       in
                    let uu____13613 = FStar_Ident.range_of_lid mname  in
                    FStar_Errors.raise_error uu____13607 uu____13613
                  else ());
                 (let uu____13615 =
                    let uu____13616 = push env  in prep uu____13616  in
                  (uu____13615, true)))
  
let (enter_monad_scope : env -> FStar_Ident.ident -> env) =
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
          let uu___220_13628 = env  in
          {
            curmodule = (uu___220_13628.curmodule);
            curmonad = (FStar_Pervasives_Native.Some mname);
            modules = (uu___220_13628.modules);
            scope_mods = (uu___220_13628.scope_mods);
            exported_ids = (uu___220_13628.exported_ids);
            trans_exported_ids = (uu___220_13628.trans_exported_ids);
            includes = (uu___220_13628.includes);
            sigaccum = (uu___220_13628.sigaccum);
            sigmap = (uu___220_13628.sigmap);
            iface = (uu___220_13628.iface);
            admitted_iface = (uu___220_13628.admitted_iface);
            expect_typ = (uu___220_13628.expect_typ);
            docs = (uu___220_13628.docs);
            remaining_iface_decls = (uu___220_13628.remaining_iface_decls);
            syntax_only = (uu___220_13628.syntax_only);
            ds_hooks = (uu___220_13628.ds_hooks);
            dep_graph = (uu___220_13628.dep_graph)
          }
  
let fail_or :
  'a .
    env ->
      (FStar_Ident.lident -> 'a FStar_Pervasives_Native.option) ->
        FStar_Ident.lident -> 'a
  =
  fun env  ->
    fun lookup1  ->
      fun lid  ->
        let uu____13662 = lookup1 lid  in
        match uu____13662 with
        | FStar_Pervasives_Native.None  ->
            let opened_modules =
              FStar_List.map
                (fun uu____13675  ->
                   match uu____13675 with
                   | (lid1,uu____13681) -> FStar_Ident.text_of_lid lid1)
                env.modules
               in
            let msg =
              let uu____13683 = FStar_Ident.text_of_lid lid  in
              FStar_Util.format1 "Identifier not found: [%s]" uu____13683  in
            let msg1 =
              if
                (FStar_List.length lid.FStar_Ident.ns) =
                  (Prims.parse_int "0")
              then msg
              else
                (let modul =
                   let uu____13687 =
                     FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
                   let uu____13688 = FStar_Ident.range_of_lid lid  in
                   FStar_Ident.set_lid_range uu____13687 uu____13688  in
                 let uu____13689 = resolve_module_name env modul true  in
                 match uu____13689 with
                 | FStar_Pervasives_Native.None  ->
                     let opened_modules1 =
                       FStar_String.concat ", " opened_modules  in
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
                       FStar_String.concat ", " opened_modules  in
                     FStar_Util.format4
                       "%s\nModule %s resolved into %s, which does not belong to the list of modules in scope, namely %s"
                       msg modul.FStar_Ident.str modul'.FStar_Ident.str
                       opened_modules1
                 | FStar_Pervasives_Native.Some modul' ->
                     FStar_Util.format4
                       "%s\nModule %s resolved into %s, definition %s not found"
                       msg modul.FStar_Ident.str modul'.FStar_Ident.str
                       (lid.FStar_Ident.ident).FStar_Ident.idText)
               in
            let uu____13698 = FStar_Ident.range_of_lid lid  in
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_IdentifierNotFound, msg1) uu____13698
        | FStar_Pervasives_Native.Some r -> r
  
let fail_or2 :
  'a .
    (FStar_Ident.ident -> 'a FStar_Pervasives_Native.option) ->
      FStar_Ident.ident -> 'a
  =
  fun lookup1  ->
    fun id1  ->
      let uu____13726 = lookup1 id1  in
      match uu____13726 with
      | FStar_Pervasives_Native.None  ->
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_IdentifierNotFound,
              (Prims.strcat "Identifier not found ["
                 (Prims.strcat id1.FStar_Ident.idText "]")))
            id1.FStar_Ident.idRange
      | FStar_Pervasives_Native.Some r -> r
  