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
    ds_push_open_hook = (fun uu____1817  -> fun uu____1818  -> ());
    ds_push_include_hook = (fun uu____1821  -> fun uu____1822  -> ());
    ds_push_module_abbrev_hook =
      (fun uu____1826  -> fun uu____1827  -> fun uu____1828  -> ())
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
    match projectee with | Term_name _0 -> true | uu____1865 -> false
  
let (__proj__Term_name__item___0 :
  foundname ->
    (FStar_Syntax_Syntax.typ,Prims.bool,FStar_Syntax_Syntax.attribute
                                          Prims.list)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Term_name _0 -> _0 
let (uu___is_Eff_name : foundname -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eff_name _0 -> true | uu____1907 -> false
  
let (__proj__Eff_name__item___0 :
  foundname ->
    (FStar_Syntax_Syntax.sigelt,FStar_Ident.lident)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Eff_name _0 -> _0 
let (set_iface : env -> Prims.bool -> env) =
  fun env  ->
    fun b  ->
      let uu___198_1937 = env  in
      {
        curmodule = (uu___198_1937.curmodule);
        curmonad = (uu___198_1937.curmonad);
        modules = (uu___198_1937.modules);
        scope_mods = (uu___198_1937.scope_mods);
        exported_ids = (uu___198_1937.exported_ids);
        trans_exported_ids = (uu___198_1937.trans_exported_ids);
        includes = (uu___198_1937.includes);
        sigaccum = (uu___198_1937.sigaccum);
        sigmap = (uu___198_1937.sigmap);
        iface = b;
        admitted_iface = (uu___198_1937.admitted_iface);
        expect_typ = (uu___198_1937.expect_typ);
        docs = (uu___198_1937.docs);
        remaining_iface_decls = (uu___198_1937.remaining_iface_decls);
        syntax_only = (uu___198_1937.syntax_only);
        ds_hooks = (uu___198_1937.ds_hooks);
        dep_graph = (uu___198_1937.dep_graph)
      }
  
let (iface : env -> Prims.bool) = fun e  -> e.iface 
let (set_admitted_iface : env -> Prims.bool -> env) =
  fun e  ->
    fun b  ->
      let uu___199_1953 = e  in
      {
        curmodule = (uu___199_1953.curmodule);
        curmonad = (uu___199_1953.curmonad);
        modules = (uu___199_1953.modules);
        scope_mods = (uu___199_1953.scope_mods);
        exported_ids = (uu___199_1953.exported_ids);
        trans_exported_ids = (uu___199_1953.trans_exported_ids);
        includes = (uu___199_1953.includes);
        sigaccum = (uu___199_1953.sigaccum);
        sigmap = (uu___199_1953.sigmap);
        iface = (uu___199_1953.iface);
        admitted_iface = b;
        expect_typ = (uu___199_1953.expect_typ);
        docs = (uu___199_1953.docs);
        remaining_iface_decls = (uu___199_1953.remaining_iface_decls);
        syntax_only = (uu___199_1953.syntax_only);
        ds_hooks = (uu___199_1953.ds_hooks);
        dep_graph = (uu___199_1953.dep_graph)
      }
  
let (admitted_iface : env -> Prims.bool) = fun e  -> e.admitted_iface 
let (set_expect_typ : env -> Prims.bool -> env) =
  fun e  ->
    fun b  ->
      let uu___200_1969 = e  in
      {
        curmodule = (uu___200_1969.curmodule);
        curmonad = (uu___200_1969.curmonad);
        modules = (uu___200_1969.modules);
        scope_mods = (uu___200_1969.scope_mods);
        exported_ids = (uu___200_1969.exported_ids);
        trans_exported_ids = (uu___200_1969.trans_exported_ids);
        includes = (uu___200_1969.includes);
        sigaccum = (uu___200_1969.sigaccum);
        sigmap = (uu___200_1969.sigmap);
        iface = (uu___200_1969.iface);
        admitted_iface = (uu___200_1969.admitted_iface);
        expect_typ = b;
        docs = (uu___200_1969.docs);
        remaining_iface_decls = (uu___200_1969.remaining_iface_decls);
        syntax_only = (uu___200_1969.syntax_only);
        ds_hooks = (uu___200_1969.ds_hooks);
        dep_graph = (uu___200_1969.dep_graph)
      }
  
let (expect_typ : env -> Prims.bool) = fun e  -> e.expect_typ 
let (all_exported_id_kinds : exported_id_kind Prims.list) =
  [Exported_id_field; Exported_id_term_type] 
let (transitive_exported_ids :
  env -> FStar_Ident.lident -> Prims.string Prims.list) =
  fun env  ->
    fun lid  ->
      let module_name = FStar_Ident.string_of_lid lid  in
      let uu____1990 =
        FStar_Util.smap_try_find env.trans_exported_ids module_name  in
      match uu____1990 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some exported_id_set ->
          let uu____2001 =
            let uu____2004 = exported_id_set Exported_id_term_type  in
            FStar_ST.op_Bang uu____2004  in
          FStar_All.pipe_right uu____2001 FStar_Util.set_elements
  
let (open_modules :
  env ->
    (FStar_Ident.lident,FStar_Syntax_Syntax.modul)
      FStar_Pervasives_Native.tuple2 Prims.list)
  = fun e  -> e.modules 
let (open_modules_and_namespaces : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    FStar_List.filter_map
      (fun uu___165_2140  ->
         match uu___165_2140 with
         | Open_module_or_namespace (lid,_info) ->
             FStar_Pervasives_Native.Some lid
         | uu____2145 -> FStar_Pervasives_Native.None) env.scope_mods
  
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun e  ->
    fun l  ->
      let uu___201_2156 = e  in
      {
        curmodule = (FStar_Pervasives_Native.Some l);
        curmonad = (uu___201_2156.curmonad);
        modules = (uu___201_2156.modules);
        scope_mods = (uu___201_2156.scope_mods);
        exported_ids = (uu___201_2156.exported_ids);
        trans_exported_ids = (uu___201_2156.trans_exported_ids);
        includes = (uu___201_2156.includes);
        sigaccum = (uu___201_2156.sigaccum);
        sigmap = (uu___201_2156.sigmap);
        iface = (uu___201_2156.iface);
        admitted_iface = (uu___201_2156.admitted_iface);
        expect_typ = (uu___201_2156.expect_typ);
        docs = (uu___201_2156.docs);
        remaining_iface_decls = (uu___201_2156.remaining_iface_decls);
        syntax_only = (uu___201_2156.syntax_only);
        ds_hooks = (uu___201_2156.ds_hooks);
        dep_graph = (uu___201_2156.dep_graph)
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
      let uu____2177 =
        FStar_All.pipe_right env.remaining_iface_decls
          (FStar_List.tryFind
             (fun uu____2211  ->
                match uu____2211 with
                | (m,uu____2219) -> FStar_Ident.lid_equals l m))
         in
      match uu____2177 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (uu____2236,decls) ->
          FStar_Pervasives_Native.Some decls
  
let (set_iface_decls :
  env -> FStar_Ident.lident -> FStar_Parser_AST.decl Prims.list -> env) =
  fun env  ->
    fun l  ->
      fun ds  ->
        let uu____2269 =
          FStar_List.partition
            (fun uu____2299  ->
               match uu____2299 with
               | (m,uu____2307) -> FStar_Ident.lid_equals l m)
            env.remaining_iface_decls
           in
        match uu____2269 with
        | (uu____2312,rest) ->
            let uu___202_2346 = env  in
            {
              curmodule = (uu___202_2346.curmodule);
              curmonad = (uu___202_2346.curmonad);
              modules = (uu___202_2346.modules);
              scope_mods = (uu___202_2346.scope_mods);
              exported_ids = (uu___202_2346.exported_ids);
              trans_exported_ids = (uu___202_2346.trans_exported_ids);
              includes = (uu___202_2346.includes);
              sigaccum = (uu___202_2346.sigaccum);
              sigmap = (uu___202_2346.sigmap);
              iface = (uu___202_2346.iface);
              admitted_iface = (uu___202_2346.admitted_iface);
              expect_typ = (uu___202_2346.expect_typ);
              docs = (uu___202_2346.docs);
              remaining_iface_decls = ((l, ds) :: rest);
              syntax_only = (uu___202_2346.syntax_only);
              ds_hooks = (uu___202_2346.ds_hooks);
              dep_graph = (uu___202_2346.dep_graph)
            }
  
let (qual : FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident) =
  FStar_Syntax_Util.qual_id 
let (qualify : env -> FStar_Ident.ident -> FStar_Ident.lident) =
  fun env  ->
    fun id1  ->
      match env.curmonad with
      | FStar_Pervasives_Native.None  ->
          let uu____2373 = current_module env  in qual uu____2373 id1
      | FStar_Pervasives_Native.Some monad ->
          let uu____2375 =
            let uu____2376 = current_module env  in qual uu____2376 monad  in
          FStar_Syntax_Util.mk_field_projector_name_from_ident uu____2375 id1
  
let (syntax_only : env -> Prims.bool) = fun env  -> env.syntax_only 
let (set_syntax_only : env -> Prims.bool -> env) =
  fun env  ->
    fun b  ->
      let uu___203_2392 = env  in
      {
        curmodule = (uu___203_2392.curmodule);
        curmonad = (uu___203_2392.curmonad);
        modules = (uu___203_2392.modules);
        scope_mods = (uu___203_2392.scope_mods);
        exported_ids = (uu___203_2392.exported_ids);
        trans_exported_ids = (uu___203_2392.trans_exported_ids);
        includes = (uu___203_2392.includes);
        sigaccum = (uu___203_2392.sigaccum);
        sigmap = (uu___203_2392.sigmap);
        iface = (uu___203_2392.iface);
        admitted_iface = (uu___203_2392.admitted_iface);
        expect_typ = (uu___203_2392.expect_typ);
        docs = (uu___203_2392.docs);
        remaining_iface_decls = (uu___203_2392.remaining_iface_decls);
        syntax_only = b;
        ds_hooks = (uu___203_2392.ds_hooks);
        dep_graph = (uu___203_2392.dep_graph)
      }
  
let (ds_hooks : env -> dsenv_hooks) = fun env  -> env.ds_hooks 
let (set_ds_hooks : env -> dsenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___204_2408 = env  in
      {
        curmodule = (uu___204_2408.curmodule);
        curmonad = (uu___204_2408.curmonad);
        modules = (uu___204_2408.modules);
        scope_mods = (uu___204_2408.scope_mods);
        exported_ids = (uu___204_2408.exported_ids);
        trans_exported_ids = (uu___204_2408.trans_exported_ids);
        includes = (uu___204_2408.includes);
        sigaccum = (uu___204_2408.sigaccum);
        sigmap = (uu___204_2408.sigmap);
        iface = (uu___204_2408.iface);
        admitted_iface = (uu___204_2408.admitted_iface);
        expect_typ = (uu___204_2408.expect_typ);
        docs = (uu___204_2408.docs);
        remaining_iface_decls = (uu___204_2408.remaining_iface_decls);
        syntax_only = (uu___204_2408.syntax_only);
        ds_hooks = hooks;
        dep_graph = (uu___204_2408.dep_graph)
      }
  
let new_sigmap : 'Auu____2413 . unit -> 'Auu____2413 FStar_Util.smap =
  fun uu____2420  -> FStar_Util.smap_create (Prims.parse_int "100") 
let (empty_env : FStar_Parser_Dep.deps -> env) =
  fun deps  ->
    let uu____2426 = new_sigmap ()  in
    let uu____2431 = new_sigmap ()  in
    let uu____2436 = new_sigmap ()  in
    let uu____2447 = new_sigmap ()  in
    let uu____2458 = new_sigmap ()  in
    {
      curmodule = FStar_Pervasives_Native.None;
      curmonad = FStar_Pervasives_Native.None;
      modules = [];
      scope_mods = [];
      exported_ids = uu____2426;
      trans_exported_ids = uu____2431;
      includes = uu____2436;
      sigaccum = [];
      sigmap = uu____2447;
      iface = false;
      admitted_iface = false;
      expect_typ = false;
      docs = uu____2458;
      remaining_iface_decls = [];
      syntax_only = false;
      ds_hooks = default_ds_hooks;
      dep_graph = deps
    }
  
let (dep_graph : env -> FStar_Parser_Dep.deps) = fun env  -> env.dep_graph 
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun env  ->
    fun ds  ->
      let uu___205_2486 = env  in
      {
        curmodule = (uu___205_2486.curmodule);
        curmonad = (uu___205_2486.curmonad);
        modules = (uu___205_2486.modules);
        scope_mods = (uu___205_2486.scope_mods);
        exported_ids = (uu___205_2486.exported_ids);
        trans_exported_ids = (uu___205_2486.trans_exported_ids);
        includes = (uu___205_2486.includes);
        sigaccum = (uu___205_2486.sigaccum);
        sigmap = (uu___205_2486.sigmap);
        iface = (uu___205_2486.iface);
        admitted_iface = (uu___205_2486.admitted_iface);
        expect_typ = (uu___205_2486.expect_typ);
        docs = (uu___205_2486.docs);
        remaining_iface_decls = (uu___205_2486.remaining_iface_decls);
        syntax_only = (uu___205_2486.syntax_only);
        ds_hooks = (uu___205_2486.ds_hooks);
        dep_graph = ds
      }
  
let (sigmap :
  env ->
    (FStar_Syntax_Syntax.sigelt,Prims.bool) FStar_Pervasives_Native.tuple2
      FStar_Util.smap)
  = fun env  -> env.sigmap 
let (has_all_in_scope : env -> Prims.bool) =
  fun env  ->
    FStar_List.existsb
      (fun uu____2510  ->
         match uu____2510 with
         | (m,uu____2516) ->
             FStar_Ident.lid_equals m FStar_Parser_Const.all_lid) env.modules
  
let (set_bv_range :
  FStar_Syntax_Syntax.bv -> FStar_Range.range -> FStar_Syntax_Syntax.bv) =
  fun bv  ->
    fun r  ->
      let id1 =
        let uu___206_2528 = bv.FStar_Syntax_Syntax.ppname  in
        {
          FStar_Ident.idText = (uu___206_2528.FStar_Ident.idText);
          FStar_Ident.idRange = r
        }  in
      let uu___207_2529 = bv  in
      {
        FStar_Syntax_Syntax.ppname = id1;
        FStar_Syntax_Syntax.index = (uu___207_2529.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = (uu___207_2529.FStar_Syntax_Syntax.sort)
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
        (fun uu____2622  ->
           match uu____2622 with
           | (x,y,dd,dq) ->
               if id1.FStar_Ident.idText = x
               then
                 let uu____2645 =
                   let uu____2646 =
                     FStar_Ident.lid_of_path ["Prims"; y]
                       id1.FStar_Ident.idRange
                      in
                   FStar_Syntax_Syntax.fvar uu____2646 dd dq  in
                 FStar_Pervasives_Native.Some uu____2645
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
    match projectee with | Cont_ok _0 -> true | uu____2693 -> false
  
let __proj__Cont_ok__item___0 : 'a . 'a cont_t -> 'a =
  fun projectee  -> match projectee with | Cont_ok _0 -> _0 
let uu___is_Cont_fail : 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_fail  -> true | uu____2726 -> false
  
let uu___is_Cont_ignore : 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_ignore  -> true | uu____2743 -> false
  
let option_of_cont :
  'a .
    (unit -> 'a FStar_Pervasives_Native.option) ->
      'a cont_t -> 'a FStar_Pervasives_Native.option
  =
  fun k_ignore  ->
    fun uu___166_2771  ->
      match uu___166_2771 with
      | Cont_ok a -> FStar_Pervasives_Native.Some a
      | Cont_fail  -> FStar_Pervasives_Native.None
      | Cont_ignore  -> k_ignore ()
  
let find_in_record :
  'Auu____2789 .
    FStar_Ident.ident Prims.list ->
      FStar_Ident.ident ->
        record_or_dc ->
          (record_or_dc -> 'Auu____2789 cont_t) -> 'Auu____2789 cont_t
  =
  fun ns  ->
    fun id1  ->
      fun record  ->
        fun cont  ->
          let typename' =
            FStar_Ident.lid_of_ids
              (FStar_List.append ns [(record.typename).FStar_Ident.ident])
             in
          let uu____2826 = FStar_Ident.lid_equals typename' record.typename
             in
          if uu____2826
          then
            let fname =
              FStar_Ident.lid_of_ids
                (FStar_List.append (record.typename).FStar_Ident.ns [id1])
               in
            let find1 =
              FStar_Util.find_map record.fields
                (fun uu____2840  ->
                   match uu____2840 with
                   | (f,uu____2848) ->
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
  fun uu___167_2910  ->
    match uu___167_2910 with
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
              let rec aux uu___168_2981 =
                match uu___168_2981 with
                | [] -> find_in_module_default
                | modul::q ->
                    let mname = modul.FStar_Ident.str  in
                    let not_shadowed =
                      let uu____2992 = get_exported_id_set env mname  in
                      match uu____2992 with
                      | FStar_Pervasives_Native.None  -> true
                      | FStar_Pervasives_Native.Some mex ->
                          let mexports =
                            let uu____3017 = mex eikind  in
                            FStar_ST.op_Bang uu____3017  in
                          FStar_Util.set_mem idstr mexports
                       in
                    let mincludes =
                      let uu____3131 =
                        FStar_Util.smap_try_find env.includes mname  in
                      match uu____3131 with
                      | FStar_Pervasives_Native.None  -> []
                      | FStar_Pervasives_Native.Some minc ->
                          FStar_ST.op_Bang minc
                       in
                    let look_into =
                      if not_shadowed
                      then
                        let uu____3207 = qual modul id1  in
                        find_in_module uu____3207
                      else Cont_ignore  in
                    (match look_into with
                     | Cont_ignore  -> aux (FStar_List.append mincludes q)
                     | uu____3211 -> look_into)
                 in
              aux [ns]
  
let (is_exported_id_field : exported_id_kind -> Prims.bool) =
  fun uu___169_3218  ->
    match uu___169_3218 with
    | Exported_id_field  -> true
    | uu____3219 -> false
  
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
                  let check_local_binding_id uu___170_3340 =
                    match uu___170_3340 with
                    | (id',uu____3342,uu____3343) ->
                        id'.FStar_Ident.idText = id1.FStar_Ident.idText
                     in
                  let check_rec_binding_id uu___171_3349 =
                    match uu___171_3349 with
                    | (id',uu____3351,uu____3352) ->
                        id'.FStar_Ident.idText = id1.FStar_Ident.idText
                     in
                  let curmod_ns =
                    let uu____3356 = current_module env  in
                    FStar_Ident.ids_of_lid uu____3356  in
                  let proc uu___172_3364 =
                    match uu___172_3364 with
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
                        let uu____3372 = FStar_Ident.lid_of_ids curmod_ns  in
                        find_in_module_with_includes Exported_id_field
                          (fun lid  ->
                             let id2 = lid.FStar_Ident.ident  in
                             find_in_record lid.FStar_Ident.ns id2 r k_record)
                          Cont_ignore env uu____3372 id1
                    | uu____3377 -> Cont_ignore  in
                  let rec aux uu___173_3387 =
                    match uu___173_3387 with
                    | a::q ->
                        let uu____3396 = proc a  in
                        option_of_cont (fun uu____3400  -> aux q) uu____3396
                    | [] ->
                        let uu____3401 = lookup_default_id Cont_fail id1  in
                        option_of_cont
                          (fun uu____3405  -> FStar_Pervasives_Native.None)
                          uu____3401
                     in
                  aux env.scope_mods
  
let found_local_binding :
  'Auu____3414 'Auu____3415 .
    FStar_Range.range ->
      ('Auu____3414,FStar_Syntax_Syntax.bv,'Auu____3415)
        FStar_Pervasives_Native.tuple3 ->
        (FStar_Syntax_Syntax.term,'Auu____3415)
          FStar_Pervasives_Native.tuple2
  =
  fun r  ->
    fun uu____3435  ->
      match uu____3435 with
      | (id',x,mut) -> let uu____3445 = bv_to_name x r  in (uu____3445, mut)
  
let find_in_module :
  'Auu____3456 .
    env ->
      FStar_Ident.lident ->
        (FStar_Ident.lident ->
           (FStar_Syntax_Syntax.sigelt,Prims.bool)
             FStar_Pervasives_Native.tuple2 -> 'Auu____3456)
          -> 'Auu____3456 -> 'Auu____3456
  =
  fun env  ->
    fun lid  ->
      fun k_global_def  ->
        fun k_not_found  ->
          let uu____3495 =
            FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str  in
          match uu____3495 with
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
      let uu____3535 = unmangleOpName id1  in
      match uu____3535 with
      | FStar_Pervasives_Native.Some f -> FStar_Pervasives_Native.Some f
      | uu____3561 ->
          try_lookup_id'' env id1 Exported_id_term_type
            (fun r  ->
               let uu____3575 = found_local_binding id1.FStar_Ident.idRange r
                  in
               Cont_ok uu____3575) (fun uu____3585  -> Cont_fail)
            (fun uu____3591  -> Cont_ignore)
            (fun i  ->
               find_in_module env i
                 (fun uu____3606  -> fun uu____3607  -> Cont_fail)
                 Cont_ignore)
            (fun uu____3622  -> fun uu____3623  -> Cont_fail)
  
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
            | FStar_Pervasives_Native.Some uu____3702 ->
                let lid = qualify env id1  in
                let uu____3704 =
                  FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str
                   in
                (match uu____3704 with
                 | FStar_Pervasives_Native.Some r ->
                     let uu____3728 = k_global_def lid r  in
                     FStar_Pervasives_Native.Some uu____3728
                 | FStar_Pervasives_Native.None  ->
                     FStar_Pervasives_Native.None)
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             in
          match find_in_monad with
          | FStar_Pervasives_Native.Some v1 -> v1
          | FStar_Pervasives_Native.None  ->
              let lid =
                let uu____3751 = current_module env  in qual uu____3751 id1
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
        let rec aux uu___174_3814 =
          match uu___174_3814 with
          | [] ->
              let uu____3819 = module_is_defined env lid  in
              if uu____3819
              then FStar_Pervasives_Native.Some lid
              else FStar_Pervasives_Native.None
          | (Open_module_or_namespace (ns,Open_namespace ))::q when honor_ns
              ->
              let new_lid =
                let uu____3828 =
                  let uu____3829 = FStar_Ident.path_of_lid ns  in
                  let uu____3832 = FStar_Ident.path_of_lid lid  in
                  FStar_List.append uu____3829 uu____3832  in
                let uu____3835 = FStar_Ident.range_of_lid lid  in
                FStar_Ident.lid_of_path uu____3828 uu____3835  in
              let uu____3836 = module_is_defined env new_lid  in
              if uu____3836
              then FStar_Pervasives_Native.Some new_lid
              else aux q
          | (Module_abbrev (name,modul))::uu____3842 when
              (nslen = (Prims.parse_int "0")) &&
                (name.FStar_Ident.idText =
                   (lid.FStar_Ident.ident).FStar_Ident.idText)
              -> FStar_Pervasives_Native.Some modul
          | uu____3849::q -> aux q  in
        aux env.scope_mods
  
let (fail_if_curmodule :
  env -> FStar_Ident.lident -> FStar_Ident.lident -> unit) =
  fun env  ->
    fun ns_original  ->
      fun ns_resolved  ->
        let uu____3868 =
          let uu____3869 = current_module env  in
          FStar_Ident.lid_equals ns_resolved uu____3869  in
        if uu____3868
        then
          let uu____3870 =
            FStar_Ident.lid_equals ns_resolved FStar_Parser_Const.prims_lid
             in
          (if uu____3870
           then ()
           else
             (let uu____3872 =
                let uu____3877 =
                  FStar_Util.format1
                    "Reference %s to current module is forbidden (see GitHub issue #451)"
                    ns_original.FStar_Ident.str
                   in
                (FStar_Errors.Fatal_ForbiddenReferenceToCurrentModule,
                  uu____3877)
                 in
              let uu____3878 = FStar_Ident.range_of_lid ns_original  in
              FStar_Errors.raise_error uu____3872 uu____3878))
        else ()
  
let (fail_if_qualified_by_curmodule : env -> FStar_Ident.lident -> unit) =
  fun env  ->
    fun lid  ->
      match lid.FStar_Ident.ns with
      | [] -> ()
      | uu____3890 ->
          let modul_orig = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          let uu____3894 = resolve_module_name env modul_orig true  in
          (match uu____3894 with
           | FStar_Pervasives_Native.Some modul_res ->
               fail_if_curmodule env modul_orig modul_res
           | uu____3898 -> ())
  
let (is_open : env -> FStar_Ident.lident -> open_kind -> Prims.bool) =
  fun env  ->
    fun lid  ->
      fun open_kind  ->
        FStar_List.existsb
          (fun uu___175_3919  ->
             match uu___175_3919 with
             | Open_module_or_namespace (ns,k) ->
                 (k = open_kind) && (FStar_Ident.lid_equals lid ns)
             | uu____3922 -> false) env.scope_mods
  
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
                 let uu____4041 = aux rev_ns_prefix ns_last_id  in
                 FStar_All.pipe_right uu____4041
                   (FStar_Util.map_option
                      (fun uu____4091  ->
                         match uu____4091 with
                         | (stripped_ids,rev_kept_ids) ->
                             (stripped_ids, (id1 :: rev_kept_ids)))))
           in
        let do_shorten env1 ids1 =
          match FStar_List.rev ids1 with
          | [] -> ([], [])
          | ns_last_id::ns_rev_prefix ->
              let uu____4161 = aux ns_rev_prefix ns_last_id  in
              (match uu____4161 with
               | FStar_Pervasives_Native.None  -> ([], ids1)
               | FStar_Pervasives_Native.Some (stripped_ids,rev_kept_ids) ->
                   (stripped_ids, (FStar_List.rev rev_kept_ids)))
           in
        if is_full_path && ((FStar_List.length ids) > (Prims.parse_int "0"))
        then
          let uu____4222 =
            let uu____4225 = FStar_Ident.lid_of_ids ids  in
            resolve_module_name env uu____4225 true  in
          match uu____4222 with
          | FStar_Pervasives_Native.Some m when module_is_open env m ->
              (ids, [])
          | uu____4239 -> do_shorten env ids
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
                  | uu____4358::uu____4359 ->
                      let uu____4362 =
                        let uu____4365 =
                          let uu____4366 =
                            FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
                          let uu____4367 = FStar_Ident.range_of_lid lid  in
                          FStar_Ident.set_lid_range uu____4366 uu____4367  in
                        resolve_module_name env uu____4365 true  in
                      (match uu____4362 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some modul ->
                           let uu____4371 =
                             find_in_module_with_includes eikind f_module
                               Cont_fail env modul lid.FStar_Ident.ident
                              in
                           option_of_cont
                             (fun uu____4375  -> FStar_Pervasives_Native.None)
                             uu____4371)
                  | [] ->
                      try_lookup_id'' env lid.FStar_Ident.ident eikind
                        k_local_binding k_rec_binding k_record f_module
                        l_default
  
let cont_of_option :
  'a . 'a cont_t -> 'a FStar_Pervasives_Native.option -> 'a cont_t =
  fun k_none  ->
    fun uu___176_4398  ->
      match uu___176_4398 with
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
              let uu____4514 = k_global_def lid1 def  in
              cont_of_option k uu____4514  in
            let f_module lid' =
              let k = Cont_ignore  in
              find_in_module env lid' (k_global_def' k) k  in
            let l_default k i = lookup_default_id env i (k_global_def' k) k
               in
            resolve_in_open_namespaces'' env lid Exported_id_term_type
              (fun l  ->
                 let uu____4550 = k_local_binding l  in
                 cont_of_option Cont_fail uu____4550)
              (fun r  ->
                 let uu____4556 = k_rec_binding r  in
                 cont_of_option Cont_fail uu____4556)
              (fun uu____4560  -> Cont_ignore) f_module l_default
  
let (fv_qual_of_se :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option)
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____4570,uu____4571,uu____4572,l,uu____4574,uu____4575) ->
        let qopt =
          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
            (fun uu___177_4586  ->
               match uu___177_4586 with
               | FStar_Syntax_Syntax.RecordConstructor (uu____4589,fs) ->
                   FStar_Pervasives_Native.Some
                     (FStar_Syntax_Syntax.Record_ctor (l, fs))
               | uu____4601 -> FStar_Pervasives_Native.None)
           in
        (match qopt with
         | FStar_Pervasives_Native.None  ->
             FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor
         | x -> x)
    | FStar_Syntax_Syntax.Sig_declare_typ (uu____4607,uu____4608,uu____4609)
        -> FStar_Pervasives_Native.None
    | uu____4610 -> FStar_Pervasives_Native.None
  
let (lb_fv :
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Ident.lident -> FStar_Syntax_Syntax.fv)
  =
  fun lbs  ->
    fun lid  ->
      let uu____4625 =
        FStar_Util.find_map lbs
          (fun lb  ->
             let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
             let uu____4633 = FStar_Syntax_Syntax.fv_eq_lid fv lid  in
             if uu____4633
             then FStar_Pervasives_Native.Some fv
             else FStar_Pervasives_Native.None)
         in
      FStar_All.pipe_right uu____4625 FStar_Util.must
  
let (ns_of_lid_equals :
  FStar_Ident.lident -> FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    fun ns  ->
      (let uu____4651 =
         let uu____4652 = FStar_Ident.ids_of_lid ns  in
         FStar_List.length uu____4652  in
       (FStar_List.length lid.FStar_Ident.ns) = uu____4651) &&
        (let uu____4660 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
         FStar_Ident.lid_equals uu____4660 ns)
  
let (delta_depth_of_declaration :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Syntax_Syntax.delta_depth)
  =
  fun lid  ->
    fun quals  ->
      let dd =
        let uu____4676 =
          (FStar_Syntax_Util.is_primop_lid lid) ||
            (FStar_All.pipe_right quals
               (FStar_Util.for_some
                  (fun uu___178_4681  ->
                     match uu___178_4681 with
                     | FStar_Syntax_Syntax.Projector uu____4682 -> true
                     | FStar_Syntax_Syntax.Discriminator uu____4687 -> true
                     | uu____4688 -> false)))
           in
        if uu____4676
        then FStar_Syntax_Syntax.delta_equational
        else FStar_Syntax_Syntax.delta_constant  in
      let uu____4690 =
        (FStar_All.pipe_right quals
           (FStar_Util.for_some
              (fun uu___179_4694  ->
                 match uu___179_4694 with
                 | FStar_Syntax_Syntax.Abstract  -> true
                 | uu____4695 -> false)))
          ||
          ((FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___180_4699  ->
                    match uu___180_4699 with
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____4700 -> false)))
             &&
             (let uu____4702 =
                FStar_All.pipe_right quals
                  (FStar_Util.for_some
                     (fun uu___181_4706  ->
                        match uu___181_4706 with
                        | FStar_Syntax_Syntax.New  -> true
                        | uu____4707 -> false))
                 in
              Prims.op_Negation uu____4702))
         in
      if uu____4690 then FStar_Syntax_Syntax.Delta_abstract dd else dd
  
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
          let k_global_def source_lid uu___184_4750 =
            match uu___184_4750 with
            | (uu____4757,true ) when exclude_interf ->
                FStar_Pervasives_Native.None
            | (se,uu____4759) ->
                (match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_inductive_typ uu____4762 ->
                     let uu____4779 =
                       let uu____4780 =
                         let uu____4789 =
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None
                            in
                         (uu____4789, false,
                           (se.FStar_Syntax_Syntax.sigattrs))
                          in
                       Term_name uu____4780  in
                     FStar_Pervasives_Native.Some uu____4779
                 | FStar_Syntax_Syntax.Sig_datacon uu____4792 ->
                     let uu____4807 =
                       let uu____4808 =
                         let uu____4817 =
                           let uu____4818 = fv_qual_of_se se  in
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.delta_constant uu____4818
                            in
                         (uu____4817, false,
                           (se.FStar_Syntax_Syntax.sigattrs))
                          in
                       Term_name uu____4808  in
                     FStar_Pervasives_Native.Some uu____4807
                 | FStar_Syntax_Syntax.Sig_let ((uu____4823,lbs),uu____4825)
                     ->
                     let fv = lb_fv lbs source_lid  in
                     let uu____4835 =
                       let uu____4836 =
                         let uu____4845 =
                           FStar_Syntax_Syntax.fvar source_lid
                             fv.FStar_Syntax_Syntax.fv_delta
                             fv.FStar_Syntax_Syntax.fv_qual
                            in
                         (uu____4845, false,
                           (se.FStar_Syntax_Syntax.sigattrs))
                          in
                       Term_name uu____4836  in
                     FStar_Pervasives_Native.Some uu____4835
                 | FStar_Syntax_Syntax.Sig_declare_typ
                     (lid1,uu____4849,uu____4850) ->
                     let quals = se.FStar_Syntax_Syntax.sigquals  in
                     let uu____4854 =
                       any_val ||
                         (FStar_All.pipe_right quals
                            (FStar_Util.for_some
                               (fun uu___182_4858  ->
                                  match uu___182_4858 with
                                  | FStar_Syntax_Syntax.Assumption  -> true
                                  | uu____4859 -> false)))
                        in
                     if uu____4854
                     then
                       let lid2 =
                         let uu____4863 = FStar_Ident.range_of_lid source_lid
                            in
                         FStar_Ident.set_lid_range lid1 uu____4863  in
                       let dd = delta_depth_of_declaration lid2 quals  in
                       let uu____4865 =
                         FStar_Util.find_map quals
                           (fun uu___183_4870  ->
                              match uu___183_4870 with
                              | FStar_Syntax_Syntax.Reflectable refl_monad ->
                                  FStar_Pervasives_Native.Some refl_monad
                              | uu____4874 -> FStar_Pervasives_Native.None)
                          in
                       (match uu____4865 with
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
                        | uu____4883 ->
                            let uu____4886 =
                              let uu____4887 =
                                let uu____4896 =
                                  let uu____4897 = fv_qual_of_se se  in
                                  FStar_Syntax_Syntax.fvar lid2 dd uu____4897
                                   in
                                (uu____4896, false,
                                  (se.FStar_Syntax_Syntax.sigattrs))
                                 in
                              Term_name uu____4887  in
                            FStar_Pervasives_Native.Some uu____4886)
                     else FStar_Pervasives_Native.None
                 | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
                     let uu____4904 =
                       let uu____4905 =
                         let uu____4910 =
                           let uu____4911 =
                             FStar_Ident.range_of_lid source_lid  in
                           FStar_Ident.set_lid_range
                             ne.FStar_Syntax_Syntax.mname uu____4911
                            in
                         (se, uu____4910)  in
                       Eff_name uu____4905  in
                     FStar_Pervasives_Native.Some uu____4904
                 | FStar_Syntax_Syntax.Sig_new_effect ne ->
                     let uu____4913 =
                       let uu____4914 =
                         let uu____4919 =
                           let uu____4920 =
                             FStar_Ident.range_of_lid source_lid  in
                           FStar_Ident.set_lid_range
                             ne.FStar_Syntax_Syntax.mname uu____4920
                            in
                         (se, uu____4919)  in
                       Eff_name uu____4914  in
                     FStar_Pervasives_Native.Some uu____4913
                 | FStar_Syntax_Syntax.Sig_effect_abbrev uu____4921 ->
                     FStar_Pervasives_Native.Some (Eff_name (se, source_lid))
                 | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
                     let uu____4940 =
                       let uu____4941 =
                         let uu____4950 =
                           FStar_Syntax_Syntax.fvar source_lid
                             (FStar_Syntax_Syntax.Delta_constant_at_level
                                (Prims.parse_int "1"))
                             FStar_Pervasives_Native.None
                            in
                         (uu____4950, false, [])  in
                       Term_name uu____4941  in
                     FStar_Pervasives_Native.Some uu____4940
                 | uu____4953 -> FStar_Pervasives_Native.None)
             in
          let k_local_binding r =
            let uu____4974 =
              let uu____4979 = FStar_Ident.range_of_lid lid  in
              found_local_binding uu____4979 r  in
            match uu____4974 with
            | (t,mut) ->
                FStar_Pervasives_Native.Some (Term_name (t, mut, []))
             in
          let k_rec_binding uu____4999 =
            match uu____4999 with
            | (id1,l,dd) ->
                let uu____5011 =
                  let uu____5012 =
                    let uu____5021 =
                      let uu____5022 =
                        let uu____5023 = FStar_Ident.range_of_lid lid  in
                        FStar_Ident.set_lid_range l uu____5023  in
                      FStar_Syntax_Syntax.fvar uu____5022 dd
                        FStar_Pervasives_Native.None
                       in
                    (uu____5021, false, [])  in
                  Term_name uu____5012  in
                FStar_Pervasives_Native.Some uu____5011
             in
          let found_unmangled =
            match lid.FStar_Ident.ns with
            | [] ->
                let uu____5031 = unmangleOpName lid.FStar_Ident.ident  in
                (match uu____5031 with
                 | FStar_Pervasives_Native.Some (t,mut) ->
                     FStar_Pervasives_Native.Some (Term_name (t, mut, []))
                 | uu____5048 -> FStar_Pervasives_Native.None)
            | uu____5055 -> FStar_Pervasives_Native.None  in
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
        let uu____5090 = try_lookup_name true exclude_interf env lid  in
        match uu____5090 with
        | FStar_Pervasives_Native.Some (Eff_name (o,l)) ->
            FStar_Pervasives_Native.Some (o, l)
        | uu____5105 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____5124 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____5124 with
      | FStar_Pervasives_Native.Some (o,l1) ->
          FStar_Pervasives_Native.Some l1
      | uu____5139 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_name_and_attributes :
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident,FStar_Syntax_Syntax.cflags Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____5164 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____5164 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____5180;
             FStar_Syntax_Syntax.sigquals = uu____5181;
             FStar_Syntax_Syntax.sigmeta = uu____5182;
             FStar_Syntax_Syntax.sigattrs = uu____5183;_},l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____5202;
             FStar_Syntax_Syntax.sigquals = uu____5203;
             FStar_Syntax_Syntax.sigmeta = uu____5204;
             FStar_Syntax_Syntax.sigattrs = uu____5205;_},l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (uu____5223,uu____5224,uu____5225,uu____5226,cattributes);
             FStar_Syntax_Syntax.sigrng = uu____5228;
             FStar_Syntax_Syntax.sigquals = uu____5229;
             FStar_Syntax_Syntax.sigmeta = uu____5230;
             FStar_Syntax_Syntax.sigattrs = uu____5231;_},l1)
          -> FStar_Pervasives_Native.Some (l1, cattributes)
      | uu____5253 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_defn :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.eff_decl FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____5278 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____5278 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____5288;
             FStar_Syntax_Syntax.sigquals = uu____5289;
             FStar_Syntax_Syntax.sigmeta = uu____5290;
             FStar_Syntax_Syntax.sigattrs = uu____5291;_},uu____5292)
          -> FStar_Pervasives_Native.Some ne
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____5302;
             FStar_Syntax_Syntax.sigquals = uu____5303;
             FStar_Syntax_Syntax.sigmeta = uu____5304;
             FStar_Syntax_Syntax.sigattrs = uu____5305;_},uu____5306)
          -> FStar_Pervasives_Native.Some ne
      | uu____5315 -> FStar_Pervasives_Native.None
  
let (is_effect_name : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____5332 = try_lookup_effect_name env lid  in
      match uu____5332 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____5335 -> true
  
let (try_lookup_root_effect_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____5348 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____5348 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (l',uu____5358,uu____5359,uu____5360,uu____5361);
             FStar_Syntax_Syntax.sigrng = uu____5362;
             FStar_Syntax_Syntax.sigquals = uu____5363;
             FStar_Syntax_Syntax.sigmeta = uu____5364;
             FStar_Syntax_Syntax.sigattrs = uu____5365;_},uu____5366)
          ->
          let rec aux new_name =
            let uu____5387 =
              FStar_Util.smap_try_find (sigmap env) new_name.FStar_Ident.str
               in
            match uu____5387 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (s,uu____5405) ->
                (match s.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
                     let uu____5413 =
                       let uu____5414 = FStar_Ident.range_of_lid l  in
                       FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname
                         uu____5414
                        in
                     FStar_Pervasives_Native.Some uu____5413
                 | FStar_Syntax_Syntax.Sig_new_effect ne ->
                     let uu____5416 =
                       let uu____5417 = FStar_Ident.range_of_lid l  in
                       FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname
                         uu____5417
                        in
                     FStar_Pervasives_Native.Some uu____5416
                 | FStar_Syntax_Syntax.Sig_effect_abbrev
                     (uu____5418,uu____5419,uu____5420,cmp,uu____5422) ->
                     let l'' = FStar_Syntax_Util.comp_effect_name cmp  in
                     aux l''
                 | uu____5428 -> FStar_Pervasives_Native.None)
             in
          aux l'
      | FStar_Pervasives_Native.Some (uu____5429,l') ->
          FStar_Pervasives_Native.Some l'
      | uu____5435 -> FStar_Pervasives_Native.None
  
let (lookup_letbinding_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___185_5472 =
        match uu___185_5472 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____5481,uu____5482,uu____5483);
             FStar_Syntax_Syntax.sigrng = uu____5484;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____5486;
             FStar_Syntax_Syntax.sigattrs = uu____5487;_},uu____5488)
            -> FStar_Pervasives_Native.Some quals
        | uu____5495 -> FStar_Pervasives_Native.None  in
      let uu____5502 =
        resolve_in_open_namespaces' env lid
          (fun uu____5510  -> FStar_Pervasives_Native.None)
          (fun uu____5514  -> FStar_Pervasives_Native.None) k_global_def
         in
      match uu____5502 with
      | FStar_Pervasives_Native.Some quals -> quals
      | uu____5524 -> []
  
let (try_lookup_module :
  env ->
    FStar_Ident.path ->
      FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun path  ->
      let uu____5541 =
        FStar_List.tryFind
          (fun uu____5556  ->
             match uu____5556 with
             | (mlid,modul) ->
                 let uu____5563 = FStar_Ident.path_of_lid mlid  in
                 uu____5563 = path) env.modules
         in
      match uu____5541 with
      | FStar_Pervasives_Native.Some (uu____5566,modul) ->
          FStar_Pervasives_Native.Some modul
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (try_lookup_let :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___186_5604 =
        match uu___186_5604 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               ((uu____5611,lbs),uu____5613);
             FStar_Syntax_Syntax.sigrng = uu____5614;
             FStar_Syntax_Syntax.sigquals = uu____5615;
             FStar_Syntax_Syntax.sigmeta = uu____5616;
             FStar_Syntax_Syntax.sigattrs = uu____5617;_},uu____5618)
            ->
            let fv = lb_fv lbs lid1  in
            let uu____5632 =
              FStar_Syntax_Syntax.fvar lid1 fv.FStar_Syntax_Syntax.fv_delta
                fv.FStar_Syntax_Syntax.fv_qual
               in
            FStar_Pervasives_Native.Some uu____5632
        | uu____5633 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____5639  -> FStar_Pervasives_Native.None)
        (fun uu____5641  -> FStar_Pervasives_Native.None) k_global_def
  
let (try_lookup_definition :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___187_5672 =
        match uu___187_5672 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               (lbs,uu____5682);
             FStar_Syntax_Syntax.sigrng = uu____5683;
             FStar_Syntax_Syntax.sigquals = uu____5684;
             FStar_Syntax_Syntax.sigmeta = uu____5685;
             FStar_Syntax_Syntax.sigattrs = uu____5686;_},uu____5687)
            ->
            FStar_Util.find_map (FStar_Pervasives_Native.snd lbs)
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inr fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv lid1 ->
                     FStar_Pervasives_Native.Some
                       (lb.FStar_Syntax_Syntax.lbdef)
                 | uu____5710 -> FStar_Pervasives_Native.None)
        | uu____5717 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____5727  -> FStar_Pervasives_Native.None)
        (fun uu____5731  -> FStar_Pervasives_Native.None) k_global_def
  
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
          let uu____5788 = try_lookup_name any_val exclude_interface env lid
             in
          match uu____5788 with
          | FStar_Pervasives_Native.Some (Term_name (e,mut,attrs)) ->
              FStar_Pervasives_Native.Some (e, mut, attrs)
          | uu____5818 -> FStar_Pervasives_Native.None
  
let (drop_attributes :
  (FStar_Syntax_Syntax.term,Prims.bool,FStar_Syntax_Syntax.attribute
                                         Prims.list)
    FStar_Pervasives_Native.tuple3 FStar_Pervasives_Native.option ->
    (FStar_Syntax_Syntax.term,Prims.bool) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option)
  =
  fun x  ->
    match x with
    | FStar_Pervasives_Native.Some (t,mut,uu____5874) ->
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
      let uu____5949 = try_lookup_lid_with_attributes env l  in
      FStar_All.pipe_right uu____5949 drop_attributes
  
let (resolve_to_fully_qualified_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____5988 = try_lookup_lid env l  in
      match uu____5988 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (e,uu____6002) ->
          let uu____6007 =
            let uu____6008 = FStar_Syntax_Subst.compress e  in
            uu____6008.FStar_Syntax_Syntax.n  in
          (match uu____6007 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               FStar_Pervasives_Native.Some
                 ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
           | uu____6014 -> FStar_Pervasives_Native.None)
  
let (shorten_lid' : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____6025 = shorten_module_path env lid.FStar_Ident.ns true  in
      match uu____6025 with
      | (uu____6034,short) ->
          FStar_Ident.lid_of_ns_and_id short lid.FStar_Ident.ident
  
let (shorten_lid : env -> FStar_Ident.lid -> FStar_Ident.lid) =
  fun env  ->
    fun lid  ->
      match env.curmodule with
      | FStar_Pervasives_Native.None  -> shorten_lid' env lid
      | uu____6054 ->
          let lid_without_ns =
            FStar_Ident.lid_of_ns_and_id [] lid.FStar_Ident.ident  in
          let uu____6058 = resolve_to_fully_qualified_name env lid_without_ns
             in
          (match uu____6058 with
           | FStar_Pervasives_Native.Some lid' when
               lid'.FStar_Ident.str = lid.FStar_Ident.str -> lid_without_ns
           | uu____6062 -> shorten_lid' env lid)
  
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
        let uu___208_6096 = env  in
        {
          curmodule = (uu___208_6096.curmodule);
          curmonad = (uu___208_6096.curmonad);
          modules = (uu___208_6096.modules);
          scope_mods = [];
          exported_ids = empty_exported_id_smap;
          trans_exported_ids = (uu___208_6096.trans_exported_ids);
          includes = empty_include_smap;
          sigaccum = (uu___208_6096.sigaccum);
          sigmap = (uu___208_6096.sigmap);
          iface = (uu___208_6096.iface);
          admitted_iface = (uu___208_6096.admitted_iface);
          expect_typ = (uu___208_6096.expect_typ);
          docs = (uu___208_6096.docs);
          remaining_iface_decls = (uu___208_6096.remaining_iface_decls);
          syntax_only = (uu___208_6096.syntax_only);
          ds_hooks = (uu___208_6096.ds_hooks);
          dep_graph = (uu___208_6096.dep_graph)
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
      let uu____6119 = try_lookup_lid_with_attributes_no_resolve env l  in
      FStar_All.pipe_right uu____6119 drop_attributes
  
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
               (uu____6193,uu____6194,uu____6195);
             FStar_Syntax_Syntax.sigrng = uu____6196;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____6198;
             FStar_Syntax_Syntax.sigattrs = uu____6199;_},uu____6200)
            ->
            let uu____6205 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___188_6209  ->
                      match uu___188_6209 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | uu____6210 -> false))
               in
            if uu____6205
            then
              let uu____6213 =
                FStar_Syntax_Syntax.lid_as_fv lid1
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Pervasives_Native.Some uu____6213
            else FStar_Pervasives_Native.None
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
               uu____6215;
             FStar_Syntax_Syntax.sigrng = uu____6216;
             FStar_Syntax_Syntax.sigquals = uu____6217;
             FStar_Syntax_Syntax.sigmeta = uu____6218;
             FStar_Syntax_Syntax.sigattrs = uu____6219;_},uu____6220)
            ->
            let qual1 = fv_qual_of_se (FStar_Pervasives_Native.fst se)  in
            let uu____6242 =
              FStar_Syntax_Syntax.lid_as_fv lid1
                FStar_Syntax_Syntax.delta_constant qual1
               in
            FStar_Pervasives_Native.Some uu____6242
        | uu____6243 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____6249  -> FStar_Pervasives_Native.None)
        (fun uu____6251  -> FStar_Pervasives_Native.None) k_global_def
  
let (find_all_datacons :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___189_6284 =
        match uu___189_6284 with
        | ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_inductive_typ
               (uu____6293,uu____6294,uu____6295,uu____6296,datas,uu____6298);
             FStar_Syntax_Syntax.sigrng = uu____6299;
             FStar_Syntax_Syntax.sigquals = uu____6300;
             FStar_Syntax_Syntax.sigmeta = uu____6301;
             FStar_Syntax_Syntax.sigattrs = uu____6302;_},uu____6303)
            -> FStar_Pervasives_Native.Some datas
        | uu____6318 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____6328  -> FStar_Pervasives_Native.None)
        (fun uu____6332  -> FStar_Pervasives_Native.None) k_global_def
  
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
  let push1 uu____6408 =
    let uu____6409 =
      let uu____6414 =
        let uu____6417 = FStar_ST.op_Bang record_cache  in
        FStar_List.hd uu____6417  in
      let uu____6473 = FStar_ST.op_Bang record_cache  in uu____6414 ::
        uu____6473
       in
    FStar_ST.op_Colon_Equals record_cache uu____6409  in
  let pop1 uu____6583 =
    let uu____6584 =
      let uu____6589 = FStar_ST.op_Bang record_cache  in
      FStar_List.tl uu____6589  in
    FStar_ST.op_Colon_Equals record_cache uu____6584  in
  let snapshot1 uu____6703 = FStar_Common.snapshot push1 record_cache ()  in
  let rollback1 depth = FStar_Common.rollback pop1 record_cache depth  in
  let peek1 uu____6769 =
    let uu____6770 = FStar_ST.op_Bang record_cache  in
    FStar_List.hd uu____6770  in
  let insert r =
    let uu____6832 =
      let uu____6837 = let uu____6840 = peek1 ()  in r :: uu____6840  in
      let uu____6843 =
        let uu____6848 = FStar_ST.op_Bang record_cache  in
        FStar_List.tl uu____6848  in
      uu____6837 :: uu____6843  in
    FStar_ST.op_Colon_Equals record_cache uu____6832  in
  let filter1 uu____6960 =
    let rc = peek1 ()  in
    let filtered =
      FStar_List.filter
        (fun r  -> Prims.op_Negation r.is_private_or_abstract) rc
       in
    let uu____6969 =
      let uu____6974 =
        let uu____6979 = FStar_ST.op_Bang record_cache  in
        FStar_List.tl uu____6979  in
      filtered :: uu____6974  in
    FStar_ST.op_Colon_Equals record_cache uu____6969  in
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
        | FStar_Syntax_Syntax.Sig_bundle (sigs,uu____7920) ->
            let is_record =
              FStar_Util.for_some
                (fun uu___190_7938  ->
                   match uu___190_7938 with
                   | FStar_Syntax_Syntax.RecordType uu____7939 -> true
                   | FStar_Syntax_Syntax.RecordConstructor uu____7948 -> true
                   | uu____7957 -> false)
               in
            let find_dc dc =
              FStar_All.pipe_right sigs
                (FStar_Util.find_opt
                   (fun uu___191_7981  ->
                      match uu___191_7981 with
                      | {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_datacon
                            (lid,uu____7983,uu____7984,uu____7985,uu____7986,uu____7987);
                          FStar_Syntax_Syntax.sigrng = uu____7988;
                          FStar_Syntax_Syntax.sigquals = uu____7989;
                          FStar_Syntax_Syntax.sigmeta = uu____7990;
                          FStar_Syntax_Syntax.sigattrs = uu____7991;_} ->
                          FStar_Ident.lid_equals dc lid
                      | uu____8000 -> false))
               in
            FStar_All.pipe_right sigs
              (FStar_List.iter
                 (fun uu___192_8035  ->
                    match uu___192_8035 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ
                          (typename,univs1,parms,uu____8039,uu____8040,dc::[]);
                        FStar_Syntax_Syntax.sigrng = uu____8042;
                        FStar_Syntax_Syntax.sigquals = typename_quals;
                        FStar_Syntax_Syntax.sigmeta = uu____8044;
                        FStar_Syntax_Syntax.sigattrs = uu____8045;_} ->
                        let uu____8056 =
                          let uu____8057 = find_dc dc  in
                          FStar_All.pipe_left FStar_Util.must uu____8057  in
                        (match uu____8056 with
                         | {
                             FStar_Syntax_Syntax.sigel =
                               FStar_Syntax_Syntax.Sig_datacon
                               (constrname,uu____8063,t,uu____8065,uu____8066,uu____8067);
                             FStar_Syntax_Syntax.sigrng = uu____8068;
                             FStar_Syntax_Syntax.sigquals = uu____8069;
                             FStar_Syntax_Syntax.sigmeta = uu____8070;
                             FStar_Syntax_Syntax.sigattrs = uu____8071;_} ->
                             let uu____8080 =
                               FStar_Syntax_Util.arrow_formals t  in
                             (match uu____8080 with
                              | (formals,uu____8096) ->
                                  let is_rec = is_record typename_quals  in
                                  let formals' =
                                    FStar_All.pipe_right formals
                                      (FStar_List.collect
                                         (fun uu____8149  ->
                                            match uu____8149 with
                                            | (x,q) ->
                                                let uu____8162 =
                                                  (FStar_Syntax_Syntax.is_null_bv
                                                     x)
                                                    ||
                                                    (is_rec &&
                                                       (FStar_Syntax_Syntax.is_implicit
                                                          q))
                                                   in
                                                if uu____8162
                                                then []
                                                else [(x, q)]))
                                     in
                                  let fields' =
                                    FStar_All.pipe_right formals'
                                      (FStar_List.map
                                         (fun uu____8215  ->
                                            match uu____8215 with
                                            | (x,q) ->
                                                let uu____8228 =
                                                  if is_rec
                                                  then
                                                    FStar_Syntax_Util.unmangle_field_name
                                                      x.FStar_Syntax_Syntax.ppname
                                                  else
                                                    x.FStar_Syntax_Syntax.ppname
                                                   in
                                                (uu____8228,
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
                                  ((let uu____8241 =
                                      let uu____8244 =
                                        FStar_ST.op_Bang new_globs  in
                                      (Record_or_dc record) :: uu____8244  in
                                    FStar_ST.op_Colon_Equals new_globs
                                      uu____8241);
                                   (match () with
                                    | () ->
                                        ((let add_field uu____8347 =
                                            match uu____8347 with
                                            | (id1,uu____8353) ->
                                                let modul =
                                                  let uu____8355 =
                                                    FStar_Ident.lid_of_ids
                                                      constrname.FStar_Ident.ns
                                                     in
                                                  uu____8355.FStar_Ident.str
                                                   in
                                                let uu____8356 =
                                                  get_exported_id_set e modul
                                                   in
                                                (match uu____8356 with
                                                 | FStar_Pervasives_Native.Some
                                                     my_ex ->
                                                     let my_exported_ids =
                                                       my_ex
                                                         Exported_id_field
                                                        in
                                                     ((let uu____8390 =
                                                         let uu____8391 =
                                                           FStar_ST.op_Bang
                                                             my_exported_ids
                                                            in
                                                         FStar_Util.set_add
                                                           id1.FStar_Ident.idText
                                                           uu____8391
                                                          in
                                                       FStar_ST.op_Colon_Equals
                                                         my_exported_ids
                                                         uu____8390);
                                                      (match () with
                                                       | () ->
                                                           let projname =
                                                             let uu____8477 =
                                                               let uu____8478
                                                                 =
                                                                 FStar_Syntax_Util.mk_field_projector_name_from_ident
                                                                   constrname
                                                                   id1
                                                                  in
                                                               uu____8478.FStar_Ident.ident
                                                                in
                                                             uu____8477.FStar_Ident.idText
                                                              in
                                                           let uu____8480 =
                                                             let uu____8481 =
                                                               FStar_ST.op_Bang
                                                                 my_exported_ids
                                                                in
                                                             FStar_Util.set_add
                                                               projname
                                                               uu____8481
                                                              in
                                                           FStar_ST.op_Colon_Equals
                                                             my_exported_ids
                                                             uu____8480))
                                                 | FStar_Pervasives_Native.None
                                                      -> ())
                                             in
                                          FStar_List.iter add_field fields');
                                         (match () with
                                          | () -> insert_record_cache record)))))
                         | uu____8575 -> ())
                    | uu____8576 -> ()))
        | uu____8577 -> ()
  
let (try_lookup_record_or_dc_by_field_name :
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option) =
  fun env  ->
    fun fieldname  ->
      let find_in_cache fieldname1 =
        let uu____8598 =
          ((fieldname1.FStar_Ident.ns), (fieldname1.FStar_Ident.ident))  in
        match uu____8598 with
        | (ns,id1) ->
            let uu____8615 = peek_record_cache ()  in
            FStar_Util.find_map uu____8615
              (fun record  ->
                 let uu____8621 =
                   find_in_record ns id1 record (fun r  -> Cont_ok r)  in
                 option_of_cont
                   (fun uu____8627  -> FStar_Pervasives_Native.None)
                   uu____8621)
         in
      resolve_in_open_namespaces'' env fieldname Exported_id_field
        (fun uu____8629  -> Cont_ignore) (fun uu____8631  -> Cont_ignore)
        (fun r  -> Cont_ok r)
        (fun fn  ->
           let uu____8637 = find_in_cache fn  in
           cont_of_option Cont_ignore uu____8637)
        (fun k  -> fun uu____8643  -> k)
  
let (try_lookup_record_by_field_name :
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option) =
  fun env  ->
    fun fieldname  ->
      let uu____8658 = try_lookup_record_or_dc_by_field_name env fieldname
         in
      match uu____8658 with
      | FStar_Pervasives_Native.Some r when r.is_record ->
          FStar_Pervasives_Native.Some r
      | uu____8664 -> FStar_Pervasives_Native.None
  
let (belongs_to_record :
  env -> FStar_Ident.lident -> record_or_dc -> Prims.bool) =
  fun env  ->
    fun lid  ->
      fun record  ->
        let uu____8682 = try_lookup_record_by_field_name env lid  in
        match uu____8682 with
        | FStar_Pervasives_Native.Some record' when
            let uu____8686 =
              let uu____8687 =
                FStar_Ident.path_of_ns (record.typename).FStar_Ident.ns  in
              FStar_Ident.text_of_path uu____8687  in
            let uu____8688 =
              let uu____8689 =
                FStar_Ident.path_of_ns (record'.typename).FStar_Ident.ns  in
              FStar_Ident.text_of_path uu____8689  in
            uu____8686 = uu____8688 ->
            let uu____8690 =
              find_in_record (record.typename).FStar_Ident.ns
                lid.FStar_Ident.ident record (fun uu____8694  -> Cont_ok ())
               in
            (match uu____8690 with
             | Cont_ok uu____8695 -> true
             | uu____8696 -> false)
        | uu____8699 -> false
  
let (try_lookup_dc_by_field_name :
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident,Prims.bool) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun fieldname  ->
      let uu____8718 = try_lookup_record_or_dc_by_field_name env fieldname
         in
      match uu____8718 with
      | FStar_Pervasives_Native.Some r ->
          let uu____8728 =
            let uu____8733 =
              let uu____8734 =
                FStar_Ident.lid_of_ids
                  (FStar_List.append (r.typename).FStar_Ident.ns
                     [r.constrname])
                 in
              let uu____8735 = FStar_Ident.range_of_lid fieldname  in
              FStar_Ident.set_lid_range uu____8734 uu____8735  in
            (uu____8733, (r.is_record))  in
          FStar_Pervasives_Native.Some uu____8728
      | uu____8740 -> FStar_Pervasives_Native.None
  
let (string_set_ref_new : unit -> Prims.string FStar_Util.set FStar_ST.ref) =
  fun uu____8766  ->
    let uu____8767 = FStar_Util.new_set FStar_Util.compare  in
    FStar_Util.mk_ref uu____8767
  
let (exported_id_set_new :
  unit -> exported_id_kind -> Prims.string FStar_Util.set FStar_ST.ref) =
  fun uu____8794  ->
    let term_type_set = string_set_ref_new ()  in
    let field_set = string_set_ref_new ()  in
    fun uu___193_8805  ->
      match uu___193_8805 with
      | Exported_id_term_type  -> term_type_set
      | Exported_id_field  -> field_set
  
let (unique :
  Prims.bool -> Prims.bool -> env -> FStar_Ident.lident -> Prims.bool) =
  fun any_val  ->
    fun exclude_interface  ->
      fun env  ->
        fun lid  ->
          let filter_scope_mods uu___194_8857 =
            match uu___194_8857 with
            | Rec_binding uu____8858 -> true
            | uu____8859 -> false  in
          let this_env =
            let uu___209_8861 = env  in
            let uu____8862 =
              FStar_List.filter filter_scope_mods env.scope_mods  in
            {
              curmodule = (uu___209_8861.curmodule);
              curmonad = (uu___209_8861.curmonad);
              modules = (uu___209_8861.modules);
              scope_mods = uu____8862;
              exported_ids = empty_exported_id_smap;
              trans_exported_ids = (uu___209_8861.trans_exported_ids);
              includes = empty_include_smap;
              sigaccum = (uu___209_8861.sigaccum);
              sigmap = (uu___209_8861.sigmap);
              iface = (uu___209_8861.iface);
              admitted_iface = (uu___209_8861.admitted_iface);
              expect_typ = (uu___209_8861.expect_typ);
              docs = (uu___209_8861.docs);
              remaining_iface_decls = (uu___209_8861.remaining_iface_decls);
              syntax_only = (uu___209_8861.syntax_only);
              ds_hooks = (uu___209_8861.ds_hooks);
              dep_graph = (uu___209_8861.dep_graph)
            }  in
          let uu____8865 =
            try_lookup_lid' any_val exclude_interface this_env lid  in
          match uu____8865 with
          | FStar_Pervasives_Native.None  -> true
          | FStar_Pervasives_Native.Some uu____8884 -> false
  
let (push_scope_mod : env -> scope_mod -> env) =
  fun env  ->
    fun scope_mod  ->
      let uu___210_8911 = env  in
      {
        curmodule = (uu___210_8911.curmodule);
        curmonad = (uu___210_8911.curmonad);
        modules = (uu___210_8911.modules);
        scope_mods = (scope_mod :: (env.scope_mods));
        exported_ids = (uu___210_8911.exported_ids);
        trans_exported_ids = (uu___210_8911.trans_exported_ids);
        includes = (uu___210_8911.includes);
        sigaccum = (uu___210_8911.sigaccum);
        sigmap = (uu___210_8911.sigmap);
        iface = (uu___210_8911.iface);
        admitted_iface = (uu___210_8911.admitted_iface);
        expect_typ = (uu___210_8911.expect_typ);
        docs = (uu___210_8911.docs);
        remaining_iface_decls = (uu___210_8911.remaining_iface_decls);
        syntax_only = (uu___210_8911.syntax_only);
        ds_hooks = (uu___210_8911.ds_hooks);
        dep_graph = (uu___210_8911.dep_graph)
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
        let uu____8976 =
          (unique false true env l) || (FStar_Options.interactive ())  in
        if uu____8976
        then push_scope_mod env (Rec_binding (x, l, dd))
        else
          (let uu____8978 = FStar_Ident.range_of_lid l  in
           FStar_Errors.raise_error
             (FStar_Errors.Fatal_DuplicateTopLevelNames,
               (Prims.strcat "Duplicate top-level names " l.FStar_Ident.str))
             uu____8978)
  
let (push_sigelt' : Prims.bool -> env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun fail_on_dup  ->
    fun env  ->
      fun s  ->
        let err l =
          let sopt = FStar_Util.smap_try_find (sigmap env) l.FStar_Ident.str
             in
          let r =
            match sopt with
            | FStar_Pervasives_Native.Some (se,uu____9013) ->
                let uu____9018 =
                  FStar_Util.find_opt (FStar_Ident.lid_equals l)
                    (FStar_Syntax_Util.lids_of_sigelt se)
                   in
                (match uu____9018 with
                 | FStar_Pervasives_Native.Some l1 ->
                     let uu____9022 = FStar_Ident.range_of_lid l1  in
                     FStar_All.pipe_left FStar_Range.string_of_range
                       uu____9022
                 | FStar_Pervasives_Native.None  -> "<unknown>")
            | FStar_Pervasives_Native.None  -> "<unknown>"  in
          let uu____9027 =
            let uu____9032 =
              let uu____9033 = FStar_Ident.text_of_lid l  in
              FStar_Util.format2
                "Duplicate top-level names [%s]; previously declared at %s"
                uu____9033 r
               in
            (FStar_Errors.Fatal_DuplicateTopLevelNames, uu____9032)  in
          let uu____9034 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____9027 uu____9034  in
        let globals = FStar_Util.mk_ref env.scope_mods  in
        let env1 =
          let uu____9043 =
            match s.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_let uu____9052 -> (false, true)
            | FStar_Syntax_Syntax.Sig_bundle uu____9059 -> (false, true)
            | uu____9068 -> (false, false)  in
          match uu____9043 with
          | (any_val,exclude_interface) ->
              let lids = FStar_Syntax_Util.lids_of_sigelt s  in
              let uu____9074 =
                FStar_Util.find_map lids
                  (fun l  ->
                     let uu____9080 =
                       let uu____9081 =
                         unique any_val exclude_interface env l  in
                       Prims.op_Negation uu____9081  in
                     if uu____9080
                     then FStar_Pervasives_Native.Some l
                     else FStar_Pervasives_Native.None)
                 in
              (match uu____9074 with
               | FStar_Pervasives_Native.Some l when fail_on_dup -> err l
               | uu____9086 ->
                   (extract_record env globals s;
                    (let uu___211_9112 = env  in
                     {
                       curmodule = (uu___211_9112.curmodule);
                       curmonad = (uu___211_9112.curmonad);
                       modules = (uu___211_9112.modules);
                       scope_mods = (uu___211_9112.scope_mods);
                       exported_ids = (uu___211_9112.exported_ids);
                       trans_exported_ids =
                         (uu___211_9112.trans_exported_ids);
                       includes = (uu___211_9112.includes);
                       sigaccum = (s :: (env.sigaccum));
                       sigmap = (uu___211_9112.sigmap);
                       iface = (uu___211_9112.iface);
                       admitted_iface = (uu___211_9112.admitted_iface);
                       expect_typ = (uu___211_9112.expect_typ);
                       docs = (uu___211_9112.docs);
                       remaining_iface_decls =
                         (uu___211_9112.remaining_iface_decls);
                       syntax_only = (uu___211_9112.syntax_only);
                       ds_hooks = (uu___211_9112.ds_hooks);
                       dep_graph = (uu___211_9112.dep_graph)
                     })))
           in
        let env2 =
          let uu___212_9114 = env1  in
          let uu____9115 = FStar_ST.op_Bang globals  in
          {
            curmodule = (uu___212_9114.curmodule);
            curmonad = (uu___212_9114.curmonad);
            modules = (uu___212_9114.modules);
            scope_mods = uu____9115;
            exported_ids = (uu___212_9114.exported_ids);
            trans_exported_ids = (uu___212_9114.trans_exported_ids);
            includes = (uu___212_9114.includes);
            sigaccum = (uu___212_9114.sigaccum);
            sigmap = (uu___212_9114.sigmap);
            iface = (uu___212_9114.iface);
            admitted_iface = (uu___212_9114.admitted_iface);
            expect_typ = (uu___212_9114.expect_typ);
            docs = (uu___212_9114.docs);
            remaining_iface_decls = (uu___212_9114.remaining_iface_decls);
            syntax_only = (uu___212_9114.syntax_only);
            ds_hooks = (uu___212_9114.ds_hooks);
            dep_graph = (uu___212_9114.dep_graph)
          }  in
        let uu____9163 =
          match s.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____9189) ->
              let uu____9198 =
                FStar_List.map
                  (fun se  -> ((FStar_Syntax_Util.lids_of_sigelt se), se))
                  ses
                 in
              (env2, uu____9198)
          | uu____9225 -> (env2, [((FStar_Syntax_Util.lids_of_sigelt s), s)])
           in
        match uu____9163 with
        | (env3,lss) ->
            (FStar_All.pipe_right lss
               (FStar_List.iter
                  (fun uu____9284  ->
                     match uu____9284 with
                     | (lids,se) ->
                         FStar_All.pipe_right lids
                           (FStar_List.iter
                              (fun lid  ->
                                 (let uu____9306 =
                                    let uu____9309 = FStar_ST.op_Bang globals
                                       in
                                    (Top_level_def (lid.FStar_Ident.ident))
                                      :: uu____9309
                                     in
                                  FStar_ST.op_Colon_Equals globals uu____9306);
                                 (match () with
                                  | () ->
                                      let modul =
                                        let uu____9403 =
                                          FStar_Ident.lid_of_ids
                                            lid.FStar_Ident.ns
                                           in
                                        uu____9403.FStar_Ident.str  in
                                      ((let uu____9405 =
                                          get_exported_id_set env3 modul  in
                                        match uu____9405 with
                                        | FStar_Pervasives_Native.Some f ->
                                            let my_exported_ids =
                                              f Exported_id_term_type  in
                                            let uu____9438 =
                                              let uu____9439 =
                                                FStar_ST.op_Bang
                                                  my_exported_ids
                                                 in
                                              FStar_Util.set_add
                                                (lid.FStar_Ident.ident).FStar_Ident.idText
                                                uu____9439
                                               in
                                            FStar_ST.op_Colon_Equals
                                              my_exported_ids uu____9438
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
                let uu___213_9535 = env3  in
                let uu____9536 = FStar_ST.op_Bang globals  in
                {
                  curmodule = (uu___213_9535.curmodule);
                  curmonad = (uu___213_9535.curmonad);
                  modules = (uu___213_9535.modules);
                  scope_mods = uu____9536;
                  exported_ids = (uu___213_9535.exported_ids);
                  trans_exported_ids = (uu___213_9535.trans_exported_ids);
                  includes = (uu___213_9535.includes);
                  sigaccum = (uu___213_9535.sigaccum);
                  sigmap = (uu___213_9535.sigmap);
                  iface = (uu___213_9535.iface);
                  admitted_iface = (uu___213_9535.admitted_iface);
                  expect_typ = (uu___213_9535.expect_typ);
                  docs = (uu___213_9535.docs);
                  remaining_iface_decls =
                    (uu___213_9535.remaining_iface_decls);
                  syntax_only = (uu___213_9535.syntax_only);
                  ds_hooks = (uu___213_9535.ds_hooks);
                  dep_graph = (uu___213_9535.dep_graph)
                }  in
              env4))
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  -> fun se  -> push_sigelt' true env se 
let (push_sigelt_force : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  -> fun se  -> push_sigelt' false env se 
let (push_namespace : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun ns  ->
      let uu____9614 =
        let uu____9619 = resolve_module_name env ns false  in
        match uu____9619 with
        | FStar_Pervasives_Native.None  ->
            let modules = env.modules  in
            let uu____9633 =
              FStar_All.pipe_right modules
                (FStar_Util.for_some
                   (fun uu____9649  ->
                      match uu____9649 with
                      | (m,uu____9655) ->
                          let uu____9656 =
                            let uu____9657 = FStar_Ident.text_of_lid m  in
                            Prims.strcat uu____9657 "."  in
                          let uu____9658 =
                            let uu____9659 = FStar_Ident.text_of_lid ns  in
                            Prims.strcat uu____9659 "."  in
                          FStar_Util.starts_with uu____9656 uu____9658))
               in
            if uu____9633
            then (ns, Open_namespace)
            else
              (let uu____9665 =
                 let uu____9670 =
                   let uu____9671 = FStar_Ident.text_of_lid ns  in
                   FStar_Util.format1 "Namespace %s cannot be found"
                     uu____9671
                    in
                 (FStar_Errors.Fatal_NameSpaceNotFound, uu____9670)  in
               let uu____9672 = FStar_Ident.range_of_lid ns  in
               FStar_Errors.raise_error uu____9665 uu____9672)
        | FStar_Pervasives_Native.Some ns' ->
            (fail_if_curmodule env ns ns'; (ns', Open_module))
         in
      match uu____9614 with
      | (ns',kd) ->
          ((env.ds_hooks).ds_push_open_hook env (ns', kd);
           push_scope_mod env (Open_module_or_namespace (ns', kd)))
  
let (push_include : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun ns  ->
      let ns0 = ns  in
      let uu____9693 = resolve_module_name env ns false  in
      match uu____9693 with
      | FStar_Pervasives_Native.Some ns1 ->
          ((env.ds_hooks).ds_push_include_hook env ns1;
           fail_if_curmodule env ns0 ns1;
           (let env1 =
              push_scope_mod env
                (Open_module_or_namespace (ns1, Open_module))
               in
            let curmod =
              let uu____9701 = current_module env1  in
              uu____9701.FStar_Ident.str  in
            (let uu____9703 = FStar_Util.smap_try_find env1.includes curmod
                in
             match uu____9703 with
             | FStar_Pervasives_Native.None  -> ()
             | FStar_Pervasives_Native.Some incl ->
                 let uu____9727 =
                   let uu____9730 = FStar_ST.op_Bang incl  in ns1 ::
                     uu____9730
                    in
                 FStar_ST.op_Colon_Equals incl uu____9727);
            (match () with
             | () ->
                 let uu____9823 =
                   get_trans_exported_id_set env1 ns1.FStar_Ident.str  in
                 (match uu____9823 with
                  | FStar_Pervasives_Native.Some ns_trans_exports ->
                      ((let uu____9843 =
                          let uu____9938 = get_exported_id_set env1 curmod
                             in
                          let uu____9984 =
                            get_trans_exported_id_set env1 curmod  in
                          (uu____9938, uu____9984)  in
                        match uu____9843 with
                        | (FStar_Pervasives_Native.Some
                           cur_exports,FStar_Pervasives_Native.Some
                           cur_trans_exports) ->
                            let update_exports k =
                              let ns_ex =
                                let uu____10391 = ns_trans_exports k  in
                                FStar_ST.op_Bang uu____10391  in
                              let ex = cur_exports k  in
                              (let uu____10565 =
                                 let uu____10568 = FStar_ST.op_Bang ex  in
                                 FStar_Util.set_difference uu____10568 ns_ex
                                  in
                               FStar_ST.op_Colon_Equals ex uu____10565);
                              (match () with
                               | () ->
                                   let trans_ex = cur_trans_exports k  in
                                   let uu____10760 =
                                     let uu____10763 =
                                       FStar_ST.op_Bang trans_ex  in
                                     FStar_Util.set_union uu____10763 ns_ex
                                      in
                                   FStar_ST.op_Colon_Equals trans_ex
                                     uu____10760)
                               in
                            FStar_List.iter update_exports
                              all_exported_id_kinds
                        | uu____10892 -> ());
                       (match () with | () -> env1))
                  | FStar_Pervasives_Native.None  ->
                      let uu____10992 =
                        let uu____10997 =
                          FStar_Util.format1
                            "include: Module %s was not prepared"
                            ns1.FStar_Ident.str
                           in
                        (FStar_Errors.Fatal_IncludeModuleNotPrepared,
                          uu____10997)
                         in
                      let uu____10998 = FStar_Ident.range_of_lid ns1  in
                      FStar_Errors.raise_error uu____10992 uu____10998))))
      | uu____10999 ->
          let uu____11002 =
            let uu____11007 =
              FStar_Util.format1 "include: Module %s cannot be found"
                ns.FStar_Ident.str
               in
            (FStar_Errors.Fatal_ModuleNotFound, uu____11007)  in
          let uu____11008 = FStar_Ident.range_of_lid ns  in
          FStar_Errors.raise_error uu____11002 uu____11008
  
let (push_module_abbrev :
  env -> FStar_Ident.ident -> FStar_Ident.lident -> env) =
  fun env  ->
    fun x  ->
      fun l  ->
        let uu____11024 = module_is_defined env l  in
        if uu____11024
        then
          (fail_if_curmodule env l l;
           (env.ds_hooks).ds_push_module_abbrev_hook env x l;
           push_scope_mod env (Module_abbrev (x, l)))
        else
          (let uu____11028 =
             let uu____11033 =
               let uu____11034 = FStar_Ident.text_of_lid l  in
               FStar_Util.format1 "Module %s cannot be found" uu____11034  in
             (FStar_Errors.Fatal_ModuleNotFound, uu____11033)  in
           let uu____11035 = FStar_Ident.range_of_lid l  in
           FStar_Errors.raise_error uu____11028 uu____11035)
  
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
            ((let uu____11057 =
                FStar_Util.smap_try_find env.docs l.FStar_Ident.str  in
              match uu____11057 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some old_doc ->
                  let uu____11061 = FStar_Ident.range_of_lid l  in
                  let uu____11062 =
                    let uu____11067 =
                      let uu____11068 = FStar_Ident.string_of_lid l  in
                      let uu____11069 =
                        FStar_Parser_AST.string_of_fsdoc old_doc  in
                      let uu____11070 = FStar_Parser_AST.string_of_fsdoc doc1
                         in
                      FStar_Util.format3
                        "Overwriting doc of %s; old doc was [%s]; new doc are [%s]"
                        uu____11068 uu____11069 uu____11070
                       in
                    (FStar_Errors.Warning_DocOverwrite, uu____11067)  in
                  FStar_Errors.log_issue uu____11061 uu____11062);
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
                      let uu____11112 =
                        FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption)
                         in
                      Prims.op_Negation uu____11112 ->
                      let uu____11115 =
                        FStar_Util.smap_try_find (sigmap env)
                          l.FStar_Ident.str
                         in
                      (match uu____11115 with
                       | FStar_Pervasives_Native.Some
                           ({
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_let uu____11128;
                              FStar_Syntax_Syntax.sigrng = uu____11129;
                              FStar_Syntax_Syntax.sigquals = uu____11130;
                              FStar_Syntax_Syntax.sigmeta = uu____11131;
                              FStar_Syntax_Syntax.sigattrs = uu____11132;_},uu____11133)
                           -> lids
                       | FStar_Pervasives_Native.Some
                           ({
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_inductive_typ
                                uu____11148;
                              FStar_Syntax_Syntax.sigrng = uu____11149;
                              FStar_Syntax_Syntax.sigquals = uu____11150;
                              FStar_Syntax_Syntax.sigmeta = uu____11151;
                              FStar_Syntax_Syntax.sigattrs = uu____11152;_},uu____11153)
                           -> lids
                       | uu____11178 ->
                           ((let uu____11186 =
                               let uu____11187 = FStar_Options.interactive ()
                                  in
                               Prims.op_Negation uu____11187  in
                             if uu____11186
                             then
                               let uu____11188 = FStar_Ident.range_of_lid l
                                  in
                               let uu____11189 =
                                 let uu____11194 =
                                   let uu____11195 =
                                     FStar_Ident.string_of_lid l  in
                                   FStar_Util.format1
                                     "Admitting %s without a definition"
                                     uu____11195
                                    in
                                 (FStar_Errors.Warning_AdmitWithoutDefinition,
                                   uu____11194)
                                  in
                               FStar_Errors.log_issue uu____11188 uu____11189
                             else ());
                            (let quals = FStar_Syntax_Syntax.Assumption ::
                               (se.FStar_Syntax_Syntax.sigquals)  in
                             FStar_Util.smap_add (sigmap env)
                               l.FStar_Ident.str
                               ((let uu___214_11206 = se  in
                                 {
                                   FStar_Syntax_Syntax.sigel =
                                     (uu___214_11206.FStar_Syntax_Syntax.sigel);
                                   FStar_Syntax_Syntax.sigrng =
                                     (uu___214_11206.FStar_Syntax_Syntax.sigrng);
                                   FStar_Syntax_Syntax.sigquals = quals;
                                   FStar_Syntax_Syntax.sigmeta =
                                     (uu___214_11206.FStar_Syntax_Syntax.sigmeta);
                                   FStar_Syntax_Syntax.sigattrs =
                                     (uu___214_11206.FStar_Syntax_Syntax.sigattrs)
                                 }), false);
                             l
                             ::
                             lids)))
                  | uu____11207 -> lids) [])
         in
      let uu___215_11208 = m  in
      let uu____11209 =
        FStar_All.pipe_right m.FStar_Syntax_Syntax.declarations
          (FStar_List.map
             (fun s  ->
                match s.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_declare_typ
                    (lid,uu____11219,uu____11220) when
                    FStar_List.existsb
                      (fun l  -> FStar_Ident.lid_equals l lid)
                      admitted_sig_lids
                    ->
                    let uu___216_11223 = s  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___216_11223.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___216_11223.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals =
                        (FStar_Syntax_Syntax.Assumption ::
                        (s.FStar_Syntax_Syntax.sigquals));
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___216_11223.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___216_11223.FStar_Syntax_Syntax.sigattrs)
                    }
                | uu____11224 -> s))
         in
      {
        FStar_Syntax_Syntax.name = (uu___215_11208.FStar_Syntax_Syntax.name);
        FStar_Syntax_Syntax.declarations = uu____11209;
        FStar_Syntax_Syntax.exports =
          (uu___215_11208.FStar_Syntax_Syntax.exports);
        FStar_Syntax_Syntax.is_interface =
          (uu___215_11208.FStar_Syntax_Syntax.is_interface)
      }
  
let (finish : env -> FStar_Syntax_Syntax.modul -> env) =
  fun env  ->
    fun modul  ->
      FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations
        (FStar_List.iter
           (fun se  ->
              let quals = se.FStar_Syntax_Syntax.sigquals  in
              match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_bundle (ses,uu____11247) ->
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
                                (lid,uu____11267,uu____11268,uu____11269,uu____11270,uu____11271)
                                ->
                                FStar_Util.smap_remove (sigmap env)
                                  lid.FStar_Ident.str
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (lid,univ_names,binders,typ,uu____11284,uu____11285)
                                ->
                                (FStar_Util.smap_remove (sigmap env)
                                   lid.FStar_Ident.str;
                                 if
                                   Prims.op_Negation
                                     (FStar_List.contains
                                        FStar_Syntax_Syntax.Private quals)
                                 then
                                   (let sigel =
                                      let uu____11300 =
                                        let uu____11307 =
                                          let uu____11308 =
                                            FStar_Ident.range_of_lid lid  in
                                          let uu____11309 =
                                            let uu____11316 =
                                              let uu____11317 =
                                                let uu____11332 =
                                                  FStar_Syntax_Syntax.mk_Total
                                                    typ
                                                   in
                                                (binders, uu____11332)  in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____11317
                                               in
                                            FStar_Syntax_Syntax.mk
                                              uu____11316
                                             in
                                          uu____11309
                                            FStar_Pervasives_Native.None
                                            uu____11308
                                           in
                                        (lid, univ_names, uu____11307)  in
                                      FStar_Syntax_Syntax.Sig_declare_typ
                                        uu____11300
                                       in
                                    let se2 =
                                      let uu___217_11349 = se1  in
                                      {
                                        FStar_Syntax_Syntax.sigel = sigel;
                                        FStar_Syntax_Syntax.sigrng =
                                          (uu___217_11349.FStar_Syntax_Syntax.sigrng);
                                        FStar_Syntax_Syntax.sigquals =
                                          (FStar_Syntax_Syntax.Assumption ::
                                          quals);
                                        FStar_Syntax_Syntax.sigmeta =
                                          (uu___217_11349.FStar_Syntax_Syntax.sigmeta);
                                        FStar_Syntax_Syntax.sigattrs =
                                          (uu___217_11349.FStar_Syntax_Syntax.sigattrs)
                                      }  in
                                    FStar_Util.smap_add (sigmap env)
                                      lid.FStar_Ident.str (se2, false))
                                 else ())
                            | uu____11355 -> ()))
                  else ()
              | FStar_Syntax_Syntax.Sig_declare_typ
                  (lid,uu____11358,uu____11359) ->
                  if FStar_List.contains FStar_Syntax_Syntax.Private quals
                  then
                    FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str
                  else ()
              | FStar_Syntax_Syntax.Sig_let ((uu____11365,lbs),uu____11367)
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
                             let uu____11382 =
                               let uu____11383 =
                                 let uu____11384 =
                                   let uu____11387 =
                                     FStar_Util.right
                                       lb.FStar_Syntax_Syntax.lbname
                                      in
                                   uu____11387.FStar_Syntax_Syntax.fv_name
                                    in
                                 uu____11384.FStar_Syntax_Syntax.v  in
                               uu____11383.FStar_Ident.str  in
                             FStar_Util.smap_remove (sigmap env) uu____11382))
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
                               let uu____11401 =
                                 let uu____11404 =
                                   FStar_Util.right
                                     lb.FStar_Syntax_Syntax.lbname
                                    in
                                 uu____11404.FStar_Syntax_Syntax.fv_name  in
                               uu____11401.FStar_Syntax_Syntax.v  in
                             let quals1 = FStar_Syntax_Syntax.Assumption ::
                               quals  in
                             let decl =
                               let uu___218_11409 = se  in
                               {
                                 FStar_Syntax_Syntax.sigel =
                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                      (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                        (lb.FStar_Syntax_Syntax.lbtyp)));
                                 FStar_Syntax_Syntax.sigrng =
                                   (uu___218_11409.FStar_Syntax_Syntax.sigrng);
                                 FStar_Syntax_Syntax.sigquals = quals1;
                                 FStar_Syntax_Syntax.sigmeta =
                                   (uu___218_11409.FStar_Syntax_Syntax.sigmeta);
                                 FStar_Syntax_Syntax.sigattrs =
                                   (uu___218_11409.FStar_Syntax_Syntax.sigattrs)
                               }  in
                             FStar_Util.smap_add (sigmap env)
                               lid.FStar_Ident.str (decl, false)))
                   else ())
              | uu____11415 -> ()));
      (let curmod =
         let uu____11417 = current_module env  in uu____11417.FStar_Ident.str
          in
       (let uu____11419 =
          let uu____11514 = get_exported_id_set env curmod  in
          let uu____11560 = get_trans_exported_id_set env curmod  in
          (uu____11514, uu____11560)  in
        match uu____11419 with
        | (FStar_Pervasives_Native.Some cur_ex,FStar_Pervasives_Native.Some
           cur_trans_ex) ->
            let update_exports eikind =
              let cur_ex_set =
                let uu____11969 = cur_ex eikind  in
                FStar_ST.op_Bang uu____11969  in
              let cur_trans_ex_set_ref = cur_trans_ex eikind  in
              let uu____12156 =
                let uu____12159 = FStar_ST.op_Bang cur_trans_ex_set_ref  in
                FStar_Util.set_union cur_ex_set uu____12159  in
              FStar_ST.op_Colon_Equals cur_trans_ex_set_ref uu____12156  in
            FStar_List.iter update_exports all_exported_id_kinds
        | uu____12288 -> ());
       (match () with
        | () ->
            (filter_record_cache ();
             (match () with
              | () ->
                  let uu___219_12384 = env  in
                  {
                    curmodule = FStar_Pervasives_Native.None;
                    curmonad = (uu___219_12384.curmonad);
                    modules = (((modul.FStar_Syntax_Syntax.name), modul) ::
                      (env.modules));
                    scope_mods = [];
                    exported_ids = (uu___219_12384.exported_ids);
                    trans_exported_ids = (uu___219_12384.trans_exported_ids);
                    includes = (uu___219_12384.includes);
                    sigaccum = [];
                    sigmap = (uu___219_12384.sigmap);
                    iface = (uu___219_12384.iface);
                    admitted_iface = (uu___219_12384.admitted_iface);
                    expect_typ = (uu___219_12384.expect_typ);
                    docs = (uu___219_12384.docs);
                    remaining_iface_decls =
                      (uu___219_12384.remaining_iface_decls);
                    syntax_only = (uu___219_12384.syntax_only);
                    ds_hooks = (uu___219_12384.ds_hooks);
                    dep_graph = (uu___219_12384.dep_graph)
                  }))))
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push : env -> env) =
  fun env  ->
    FStar_Util.atomically
      (fun uu____12420  ->
         push_record_cache ();
         (let uu____12423 =
            let uu____12426 = FStar_ST.op_Bang stack  in env :: uu____12426
             in
          FStar_ST.op_Colon_Equals stack uu____12423);
         (let uu___220_12475 = env  in
          let uu____12476 = FStar_Util.smap_copy env.exported_ids  in
          let uu____12481 = FStar_Util.smap_copy env.trans_exported_ids  in
          let uu____12486 = FStar_Util.smap_copy env.includes  in
          let uu____12497 = FStar_Util.smap_copy env.sigmap  in
          let uu____12508 = FStar_Util.smap_copy env.docs  in
          {
            curmodule = (uu___220_12475.curmodule);
            curmonad = (uu___220_12475.curmonad);
            modules = (uu___220_12475.modules);
            scope_mods = (uu___220_12475.scope_mods);
            exported_ids = uu____12476;
            trans_exported_ids = uu____12481;
            includes = uu____12486;
            sigaccum = (uu___220_12475.sigaccum);
            sigmap = uu____12497;
            iface = (uu___220_12475.iface);
            admitted_iface = (uu___220_12475.admitted_iface);
            expect_typ = (uu___220_12475.expect_typ);
            docs = uu____12508;
            remaining_iface_decls = (uu___220_12475.remaining_iface_decls);
            syntax_only = (uu___220_12475.syntax_only);
            ds_hooks = (uu___220_12475.ds_hooks);
            dep_graph = (uu___220_12475.dep_graph)
          }))
  
let (pop : unit -> env) =
  fun uu____12515  ->
    FStar_Util.atomically
      (fun uu____12522  ->
         let uu____12523 = FStar_ST.op_Bang stack  in
         match uu____12523 with
         | env::tl1 ->
             (pop_record_cache (); FStar_ST.op_Colon_Equals stack tl1; env)
         | uu____12578 -> failwith "Impossible: Too many pops")
  
let (snapshot : env -> (Prims.int,env) FStar_Pervasives_Native.tuple2) =
  fun env  -> FStar_Common.snapshot push stack env 
let (rollback : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth  -> FStar_Common.rollback pop stack depth 
let (export_interface : FStar_Ident.lident -> env -> env) =
  fun m  ->
    fun env  ->
      let sigelt_in_m se =
        match FStar_Syntax_Util.lids_of_sigelt se with
        | l::uu____12616 -> l.FStar_Ident.nsstr = m.FStar_Ident.str
        | uu____12619 -> false  in
      let sm = sigmap env  in
      let env1 = pop ()  in
      let keys = FStar_Util.smap_keys sm  in
      let sm' = sigmap env1  in
      FStar_All.pipe_right keys
        (FStar_List.iter
           (fun k  ->
              let uu____12653 = FStar_Util.smap_try_find sm' k  in
              match uu____12653 with
              | FStar_Pervasives_Native.Some (se,true ) when sigelt_in_m se
                  ->
                  (FStar_Util.smap_remove sm' k;
                   (let se1 =
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t) ->
                          let uu___221_12678 = se  in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (uu___221_12678.FStar_Syntax_Syntax.sigel);
                            FStar_Syntax_Syntax.sigrng =
                              (uu___221_12678.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (FStar_Syntax_Syntax.Assumption ::
                              (se.FStar_Syntax_Syntax.sigquals));
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___221_12678.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___221_12678.FStar_Syntax_Syntax.sigattrs)
                          }
                      | uu____12679 -> se  in
                    FStar_Util.smap_add sm' k (se1, false)))
              | uu____12684 -> ()));
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
      let uu____12707 = finish env modul1  in (uu____12707, modul1)
  
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
      let uu____12795 =
        let uu____12798 = e Exported_id_term_type  in
        FStar_ST.op_Bang uu____12798  in
      FStar_Util.set_elements uu____12795  in
    let fields =
      let uu____12912 =
        let uu____12915 = e Exported_id_field  in
        FStar_ST.op_Bang uu____12915  in
      FStar_Util.set_elements uu____12912  in
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
          let uu____13066 =
            FStar_Util.as_set e1.exported_id_terms FStar_Util.compare  in
          FStar_Util.mk_ref uu____13066  in
        let fields =
          let uu____13076 =
            FStar_Util.as_set e1.exported_id_fields FStar_Util.compare  in
          FStar_Util.mk_ref uu____13076  in
        (fun uu___195_13081  ->
           match uu___195_13081 with
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
  'Auu____13212 .
    'Auu____13212 Prims.list FStar_Pervasives_Native.option ->
      'Auu____13212 Prims.list FStar_ST.ref
  =
  fun uu___196_13225  ->
    match uu___196_13225 with
    | FStar_Pervasives_Native.None  -> FStar_Util.mk_ref []
    | FStar_Pervasives_Native.Some l -> FStar_Util.mk_ref l
  
let (inclusion_info : env -> FStar_Ident.lident -> module_inclusion_info) =
  fun env  ->
    fun l  ->
      let mname = FStar_Ident.string_of_lid l  in
      let as_ids_opt m =
        let uu____13266 = FStar_Util.smap_try_find m mname  in
        FStar_Util.map_opt uu____13266 as_exported_ids  in
      let uu____13272 = as_ids_opt env.exported_ids  in
      let uu____13275 = as_ids_opt env.trans_exported_ids  in
      let uu____13278 =
        let uu____13283 = FStar_Util.smap_try_find env.includes mname  in
        FStar_Util.map_opt uu____13283 (fun r  -> FStar_ST.op_Bang r)  in
      {
        mii_exported_ids = uu____13272;
        mii_trans_exported_ids = uu____13275;
        mii_includes = uu____13278
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
                let uu____13398 = FStar_Ident.text_of_lid mname  in
                FStar_Util.strcat uu____13398 ".fst"  in
              let auto_open =
                FStar_Parser_Dep.hard_coded_dependencies filename  in
              let auto_open1 =
                let convert_kind uu___197_13418 =
                  match uu___197_13418 with
                  | FStar_Parser_Dep.Open_namespace  -> Open_namespace
                  | FStar_Parser_Dep.Open_module  -> Open_module  in
                FStar_List.map
                  (fun uu____13430  ->
                     match uu____13430 with
                     | (lid,kind) -> (lid, (convert_kind kind))) auto_open
                 in
              let namespace_of_module =
                if
                  (FStar_List.length mname.FStar_Ident.ns) >
                    (Prims.parse_int "0")
                then
                  let uu____13454 =
                    let uu____13459 =
                      FStar_Ident.lid_of_ids mname.FStar_Ident.ns  in
                    (uu____13459, Open_namespace)  in
                  [uu____13454]
                else []  in
              let auto_open2 =
                FStar_List.append namespace_of_module
                  (FStar_List.rev auto_open1)
                 in
              (let uu____13489 = as_exported_id_set mii.mii_exported_ids  in
               FStar_Util.smap_add env1.exported_ids mname.FStar_Ident.str
                 uu____13489);
              (match () with
               | () ->
                   ((let uu____13516 =
                       as_exported_id_set mii.mii_trans_exported_ids  in
                     FStar_Util.smap_add env1.trans_exported_ids
                       mname.FStar_Ident.str uu____13516);
                    (match () with
                     | () ->
                         ((let uu____13543 = as_includes mii.mii_includes  in
                           FStar_Util.smap_add env1.includes
                             mname.FStar_Ident.str uu____13543);
                          (match () with
                           | () ->
                               let env' =
                                 let uu___222_13575 = env1  in
                                 let uu____13576 =
                                   FStar_List.map
                                     (fun x  -> Open_module_or_namespace x)
                                     auto_open2
                                    in
                                 {
                                   curmodule =
                                     (FStar_Pervasives_Native.Some mname);
                                   curmonad = (uu___222_13575.curmonad);
                                   modules = (uu___222_13575.modules);
                                   scope_mods = uu____13576;
                                   exported_ids =
                                     (uu___222_13575.exported_ids);
                                   trans_exported_ids =
                                     (uu___222_13575.trans_exported_ids);
                                   includes = (uu___222_13575.includes);
                                   sigaccum = (uu___222_13575.sigaccum);
                                   sigmap = (env1.sigmap);
                                   iface = intf;
                                   admitted_iface = admitted;
                                   expect_typ = (uu___222_13575.expect_typ);
                                   docs = (uu___222_13575.docs);
                                   remaining_iface_decls =
                                     (uu___222_13575.remaining_iface_decls);
                                   syntax_only = (uu___222_13575.syntax_only);
                                   ds_hooks = (uu___222_13575.ds_hooks);
                                   dep_graph = (uu___222_13575.dep_graph)
                                 }  in
                               (FStar_List.iter
                                  (fun op  ->
                                     (env1.ds_hooks).ds_push_open_hook env'
                                       op) (FStar_List.rev auto_open2);
                                env'))))))
               in
            let uu____13588 =
              FStar_All.pipe_right env.modules
                (FStar_Util.find_opt
                   (fun uu____13614  ->
                      match uu____13614 with
                      | (l,uu____13620) -> FStar_Ident.lid_equals l mname))
               in
            match uu____13588 with
            | FStar_Pervasives_Native.None  ->
                let uu____13629 = prep env  in (uu____13629, false)
            | FStar_Pervasives_Native.Some (uu____13630,m) ->
                ((let uu____13637 =
                    (let uu____13640 = FStar_Options.interactive ()  in
                     Prims.op_Negation uu____13640) &&
                      ((Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)
                         || intf)
                     in
                  if uu____13637
                  then
                    let uu____13641 =
                      let uu____13646 =
                        FStar_Util.format1
                          "Duplicate module or interface name: %s"
                          mname.FStar_Ident.str
                         in
                      (FStar_Errors.Fatal_DuplicateModuleOrInterface,
                        uu____13646)
                       in
                    let uu____13647 = FStar_Ident.range_of_lid mname  in
                    FStar_Errors.raise_error uu____13641 uu____13647
                  else ());
                 (let uu____13649 =
                    let uu____13650 = push env  in prep uu____13650  in
                  (uu____13649, true)))
  
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
          let uu___223_13662 = env  in
          {
            curmodule = (uu___223_13662.curmodule);
            curmonad = (FStar_Pervasives_Native.Some mname);
            modules = (uu___223_13662.modules);
            scope_mods = (uu___223_13662.scope_mods);
            exported_ids = (uu___223_13662.exported_ids);
            trans_exported_ids = (uu___223_13662.trans_exported_ids);
            includes = (uu___223_13662.includes);
            sigaccum = (uu___223_13662.sigaccum);
            sigmap = (uu___223_13662.sigmap);
            iface = (uu___223_13662.iface);
            admitted_iface = (uu___223_13662.admitted_iface);
            expect_typ = (uu___223_13662.expect_typ);
            docs = (uu___223_13662.docs);
            remaining_iface_decls = (uu___223_13662.remaining_iface_decls);
            syntax_only = (uu___223_13662.syntax_only);
            ds_hooks = (uu___223_13662.ds_hooks);
            dep_graph = (uu___223_13662.dep_graph)
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
        let uu____13696 = lookup1 lid  in
        match uu____13696 with
        | FStar_Pervasives_Native.None  ->
            let opened_modules =
              FStar_List.map
                (fun uu____13709  ->
                   match uu____13709 with
                   | (lid1,uu____13715) -> FStar_Ident.text_of_lid lid1)
                env.modules
               in
            let msg =
              let uu____13717 = FStar_Ident.text_of_lid lid  in
              FStar_Util.format1 "Identifier not found: [%s]" uu____13717  in
            let msg1 =
              if
                (FStar_List.length lid.FStar_Ident.ns) =
                  (Prims.parse_int "0")
              then msg
              else
                (let modul =
                   let uu____13721 =
                     FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
                   let uu____13722 = FStar_Ident.range_of_lid lid  in
                   FStar_Ident.set_lid_range uu____13721 uu____13722  in
                 let uu____13723 = resolve_module_name env modul true  in
                 match uu____13723 with
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
            let uu____13732 = FStar_Ident.range_of_lid lid  in
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_IdentifierNotFound, msg1) uu____13732
        | FStar_Pervasives_Native.Some r -> r
  
let fail_or2 :
  'a .
    (FStar_Ident.ident -> 'a FStar_Pervasives_Native.option) ->
      FStar_Ident.ident -> 'a
  =
  fun lookup1  ->
    fun id1  ->
      let uu____13760 = lookup1 id1  in
      match uu____13760 with
      | FStar_Pervasives_Native.None  ->
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_IdentifierNotFound,
              (Prims.strcat "Identifier not found ["
                 (Prims.strcat id1.FStar_Ident.idText "]")))
            id1.FStar_Ident.idRange
      | FStar_Pervasives_Native.Some r -> r
  