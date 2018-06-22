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
  ds_hooks: dsenv_hooks }
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
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;_}
        -> __fname__curmodule
  
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
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;_}
        -> __fname__curmonad
  
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
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;_}
        -> __fname__modules
  
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
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;_}
        -> __fname__scope_mods
  
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
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;_}
        -> __fname__exported_ids
  
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
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;_}
        -> __fname__trans_exported_ids
  
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
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;_}
        -> __fname__includes
  
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
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;_}
        -> __fname__sigaccum
  
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
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;_}
        -> __fname__sigmap
  
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
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;_}
        -> __fname__iface
  
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
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;_}
        -> __fname__admitted_iface
  
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
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;_}
        -> __fname__expect_typ
  
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
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;_}
        -> __fname__docs
  
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
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;_}
        -> __fname__remaining_iface_decls
  
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
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;_}
        -> __fname__syntax_only
  
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
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;_}
        -> __fname__ds_hooks
  
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
    ds_push_open_hook = (fun uu____1725  -> fun uu____1726  -> ());
    ds_push_include_hook = (fun uu____1729  -> fun uu____1730  -> ());
    ds_push_module_abbrev_hook =
      (fun uu____1734  -> fun uu____1735  -> fun uu____1736  -> ())
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
    match projectee with | Term_name _0 -> true | uu____1773 -> false
  
let (__proj__Term_name__item___0 :
  foundname ->
    (FStar_Syntax_Syntax.typ,Prims.bool,FStar_Syntax_Syntax.attribute
                                          Prims.list)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Term_name _0 -> _0 
let (uu___is_Eff_name : foundname -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eff_name _0 -> true | uu____1815 -> false
  
let (__proj__Eff_name__item___0 :
  foundname ->
    (FStar_Syntax_Syntax.sigelt,FStar_Ident.lident)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Eff_name _0 -> _0 
let (set_iface : env -> Prims.bool -> env) =
  fun env  ->
    fun b  ->
      let uu___194_1845 = env  in
      {
        curmodule = (uu___194_1845.curmodule);
        curmonad = (uu___194_1845.curmonad);
        modules = (uu___194_1845.modules);
        scope_mods = (uu___194_1845.scope_mods);
        exported_ids = (uu___194_1845.exported_ids);
        trans_exported_ids = (uu___194_1845.trans_exported_ids);
        includes = (uu___194_1845.includes);
        sigaccum = (uu___194_1845.sigaccum);
        sigmap = (uu___194_1845.sigmap);
        iface = b;
        admitted_iface = (uu___194_1845.admitted_iface);
        expect_typ = (uu___194_1845.expect_typ);
        docs = (uu___194_1845.docs);
        remaining_iface_decls = (uu___194_1845.remaining_iface_decls);
        syntax_only = (uu___194_1845.syntax_only);
        ds_hooks = (uu___194_1845.ds_hooks)
      }
  
let (iface : env -> Prims.bool) = fun e  -> e.iface 
let (set_admitted_iface : env -> Prims.bool -> env) =
  fun e  ->
    fun b  ->
      let uu___195_1861 = e  in
      {
        curmodule = (uu___195_1861.curmodule);
        curmonad = (uu___195_1861.curmonad);
        modules = (uu___195_1861.modules);
        scope_mods = (uu___195_1861.scope_mods);
        exported_ids = (uu___195_1861.exported_ids);
        trans_exported_ids = (uu___195_1861.trans_exported_ids);
        includes = (uu___195_1861.includes);
        sigaccum = (uu___195_1861.sigaccum);
        sigmap = (uu___195_1861.sigmap);
        iface = (uu___195_1861.iface);
        admitted_iface = b;
        expect_typ = (uu___195_1861.expect_typ);
        docs = (uu___195_1861.docs);
        remaining_iface_decls = (uu___195_1861.remaining_iface_decls);
        syntax_only = (uu___195_1861.syntax_only);
        ds_hooks = (uu___195_1861.ds_hooks)
      }
  
let (admitted_iface : env -> Prims.bool) = fun e  -> e.admitted_iface 
let (set_expect_typ : env -> Prims.bool -> env) =
  fun e  ->
    fun b  ->
      let uu___196_1877 = e  in
      {
        curmodule = (uu___196_1877.curmodule);
        curmonad = (uu___196_1877.curmonad);
        modules = (uu___196_1877.modules);
        scope_mods = (uu___196_1877.scope_mods);
        exported_ids = (uu___196_1877.exported_ids);
        trans_exported_ids = (uu___196_1877.trans_exported_ids);
        includes = (uu___196_1877.includes);
        sigaccum = (uu___196_1877.sigaccum);
        sigmap = (uu___196_1877.sigmap);
        iface = (uu___196_1877.iface);
        admitted_iface = (uu___196_1877.admitted_iface);
        expect_typ = b;
        docs = (uu___196_1877.docs);
        remaining_iface_decls = (uu___196_1877.remaining_iface_decls);
        syntax_only = (uu___196_1877.syntax_only);
        ds_hooks = (uu___196_1877.ds_hooks)
      }
  
let (expect_typ : env -> Prims.bool) = fun e  -> e.expect_typ 
let (all_exported_id_kinds : exported_id_kind Prims.list) =
  [Exported_id_field; Exported_id_term_type] 
let (transitive_exported_ids :
  env -> FStar_Ident.lident -> Prims.string Prims.list) =
  fun env  ->
    fun lid  ->
      let module_name = FStar_Ident.string_of_lid lid  in
      let uu____1898 =
        FStar_Util.smap_try_find env.trans_exported_ids module_name  in
      match uu____1898 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some exported_id_set ->
          let uu____1909 =
            let uu____1912 = exported_id_set Exported_id_term_type  in
            FStar_ST.op_Bang uu____1912  in
          FStar_All.pipe_right uu____1909 FStar_Util.set_elements
  
let (open_modules :
  env ->
    (FStar_Ident.lident,FStar_Syntax_Syntax.modul)
      FStar_Pervasives_Native.tuple2 Prims.list)
  = fun e  -> e.modules 
let (open_modules_and_namespaces : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    FStar_List.filter_map
      (fun uu___161_2056  ->
         match uu___161_2056 with
         | Open_module_or_namespace (lid,_info) ->
             FStar_Pervasives_Native.Some lid
         | uu____2061 -> FStar_Pervasives_Native.None) env.scope_mods
  
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun e  ->
    fun l  ->
      let uu___197_2072 = e  in
      {
        curmodule = (FStar_Pervasives_Native.Some l);
        curmonad = (uu___197_2072.curmonad);
        modules = (uu___197_2072.modules);
        scope_mods = (uu___197_2072.scope_mods);
        exported_ids = (uu___197_2072.exported_ids);
        trans_exported_ids = (uu___197_2072.trans_exported_ids);
        includes = (uu___197_2072.includes);
        sigaccum = (uu___197_2072.sigaccum);
        sigmap = (uu___197_2072.sigmap);
        iface = (uu___197_2072.iface);
        admitted_iface = (uu___197_2072.admitted_iface);
        expect_typ = (uu___197_2072.expect_typ);
        docs = (uu___197_2072.docs);
        remaining_iface_decls = (uu___197_2072.remaining_iface_decls);
        syntax_only = (uu___197_2072.syntax_only);
        ds_hooks = (uu___197_2072.ds_hooks)
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
      let uu____2093 =
        FStar_All.pipe_right env.remaining_iface_decls
          (FStar_List.tryFind
             (fun uu____2127  ->
                match uu____2127 with
                | (m,uu____2135) -> FStar_Ident.lid_equals l m))
         in
      match uu____2093 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (uu____2152,decls) ->
          FStar_Pervasives_Native.Some decls
  
let (set_iface_decls :
  env -> FStar_Ident.lident -> FStar_Parser_AST.decl Prims.list -> env) =
  fun env  ->
    fun l  ->
      fun ds  ->
        let uu____2185 =
          FStar_List.partition
            (fun uu____2215  ->
               match uu____2215 with
               | (m,uu____2223) -> FStar_Ident.lid_equals l m)
            env.remaining_iface_decls
           in
        match uu____2185 with
        | (uu____2228,rest) ->
            let uu___198_2262 = env  in
            {
              curmodule = (uu___198_2262.curmodule);
              curmonad = (uu___198_2262.curmonad);
              modules = (uu___198_2262.modules);
              scope_mods = (uu___198_2262.scope_mods);
              exported_ids = (uu___198_2262.exported_ids);
              trans_exported_ids = (uu___198_2262.trans_exported_ids);
              includes = (uu___198_2262.includes);
              sigaccum = (uu___198_2262.sigaccum);
              sigmap = (uu___198_2262.sigmap);
              iface = (uu___198_2262.iface);
              admitted_iface = (uu___198_2262.admitted_iface);
              expect_typ = (uu___198_2262.expect_typ);
              docs = (uu___198_2262.docs);
              remaining_iface_decls = ((l, ds) :: rest);
              syntax_only = (uu___198_2262.syntax_only);
              ds_hooks = (uu___198_2262.ds_hooks)
            }
  
let (qual : FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident) =
  FStar_Syntax_Util.qual_id 
let (qualify : env -> FStar_Ident.ident -> FStar_Ident.lident) =
  fun env  ->
    fun id1  ->
      match env.curmonad with
      | FStar_Pervasives_Native.None  ->
          let uu____2289 = current_module env  in qual uu____2289 id1
      | FStar_Pervasives_Native.Some monad ->
          let uu____2291 =
            let uu____2292 = current_module env  in qual uu____2292 monad  in
          FStar_Syntax_Util.mk_field_projector_name_from_ident uu____2291 id1
  
let (syntax_only : env -> Prims.bool) = fun env  -> env.syntax_only 
let (set_syntax_only : env -> Prims.bool -> env) =
  fun env  ->
    fun b  ->
      let uu___199_2308 = env  in
      {
        curmodule = (uu___199_2308.curmodule);
        curmonad = (uu___199_2308.curmonad);
        modules = (uu___199_2308.modules);
        scope_mods = (uu___199_2308.scope_mods);
        exported_ids = (uu___199_2308.exported_ids);
        trans_exported_ids = (uu___199_2308.trans_exported_ids);
        includes = (uu___199_2308.includes);
        sigaccum = (uu___199_2308.sigaccum);
        sigmap = (uu___199_2308.sigmap);
        iface = (uu___199_2308.iface);
        admitted_iface = (uu___199_2308.admitted_iface);
        expect_typ = (uu___199_2308.expect_typ);
        docs = (uu___199_2308.docs);
        remaining_iface_decls = (uu___199_2308.remaining_iface_decls);
        syntax_only = b;
        ds_hooks = (uu___199_2308.ds_hooks)
      }
  
let (ds_hooks : env -> dsenv_hooks) = fun env  -> env.ds_hooks 
let (set_ds_hooks : env -> dsenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___200_2324 = env  in
      {
        curmodule = (uu___200_2324.curmodule);
        curmonad = (uu___200_2324.curmonad);
        modules = (uu___200_2324.modules);
        scope_mods = (uu___200_2324.scope_mods);
        exported_ids = (uu___200_2324.exported_ids);
        trans_exported_ids = (uu___200_2324.trans_exported_ids);
        includes = (uu___200_2324.includes);
        sigaccum = (uu___200_2324.sigaccum);
        sigmap = (uu___200_2324.sigmap);
        iface = (uu___200_2324.iface);
        admitted_iface = (uu___200_2324.admitted_iface);
        expect_typ = (uu___200_2324.expect_typ);
        docs = (uu___200_2324.docs);
        remaining_iface_decls = (uu___200_2324.remaining_iface_decls);
        syntax_only = (uu___200_2324.syntax_only);
        ds_hooks = hooks
      }
  
let new_sigmap : 'Auu____2329 . unit -> 'Auu____2329 FStar_Util.smap =
  fun uu____2336  -> FStar_Util.smap_create (Prims.parse_int "100") 
let (empty_env : unit -> env) =
  fun uu____2341  ->
    let uu____2342 = new_sigmap ()  in
    let uu____2347 = new_sigmap ()  in
    let uu____2352 = new_sigmap ()  in
    let uu____2363 = new_sigmap ()  in
    let uu____2374 = new_sigmap ()  in
    {
      curmodule = FStar_Pervasives_Native.None;
      curmonad = FStar_Pervasives_Native.None;
      modules = [];
      scope_mods = [];
      exported_ids = uu____2342;
      trans_exported_ids = uu____2347;
      includes = uu____2352;
      sigaccum = [];
      sigmap = uu____2363;
      iface = false;
      admitted_iface = false;
      expect_typ = false;
      docs = uu____2374;
      remaining_iface_decls = [];
      syntax_only = false;
      ds_hooks = default_ds_hooks
    }
  
let (sigmap :
  env ->
    (FStar_Syntax_Syntax.sigelt,Prims.bool) FStar_Pervasives_Native.tuple2
      FStar_Util.smap)
  = fun env  -> env.sigmap 
let (has_all_in_scope : env -> Prims.bool) =
  fun env  ->
    FStar_List.existsb
      (fun uu____2410  ->
         match uu____2410 with
         | (m,uu____2416) ->
             FStar_Ident.lid_equals m FStar_Parser_Const.all_lid) env.modules
  
let (set_bv_range :
  FStar_Syntax_Syntax.bv -> FStar_Range.range -> FStar_Syntax_Syntax.bv) =
  fun bv  ->
    fun r  ->
      let id1 =
        let uu___201_2428 = bv.FStar_Syntax_Syntax.ppname  in
        {
          FStar_Ident.idText = (uu___201_2428.FStar_Ident.idText);
          FStar_Ident.idRange = r
        }  in
      let uu___202_2429 = bv  in
      {
        FStar_Syntax_Syntax.ppname = id1;
        FStar_Syntax_Syntax.index = (uu___202_2429.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = (uu___202_2429.FStar_Syntax_Syntax.sort)
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
        (fun uu____2522  ->
           match uu____2522 with
           | (x,y,dd,dq) ->
               if id1.FStar_Ident.idText = x
               then
                 let uu____2545 =
                   let uu____2546 =
                     FStar_Ident.lid_of_path ["Prims"; y]
                       id1.FStar_Ident.idRange
                      in
                   FStar_Syntax_Syntax.fvar uu____2546 dd dq  in
                 FStar_Pervasives_Native.Some uu____2545
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
    match projectee with | Cont_ok _0 -> true | uu____2593 -> false
  
let __proj__Cont_ok__item___0 : 'a . 'a cont_t -> 'a =
  fun projectee  -> match projectee with | Cont_ok _0 -> _0 
let uu___is_Cont_fail : 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_fail  -> true | uu____2626 -> false
  
let uu___is_Cont_ignore : 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_ignore  -> true | uu____2643 -> false
  
let option_of_cont :
  'a .
    (unit -> 'a FStar_Pervasives_Native.option) ->
      'a cont_t -> 'a FStar_Pervasives_Native.option
  =
  fun k_ignore  ->
    fun uu___162_2671  ->
      match uu___162_2671 with
      | Cont_ok a -> FStar_Pervasives_Native.Some a
      | Cont_fail  -> FStar_Pervasives_Native.None
      | Cont_ignore  -> k_ignore ()
  
let find_in_record :
  'Auu____2689 .
    FStar_Ident.ident Prims.list ->
      FStar_Ident.ident ->
        record_or_dc ->
          (record_or_dc -> 'Auu____2689 cont_t) -> 'Auu____2689 cont_t
  =
  fun ns  ->
    fun id1  ->
      fun record  ->
        fun cont  ->
          let typename' =
            FStar_Ident.lid_of_ids
              (FStar_List.append ns [(record.typename).FStar_Ident.ident])
             in
          let uu____2726 = FStar_Ident.lid_equals typename' record.typename
             in
          if uu____2726
          then
            let fname =
              FStar_Ident.lid_of_ids
                (FStar_List.append (record.typename).FStar_Ident.ns [id1])
               in
            let find1 =
              FStar_Util.find_map record.fields
                (fun uu____2740  ->
                   match uu____2740 with
                   | (f,uu____2748) ->
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
  fun uu___163_2810  ->
    match uu___163_2810 with
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
              let rec aux uu___164_2881 =
                match uu___164_2881 with
                | [] -> find_in_module_default
                | modul::q ->
                    let mname = modul.FStar_Ident.str  in
                    let not_shadowed =
                      let uu____2892 = get_exported_id_set env mname  in
                      match uu____2892 with
                      | FStar_Pervasives_Native.None  -> true
                      | FStar_Pervasives_Native.Some mex ->
                          let mexports =
                            let uu____2917 = mex eikind  in
                            FStar_ST.op_Bang uu____2917  in
                          FStar_Util.set_mem idstr mexports
                       in
                    let mincludes =
                      let uu____3039 =
                        FStar_Util.smap_try_find env.includes mname  in
                      match uu____3039 with
                      | FStar_Pervasives_Native.None  -> []
                      | FStar_Pervasives_Native.Some minc ->
                          FStar_ST.op_Bang minc
                       in
                    let look_into =
                      if not_shadowed
                      then
                        let uu____3119 = qual modul id1  in
                        find_in_module uu____3119
                      else Cont_ignore  in
                    (match look_into with
                     | Cont_ignore  -> aux (FStar_List.append mincludes q)
                     | uu____3123 -> look_into)
                 in
              aux [ns]
  
let (is_exported_id_field : exported_id_kind -> Prims.bool) =
  fun uu___165_3130  ->
    match uu___165_3130 with
    | Exported_id_field  -> true
    | uu____3131 -> false
  
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
                  let check_local_binding_id uu___166_3252 =
                    match uu___166_3252 with
                    | (id',uu____3254,uu____3255) ->
                        id'.FStar_Ident.idText = id1.FStar_Ident.idText
                     in
                  let check_rec_binding_id uu___167_3261 =
                    match uu___167_3261 with
                    | (id',uu____3263,uu____3264) ->
                        id'.FStar_Ident.idText = id1.FStar_Ident.idText
                     in
                  let curmod_ns =
                    let uu____3268 = current_module env  in
                    FStar_Ident.ids_of_lid uu____3268  in
                  let proc uu___168_3276 =
                    match uu___168_3276 with
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
                        let uu____3284 = FStar_Ident.lid_of_ids curmod_ns  in
                        find_in_module_with_includes Exported_id_field
                          (fun lid  ->
                             let id2 = lid.FStar_Ident.ident  in
                             find_in_record lid.FStar_Ident.ns id2 r k_record)
                          Cont_ignore env uu____3284 id1
                    | uu____3289 -> Cont_ignore  in
                  let rec aux uu___169_3299 =
                    match uu___169_3299 with
                    | a::q ->
                        let uu____3308 = proc a  in
                        option_of_cont (fun uu____3312  -> aux q) uu____3308
                    | [] ->
                        let uu____3313 = lookup_default_id Cont_fail id1  in
                        option_of_cont
                          (fun uu____3317  -> FStar_Pervasives_Native.None)
                          uu____3313
                     in
                  aux env.scope_mods
  
let found_local_binding :
  'Auu____3326 'Auu____3327 .
    FStar_Range.range ->
      ('Auu____3326,FStar_Syntax_Syntax.bv,'Auu____3327)
        FStar_Pervasives_Native.tuple3 ->
        (FStar_Syntax_Syntax.term,'Auu____3327)
          FStar_Pervasives_Native.tuple2
  =
  fun r  ->
    fun uu____3347  ->
      match uu____3347 with
      | (id',x,mut) -> let uu____3357 = bv_to_name x r  in (uu____3357, mut)
  
let find_in_module :
  'Auu____3368 .
    env ->
      FStar_Ident.lident ->
        (FStar_Ident.lident ->
           (FStar_Syntax_Syntax.sigelt,Prims.bool)
             FStar_Pervasives_Native.tuple2 -> 'Auu____3368)
          -> 'Auu____3368 -> 'Auu____3368
  =
  fun env  ->
    fun lid  ->
      fun k_global_def  ->
        fun k_not_found  ->
          let uu____3407 =
            FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str  in
          match uu____3407 with
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
      let uu____3447 = unmangleOpName id1  in
      match uu____3447 with
      | FStar_Pervasives_Native.Some f -> FStar_Pervasives_Native.Some f
      | uu____3473 ->
          try_lookup_id'' env id1 Exported_id_term_type
            (fun r  ->
               let uu____3487 = found_local_binding id1.FStar_Ident.idRange r
                  in
               Cont_ok uu____3487) (fun uu____3497  -> Cont_fail)
            (fun uu____3503  -> Cont_ignore)
            (fun i  ->
               find_in_module env i
                 (fun uu____3518  -> fun uu____3519  -> Cont_fail)
                 Cont_ignore)
            (fun uu____3534  -> fun uu____3535  -> Cont_fail)
  
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
            | FStar_Pervasives_Native.Some uu____3614 ->
                let lid = qualify env id1  in
                let uu____3616 =
                  FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str
                   in
                (match uu____3616 with
                 | FStar_Pervasives_Native.Some r ->
                     let uu____3640 = k_global_def lid r  in
                     FStar_Pervasives_Native.Some uu____3640
                 | FStar_Pervasives_Native.None  ->
                     FStar_Pervasives_Native.None)
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             in
          match find_in_monad with
          | FStar_Pervasives_Native.Some v1 -> v1
          | FStar_Pervasives_Native.None  ->
              let lid =
                let uu____3663 = current_module env  in qual uu____3663 id1
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
        let rec aux uu___170_3726 =
          match uu___170_3726 with
          | [] ->
              let uu____3731 = module_is_defined env lid  in
              if uu____3731
              then FStar_Pervasives_Native.Some lid
              else FStar_Pervasives_Native.None
          | (Open_module_or_namespace (ns,Open_namespace ))::q when honor_ns
              ->
              let new_lid =
                let uu____3740 =
                  let uu____3741 = FStar_Ident.path_of_lid ns  in
                  let uu____3744 = FStar_Ident.path_of_lid lid  in
                  FStar_List.append uu____3741 uu____3744  in
                let uu____3747 = FStar_Ident.range_of_lid lid  in
                FStar_Ident.lid_of_path uu____3740 uu____3747  in
              let uu____3748 = module_is_defined env new_lid  in
              if uu____3748
              then FStar_Pervasives_Native.Some new_lid
              else aux q
          | (Module_abbrev (name,modul))::uu____3754 when
              (nslen = (Prims.parse_int "0")) &&
                (name.FStar_Ident.idText =
                   (lid.FStar_Ident.ident).FStar_Ident.idText)
              -> FStar_Pervasives_Native.Some modul
          | uu____3761::q -> aux q  in
        aux env.scope_mods
  
let (fail_if_curmodule :
  env -> FStar_Ident.lident -> FStar_Ident.lident -> unit) =
  fun env  ->
    fun ns_original  ->
      fun ns_resolved  ->
        let uu____3780 =
          let uu____3781 = current_module env  in
          FStar_Ident.lid_equals ns_resolved uu____3781  in
        if uu____3780
        then
          let uu____3782 =
            FStar_Ident.lid_equals ns_resolved FStar_Parser_Const.prims_lid
             in
          (if uu____3782
           then ()
           else
             (let uu____3784 =
                let uu____3789 =
                  FStar_Util.format1
                    "Reference %s to current module is forbidden (see GitHub issue #451)"
                    ns_original.FStar_Ident.str
                   in
                (FStar_Errors.Fatal_ForbiddenReferenceToCurrentModule,
                  uu____3789)
                 in
              let uu____3790 = FStar_Ident.range_of_lid ns_original  in
              FStar_Errors.raise_error uu____3784 uu____3790))
        else ()
  
let (fail_if_qualified_by_curmodule : env -> FStar_Ident.lident -> unit) =
  fun env  ->
    fun lid  ->
      match lid.FStar_Ident.ns with
      | [] -> ()
      | uu____3802 ->
          let modul_orig = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          let uu____3806 = resolve_module_name env modul_orig true  in
          (match uu____3806 with
           | FStar_Pervasives_Native.Some modul_res ->
               fail_if_curmodule env modul_orig modul_res
           | uu____3810 -> ())
  
let (is_open : env -> FStar_Ident.lident -> open_kind -> Prims.bool) =
  fun env  ->
    fun lid  ->
      fun open_kind  ->
        FStar_List.existsb
          (fun uu___171_3831  ->
             match uu___171_3831 with
             | Open_module_or_namespace (ns,k) ->
                 (k = open_kind) && (FStar_Ident.lid_equals lid ns)
             | uu____3834 -> false) env.scope_mods
  
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
                 let uu____3953 = aux rev_ns_prefix ns_last_id  in
                 FStar_All.pipe_right uu____3953
                   (FStar_Util.map_option
                      (fun uu____4003  ->
                         match uu____4003 with
                         | (stripped_ids,rev_kept_ids) ->
                             (stripped_ids, (id1 :: rev_kept_ids)))))
           in
        let do_shorten env1 ids1 =
          match FStar_List.rev ids1 with
          | [] -> ([], [])
          | ns_last_id::ns_rev_prefix ->
              let uu____4073 = aux ns_rev_prefix ns_last_id  in
              (match uu____4073 with
               | FStar_Pervasives_Native.None  -> ([], ids1)
               | FStar_Pervasives_Native.Some (stripped_ids,rev_kept_ids) ->
                   (stripped_ids, (FStar_List.rev rev_kept_ids)))
           in
        if is_full_path && ((FStar_List.length ids) > (Prims.parse_int "0"))
        then
          let uu____4134 =
            let uu____4137 = FStar_Ident.lid_of_ids ids  in
            resolve_module_name env uu____4137 true  in
          match uu____4134 with
          | FStar_Pervasives_Native.Some m when module_is_open env m ->
              (ids, [])
          | uu____4151 -> do_shorten env ids
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
                  | uu____4270::uu____4271 ->
                      let uu____4274 =
                        let uu____4277 =
                          let uu____4278 =
                            FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
                          let uu____4279 = FStar_Ident.range_of_lid lid  in
                          FStar_Ident.set_lid_range uu____4278 uu____4279  in
                        resolve_module_name env uu____4277 true  in
                      (match uu____4274 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some modul ->
                           let uu____4283 =
                             find_in_module_with_includes eikind f_module
                               Cont_fail env modul lid.FStar_Ident.ident
                              in
                           option_of_cont
                             (fun uu____4287  -> FStar_Pervasives_Native.None)
                             uu____4283)
                  | [] ->
                      try_lookup_id'' env lid.FStar_Ident.ident eikind
                        k_local_binding k_rec_binding k_record f_module
                        l_default
  
let cont_of_option :
  'a . 'a cont_t -> 'a FStar_Pervasives_Native.option -> 'a cont_t =
  fun k_none  ->
    fun uu___172_4310  ->
      match uu___172_4310 with
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
              let uu____4426 = k_global_def lid1 def  in
              cont_of_option k uu____4426  in
            let f_module lid' =
              let k = Cont_ignore  in
              find_in_module env lid' (k_global_def' k) k  in
            let l_default k i = lookup_default_id env i (k_global_def' k) k
               in
            resolve_in_open_namespaces'' env lid Exported_id_term_type
              (fun l  ->
                 let uu____4462 = k_local_binding l  in
                 cont_of_option Cont_fail uu____4462)
              (fun r  ->
                 let uu____4468 = k_rec_binding r  in
                 cont_of_option Cont_fail uu____4468)
              (fun uu____4472  -> Cont_ignore) f_module l_default
  
let (fv_qual_of_se :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option)
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____4482,uu____4483,uu____4484,l,uu____4486,uu____4487) ->
        let qopt =
          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
            (fun uu___173_4498  ->
               match uu___173_4498 with
               | FStar_Syntax_Syntax.RecordConstructor (uu____4501,fs) ->
                   FStar_Pervasives_Native.Some
                     (FStar_Syntax_Syntax.Record_ctor (l, fs))
               | uu____4513 -> FStar_Pervasives_Native.None)
           in
        (match qopt with
         | FStar_Pervasives_Native.None  ->
             FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor
         | x -> x)
    | FStar_Syntax_Syntax.Sig_declare_typ (uu____4519,uu____4520,uu____4521)
        -> FStar_Pervasives_Native.None
    | uu____4522 -> FStar_Pervasives_Native.None
  
let (lb_fv :
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Ident.lident -> FStar_Syntax_Syntax.fv)
  =
  fun lbs  ->
    fun lid  ->
      let uu____4537 =
        FStar_Util.find_map lbs
          (fun lb  ->
             let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
             let uu____4545 = FStar_Syntax_Syntax.fv_eq_lid fv lid  in
             if uu____4545
             then FStar_Pervasives_Native.Some fv
             else FStar_Pervasives_Native.None)
         in
      FStar_All.pipe_right uu____4537 FStar_Util.must
  
let (ns_of_lid_equals :
  FStar_Ident.lident -> FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    fun ns  ->
      (let uu____4563 =
         let uu____4564 = FStar_Ident.ids_of_lid ns  in
         FStar_List.length uu____4564  in
       (FStar_List.length lid.FStar_Ident.ns) = uu____4563) &&
        (let uu____4572 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
         FStar_Ident.lid_equals uu____4572 ns)
  
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
          let k_global_def source_lid uu___180_4614 =
            match uu___180_4614 with
            | (uu____4621,true ) when exclude_interf ->
                FStar_Pervasives_Native.None
            | (se,uu____4623) ->
                (match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_inductive_typ uu____4626 ->
                     let uu____4643 =
                       let uu____4644 =
                         let uu____4653 =
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None
                            in
                         (uu____4653, false,
                           (se.FStar_Syntax_Syntax.sigattrs))
                          in
                       Term_name uu____4644  in
                     FStar_Pervasives_Native.Some uu____4643
                 | FStar_Syntax_Syntax.Sig_datacon uu____4656 ->
                     let uu____4671 =
                       let uu____4672 =
                         let uu____4681 =
                           let uu____4682 = fv_qual_of_se se  in
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.delta_constant uu____4682
                            in
                         (uu____4681, false,
                           (se.FStar_Syntax_Syntax.sigattrs))
                          in
                       Term_name uu____4672  in
                     FStar_Pervasives_Native.Some uu____4671
                 | FStar_Syntax_Syntax.Sig_let ((uu____4687,lbs),uu____4689)
                     ->
                     let fv = lb_fv lbs source_lid  in
                     let uu____4699 =
                       let uu____4700 =
                         let uu____4709 =
                           FStar_Syntax_Syntax.fvar source_lid
                             fv.FStar_Syntax_Syntax.fv_delta
                             fv.FStar_Syntax_Syntax.fv_qual
                            in
                         (uu____4709, false,
                           (se.FStar_Syntax_Syntax.sigattrs))
                          in
                       Term_name uu____4700  in
                     FStar_Pervasives_Native.Some uu____4699
                 | FStar_Syntax_Syntax.Sig_declare_typ
                     (lid1,uu____4713,uu____4714) ->
                     let quals = se.FStar_Syntax_Syntax.sigquals  in
                     let uu____4718 =
                       any_val ||
                         (FStar_All.pipe_right quals
                            (FStar_Util.for_some
                               (fun uu___174_4722  ->
                                  match uu___174_4722 with
                                  | FStar_Syntax_Syntax.Assumption  -> true
                                  | uu____4723 -> false)))
                        in
                     if uu____4718
                     then
                       let lid2 =
                         let uu____4727 = FStar_Ident.range_of_lid source_lid
                            in
                         FStar_Ident.set_lid_range lid1 uu____4727  in
                       let dd =
                         let uu____4729 =
                           (FStar_Syntax_Util.is_primop_lid lid2) ||
                             (FStar_All.pipe_right quals
                                (FStar_Util.for_some
                                   (fun uu___175_4734  ->
                                      match uu___175_4734 with
                                      | FStar_Syntax_Syntax.Projector
                                          uu____4735 -> true
                                      | FStar_Syntax_Syntax.Discriminator
                                          uu____4740 -> true
                                      | uu____4741 -> false)))
                            in
                         if uu____4729
                         then FStar_Syntax_Syntax.delta_equational
                         else FStar_Syntax_Syntax.delta_constant  in
                       let dd1 =
                         let uu____4744 =
                           (FStar_All.pipe_right quals
                              (FStar_Util.for_some
                                 (fun uu___176_4748  ->
                                    match uu___176_4748 with
                                    | FStar_Syntax_Syntax.Abstract  -> true
                                    | uu____4749 -> false)))
                             ||
                             ((FStar_All.pipe_right quals
                                 (FStar_Util.for_some
                                    (fun uu___177_4753  ->
                                       match uu___177_4753 with
                                       | FStar_Syntax_Syntax.Assumption  ->
                                           true
                                       | uu____4754 -> false)))
                                &&
                                (let uu____4756 =
                                   FStar_All.pipe_right quals
                                     (FStar_Util.for_some
                                        (fun uu___178_4760  ->
                                           match uu___178_4760 with
                                           | FStar_Syntax_Syntax.New  -> true
                                           | uu____4761 -> false))
                                    in
                                 Prims.op_Negation uu____4756))
                            in
                         if uu____4744
                         then FStar_Syntax_Syntax.Delta_abstract dd
                         else dd  in
                       let uu____4763 =
                         FStar_Util.find_map quals
                           (fun uu___179_4768  ->
                              match uu___179_4768 with
                              | FStar_Syntax_Syntax.Reflectable refl_monad ->
                                  FStar_Pervasives_Native.Some refl_monad
                              | uu____4772 -> FStar_Pervasives_Native.None)
                          in
                       (match uu____4763 with
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
                        | uu____4781 ->
                            let uu____4784 =
                              let uu____4785 =
                                let uu____4794 =
                                  let uu____4795 = fv_qual_of_se se  in
                                  FStar_Syntax_Syntax.fvar lid2 dd1
                                    uu____4795
                                   in
                                (uu____4794, false,
                                  (se.FStar_Syntax_Syntax.sigattrs))
                                 in
                              Term_name uu____4785  in
                            FStar_Pervasives_Native.Some uu____4784)
                     else FStar_Pervasives_Native.None
                 | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
                     let uu____4802 =
                       let uu____4803 =
                         let uu____4808 =
                           let uu____4809 =
                             FStar_Ident.range_of_lid source_lid  in
                           FStar_Ident.set_lid_range
                             ne.FStar_Syntax_Syntax.mname uu____4809
                            in
                         (se, uu____4808)  in
                       Eff_name uu____4803  in
                     FStar_Pervasives_Native.Some uu____4802
                 | FStar_Syntax_Syntax.Sig_new_effect ne ->
                     let uu____4811 =
                       let uu____4812 =
                         let uu____4817 =
                           let uu____4818 =
                             FStar_Ident.range_of_lid source_lid  in
                           FStar_Ident.set_lid_range
                             ne.FStar_Syntax_Syntax.mname uu____4818
                            in
                         (se, uu____4817)  in
                       Eff_name uu____4812  in
                     FStar_Pervasives_Native.Some uu____4811
                 | FStar_Syntax_Syntax.Sig_effect_abbrev uu____4819 ->
                     FStar_Pervasives_Native.Some (Eff_name (se, source_lid))
                 | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
                     let uu____4838 =
                       let uu____4839 =
                         let uu____4848 =
                           FStar_Syntax_Syntax.fvar source_lid
                             (FStar_Syntax_Syntax.Delta_constant_at_level
                                (Prims.parse_int "1"))
                             FStar_Pervasives_Native.None
                            in
                         (uu____4848, false, [])  in
                       Term_name uu____4839  in
                     FStar_Pervasives_Native.Some uu____4838
                 | uu____4851 -> FStar_Pervasives_Native.None)
             in
          let k_local_binding r =
            let uu____4872 =
              let uu____4877 = FStar_Ident.range_of_lid lid  in
              found_local_binding uu____4877 r  in
            match uu____4872 with
            | (t,mut) ->
                FStar_Pervasives_Native.Some (Term_name (t, mut, []))
             in
          let k_rec_binding uu____4897 =
            match uu____4897 with
            | (id1,l,dd) ->
                let uu____4909 =
                  let uu____4910 =
                    let uu____4919 =
                      let uu____4920 =
                        let uu____4921 = FStar_Ident.range_of_lid lid  in
                        FStar_Ident.set_lid_range l uu____4921  in
                      FStar_Syntax_Syntax.fvar uu____4920 dd
                        FStar_Pervasives_Native.None
                       in
                    (uu____4919, false, [])  in
                  Term_name uu____4910  in
                FStar_Pervasives_Native.Some uu____4909
             in
          let found_unmangled =
            match lid.FStar_Ident.ns with
            | [] ->
                let uu____4929 = unmangleOpName lid.FStar_Ident.ident  in
                (match uu____4929 with
                 | FStar_Pervasives_Native.Some (t,mut) ->
                     FStar_Pervasives_Native.Some (Term_name (t, mut, []))
                 | uu____4946 -> FStar_Pervasives_Native.None)
            | uu____4953 -> FStar_Pervasives_Native.None  in
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
        let uu____4988 = try_lookup_name true exclude_interf env lid  in
        match uu____4988 with
        | FStar_Pervasives_Native.Some (Eff_name (o,l)) ->
            FStar_Pervasives_Native.Some (o, l)
        | uu____5003 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____5022 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____5022 with
      | FStar_Pervasives_Native.Some (o,l1) ->
          FStar_Pervasives_Native.Some l1
      | uu____5037 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_name_and_attributes :
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident,FStar_Syntax_Syntax.cflags Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____5062 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____5062 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____5078;
             FStar_Syntax_Syntax.sigquals = uu____5079;
             FStar_Syntax_Syntax.sigmeta = uu____5080;
             FStar_Syntax_Syntax.sigattrs = uu____5081;_},l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____5100;
             FStar_Syntax_Syntax.sigquals = uu____5101;
             FStar_Syntax_Syntax.sigmeta = uu____5102;
             FStar_Syntax_Syntax.sigattrs = uu____5103;_},l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (uu____5121,uu____5122,uu____5123,uu____5124,cattributes);
             FStar_Syntax_Syntax.sigrng = uu____5126;
             FStar_Syntax_Syntax.sigquals = uu____5127;
             FStar_Syntax_Syntax.sigmeta = uu____5128;
             FStar_Syntax_Syntax.sigattrs = uu____5129;_},l1)
          -> FStar_Pervasives_Native.Some (l1, cattributes)
      | uu____5151 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_defn :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.eff_decl FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____5176 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____5176 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____5186;
             FStar_Syntax_Syntax.sigquals = uu____5187;
             FStar_Syntax_Syntax.sigmeta = uu____5188;
             FStar_Syntax_Syntax.sigattrs = uu____5189;_},uu____5190)
          -> FStar_Pervasives_Native.Some ne
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____5200;
             FStar_Syntax_Syntax.sigquals = uu____5201;
             FStar_Syntax_Syntax.sigmeta = uu____5202;
             FStar_Syntax_Syntax.sigattrs = uu____5203;_},uu____5204)
          -> FStar_Pervasives_Native.Some ne
      | uu____5213 -> FStar_Pervasives_Native.None
  
let (is_effect_name : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____5230 = try_lookup_effect_name env lid  in
      match uu____5230 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____5233 -> true
  
let (try_lookup_root_effect_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____5246 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____5246 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (l',uu____5256,uu____5257,uu____5258,uu____5259);
             FStar_Syntax_Syntax.sigrng = uu____5260;
             FStar_Syntax_Syntax.sigquals = uu____5261;
             FStar_Syntax_Syntax.sigmeta = uu____5262;
             FStar_Syntax_Syntax.sigattrs = uu____5263;_},uu____5264)
          ->
          let rec aux new_name =
            let uu____5285 =
              FStar_Util.smap_try_find (sigmap env) new_name.FStar_Ident.str
               in
            match uu____5285 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (s,uu____5303) ->
                (match s.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
                     let uu____5311 =
                       let uu____5312 = FStar_Ident.range_of_lid l  in
                       FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname
                         uu____5312
                        in
                     FStar_Pervasives_Native.Some uu____5311
                 | FStar_Syntax_Syntax.Sig_new_effect ne ->
                     let uu____5314 =
                       let uu____5315 = FStar_Ident.range_of_lid l  in
                       FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname
                         uu____5315
                        in
                     FStar_Pervasives_Native.Some uu____5314
                 | FStar_Syntax_Syntax.Sig_effect_abbrev
                     (uu____5316,uu____5317,uu____5318,cmp,uu____5320) ->
                     let l'' = FStar_Syntax_Util.comp_effect_name cmp  in
                     aux l''
                 | uu____5326 -> FStar_Pervasives_Native.None)
             in
          aux l'
      | FStar_Pervasives_Native.Some (uu____5327,l') ->
          FStar_Pervasives_Native.Some l'
      | uu____5333 -> FStar_Pervasives_Native.None
  
let (lookup_letbinding_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___181_5370 =
        match uu___181_5370 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____5379,uu____5380,uu____5381);
             FStar_Syntax_Syntax.sigrng = uu____5382;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____5384;
             FStar_Syntax_Syntax.sigattrs = uu____5385;_},uu____5386)
            -> FStar_Pervasives_Native.Some quals
        | uu____5393 -> FStar_Pervasives_Native.None  in
      let uu____5400 =
        resolve_in_open_namespaces' env lid
          (fun uu____5408  -> FStar_Pervasives_Native.None)
          (fun uu____5412  -> FStar_Pervasives_Native.None) k_global_def
         in
      match uu____5400 with
      | FStar_Pervasives_Native.Some quals -> quals
      | uu____5422 -> []
  
let (try_lookup_module :
  env ->
    FStar_Ident.path ->
      FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun path  ->
      let uu____5439 =
        FStar_List.tryFind
          (fun uu____5454  ->
             match uu____5454 with
             | (mlid,modul) ->
                 let uu____5461 = FStar_Ident.path_of_lid mlid  in
                 uu____5461 = path) env.modules
         in
      match uu____5439 with
      | FStar_Pervasives_Native.Some (uu____5464,modul) ->
          FStar_Pervasives_Native.Some modul
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (try_lookup_let :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___182_5502 =
        match uu___182_5502 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               ((uu____5509,lbs),uu____5511);
             FStar_Syntax_Syntax.sigrng = uu____5512;
             FStar_Syntax_Syntax.sigquals = uu____5513;
             FStar_Syntax_Syntax.sigmeta = uu____5514;
             FStar_Syntax_Syntax.sigattrs = uu____5515;_},uu____5516)
            ->
            let fv = lb_fv lbs lid1  in
            let uu____5530 =
              FStar_Syntax_Syntax.fvar lid1 fv.FStar_Syntax_Syntax.fv_delta
                fv.FStar_Syntax_Syntax.fv_qual
               in
            FStar_Pervasives_Native.Some uu____5530
        | uu____5531 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____5537  -> FStar_Pervasives_Native.None)
        (fun uu____5539  -> FStar_Pervasives_Native.None) k_global_def
  
let (try_lookup_definition :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___183_5570 =
        match uu___183_5570 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               (lbs,uu____5580);
             FStar_Syntax_Syntax.sigrng = uu____5581;
             FStar_Syntax_Syntax.sigquals = uu____5582;
             FStar_Syntax_Syntax.sigmeta = uu____5583;
             FStar_Syntax_Syntax.sigattrs = uu____5584;_},uu____5585)
            ->
            FStar_Util.find_map (FStar_Pervasives_Native.snd lbs)
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inr fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv lid1 ->
                     FStar_Pervasives_Native.Some
                       (lb.FStar_Syntax_Syntax.lbdef)
                 | uu____5608 -> FStar_Pervasives_Native.None)
        | uu____5615 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____5625  -> FStar_Pervasives_Native.None)
        (fun uu____5629  -> FStar_Pervasives_Native.None) k_global_def
  
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
          let uu____5686 = try_lookup_name any_val exclude_interface env lid
             in
          match uu____5686 with
          | FStar_Pervasives_Native.Some (Term_name (e,mut,attrs)) ->
              FStar_Pervasives_Native.Some (e, mut, attrs)
          | uu____5716 -> FStar_Pervasives_Native.None
  
let (drop_attributes :
  (FStar_Syntax_Syntax.term,Prims.bool,FStar_Syntax_Syntax.attribute
                                         Prims.list)
    FStar_Pervasives_Native.tuple3 FStar_Pervasives_Native.option ->
    (FStar_Syntax_Syntax.term,Prims.bool) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option)
  =
  fun x  ->
    match x with
    | FStar_Pervasives_Native.Some (t,mut,uu____5772) ->
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
      let uu____5847 = try_lookup_lid_with_attributes env l  in
      FStar_All.pipe_right uu____5847 drop_attributes
  
let (resolve_to_fully_qualified_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____5886 = try_lookup_lid env l  in
      match uu____5886 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (e,uu____5900) ->
          let uu____5905 =
            let uu____5906 = FStar_Syntax_Subst.compress e  in
            uu____5906.FStar_Syntax_Syntax.n  in
          (match uu____5905 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               FStar_Pervasives_Native.Some
                 ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
           | uu____5912 -> FStar_Pervasives_Native.None)
  
let (shorten_lid' : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____5923 = shorten_module_path env lid.FStar_Ident.ns true  in
      match uu____5923 with
      | (uu____5932,short) ->
          FStar_Ident.lid_of_ns_and_id short lid.FStar_Ident.ident
  
let (shorten_lid : env -> FStar_Ident.lid -> FStar_Ident.lid) =
  fun env  ->
    fun lid  ->
      match env.curmodule with
      | FStar_Pervasives_Native.None  -> shorten_lid' env lid
      | uu____5952 ->
          let lid_without_ns =
            FStar_Ident.lid_of_ns_and_id [] lid.FStar_Ident.ident  in
          let uu____5956 = resolve_to_fully_qualified_name env lid_without_ns
             in
          (match uu____5956 with
           | FStar_Pervasives_Native.Some lid' when
               lid'.FStar_Ident.str = lid.FStar_Ident.str -> lid_without_ns
           | uu____5960 -> shorten_lid' env lid)
  
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
        let uu___203_5994 = env  in
        {
          curmodule = (uu___203_5994.curmodule);
          curmonad = (uu___203_5994.curmonad);
          modules = (uu___203_5994.modules);
          scope_mods = [];
          exported_ids = empty_exported_id_smap;
          trans_exported_ids = (uu___203_5994.trans_exported_ids);
          includes = empty_include_smap;
          sigaccum = (uu___203_5994.sigaccum);
          sigmap = (uu___203_5994.sigmap);
          iface = (uu___203_5994.iface);
          admitted_iface = (uu___203_5994.admitted_iface);
          expect_typ = (uu___203_5994.expect_typ);
          docs = (uu___203_5994.docs);
          remaining_iface_decls = (uu___203_5994.remaining_iface_decls);
          syntax_only = (uu___203_5994.syntax_only);
          ds_hooks = (uu___203_5994.ds_hooks)
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
      let uu____6017 = try_lookup_lid_with_attributes_no_resolve env l  in
      FStar_All.pipe_right uu____6017 drop_attributes
  
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
               (uu____6091,uu____6092,uu____6093);
             FStar_Syntax_Syntax.sigrng = uu____6094;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____6096;
             FStar_Syntax_Syntax.sigattrs = uu____6097;_},uu____6098)
            ->
            let uu____6103 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___184_6107  ->
                      match uu___184_6107 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | uu____6108 -> false))
               in
            if uu____6103
            then
              let uu____6111 =
                FStar_Syntax_Syntax.lid_as_fv lid1
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Pervasives_Native.Some uu____6111
            else FStar_Pervasives_Native.None
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
               uu____6113;
             FStar_Syntax_Syntax.sigrng = uu____6114;
             FStar_Syntax_Syntax.sigquals = uu____6115;
             FStar_Syntax_Syntax.sigmeta = uu____6116;
             FStar_Syntax_Syntax.sigattrs = uu____6117;_},uu____6118)
            ->
            let qual1 = fv_qual_of_se (FStar_Pervasives_Native.fst se)  in
            let uu____6140 =
              FStar_Syntax_Syntax.lid_as_fv lid1
                FStar_Syntax_Syntax.delta_constant qual1
               in
            FStar_Pervasives_Native.Some uu____6140
        | uu____6141 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____6147  -> FStar_Pervasives_Native.None)
        (fun uu____6149  -> FStar_Pervasives_Native.None) k_global_def
  
let (find_all_datacons :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___185_6182 =
        match uu___185_6182 with
        | ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_inductive_typ
               (uu____6191,uu____6192,uu____6193,uu____6194,datas,uu____6196);
             FStar_Syntax_Syntax.sigrng = uu____6197;
             FStar_Syntax_Syntax.sigquals = uu____6198;
             FStar_Syntax_Syntax.sigmeta = uu____6199;
             FStar_Syntax_Syntax.sigattrs = uu____6200;_},uu____6201)
            -> FStar_Pervasives_Native.Some datas
        | uu____6216 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____6226  -> FStar_Pervasives_Native.None)
        (fun uu____6230  -> FStar_Pervasives_Native.None) k_global_def
  
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
  let push1 uu____6306 =
    let uu____6307 =
      let uu____6312 =
        let uu____6315 = FStar_ST.op_Bang record_cache  in
        FStar_List.hd uu____6315  in
      let uu____6375 = FStar_ST.op_Bang record_cache  in uu____6312 ::
        uu____6375
       in
    FStar_ST.op_Colon_Equals record_cache uu____6307  in
  let pop1 uu____6493 =
    let uu____6494 =
      let uu____6499 = FStar_ST.op_Bang record_cache  in
      FStar_List.tl uu____6499  in
    FStar_ST.op_Colon_Equals record_cache uu____6494  in
  let snapshot1 uu____6621 = FStar_Common.snapshot push1 record_cache ()  in
  let rollback1 depth = FStar_Common.rollback pop1 record_cache depth  in
  let peek1 uu____6687 =
    let uu____6688 = FStar_ST.op_Bang record_cache  in
    FStar_List.hd uu____6688  in
  let insert r =
    let uu____6754 =
      let uu____6759 = let uu____6762 = peek1 ()  in r :: uu____6762  in
      let uu____6765 =
        let uu____6770 = FStar_ST.op_Bang record_cache  in
        FStar_List.tl uu____6770  in
      uu____6759 :: uu____6765  in
    FStar_ST.op_Colon_Equals record_cache uu____6754  in
  let filter1 uu____6890 =
    let rc = peek1 ()  in
    let filtered =
      FStar_List.filter
        (fun r  -> Prims.op_Negation r.is_private_or_abstract) rc
       in
    let uu____6899 =
      let uu____6904 =
        let uu____6909 = FStar_ST.op_Bang record_cache  in
        FStar_List.tl uu____6909  in
      filtered :: uu____6904  in
    FStar_ST.op_Colon_Equals record_cache uu____6899  in
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
        | FStar_Syntax_Syntax.Sig_bundle (sigs,uu____7858) ->
            let is_record =
              FStar_Util.for_some
                (fun uu___186_7876  ->
                   match uu___186_7876 with
                   | FStar_Syntax_Syntax.RecordType uu____7877 -> true
                   | FStar_Syntax_Syntax.RecordConstructor uu____7886 -> true
                   | uu____7895 -> false)
               in
            let find_dc dc =
              FStar_All.pipe_right sigs
                (FStar_Util.find_opt
                   (fun uu___187_7919  ->
                      match uu___187_7919 with
                      | {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_datacon
                            (lid,uu____7921,uu____7922,uu____7923,uu____7924,uu____7925);
                          FStar_Syntax_Syntax.sigrng = uu____7926;
                          FStar_Syntax_Syntax.sigquals = uu____7927;
                          FStar_Syntax_Syntax.sigmeta = uu____7928;
                          FStar_Syntax_Syntax.sigattrs = uu____7929;_} ->
                          FStar_Ident.lid_equals dc lid
                      | uu____7938 -> false))
               in
            FStar_All.pipe_right sigs
              (FStar_List.iter
                 (fun uu___188_7973  ->
                    match uu___188_7973 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ
                          (typename,univs1,parms,uu____7977,uu____7978,dc::[]);
                        FStar_Syntax_Syntax.sigrng = uu____7980;
                        FStar_Syntax_Syntax.sigquals = typename_quals;
                        FStar_Syntax_Syntax.sigmeta = uu____7982;
                        FStar_Syntax_Syntax.sigattrs = uu____7983;_} ->
                        let uu____7994 =
                          let uu____7995 = find_dc dc  in
                          FStar_All.pipe_left FStar_Util.must uu____7995  in
                        (match uu____7994 with
                         | {
                             FStar_Syntax_Syntax.sigel =
                               FStar_Syntax_Syntax.Sig_datacon
                               (constrname,uu____8001,t,uu____8003,uu____8004,uu____8005);
                             FStar_Syntax_Syntax.sigrng = uu____8006;
                             FStar_Syntax_Syntax.sigquals = uu____8007;
                             FStar_Syntax_Syntax.sigmeta = uu____8008;
                             FStar_Syntax_Syntax.sigattrs = uu____8009;_} ->
                             let uu____8018 =
                               FStar_Syntax_Util.arrow_formals t  in
                             (match uu____8018 with
                              | (formals,uu____8034) ->
                                  let is_rec = is_record typename_quals  in
                                  let formals' =
                                    FStar_All.pipe_right formals
                                      (FStar_List.collect
                                         (fun uu____8087  ->
                                            match uu____8087 with
                                            | (x,q) ->
                                                let uu____8100 =
                                                  (FStar_Syntax_Syntax.is_null_bv
                                                     x)
                                                    ||
                                                    (is_rec &&
                                                       (FStar_Syntax_Syntax.is_implicit
                                                          q))
                                                   in
                                                if uu____8100
                                                then []
                                                else [(x, q)]))
                                     in
                                  let fields' =
                                    FStar_All.pipe_right formals'
                                      (FStar_List.map
                                         (fun uu____8153  ->
                                            match uu____8153 with
                                            | (x,q) ->
                                                let uu____8166 =
                                                  if is_rec
                                                  then
                                                    FStar_Syntax_Util.unmangle_field_name
                                                      x.FStar_Syntax_Syntax.ppname
                                                  else
                                                    x.FStar_Syntax_Syntax.ppname
                                                   in
                                                (uu____8166,
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
                                  ((let uu____8179 =
                                      let uu____8182 =
                                        FStar_ST.op_Bang new_globs  in
                                      (Record_or_dc record) :: uu____8182  in
                                    FStar_ST.op_Colon_Equals new_globs
                                      uu____8179);
                                   (match () with
                                    | () ->
                                        ((let add_field uu____8293 =
                                            match uu____8293 with
                                            | (id1,uu____8299) ->
                                                let modul =
                                                  let uu____8301 =
                                                    FStar_Ident.lid_of_ids
                                                      constrname.FStar_Ident.ns
                                                     in
                                                  uu____8301.FStar_Ident.str
                                                   in
                                                let uu____8302 =
                                                  get_exported_id_set e modul
                                                   in
                                                (match uu____8302 with
                                                 | FStar_Pervasives_Native.Some
                                                     my_ex ->
                                                     let my_exported_ids =
                                                       my_ex
                                                         Exported_id_field
                                                        in
                                                     ((let uu____8336 =
                                                         let uu____8337 =
                                                           FStar_ST.op_Bang
                                                             my_exported_ids
                                                            in
                                                         FStar_Util.set_add
                                                           id1.FStar_Ident.idText
                                                           uu____8337
                                                          in
                                                       FStar_ST.op_Colon_Equals
                                                         my_exported_ids
                                                         uu____8336);
                                                      (match () with
                                                       | () ->
                                                           let projname =
                                                             let uu____8431 =
                                                               let uu____8432
                                                                 =
                                                                 FStar_Syntax_Util.mk_field_projector_name_from_ident
                                                                   constrname
                                                                   id1
                                                                  in
                                                               uu____8432.FStar_Ident.ident
                                                                in
                                                             uu____8431.FStar_Ident.idText
                                                              in
                                                           let uu____8434 =
                                                             let uu____8435 =
                                                               FStar_ST.op_Bang
                                                                 my_exported_ids
                                                                in
                                                             FStar_Util.set_add
                                                               projname
                                                               uu____8435
                                                              in
                                                           FStar_ST.op_Colon_Equals
                                                             my_exported_ids
                                                             uu____8434))
                                                 | FStar_Pervasives_Native.None
                                                      -> ())
                                             in
                                          FStar_List.iter add_field fields');
                                         (match () with
                                          | () -> insert_record_cache record)))))
                         | uu____8537 -> ())
                    | uu____8538 -> ()))
        | uu____8539 -> ()
  
let (try_lookup_record_or_dc_by_field_name :
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option) =
  fun env  ->
    fun fieldname  ->
      let find_in_cache fieldname1 =
        let uu____8560 =
          ((fieldname1.FStar_Ident.ns), (fieldname1.FStar_Ident.ident))  in
        match uu____8560 with
        | (ns,id1) ->
            let uu____8577 = peek_record_cache ()  in
            FStar_Util.find_map uu____8577
              (fun record  ->
                 let uu____8583 =
                   find_in_record ns id1 record (fun r  -> Cont_ok r)  in
                 option_of_cont
                   (fun uu____8589  -> FStar_Pervasives_Native.None)
                   uu____8583)
         in
      resolve_in_open_namespaces'' env fieldname Exported_id_field
        (fun uu____8591  -> Cont_ignore) (fun uu____8593  -> Cont_ignore)
        (fun r  -> Cont_ok r)
        (fun fn  ->
           let uu____8599 = find_in_cache fn  in
           cont_of_option Cont_ignore uu____8599)
        (fun k  -> fun uu____8605  -> k)
  
let (try_lookup_record_by_field_name :
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option) =
  fun env  ->
    fun fieldname  ->
      let uu____8620 = try_lookup_record_or_dc_by_field_name env fieldname
         in
      match uu____8620 with
      | FStar_Pervasives_Native.Some r when r.is_record ->
          FStar_Pervasives_Native.Some r
      | uu____8626 -> FStar_Pervasives_Native.None
  
let (belongs_to_record :
  env -> FStar_Ident.lident -> record_or_dc -> Prims.bool) =
  fun env  ->
    fun lid  ->
      fun record  ->
        let uu____8644 = try_lookup_record_by_field_name env lid  in
        match uu____8644 with
        | FStar_Pervasives_Native.Some record' when
            let uu____8648 =
              let uu____8649 =
                FStar_Ident.path_of_ns (record.typename).FStar_Ident.ns  in
              FStar_Ident.text_of_path uu____8649  in
            let uu____8650 =
              let uu____8651 =
                FStar_Ident.path_of_ns (record'.typename).FStar_Ident.ns  in
              FStar_Ident.text_of_path uu____8651  in
            uu____8648 = uu____8650 ->
            let uu____8652 =
              find_in_record (record.typename).FStar_Ident.ns
                lid.FStar_Ident.ident record (fun uu____8656  -> Cont_ok ())
               in
            (match uu____8652 with
             | Cont_ok uu____8657 -> true
             | uu____8658 -> false)
        | uu____8661 -> false
  
let (try_lookup_dc_by_field_name :
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident,Prims.bool) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun fieldname  ->
      let uu____8680 = try_lookup_record_or_dc_by_field_name env fieldname
         in
      match uu____8680 with
      | FStar_Pervasives_Native.Some r ->
          let uu____8690 =
            let uu____8695 =
              let uu____8696 =
                FStar_Ident.lid_of_ids
                  (FStar_List.append (r.typename).FStar_Ident.ns
                     [r.constrname])
                 in
              let uu____8697 = FStar_Ident.range_of_lid fieldname  in
              FStar_Ident.set_lid_range uu____8696 uu____8697  in
            (uu____8695, (r.is_record))  in
          FStar_Pervasives_Native.Some uu____8690
      | uu____8702 -> FStar_Pervasives_Native.None
  
let (string_set_ref_new : unit -> Prims.string FStar_Util.set FStar_ST.ref) =
  fun uu____8728  ->
    let uu____8729 = FStar_Util.new_set FStar_Util.compare  in
    FStar_Util.mk_ref uu____8729
  
let (exported_id_set_new :
  unit -> exported_id_kind -> Prims.string FStar_Util.set FStar_ST.ref) =
  fun uu____8756  ->
    let term_type_set = string_set_ref_new ()  in
    let field_set = string_set_ref_new ()  in
    fun uu___189_8767  ->
      match uu___189_8767 with
      | Exported_id_term_type  -> term_type_set
      | Exported_id_field  -> field_set
  
let (unique :
  Prims.bool -> Prims.bool -> env -> FStar_Ident.lident -> Prims.bool) =
  fun any_val  ->
    fun exclude_interface  ->
      fun env  ->
        fun lid  ->
          let filter_scope_mods uu___190_8819 =
            match uu___190_8819 with
            | Rec_binding uu____8820 -> true
            | uu____8821 -> false  in
          let this_env =
            let uu___204_8823 = env  in
            let uu____8824 =
              FStar_List.filter filter_scope_mods env.scope_mods  in
            {
              curmodule = (uu___204_8823.curmodule);
              curmonad = (uu___204_8823.curmonad);
              modules = (uu___204_8823.modules);
              scope_mods = uu____8824;
              exported_ids = empty_exported_id_smap;
              trans_exported_ids = (uu___204_8823.trans_exported_ids);
              includes = empty_include_smap;
              sigaccum = (uu___204_8823.sigaccum);
              sigmap = (uu___204_8823.sigmap);
              iface = (uu___204_8823.iface);
              admitted_iface = (uu___204_8823.admitted_iface);
              expect_typ = (uu___204_8823.expect_typ);
              docs = (uu___204_8823.docs);
              remaining_iface_decls = (uu___204_8823.remaining_iface_decls);
              syntax_only = (uu___204_8823.syntax_only);
              ds_hooks = (uu___204_8823.ds_hooks)
            }  in
          let uu____8827 =
            try_lookup_lid' any_val exclude_interface this_env lid  in
          match uu____8827 with
          | FStar_Pervasives_Native.None  -> true
          | FStar_Pervasives_Native.Some uu____8846 -> false
  
let (push_scope_mod : env -> scope_mod -> env) =
  fun env  ->
    fun scope_mod  ->
      let uu___205_8873 = env  in
      {
        curmodule = (uu___205_8873.curmodule);
        curmonad = (uu___205_8873.curmonad);
        modules = (uu___205_8873.modules);
        scope_mods = (scope_mod :: (env.scope_mods));
        exported_ids = (uu___205_8873.exported_ids);
        trans_exported_ids = (uu___205_8873.trans_exported_ids);
        includes = (uu___205_8873.includes);
        sigaccum = (uu___205_8873.sigaccum);
        sigmap = (uu___205_8873.sigmap);
        iface = (uu___205_8873.iface);
        admitted_iface = (uu___205_8873.admitted_iface);
        expect_typ = (uu___205_8873.expect_typ);
        docs = (uu___205_8873.docs);
        remaining_iface_decls = (uu___205_8873.remaining_iface_decls);
        syntax_only = (uu___205_8873.syntax_only);
        ds_hooks = (uu___205_8873.ds_hooks)
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
        let uu____8938 =
          (unique false true env l) || (FStar_Options.interactive ())  in
        if uu____8938
        then push_scope_mod env (Rec_binding (x, l, dd))
        else
          (let uu____8940 = FStar_Ident.range_of_lid l  in
           FStar_Errors.raise_error
             (FStar_Errors.Fatal_DuplicateTopLevelNames,
               (Prims.strcat "Duplicate top-level names " l.FStar_Ident.str))
             uu____8940)
  
let (push_sigelt' : Prims.bool -> env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun fail_on_dup  ->
    fun env  ->
      fun s  ->
        let err l =
          let sopt = FStar_Util.smap_try_find (sigmap env) l.FStar_Ident.str
             in
          let r =
            match sopt with
            | FStar_Pervasives_Native.Some (se,uu____8975) ->
                let uu____8980 =
                  FStar_Util.find_opt (FStar_Ident.lid_equals l)
                    (FStar_Syntax_Util.lids_of_sigelt se)
                   in
                (match uu____8980 with
                 | FStar_Pervasives_Native.Some l1 ->
                     let uu____8984 = FStar_Ident.range_of_lid l1  in
                     FStar_All.pipe_left FStar_Range.string_of_range
                       uu____8984
                 | FStar_Pervasives_Native.None  -> "<unknown>")
            | FStar_Pervasives_Native.None  -> "<unknown>"  in
          let uu____8989 =
            let uu____8994 =
              let uu____8995 = FStar_Ident.text_of_lid l  in
              FStar_Util.format2
                "Duplicate top-level names [%s]; previously declared at %s"
                uu____8995 r
               in
            (FStar_Errors.Fatal_DuplicateTopLevelNames, uu____8994)  in
          let uu____8996 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____8989 uu____8996  in
        let globals = FStar_Util.mk_ref env.scope_mods  in
        let env1 =
          let uu____9005 =
            match s.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_let uu____9014 -> (false, true)
            | FStar_Syntax_Syntax.Sig_bundle uu____9021 -> (false, true)
            | uu____9030 -> (false, false)  in
          match uu____9005 with
          | (any_val,exclude_interface) ->
              let lids = FStar_Syntax_Util.lids_of_sigelt s  in
              let uu____9036 =
                FStar_Util.find_map lids
                  (fun l  ->
                     let uu____9042 =
                       let uu____9043 =
                         unique any_val exclude_interface env l  in
                       Prims.op_Negation uu____9043  in
                     if uu____9042
                     then FStar_Pervasives_Native.Some l
                     else FStar_Pervasives_Native.None)
                 in
              (match uu____9036 with
               | FStar_Pervasives_Native.Some l when fail_on_dup -> err l
               | uu____9048 ->
                   (extract_record env globals s;
                    (let uu___206_9074 = env  in
                     {
                       curmodule = (uu___206_9074.curmodule);
                       curmonad = (uu___206_9074.curmonad);
                       modules = (uu___206_9074.modules);
                       scope_mods = (uu___206_9074.scope_mods);
                       exported_ids = (uu___206_9074.exported_ids);
                       trans_exported_ids =
                         (uu___206_9074.trans_exported_ids);
                       includes = (uu___206_9074.includes);
                       sigaccum = (s :: (env.sigaccum));
                       sigmap = (uu___206_9074.sigmap);
                       iface = (uu___206_9074.iface);
                       admitted_iface = (uu___206_9074.admitted_iface);
                       expect_typ = (uu___206_9074.expect_typ);
                       docs = (uu___206_9074.docs);
                       remaining_iface_decls =
                         (uu___206_9074.remaining_iface_decls);
                       syntax_only = (uu___206_9074.syntax_only);
                       ds_hooks = (uu___206_9074.ds_hooks)
                     })))
           in
        let env2 =
          let uu___207_9076 = env1  in
          let uu____9077 = FStar_ST.op_Bang globals  in
          {
            curmodule = (uu___207_9076.curmodule);
            curmonad = (uu___207_9076.curmonad);
            modules = (uu___207_9076.modules);
            scope_mods = uu____9077;
            exported_ids = (uu___207_9076.exported_ids);
            trans_exported_ids = (uu___207_9076.trans_exported_ids);
            includes = (uu___207_9076.includes);
            sigaccum = (uu___207_9076.sigaccum);
            sigmap = (uu___207_9076.sigmap);
            iface = (uu___207_9076.iface);
            admitted_iface = (uu___207_9076.admitted_iface);
            expect_typ = (uu___207_9076.expect_typ);
            docs = (uu___207_9076.docs);
            remaining_iface_decls = (uu___207_9076.remaining_iface_decls);
            syntax_only = (uu___207_9076.syntax_only);
            ds_hooks = (uu___207_9076.ds_hooks)
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
                                        let uu____9377 =
                                          FStar_Ident.lid_of_ids
                                            lid.FStar_Ident.ns
                                           in
                                        uu____9377.FStar_Ident.str  in
                                      ((let uu____9379 =
                                          get_exported_id_set env3 modul  in
                                        match uu____9379 with
                                        | FStar_Pervasives_Native.Some f ->
                                            let my_exported_ids =
                                              f Exported_id_term_type  in
                                            let uu____9412 =
                                              let uu____9413 =
                                                FStar_ST.op_Bang
                                                  my_exported_ids
                                                 in
                                              FStar_Util.set_add
                                                (lid.FStar_Ident.ident).FStar_Ident.idText
                                                uu____9413
                                               in
                                            FStar_ST.op_Colon_Equals
                                              my_exported_ids uu____9412
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
                let uu___208_9517 = env3  in
                let uu____9518 = FStar_ST.op_Bang globals  in
                {
                  curmodule = (uu___208_9517.curmodule);
                  curmonad = (uu___208_9517.curmonad);
                  modules = (uu___208_9517.modules);
                  scope_mods = uu____9518;
                  exported_ids = (uu___208_9517.exported_ids);
                  trans_exported_ids = (uu___208_9517.trans_exported_ids);
                  includes = (uu___208_9517.includes);
                  sigaccum = (uu___208_9517.sigaccum);
                  sigmap = (uu___208_9517.sigmap);
                  iface = (uu___208_9517.iface);
                  admitted_iface = (uu___208_9517.admitted_iface);
                  expect_typ = (uu___208_9517.expect_typ);
                  docs = (uu___208_9517.docs);
                  remaining_iface_decls =
                    (uu___208_9517.remaining_iface_decls);
                  syntax_only = (uu___208_9517.syntax_only);
                  ds_hooks = (uu___208_9517.ds_hooks)
                }  in
              env4))
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  -> fun se  -> push_sigelt' true env se 
let (push_sigelt_force : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  -> fun se  -> push_sigelt' false env se 
let (push_namespace : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun ns  ->
      let uu____9600 =
        let uu____9605 = resolve_module_name env ns false  in
        match uu____9605 with
        | FStar_Pervasives_Native.None  ->
            let modules = env.modules  in
            let uu____9619 =
              FStar_All.pipe_right modules
                (FStar_Util.for_some
                   (fun uu____9635  ->
                      match uu____9635 with
                      | (m,uu____9641) ->
                          let uu____9642 =
                            let uu____9643 = FStar_Ident.text_of_lid m  in
                            Prims.strcat uu____9643 "."  in
                          let uu____9644 =
                            let uu____9645 = FStar_Ident.text_of_lid ns  in
                            Prims.strcat uu____9645 "."  in
                          FStar_Util.starts_with uu____9642 uu____9644))
               in
            if uu____9619
            then (ns, Open_namespace)
            else
              (let uu____9651 =
                 let uu____9656 =
                   let uu____9657 = FStar_Ident.text_of_lid ns  in
                   FStar_Util.format1 "Namespace %s cannot be found"
                     uu____9657
                    in
                 (FStar_Errors.Fatal_NameSpaceNotFound, uu____9656)  in
               let uu____9658 = FStar_Ident.range_of_lid ns  in
               FStar_Errors.raise_error uu____9651 uu____9658)
        | FStar_Pervasives_Native.Some ns' ->
            (fail_if_curmodule env ns ns'; (ns', Open_module))
         in
      match uu____9600 with
      | (ns',kd) ->
          ((env.ds_hooks).ds_push_open_hook env (ns', kd);
           push_scope_mod env (Open_module_or_namespace (ns', kd)))
  
let (push_include : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun ns  ->
      let ns0 = ns  in
      let uu____9679 = resolve_module_name env ns false  in
      match uu____9679 with
      | FStar_Pervasives_Native.Some ns1 ->
          ((env.ds_hooks).ds_push_include_hook env ns1;
           fail_if_curmodule env ns0 ns1;
           (let env1 =
              push_scope_mod env
                (Open_module_or_namespace (ns1, Open_module))
               in
            let curmod =
              let uu____9687 = current_module env1  in
              uu____9687.FStar_Ident.str  in
            (let uu____9689 = FStar_Util.smap_try_find env1.includes curmod
                in
             match uu____9689 with
             | FStar_Pervasives_Native.None  -> ()
             | FStar_Pervasives_Native.Some incl ->
                 let uu____9713 =
                   let uu____9716 = FStar_ST.op_Bang incl  in ns1 ::
                     uu____9716
                    in
                 FStar_ST.op_Colon_Equals incl uu____9713);
            (match () with
             | () ->
                 let uu____9817 =
                   get_trans_exported_id_set env1 ns1.FStar_Ident.str  in
                 (match uu____9817 with
                  | FStar_Pervasives_Native.Some ns_trans_exports ->
                      ((let uu____9837 =
                          let uu____9940 = get_exported_id_set env1 curmod
                             in
                          let uu____9990 =
                            get_trans_exported_id_set env1 curmod  in
                          (uu____9940, uu____9990)  in
                        match uu____9837 with
                        | (FStar_Pervasives_Native.Some
                           cur_exports,FStar_Pervasives_Native.Some
                           cur_trans_exports) ->
                            let update_exports k =
                              let ns_ex =
                                let uu____10433 = ns_trans_exports k  in
                                FStar_ST.op_Bang uu____10433  in
                              let ex = cur_exports k  in
                              (let uu____10619 =
                                 let uu____10622 = FStar_ST.op_Bang ex  in
                                 FStar_Util.set_difference uu____10622 ns_ex
                                  in
                               FStar_ST.op_Colon_Equals ex uu____10619);
                              (match () with
                               | () ->
                                   let trans_ex = cur_trans_exports k  in
                                   let uu____10826 =
                                     let uu____10829 =
                                       FStar_ST.op_Bang trans_ex  in
                                     FStar_Util.set_union uu____10829 ns_ex
                                      in
                                   FStar_ST.op_Colon_Equals trans_ex
                                     uu____10826)
                               in
                            FStar_List.iter update_exports
                              all_exported_id_kinds
                        | uu____10966 -> ());
                       (match () with | () -> env1))
                  | FStar_Pervasives_Native.None  ->
                      let uu____11074 =
                        let uu____11079 =
                          FStar_Util.format1
                            "include: Module %s was not prepared"
                            ns1.FStar_Ident.str
                           in
                        (FStar_Errors.Fatal_IncludeModuleNotPrepared,
                          uu____11079)
                         in
                      let uu____11080 = FStar_Ident.range_of_lid ns1  in
                      FStar_Errors.raise_error uu____11074 uu____11080))))
      | uu____11081 ->
          let uu____11084 =
            let uu____11089 =
              FStar_Util.format1 "include: Module %s cannot be found"
                ns.FStar_Ident.str
               in
            (FStar_Errors.Fatal_ModuleNotFound, uu____11089)  in
          let uu____11090 = FStar_Ident.range_of_lid ns  in
          FStar_Errors.raise_error uu____11084 uu____11090
  
let (push_module_abbrev :
  env -> FStar_Ident.ident -> FStar_Ident.lident -> env) =
  fun env  ->
    fun x  ->
      fun l  ->
        let uu____11106 = module_is_defined env l  in
        if uu____11106
        then
          (fail_if_curmodule env l l;
           (env.ds_hooks).ds_push_module_abbrev_hook env x l;
           push_scope_mod env (Module_abbrev (x, l)))
        else
          (let uu____11110 =
             let uu____11115 =
               let uu____11116 = FStar_Ident.text_of_lid l  in
               FStar_Util.format1 "Module %s cannot be found" uu____11116  in
             (FStar_Errors.Fatal_ModuleNotFound, uu____11115)  in
           let uu____11117 = FStar_Ident.range_of_lid l  in
           FStar_Errors.raise_error uu____11110 uu____11117)
  
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
            ((let uu____11139 =
                FStar_Util.smap_try_find env.docs l.FStar_Ident.str  in
              match uu____11139 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some old_doc ->
                  let uu____11143 = FStar_Ident.range_of_lid l  in
                  let uu____11144 =
                    let uu____11149 =
                      let uu____11150 = FStar_Ident.string_of_lid l  in
                      let uu____11151 =
                        FStar_Parser_AST.string_of_fsdoc old_doc  in
                      let uu____11152 = FStar_Parser_AST.string_of_fsdoc doc1
                         in
                      FStar_Util.format3
                        "Overwriting doc of %s; old doc was [%s]; new doc are [%s]"
                        uu____11150 uu____11151 uu____11152
                       in
                    (FStar_Errors.Warning_DocOverwrite, uu____11149)  in
                  FStar_Errors.log_issue uu____11143 uu____11144);
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
                      let uu____11194 =
                        FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption)
                         in
                      Prims.op_Negation uu____11194 ->
                      let uu____11197 =
                        FStar_Util.smap_try_find (sigmap env)
                          l.FStar_Ident.str
                         in
                      (match uu____11197 with
                       | FStar_Pervasives_Native.Some
                           ({
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_let uu____11210;
                              FStar_Syntax_Syntax.sigrng = uu____11211;
                              FStar_Syntax_Syntax.sigquals = uu____11212;
                              FStar_Syntax_Syntax.sigmeta = uu____11213;
                              FStar_Syntax_Syntax.sigattrs = uu____11214;_},uu____11215)
                           -> lids
                       | FStar_Pervasives_Native.Some
                           ({
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_inductive_typ
                                uu____11230;
                              FStar_Syntax_Syntax.sigrng = uu____11231;
                              FStar_Syntax_Syntax.sigquals = uu____11232;
                              FStar_Syntax_Syntax.sigmeta = uu____11233;
                              FStar_Syntax_Syntax.sigattrs = uu____11234;_},uu____11235)
                           -> lids
                       | uu____11260 ->
                           ((let uu____11268 =
                               let uu____11269 = FStar_Options.interactive ()
                                  in
                               Prims.op_Negation uu____11269  in
                             if uu____11268
                             then
                               let uu____11270 = FStar_Ident.range_of_lid l
                                  in
                               let uu____11271 =
                                 let uu____11276 =
                                   let uu____11277 =
                                     FStar_Ident.string_of_lid l  in
                                   FStar_Util.format1
                                     "Admitting %s without a definition"
                                     uu____11277
                                    in
                                 (FStar_Errors.Warning_AdmitWithoutDefinition,
                                   uu____11276)
                                  in
                               FStar_Errors.log_issue uu____11270 uu____11271
                             else ());
                            (let quals = FStar_Syntax_Syntax.Assumption ::
                               (se.FStar_Syntax_Syntax.sigquals)  in
                             FStar_Util.smap_add (sigmap env)
                               l.FStar_Ident.str
                               ((let uu___209_11288 = se  in
                                 {
                                   FStar_Syntax_Syntax.sigel =
                                     (uu___209_11288.FStar_Syntax_Syntax.sigel);
                                   FStar_Syntax_Syntax.sigrng =
                                     (uu___209_11288.FStar_Syntax_Syntax.sigrng);
                                   FStar_Syntax_Syntax.sigquals = quals;
                                   FStar_Syntax_Syntax.sigmeta =
                                     (uu___209_11288.FStar_Syntax_Syntax.sigmeta);
                                   FStar_Syntax_Syntax.sigattrs =
                                     (uu___209_11288.FStar_Syntax_Syntax.sigattrs)
                                 }), false);
                             l
                             ::
                             lids)))
                  | uu____11289 -> lids) [])
         in
      let uu___210_11290 = m  in
      let uu____11291 =
        FStar_All.pipe_right m.FStar_Syntax_Syntax.declarations
          (FStar_List.map
             (fun s  ->
                match s.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_declare_typ
                    (lid,uu____11301,uu____11302) when
                    FStar_List.existsb
                      (fun l  -> FStar_Ident.lid_equals l lid)
                      admitted_sig_lids
                    ->
                    let uu___211_11305 = s  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___211_11305.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___211_11305.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals =
                        (FStar_Syntax_Syntax.Assumption ::
                        (s.FStar_Syntax_Syntax.sigquals));
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___211_11305.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___211_11305.FStar_Syntax_Syntax.sigattrs)
                    }
                | uu____11306 -> s))
         in
      {
        FStar_Syntax_Syntax.name = (uu___210_11290.FStar_Syntax_Syntax.name);
        FStar_Syntax_Syntax.declarations = uu____11291;
        FStar_Syntax_Syntax.exports =
          (uu___210_11290.FStar_Syntax_Syntax.exports);
        FStar_Syntax_Syntax.is_interface =
          (uu___210_11290.FStar_Syntax_Syntax.is_interface)
      }
  
let (finish : env -> FStar_Syntax_Syntax.modul -> env) =
  fun env  ->
    fun modul  ->
      FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations
        (FStar_List.iter
           (fun se  ->
              let quals = se.FStar_Syntax_Syntax.sigquals  in
              match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_bundle (ses,uu____11329) ->
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
                                (lid,uu____11349,uu____11350,uu____11351,uu____11352,uu____11353)
                                ->
                                FStar_Util.smap_remove (sigmap env)
                                  lid.FStar_Ident.str
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (lid,univ_names,binders,typ,uu____11366,uu____11367)
                                ->
                                (FStar_Util.smap_remove (sigmap env)
                                   lid.FStar_Ident.str;
                                 if
                                   Prims.op_Negation
                                     (FStar_List.contains
                                        FStar_Syntax_Syntax.Private quals)
                                 then
                                   (let sigel =
                                      let uu____11382 =
                                        let uu____11389 =
                                          let uu____11390 =
                                            FStar_Ident.range_of_lid lid  in
                                          let uu____11391 =
                                            let uu____11398 =
                                              let uu____11399 =
                                                let uu____11414 =
                                                  FStar_Syntax_Syntax.mk_Total
                                                    typ
                                                   in
                                                (binders, uu____11414)  in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____11399
                                               in
                                            FStar_Syntax_Syntax.mk
                                              uu____11398
                                             in
                                          uu____11391
                                            FStar_Pervasives_Native.None
                                            uu____11390
                                           in
                                        (lid, univ_names, uu____11389)  in
                                      FStar_Syntax_Syntax.Sig_declare_typ
                                        uu____11382
                                       in
                                    let se2 =
                                      let uu___212_11431 = se1  in
                                      {
                                        FStar_Syntax_Syntax.sigel = sigel;
                                        FStar_Syntax_Syntax.sigrng =
                                          (uu___212_11431.FStar_Syntax_Syntax.sigrng);
                                        FStar_Syntax_Syntax.sigquals =
                                          (FStar_Syntax_Syntax.Assumption ::
                                          quals);
                                        FStar_Syntax_Syntax.sigmeta =
                                          (uu___212_11431.FStar_Syntax_Syntax.sigmeta);
                                        FStar_Syntax_Syntax.sigattrs =
                                          (uu___212_11431.FStar_Syntax_Syntax.sigattrs)
                                      }  in
                                    FStar_Util.smap_add (sigmap env)
                                      lid.FStar_Ident.str (se2, false))
                                 else ())
                            | uu____11437 -> ()))
                  else ()
              | FStar_Syntax_Syntax.Sig_declare_typ
                  (lid,uu____11440,uu____11441) ->
                  if FStar_List.contains FStar_Syntax_Syntax.Private quals
                  then
                    FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str
                  else ()
              | FStar_Syntax_Syntax.Sig_let ((uu____11447,lbs),uu____11449)
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
                             let uu____11464 =
                               let uu____11465 =
                                 let uu____11466 =
                                   let uu____11469 =
                                     FStar_Util.right
                                       lb.FStar_Syntax_Syntax.lbname
                                      in
                                   uu____11469.FStar_Syntax_Syntax.fv_name
                                    in
                                 uu____11466.FStar_Syntax_Syntax.v  in
                               uu____11465.FStar_Ident.str  in
                             FStar_Util.smap_remove (sigmap env) uu____11464))
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
                               let uu____11483 =
                                 let uu____11486 =
                                   FStar_Util.right
                                     lb.FStar_Syntax_Syntax.lbname
                                    in
                                 uu____11486.FStar_Syntax_Syntax.fv_name  in
                               uu____11483.FStar_Syntax_Syntax.v  in
                             let quals1 = FStar_Syntax_Syntax.Assumption ::
                               quals  in
                             let decl =
                               let uu___213_11491 = se  in
                               {
                                 FStar_Syntax_Syntax.sigel =
                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                      (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                        (lb.FStar_Syntax_Syntax.lbtyp)));
                                 FStar_Syntax_Syntax.sigrng =
                                   (uu___213_11491.FStar_Syntax_Syntax.sigrng);
                                 FStar_Syntax_Syntax.sigquals = quals1;
                                 FStar_Syntax_Syntax.sigmeta =
                                   (uu___213_11491.FStar_Syntax_Syntax.sigmeta);
                                 FStar_Syntax_Syntax.sigattrs =
                                   (uu___213_11491.FStar_Syntax_Syntax.sigattrs)
                               }  in
                             FStar_Util.smap_add (sigmap env)
                               lid.FStar_Ident.str (decl, false)))
                   else ())
              | uu____11497 -> ()));
      (let curmod =
         let uu____11499 = current_module env  in uu____11499.FStar_Ident.str
          in
       (let uu____11501 =
          let uu____11604 = get_exported_id_set env curmod  in
          let uu____11654 = get_trans_exported_id_set env curmod  in
          (uu____11604, uu____11654)  in
        match uu____11501 with
        | (FStar_Pervasives_Native.Some cur_ex,FStar_Pervasives_Native.Some
           cur_trans_ex) ->
            let update_exports eikind =
              let cur_ex_set =
                let uu____12099 = cur_ex eikind  in
                FStar_ST.op_Bang uu____12099  in
              let cur_trans_ex_set_ref = cur_trans_ex eikind  in
              let uu____12298 =
                let uu____12301 = FStar_ST.op_Bang cur_trans_ex_set_ref  in
                FStar_Util.set_union cur_ex_set uu____12301  in
              FStar_ST.op_Colon_Equals cur_trans_ex_set_ref uu____12298  in
            FStar_List.iter update_exports all_exported_id_kinds
        | uu____12438 -> ());
       (match () with
        | () ->
            (filter_record_cache ();
             (match () with
              | () ->
                  let uu___214_12542 = env  in
                  {
                    curmodule = FStar_Pervasives_Native.None;
                    curmonad = (uu___214_12542.curmonad);
                    modules = (((modul.FStar_Syntax_Syntax.name), modul) ::
                      (env.modules));
                    scope_mods = [];
                    exported_ids = (uu___214_12542.exported_ids);
                    trans_exported_ids = (uu___214_12542.trans_exported_ids);
                    includes = (uu___214_12542.includes);
                    sigaccum = [];
                    sigmap = (uu___214_12542.sigmap);
                    iface = (uu___214_12542.iface);
                    admitted_iface = (uu___214_12542.admitted_iface);
                    expect_typ = (uu___214_12542.expect_typ);
                    docs = (uu___214_12542.docs);
                    remaining_iface_decls =
                      (uu___214_12542.remaining_iface_decls);
                    syntax_only = (uu___214_12542.syntax_only);
                    ds_hooks = (uu___214_12542.ds_hooks)
                  }))))
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push : env -> env) =
  fun env  ->
    FStar_Util.atomically
      (fun uu____12578  ->
         push_record_cache ();
         (let uu____12581 =
            let uu____12584 = FStar_ST.op_Bang stack  in env :: uu____12584
             in
          FStar_ST.op_Colon_Equals stack uu____12581);
         (let uu___215_12641 = env  in
          let uu____12642 = FStar_Util.smap_copy env.exported_ids  in
          let uu____12647 = FStar_Util.smap_copy env.trans_exported_ids  in
          let uu____12652 = FStar_Util.smap_copy env.includes  in
          let uu____12663 = FStar_Util.smap_copy env.sigmap  in
          let uu____12674 = FStar_Util.smap_copy env.docs  in
          {
            curmodule = (uu___215_12641.curmodule);
            curmonad = (uu___215_12641.curmonad);
            modules = (uu___215_12641.modules);
            scope_mods = (uu___215_12641.scope_mods);
            exported_ids = uu____12642;
            trans_exported_ids = uu____12647;
            includes = uu____12652;
            sigaccum = (uu___215_12641.sigaccum);
            sigmap = uu____12663;
            iface = (uu___215_12641.iface);
            admitted_iface = (uu___215_12641.admitted_iface);
            expect_typ = (uu___215_12641.expect_typ);
            docs = uu____12674;
            remaining_iface_decls = (uu___215_12641.remaining_iface_decls);
            syntax_only = (uu___215_12641.syntax_only);
            ds_hooks = (uu___215_12641.ds_hooks)
          }))
  
let (pop : unit -> env) =
  fun uu____12681  ->
    FStar_Util.atomically
      (fun uu____12688  ->
         let uu____12689 = FStar_ST.op_Bang stack  in
         match uu____12689 with
         | env::tl1 ->
             (pop_record_cache (); FStar_ST.op_Colon_Equals stack tl1; env)
         | uu____12752 -> failwith "Impossible: Too many pops")
  
let (snapshot : env -> (Prims.int,env) FStar_Pervasives_Native.tuple2) =
  fun env  -> FStar_Common.snapshot push stack env 
let (rollback : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth  -> FStar_Common.rollback pop stack depth 
let (export_interface : FStar_Ident.lident -> env -> env) =
  fun m  ->
    fun env  ->
      let sigelt_in_m se =
        match FStar_Syntax_Util.lids_of_sigelt se with
        | l::uu____12790 -> l.FStar_Ident.nsstr = m.FStar_Ident.str
        | uu____12793 -> false  in
      let sm = sigmap env  in
      let env1 = pop ()  in
      let keys = FStar_Util.smap_keys sm  in
      let sm' = sigmap env1  in
      FStar_All.pipe_right keys
        (FStar_List.iter
           (fun k  ->
              let uu____12827 = FStar_Util.smap_try_find sm' k  in
              match uu____12827 with
              | FStar_Pervasives_Native.Some (se,true ) when sigelt_in_m se
                  ->
                  (FStar_Util.smap_remove sm' k;
                   (let se1 =
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t) ->
                          let uu___216_12852 = se  in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (uu___216_12852.FStar_Syntax_Syntax.sigel);
                            FStar_Syntax_Syntax.sigrng =
                              (uu___216_12852.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (FStar_Syntax_Syntax.Assumption ::
                              (se.FStar_Syntax_Syntax.sigquals));
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___216_12852.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___216_12852.FStar_Syntax_Syntax.sigattrs)
                          }
                      | uu____12853 -> se  in
                    FStar_Util.smap_add sm' k (se1, false)))
              | uu____12858 -> ()));
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
      let uu____12881 = finish env modul1  in (uu____12881, modul1)
  
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
      let uu____12969 =
        let uu____12972 = e Exported_id_term_type  in
        FStar_ST.op_Bang uu____12972  in
      FStar_Util.set_elements uu____12969  in
    let fields =
      let uu____13094 =
        let uu____13097 = e Exported_id_field  in
        FStar_ST.op_Bang uu____13097  in
      FStar_Util.set_elements uu____13094  in
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
          let uu____13256 =
            FStar_Util.as_set e1.exported_id_terms FStar_Util.compare  in
          FStar_Util.mk_ref uu____13256  in
        let fields =
          let uu____13266 =
            FStar_Util.as_set e1.exported_id_fields FStar_Util.compare  in
          FStar_Util.mk_ref uu____13266  in
        (fun uu___191_13271  ->
           match uu___191_13271 with
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
  'Auu____13402 .
    'Auu____13402 Prims.list FStar_Pervasives_Native.option ->
      'Auu____13402 Prims.list FStar_ST.ref
  =
  fun uu___192_13415  ->
    match uu___192_13415 with
    | FStar_Pervasives_Native.None  -> FStar_Util.mk_ref []
    | FStar_Pervasives_Native.Some l -> FStar_Util.mk_ref l
  
let (inclusion_info : env -> FStar_Ident.lident -> module_inclusion_info) =
  fun env  ->
    fun l  ->
      let mname = FStar_Ident.string_of_lid l  in
      let as_ids_opt m =
        let uu____13456 = FStar_Util.smap_try_find m mname  in
        FStar_Util.map_opt uu____13456 as_exported_ids  in
      let uu____13462 = as_ids_opt env.exported_ids  in
      let uu____13465 = as_ids_opt env.trans_exported_ids  in
      let uu____13468 =
        let uu____13473 = FStar_Util.smap_try_find env.includes mname  in
        FStar_Util.map_opt uu____13473 (fun r  -> FStar_ST.op_Bang r)  in
      {
        mii_exported_ids = uu____13462;
        mii_trans_exported_ids = uu____13465;
        mii_includes = uu____13468
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
                let uu____13592 = FStar_Ident.text_of_lid mname  in
                FStar_Util.strcat uu____13592 ".fst"  in
              let auto_open =
                FStar_Parser_Dep.hard_coded_dependencies filename  in
              let auto_open1 =
                let convert_kind uu___193_13612 =
                  match uu___193_13612 with
                  | FStar_Parser_Dep.Open_namespace  -> Open_namespace
                  | FStar_Parser_Dep.Open_module  -> Open_module  in
                FStar_List.map
                  (fun uu____13624  ->
                     match uu____13624 with
                     | (lid,kind) -> (lid, (convert_kind kind))) auto_open
                 in
              let namespace_of_module =
                if
                  (FStar_List.length mname.FStar_Ident.ns) >
                    (Prims.parse_int "0")
                then
                  let uu____13648 =
                    let uu____13653 =
                      FStar_Ident.lid_of_ids mname.FStar_Ident.ns  in
                    (uu____13653, Open_namespace)  in
                  [uu____13648]
                else []  in
              let auto_open2 =
                FStar_List.append namespace_of_module
                  (FStar_List.rev auto_open1)
                 in
              (let uu____13683 = as_exported_id_set mii.mii_exported_ids  in
               FStar_Util.smap_add env1.exported_ids mname.FStar_Ident.str
                 uu____13683);
              (match () with
               | () ->
                   ((let uu____13710 =
                       as_exported_id_set mii.mii_trans_exported_ids  in
                     FStar_Util.smap_add env1.trans_exported_ids
                       mname.FStar_Ident.str uu____13710);
                    (match () with
                     | () ->
                         ((let uu____13737 = as_includes mii.mii_includes  in
                           FStar_Util.smap_add env1.includes
                             mname.FStar_Ident.str uu____13737);
                          (match () with
                           | () ->
                               let env' =
                                 let uu___217_13769 = env1  in
                                 let uu____13770 =
                                   FStar_List.map
                                     (fun x  -> Open_module_or_namespace x)
                                     auto_open2
                                    in
                                 {
                                   curmodule =
                                     (FStar_Pervasives_Native.Some mname);
                                   curmonad = (uu___217_13769.curmonad);
                                   modules = (uu___217_13769.modules);
                                   scope_mods = uu____13770;
                                   exported_ids =
                                     (uu___217_13769.exported_ids);
                                   trans_exported_ids =
                                     (uu___217_13769.trans_exported_ids);
                                   includes = (uu___217_13769.includes);
                                   sigaccum = (uu___217_13769.sigaccum);
                                   sigmap = (env1.sigmap);
                                   iface = intf;
                                   admitted_iface = admitted;
                                   expect_typ = (uu___217_13769.expect_typ);
                                   docs = (uu___217_13769.docs);
                                   remaining_iface_decls =
                                     (uu___217_13769.remaining_iface_decls);
                                   syntax_only = (uu___217_13769.syntax_only);
                                   ds_hooks = (uu___217_13769.ds_hooks)
                                 }  in
                               (FStar_List.iter
                                  (fun op  ->
                                     (env1.ds_hooks).ds_push_open_hook env'
                                       op) (FStar_List.rev auto_open2);
                                env'))))))
               in
            let uu____13782 =
              FStar_All.pipe_right env.modules
                (FStar_Util.find_opt
                   (fun uu____13808  ->
                      match uu____13808 with
                      | (l,uu____13814) -> FStar_Ident.lid_equals l mname))
               in
            match uu____13782 with
            | FStar_Pervasives_Native.None  ->
                let uu____13823 = prep env  in (uu____13823, false)
            | FStar_Pervasives_Native.Some (uu____13824,m) ->
                ((let uu____13831 =
                    (let uu____13834 = FStar_Options.interactive ()  in
                     Prims.op_Negation uu____13834) &&
                      ((Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)
                         || intf)
                     in
                  if uu____13831
                  then
                    let uu____13835 =
                      let uu____13840 =
                        FStar_Util.format1
                          "Duplicate module or interface name: %s"
                          mname.FStar_Ident.str
                         in
                      (FStar_Errors.Fatal_DuplicateModuleOrInterface,
                        uu____13840)
                       in
                    let uu____13841 = FStar_Ident.range_of_lid mname  in
                    FStar_Errors.raise_error uu____13835 uu____13841
                  else ());
                 (let uu____13843 =
                    let uu____13844 = push env  in prep uu____13844  in
                  (uu____13843, true)))
  
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
          let uu___218_13856 = env  in
          {
            curmodule = (uu___218_13856.curmodule);
            curmonad = (FStar_Pervasives_Native.Some mname);
            modules = (uu___218_13856.modules);
            scope_mods = (uu___218_13856.scope_mods);
            exported_ids = (uu___218_13856.exported_ids);
            trans_exported_ids = (uu___218_13856.trans_exported_ids);
            includes = (uu___218_13856.includes);
            sigaccum = (uu___218_13856.sigaccum);
            sigmap = (uu___218_13856.sigmap);
            iface = (uu___218_13856.iface);
            admitted_iface = (uu___218_13856.admitted_iface);
            expect_typ = (uu___218_13856.expect_typ);
            docs = (uu___218_13856.docs);
            remaining_iface_decls = (uu___218_13856.remaining_iface_decls);
            syntax_only = (uu___218_13856.syntax_only);
            ds_hooks = (uu___218_13856.ds_hooks)
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
        let uu____13890 = lookup1 lid  in
        match uu____13890 with
        | FStar_Pervasives_Native.None  ->
            let opened_modules =
              FStar_List.map
                (fun uu____13903  ->
                   match uu____13903 with
                   | (lid1,uu____13909) -> FStar_Ident.text_of_lid lid1)
                env.modules
               in
            let msg =
              let uu____13911 = FStar_Ident.text_of_lid lid  in
              FStar_Util.format1 "Identifier not found: [%s]" uu____13911  in
            let msg1 =
              if
                (FStar_List.length lid.FStar_Ident.ns) =
                  (Prims.parse_int "0")
              then msg
              else
                (let modul =
                   let uu____13915 =
                     FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
                   let uu____13916 = FStar_Ident.range_of_lid lid  in
                   FStar_Ident.set_lid_range uu____13915 uu____13916  in
                 let uu____13917 = resolve_module_name env modul true  in
                 match uu____13917 with
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
            let uu____13926 = FStar_Ident.range_of_lid lid  in
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_IdentifierNotFound, msg1) uu____13926
        | FStar_Pervasives_Native.Some r -> r
  
let fail_or2 :
  'a .
    (FStar_Ident.ident -> 'a FStar_Pervasives_Native.option) ->
      FStar_Ident.ident -> 'a
  =
  fun lookup1  ->
    fun id1  ->
      let uu____13954 = lookup1 id1  in
      match uu____13954 with
      | FStar_Pervasives_Native.None  ->
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_IdentifierNotFound,
              (Prims.strcat "Identifier not found ["
                 (Prims.strcat id1.FStar_Ident.idText "]")))
            id1.FStar_Ident.idRange
      | FStar_Pervasives_Native.Some r -> r
  