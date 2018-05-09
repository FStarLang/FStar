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
      let uu___139_1845 = env  in
      {
        curmodule = (uu___139_1845.curmodule);
        curmonad = (uu___139_1845.curmonad);
        modules = (uu___139_1845.modules);
        scope_mods = (uu___139_1845.scope_mods);
        exported_ids = (uu___139_1845.exported_ids);
        trans_exported_ids = (uu___139_1845.trans_exported_ids);
        includes = (uu___139_1845.includes);
        sigaccum = (uu___139_1845.sigaccum);
        sigmap = (uu___139_1845.sigmap);
        iface = b;
        admitted_iface = (uu___139_1845.admitted_iface);
        expect_typ = (uu___139_1845.expect_typ);
        docs = (uu___139_1845.docs);
        remaining_iface_decls = (uu___139_1845.remaining_iface_decls);
        syntax_only = (uu___139_1845.syntax_only);
        ds_hooks = (uu___139_1845.ds_hooks)
      }
  
let (iface : env -> Prims.bool) = fun e  -> e.iface 
let (set_admitted_iface : env -> Prims.bool -> env) =
  fun e  ->
    fun b  ->
      let uu___140_1861 = e  in
      {
        curmodule = (uu___140_1861.curmodule);
        curmonad = (uu___140_1861.curmonad);
        modules = (uu___140_1861.modules);
        scope_mods = (uu___140_1861.scope_mods);
        exported_ids = (uu___140_1861.exported_ids);
        trans_exported_ids = (uu___140_1861.trans_exported_ids);
        includes = (uu___140_1861.includes);
        sigaccum = (uu___140_1861.sigaccum);
        sigmap = (uu___140_1861.sigmap);
        iface = (uu___140_1861.iface);
        admitted_iface = b;
        expect_typ = (uu___140_1861.expect_typ);
        docs = (uu___140_1861.docs);
        remaining_iface_decls = (uu___140_1861.remaining_iface_decls);
        syntax_only = (uu___140_1861.syntax_only);
        ds_hooks = (uu___140_1861.ds_hooks)
      }
  
let (admitted_iface : env -> Prims.bool) = fun e  -> e.admitted_iface 
let (set_expect_typ : env -> Prims.bool -> env) =
  fun e  ->
    fun b  ->
      let uu___141_1877 = e  in
      {
        curmodule = (uu___141_1877.curmodule);
        curmonad = (uu___141_1877.curmonad);
        modules = (uu___141_1877.modules);
        scope_mods = (uu___141_1877.scope_mods);
        exported_ids = (uu___141_1877.exported_ids);
        trans_exported_ids = (uu___141_1877.trans_exported_ids);
        includes = (uu___141_1877.includes);
        sigaccum = (uu___141_1877.sigaccum);
        sigmap = (uu___141_1877.sigmap);
        iface = (uu___141_1877.iface);
        admitted_iface = (uu___141_1877.admitted_iface);
        expect_typ = b;
        docs = (uu___141_1877.docs);
        remaining_iface_decls = (uu___141_1877.remaining_iface_decls);
        syntax_only = (uu___141_1877.syntax_only);
        ds_hooks = (uu___141_1877.ds_hooks)
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
      (fun uu___108_2056  ->
         match uu___108_2056 with
         | Open_module_or_namespace (lid,_info) ->
             FStar_Pervasives_Native.Some lid
         | uu____2061 -> FStar_Pervasives_Native.None) env.scope_mods
  
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun e  ->
    fun l  ->
      let uu___142_2072 = e  in
      {
        curmodule = (FStar_Pervasives_Native.Some l);
        curmonad = (uu___142_2072.curmonad);
        modules = (uu___142_2072.modules);
        scope_mods = (uu___142_2072.scope_mods);
        exported_ids = (uu___142_2072.exported_ids);
        trans_exported_ids = (uu___142_2072.trans_exported_ids);
        includes = (uu___142_2072.includes);
        sigaccum = (uu___142_2072.sigaccum);
        sigmap = (uu___142_2072.sigmap);
        iface = (uu___142_2072.iface);
        admitted_iface = (uu___142_2072.admitted_iface);
        expect_typ = (uu___142_2072.expect_typ);
        docs = (uu___142_2072.docs);
        remaining_iface_decls = (uu___142_2072.remaining_iface_decls);
        syntax_only = (uu___142_2072.syntax_only);
        ds_hooks = (uu___142_2072.ds_hooks)
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
            let uu___143_2262 = env  in
            {
              curmodule = (uu___143_2262.curmodule);
              curmonad = (uu___143_2262.curmonad);
              modules = (uu___143_2262.modules);
              scope_mods = (uu___143_2262.scope_mods);
              exported_ids = (uu___143_2262.exported_ids);
              trans_exported_ids = (uu___143_2262.trans_exported_ids);
              includes = (uu___143_2262.includes);
              sigaccum = (uu___143_2262.sigaccum);
              sigmap = (uu___143_2262.sigmap);
              iface = (uu___143_2262.iface);
              admitted_iface = (uu___143_2262.admitted_iface);
              expect_typ = (uu___143_2262.expect_typ);
              docs = (uu___143_2262.docs);
              remaining_iface_decls = ((l, ds) :: rest);
              syntax_only = (uu___143_2262.syntax_only);
              ds_hooks = (uu___143_2262.ds_hooks)
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
      let uu___144_2308 = env  in
      {
        curmodule = (uu___144_2308.curmodule);
        curmonad = (uu___144_2308.curmonad);
        modules = (uu___144_2308.modules);
        scope_mods = (uu___144_2308.scope_mods);
        exported_ids = (uu___144_2308.exported_ids);
        trans_exported_ids = (uu___144_2308.trans_exported_ids);
        includes = (uu___144_2308.includes);
        sigaccum = (uu___144_2308.sigaccum);
        sigmap = (uu___144_2308.sigmap);
        iface = (uu___144_2308.iface);
        admitted_iface = (uu___144_2308.admitted_iface);
        expect_typ = (uu___144_2308.expect_typ);
        docs = (uu___144_2308.docs);
        remaining_iface_decls = (uu___144_2308.remaining_iface_decls);
        syntax_only = b;
        ds_hooks = (uu___144_2308.ds_hooks)
      }
  
let (ds_hooks : env -> dsenv_hooks) = fun env  -> env.ds_hooks 
let (set_ds_hooks : env -> dsenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___145_2324 = env  in
      {
        curmodule = (uu___145_2324.curmodule);
        curmonad = (uu___145_2324.curmonad);
        modules = (uu___145_2324.modules);
        scope_mods = (uu___145_2324.scope_mods);
        exported_ids = (uu___145_2324.exported_ids);
        trans_exported_ids = (uu___145_2324.trans_exported_ids);
        includes = (uu___145_2324.includes);
        sigaccum = (uu___145_2324.sigaccum);
        sigmap = (uu___145_2324.sigmap);
        iface = (uu___145_2324.iface);
        admitted_iface = (uu___145_2324.admitted_iface);
        expect_typ = (uu___145_2324.expect_typ);
        docs = (uu___145_2324.docs);
        remaining_iface_decls = (uu___145_2324.remaining_iface_decls);
        syntax_only = (uu___145_2324.syntax_only);
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
        let uu___146_2428 = bv.FStar_Syntax_Syntax.ppname  in
        {
          FStar_Ident.idText = (uu___146_2428.FStar_Ident.idText);
          FStar_Ident.idRange = r
        }  in
      let uu___147_2429 = bv  in
      {
        FStar_Syntax_Syntax.ppname = id1;
        FStar_Syntax_Syntax.index = (uu___147_2429.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = (uu___147_2429.FStar_Syntax_Syntax.sort)
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
    fun uu___109_2671  ->
      match uu___109_2671 with
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
  fun uu___110_2810  ->
    match uu___110_2810 with
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
              let rec aux uu___111_2881 =
                match uu___111_2881 with
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
  fun uu___112_3130  ->
    match uu___112_3130 with
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
                  let check_local_binding_id uu___113_3252 =
                    match uu___113_3252 with
                    | (id',uu____3254,uu____3255) ->
                        id'.FStar_Ident.idText = id1.FStar_Ident.idText
                     in
                  let check_rec_binding_id uu___114_3261 =
                    match uu___114_3261 with
                    | (id',uu____3263,uu____3264) ->
                        id'.FStar_Ident.idText = id1.FStar_Ident.idText
                     in
                  let curmod_ns =
                    let uu____3268 = current_module env  in
                    FStar_Ident.ids_of_lid uu____3268  in
                  let proc uu___115_3276 =
                    match uu___115_3276 with
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
                  let rec aux uu___116_3299 =
                    match uu___116_3299 with
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
        let rec aux uu___117_3726 =
          match uu___117_3726 with
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
          | uu____3762::q -> aux q  in
        aux env.scope_mods
  
let (fail_if_curmodule :
  env -> FStar_Ident.lident -> FStar_Ident.lident -> unit) =
  fun env  ->
    fun ns_original  ->
      fun ns_resolved  ->
        let uu____3781 =
          let uu____3782 = current_module env  in
          FStar_Ident.lid_equals ns_resolved uu____3782  in
        if uu____3781
        then
          let uu____3783 =
            FStar_Ident.lid_equals ns_resolved FStar_Parser_Const.prims_lid
             in
          (if uu____3783
           then ()
           else
             (let uu____3785 =
                let uu____3790 =
                  FStar_Util.format1
                    "Reference %s to current module is forbidden (see GitHub issue #451)"
                    ns_original.FStar_Ident.str
                   in
                (FStar_Errors.Fatal_ForbiddenReferenceToCurrentModule,
                  uu____3790)
                 in
              let uu____3791 = FStar_Ident.range_of_lid ns_original  in
              FStar_Errors.raise_error uu____3785 uu____3791))
        else ()
  
let (fail_if_qualified_by_curmodule : env -> FStar_Ident.lident -> unit) =
  fun env  ->
    fun lid  ->
      match lid.FStar_Ident.ns with
      | [] -> ()
      | uu____3803 ->
          let modul_orig = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          let uu____3807 = resolve_module_name env modul_orig true  in
          (match uu____3807 with
           | FStar_Pervasives_Native.Some modul_res ->
               fail_if_curmodule env modul_orig modul_res
           | uu____3811 -> ())
  
let (is_open : env -> FStar_Ident.lident -> open_kind -> Prims.bool) =
  fun env  ->
    fun lid  ->
      fun open_kind  ->
        FStar_List.existsb
          (fun uu___118_3832  ->
             match uu___118_3832 with
             | Open_module_or_namespace (ns,k) ->
                 (k = open_kind) && (FStar_Ident.lid_equals lid ns)
             | uu____3835 -> false) env.scope_mods
  
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
                 let uu____3954 = aux rev_ns_prefix ns_last_id  in
                 FStar_All.pipe_right uu____3954
                   (FStar_Util.map_option
                      (fun uu____4004  ->
                         match uu____4004 with
                         | (stripped_ids,rev_kept_ids) ->
                             (stripped_ids, (id1 :: rev_kept_ids)))))
           in
        let do_shorten env1 ids1 =
          match FStar_List.rev ids1 with
          | [] -> ([], [])
          | ns_last_id::ns_rev_prefix ->
              let uu____4074 = aux ns_rev_prefix ns_last_id  in
              (match uu____4074 with
               | FStar_Pervasives_Native.None  -> ([], ids1)
               | FStar_Pervasives_Native.Some (stripped_ids,rev_kept_ids) ->
                   (stripped_ids, (FStar_List.rev rev_kept_ids)))
           in
        if is_full_path
        then
          let uu____4135 =
            let uu____4138 = FStar_Ident.lid_of_ids ids  in
            resolve_module_name env uu____4138 true  in
          match uu____4135 with
          | FStar_Pervasives_Native.Some m when module_is_open env m ->
              (ids, [])
          | uu____4152 -> do_shorten env ids
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
                  | uu____4271::uu____4272 ->
                      let uu____4275 =
                        let uu____4278 =
                          let uu____4279 =
                            FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
                          let uu____4280 = FStar_Ident.range_of_lid lid  in
                          FStar_Ident.set_lid_range uu____4279 uu____4280  in
                        resolve_module_name env uu____4278 true  in
                      (match uu____4275 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some modul ->
                           let uu____4284 =
                             find_in_module_with_includes eikind f_module
                               Cont_fail env modul lid.FStar_Ident.ident
                              in
                           option_of_cont
                             (fun uu____4288  -> FStar_Pervasives_Native.None)
                             uu____4284)
                  | [] ->
                      try_lookup_id'' env lid.FStar_Ident.ident eikind
                        k_local_binding k_rec_binding k_record f_module
                        l_default
  
let cont_of_option :
  'a . 'a cont_t -> 'a FStar_Pervasives_Native.option -> 'a cont_t =
  fun k_none  ->
    fun uu___119_4311  ->
      match uu___119_4311 with
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
              let uu____4427 = k_global_def lid1 def  in
              cont_of_option k uu____4427  in
            let f_module lid' =
              let k = Cont_ignore  in
              find_in_module env lid' (k_global_def' k) k  in
            let l_default k i = lookup_default_id env i (k_global_def' k) k
               in
            resolve_in_open_namespaces'' env lid Exported_id_term_type
              (fun l  ->
                 let uu____4463 = k_local_binding l  in
                 cont_of_option Cont_fail uu____4463)
              (fun r  ->
                 let uu____4469 = k_rec_binding r  in
                 cont_of_option Cont_fail uu____4469)
              (fun uu____4473  -> Cont_ignore) f_module l_default
  
let (fv_qual_of_se :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option)
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____4483,uu____4484,uu____4485,l,uu____4487,uu____4488) ->
        let qopt =
          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
            (fun uu___120_4499  ->
               match uu___120_4499 with
               | FStar_Syntax_Syntax.RecordConstructor (uu____4502,fs) ->
                   FStar_Pervasives_Native.Some
                     (FStar_Syntax_Syntax.Record_ctor (l, fs))
               | uu____4514 -> FStar_Pervasives_Native.None)
           in
        (match qopt with
         | FStar_Pervasives_Native.None  ->
             FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor
         | x -> x)
    | FStar_Syntax_Syntax.Sig_declare_typ (uu____4520,uu____4521,uu____4522)
        -> FStar_Pervasives_Native.None
    | uu____4523 -> FStar_Pervasives_Native.None
  
let (lb_fv :
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Ident.lident -> FStar_Syntax_Syntax.fv)
  =
  fun lbs  ->
    fun lid  ->
      let uu____4538 =
        FStar_Util.find_map lbs
          (fun lb  ->
             let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
             let uu____4546 = FStar_Syntax_Syntax.fv_eq_lid fv lid  in
             if uu____4546
             then FStar_Pervasives_Native.Some fv
             else FStar_Pervasives_Native.None)
         in
      FStar_All.pipe_right uu____4538 FStar_Util.must
  
let (ns_of_lid_equals :
  FStar_Ident.lident -> FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    fun ns  ->
      (let uu____4564 =
         let uu____4565 = FStar_Ident.ids_of_lid ns  in
         FStar_List.length uu____4565  in
       (FStar_List.length lid.FStar_Ident.ns) = uu____4564) &&
        (let uu____4573 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
         FStar_Ident.lid_equals uu____4573 ns)
  
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
          let k_global_def source_lid uu___125_4615 =
            match uu___125_4615 with
            | (uu____4622,true ) when exclude_interf ->
                FStar_Pervasives_Native.None
            | (se,uu____4624) ->
                (match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_inductive_typ uu____4627 ->
                     let uu____4644 =
                       let uu____4645 =
                         let uu____4654 =
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None
                            in
                         (uu____4654, false,
                           (se.FStar_Syntax_Syntax.sigattrs))
                          in
                       Term_name uu____4645  in
                     FStar_Pervasives_Native.Some uu____4644
                 | FStar_Syntax_Syntax.Sig_datacon uu____4657 ->
                     let uu____4672 =
                       let uu____4673 =
                         let uu____4682 =
                           let uu____4683 = fv_qual_of_se se  in
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.delta_constant uu____4683
                            in
                         (uu____4682, false,
                           (se.FStar_Syntax_Syntax.sigattrs))
                          in
                       Term_name uu____4673  in
                     FStar_Pervasives_Native.Some uu____4672
                 | FStar_Syntax_Syntax.Sig_let ((uu____4688,lbs),uu____4690)
                     ->
                     let fv = lb_fv lbs source_lid  in
                     let uu____4700 =
                       let uu____4701 =
                         let uu____4710 =
                           FStar_Syntax_Syntax.fvar source_lid
                             fv.FStar_Syntax_Syntax.fv_delta
                             fv.FStar_Syntax_Syntax.fv_qual
                            in
                         (uu____4710, false,
                           (se.FStar_Syntax_Syntax.sigattrs))
                          in
                       Term_name uu____4701  in
                     FStar_Pervasives_Native.Some uu____4700
                 | FStar_Syntax_Syntax.Sig_declare_typ
                     (lid1,uu____4714,uu____4715) ->
                     let quals = se.FStar_Syntax_Syntax.sigquals  in
                     let uu____4719 =
                       any_val ||
                         (FStar_All.pipe_right quals
                            (FStar_Util.for_some
                               (fun uu___121_4723  ->
                                  match uu___121_4723 with
                                  | FStar_Syntax_Syntax.Assumption  -> true
                                  | uu____4724 -> false)))
                        in
                     if uu____4719
                     then
                       let lid2 =
                         let uu____4728 = FStar_Ident.range_of_lid source_lid
                            in
                         FStar_Ident.set_lid_range lid1 uu____4728  in
                       let dd =
                         let uu____4730 =
                           (FStar_Syntax_Util.is_primop_lid lid2) ||
                             (FStar_All.pipe_right quals
                                (FStar_Util.for_some
                                   (fun uu___122_4735  ->
                                      match uu___122_4735 with
                                      | FStar_Syntax_Syntax.Projector
                                          uu____4736 -> true
                                      | FStar_Syntax_Syntax.Discriminator
                                          uu____4741 -> true
                                      | uu____4742 -> false)))
                            in
                         if uu____4730
                         then FStar_Syntax_Syntax.delta_equational
                         else FStar_Syntax_Syntax.delta_constant  in
                       let dd1 =
                         let uu____4745 =
                           FStar_All.pipe_right quals
                             (FStar_Util.for_some
                                (fun uu___123_4749  ->
                                   match uu___123_4749 with
                                   | FStar_Syntax_Syntax.Abstract  -> true
                                   | uu____4750 -> false))
                            in
                         if uu____4745
                         then FStar_Syntax_Syntax.Delta_abstract dd
                         else dd  in
                       let uu____4752 =
                         FStar_Util.find_map quals
                           (fun uu___124_4757  ->
                              match uu___124_4757 with
                              | FStar_Syntax_Syntax.Reflectable refl_monad ->
                                  FStar_Pervasives_Native.Some refl_monad
                              | uu____4761 -> FStar_Pervasives_Native.None)
                          in
                       (match uu____4752 with
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
                        | uu____4770 ->
                            let uu____4773 =
                              let uu____4774 =
                                let uu____4783 =
                                  let uu____4784 = fv_qual_of_se se  in
                                  FStar_Syntax_Syntax.fvar lid2 dd1
                                    uu____4784
                                   in
                                (uu____4783, false,
                                  (se.FStar_Syntax_Syntax.sigattrs))
                                 in
                              Term_name uu____4774  in
                            FStar_Pervasives_Native.Some uu____4773)
                     else FStar_Pervasives_Native.None
                 | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
                     let uu____4791 =
                       let uu____4792 =
                         let uu____4797 =
                           let uu____4798 =
                             FStar_Ident.range_of_lid source_lid  in
                           FStar_Ident.set_lid_range
                             ne.FStar_Syntax_Syntax.mname uu____4798
                            in
                         (se, uu____4797)  in
                       Eff_name uu____4792  in
                     FStar_Pervasives_Native.Some uu____4791
                 | FStar_Syntax_Syntax.Sig_new_effect ne ->
                     let uu____4800 =
                       let uu____4801 =
                         let uu____4806 =
                           let uu____4807 =
                             FStar_Ident.range_of_lid source_lid  in
                           FStar_Ident.set_lid_range
                             ne.FStar_Syntax_Syntax.mname uu____4807
                            in
                         (se, uu____4806)  in
                       Eff_name uu____4801  in
                     FStar_Pervasives_Native.Some uu____4800
                 | FStar_Syntax_Syntax.Sig_effect_abbrev uu____4808 ->
                     FStar_Pervasives_Native.Some (Eff_name (se, source_lid))
                 | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
                     let uu____4827 =
                       let uu____4828 =
                         let uu____4837 =
                           FStar_Syntax_Syntax.fvar source_lid
                             (FStar_Syntax_Syntax.Delta_constant_at_level
                                (Prims.parse_int "1"))
                             FStar_Pervasives_Native.None
                            in
                         (uu____4837, false, [])  in
                       Term_name uu____4828  in
                     FStar_Pervasives_Native.Some uu____4827
                 | uu____4840 -> FStar_Pervasives_Native.None)
             in
          let k_local_binding r =
            let uu____4861 =
              let uu____4866 = FStar_Ident.range_of_lid lid  in
              found_local_binding uu____4866 r  in
            match uu____4861 with
            | (t,mut) ->
                FStar_Pervasives_Native.Some (Term_name (t, mut, []))
             in
          let k_rec_binding uu____4886 =
            match uu____4886 with
            | (id1,l,dd) ->
                let uu____4898 =
                  let uu____4899 =
                    let uu____4908 =
                      let uu____4909 =
                        let uu____4910 = FStar_Ident.range_of_lid lid  in
                        FStar_Ident.set_lid_range l uu____4910  in
                      FStar_Syntax_Syntax.fvar uu____4909 dd
                        FStar_Pervasives_Native.None
                       in
                    (uu____4908, false, [])  in
                  Term_name uu____4899  in
                FStar_Pervasives_Native.Some uu____4898
             in
          let found_unmangled =
            match lid.FStar_Ident.ns with
            | [] ->
                let uu____4918 = unmangleOpName lid.FStar_Ident.ident  in
                (match uu____4918 with
                 | FStar_Pervasives_Native.Some (t,mut) ->
                     FStar_Pervasives_Native.Some (Term_name (t, mut, []))
                 | uu____4935 -> FStar_Pervasives_Native.None)
            | uu____4942 -> FStar_Pervasives_Native.None  in
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
        let uu____4977 = try_lookup_name true exclude_interf env lid  in
        match uu____4977 with
        | FStar_Pervasives_Native.Some (Eff_name (o,l)) ->
            FStar_Pervasives_Native.Some (o, l)
        | uu____4992 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____5011 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____5011 with
      | FStar_Pervasives_Native.Some (o,l1) ->
          FStar_Pervasives_Native.Some l1
      | uu____5026 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_name_and_attributes :
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident,FStar_Syntax_Syntax.cflags Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____5051 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____5051 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____5067;
             FStar_Syntax_Syntax.sigquals = uu____5068;
             FStar_Syntax_Syntax.sigmeta = uu____5069;
             FStar_Syntax_Syntax.sigattrs = uu____5070;_},l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____5089;
             FStar_Syntax_Syntax.sigquals = uu____5090;
             FStar_Syntax_Syntax.sigmeta = uu____5091;
             FStar_Syntax_Syntax.sigattrs = uu____5092;_},l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (uu____5110,uu____5111,uu____5112,uu____5113,cattributes);
             FStar_Syntax_Syntax.sigrng = uu____5115;
             FStar_Syntax_Syntax.sigquals = uu____5116;
             FStar_Syntax_Syntax.sigmeta = uu____5117;
             FStar_Syntax_Syntax.sigattrs = uu____5118;_},l1)
          -> FStar_Pervasives_Native.Some (l1, cattributes)
      | uu____5140 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_defn :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.eff_decl FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____5165 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____5165 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____5175;
             FStar_Syntax_Syntax.sigquals = uu____5176;
             FStar_Syntax_Syntax.sigmeta = uu____5177;
             FStar_Syntax_Syntax.sigattrs = uu____5178;_},uu____5179)
          -> FStar_Pervasives_Native.Some ne
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____5189;
             FStar_Syntax_Syntax.sigquals = uu____5190;
             FStar_Syntax_Syntax.sigmeta = uu____5191;
             FStar_Syntax_Syntax.sigattrs = uu____5192;_},uu____5193)
          -> FStar_Pervasives_Native.Some ne
      | uu____5202 -> FStar_Pervasives_Native.None
  
let (is_effect_name : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____5219 = try_lookup_effect_name env lid  in
      match uu____5219 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____5222 -> true
  
let (try_lookup_root_effect_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____5235 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____5235 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (l',uu____5245,uu____5246,uu____5247,uu____5248);
             FStar_Syntax_Syntax.sigrng = uu____5249;
             FStar_Syntax_Syntax.sigquals = uu____5250;
             FStar_Syntax_Syntax.sigmeta = uu____5251;
             FStar_Syntax_Syntax.sigattrs = uu____5252;_},uu____5253)
          ->
          let rec aux new_name =
            let uu____5274 =
              FStar_Util.smap_try_find (sigmap env) new_name.FStar_Ident.str
               in
            match uu____5274 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (s,uu____5292) ->
                (match s.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
                     let uu____5300 =
                       let uu____5301 = FStar_Ident.range_of_lid l  in
                       FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname
                         uu____5301
                        in
                     FStar_Pervasives_Native.Some uu____5300
                 | FStar_Syntax_Syntax.Sig_new_effect ne ->
                     let uu____5303 =
                       let uu____5304 = FStar_Ident.range_of_lid l  in
                       FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname
                         uu____5304
                        in
                     FStar_Pervasives_Native.Some uu____5303
                 | FStar_Syntax_Syntax.Sig_effect_abbrev
                     (uu____5305,uu____5306,uu____5307,cmp,uu____5309) ->
                     let l'' = FStar_Syntax_Util.comp_effect_name cmp  in
                     aux l''
                 | uu____5315 -> FStar_Pervasives_Native.None)
             in
          aux l'
      | FStar_Pervasives_Native.Some (uu____5316,l') ->
          FStar_Pervasives_Native.Some l'
      | uu____5322 -> FStar_Pervasives_Native.None
  
let (lookup_letbinding_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___126_5359 =
        match uu___126_5359 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____5368,uu____5369,uu____5370);
             FStar_Syntax_Syntax.sigrng = uu____5371;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____5373;
             FStar_Syntax_Syntax.sigattrs = uu____5374;_},uu____5375)
            -> FStar_Pervasives_Native.Some quals
        | uu____5382 -> FStar_Pervasives_Native.None  in
      let uu____5389 =
        resolve_in_open_namespaces' env lid
          (fun uu____5397  -> FStar_Pervasives_Native.None)
          (fun uu____5401  -> FStar_Pervasives_Native.None) k_global_def
         in
      match uu____5389 with
      | FStar_Pervasives_Native.Some quals -> quals
      | uu____5411 -> []
  
let (try_lookup_module :
  env ->
    FStar_Ident.path ->
      FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun path  ->
      let uu____5428 =
        FStar_List.tryFind
          (fun uu____5443  ->
             match uu____5443 with
             | (mlid,modul) ->
                 let uu____5450 = FStar_Ident.path_of_lid mlid  in
                 uu____5450 = path) env.modules
         in
      match uu____5428 with
      | FStar_Pervasives_Native.Some (uu____5453,modul) ->
          FStar_Pervasives_Native.Some modul
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (try_lookup_let :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___127_5491 =
        match uu___127_5491 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               ((uu____5498,lbs),uu____5500);
             FStar_Syntax_Syntax.sigrng = uu____5501;
             FStar_Syntax_Syntax.sigquals = uu____5502;
             FStar_Syntax_Syntax.sigmeta = uu____5503;
             FStar_Syntax_Syntax.sigattrs = uu____5504;_},uu____5505)
            ->
            let fv = lb_fv lbs lid1  in
            let uu____5519 =
              FStar_Syntax_Syntax.fvar lid1 fv.FStar_Syntax_Syntax.fv_delta
                fv.FStar_Syntax_Syntax.fv_qual
               in
            FStar_Pervasives_Native.Some uu____5519
        | uu____5520 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____5526  -> FStar_Pervasives_Native.None)
        (fun uu____5528  -> FStar_Pervasives_Native.None) k_global_def
  
let (try_lookup_definition :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___128_5559 =
        match uu___128_5559 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               (lbs,uu____5569);
             FStar_Syntax_Syntax.sigrng = uu____5570;
             FStar_Syntax_Syntax.sigquals = uu____5571;
             FStar_Syntax_Syntax.sigmeta = uu____5572;
             FStar_Syntax_Syntax.sigattrs = uu____5573;_},uu____5574)
            ->
            FStar_Util.find_map (FStar_Pervasives_Native.snd lbs)
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inr fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv lid1 ->
                     FStar_Pervasives_Native.Some
                       (lb.FStar_Syntax_Syntax.lbdef)
                 | uu____5597 -> FStar_Pervasives_Native.None)
        | uu____5604 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____5614  -> FStar_Pervasives_Native.None)
        (fun uu____5618  -> FStar_Pervasives_Native.None) k_global_def
  
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
          let uu____5675 = try_lookup_name any_val exclude_interface env lid
             in
          match uu____5675 with
          | FStar_Pervasives_Native.Some (Term_name (e,mut,attrs)) ->
              FStar_Pervasives_Native.Some (e, mut, attrs)
          | uu____5705 -> FStar_Pervasives_Native.None
  
let (drop_attributes :
  (FStar_Syntax_Syntax.term,Prims.bool,FStar_Syntax_Syntax.attribute
                                         Prims.list)
    FStar_Pervasives_Native.tuple3 FStar_Pervasives_Native.option ->
    (FStar_Syntax_Syntax.term,Prims.bool) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option)
  =
  fun x  ->
    match x with
    | FStar_Pervasives_Native.Some (t,mut,uu____5761) ->
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
      let uu____5836 = try_lookup_lid_with_attributes env l  in
      FStar_All.pipe_right uu____5836 drop_attributes
  
let (resolve_to_fully_qualified_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____5875 = try_lookup_lid env l  in
      match uu____5875 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (e,uu____5889) ->
          let uu____5894 =
            let uu____5895 = FStar_Syntax_Subst.compress e  in
            uu____5895.FStar_Syntax_Syntax.n  in
          (match uu____5894 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               FStar_Pervasives_Native.Some
                 ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
           | uu____5901 -> FStar_Pervasives_Native.None)
  
let (shorten_lid' : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____5912 = shorten_module_path env lid.FStar_Ident.ns true  in
      match uu____5912 with
      | (uu____5921,short) ->
          FStar_Ident.lid_of_ns_and_id short lid.FStar_Ident.ident
  
let (shorten_lid : env -> FStar_Ident.lid -> FStar_Ident.lid) =
  fun env  ->
    fun lid  ->
      match env.curmodule with
      | FStar_Pervasives_Native.None  -> shorten_lid' env lid
      | uu____5941 ->
          let lid_without_ns =
            FStar_Ident.lid_of_ns_and_id [] lid.FStar_Ident.ident  in
          let uu____5945 = resolve_to_fully_qualified_name env lid_without_ns
             in
          (match uu____5945 with
           | FStar_Pervasives_Native.Some lid' when
               lid'.FStar_Ident.str = lid.FStar_Ident.str -> lid_without_ns
           | uu____5949 -> shorten_lid' env lid)
  
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
        let uu___148_5983 = env  in
        {
          curmodule = (uu___148_5983.curmodule);
          curmonad = (uu___148_5983.curmonad);
          modules = (uu___148_5983.modules);
          scope_mods = [];
          exported_ids = empty_exported_id_smap;
          trans_exported_ids = (uu___148_5983.trans_exported_ids);
          includes = empty_include_smap;
          sigaccum = (uu___148_5983.sigaccum);
          sigmap = (uu___148_5983.sigmap);
          iface = (uu___148_5983.iface);
          admitted_iface = (uu___148_5983.admitted_iface);
          expect_typ = (uu___148_5983.expect_typ);
          docs = (uu___148_5983.docs);
          remaining_iface_decls = (uu___148_5983.remaining_iface_decls);
          syntax_only = (uu___148_5983.syntax_only);
          ds_hooks = (uu___148_5983.ds_hooks)
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
      let uu____6006 = try_lookup_lid_with_attributes_no_resolve env l  in
      FStar_All.pipe_right uu____6006 drop_attributes
  
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
               (uu____6080,uu____6081,uu____6082);
             FStar_Syntax_Syntax.sigrng = uu____6083;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____6085;
             FStar_Syntax_Syntax.sigattrs = uu____6086;_},uu____6087)
            ->
            let uu____6092 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___129_6096  ->
                      match uu___129_6096 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | uu____6097 -> false))
               in
            if uu____6092
            then
              let uu____6100 =
                FStar_Syntax_Syntax.lid_as_fv lid1
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Pervasives_Native.Some uu____6100
            else FStar_Pervasives_Native.None
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
               uu____6102;
             FStar_Syntax_Syntax.sigrng = uu____6103;
             FStar_Syntax_Syntax.sigquals = uu____6104;
             FStar_Syntax_Syntax.sigmeta = uu____6105;
             FStar_Syntax_Syntax.sigattrs = uu____6106;_},uu____6107)
            ->
            let qual1 = fv_qual_of_se (FStar_Pervasives_Native.fst se)  in
            let uu____6129 =
              FStar_Syntax_Syntax.lid_as_fv lid1
                FStar_Syntax_Syntax.delta_constant qual1
               in
            FStar_Pervasives_Native.Some uu____6129
        | uu____6130 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____6136  -> FStar_Pervasives_Native.None)
        (fun uu____6138  -> FStar_Pervasives_Native.None) k_global_def
  
let (find_all_datacons :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___130_6171 =
        match uu___130_6171 with
        | ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_inductive_typ
               (uu____6180,uu____6181,uu____6182,uu____6183,datas,uu____6185);
             FStar_Syntax_Syntax.sigrng = uu____6186;
             FStar_Syntax_Syntax.sigquals = uu____6187;
             FStar_Syntax_Syntax.sigmeta = uu____6188;
             FStar_Syntax_Syntax.sigattrs = uu____6189;_},uu____6190)
            -> FStar_Pervasives_Native.Some datas
        | uu____6205 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____6215  -> FStar_Pervasives_Native.None)
        (fun uu____6219  -> FStar_Pervasives_Native.None) k_global_def
  
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
  let push1 uu____6295 =
    let uu____6296 =
      let uu____6301 =
        let uu____6304 = FStar_ST.op_Bang record_cache  in
        FStar_List.hd uu____6304  in
      let uu____6364 = FStar_ST.op_Bang record_cache  in uu____6301 ::
        uu____6364
       in
    FStar_ST.op_Colon_Equals record_cache uu____6296  in
  let pop1 uu____6482 =
    let uu____6483 =
      let uu____6488 = FStar_ST.op_Bang record_cache  in
      FStar_List.tl uu____6488  in
    FStar_ST.op_Colon_Equals record_cache uu____6483  in
  let snapshot1 uu____6610 = FStar_Common.snapshot push1 record_cache ()  in
  let rollback1 depth = FStar_Common.rollback pop1 record_cache depth  in
  let peek1 uu____6676 =
    let uu____6677 = FStar_ST.op_Bang record_cache  in
    FStar_List.hd uu____6677  in
  let insert r =
    let uu____6743 =
      let uu____6748 = let uu____6751 = peek1 ()  in r :: uu____6751  in
      let uu____6754 =
        let uu____6759 = FStar_ST.op_Bang record_cache  in
        FStar_List.tl uu____6759  in
      uu____6748 :: uu____6754  in
    FStar_ST.op_Colon_Equals record_cache uu____6743  in
  let filter1 uu____6879 =
    let rc = peek1 ()  in
    let filtered =
      FStar_List.filter
        (fun r  -> Prims.op_Negation r.is_private_or_abstract) rc
       in
    let uu____6888 =
      let uu____6893 =
        let uu____6898 = FStar_ST.op_Bang record_cache  in
        FStar_List.tl uu____6898  in
      filtered :: uu____6893  in
    FStar_ST.op_Colon_Equals record_cache uu____6888  in
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
        | FStar_Syntax_Syntax.Sig_bundle (sigs,uu____7847) ->
            let is_record =
              FStar_Util.for_some
                (fun uu___131_7865  ->
                   match uu___131_7865 with
                   | FStar_Syntax_Syntax.RecordType uu____7866 -> true
                   | FStar_Syntax_Syntax.RecordConstructor uu____7875 -> true
                   | uu____7884 -> false)
               in
            let find_dc dc =
              FStar_All.pipe_right sigs
                (FStar_Util.find_opt
                   (fun uu___132_7908  ->
                      match uu___132_7908 with
                      | {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_datacon
                            (lid,uu____7910,uu____7911,uu____7912,uu____7913,uu____7914);
                          FStar_Syntax_Syntax.sigrng = uu____7915;
                          FStar_Syntax_Syntax.sigquals = uu____7916;
                          FStar_Syntax_Syntax.sigmeta = uu____7917;
                          FStar_Syntax_Syntax.sigattrs = uu____7918;_} ->
                          FStar_Ident.lid_equals dc lid
                      | uu____7927 -> false))
               in
            FStar_All.pipe_right sigs
              (FStar_List.iter
                 (fun uu___133_7962  ->
                    match uu___133_7962 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ
                          (typename,univs1,parms,uu____7966,uu____7967,dc::[]);
                        FStar_Syntax_Syntax.sigrng = uu____7969;
                        FStar_Syntax_Syntax.sigquals = typename_quals;
                        FStar_Syntax_Syntax.sigmeta = uu____7971;
                        FStar_Syntax_Syntax.sigattrs = uu____7972;_} ->
                        let uu____7983 =
                          let uu____7984 = find_dc dc  in
                          FStar_All.pipe_left FStar_Util.must uu____7984  in
                        (match uu____7983 with
                         | {
                             FStar_Syntax_Syntax.sigel =
                               FStar_Syntax_Syntax.Sig_datacon
                               (constrname,uu____7990,t,uu____7992,uu____7993,uu____7994);
                             FStar_Syntax_Syntax.sigrng = uu____7995;
                             FStar_Syntax_Syntax.sigquals = uu____7996;
                             FStar_Syntax_Syntax.sigmeta = uu____7997;
                             FStar_Syntax_Syntax.sigattrs = uu____7998;_} ->
                             let uu____8007 =
                               FStar_Syntax_Util.arrow_formals t  in
                             (match uu____8007 with
                              | (formals,uu____8021) ->
                                  let is_rec = is_record typename_quals  in
                                  let formals' =
                                    FStar_All.pipe_right formals
                                      (FStar_List.collect
                                         (fun uu____8070  ->
                                            match uu____8070 with
                                            | (x,q) ->
                                                let uu____8083 =
                                                  (FStar_Syntax_Syntax.is_null_bv
                                                     x)
                                                    ||
                                                    (is_rec &&
                                                       (FStar_Syntax_Syntax.is_implicit
                                                          q))
                                                   in
                                                if uu____8083
                                                then []
                                                else [(x, q)]))
                                     in
                                  let fields' =
                                    FStar_All.pipe_right formals'
                                      (FStar_List.map
                                         (fun uu____8136  ->
                                            match uu____8136 with
                                            | (x,q) ->
                                                let uu____8149 =
                                                  if is_rec
                                                  then
                                                    FStar_Syntax_Util.unmangle_field_name
                                                      x.FStar_Syntax_Syntax.ppname
                                                  else
                                                    x.FStar_Syntax_Syntax.ppname
                                                   in
                                                (uu____8149,
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
                                  ((let uu____8162 =
                                      let uu____8165 =
                                        FStar_ST.op_Bang new_globs  in
                                      (Record_or_dc record) :: uu____8165  in
                                    FStar_ST.op_Colon_Equals new_globs
                                      uu____8162);
                                   (match () with
                                    | () ->
                                        ((let add_field uu____8276 =
                                            match uu____8276 with
                                            | (id1,uu____8282) ->
                                                let modul =
                                                  let uu____8284 =
                                                    FStar_Ident.lid_of_ids
                                                      constrname.FStar_Ident.ns
                                                     in
                                                  uu____8284.FStar_Ident.str
                                                   in
                                                let uu____8285 =
                                                  get_exported_id_set e modul
                                                   in
                                                (match uu____8285 with
                                                 | FStar_Pervasives_Native.Some
                                                     my_ex ->
                                                     let my_exported_ids =
                                                       my_ex
                                                         Exported_id_field
                                                        in
                                                     ((let uu____8319 =
                                                         let uu____8320 =
                                                           FStar_ST.op_Bang
                                                             my_exported_ids
                                                            in
                                                         FStar_Util.set_add
                                                           id1.FStar_Ident.idText
                                                           uu____8320
                                                          in
                                                       FStar_ST.op_Colon_Equals
                                                         my_exported_ids
                                                         uu____8319);
                                                      (match () with
                                                       | () ->
                                                           let projname =
                                                             let uu____8414 =
                                                               let uu____8415
                                                                 =
                                                                 FStar_Syntax_Util.mk_field_projector_name_from_ident
                                                                   constrname
                                                                   id1
                                                                  in
                                                               uu____8415.FStar_Ident.ident
                                                                in
                                                             uu____8414.FStar_Ident.idText
                                                              in
                                                           let uu____8417 =
                                                             let uu____8418 =
                                                               FStar_ST.op_Bang
                                                                 my_exported_ids
                                                                in
                                                             FStar_Util.set_add
                                                               projname
                                                               uu____8418
                                                              in
                                                           FStar_ST.op_Colon_Equals
                                                             my_exported_ids
                                                             uu____8417))
                                                 | FStar_Pervasives_Native.None
                                                      -> ())
                                             in
                                          FStar_List.iter add_field fields');
                                         (match () with
                                          | () -> insert_record_cache record)))))
                         | uu____8520 -> ())
                    | uu____8521 -> ()))
        | uu____8522 -> ()
  
let (try_lookup_record_or_dc_by_field_name :
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option) =
  fun env  ->
    fun fieldname  ->
      let find_in_cache fieldname1 =
        let uu____8543 =
          ((fieldname1.FStar_Ident.ns), (fieldname1.FStar_Ident.ident))  in
        match uu____8543 with
        | (ns,id1) ->
            let uu____8560 = peek_record_cache ()  in
            FStar_Util.find_map uu____8560
              (fun record  ->
                 let uu____8566 =
                   find_in_record ns id1 record (fun r  -> Cont_ok r)  in
                 option_of_cont
                   (fun uu____8572  -> FStar_Pervasives_Native.None)
                   uu____8566)
         in
      resolve_in_open_namespaces'' env fieldname Exported_id_field
        (fun uu____8574  -> Cont_ignore) (fun uu____8576  -> Cont_ignore)
        (fun r  -> Cont_ok r)
        (fun fn  ->
           let uu____8582 = find_in_cache fn  in
           cont_of_option Cont_ignore uu____8582)
        (fun k  -> fun uu____8588  -> k)
  
let (try_lookup_record_by_field_name :
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option) =
  fun env  ->
    fun fieldname  ->
      let uu____8603 = try_lookup_record_or_dc_by_field_name env fieldname
         in
      match uu____8603 with
      | FStar_Pervasives_Native.Some r when r.is_record ->
          FStar_Pervasives_Native.Some r
      | uu____8609 -> FStar_Pervasives_Native.None
  
let (belongs_to_record :
  env -> FStar_Ident.lident -> record_or_dc -> Prims.bool) =
  fun env  ->
    fun lid  ->
      fun record  ->
        let uu____8627 = try_lookup_record_by_field_name env lid  in
        match uu____8627 with
        | FStar_Pervasives_Native.Some record' when
            let uu____8631 =
              let uu____8632 =
                FStar_Ident.path_of_ns (record.typename).FStar_Ident.ns  in
              FStar_Ident.text_of_path uu____8632  in
            let uu____8633 =
              let uu____8634 =
                FStar_Ident.path_of_ns (record'.typename).FStar_Ident.ns  in
              FStar_Ident.text_of_path uu____8634  in
            uu____8631 = uu____8633 ->
            let uu____8635 =
              find_in_record (record.typename).FStar_Ident.ns
                lid.FStar_Ident.ident record (fun uu____8639  -> Cont_ok ())
               in
            (match uu____8635 with
             | Cont_ok uu____8640 -> true
             | uu____8641 -> false)
        | uu____8644 -> false
  
let (try_lookup_dc_by_field_name :
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident,Prims.bool) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun fieldname  ->
      let uu____8663 = try_lookup_record_or_dc_by_field_name env fieldname
         in
      match uu____8663 with
      | FStar_Pervasives_Native.Some r ->
          let uu____8673 =
            let uu____8678 =
              let uu____8679 =
                FStar_Ident.lid_of_ids
                  (FStar_List.append (r.typename).FStar_Ident.ns
                     [r.constrname])
                 in
              let uu____8680 = FStar_Ident.range_of_lid fieldname  in
              FStar_Ident.set_lid_range uu____8679 uu____8680  in
            (uu____8678, (r.is_record))  in
          FStar_Pervasives_Native.Some uu____8673
      | uu____8685 -> FStar_Pervasives_Native.None
  
let (string_set_ref_new : unit -> Prims.string FStar_Util.set FStar_ST.ref) =
  fun uu____8711  ->
    let uu____8712 = FStar_Util.new_set FStar_Util.compare  in
    FStar_Util.mk_ref uu____8712
  
let (exported_id_set_new :
  unit -> exported_id_kind -> Prims.string FStar_Util.set FStar_ST.ref) =
  fun uu____8739  ->
    let term_type_set = string_set_ref_new ()  in
    let field_set = string_set_ref_new ()  in
    fun uu___134_8750  ->
      match uu___134_8750 with
      | Exported_id_term_type  -> term_type_set
      | Exported_id_field  -> field_set
  
let (unique :
  Prims.bool -> Prims.bool -> env -> FStar_Ident.lident -> Prims.bool) =
  fun any_val  ->
    fun exclude_interface  ->
      fun env  ->
        fun lid  ->
          let filter_scope_mods uu___135_8802 =
            match uu___135_8802 with
            | Rec_binding uu____8803 -> true
            | uu____8804 -> false  in
          let this_env =
            let uu___149_8806 = env  in
            let uu____8807 =
              FStar_List.filter filter_scope_mods env.scope_mods  in
            {
              curmodule = (uu___149_8806.curmodule);
              curmonad = (uu___149_8806.curmonad);
              modules = (uu___149_8806.modules);
              scope_mods = uu____8807;
              exported_ids = empty_exported_id_smap;
              trans_exported_ids = (uu___149_8806.trans_exported_ids);
              includes = empty_include_smap;
              sigaccum = (uu___149_8806.sigaccum);
              sigmap = (uu___149_8806.sigmap);
              iface = (uu___149_8806.iface);
              admitted_iface = (uu___149_8806.admitted_iface);
              expect_typ = (uu___149_8806.expect_typ);
              docs = (uu___149_8806.docs);
              remaining_iface_decls = (uu___149_8806.remaining_iface_decls);
              syntax_only = (uu___149_8806.syntax_only);
              ds_hooks = (uu___149_8806.ds_hooks)
            }  in
          let uu____8810 =
            try_lookup_lid' any_val exclude_interface this_env lid  in
          match uu____8810 with
          | FStar_Pervasives_Native.None  -> true
          | FStar_Pervasives_Native.Some uu____8829 -> false
  
let (push_scope_mod : env -> scope_mod -> env) =
  fun env  ->
    fun scope_mod  ->
      let uu___150_8856 = env  in
      {
        curmodule = (uu___150_8856.curmodule);
        curmonad = (uu___150_8856.curmonad);
        modules = (uu___150_8856.modules);
        scope_mods = (scope_mod :: (env.scope_mods));
        exported_ids = (uu___150_8856.exported_ids);
        trans_exported_ids = (uu___150_8856.trans_exported_ids);
        includes = (uu___150_8856.includes);
        sigaccum = (uu___150_8856.sigaccum);
        sigmap = (uu___150_8856.sigmap);
        iface = (uu___150_8856.iface);
        admitted_iface = (uu___150_8856.admitted_iface);
        expect_typ = (uu___150_8856.expect_typ);
        docs = (uu___150_8856.docs);
        remaining_iface_decls = (uu___150_8856.remaining_iface_decls);
        syntax_only = (uu___150_8856.syntax_only);
        ds_hooks = (uu___150_8856.ds_hooks)
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
        let uu____8921 =
          (unique false true env l) || (FStar_Options.interactive ())  in
        if uu____8921
        then push_scope_mod env (Rec_binding (x, l, dd))
        else
          (let uu____8923 = FStar_Ident.range_of_lid l  in
           FStar_Errors.raise_error
             (FStar_Errors.Fatal_DuplicateTopLevelNames,
               (Prims.strcat "Duplicate top-level names " l.FStar_Ident.str))
             uu____8923)
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let err l =
        let sopt = FStar_Util.smap_try_find (sigmap env) l.FStar_Ident.str
           in
        let r =
          match sopt with
          | FStar_Pervasives_Native.Some (se,uu____8953) ->
              let uu____8958 =
                FStar_Util.find_opt (FStar_Ident.lid_equals l)
                  (FStar_Syntax_Util.lids_of_sigelt se)
                 in
              (match uu____8958 with
               | FStar_Pervasives_Native.Some l1 ->
                   let uu____8962 = FStar_Ident.range_of_lid l1  in
                   FStar_All.pipe_left FStar_Range.string_of_range uu____8962
               | FStar_Pervasives_Native.None  -> "<unknown>")
          | FStar_Pervasives_Native.None  -> "<unknown>"  in
        let uu____8967 =
          let uu____8972 =
            let uu____8973 = FStar_Ident.text_of_lid l  in
            FStar_Util.format2
              "Duplicate top-level names [%s]; previously declared at %s"
              uu____8973 r
             in
          (FStar_Errors.Fatal_DuplicateTopLevelNames, uu____8972)  in
        let uu____8974 = FStar_Ident.range_of_lid l  in
        FStar_Errors.raise_error uu____8967 uu____8974  in
      let globals = FStar_Util.mk_ref env.scope_mods  in
      let env1 =
        let uu____8983 =
          match s.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let uu____8992 -> (false, true)
          | FStar_Syntax_Syntax.Sig_bundle uu____8999 -> (false, true)
          | uu____9008 -> (false, false)  in
        match uu____8983 with
        | (any_val,exclude_interface) ->
            let lids = FStar_Syntax_Util.lids_of_sigelt s  in
            let uu____9014 =
              FStar_Util.find_map lids
                (fun l  ->
                   let uu____9020 =
                     let uu____9021 = unique any_val exclude_interface env l
                        in
                     Prims.op_Negation uu____9021  in
                   if uu____9020
                   then FStar_Pervasives_Native.Some l
                   else FStar_Pervasives_Native.None)
               in
            (match uu____9014 with
             | FStar_Pervasives_Native.Some l -> err l
             | uu____9026 ->
                 (extract_record env globals s;
                  (let uu___151_9052 = env  in
                   {
                     curmodule = (uu___151_9052.curmodule);
                     curmonad = (uu___151_9052.curmonad);
                     modules = (uu___151_9052.modules);
                     scope_mods = (uu___151_9052.scope_mods);
                     exported_ids = (uu___151_9052.exported_ids);
                     trans_exported_ids = (uu___151_9052.trans_exported_ids);
                     includes = (uu___151_9052.includes);
                     sigaccum = (s :: (env.sigaccum));
                     sigmap = (uu___151_9052.sigmap);
                     iface = (uu___151_9052.iface);
                     admitted_iface = (uu___151_9052.admitted_iface);
                     expect_typ = (uu___151_9052.expect_typ);
                     docs = (uu___151_9052.docs);
                     remaining_iface_decls =
                       (uu___151_9052.remaining_iface_decls);
                     syntax_only = (uu___151_9052.syntax_only);
                     ds_hooks = (uu___151_9052.ds_hooks)
                   })))
         in
      let env2 =
        let uu___152_9054 = env1  in
        let uu____9055 = FStar_ST.op_Bang globals  in
        {
          curmodule = (uu___152_9054.curmodule);
          curmonad = (uu___152_9054.curmonad);
          modules = (uu___152_9054.modules);
          scope_mods = uu____9055;
          exported_ids = (uu___152_9054.exported_ids);
          trans_exported_ids = (uu___152_9054.trans_exported_ids);
          includes = (uu___152_9054.includes);
          sigaccum = (uu___152_9054.sigaccum);
          sigmap = (uu___152_9054.sigmap);
          iface = (uu___152_9054.iface);
          admitted_iface = (uu___152_9054.admitted_iface);
          expect_typ = (uu___152_9054.expect_typ);
          docs = (uu___152_9054.docs);
          remaining_iface_decls = (uu___152_9054.remaining_iface_decls);
          syntax_only = (uu___152_9054.syntax_only);
          ds_hooks = (uu___152_9054.ds_hooks)
        }  in
      let uu____9107 =
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_bundle (ses,uu____9133) ->
            let uu____9142 =
              FStar_List.map
                (fun se  -> ((FStar_Syntax_Util.lids_of_sigelt se), se)) ses
               in
            (env2, uu____9142)
        | uu____9169 -> (env2, [((FStar_Syntax_Util.lids_of_sigelt s), s)])
         in
      match uu____9107 with
      | (env3,lss) ->
          (FStar_All.pipe_right lss
             (FStar_List.iter
                (fun uu____9228  ->
                   match uu____9228 with
                   | (lids,se) ->
                       FStar_All.pipe_right lids
                         (FStar_List.iter
                            (fun lid  ->
                               (let uu____9250 =
                                  let uu____9253 = FStar_ST.op_Bang globals
                                     in
                                  (Top_level_def (lid.FStar_Ident.ident)) ::
                                    uu____9253
                                   in
                                FStar_ST.op_Colon_Equals globals uu____9250);
                               (match () with
                                | () ->
                                    let modul =
                                      let uu____9355 =
                                        FStar_Ident.lid_of_ids
                                          lid.FStar_Ident.ns
                                         in
                                      uu____9355.FStar_Ident.str  in
                                    ((let uu____9357 =
                                        get_exported_id_set env3 modul  in
                                      match uu____9357 with
                                      | FStar_Pervasives_Native.Some f ->
                                          let my_exported_ids =
                                            f Exported_id_term_type  in
                                          let uu____9390 =
                                            let uu____9391 =
                                              FStar_ST.op_Bang
                                                my_exported_ids
                                               in
                                            FStar_Util.set_add
                                              (lid.FStar_Ident.ident).FStar_Ident.idText
                                              uu____9391
                                             in
                                          FStar_ST.op_Colon_Equals
                                            my_exported_ids uu____9390
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
              let uu___153_9495 = env3  in
              let uu____9496 = FStar_ST.op_Bang globals  in
              {
                curmodule = (uu___153_9495.curmodule);
                curmonad = (uu___153_9495.curmonad);
                modules = (uu___153_9495.modules);
                scope_mods = uu____9496;
                exported_ids = (uu___153_9495.exported_ids);
                trans_exported_ids = (uu___153_9495.trans_exported_ids);
                includes = (uu___153_9495.includes);
                sigaccum = (uu___153_9495.sigaccum);
                sigmap = (uu___153_9495.sigmap);
                iface = (uu___153_9495.iface);
                admitted_iface = (uu___153_9495.admitted_iface);
                expect_typ = (uu___153_9495.expect_typ);
                docs = (uu___153_9495.docs);
                remaining_iface_decls = (uu___153_9495.remaining_iface_decls);
                syntax_only = (uu___153_9495.syntax_only);
                ds_hooks = (uu___153_9495.ds_hooks)
              }  in
            env4))
  
let (push_namespace : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun ns  ->
      let uu____9558 =
        let uu____9563 = resolve_module_name env ns false  in
        match uu____9563 with
        | FStar_Pervasives_Native.None  ->
            let modules = env.modules  in
            let uu____9577 =
              FStar_All.pipe_right modules
                (FStar_Util.for_some
                   (fun uu____9593  ->
                      match uu____9593 with
                      | (m,uu____9599) ->
                          let uu____9600 =
                            let uu____9601 = FStar_Ident.text_of_lid m  in
                            Prims.strcat uu____9601 "."  in
                          let uu____9602 =
                            let uu____9603 = FStar_Ident.text_of_lid ns  in
                            Prims.strcat uu____9603 "."  in
                          FStar_Util.starts_with uu____9600 uu____9602))
               in
            if uu____9577
            then (ns, Open_namespace)
            else
              (let uu____9609 =
                 let uu____9614 =
                   let uu____9615 = FStar_Ident.text_of_lid ns  in
                   FStar_Util.format1 "Namespace %s cannot be found"
                     uu____9615
                    in
                 (FStar_Errors.Fatal_NameSpaceNotFound, uu____9614)  in
               let uu____9616 = FStar_Ident.range_of_lid ns  in
               FStar_Errors.raise_error uu____9609 uu____9616)
        | FStar_Pervasives_Native.Some ns' ->
            (fail_if_curmodule env ns ns'; (ns', Open_module))
         in
      match uu____9558 with
      | (ns',kd) ->
          ((env.ds_hooks).ds_push_open_hook env (ns', kd);
           push_scope_mod env (Open_module_or_namespace (ns', kd)))
  
let (push_include : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun ns  ->
      let ns0 = ns  in
      let uu____9637 = resolve_module_name env ns false  in
      match uu____9637 with
      | FStar_Pervasives_Native.Some ns1 ->
          ((env.ds_hooks).ds_push_include_hook env ns1;
           fail_if_curmodule env ns0 ns1;
           (let env1 =
              push_scope_mod env
                (Open_module_or_namespace (ns1, Open_module))
               in
            let curmod =
              let uu____9645 = current_module env1  in
              uu____9645.FStar_Ident.str  in
            (let uu____9647 = FStar_Util.smap_try_find env1.includes curmod
                in
             match uu____9647 with
             | FStar_Pervasives_Native.None  -> ()
             | FStar_Pervasives_Native.Some incl ->
                 let uu____9671 =
                   let uu____9674 = FStar_ST.op_Bang incl  in ns1 ::
                     uu____9674
                    in
                 FStar_ST.op_Colon_Equals incl uu____9671);
            (match () with
             | () ->
                 let uu____9775 =
                   get_trans_exported_id_set env1 ns1.FStar_Ident.str  in
                 (match uu____9775 with
                  | FStar_Pervasives_Native.Some ns_trans_exports ->
                      ((let uu____9795 =
                          let uu____9898 = get_exported_id_set env1 curmod
                             in
                          let uu____9948 =
                            get_trans_exported_id_set env1 curmod  in
                          (uu____9898, uu____9948)  in
                        match uu____9795 with
                        | (FStar_Pervasives_Native.Some
                           cur_exports,FStar_Pervasives_Native.Some
                           cur_trans_exports) ->
                            let update_exports k =
                              let ns_ex =
                                let uu____10391 = ns_trans_exports k  in
                                FStar_ST.op_Bang uu____10391  in
                              let ex = cur_exports k  in
                              (let uu____10577 =
                                 let uu____10580 = FStar_ST.op_Bang ex  in
                                 FStar_Util.set_difference uu____10580 ns_ex
                                  in
                               FStar_ST.op_Colon_Equals ex uu____10577);
                              (match () with
                               | () ->
                                   let trans_ex = cur_trans_exports k  in
                                   let uu____10784 =
                                     let uu____10787 =
                                       FStar_ST.op_Bang trans_ex  in
                                     FStar_Util.set_union uu____10787 ns_ex
                                      in
                                   FStar_ST.op_Colon_Equals trans_ex
                                     uu____10784)
                               in
                            FStar_List.iter update_exports
                              all_exported_id_kinds
                        | uu____10924 -> ());
                       (match () with | () -> env1))
                  | FStar_Pervasives_Native.None  ->
                      let uu____11032 =
                        let uu____11037 =
                          FStar_Util.format1
                            "include: Module %s was not prepared"
                            ns1.FStar_Ident.str
                           in
                        (FStar_Errors.Fatal_IncludeModuleNotPrepared,
                          uu____11037)
                         in
                      let uu____11038 = FStar_Ident.range_of_lid ns1  in
                      FStar_Errors.raise_error uu____11032 uu____11038))))
      | uu____11039 ->
          let uu____11042 =
            let uu____11047 =
              FStar_Util.format1 "include: Module %s cannot be found"
                ns.FStar_Ident.str
               in
            (FStar_Errors.Fatal_ModuleNotFound, uu____11047)  in
          let uu____11048 = FStar_Ident.range_of_lid ns  in
          FStar_Errors.raise_error uu____11042 uu____11048
  
let (push_module_abbrev :
  env -> FStar_Ident.ident -> FStar_Ident.lident -> env) =
  fun env  ->
    fun x  ->
      fun l  ->
        let uu____11064 = module_is_defined env l  in
        if uu____11064
        then
          (fail_if_curmodule env l l;
           (env.ds_hooks).ds_push_module_abbrev_hook env x l;
           push_scope_mod env (Module_abbrev (x, l)))
        else
          (let uu____11068 =
             let uu____11073 =
               let uu____11074 = FStar_Ident.text_of_lid l  in
               FStar_Util.format1 "Module %s cannot be found" uu____11074  in
             (FStar_Errors.Fatal_ModuleNotFound, uu____11073)  in
           let uu____11075 = FStar_Ident.range_of_lid l  in
           FStar_Errors.raise_error uu____11068 uu____11075)
  
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
            ((let uu____11097 =
                FStar_Util.smap_try_find env.docs l.FStar_Ident.str  in
              match uu____11097 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some old_doc ->
                  let uu____11101 = FStar_Ident.range_of_lid l  in
                  let uu____11102 =
                    let uu____11107 =
                      let uu____11108 = FStar_Ident.string_of_lid l  in
                      let uu____11109 =
                        FStar_Parser_AST.string_of_fsdoc old_doc  in
                      let uu____11110 = FStar_Parser_AST.string_of_fsdoc doc1
                         in
                      FStar_Util.format3
                        "Overwriting doc of %s; old doc was [%s]; new doc are [%s]"
                        uu____11108 uu____11109 uu____11110
                       in
                    (FStar_Errors.Warning_DocOverwrite, uu____11107)  in
                  FStar_Errors.log_issue uu____11101 uu____11102);
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
                      let uu____11152 =
                        FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption)
                         in
                      Prims.op_Negation uu____11152 ->
                      let uu____11155 =
                        FStar_Util.smap_try_find (sigmap env)
                          l.FStar_Ident.str
                         in
                      (match uu____11155 with
                       | FStar_Pervasives_Native.Some
                           ({
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_let uu____11168;
                              FStar_Syntax_Syntax.sigrng = uu____11169;
                              FStar_Syntax_Syntax.sigquals = uu____11170;
                              FStar_Syntax_Syntax.sigmeta = uu____11171;
                              FStar_Syntax_Syntax.sigattrs = uu____11172;_},uu____11173)
                           -> lids
                       | FStar_Pervasives_Native.Some
                           ({
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_inductive_typ
                                uu____11188;
                              FStar_Syntax_Syntax.sigrng = uu____11189;
                              FStar_Syntax_Syntax.sigquals = uu____11190;
                              FStar_Syntax_Syntax.sigmeta = uu____11191;
                              FStar_Syntax_Syntax.sigattrs = uu____11192;_},uu____11193)
                           -> lids
                       | uu____11218 ->
                           ((let uu____11226 =
                               let uu____11227 = FStar_Options.interactive ()
                                  in
                               Prims.op_Negation uu____11227  in
                             if uu____11226
                             then
                               let uu____11228 = FStar_Ident.range_of_lid l
                                  in
                               let uu____11229 =
                                 let uu____11234 =
                                   let uu____11235 =
                                     FStar_Ident.string_of_lid l  in
                                   FStar_Util.format1
                                     "Admitting %s without a definition"
                                     uu____11235
                                    in
                                 (FStar_Errors.Warning_AdmitWithoutDefinition,
                                   uu____11234)
                                  in
                               FStar_Errors.log_issue uu____11228 uu____11229
                             else ());
                            (let quals = FStar_Syntax_Syntax.Assumption ::
                               (se.FStar_Syntax_Syntax.sigquals)  in
                             FStar_Util.smap_add (sigmap env)
                               l.FStar_Ident.str
                               ((let uu___154_11246 = se  in
                                 {
                                   FStar_Syntax_Syntax.sigel =
                                     (uu___154_11246.FStar_Syntax_Syntax.sigel);
                                   FStar_Syntax_Syntax.sigrng =
                                     (uu___154_11246.FStar_Syntax_Syntax.sigrng);
                                   FStar_Syntax_Syntax.sigquals = quals;
                                   FStar_Syntax_Syntax.sigmeta =
                                     (uu___154_11246.FStar_Syntax_Syntax.sigmeta);
                                   FStar_Syntax_Syntax.sigattrs =
                                     (uu___154_11246.FStar_Syntax_Syntax.sigattrs)
                                 }), false);
                             l
                             ::
                             lids)))
                  | uu____11247 -> lids) [])
         in
      let uu___155_11248 = m  in
      let uu____11249 =
        FStar_All.pipe_right m.FStar_Syntax_Syntax.declarations
          (FStar_List.map
             (fun s  ->
                match s.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_declare_typ
                    (lid,uu____11259,uu____11260) when
                    FStar_List.existsb
                      (fun l  -> FStar_Ident.lid_equals l lid)
                      admitted_sig_lids
                    ->
                    let uu___156_11263 = s  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___156_11263.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___156_11263.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals =
                        (FStar_Syntax_Syntax.Assumption ::
                        (s.FStar_Syntax_Syntax.sigquals));
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___156_11263.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___156_11263.FStar_Syntax_Syntax.sigattrs)
                    }
                | uu____11264 -> s))
         in
      {
        FStar_Syntax_Syntax.name = (uu___155_11248.FStar_Syntax_Syntax.name);
        FStar_Syntax_Syntax.declarations = uu____11249;
        FStar_Syntax_Syntax.exports =
          (uu___155_11248.FStar_Syntax_Syntax.exports);
        FStar_Syntax_Syntax.is_interface =
          (uu___155_11248.FStar_Syntax_Syntax.is_interface)
      }
  
let (finish : env -> FStar_Syntax_Syntax.modul -> env) =
  fun env  ->
    fun modul  ->
      FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations
        (FStar_List.iter
           (fun se  ->
              let quals = se.FStar_Syntax_Syntax.sigquals  in
              match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_bundle (ses,uu____11287) ->
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
                                (lid,uu____11307,uu____11308,uu____11309,uu____11310,uu____11311)
                                ->
                                FStar_Util.smap_remove (sigmap env)
                                  lid.FStar_Ident.str
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (lid,univ_names,binders,typ,uu____11324,uu____11325)
                                ->
                                (FStar_Util.smap_remove (sigmap env)
                                   lid.FStar_Ident.str;
                                 if
                                   Prims.op_Negation
                                     (FStar_List.contains
                                        FStar_Syntax_Syntax.Private quals)
                                 then
                                   (let sigel =
                                      let uu____11340 =
                                        let uu____11347 =
                                          let uu____11348 =
                                            FStar_Ident.range_of_lid lid  in
                                          let uu____11349 =
                                            let uu____11356 =
                                              let uu____11357 =
                                                let uu____11370 =
                                                  FStar_Syntax_Syntax.mk_Total
                                                    typ
                                                   in
                                                (binders, uu____11370)  in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____11357
                                               in
                                            FStar_Syntax_Syntax.mk
                                              uu____11356
                                             in
                                          uu____11349
                                            FStar_Pervasives_Native.None
                                            uu____11348
                                           in
                                        (lid, univ_names, uu____11347)  in
                                      FStar_Syntax_Syntax.Sig_declare_typ
                                        uu____11340
                                       in
                                    let se2 =
                                      let uu___157_11385 = se1  in
                                      {
                                        FStar_Syntax_Syntax.sigel = sigel;
                                        FStar_Syntax_Syntax.sigrng =
                                          (uu___157_11385.FStar_Syntax_Syntax.sigrng);
                                        FStar_Syntax_Syntax.sigquals =
                                          (FStar_Syntax_Syntax.Assumption ::
                                          quals);
                                        FStar_Syntax_Syntax.sigmeta =
                                          (uu___157_11385.FStar_Syntax_Syntax.sigmeta);
                                        FStar_Syntax_Syntax.sigattrs =
                                          (uu___157_11385.FStar_Syntax_Syntax.sigattrs)
                                      }  in
                                    FStar_Util.smap_add (sigmap env)
                                      lid.FStar_Ident.str (se2, false))
                                 else ())
                            | uu____11391 -> ()))
                  else ()
              | FStar_Syntax_Syntax.Sig_declare_typ
                  (lid,uu____11394,uu____11395) ->
                  if FStar_List.contains FStar_Syntax_Syntax.Private quals
                  then
                    FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str
                  else ()
              | FStar_Syntax_Syntax.Sig_let ((uu____11401,lbs),uu____11403)
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
                             let uu____11418 =
                               let uu____11419 =
                                 let uu____11420 =
                                   let uu____11423 =
                                     FStar_Util.right
                                       lb.FStar_Syntax_Syntax.lbname
                                      in
                                   uu____11423.FStar_Syntax_Syntax.fv_name
                                    in
                                 uu____11420.FStar_Syntax_Syntax.v  in
                               uu____11419.FStar_Ident.str  in
                             FStar_Util.smap_remove (sigmap env) uu____11418))
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
                               let uu____11437 =
                                 let uu____11440 =
                                   FStar_Util.right
                                     lb.FStar_Syntax_Syntax.lbname
                                    in
                                 uu____11440.FStar_Syntax_Syntax.fv_name  in
                               uu____11437.FStar_Syntax_Syntax.v  in
                             let quals1 = FStar_Syntax_Syntax.Assumption ::
                               quals  in
                             let decl =
                               let uu___158_11445 = se  in
                               {
                                 FStar_Syntax_Syntax.sigel =
                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                      (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                        (lb.FStar_Syntax_Syntax.lbtyp)));
                                 FStar_Syntax_Syntax.sigrng =
                                   (uu___158_11445.FStar_Syntax_Syntax.sigrng);
                                 FStar_Syntax_Syntax.sigquals = quals1;
                                 FStar_Syntax_Syntax.sigmeta =
                                   (uu___158_11445.FStar_Syntax_Syntax.sigmeta);
                                 FStar_Syntax_Syntax.sigattrs =
                                   (uu___158_11445.FStar_Syntax_Syntax.sigattrs)
                               }  in
                             FStar_Util.smap_add (sigmap env)
                               lid.FStar_Ident.str (decl, false)))
                   else ())
              | uu____11451 -> ()));
      (let curmod =
         let uu____11453 = current_module env  in uu____11453.FStar_Ident.str
          in
       (let uu____11455 =
          let uu____11558 = get_exported_id_set env curmod  in
          let uu____11608 = get_trans_exported_id_set env curmod  in
          (uu____11558, uu____11608)  in
        match uu____11455 with
        | (FStar_Pervasives_Native.Some cur_ex,FStar_Pervasives_Native.Some
           cur_trans_ex) ->
            let update_exports eikind =
              let cur_ex_set =
                let uu____12053 = cur_ex eikind  in
                FStar_ST.op_Bang uu____12053  in
              let cur_trans_ex_set_ref = cur_trans_ex eikind  in
              let uu____12252 =
                let uu____12255 = FStar_ST.op_Bang cur_trans_ex_set_ref  in
                FStar_Util.set_union cur_ex_set uu____12255  in
              FStar_ST.op_Colon_Equals cur_trans_ex_set_ref uu____12252  in
            FStar_List.iter update_exports all_exported_id_kinds
        | uu____12392 -> ());
       (match () with
        | () ->
            (filter_record_cache ();
             (match () with
              | () ->
                  let uu___159_12496 = env  in
                  {
                    curmodule = FStar_Pervasives_Native.None;
                    curmonad = (uu___159_12496.curmonad);
                    modules = (((modul.FStar_Syntax_Syntax.name), modul) ::
                      (env.modules));
                    scope_mods = [];
                    exported_ids = (uu___159_12496.exported_ids);
                    trans_exported_ids = (uu___159_12496.trans_exported_ids);
                    includes = (uu___159_12496.includes);
                    sigaccum = [];
                    sigmap = (uu___159_12496.sigmap);
                    iface = (uu___159_12496.iface);
                    admitted_iface = (uu___159_12496.admitted_iface);
                    expect_typ = (uu___159_12496.expect_typ);
                    docs = (uu___159_12496.docs);
                    remaining_iface_decls =
                      (uu___159_12496.remaining_iface_decls);
                    syntax_only = (uu___159_12496.syntax_only);
                    ds_hooks = (uu___159_12496.ds_hooks)
                  }))))
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push : env -> env) =
  fun env  ->
    FStar_Util.atomically
      (fun uu____12532  ->
         push_record_cache ();
         (let uu____12535 =
            let uu____12538 = FStar_ST.op_Bang stack  in env :: uu____12538
             in
          FStar_ST.op_Colon_Equals stack uu____12535);
         (let uu___160_12595 = env  in
          let uu____12596 = FStar_Util.smap_copy env.exported_ids  in
          let uu____12601 = FStar_Util.smap_copy env.trans_exported_ids  in
          let uu____12606 = FStar_Util.smap_copy env.includes  in
          let uu____12617 = FStar_Util.smap_copy env.sigmap  in
          let uu____12628 = FStar_Util.smap_copy env.docs  in
          {
            curmodule = (uu___160_12595.curmodule);
            curmonad = (uu___160_12595.curmonad);
            modules = (uu___160_12595.modules);
            scope_mods = (uu___160_12595.scope_mods);
            exported_ids = uu____12596;
            trans_exported_ids = uu____12601;
            includes = uu____12606;
            sigaccum = (uu___160_12595.sigaccum);
            sigmap = uu____12617;
            iface = (uu___160_12595.iface);
            admitted_iface = (uu___160_12595.admitted_iface);
            expect_typ = (uu___160_12595.expect_typ);
            docs = uu____12628;
            remaining_iface_decls = (uu___160_12595.remaining_iface_decls);
            syntax_only = (uu___160_12595.syntax_only);
            ds_hooks = (uu___160_12595.ds_hooks)
          }))
  
let (pop : unit -> env) =
  fun uu____12635  ->
    FStar_Util.atomically
      (fun uu____12642  ->
         let uu____12643 = FStar_ST.op_Bang stack  in
         match uu____12643 with
         | env::tl1 ->
             (pop_record_cache (); FStar_ST.op_Colon_Equals stack tl1; env)
         | uu____12706 -> failwith "Impossible: Too many pops")
  
let (snapshot : env -> (Prims.int,env) FStar_Pervasives_Native.tuple2) =
  fun env  -> FStar_Common.snapshot push stack env 
let (rollback : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth  -> FStar_Common.rollback pop stack depth 
let (export_interface : FStar_Ident.lident -> env -> env) =
  fun m  ->
    fun env  ->
      let sigelt_in_m se =
        match FStar_Syntax_Util.lids_of_sigelt se with
        | l::uu____12744 -> l.FStar_Ident.nsstr = m.FStar_Ident.str
        | uu____12747 -> false  in
      let sm = sigmap env  in
      let env1 = pop ()  in
      let keys = FStar_Util.smap_keys sm  in
      let sm' = sigmap env1  in
      FStar_All.pipe_right keys
        (FStar_List.iter
           (fun k  ->
              let uu____12781 = FStar_Util.smap_try_find sm' k  in
              match uu____12781 with
              | FStar_Pervasives_Native.Some (se,true ) when sigelt_in_m se
                  ->
                  (FStar_Util.smap_remove sm' k;
                   (let se1 =
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t) ->
                          let uu___161_12806 = se  in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (uu___161_12806.FStar_Syntax_Syntax.sigel);
                            FStar_Syntax_Syntax.sigrng =
                              (uu___161_12806.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (FStar_Syntax_Syntax.Assumption ::
                              (se.FStar_Syntax_Syntax.sigquals));
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___161_12806.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___161_12806.FStar_Syntax_Syntax.sigattrs)
                          }
                      | uu____12807 -> se  in
                    FStar_Util.smap_add sm' k (se1, false)))
              | uu____12812 -> ()));
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
      let uu____12835 = finish env modul1  in (uu____12835, modul1)
  
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
      let uu____12923 =
        let uu____12926 = e Exported_id_term_type  in
        FStar_ST.op_Bang uu____12926  in
      FStar_Util.set_elements uu____12923  in
    let fields =
      let uu____13048 =
        let uu____13051 = e Exported_id_field  in
        FStar_ST.op_Bang uu____13051  in
      FStar_Util.set_elements uu____13048  in
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
          let uu____13210 =
            FStar_Util.as_set e1.exported_id_terms FStar_Util.compare  in
          FStar_Util.mk_ref uu____13210  in
        let fields =
          let uu____13220 =
            FStar_Util.as_set e1.exported_id_fields FStar_Util.compare  in
          FStar_Util.mk_ref uu____13220  in
        (fun uu___136_13225  ->
           match uu___136_13225 with
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
  'Auu____13356 .
    'Auu____13356 Prims.list FStar_Pervasives_Native.option ->
      'Auu____13356 Prims.list FStar_ST.ref
  =
  fun uu___137_13369  ->
    match uu___137_13369 with
    | FStar_Pervasives_Native.None  -> FStar_Util.mk_ref []
    | FStar_Pervasives_Native.Some l -> FStar_Util.mk_ref l
  
let (inclusion_info : env -> FStar_Ident.lident -> module_inclusion_info) =
  fun env  ->
    fun l  ->
      let mname = FStar_Ident.string_of_lid l  in
      let as_ids_opt m =
        let uu____13410 = FStar_Util.smap_try_find m mname  in
        FStar_Util.map_opt uu____13410 as_exported_ids  in
      let uu____13416 = as_ids_opt env.exported_ids  in
      let uu____13419 = as_ids_opt env.trans_exported_ids  in
      let uu____13422 =
        let uu____13427 = FStar_Util.smap_try_find env.includes mname  in
        FStar_Util.map_opt uu____13427 (fun r  -> FStar_ST.op_Bang r)  in
      {
        mii_exported_ids = uu____13416;
        mii_trans_exported_ids = uu____13419;
        mii_includes = uu____13422
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
                let uu____13546 = FStar_Ident.text_of_lid mname  in
                FStar_Util.strcat uu____13546 ".fst"  in
              let auto_open =
                FStar_Parser_Dep.hard_coded_dependencies filename  in
              let auto_open1 =
                let convert_kind uu___138_13566 =
                  match uu___138_13566 with
                  | FStar_Parser_Dep.Open_namespace  -> Open_namespace
                  | FStar_Parser_Dep.Open_module  -> Open_module  in
                FStar_List.map
                  (fun uu____13578  ->
                     match uu____13578 with
                     | (lid,kind) -> (lid, (convert_kind kind))) auto_open
                 in
              let namespace_of_module =
                if
                  (FStar_List.length mname.FStar_Ident.ns) >
                    (Prims.parse_int "0")
                then
                  let uu____13602 =
                    let uu____13607 =
                      FStar_Ident.lid_of_ids mname.FStar_Ident.ns  in
                    (uu____13607, Open_namespace)  in
                  [uu____13602]
                else []  in
              let auto_open2 =
                FStar_List.append namespace_of_module
                  (FStar_List.rev auto_open1)
                 in
              (let uu____13637 = as_exported_id_set mii.mii_exported_ids  in
               FStar_Util.smap_add env1.exported_ids mname.FStar_Ident.str
                 uu____13637);
              (match () with
               | () ->
                   ((let uu____13664 =
                       as_exported_id_set mii.mii_trans_exported_ids  in
                     FStar_Util.smap_add env1.trans_exported_ids
                       mname.FStar_Ident.str uu____13664);
                    (match () with
                     | () ->
                         ((let uu____13691 = as_includes mii.mii_includes  in
                           FStar_Util.smap_add env1.includes
                             mname.FStar_Ident.str uu____13691);
                          (match () with
                           | () ->
                               let env' =
                                 let uu___162_13723 = env1  in
                                 let uu____13724 =
                                   FStar_List.map
                                     (fun x  -> Open_module_or_namespace x)
                                     auto_open2
                                    in
                                 {
                                   curmodule =
                                     (FStar_Pervasives_Native.Some mname);
                                   curmonad = (uu___162_13723.curmonad);
                                   modules = (uu___162_13723.modules);
                                   scope_mods = uu____13724;
                                   exported_ids =
                                     (uu___162_13723.exported_ids);
                                   trans_exported_ids =
                                     (uu___162_13723.trans_exported_ids);
                                   includes = (uu___162_13723.includes);
                                   sigaccum = (uu___162_13723.sigaccum);
                                   sigmap = (env1.sigmap);
                                   iface = intf;
                                   admitted_iface = admitted;
                                   expect_typ = (uu___162_13723.expect_typ);
                                   docs = (uu___162_13723.docs);
                                   remaining_iface_decls =
                                     (uu___162_13723.remaining_iface_decls);
                                   syntax_only = (uu___162_13723.syntax_only);
                                   ds_hooks = (uu___162_13723.ds_hooks)
                                 }  in
                               (FStar_List.iter
                                  (fun op  ->
                                     (env1.ds_hooks).ds_push_open_hook env'
                                       op) (FStar_List.rev auto_open2);
                                env'))))))
               in
            let uu____13736 =
              FStar_All.pipe_right env.modules
                (FStar_Util.find_opt
                   (fun uu____13762  ->
                      match uu____13762 with
                      | (l,uu____13768) -> FStar_Ident.lid_equals l mname))
               in
            match uu____13736 with
            | FStar_Pervasives_Native.None  ->
                let uu____13777 = prep env  in (uu____13777, false)
            | FStar_Pervasives_Native.Some (uu____13778,m) ->
                ((let uu____13785 =
                    (let uu____13788 = FStar_Options.interactive ()  in
                     Prims.op_Negation uu____13788) &&
                      ((Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)
                         || intf)
                     in
                  if uu____13785
                  then
                    let uu____13789 =
                      let uu____13794 =
                        FStar_Util.format1
                          "Duplicate module or interface name: %s"
                          mname.FStar_Ident.str
                         in
                      (FStar_Errors.Fatal_DuplicateModuleOrInterface,
                        uu____13794)
                       in
                    let uu____13795 = FStar_Ident.range_of_lid mname  in
                    FStar_Errors.raise_error uu____13789 uu____13795
                  else ());
                 (let uu____13797 =
                    let uu____13798 = push env  in prep uu____13798  in
                  (uu____13797, true)))
  
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
          let uu___163_13810 = env  in
          {
            curmodule = (uu___163_13810.curmodule);
            curmonad = (FStar_Pervasives_Native.Some mname);
            modules = (uu___163_13810.modules);
            scope_mods = (uu___163_13810.scope_mods);
            exported_ids = (uu___163_13810.exported_ids);
            trans_exported_ids = (uu___163_13810.trans_exported_ids);
            includes = (uu___163_13810.includes);
            sigaccum = (uu___163_13810.sigaccum);
            sigmap = (uu___163_13810.sigmap);
            iface = (uu___163_13810.iface);
            admitted_iface = (uu___163_13810.admitted_iface);
            expect_typ = (uu___163_13810.expect_typ);
            docs = (uu___163_13810.docs);
            remaining_iface_decls = (uu___163_13810.remaining_iface_decls);
            syntax_only = (uu___163_13810.syntax_only);
            ds_hooks = (uu___163_13810.ds_hooks)
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
        let uu____13844 = lookup1 lid  in
        match uu____13844 with
        | FStar_Pervasives_Native.None  ->
            let opened_modules =
              FStar_List.map
                (fun uu____13857  ->
                   match uu____13857 with
                   | (lid1,uu____13863) -> FStar_Ident.text_of_lid lid1)
                env.modules
               in
            let msg =
              let uu____13865 = FStar_Ident.text_of_lid lid  in
              FStar_Util.format1 "Identifier not found: [%s]" uu____13865  in
            let msg1 =
              if
                (FStar_List.length lid.FStar_Ident.ns) =
                  (Prims.parse_int "0")
              then msg
              else
                (let modul =
                   let uu____13870 =
                     FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
                   let uu____13871 = FStar_Ident.range_of_lid lid  in
                   FStar_Ident.set_lid_range uu____13870 uu____13871  in
                 let uu____13872 = resolve_module_name env modul true  in
                 match uu____13872 with
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
            let uu____13881 = FStar_Ident.range_of_lid lid  in
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_IdentifierNotFound, msg1) uu____13881
        | FStar_Pervasives_Native.Some r -> r
  
let fail_or2 :
  'a .
    (FStar_Ident.ident -> 'a FStar_Pervasives_Native.option) ->
      FStar_Ident.ident -> 'a
  =
  fun lookup1  ->
    fun id1  ->
      let uu____13909 = lookup1 id1  in
      match uu____13909 with
      | FStar_Pervasives_Native.None  ->
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_IdentifierNotFound,
              (Prims.strcat "Identifier not found ["
                 (Prims.strcat id1.FStar_Ident.idText "]")))
            id1.FStar_Ident.idRange
      | FStar_Pervasives_Native.Some r -> r
  