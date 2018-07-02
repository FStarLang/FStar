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
      let uu___283_1845 = env  in
      {
        curmodule = (uu___283_1845.curmodule);
        curmonad = (uu___283_1845.curmonad);
        modules = (uu___283_1845.modules);
        scope_mods = (uu___283_1845.scope_mods);
        exported_ids = (uu___283_1845.exported_ids);
        trans_exported_ids = (uu___283_1845.trans_exported_ids);
        includes = (uu___283_1845.includes);
        sigaccum = (uu___283_1845.sigaccum);
        sigmap = (uu___283_1845.sigmap);
        iface = b;
        admitted_iface = (uu___283_1845.admitted_iface);
        expect_typ = (uu___283_1845.expect_typ);
        docs = (uu___283_1845.docs);
        remaining_iface_decls = (uu___283_1845.remaining_iface_decls);
        syntax_only = (uu___283_1845.syntax_only);
        ds_hooks = (uu___283_1845.ds_hooks)
      }
  
let (iface : env -> Prims.bool) = fun e  -> e.iface 
let (set_admitted_iface : env -> Prims.bool -> env) =
  fun e  ->
    fun b  ->
      let uu___284_1861 = e  in
      {
        curmodule = (uu___284_1861.curmodule);
        curmonad = (uu___284_1861.curmonad);
        modules = (uu___284_1861.modules);
        scope_mods = (uu___284_1861.scope_mods);
        exported_ids = (uu___284_1861.exported_ids);
        trans_exported_ids = (uu___284_1861.trans_exported_ids);
        includes = (uu___284_1861.includes);
        sigaccum = (uu___284_1861.sigaccum);
        sigmap = (uu___284_1861.sigmap);
        iface = (uu___284_1861.iface);
        admitted_iface = b;
        expect_typ = (uu___284_1861.expect_typ);
        docs = (uu___284_1861.docs);
        remaining_iface_decls = (uu___284_1861.remaining_iface_decls);
        syntax_only = (uu___284_1861.syntax_only);
        ds_hooks = (uu___284_1861.ds_hooks)
      }
  
let (admitted_iface : env -> Prims.bool) = fun e  -> e.admitted_iface 
let (set_expect_typ : env -> Prims.bool -> env) =
  fun e  ->
    fun b  ->
      let uu___285_1877 = e  in
      {
        curmodule = (uu___285_1877.curmodule);
        curmonad = (uu___285_1877.curmonad);
        modules = (uu___285_1877.modules);
        scope_mods = (uu___285_1877.scope_mods);
        exported_ids = (uu___285_1877.exported_ids);
        trans_exported_ids = (uu___285_1877.trans_exported_ids);
        includes = (uu___285_1877.includes);
        sigaccum = (uu___285_1877.sigaccum);
        sigmap = (uu___285_1877.sigmap);
        iface = (uu___285_1877.iface);
        admitted_iface = (uu___285_1877.admitted_iface);
        expect_typ = b;
        docs = (uu___285_1877.docs);
        remaining_iface_decls = (uu___285_1877.remaining_iface_decls);
        syntax_only = (uu___285_1877.syntax_only);
        ds_hooks = (uu___285_1877.ds_hooks)
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
      (fun uu___250_2048  ->
         match uu___250_2048 with
         | Open_module_or_namespace (lid,_info) ->
             FStar_Pervasives_Native.Some lid
         | uu____2053 -> FStar_Pervasives_Native.None) env.scope_mods
  
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun e  ->
    fun l  ->
      let uu___286_2064 = e  in
      {
        curmodule = (FStar_Pervasives_Native.Some l);
        curmonad = (uu___286_2064.curmonad);
        modules = (uu___286_2064.modules);
        scope_mods = (uu___286_2064.scope_mods);
        exported_ids = (uu___286_2064.exported_ids);
        trans_exported_ids = (uu___286_2064.trans_exported_ids);
        includes = (uu___286_2064.includes);
        sigaccum = (uu___286_2064.sigaccum);
        sigmap = (uu___286_2064.sigmap);
        iface = (uu___286_2064.iface);
        admitted_iface = (uu___286_2064.admitted_iface);
        expect_typ = (uu___286_2064.expect_typ);
        docs = (uu___286_2064.docs);
        remaining_iface_decls = (uu___286_2064.remaining_iface_decls);
        syntax_only = (uu___286_2064.syntax_only);
        ds_hooks = (uu___286_2064.ds_hooks)
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
      let uu____2085 =
        FStar_All.pipe_right env.remaining_iface_decls
          (FStar_List.tryFind
             (fun uu____2119  ->
                match uu____2119 with
                | (m,uu____2127) -> FStar_Ident.lid_equals l m))
         in
      match uu____2085 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (uu____2144,decls) ->
          FStar_Pervasives_Native.Some decls
  
let (set_iface_decls :
  env -> FStar_Ident.lident -> FStar_Parser_AST.decl Prims.list -> env) =
  fun env  ->
    fun l  ->
      fun ds  ->
        let uu____2177 =
          FStar_List.partition
            (fun uu____2207  ->
               match uu____2207 with
               | (m,uu____2215) -> FStar_Ident.lid_equals l m)
            env.remaining_iface_decls
           in
        match uu____2177 with
        | (uu____2220,rest) ->
            let uu___287_2254 = env  in
            {
              curmodule = (uu___287_2254.curmodule);
              curmonad = (uu___287_2254.curmonad);
              modules = (uu___287_2254.modules);
              scope_mods = (uu___287_2254.scope_mods);
              exported_ids = (uu___287_2254.exported_ids);
              trans_exported_ids = (uu___287_2254.trans_exported_ids);
              includes = (uu___287_2254.includes);
              sigaccum = (uu___287_2254.sigaccum);
              sigmap = (uu___287_2254.sigmap);
              iface = (uu___287_2254.iface);
              admitted_iface = (uu___287_2254.admitted_iface);
              expect_typ = (uu___287_2254.expect_typ);
              docs = (uu___287_2254.docs);
              remaining_iface_decls = ((l, ds) :: rest);
              syntax_only = (uu___287_2254.syntax_only);
              ds_hooks = (uu___287_2254.ds_hooks)
            }
  
let (qual : FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident) =
  FStar_Syntax_Util.qual_id 
let (qualify : env -> FStar_Ident.ident -> FStar_Ident.lident) =
  fun env  ->
    fun id1  ->
      match env.curmonad with
      | FStar_Pervasives_Native.None  ->
          let uu____2281 = current_module env  in qual uu____2281 id1
      | FStar_Pervasives_Native.Some monad ->
          let uu____2283 =
            let uu____2284 = current_module env  in qual uu____2284 monad  in
          FStar_Syntax_Util.mk_field_projector_name_from_ident uu____2283 id1
  
let (syntax_only : env -> Prims.bool) = fun env  -> env.syntax_only 
let (set_syntax_only : env -> Prims.bool -> env) =
  fun env  ->
    fun b  ->
      let uu___288_2300 = env  in
      {
        curmodule = (uu___288_2300.curmodule);
        curmonad = (uu___288_2300.curmonad);
        modules = (uu___288_2300.modules);
        scope_mods = (uu___288_2300.scope_mods);
        exported_ids = (uu___288_2300.exported_ids);
        trans_exported_ids = (uu___288_2300.trans_exported_ids);
        includes = (uu___288_2300.includes);
        sigaccum = (uu___288_2300.sigaccum);
        sigmap = (uu___288_2300.sigmap);
        iface = (uu___288_2300.iface);
        admitted_iface = (uu___288_2300.admitted_iface);
        expect_typ = (uu___288_2300.expect_typ);
        docs = (uu___288_2300.docs);
        remaining_iface_decls = (uu___288_2300.remaining_iface_decls);
        syntax_only = b;
        ds_hooks = (uu___288_2300.ds_hooks)
      }
  
let (ds_hooks : env -> dsenv_hooks) = fun env  -> env.ds_hooks 
let (set_ds_hooks : env -> dsenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___289_2316 = env  in
      {
        curmodule = (uu___289_2316.curmodule);
        curmonad = (uu___289_2316.curmonad);
        modules = (uu___289_2316.modules);
        scope_mods = (uu___289_2316.scope_mods);
        exported_ids = (uu___289_2316.exported_ids);
        trans_exported_ids = (uu___289_2316.trans_exported_ids);
        includes = (uu___289_2316.includes);
        sigaccum = (uu___289_2316.sigaccum);
        sigmap = (uu___289_2316.sigmap);
        iface = (uu___289_2316.iface);
        admitted_iface = (uu___289_2316.admitted_iface);
        expect_typ = (uu___289_2316.expect_typ);
        docs = (uu___289_2316.docs);
        remaining_iface_decls = (uu___289_2316.remaining_iface_decls);
        syntax_only = (uu___289_2316.syntax_only);
        ds_hooks = hooks
      }
  
let new_sigmap : 'Auu____2321 . unit -> 'Auu____2321 FStar_Util.smap =
  fun uu____2328  -> FStar_Util.smap_create (Prims.parse_int "100") 
let (empty_env : unit -> env) =
  fun uu____2333  ->
    let uu____2334 = new_sigmap ()  in
    let uu____2339 = new_sigmap ()  in
    let uu____2344 = new_sigmap ()  in
    let uu____2355 = new_sigmap ()  in
    let uu____2366 = new_sigmap ()  in
    {
      curmodule = FStar_Pervasives_Native.None;
      curmonad = FStar_Pervasives_Native.None;
      modules = [];
      scope_mods = [];
      exported_ids = uu____2334;
      trans_exported_ids = uu____2339;
      includes = uu____2344;
      sigaccum = [];
      sigmap = uu____2355;
      iface = false;
      admitted_iface = false;
      expect_typ = false;
      docs = uu____2366;
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
      (fun uu____2402  ->
         match uu____2402 with
         | (m,uu____2408) ->
             FStar_Ident.lid_equals m FStar_Parser_Const.all_lid) env.modules
  
let (set_bv_range :
  FStar_Syntax_Syntax.bv -> FStar_Range.range -> FStar_Syntax_Syntax.bv) =
  fun bv  ->
    fun r  ->
      let id1 =
        let uu___290_2420 = bv.FStar_Syntax_Syntax.ppname  in
        {
          FStar_Ident.idText = (uu___290_2420.FStar_Ident.idText);
          FStar_Ident.idRange = r
        }  in
      let uu___291_2421 = bv  in
      {
        FStar_Syntax_Syntax.ppname = id1;
        FStar_Syntax_Syntax.index = (uu___291_2421.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = (uu___291_2421.FStar_Syntax_Syntax.sort)
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
        (fun uu____2514  ->
           match uu____2514 with
           | (x,y,dd,dq) ->
               if id1.FStar_Ident.idText = x
               then
                 let uu____2537 =
                   let uu____2538 =
                     FStar_Ident.lid_of_path ["Prims"; y]
                       id1.FStar_Ident.idRange
                      in
                   FStar_Syntax_Syntax.fvar uu____2538 dd dq  in
                 FStar_Pervasives_Native.Some uu____2537
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
    match projectee with | Cont_ok _0 -> true | uu____2585 -> false
  
let __proj__Cont_ok__item___0 : 'a . 'a cont_t -> 'a =
  fun projectee  -> match projectee with | Cont_ok _0 -> _0 
let uu___is_Cont_fail : 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_fail  -> true | uu____2618 -> false
  
let uu___is_Cont_ignore : 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_ignore  -> true | uu____2635 -> false
  
let option_of_cont :
  'a .
    (unit -> 'a FStar_Pervasives_Native.option) ->
      'a cont_t -> 'a FStar_Pervasives_Native.option
  =
  fun k_ignore  ->
    fun uu___251_2663  ->
      match uu___251_2663 with
      | Cont_ok a -> FStar_Pervasives_Native.Some a
      | Cont_fail  -> FStar_Pervasives_Native.None
      | Cont_ignore  -> k_ignore ()
  
let find_in_record :
  'Auu____2681 .
    FStar_Ident.ident Prims.list ->
      FStar_Ident.ident ->
        record_or_dc ->
          (record_or_dc -> 'Auu____2681 cont_t) -> 'Auu____2681 cont_t
  =
  fun ns  ->
    fun id1  ->
      fun record  ->
        fun cont  ->
          let typename' =
            FStar_Ident.lid_of_ids
              (FStar_List.append ns [(record.typename).FStar_Ident.ident])
             in
          let uu____2718 = FStar_Ident.lid_equals typename' record.typename
             in
          if uu____2718
          then
            let fname =
              FStar_Ident.lid_of_ids
                (FStar_List.append (record.typename).FStar_Ident.ns [id1])
               in
            let find1 =
              FStar_Util.find_map record.fields
                (fun uu____2732  ->
                   match uu____2732 with
                   | (f,uu____2740) ->
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
  fun uu___252_2802  ->
    match uu___252_2802 with
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
              let rec aux uu___253_2873 =
                match uu___253_2873 with
                | [] -> find_in_module_default
                | modul::q ->
                    let mname = modul.FStar_Ident.str  in
                    let not_shadowed =
                      let uu____2884 = get_exported_id_set env mname  in
                      match uu____2884 with
                      | FStar_Pervasives_Native.None  -> true
                      | FStar_Pervasives_Native.Some mex ->
                          let mexports =
                            let uu____2909 = mex eikind  in
                            FStar_ST.op_Bang uu____2909  in
                          FStar_Util.set_mem idstr mexports
                       in
                    let mincludes =
                      let uu____3023 =
                        FStar_Util.smap_try_find env.includes mname  in
                      match uu____3023 with
                      | FStar_Pervasives_Native.None  -> []
                      | FStar_Pervasives_Native.Some minc ->
                          FStar_ST.op_Bang minc
                       in
                    let look_into =
                      if not_shadowed
                      then
                        let uu____3099 = qual modul id1  in
                        find_in_module uu____3099
                      else Cont_ignore  in
                    (match look_into with
                     | Cont_ignore  -> aux (FStar_List.append mincludes q)
                     | uu____3103 -> look_into)
                 in
              aux [ns]
  
let (is_exported_id_field : exported_id_kind -> Prims.bool) =
  fun uu___254_3110  ->
    match uu___254_3110 with
    | Exported_id_field  -> true
    | uu____3111 -> false
  
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
                  let check_local_binding_id uu___255_3232 =
                    match uu___255_3232 with
                    | (id',uu____3234,uu____3235) ->
                        id'.FStar_Ident.idText = id1.FStar_Ident.idText
                     in
                  let check_rec_binding_id uu___256_3241 =
                    match uu___256_3241 with
                    | (id',uu____3243,uu____3244) ->
                        id'.FStar_Ident.idText = id1.FStar_Ident.idText
                     in
                  let curmod_ns =
                    let uu____3248 = current_module env  in
                    FStar_Ident.ids_of_lid uu____3248  in
                  let proc uu___257_3256 =
                    match uu___257_3256 with
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
                        let uu____3264 = FStar_Ident.lid_of_ids curmod_ns  in
                        find_in_module_with_includes Exported_id_field
                          (fun lid  ->
                             let id2 = lid.FStar_Ident.ident  in
                             find_in_record lid.FStar_Ident.ns id2 r k_record)
                          Cont_ignore env uu____3264 id1
                    | uu____3269 -> Cont_ignore  in
                  let rec aux uu___258_3279 =
                    match uu___258_3279 with
                    | a::q ->
                        let uu____3288 = proc a  in
                        option_of_cont (fun uu____3292  -> aux q) uu____3288
                    | [] ->
                        let uu____3293 = lookup_default_id Cont_fail id1  in
                        option_of_cont
                          (fun uu____3297  -> FStar_Pervasives_Native.None)
                          uu____3293
                     in
                  aux env.scope_mods
  
let found_local_binding :
  'Auu____3306 'Auu____3307 .
    FStar_Range.range ->
      ('Auu____3306,FStar_Syntax_Syntax.bv,'Auu____3307)
        FStar_Pervasives_Native.tuple3 ->
        (FStar_Syntax_Syntax.term,'Auu____3307)
          FStar_Pervasives_Native.tuple2
  =
  fun r  ->
    fun uu____3327  ->
      match uu____3327 with
      | (id',x,mut) -> let uu____3337 = bv_to_name x r  in (uu____3337, mut)
  
let find_in_module :
  'Auu____3348 .
    env ->
      FStar_Ident.lident ->
        (FStar_Ident.lident ->
           (FStar_Syntax_Syntax.sigelt,Prims.bool)
             FStar_Pervasives_Native.tuple2 -> 'Auu____3348)
          -> 'Auu____3348 -> 'Auu____3348
  =
  fun env  ->
    fun lid  ->
      fun k_global_def  ->
        fun k_not_found  ->
          let uu____3387 =
            FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str  in
          match uu____3387 with
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
      let uu____3427 = unmangleOpName id1  in
      match uu____3427 with
      | FStar_Pervasives_Native.Some f -> FStar_Pervasives_Native.Some f
      | uu____3453 ->
          try_lookup_id'' env id1 Exported_id_term_type
            (fun r  ->
               let uu____3467 = found_local_binding id1.FStar_Ident.idRange r
                  in
               Cont_ok uu____3467) (fun uu____3477  -> Cont_fail)
            (fun uu____3483  -> Cont_ignore)
            (fun i  ->
               find_in_module env i
                 (fun uu____3498  -> fun uu____3499  -> Cont_fail)
                 Cont_ignore)
            (fun uu____3514  -> fun uu____3515  -> Cont_fail)
  
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
            | FStar_Pervasives_Native.Some uu____3594 ->
                let lid = qualify env id1  in
                let uu____3596 =
                  FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str
                   in
                (match uu____3596 with
                 | FStar_Pervasives_Native.Some r ->
                     let uu____3620 = k_global_def lid r  in
                     FStar_Pervasives_Native.Some uu____3620
                 | FStar_Pervasives_Native.None  ->
                     FStar_Pervasives_Native.None)
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             in
          match find_in_monad with
          | FStar_Pervasives_Native.Some v1 -> v1
          | FStar_Pervasives_Native.None  ->
              let lid =
                let uu____3643 = current_module env  in qual uu____3643 id1
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
        let rec aux uu___259_3706 =
          match uu___259_3706 with
          | [] ->
              let uu____3711 = module_is_defined env lid  in
              if uu____3711
              then FStar_Pervasives_Native.Some lid
              else FStar_Pervasives_Native.None
          | (Open_module_or_namespace (ns,Open_namespace ))::q when honor_ns
              ->
              let new_lid =
                let uu____3720 =
                  let uu____3721 = FStar_Ident.path_of_lid ns  in
                  let uu____3724 = FStar_Ident.path_of_lid lid  in
                  FStar_List.append uu____3721 uu____3724  in
                let uu____3727 = FStar_Ident.range_of_lid lid  in
                FStar_Ident.lid_of_path uu____3720 uu____3727  in
              let uu____3728 = module_is_defined env new_lid  in
              if uu____3728
              then FStar_Pervasives_Native.Some new_lid
              else aux q
          | (Module_abbrev (name,modul))::uu____3734 when
              (nslen = (Prims.parse_int "0")) &&
                (name.FStar_Ident.idText =
                   (lid.FStar_Ident.ident).FStar_Ident.idText)
              -> FStar_Pervasives_Native.Some modul
          | uu____3741::q -> aux q  in
        aux env.scope_mods
  
let (fail_if_curmodule :
  env -> FStar_Ident.lident -> FStar_Ident.lident -> unit) =
  fun env  ->
    fun ns_original  ->
      fun ns_resolved  ->
        let uu____3760 =
          let uu____3761 = current_module env  in
          FStar_Ident.lid_equals ns_resolved uu____3761  in
        if uu____3760
        then
          let uu____3762 =
            FStar_Ident.lid_equals ns_resolved FStar_Parser_Const.prims_lid
             in
          (if uu____3762
           then ()
           else
             (let uu____3764 =
                let uu____3769 =
                  FStar_Util.format1
                    "Reference %s to current module is forbidden (see GitHub issue #451)"
                    ns_original.FStar_Ident.str
                   in
                (FStar_Errors.Fatal_ForbiddenReferenceToCurrentModule,
                  uu____3769)
                 in
              let uu____3770 = FStar_Ident.range_of_lid ns_original  in
              FStar_Errors.raise_error uu____3764 uu____3770))
        else ()
  
let (fail_if_qualified_by_curmodule : env -> FStar_Ident.lident -> unit) =
  fun env  ->
    fun lid  ->
      match lid.FStar_Ident.ns with
      | [] -> ()
      | uu____3782 ->
          let modul_orig = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          let uu____3786 = resolve_module_name env modul_orig true  in
          (match uu____3786 with
           | FStar_Pervasives_Native.Some modul_res ->
               fail_if_curmodule env modul_orig modul_res
           | uu____3790 -> ())
  
let (is_open : env -> FStar_Ident.lident -> open_kind -> Prims.bool) =
  fun env  ->
    fun lid  ->
      fun open_kind  ->
        FStar_List.existsb
          (fun uu___260_3811  ->
             match uu___260_3811 with
             | Open_module_or_namespace (ns,k) ->
                 (k = open_kind) && (FStar_Ident.lid_equals lid ns)
             | uu____3814 -> false) env.scope_mods
  
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
                 let uu____3933 = aux rev_ns_prefix ns_last_id  in
                 FStar_All.pipe_right uu____3933
                   (FStar_Util.map_option
                      (fun uu____3983  ->
                         match uu____3983 with
                         | (stripped_ids,rev_kept_ids) ->
                             (stripped_ids, (id1 :: rev_kept_ids)))))
           in
        let do_shorten env1 ids1 =
          match FStar_List.rev ids1 with
          | [] -> ([], [])
          | ns_last_id::ns_rev_prefix ->
              let uu____4053 = aux ns_rev_prefix ns_last_id  in
              (match uu____4053 with
               | FStar_Pervasives_Native.None  -> ([], ids1)
               | FStar_Pervasives_Native.Some (stripped_ids,rev_kept_ids) ->
                   (stripped_ids, (FStar_List.rev rev_kept_ids)))
           in
        if is_full_path && ((FStar_List.length ids) > (Prims.parse_int "0"))
        then
          let uu____4114 =
            let uu____4117 = FStar_Ident.lid_of_ids ids  in
            resolve_module_name env uu____4117 true  in
          match uu____4114 with
          | FStar_Pervasives_Native.Some m when module_is_open env m ->
              (ids, [])
          | uu____4131 -> do_shorten env ids
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
                  | uu____4250::uu____4251 ->
                      let uu____4254 =
                        let uu____4257 =
                          let uu____4258 =
                            FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
                          let uu____4259 = FStar_Ident.range_of_lid lid  in
                          FStar_Ident.set_lid_range uu____4258 uu____4259  in
                        resolve_module_name env uu____4257 true  in
                      (match uu____4254 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some modul ->
                           let uu____4263 =
                             find_in_module_with_includes eikind f_module
                               Cont_fail env modul lid.FStar_Ident.ident
                              in
                           option_of_cont
                             (fun uu____4267  -> FStar_Pervasives_Native.None)
                             uu____4263)
                  | [] ->
                      try_lookup_id'' env lid.FStar_Ident.ident eikind
                        k_local_binding k_rec_binding k_record f_module
                        l_default
  
let cont_of_option :
  'a . 'a cont_t -> 'a FStar_Pervasives_Native.option -> 'a cont_t =
  fun k_none  ->
    fun uu___261_4290  ->
      match uu___261_4290 with
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
              let uu____4406 = k_global_def lid1 def  in
              cont_of_option k uu____4406  in
            let f_module lid' =
              let k = Cont_ignore  in
              find_in_module env lid' (k_global_def' k) k  in
            let l_default k i = lookup_default_id env i (k_global_def' k) k
               in
            resolve_in_open_namespaces'' env lid Exported_id_term_type
              (fun l  ->
                 let uu____4442 = k_local_binding l  in
                 cont_of_option Cont_fail uu____4442)
              (fun r  ->
                 let uu____4448 = k_rec_binding r  in
                 cont_of_option Cont_fail uu____4448)
              (fun uu____4452  -> Cont_ignore) f_module l_default
  
let (fv_qual_of_se :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option)
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____4462,uu____4463,uu____4464,l,uu____4466,uu____4467) ->
        let qopt =
          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
            (fun uu___262_4478  ->
               match uu___262_4478 with
               | FStar_Syntax_Syntax.RecordConstructor (uu____4481,fs) ->
                   FStar_Pervasives_Native.Some
                     (FStar_Syntax_Syntax.Record_ctor (l, fs))
               | uu____4493 -> FStar_Pervasives_Native.None)
           in
        (match qopt with
         | FStar_Pervasives_Native.None  ->
             FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor
         | x -> x)
    | FStar_Syntax_Syntax.Sig_declare_typ (uu____4499,uu____4500,uu____4501)
        -> FStar_Pervasives_Native.None
    | uu____4502 -> FStar_Pervasives_Native.None
  
let (lb_fv :
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Ident.lident -> FStar_Syntax_Syntax.fv)
  =
  fun lbs  ->
    fun lid  ->
      let uu____4517 =
        FStar_Util.find_map lbs
          (fun lb  ->
             let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
             let uu____4525 = FStar_Syntax_Syntax.fv_eq_lid fv lid  in
             if uu____4525
             then FStar_Pervasives_Native.Some fv
             else FStar_Pervasives_Native.None)
         in
      FStar_All.pipe_right uu____4517 FStar_Util.must
  
let (ns_of_lid_equals :
  FStar_Ident.lident -> FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    fun ns  ->
      (let uu____4543 =
         let uu____4544 = FStar_Ident.ids_of_lid ns  in
         FStar_List.length uu____4544  in
       (FStar_List.length lid.FStar_Ident.ns) = uu____4543) &&
        (let uu____4552 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
         FStar_Ident.lid_equals uu____4552 ns)
  
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
          let k_global_def source_lid uu___269_4594 =
            match uu___269_4594 with
            | (uu____4601,true ) when exclude_interf ->
                FStar_Pervasives_Native.None
            | (se,uu____4603) ->
                (match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_inductive_typ uu____4606 ->
                     let uu____4623 =
                       let uu____4624 =
                         let uu____4633 =
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None
                            in
                         (uu____4633, false,
                           (se.FStar_Syntax_Syntax.sigattrs))
                          in
                       Term_name uu____4624  in
                     FStar_Pervasives_Native.Some uu____4623
                 | FStar_Syntax_Syntax.Sig_datacon uu____4636 ->
                     let uu____4651 =
                       let uu____4652 =
                         let uu____4661 =
                           let uu____4662 = fv_qual_of_se se  in
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.delta_constant uu____4662
                            in
                         (uu____4661, false,
                           (se.FStar_Syntax_Syntax.sigattrs))
                          in
                       Term_name uu____4652  in
                     FStar_Pervasives_Native.Some uu____4651
                 | FStar_Syntax_Syntax.Sig_let ((uu____4667,lbs),uu____4669)
                     ->
                     let fv = lb_fv lbs source_lid  in
                     let uu____4679 =
                       let uu____4680 =
                         let uu____4689 =
                           FStar_Syntax_Syntax.fvar source_lid
                             fv.FStar_Syntax_Syntax.fv_delta
                             fv.FStar_Syntax_Syntax.fv_qual
                            in
                         (uu____4689, false,
                           (se.FStar_Syntax_Syntax.sigattrs))
                          in
                       Term_name uu____4680  in
                     FStar_Pervasives_Native.Some uu____4679
                 | FStar_Syntax_Syntax.Sig_declare_typ
                     (lid1,uu____4693,uu____4694) ->
                     let quals = se.FStar_Syntax_Syntax.sigquals  in
                     let uu____4698 =
                       any_val ||
                         (FStar_All.pipe_right quals
                            (FStar_Util.for_some
                               (fun uu___263_4702  ->
                                  match uu___263_4702 with
                                  | FStar_Syntax_Syntax.Assumption  -> true
                                  | uu____4703 -> false)))
                        in
                     if uu____4698
                     then
                       let lid2 =
                         let uu____4707 = FStar_Ident.range_of_lid source_lid
                            in
                         FStar_Ident.set_lid_range lid1 uu____4707  in
                       let dd =
                         let uu____4709 =
                           (FStar_Syntax_Util.is_primop_lid lid2) ||
                             (FStar_All.pipe_right quals
                                (FStar_Util.for_some
                                   (fun uu___264_4714  ->
                                      match uu___264_4714 with
                                      | FStar_Syntax_Syntax.Projector
                                          uu____4715 -> true
                                      | FStar_Syntax_Syntax.Discriminator
                                          uu____4720 -> true
                                      | uu____4721 -> false)))
                            in
                         if uu____4709
                         then FStar_Syntax_Syntax.delta_equational
                         else FStar_Syntax_Syntax.delta_constant  in
                       let dd1 =
                         let uu____4724 =
                           (FStar_All.pipe_right quals
                              (FStar_Util.for_some
                                 (fun uu___265_4728  ->
                                    match uu___265_4728 with
                                    | FStar_Syntax_Syntax.Abstract  -> true
                                    | uu____4729 -> false)))
                             ||
                             ((FStar_All.pipe_right quals
                                 (FStar_Util.for_some
                                    (fun uu___266_4733  ->
                                       match uu___266_4733 with
                                       | FStar_Syntax_Syntax.Assumption  ->
                                           true
                                       | uu____4734 -> false)))
                                &&
                                (let uu____4736 =
                                   FStar_All.pipe_right quals
                                     (FStar_Util.for_some
                                        (fun uu___267_4740  ->
                                           match uu___267_4740 with
                                           | FStar_Syntax_Syntax.New  -> true
                                           | uu____4741 -> false))
                                    in
                                 Prims.op_Negation uu____4736))
                            in
                         if uu____4724
                         then FStar_Syntax_Syntax.Delta_abstract dd
                         else dd  in
                       let uu____4743 =
                         FStar_Util.find_map quals
                           (fun uu___268_4748  ->
                              match uu___268_4748 with
                              | FStar_Syntax_Syntax.Reflectable refl_monad ->
                                  FStar_Pervasives_Native.Some refl_monad
                              | uu____4752 -> FStar_Pervasives_Native.None)
                          in
                       (match uu____4743 with
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
                        | uu____4761 ->
                            let uu____4764 =
                              let uu____4765 =
                                let uu____4774 =
                                  let uu____4775 = fv_qual_of_se se  in
                                  FStar_Syntax_Syntax.fvar lid2 dd1
                                    uu____4775
                                   in
                                (uu____4774, false,
                                  (se.FStar_Syntax_Syntax.sigattrs))
                                 in
                              Term_name uu____4765  in
                            FStar_Pervasives_Native.Some uu____4764)
                     else FStar_Pervasives_Native.None
                 | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
                     let uu____4782 =
                       let uu____4783 =
                         let uu____4788 =
                           let uu____4789 =
                             FStar_Ident.range_of_lid source_lid  in
                           FStar_Ident.set_lid_range
                             ne.FStar_Syntax_Syntax.mname uu____4789
                            in
                         (se, uu____4788)  in
                       Eff_name uu____4783  in
                     FStar_Pervasives_Native.Some uu____4782
                 | FStar_Syntax_Syntax.Sig_new_effect ne ->
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
                 | FStar_Syntax_Syntax.Sig_effect_abbrev uu____4799 ->
                     FStar_Pervasives_Native.Some (Eff_name (se, source_lid))
                 | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
                     let uu____4818 =
                       let uu____4819 =
                         let uu____4828 =
                           FStar_Syntax_Syntax.fvar source_lid
                             (FStar_Syntax_Syntax.Delta_constant_at_level
                                (Prims.parse_int "1"))
                             FStar_Pervasives_Native.None
                            in
                         (uu____4828, false, [])  in
                       Term_name uu____4819  in
                     FStar_Pervasives_Native.Some uu____4818
                 | uu____4831 -> FStar_Pervasives_Native.None)
             in
          let k_local_binding r =
            let uu____4852 =
              let uu____4857 = FStar_Ident.range_of_lid lid  in
              found_local_binding uu____4857 r  in
            match uu____4852 with
            | (t,mut) ->
                FStar_Pervasives_Native.Some (Term_name (t, mut, []))
             in
          let k_rec_binding uu____4877 =
            match uu____4877 with
            | (id1,l,dd) ->
                let uu____4889 =
                  let uu____4890 =
                    let uu____4899 =
                      let uu____4900 =
                        let uu____4901 = FStar_Ident.range_of_lid lid  in
                        FStar_Ident.set_lid_range l uu____4901  in
                      FStar_Syntax_Syntax.fvar uu____4900 dd
                        FStar_Pervasives_Native.None
                       in
                    (uu____4899, false, [])  in
                  Term_name uu____4890  in
                FStar_Pervasives_Native.Some uu____4889
             in
          let found_unmangled =
            match lid.FStar_Ident.ns with
            | [] ->
                let uu____4909 = unmangleOpName lid.FStar_Ident.ident  in
                (match uu____4909 with
                 | FStar_Pervasives_Native.Some (t,mut) ->
                     FStar_Pervasives_Native.Some (Term_name (t, mut, []))
                 | uu____4926 -> FStar_Pervasives_Native.None)
            | uu____4933 -> FStar_Pervasives_Native.None  in
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
        let uu____4968 = try_lookup_name true exclude_interf env lid  in
        match uu____4968 with
        | FStar_Pervasives_Native.Some (Eff_name (o,l)) ->
            FStar_Pervasives_Native.Some (o, l)
        | uu____4983 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____5002 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____5002 with
      | FStar_Pervasives_Native.Some (o,l1) ->
          FStar_Pervasives_Native.Some l1
      | uu____5017 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_name_and_attributes :
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident,FStar_Syntax_Syntax.cflags Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____5042 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____5042 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____5058;
             FStar_Syntax_Syntax.sigquals = uu____5059;
             FStar_Syntax_Syntax.sigmeta = uu____5060;
             FStar_Syntax_Syntax.sigattrs = uu____5061;_},l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____5080;
             FStar_Syntax_Syntax.sigquals = uu____5081;
             FStar_Syntax_Syntax.sigmeta = uu____5082;
             FStar_Syntax_Syntax.sigattrs = uu____5083;_},l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (uu____5101,uu____5102,uu____5103,uu____5104,cattributes);
             FStar_Syntax_Syntax.sigrng = uu____5106;
             FStar_Syntax_Syntax.sigquals = uu____5107;
             FStar_Syntax_Syntax.sigmeta = uu____5108;
             FStar_Syntax_Syntax.sigattrs = uu____5109;_},l1)
          -> FStar_Pervasives_Native.Some (l1, cattributes)
      | uu____5131 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_defn :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.eff_decl FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____5156 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____5156 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____5166;
             FStar_Syntax_Syntax.sigquals = uu____5167;
             FStar_Syntax_Syntax.sigmeta = uu____5168;
             FStar_Syntax_Syntax.sigattrs = uu____5169;_},uu____5170)
          -> FStar_Pervasives_Native.Some ne
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____5180;
             FStar_Syntax_Syntax.sigquals = uu____5181;
             FStar_Syntax_Syntax.sigmeta = uu____5182;
             FStar_Syntax_Syntax.sigattrs = uu____5183;_},uu____5184)
          -> FStar_Pervasives_Native.Some ne
      | uu____5193 -> FStar_Pervasives_Native.None
  
let (is_effect_name : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____5210 = try_lookup_effect_name env lid  in
      match uu____5210 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____5213 -> true
  
let (try_lookup_root_effect_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____5226 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____5226 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (l',uu____5236,uu____5237,uu____5238,uu____5239);
             FStar_Syntax_Syntax.sigrng = uu____5240;
             FStar_Syntax_Syntax.sigquals = uu____5241;
             FStar_Syntax_Syntax.sigmeta = uu____5242;
             FStar_Syntax_Syntax.sigattrs = uu____5243;_},uu____5244)
          ->
          let rec aux new_name =
            let uu____5265 =
              FStar_Util.smap_try_find (sigmap env) new_name.FStar_Ident.str
               in
            match uu____5265 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (s,uu____5283) ->
                (match s.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
                     let uu____5291 =
                       let uu____5292 = FStar_Ident.range_of_lid l  in
                       FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname
                         uu____5292
                        in
                     FStar_Pervasives_Native.Some uu____5291
                 | FStar_Syntax_Syntax.Sig_new_effect ne ->
                     let uu____5294 =
                       let uu____5295 = FStar_Ident.range_of_lid l  in
                       FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname
                         uu____5295
                        in
                     FStar_Pervasives_Native.Some uu____5294
                 | FStar_Syntax_Syntax.Sig_effect_abbrev
                     (uu____5296,uu____5297,uu____5298,cmp,uu____5300) ->
                     let l'' = FStar_Syntax_Util.comp_effect_name cmp  in
                     aux l''
                 | uu____5306 -> FStar_Pervasives_Native.None)
             in
          aux l'
      | FStar_Pervasives_Native.Some (uu____5307,l') ->
          FStar_Pervasives_Native.Some l'
      | uu____5313 -> FStar_Pervasives_Native.None
  
let (lookup_letbinding_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___270_5350 =
        match uu___270_5350 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____5359,uu____5360,uu____5361);
             FStar_Syntax_Syntax.sigrng = uu____5362;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____5364;
             FStar_Syntax_Syntax.sigattrs = uu____5365;_},uu____5366)
            -> FStar_Pervasives_Native.Some quals
        | uu____5373 -> FStar_Pervasives_Native.None  in
      let uu____5380 =
        resolve_in_open_namespaces' env lid
          (fun uu____5388  -> FStar_Pervasives_Native.None)
          (fun uu____5392  -> FStar_Pervasives_Native.None) k_global_def
         in
      match uu____5380 with
      | FStar_Pervasives_Native.Some quals -> quals
      | uu____5402 -> []
  
let (try_lookup_module :
  env ->
    FStar_Ident.path ->
      FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun path  ->
      let uu____5419 =
        FStar_List.tryFind
          (fun uu____5434  ->
             match uu____5434 with
             | (mlid,modul) ->
                 let uu____5441 = FStar_Ident.path_of_lid mlid  in
                 uu____5441 = path) env.modules
         in
      match uu____5419 with
      | FStar_Pervasives_Native.Some (uu____5444,modul) ->
          FStar_Pervasives_Native.Some modul
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (try_lookup_let :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___271_5482 =
        match uu___271_5482 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               ((uu____5489,lbs),uu____5491);
             FStar_Syntax_Syntax.sigrng = uu____5492;
             FStar_Syntax_Syntax.sigquals = uu____5493;
             FStar_Syntax_Syntax.sigmeta = uu____5494;
             FStar_Syntax_Syntax.sigattrs = uu____5495;_},uu____5496)
            ->
            let fv = lb_fv lbs lid1  in
            let uu____5510 =
              FStar_Syntax_Syntax.fvar lid1 fv.FStar_Syntax_Syntax.fv_delta
                fv.FStar_Syntax_Syntax.fv_qual
               in
            FStar_Pervasives_Native.Some uu____5510
        | uu____5511 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____5517  -> FStar_Pervasives_Native.None)
        (fun uu____5519  -> FStar_Pervasives_Native.None) k_global_def
  
let (try_lookup_definition :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___272_5550 =
        match uu___272_5550 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               (lbs,uu____5560);
             FStar_Syntax_Syntax.sigrng = uu____5561;
             FStar_Syntax_Syntax.sigquals = uu____5562;
             FStar_Syntax_Syntax.sigmeta = uu____5563;
             FStar_Syntax_Syntax.sigattrs = uu____5564;_},uu____5565)
            ->
            FStar_Util.find_map (FStar_Pervasives_Native.snd lbs)
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inr fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv lid1 ->
                     FStar_Pervasives_Native.Some
                       (lb.FStar_Syntax_Syntax.lbdef)
                 | uu____5588 -> FStar_Pervasives_Native.None)
        | uu____5595 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____5605  -> FStar_Pervasives_Native.None)
        (fun uu____5609  -> FStar_Pervasives_Native.None) k_global_def
  
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
          let uu____5666 = try_lookup_name any_val exclude_interface env lid
             in
          match uu____5666 with
          | FStar_Pervasives_Native.Some (Term_name (e,mut,attrs)) ->
              FStar_Pervasives_Native.Some (e, mut, attrs)
          | uu____5696 -> FStar_Pervasives_Native.None
  
let (drop_attributes :
  (FStar_Syntax_Syntax.term,Prims.bool,FStar_Syntax_Syntax.attribute
                                         Prims.list)
    FStar_Pervasives_Native.tuple3 FStar_Pervasives_Native.option ->
    (FStar_Syntax_Syntax.term,Prims.bool) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option)
  =
  fun x  ->
    match x with
    | FStar_Pervasives_Native.Some (t,mut,uu____5752) ->
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
      let uu____5827 = try_lookup_lid_with_attributes env l  in
      FStar_All.pipe_right uu____5827 drop_attributes
  
let (resolve_to_fully_qualified_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____5866 = try_lookup_lid env l  in
      match uu____5866 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (e,uu____5880) ->
          let uu____5885 =
            let uu____5886 = FStar_Syntax_Subst.compress e  in
            uu____5886.FStar_Syntax_Syntax.n  in
          (match uu____5885 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               FStar_Pervasives_Native.Some
                 ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
           | uu____5892 -> FStar_Pervasives_Native.None)
  
let (shorten_lid' : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____5903 = shorten_module_path env lid.FStar_Ident.ns true  in
      match uu____5903 with
      | (uu____5912,short) ->
          FStar_Ident.lid_of_ns_and_id short lid.FStar_Ident.ident
  
let (shorten_lid : env -> FStar_Ident.lid -> FStar_Ident.lid) =
  fun env  ->
    fun lid  ->
      match env.curmodule with
      | FStar_Pervasives_Native.None  -> shorten_lid' env lid
      | uu____5932 ->
          let lid_without_ns =
            FStar_Ident.lid_of_ns_and_id [] lid.FStar_Ident.ident  in
          let uu____5936 = resolve_to_fully_qualified_name env lid_without_ns
             in
          (match uu____5936 with
           | FStar_Pervasives_Native.Some lid' when
               lid'.FStar_Ident.str = lid.FStar_Ident.str -> lid_without_ns
           | uu____5940 -> shorten_lid' env lid)
  
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
        let uu___292_5974 = env  in
        {
          curmodule = (uu___292_5974.curmodule);
          curmonad = (uu___292_5974.curmonad);
          modules = (uu___292_5974.modules);
          scope_mods = [];
          exported_ids = empty_exported_id_smap;
          trans_exported_ids = (uu___292_5974.trans_exported_ids);
          includes = empty_include_smap;
          sigaccum = (uu___292_5974.sigaccum);
          sigmap = (uu___292_5974.sigmap);
          iface = (uu___292_5974.iface);
          admitted_iface = (uu___292_5974.admitted_iface);
          expect_typ = (uu___292_5974.expect_typ);
          docs = (uu___292_5974.docs);
          remaining_iface_decls = (uu___292_5974.remaining_iface_decls);
          syntax_only = (uu___292_5974.syntax_only);
          ds_hooks = (uu___292_5974.ds_hooks)
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
      let uu____5997 = try_lookup_lid_with_attributes_no_resolve env l  in
      FStar_All.pipe_right uu____5997 drop_attributes
  
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
               (uu____6071,uu____6072,uu____6073);
             FStar_Syntax_Syntax.sigrng = uu____6074;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____6076;
             FStar_Syntax_Syntax.sigattrs = uu____6077;_},uu____6078)
            ->
            let uu____6083 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___273_6087  ->
                      match uu___273_6087 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | uu____6088 -> false))
               in
            if uu____6083
            then
              let uu____6091 =
                FStar_Syntax_Syntax.lid_as_fv lid1
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Pervasives_Native.Some uu____6091
            else FStar_Pervasives_Native.None
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
               uu____6093;
             FStar_Syntax_Syntax.sigrng = uu____6094;
             FStar_Syntax_Syntax.sigquals = uu____6095;
             FStar_Syntax_Syntax.sigmeta = uu____6096;
             FStar_Syntax_Syntax.sigattrs = uu____6097;_},uu____6098)
            ->
            let qual1 = fv_qual_of_se (FStar_Pervasives_Native.fst se)  in
            let uu____6120 =
              FStar_Syntax_Syntax.lid_as_fv lid1
                FStar_Syntax_Syntax.delta_constant qual1
               in
            FStar_Pervasives_Native.Some uu____6120
        | uu____6121 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____6127  -> FStar_Pervasives_Native.None)
        (fun uu____6129  -> FStar_Pervasives_Native.None) k_global_def
  
let (find_all_datacons :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___274_6162 =
        match uu___274_6162 with
        | ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_inductive_typ
               (uu____6171,uu____6172,uu____6173,uu____6174,datas,uu____6176);
             FStar_Syntax_Syntax.sigrng = uu____6177;
             FStar_Syntax_Syntax.sigquals = uu____6178;
             FStar_Syntax_Syntax.sigmeta = uu____6179;
             FStar_Syntax_Syntax.sigattrs = uu____6180;_},uu____6181)
            -> FStar_Pervasives_Native.Some datas
        | uu____6196 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____6206  -> FStar_Pervasives_Native.None)
        (fun uu____6210  -> FStar_Pervasives_Native.None) k_global_def
  
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
  let push1 uu____6286 =
    let uu____6287 =
      let uu____6292 =
        let uu____6295 = FStar_ST.op_Bang record_cache  in
        FStar_List.hd uu____6295  in
      let uu____6351 = FStar_ST.op_Bang record_cache  in uu____6292 ::
        uu____6351
       in
    FStar_ST.op_Colon_Equals record_cache uu____6287  in
  let pop1 uu____6461 =
    let uu____6462 =
      let uu____6467 = FStar_ST.op_Bang record_cache  in
      FStar_List.tl uu____6467  in
    FStar_ST.op_Colon_Equals record_cache uu____6462  in
  let snapshot1 uu____6581 = FStar_Common.snapshot push1 record_cache ()  in
  let rollback1 depth = FStar_Common.rollback pop1 record_cache depth  in
  let peek1 uu____6647 =
    let uu____6648 = FStar_ST.op_Bang record_cache  in
    FStar_List.hd uu____6648  in
  let insert r =
    let uu____6710 =
      let uu____6715 = let uu____6718 = peek1 ()  in r :: uu____6718  in
      let uu____6721 =
        let uu____6726 = FStar_ST.op_Bang record_cache  in
        FStar_List.tl uu____6726  in
      uu____6715 :: uu____6721  in
    FStar_ST.op_Colon_Equals record_cache uu____6710  in
  let filter1 uu____6838 =
    let rc = peek1 ()  in
    let filtered =
      FStar_List.filter
        (fun r  -> Prims.op_Negation r.is_private_or_abstract) rc
       in
    let uu____6847 =
      let uu____6852 =
        let uu____6857 = FStar_ST.op_Bang record_cache  in
        FStar_List.tl uu____6857  in
      filtered :: uu____6852  in
    FStar_ST.op_Colon_Equals record_cache uu____6847  in
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
        | FStar_Syntax_Syntax.Sig_bundle (sigs,uu____7798) ->
            let is_record =
              FStar_Util.for_some
                (fun uu___275_7816  ->
                   match uu___275_7816 with
                   | FStar_Syntax_Syntax.RecordType uu____7817 -> true
                   | FStar_Syntax_Syntax.RecordConstructor uu____7826 -> true
                   | uu____7835 -> false)
               in
            let find_dc dc =
              FStar_All.pipe_right sigs
                (FStar_Util.find_opt
                   (fun uu___276_7859  ->
                      match uu___276_7859 with
                      | {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_datacon
                            (lid,uu____7861,uu____7862,uu____7863,uu____7864,uu____7865);
                          FStar_Syntax_Syntax.sigrng = uu____7866;
                          FStar_Syntax_Syntax.sigquals = uu____7867;
                          FStar_Syntax_Syntax.sigmeta = uu____7868;
                          FStar_Syntax_Syntax.sigattrs = uu____7869;_} ->
                          FStar_Ident.lid_equals dc lid
                      | uu____7878 -> false))
               in
            FStar_All.pipe_right sigs
              (FStar_List.iter
                 (fun uu___277_7913  ->
                    match uu___277_7913 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ
                          (typename,univs1,parms,uu____7917,uu____7918,dc::[]);
                        FStar_Syntax_Syntax.sigrng = uu____7920;
                        FStar_Syntax_Syntax.sigquals = typename_quals;
                        FStar_Syntax_Syntax.sigmeta = uu____7922;
                        FStar_Syntax_Syntax.sigattrs = uu____7923;_} ->
                        let uu____7934 =
                          let uu____7935 = find_dc dc  in
                          FStar_All.pipe_left FStar_Util.must uu____7935  in
                        (match uu____7934 with
                         | {
                             FStar_Syntax_Syntax.sigel =
                               FStar_Syntax_Syntax.Sig_datacon
                               (constrname,uu____7941,t,uu____7943,uu____7944,uu____7945);
                             FStar_Syntax_Syntax.sigrng = uu____7946;
                             FStar_Syntax_Syntax.sigquals = uu____7947;
                             FStar_Syntax_Syntax.sigmeta = uu____7948;
                             FStar_Syntax_Syntax.sigattrs = uu____7949;_} ->
                             let uu____7958 =
                               FStar_Syntax_Util.arrow_formals t  in
                             (match uu____7958 with
                              | (formals,uu____7974) ->
                                  let is_rec = is_record typename_quals  in
                                  let formals' =
                                    FStar_All.pipe_right formals
                                      (FStar_List.collect
                                         (fun uu____8027  ->
                                            match uu____8027 with
                                            | (x,q) ->
                                                let uu____8040 =
                                                  (FStar_Syntax_Syntax.is_null_bv
                                                     x)
                                                    ||
                                                    (is_rec &&
                                                       (FStar_Syntax_Syntax.is_implicit
                                                          q))
                                                   in
                                                if uu____8040
                                                then []
                                                else [(x, q)]))
                                     in
                                  let fields' =
                                    FStar_All.pipe_right formals'
                                      (FStar_List.map
                                         (fun uu____8093  ->
                                            match uu____8093 with
                                            | (x,q) ->
                                                let uu____8106 =
                                                  if is_rec
                                                  then
                                                    FStar_Syntax_Util.unmangle_field_name
                                                      x.FStar_Syntax_Syntax.ppname
                                                  else
                                                    x.FStar_Syntax_Syntax.ppname
                                                   in
                                                (uu____8106,
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
                                  ((let uu____8119 =
                                      let uu____8122 =
                                        FStar_ST.op_Bang new_globs  in
                                      (Record_or_dc record) :: uu____8122  in
                                    FStar_ST.op_Colon_Equals new_globs
                                      uu____8119);
                                   (match () with
                                    | () ->
                                        ((let add_field uu____8225 =
                                            match uu____8225 with
                                            | (id1,uu____8231) ->
                                                let modul =
                                                  let uu____8233 =
                                                    FStar_Ident.lid_of_ids
                                                      constrname.FStar_Ident.ns
                                                     in
                                                  uu____8233.FStar_Ident.str
                                                   in
                                                let uu____8234 =
                                                  get_exported_id_set e modul
                                                   in
                                                (match uu____8234 with
                                                 | FStar_Pervasives_Native.Some
                                                     my_ex ->
                                                     let my_exported_ids =
                                                       my_ex
                                                         Exported_id_field
                                                        in
                                                     ((let uu____8268 =
                                                         let uu____8269 =
                                                           FStar_ST.op_Bang
                                                             my_exported_ids
                                                            in
                                                         FStar_Util.set_add
                                                           id1.FStar_Ident.idText
                                                           uu____8269
                                                          in
                                                       FStar_ST.op_Colon_Equals
                                                         my_exported_ids
                                                         uu____8268);
                                                      (match () with
                                                       | () ->
                                                           let projname =
                                                             let uu____8355 =
                                                               let uu____8356
                                                                 =
                                                                 FStar_Syntax_Util.mk_field_projector_name_from_ident
                                                                   constrname
                                                                   id1
                                                                  in
                                                               uu____8356.FStar_Ident.ident
                                                                in
                                                             uu____8355.FStar_Ident.idText
                                                              in
                                                           let uu____8358 =
                                                             let uu____8359 =
                                                               FStar_ST.op_Bang
                                                                 my_exported_ids
                                                                in
                                                             FStar_Util.set_add
                                                               projname
                                                               uu____8359
                                                              in
                                                           FStar_ST.op_Colon_Equals
                                                             my_exported_ids
                                                             uu____8358))
                                                 | FStar_Pervasives_Native.None
                                                      -> ())
                                             in
                                          FStar_List.iter add_field fields');
                                         (match () with
                                          | () -> insert_record_cache record)))))
                         | uu____8453 -> ())
                    | uu____8454 -> ()))
        | uu____8455 -> ()
  
let (try_lookup_record_or_dc_by_field_name :
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option) =
  fun env  ->
    fun fieldname  ->
      let find_in_cache fieldname1 =
        let uu____8476 =
          ((fieldname1.FStar_Ident.ns), (fieldname1.FStar_Ident.ident))  in
        match uu____8476 with
        | (ns,id1) ->
            let uu____8493 = peek_record_cache ()  in
            FStar_Util.find_map uu____8493
              (fun record  ->
                 let uu____8499 =
                   find_in_record ns id1 record (fun r  -> Cont_ok r)  in
                 option_of_cont
                   (fun uu____8505  -> FStar_Pervasives_Native.None)
                   uu____8499)
         in
      resolve_in_open_namespaces'' env fieldname Exported_id_field
        (fun uu____8507  -> Cont_ignore) (fun uu____8509  -> Cont_ignore)
        (fun r  -> Cont_ok r)
        (fun fn  ->
           let uu____8515 = find_in_cache fn  in
           cont_of_option Cont_ignore uu____8515)
        (fun k  -> fun uu____8521  -> k)
  
let (try_lookup_record_by_field_name :
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option) =
  fun env  ->
    fun fieldname  ->
      let uu____8536 = try_lookup_record_or_dc_by_field_name env fieldname
         in
      match uu____8536 with
      | FStar_Pervasives_Native.Some r when r.is_record ->
          FStar_Pervasives_Native.Some r
      | uu____8542 -> FStar_Pervasives_Native.None
  
let (belongs_to_record :
  env -> FStar_Ident.lident -> record_or_dc -> Prims.bool) =
  fun env  ->
    fun lid  ->
      fun record  ->
        let uu____8560 = try_lookup_record_by_field_name env lid  in
        match uu____8560 with
        | FStar_Pervasives_Native.Some record' when
            let uu____8564 =
              let uu____8565 =
                FStar_Ident.path_of_ns (record.typename).FStar_Ident.ns  in
              FStar_Ident.text_of_path uu____8565  in
            let uu____8566 =
              let uu____8567 =
                FStar_Ident.path_of_ns (record'.typename).FStar_Ident.ns  in
              FStar_Ident.text_of_path uu____8567  in
            uu____8564 = uu____8566 ->
            let uu____8568 =
              find_in_record (record.typename).FStar_Ident.ns
                lid.FStar_Ident.ident record (fun uu____8572  -> Cont_ok ())
               in
            (match uu____8568 with
             | Cont_ok uu____8573 -> true
             | uu____8574 -> false)
        | uu____8577 -> false
  
let (try_lookup_dc_by_field_name :
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident,Prims.bool) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun fieldname  ->
      let uu____8596 = try_lookup_record_or_dc_by_field_name env fieldname
         in
      match uu____8596 with
      | FStar_Pervasives_Native.Some r ->
          let uu____8606 =
            let uu____8611 =
              let uu____8612 =
                FStar_Ident.lid_of_ids
                  (FStar_List.append (r.typename).FStar_Ident.ns
                     [r.constrname])
                 in
              let uu____8613 = FStar_Ident.range_of_lid fieldname  in
              FStar_Ident.set_lid_range uu____8612 uu____8613  in
            (uu____8611, (r.is_record))  in
          FStar_Pervasives_Native.Some uu____8606
      | uu____8618 -> FStar_Pervasives_Native.None
  
let (string_set_ref_new : unit -> Prims.string FStar_Util.set FStar_ST.ref) =
  fun uu____8644  ->
    let uu____8645 = FStar_Util.new_set FStar_Util.compare  in
    FStar_Util.mk_ref uu____8645
  
let (exported_id_set_new :
  unit -> exported_id_kind -> Prims.string FStar_Util.set FStar_ST.ref) =
  fun uu____8672  ->
    let term_type_set = string_set_ref_new ()  in
    let field_set = string_set_ref_new ()  in
    fun uu___278_8683  ->
      match uu___278_8683 with
      | Exported_id_term_type  -> term_type_set
      | Exported_id_field  -> field_set
  
let (unique :
  Prims.bool -> Prims.bool -> env -> FStar_Ident.lident -> Prims.bool) =
  fun any_val  ->
    fun exclude_interface  ->
      fun env  ->
        fun lid  ->
          let filter_scope_mods uu___279_8735 =
            match uu___279_8735 with
            | Rec_binding uu____8736 -> true
            | uu____8737 -> false  in
          let this_env =
            let uu___293_8739 = env  in
            let uu____8740 =
              FStar_List.filter filter_scope_mods env.scope_mods  in
            {
              curmodule = (uu___293_8739.curmodule);
              curmonad = (uu___293_8739.curmonad);
              modules = (uu___293_8739.modules);
              scope_mods = uu____8740;
              exported_ids = empty_exported_id_smap;
              trans_exported_ids = (uu___293_8739.trans_exported_ids);
              includes = empty_include_smap;
              sigaccum = (uu___293_8739.sigaccum);
              sigmap = (uu___293_8739.sigmap);
              iface = (uu___293_8739.iface);
              admitted_iface = (uu___293_8739.admitted_iface);
              expect_typ = (uu___293_8739.expect_typ);
              docs = (uu___293_8739.docs);
              remaining_iface_decls = (uu___293_8739.remaining_iface_decls);
              syntax_only = (uu___293_8739.syntax_only);
              ds_hooks = (uu___293_8739.ds_hooks)
            }  in
          let uu____8743 =
            try_lookup_lid' any_val exclude_interface this_env lid  in
          match uu____8743 with
          | FStar_Pervasives_Native.None  -> true
          | FStar_Pervasives_Native.Some uu____8762 -> false
  
let (push_scope_mod : env -> scope_mod -> env) =
  fun env  ->
    fun scope_mod  ->
      let uu___294_8789 = env  in
      {
        curmodule = (uu___294_8789.curmodule);
        curmonad = (uu___294_8789.curmonad);
        modules = (uu___294_8789.modules);
        scope_mods = (scope_mod :: (env.scope_mods));
        exported_ids = (uu___294_8789.exported_ids);
        trans_exported_ids = (uu___294_8789.trans_exported_ids);
        includes = (uu___294_8789.includes);
        sigaccum = (uu___294_8789.sigaccum);
        sigmap = (uu___294_8789.sigmap);
        iface = (uu___294_8789.iface);
        admitted_iface = (uu___294_8789.admitted_iface);
        expect_typ = (uu___294_8789.expect_typ);
        docs = (uu___294_8789.docs);
        remaining_iface_decls = (uu___294_8789.remaining_iface_decls);
        syntax_only = (uu___294_8789.syntax_only);
        ds_hooks = (uu___294_8789.ds_hooks)
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
        let uu____8854 =
          (unique false true env l) || (FStar_Options.interactive ())  in
        if uu____8854
        then push_scope_mod env (Rec_binding (x, l, dd))
        else
          (let uu____8856 = FStar_Ident.range_of_lid l  in
           FStar_Errors.raise_error
             (FStar_Errors.Fatal_DuplicateTopLevelNames,
               (Prims.strcat "Duplicate top-level names " l.FStar_Ident.str))
             uu____8856)
  
let (push_sigelt' : Prims.bool -> env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun fail_on_dup  ->
    fun env  ->
      fun s  ->
        let err l =
          let sopt = FStar_Util.smap_try_find (sigmap env) l.FStar_Ident.str
             in
          let r =
            match sopt with
            | FStar_Pervasives_Native.Some (se,uu____8891) ->
                let uu____8896 =
                  FStar_Util.find_opt (FStar_Ident.lid_equals l)
                    (FStar_Syntax_Util.lids_of_sigelt se)
                   in
                (match uu____8896 with
                 | FStar_Pervasives_Native.Some l1 ->
                     let uu____8900 = FStar_Ident.range_of_lid l1  in
                     FStar_All.pipe_left FStar_Range.string_of_range
                       uu____8900
                 | FStar_Pervasives_Native.None  -> "<unknown>")
            | FStar_Pervasives_Native.None  -> "<unknown>"  in
          let uu____8905 =
            let uu____8910 =
              let uu____8911 = FStar_Ident.text_of_lid l  in
              FStar_Util.format2
                "Duplicate top-level names [%s]; previously declared at %s"
                uu____8911 r
               in
            (FStar_Errors.Fatal_DuplicateTopLevelNames, uu____8910)  in
          let uu____8912 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____8905 uu____8912  in
        let globals = FStar_Util.mk_ref env.scope_mods  in
        let env1 =
          let uu____8921 =
            match s.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_let uu____8930 -> (false, true)
            | FStar_Syntax_Syntax.Sig_bundle uu____8937 -> (false, true)
            | uu____8946 -> (false, false)  in
          match uu____8921 with
          | (any_val,exclude_interface) ->
              let lids = FStar_Syntax_Util.lids_of_sigelt s  in
              let uu____8952 =
                FStar_Util.find_map lids
                  (fun l  ->
                     let uu____8958 =
                       let uu____8959 =
                         unique any_val exclude_interface env l  in
                       Prims.op_Negation uu____8959  in
                     if uu____8958
                     then FStar_Pervasives_Native.Some l
                     else FStar_Pervasives_Native.None)
                 in
              (match uu____8952 with
               | FStar_Pervasives_Native.Some l when fail_on_dup -> err l
               | uu____8964 ->
                   (extract_record env globals s;
                    (let uu___295_8990 = env  in
                     {
                       curmodule = (uu___295_8990.curmodule);
                       curmonad = (uu___295_8990.curmonad);
                       modules = (uu___295_8990.modules);
                       scope_mods = (uu___295_8990.scope_mods);
                       exported_ids = (uu___295_8990.exported_ids);
                       trans_exported_ids =
                         (uu___295_8990.trans_exported_ids);
                       includes = (uu___295_8990.includes);
                       sigaccum = (s :: (env.sigaccum));
                       sigmap = (uu___295_8990.sigmap);
                       iface = (uu___295_8990.iface);
                       admitted_iface = (uu___295_8990.admitted_iface);
                       expect_typ = (uu___295_8990.expect_typ);
                       docs = (uu___295_8990.docs);
                       remaining_iface_decls =
                         (uu___295_8990.remaining_iface_decls);
                       syntax_only = (uu___295_8990.syntax_only);
                       ds_hooks = (uu___295_8990.ds_hooks)
                     })))
           in
        let env2 =
          let uu___296_8992 = env1  in
          let uu____8993 = FStar_ST.op_Bang globals  in
          {
            curmodule = (uu___296_8992.curmodule);
            curmonad = (uu___296_8992.curmonad);
            modules = (uu___296_8992.modules);
            scope_mods = uu____8993;
            exported_ids = (uu___296_8992.exported_ids);
            trans_exported_ids = (uu___296_8992.trans_exported_ids);
            includes = (uu___296_8992.includes);
            sigaccum = (uu___296_8992.sigaccum);
            sigmap = (uu___296_8992.sigmap);
            iface = (uu___296_8992.iface);
            admitted_iface = (uu___296_8992.admitted_iface);
            expect_typ = (uu___296_8992.expect_typ);
            docs = (uu___296_8992.docs);
            remaining_iface_decls = (uu___296_8992.remaining_iface_decls);
            syntax_only = (uu___296_8992.syntax_only);
            ds_hooks = (uu___296_8992.ds_hooks)
          }  in
        let uu____9041 =
          match s.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____9067) ->
              let uu____9076 =
                FStar_List.map
                  (fun se  -> ((FStar_Syntax_Util.lids_of_sigelt se), se))
                  ses
                 in
              (env2, uu____9076)
          | uu____9103 -> (env2, [((FStar_Syntax_Util.lids_of_sigelt s), s)])
           in
        match uu____9041 with
        | (env3,lss) ->
            (FStar_All.pipe_right lss
               (FStar_List.iter
                  (fun uu____9162  ->
                     match uu____9162 with
                     | (lids,se) ->
                         FStar_All.pipe_right lids
                           (FStar_List.iter
                              (fun lid  ->
                                 (let uu____9184 =
                                    let uu____9187 = FStar_ST.op_Bang globals
                                       in
                                    (Top_level_def (lid.FStar_Ident.ident))
                                      :: uu____9187
                                     in
                                  FStar_ST.op_Colon_Equals globals uu____9184);
                                 (match () with
                                  | () ->
                                      let modul =
                                        let uu____9281 =
                                          FStar_Ident.lid_of_ids
                                            lid.FStar_Ident.ns
                                           in
                                        uu____9281.FStar_Ident.str  in
                                      ((let uu____9283 =
                                          get_exported_id_set env3 modul  in
                                        match uu____9283 with
                                        | FStar_Pervasives_Native.Some f ->
                                            let my_exported_ids =
                                              f Exported_id_term_type  in
                                            let uu____9316 =
                                              let uu____9317 =
                                                FStar_ST.op_Bang
                                                  my_exported_ids
                                                 in
                                              FStar_Util.set_add
                                                (lid.FStar_Ident.ident).FStar_Ident.idText
                                                uu____9317
                                               in
                                            FStar_ST.op_Colon_Equals
                                              my_exported_ids uu____9316
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
                let uu___297_9413 = env3  in
                let uu____9414 = FStar_ST.op_Bang globals  in
                {
                  curmodule = (uu___297_9413.curmodule);
                  curmonad = (uu___297_9413.curmonad);
                  modules = (uu___297_9413.modules);
                  scope_mods = uu____9414;
                  exported_ids = (uu___297_9413.exported_ids);
                  trans_exported_ids = (uu___297_9413.trans_exported_ids);
                  includes = (uu___297_9413.includes);
                  sigaccum = (uu___297_9413.sigaccum);
                  sigmap = (uu___297_9413.sigmap);
                  iface = (uu___297_9413.iface);
                  admitted_iface = (uu___297_9413.admitted_iface);
                  expect_typ = (uu___297_9413.expect_typ);
                  docs = (uu___297_9413.docs);
                  remaining_iface_decls =
                    (uu___297_9413.remaining_iface_decls);
                  syntax_only = (uu___297_9413.syntax_only);
                  ds_hooks = (uu___297_9413.ds_hooks)
                }  in
              env4))
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  -> fun se  -> push_sigelt' true env se 
let (push_sigelt_force : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  -> fun se  -> push_sigelt' false env se 
let (push_namespace : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun ns  ->
      let uu____9492 =
        let uu____9497 = resolve_module_name env ns false  in
        match uu____9497 with
        | FStar_Pervasives_Native.None  ->
            let modules = env.modules  in
            let uu____9511 =
              FStar_All.pipe_right modules
                (FStar_Util.for_some
                   (fun uu____9527  ->
                      match uu____9527 with
                      | (m,uu____9533) ->
                          let uu____9534 =
                            let uu____9535 = FStar_Ident.text_of_lid m  in
                            Prims.strcat uu____9535 "."  in
                          let uu____9536 =
                            let uu____9537 = FStar_Ident.text_of_lid ns  in
                            Prims.strcat uu____9537 "."  in
                          FStar_Util.starts_with uu____9534 uu____9536))
               in
            if uu____9511
            then (ns, Open_namespace)
            else
              (let uu____9543 =
                 let uu____9548 =
                   let uu____9549 = FStar_Ident.text_of_lid ns  in
                   FStar_Util.format1 "Namespace %s cannot be found"
                     uu____9549
                    in
                 (FStar_Errors.Fatal_NameSpaceNotFound, uu____9548)  in
               let uu____9550 = FStar_Ident.range_of_lid ns  in
               FStar_Errors.raise_error uu____9543 uu____9550)
        | FStar_Pervasives_Native.Some ns' ->
            (fail_if_curmodule env ns ns'; (ns', Open_module))
         in
      match uu____9492 with
      | (ns',kd) ->
          ((env.ds_hooks).ds_push_open_hook env (ns', kd);
           push_scope_mod env (Open_module_or_namespace (ns', kd)))
  
let (push_include : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun ns  ->
      let ns0 = ns  in
      let uu____9571 = resolve_module_name env ns false  in
      match uu____9571 with
      | FStar_Pervasives_Native.Some ns1 ->
          ((env.ds_hooks).ds_push_include_hook env ns1;
           fail_if_curmodule env ns0 ns1;
           (let env1 =
              push_scope_mod env
                (Open_module_or_namespace (ns1, Open_module))
               in
            let curmod =
              let uu____9579 = current_module env1  in
              uu____9579.FStar_Ident.str  in
            (let uu____9581 = FStar_Util.smap_try_find env1.includes curmod
                in
             match uu____9581 with
             | FStar_Pervasives_Native.None  -> ()
             | FStar_Pervasives_Native.Some incl ->
                 let uu____9605 =
                   let uu____9608 = FStar_ST.op_Bang incl  in ns1 ::
                     uu____9608
                    in
                 FStar_ST.op_Colon_Equals incl uu____9605);
            (match () with
             | () ->
                 let uu____9701 =
                   get_trans_exported_id_set env1 ns1.FStar_Ident.str  in
                 (match uu____9701 with
                  | FStar_Pervasives_Native.Some ns_trans_exports ->
                      ((let uu____9721 =
                          let uu____9816 = get_exported_id_set env1 curmod
                             in
                          let uu____9862 =
                            get_trans_exported_id_set env1 curmod  in
                          (uu____9816, uu____9862)  in
                        match uu____9721 with
                        | (FStar_Pervasives_Native.Some
                           cur_exports,FStar_Pervasives_Native.Some
                           cur_trans_exports) ->
                            let update_exports k =
                              let ns_ex =
                                let uu____10269 = ns_trans_exports k  in
                                FStar_ST.op_Bang uu____10269  in
                              let ex = cur_exports k  in
                              (let uu____10443 =
                                 let uu____10446 = FStar_ST.op_Bang ex  in
                                 FStar_Util.set_difference uu____10446 ns_ex
                                  in
                               FStar_ST.op_Colon_Equals ex uu____10443);
                              (match () with
                               | () ->
                                   let trans_ex = cur_trans_exports k  in
                                   let uu____10638 =
                                     let uu____10641 =
                                       FStar_ST.op_Bang trans_ex  in
                                     FStar_Util.set_union uu____10641 ns_ex
                                      in
                                   FStar_ST.op_Colon_Equals trans_ex
                                     uu____10638)
                               in
                            FStar_List.iter update_exports
                              all_exported_id_kinds
                        | uu____10770 -> ());
                       (match () with | () -> env1))
                  | FStar_Pervasives_Native.None  ->
                      let uu____10870 =
                        let uu____10875 =
                          FStar_Util.format1
                            "include: Module %s was not prepared"
                            ns1.FStar_Ident.str
                           in
                        (FStar_Errors.Fatal_IncludeModuleNotPrepared,
                          uu____10875)
                         in
                      let uu____10876 = FStar_Ident.range_of_lid ns1  in
                      FStar_Errors.raise_error uu____10870 uu____10876))))
      | uu____10877 ->
          let uu____10880 =
            let uu____10885 =
              FStar_Util.format1 "include: Module %s cannot be found"
                ns.FStar_Ident.str
               in
            (FStar_Errors.Fatal_ModuleNotFound, uu____10885)  in
          let uu____10886 = FStar_Ident.range_of_lid ns  in
          FStar_Errors.raise_error uu____10880 uu____10886
  
let (push_module_abbrev :
  env -> FStar_Ident.ident -> FStar_Ident.lident -> env) =
  fun env  ->
    fun x  ->
      fun l  ->
        let uu____10902 = module_is_defined env l  in
        if uu____10902
        then
          (fail_if_curmodule env l l;
           (env.ds_hooks).ds_push_module_abbrev_hook env x l;
           push_scope_mod env (Module_abbrev (x, l)))
        else
          (let uu____10906 =
             let uu____10911 =
               let uu____10912 = FStar_Ident.text_of_lid l  in
               FStar_Util.format1 "Module %s cannot be found" uu____10912  in
             (FStar_Errors.Fatal_ModuleNotFound, uu____10911)  in
           let uu____10913 = FStar_Ident.range_of_lid l  in
           FStar_Errors.raise_error uu____10906 uu____10913)
  
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
            ((let uu____10935 =
                FStar_Util.smap_try_find env.docs l.FStar_Ident.str  in
              match uu____10935 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some old_doc ->
                  let uu____10939 = FStar_Ident.range_of_lid l  in
                  let uu____10940 =
                    let uu____10945 =
                      let uu____10946 = FStar_Ident.string_of_lid l  in
                      let uu____10947 =
                        FStar_Parser_AST.string_of_fsdoc old_doc  in
                      let uu____10948 = FStar_Parser_AST.string_of_fsdoc doc1
                         in
                      FStar_Util.format3
                        "Overwriting doc of %s; old doc was [%s]; new doc are [%s]"
                        uu____10946 uu____10947 uu____10948
                       in
                    (FStar_Errors.Warning_DocOverwrite, uu____10945)  in
                  FStar_Errors.log_issue uu____10939 uu____10940);
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
                      let uu____10990 =
                        FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption)
                         in
                      Prims.op_Negation uu____10990 ->
                      let uu____10993 =
                        FStar_Util.smap_try_find (sigmap env)
                          l.FStar_Ident.str
                         in
                      (match uu____10993 with
                       | FStar_Pervasives_Native.Some
                           ({
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_let uu____11006;
                              FStar_Syntax_Syntax.sigrng = uu____11007;
                              FStar_Syntax_Syntax.sigquals = uu____11008;
                              FStar_Syntax_Syntax.sigmeta = uu____11009;
                              FStar_Syntax_Syntax.sigattrs = uu____11010;_},uu____11011)
                           -> lids
                       | FStar_Pervasives_Native.Some
                           ({
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_inductive_typ
                                uu____11026;
                              FStar_Syntax_Syntax.sigrng = uu____11027;
                              FStar_Syntax_Syntax.sigquals = uu____11028;
                              FStar_Syntax_Syntax.sigmeta = uu____11029;
                              FStar_Syntax_Syntax.sigattrs = uu____11030;_},uu____11031)
                           -> lids
                       | uu____11056 ->
                           ((let uu____11064 =
                               let uu____11065 = FStar_Options.interactive ()
                                  in
                               Prims.op_Negation uu____11065  in
                             if uu____11064
                             then
                               let uu____11066 = FStar_Ident.range_of_lid l
                                  in
                               let uu____11067 =
                                 let uu____11072 =
                                   let uu____11073 =
                                     FStar_Ident.string_of_lid l  in
                                   FStar_Util.format1
                                     "Admitting %s without a definition"
                                     uu____11073
                                    in
                                 (FStar_Errors.Warning_AdmitWithoutDefinition,
                                   uu____11072)
                                  in
                               FStar_Errors.log_issue uu____11066 uu____11067
                             else ());
                            (let quals = FStar_Syntax_Syntax.Assumption ::
                               (se.FStar_Syntax_Syntax.sigquals)  in
                             FStar_Util.smap_add (sigmap env)
                               l.FStar_Ident.str
                               ((let uu___298_11084 = se  in
                                 {
                                   FStar_Syntax_Syntax.sigel =
                                     (uu___298_11084.FStar_Syntax_Syntax.sigel);
                                   FStar_Syntax_Syntax.sigrng =
                                     (uu___298_11084.FStar_Syntax_Syntax.sigrng);
                                   FStar_Syntax_Syntax.sigquals = quals;
                                   FStar_Syntax_Syntax.sigmeta =
                                     (uu___298_11084.FStar_Syntax_Syntax.sigmeta);
                                   FStar_Syntax_Syntax.sigattrs =
                                     (uu___298_11084.FStar_Syntax_Syntax.sigattrs)
                                 }), false);
                             l
                             ::
                             lids)))
                  | uu____11085 -> lids) [])
         in
      let uu___299_11086 = m  in
      let uu____11087 =
        FStar_All.pipe_right m.FStar_Syntax_Syntax.declarations
          (FStar_List.map
             (fun s  ->
                match s.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_declare_typ
                    (lid,uu____11097,uu____11098) when
                    FStar_List.existsb
                      (fun l  -> FStar_Ident.lid_equals l lid)
                      admitted_sig_lids
                    ->
                    let uu___300_11101 = s  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___300_11101.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___300_11101.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals =
                        (FStar_Syntax_Syntax.Assumption ::
                        (s.FStar_Syntax_Syntax.sigquals));
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___300_11101.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___300_11101.FStar_Syntax_Syntax.sigattrs)
                    }
                | uu____11102 -> s))
         in
      {
        FStar_Syntax_Syntax.name = (uu___299_11086.FStar_Syntax_Syntax.name);
        FStar_Syntax_Syntax.declarations = uu____11087;
        FStar_Syntax_Syntax.exports =
          (uu___299_11086.FStar_Syntax_Syntax.exports);
        FStar_Syntax_Syntax.is_interface =
          (uu___299_11086.FStar_Syntax_Syntax.is_interface)
      }
  
let (finish : env -> FStar_Syntax_Syntax.modul -> env) =
  fun env  ->
    fun modul  ->
      FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations
        (FStar_List.iter
           (fun se  ->
              let quals = se.FStar_Syntax_Syntax.sigquals  in
              match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_bundle (ses,uu____11125) ->
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
                                (lid,uu____11145,uu____11146,uu____11147,uu____11148,uu____11149)
                                ->
                                FStar_Util.smap_remove (sigmap env)
                                  lid.FStar_Ident.str
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (lid,univ_names,binders,typ,uu____11162,uu____11163)
                                ->
                                (FStar_Util.smap_remove (sigmap env)
                                   lid.FStar_Ident.str;
                                 if
                                   Prims.op_Negation
                                     (FStar_List.contains
                                        FStar_Syntax_Syntax.Private quals)
                                 then
                                   (let sigel =
                                      let uu____11178 =
                                        let uu____11185 =
                                          let uu____11186 =
                                            FStar_Ident.range_of_lid lid  in
                                          let uu____11187 =
                                            let uu____11194 =
                                              let uu____11195 =
                                                let uu____11210 =
                                                  FStar_Syntax_Syntax.mk_Total
                                                    typ
                                                   in
                                                (binders, uu____11210)  in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____11195
                                               in
                                            FStar_Syntax_Syntax.mk
                                              uu____11194
                                             in
                                          uu____11187
                                            FStar_Pervasives_Native.None
                                            uu____11186
                                           in
                                        (lid, univ_names, uu____11185)  in
                                      FStar_Syntax_Syntax.Sig_declare_typ
                                        uu____11178
                                       in
                                    let se2 =
                                      let uu___301_11227 = se1  in
                                      {
                                        FStar_Syntax_Syntax.sigel = sigel;
                                        FStar_Syntax_Syntax.sigrng =
                                          (uu___301_11227.FStar_Syntax_Syntax.sigrng);
                                        FStar_Syntax_Syntax.sigquals =
                                          (FStar_Syntax_Syntax.Assumption ::
                                          quals);
                                        FStar_Syntax_Syntax.sigmeta =
                                          (uu___301_11227.FStar_Syntax_Syntax.sigmeta);
                                        FStar_Syntax_Syntax.sigattrs =
                                          (uu___301_11227.FStar_Syntax_Syntax.sigattrs)
                                      }  in
                                    FStar_Util.smap_add (sigmap env)
                                      lid.FStar_Ident.str (se2, false))
                                 else ())
                            | uu____11233 -> ()))
                  else ()
              | FStar_Syntax_Syntax.Sig_declare_typ
                  (lid,uu____11236,uu____11237) ->
                  if FStar_List.contains FStar_Syntax_Syntax.Private quals
                  then
                    FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str
                  else ()
              | FStar_Syntax_Syntax.Sig_let ((uu____11243,lbs),uu____11245)
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
                             let uu____11260 =
                               let uu____11261 =
                                 let uu____11262 =
                                   let uu____11265 =
                                     FStar_Util.right
                                       lb.FStar_Syntax_Syntax.lbname
                                      in
                                   uu____11265.FStar_Syntax_Syntax.fv_name
                                    in
                                 uu____11262.FStar_Syntax_Syntax.v  in
                               uu____11261.FStar_Ident.str  in
                             FStar_Util.smap_remove (sigmap env) uu____11260))
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
                               let uu____11279 =
                                 let uu____11282 =
                                   FStar_Util.right
                                     lb.FStar_Syntax_Syntax.lbname
                                    in
                                 uu____11282.FStar_Syntax_Syntax.fv_name  in
                               uu____11279.FStar_Syntax_Syntax.v  in
                             let quals1 = FStar_Syntax_Syntax.Assumption ::
                               quals  in
                             let decl =
                               let uu___302_11287 = se  in
                               {
                                 FStar_Syntax_Syntax.sigel =
                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                      (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                        (lb.FStar_Syntax_Syntax.lbtyp)));
                                 FStar_Syntax_Syntax.sigrng =
                                   (uu___302_11287.FStar_Syntax_Syntax.sigrng);
                                 FStar_Syntax_Syntax.sigquals = quals1;
                                 FStar_Syntax_Syntax.sigmeta =
                                   (uu___302_11287.FStar_Syntax_Syntax.sigmeta);
                                 FStar_Syntax_Syntax.sigattrs =
                                   (uu___302_11287.FStar_Syntax_Syntax.sigattrs)
                               }  in
                             FStar_Util.smap_add (sigmap env)
                               lid.FStar_Ident.str (decl, false)))
                   else ())
              | uu____11293 -> ()));
      (let curmod =
         let uu____11295 = current_module env  in uu____11295.FStar_Ident.str
          in
       (let uu____11297 =
          let uu____11392 = get_exported_id_set env curmod  in
          let uu____11438 = get_trans_exported_id_set env curmod  in
          (uu____11392, uu____11438)  in
        match uu____11297 with
        | (FStar_Pervasives_Native.Some cur_ex,FStar_Pervasives_Native.Some
           cur_trans_ex) ->
            let update_exports eikind =
              let cur_ex_set =
                let uu____11847 = cur_ex eikind  in
                FStar_ST.op_Bang uu____11847  in
              let cur_trans_ex_set_ref = cur_trans_ex eikind  in
              let uu____12034 =
                let uu____12037 = FStar_ST.op_Bang cur_trans_ex_set_ref  in
                FStar_Util.set_union cur_ex_set uu____12037  in
              FStar_ST.op_Colon_Equals cur_trans_ex_set_ref uu____12034  in
            FStar_List.iter update_exports all_exported_id_kinds
        | uu____12166 -> ());
       (match () with
        | () ->
            (filter_record_cache ();
             (match () with
              | () ->
                  let uu___303_12262 = env  in
                  {
                    curmodule = FStar_Pervasives_Native.None;
                    curmonad = (uu___303_12262.curmonad);
                    modules = (((modul.FStar_Syntax_Syntax.name), modul) ::
                      (env.modules));
                    scope_mods = [];
                    exported_ids = (uu___303_12262.exported_ids);
                    trans_exported_ids = (uu___303_12262.trans_exported_ids);
                    includes = (uu___303_12262.includes);
                    sigaccum = [];
                    sigmap = (uu___303_12262.sigmap);
                    iface = (uu___303_12262.iface);
                    admitted_iface = (uu___303_12262.admitted_iface);
                    expect_typ = (uu___303_12262.expect_typ);
                    docs = (uu___303_12262.docs);
                    remaining_iface_decls =
                      (uu___303_12262.remaining_iface_decls);
                    syntax_only = (uu___303_12262.syntax_only);
                    ds_hooks = (uu___303_12262.ds_hooks)
                  }))))
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push : env -> env) =
  fun env  ->
    FStar_Util.atomically
      (fun uu____12298  ->
         push_record_cache ();
         (let uu____12301 =
            let uu____12304 = FStar_ST.op_Bang stack  in env :: uu____12304
             in
          FStar_ST.op_Colon_Equals stack uu____12301);
         (let uu___304_12353 = env  in
          let uu____12354 = FStar_Util.smap_copy env.exported_ids  in
          let uu____12359 = FStar_Util.smap_copy env.trans_exported_ids  in
          let uu____12364 = FStar_Util.smap_copy env.includes  in
          let uu____12375 = FStar_Util.smap_copy env.sigmap  in
          let uu____12386 = FStar_Util.smap_copy env.docs  in
          {
            curmodule = (uu___304_12353.curmodule);
            curmonad = (uu___304_12353.curmonad);
            modules = (uu___304_12353.modules);
            scope_mods = (uu___304_12353.scope_mods);
            exported_ids = uu____12354;
            trans_exported_ids = uu____12359;
            includes = uu____12364;
            sigaccum = (uu___304_12353.sigaccum);
            sigmap = uu____12375;
            iface = (uu___304_12353.iface);
            admitted_iface = (uu___304_12353.admitted_iface);
            expect_typ = (uu___304_12353.expect_typ);
            docs = uu____12386;
            remaining_iface_decls = (uu___304_12353.remaining_iface_decls);
            syntax_only = (uu___304_12353.syntax_only);
            ds_hooks = (uu___304_12353.ds_hooks)
          }))
  
let (pop : unit -> env) =
  fun uu____12393  ->
    FStar_Util.atomically
      (fun uu____12400  ->
         let uu____12401 = FStar_ST.op_Bang stack  in
         match uu____12401 with
         | env::tl1 ->
             (pop_record_cache (); FStar_ST.op_Colon_Equals stack tl1; env)
         | uu____12456 -> failwith "Impossible: Too many pops")
  
let (snapshot : env -> (Prims.int,env) FStar_Pervasives_Native.tuple2) =
  fun env  -> FStar_Common.snapshot push stack env 
let (rollback : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth  -> FStar_Common.rollback pop stack depth 
let (export_interface : FStar_Ident.lident -> env -> env) =
  fun m  ->
    fun env  ->
      let sigelt_in_m se =
        match FStar_Syntax_Util.lids_of_sigelt se with
        | l::uu____12494 -> l.FStar_Ident.nsstr = m.FStar_Ident.str
        | uu____12497 -> false  in
      let sm = sigmap env  in
      let env1 = pop ()  in
      let keys = FStar_Util.smap_keys sm  in
      let sm' = sigmap env1  in
      FStar_All.pipe_right keys
        (FStar_List.iter
           (fun k  ->
              let uu____12531 = FStar_Util.smap_try_find sm' k  in
              match uu____12531 with
              | FStar_Pervasives_Native.Some (se,true ) when sigelt_in_m se
                  ->
                  (FStar_Util.smap_remove sm' k;
                   (let se1 =
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t) ->
                          let uu___305_12556 = se  in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (uu___305_12556.FStar_Syntax_Syntax.sigel);
                            FStar_Syntax_Syntax.sigrng =
                              (uu___305_12556.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (FStar_Syntax_Syntax.Assumption ::
                              (se.FStar_Syntax_Syntax.sigquals));
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___305_12556.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___305_12556.FStar_Syntax_Syntax.sigattrs)
                          }
                      | uu____12557 -> se  in
                    FStar_Util.smap_add sm' k (se1, false)))
              | uu____12562 -> ()));
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
      let uu____12585 = finish env modul1  in (uu____12585, modul1)
  
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
      let uu____12673 =
        let uu____12676 = e Exported_id_term_type  in
        FStar_ST.op_Bang uu____12676  in
      FStar_Util.set_elements uu____12673  in
    let fields =
      let uu____12790 =
        let uu____12793 = e Exported_id_field  in
        FStar_ST.op_Bang uu____12793  in
      FStar_Util.set_elements uu____12790  in
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
          let uu____12944 =
            FStar_Util.as_set e1.exported_id_terms FStar_Util.compare  in
          FStar_Util.mk_ref uu____12944  in
        let fields =
          let uu____12954 =
            FStar_Util.as_set e1.exported_id_fields FStar_Util.compare  in
          FStar_Util.mk_ref uu____12954  in
        (fun uu___280_12959  ->
           match uu___280_12959 with
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
  'Auu____13090 .
    'Auu____13090 Prims.list FStar_Pervasives_Native.option ->
      'Auu____13090 Prims.list FStar_ST.ref
  =
  fun uu___281_13103  ->
    match uu___281_13103 with
    | FStar_Pervasives_Native.None  -> FStar_Util.mk_ref []
    | FStar_Pervasives_Native.Some l -> FStar_Util.mk_ref l
  
let (inclusion_info : env -> FStar_Ident.lident -> module_inclusion_info) =
  fun env  ->
    fun l  ->
      let mname = FStar_Ident.string_of_lid l  in
      let as_ids_opt m =
        let uu____13144 = FStar_Util.smap_try_find m mname  in
        FStar_Util.map_opt uu____13144 as_exported_ids  in
      let uu____13150 = as_ids_opt env.exported_ids  in
      let uu____13153 = as_ids_opt env.trans_exported_ids  in
      let uu____13156 =
        let uu____13161 = FStar_Util.smap_try_find env.includes mname  in
        FStar_Util.map_opt uu____13161 (fun r  -> FStar_ST.op_Bang r)  in
      {
        mii_exported_ids = uu____13150;
        mii_trans_exported_ids = uu____13153;
        mii_includes = uu____13156
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
                let uu____13276 = FStar_Ident.text_of_lid mname  in
                FStar_Util.strcat uu____13276 ".fst"  in
              let auto_open =
                FStar_Parser_Dep.hard_coded_dependencies filename  in
              let auto_open1 =
                let convert_kind uu___282_13296 =
                  match uu___282_13296 with
                  | FStar_Parser_Dep.Open_namespace  -> Open_namespace
                  | FStar_Parser_Dep.Open_module  -> Open_module  in
                FStar_List.map
                  (fun uu____13308  ->
                     match uu____13308 with
                     | (lid,kind) -> (lid, (convert_kind kind))) auto_open
                 in
              let namespace_of_module =
                if
                  (FStar_List.length mname.FStar_Ident.ns) >
                    (Prims.parse_int "0")
                then
                  let uu____13332 =
                    let uu____13337 =
                      FStar_Ident.lid_of_ids mname.FStar_Ident.ns  in
                    (uu____13337, Open_namespace)  in
                  [uu____13332]
                else []  in
              let auto_open2 =
                FStar_List.append namespace_of_module
                  (FStar_List.rev auto_open1)
                 in
              (let uu____13367 = as_exported_id_set mii.mii_exported_ids  in
               FStar_Util.smap_add env1.exported_ids mname.FStar_Ident.str
                 uu____13367);
              (match () with
               | () ->
                   ((let uu____13394 =
                       as_exported_id_set mii.mii_trans_exported_ids  in
                     FStar_Util.smap_add env1.trans_exported_ids
                       mname.FStar_Ident.str uu____13394);
                    (match () with
                     | () ->
                         ((let uu____13421 = as_includes mii.mii_includes  in
                           FStar_Util.smap_add env1.includes
                             mname.FStar_Ident.str uu____13421);
                          (match () with
                           | () ->
                               let env' =
                                 let uu___306_13453 = env1  in
                                 let uu____13454 =
                                   FStar_List.map
                                     (fun x  -> Open_module_or_namespace x)
                                     auto_open2
                                    in
                                 {
                                   curmodule =
                                     (FStar_Pervasives_Native.Some mname);
                                   curmonad = (uu___306_13453.curmonad);
                                   modules = (uu___306_13453.modules);
                                   scope_mods = uu____13454;
                                   exported_ids =
                                     (uu___306_13453.exported_ids);
                                   trans_exported_ids =
                                     (uu___306_13453.trans_exported_ids);
                                   includes = (uu___306_13453.includes);
                                   sigaccum = (uu___306_13453.sigaccum);
                                   sigmap = (env1.sigmap);
                                   iface = intf;
                                   admitted_iface = admitted;
                                   expect_typ = (uu___306_13453.expect_typ);
                                   docs = (uu___306_13453.docs);
                                   remaining_iface_decls =
                                     (uu___306_13453.remaining_iface_decls);
                                   syntax_only = (uu___306_13453.syntax_only);
                                   ds_hooks = (uu___306_13453.ds_hooks)
                                 }  in
                               (FStar_List.iter
                                  (fun op  ->
                                     (env1.ds_hooks).ds_push_open_hook env'
                                       op) (FStar_List.rev auto_open2);
                                env'))))))
               in
            let uu____13466 =
              FStar_All.pipe_right env.modules
                (FStar_Util.find_opt
                   (fun uu____13492  ->
                      match uu____13492 with
                      | (l,uu____13498) -> FStar_Ident.lid_equals l mname))
               in
            match uu____13466 with
            | FStar_Pervasives_Native.None  ->
                let uu____13507 = prep env  in (uu____13507, false)
            | FStar_Pervasives_Native.Some (uu____13508,m) ->
                ((let uu____13515 =
                    (let uu____13518 = FStar_Options.interactive ()  in
                     Prims.op_Negation uu____13518) &&
                      ((Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)
                         || intf)
                     in
                  if uu____13515
                  then
                    let uu____13519 =
                      let uu____13524 =
                        FStar_Util.format1
                          "Duplicate module or interface name: %s"
                          mname.FStar_Ident.str
                         in
                      (FStar_Errors.Fatal_DuplicateModuleOrInterface,
                        uu____13524)
                       in
                    let uu____13525 = FStar_Ident.range_of_lid mname  in
                    FStar_Errors.raise_error uu____13519 uu____13525
                  else ());
                 (let uu____13527 =
                    let uu____13528 = push env  in prep uu____13528  in
                  (uu____13527, true)))
  
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
          let uu___307_13540 = env  in
          {
            curmodule = (uu___307_13540.curmodule);
            curmonad = (FStar_Pervasives_Native.Some mname);
            modules = (uu___307_13540.modules);
            scope_mods = (uu___307_13540.scope_mods);
            exported_ids = (uu___307_13540.exported_ids);
            trans_exported_ids = (uu___307_13540.trans_exported_ids);
            includes = (uu___307_13540.includes);
            sigaccum = (uu___307_13540.sigaccum);
            sigmap = (uu___307_13540.sigmap);
            iface = (uu___307_13540.iface);
            admitted_iface = (uu___307_13540.admitted_iface);
            expect_typ = (uu___307_13540.expect_typ);
            docs = (uu___307_13540.docs);
            remaining_iface_decls = (uu___307_13540.remaining_iface_decls);
            syntax_only = (uu___307_13540.syntax_only);
            ds_hooks = (uu___307_13540.ds_hooks)
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
        let uu____13574 = lookup1 lid  in
        match uu____13574 with
        | FStar_Pervasives_Native.None  ->
            let opened_modules =
              FStar_List.map
                (fun uu____13587  ->
                   match uu____13587 with
                   | (lid1,uu____13593) -> FStar_Ident.text_of_lid lid1)
                env.modules
               in
            let msg =
              let uu____13595 = FStar_Ident.text_of_lid lid  in
              FStar_Util.format1 "Identifier not found: [%s]" uu____13595  in
            let msg1 =
              if
                (FStar_List.length lid.FStar_Ident.ns) =
                  (Prims.parse_int "0")
              then msg
              else
                (let modul =
                   let uu____13599 =
                     FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
                   let uu____13600 = FStar_Ident.range_of_lid lid  in
                   FStar_Ident.set_lid_range uu____13599 uu____13600  in
                 let uu____13601 = resolve_module_name env modul true  in
                 match uu____13601 with
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
            let uu____13610 = FStar_Ident.range_of_lid lid  in
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_IdentifierNotFound, msg1) uu____13610
        | FStar_Pervasives_Native.Some r -> r
  
let fail_or2 :
  'a .
    (FStar_Ident.ident -> 'a FStar_Pervasives_Native.option) ->
      FStar_Ident.ident -> 'a
  =
  fun lookup1  ->
    fun id1  ->
      let uu____13638 = lookup1 id1  in
      match uu____13638 with
      | FStar_Pervasives_Native.None  ->
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_IdentifierNotFound,
              (Prims.strcat "Identifier not found ["
                 (Prims.strcat id1.FStar_Ident.idText "]")))
            id1.FStar_Ident.idRange
      | FStar_Pervasives_Native.Some r -> r
  