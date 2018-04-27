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
  | Open_namespace [@@deriving show]
let (uu___is_Open_module : open_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Open_module  -> true | uu____22 -> false
  
let (uu___is_Open_namespace : open_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Open_namespace  -> true | uu____28 -> false
  
type open_module_or_namespace =
  (FStar_Ident.lident,open_kind) FStar_Pervasives_Native.tuple2[@@deriving
                                                                 show]
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
  is_record: Prims.bool }[@@deriving show]
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
  | Record_or_dc of record_or_dc [@@deriving show]
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
type string_set = Prims.string FStar_Util.set[@@deriving show]
type exported_id_kind =
  | Exported_id_term_type 
  | Exported_id_field [@@deriving show]
let (uu___is_Exported_id_term_type : exported_id_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Exported_id_term_type  -> true
    | uu____304 -> false
  
let (uu___is_Exported_id_field : exported_id_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exported_id_field  -> true | uu____310 -> false
  
type exported_id_set = exported_id_kind -> string_set FStar_ST.ref[@@deriving
                                                                    show]
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
  ds_hooks: dsenv_hooks }[@@deriving show]
and dsenv_hooks =
  {
  ds_push_open_hook: env -> open_module_or_namespace -> unit ;
  ds_push_include_hook: env -> FStar_Ident.lident -> unit ;
  ds_push_module_abbrev_hook:
    env -> FStar_Ident.ident -> FStar_Ident.lident -> unit }[@@deriving show]
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
  
type 'a withenv = env -> ('a,env) FStar_Pervasives_Native.tuple2[@@deriving
                                                                  show]
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
  FStar_Pervasives_Native.tuple2 [@@deriving show]
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
      let uu___114_1845 = env  in
      {
        curmodule = (uu___114_1845.curmodule);
        curmonad = (uu___114_1845.curmonad);
        modules = (uu___114_1845.modules);
        scope_mods = (uu___114_1845.scope_mods);
        exported_ids = (uu___114_1845.exported_ids);
        trans_exported_ids = (uu___114_1845.trans_exported_ids);
        includes = (uu___114_1845.includes);
        sigaccum = (uu___114_1845.sigaccum);
        sigmap = (uu___114_1845.sigmap);
        iface = b;
        admitted_iface = (uu___114_1845.admitted_iface);
        expect_typ = (uu___114_1845.expect_typ);
        docs = (uu___114_1845.docs);
        remaining_iface_decls = (uu___114_1845.remaining_iface_decls);
        syntax_only = (uu___114_1845.syntax_only);
        ds_hooks = (uu___114_1845.ds_hooks)
      }
  
let (iface : env -> Prims.bool) = fun e  -> e.iface 
let (set_admitted_iface : env -> Prims.bool -> env) =
  fun e  ->
    fun b  ->
      let uu___115_1861 = e  in
      {
        curmodule = (uu___115_1861.curmodule);
        curmonad = (uu___115_1861.curmonad);
        modules = (uu___115_1861.modules);
        scope_mods = (uu___115_1861.scope_mods);
        exported_ids = (uu___115_1861.exported_ids);
        trans_exported_ids = (uu___115_1861.trans_exported_ids);
        includes = (uu___115_1861.includes);
        sigaccum = (uu___115_1861.sigaccum);
        sigmap = (uu___115_1861.sigmap);
        iface = (uu___115_1861.iface);
        admitted_iface = b;
        expect_typ = (uu___115_1861.expect_typ);
        docs = (uu___115_1861.docs);
        remaining_iface_decls = (uu___115_1861.remaining_iface_decls);
        syntax_only = (uu___115_1861.syntax_only);
        ds_hooks = (uu___115_1861.ds_hooks)
      }
  
let (admitted_iface : env -> Prims.bool) = fun e  -> e.admitted_iface 
let (set_expect_typ : env -> Prims.bool -> env) =
  fun e  ->
    fun b  ->
      let uu___116_1877 = e  in
      {
        curmodule = (uu___116_1877.curmodule);
        curmonad = (uu___116_1877.curmonad);
        modules = (uu___116_1877.modules);
        scope_mods = (uu___116_1877.scope_mods);
        exported_ids = (uu___116_1877.exported_ids);
        trans_exported_ids = (uu___116_1877.trans_exported_ids);
        includes = (uu___116_1877.includes);
        sigaccum = (uu___116_1877.sigaccum);
        sigmap = (uu___116_1877.sigmap);
        iface = (uu___116_1877.iface);
        admitted_iface = (uu___116_1877.admitted_iface);
        expect_typ = b;
        docs = (uu___116_1877.docs);
        remaining_iface_decls = (uu___116_1877.remaining_iface_decls);
        syntax_only = (uu___116_1877.syntax_only);
        ds_hooks = (uu___116_1877.ds_hooks)
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
      (fun uu___82_2056  ->
         match uu___82_2056 with
         | Open_module_or_namespace (lid,_info) ->
             FStar_Pervasives_Native.Some lid
         | uu____2061 -> FStar_Pervasives_Native.None) env.scope_mods
  
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun e  ->
    fun l  ->
      let uu___117_2072 = e  in
      {
        curmodule = (FStar_Pervasives_Native.Some l);
        curmonad = (uu___117_2072.curmonad);
        modules = (uu___117_2072.modules);
        scope_mods = (uu___117_2072.scope_mods);
        exported_ids = (uu___117_2072.exported_ids);
        trans_exported_ids = (uu___117_2072.trans_exported_ids);
        includes = (uu___117_2072.includes);
        sigaccum = (uu___117_2072.sigaccum);
        sigmap = (uu___117_2072.sigmap);
        iface = (uu___117_2072.iface);
        admitted_iface = (uu___117_2072.admitted_iface);
        expect_typ = (uu___117_2072.expect_typ);
        docs = (uu___117_2072.docs);
        remaining_iface_decls = (uu___117_2072.remaining_iface_decls);
        syntax_only = (uu___117_2072.syntax_only);
        ds_hooks = (uu___117_2072.ds_hooks)
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
            let uu___118_2262 = env  in
            {
              curmodule = (uu___118_2262.curmodule);
              curmonad = (uu___118_2262.curmonad);
              modules = (uu___118_2262.modules);
              scope_mods = (uu___118_2262.scope_mods);
              exported_ids = (uu___118_2262.exported_ids);
              trans_exported_ids = (uu___118_2262.trans_exported_ids);
              includes = (uu___118_2262.includes);
              sigaccum = (uu___118_2262.sigaccum);
              sigmap = (uu___118_2262.sigmap);
              iface = (uu___118_2262.iface);
              admitted_iface = (uu___118_2262.admitted_iface);
              expect_typ = (uu___118_2262.expect_typ);
              docs = (uu___118_2262.docs);
              remaining_iface_decls = ((l, ds) :: rest);
              syntax_only = (uu___118_2262.syntax_only);
              ds_hooks = (uu___118_2262.ds_hooks)
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
      let uu___119_2308 = env  in
      {
        curmodule = (uu___119_2308.curmodule);
        curmonad = (uu___119_2308.curmonad);
        modules = (uu___119_2308.modules);
        scope_mods = (uu___119_2308.scope_mods);
        exported_ids = (uu___119_2308.exported_ids);
        trans_exported_ids = (uu___119_2308.trans_exported_ids);
        includes = (uu___119_2308.includes);
        sigaccum = (uu___119_2308.sigaccum);
        sigmap = (uu___119_2308.sigmap);
        iface = (uu___119_2308.iface);
        admitted_iface = (uu___119_2308.admitted_iface);
        expect_typ = (uu___119_2308.expect_typ);
        docs = (uu___119_2308.docs);
        remaining_iface_decls = (uu___119_2308.remaining_iface_decls);
        syntax_only = b;
        ds_hooks = (uu___119_2308.ds_hooks)
      }
  
let (ds_hooks : env -> dsenv_hooks) = fun env  -> env.ds_hooks 
let (set_ds_hooks : env -> dsenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___120_2324 = env  in
      {
        curmodule = (uu___120_2324.curmodule);
        curmonad = (uu___120_2324.curmonad);
        modules = (uu___120_2324.modules);
        scope_mods = (uu___120_2324.scope_mods);
        exported_ids = (uu___120_2324.exported_ids);
        trans_exported_ids = (uu___120_2324.trans_exported_ids);
        includes = (uu___120_2324.includes);
        sigaccum = (uu___120_2324.sigaccum);
        sigmap = (uu___120_2324.sigmap);
        iface = (uu___120_2324.iface);
        admitted_iface = (uu___120_2324.admitted_iface);
        expect_typ = (uu___120_2324.expect_typ);
        docs = (uu___120_2324.docs);
        remaining_iface_decls = (uu___120_2324.remaining_iface_decls);
        syntax_only = (uu___120_2324.syntax_only);
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
        let uu___121_2428 = bv.FStar_Syntax_Syntax.ppname  in
        {
          FStar_Ident.idText = (uu___121_2428.FStar_Ident.idText);
          FStar_Ident.idRange = r
        }  in
      let uu___122_2429 = bv  in
      {
        FStar_Syntax_Syntax.ppname = id1;
        FStar_Syntax_Syntax.index = (uu___122_2429.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = (uu___122_2429.FStar_Syntax_Syntax.sort)
      }
  
let (bv_to_name :
  FStar_Syntax_Syntax.bv -> FStar_Range.range -> FStar_Syntax_Syntax.term) =
  fun bv  -> fun r  -> FStar_Syntax_Syntax.bv_to_name (set_bv_range bv r) 
let (unmangleMap :
  (Prims.string,Prims.string,FStar_Syntax_Syntax.delta_depth,FStar_Syntax_Syntax.fv_qual
                                                               FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple4 Prims.list)
  =
  [("op_ColonColon", "Cons", FStar_Syntax_Syntax.Delta_constant,
     (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor));
  ("not", "op_Negation", FStar_Syntax_Syntax.Delta_equational,
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
  | Cont_ignore [@@deriving show]
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
    fun uu___83_2671  ->
      match uu___83_2671 with
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
  fun uu___84_2810  ->
    match uu___84_2810 with
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
              let rec aux uu___85_2881 =
                match uu___85_2881 with
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
  fun uu___86_3130  ->
    match uu___86_3130 with
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
                  let check_local_binding_id uu___87_3252 =
                    match uu___87_3252 with
                    | (id',uu____3254,uu____3255) ->
                        id'.FStar_Ident.idText = id1.FStar_Ident.idText
                     in
                  let check_rec_binding_id uu___88_3261 =
                    match uu___88_3261 with
                    | (id',uu____3263,uu____3264) ->
                        id'.FStar_Ident.idText = id1.FStar_Ident.idText
                     in
                  let curmod_ns =
                    let uu____3268 = current_module env  in
                    FStar_Ident.ids_of_lid uu____3268  in
                  let proc uu___89_3276 =
                    match uu___89_3276 with
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
                  let rec aux uu___90_3299 =
                    match uu___90_3299 with
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
        let rec aux uu___91_3726 =
          match uu___91_3726 with
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
          (fun uu___92_3832  ->
             match uu___92_3832 with
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
    fun uu___93_4311  ->
      match uu___93_4311 with
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
            (fun uu___94_4499  ->
               match uu___94_4499 with
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
          let k_global_def source_lid uu___99_4615 =
            match uu___99_4615 with
            | (uu____4622,true ) when exclude_interf ->
                FStar_Pervasives_Native.None
            | (se,uu____4624) ->
                (match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_inductive_typ uu____4627 ->
                     let uu____4644 =
                       let uu____4645 =
                         let uu____4654 =
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.Delta_constant
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
                             FStar_Syntax_Syntax.Delta_constant uu____4683
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
                               (fun uu___95_4723  ->
                                  match uu___95_4723 with
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
                                   (fun uu___96_4735  ->
                                      match uu___96_4735 with
                                      | FStar_Syntax_Syntax.Projector
                                          uu____4736 -> true
                                      | FStar_Syntax_Syntax.Discriminator
                                          uu____4741 -> true
                                      | uu____4742 -> false)))
                            in
                         if uu____4730
                         then FStar_Syntax_Syntax.Delta_equational
                         else FStar_Syntax_Syntax.Delta_constant  in
                       let dd1 =
                         let uu____4745 =
                           FStar_All.pipe_right quals
                             (FStar_Util.for_some
                                (fun uu___97_4749  ->
                                   match uu___97_4749 with
                                   | FStar_Syntax_Syntax.Abstract  -> true
                                   | uu____4750 -> false))
                            in
                         if uu____4745
                         then FStar_Syntax_Syntax.Delta_abstract dd
                         else dd  in
                       let uu____4752 =
                         FStar_Util.find_map quals
                           (fun uu___98_4757  ->
                              match uu___98_4757 with
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
                             (FStar_Syntax_Syntax.Delta_defined_at_level
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
      let k_global_def lid1 uu___100_5359 =
        match uu___100_5359 with
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
      let k_global_def lid1 uu___101_5491 =
        match uu___101_5491 with
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
      let k_global_def lid1 uu___102_5559 =
        match uu___102_5559 with
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
        let uu___123_5983 = env  in
        {
          curmodule = (uu___123_5983.curmodule);
          curmonad = (uu___123_5983.curmonad);
          modules = (uu___123_5983.modules);
          scope_mods = [];
          exported_ids = empty_exported_id_smap;
          trans_exported_ids = (uu___123_5983.trans_exported_ids);
          includes = empty_include_smap;
          sigaccum = (uu___123_5983.sigaccum);
          sigmap = (uu___123_5983.sigmap);
          iface = (uu___123_5983.iface);
          admitted_iface = (uu___123_5983.admitted_iface);
          expect_typ = (uu___123_5983.expect_typ);
          docs = (uu___123_5983.docs);
          remaining_iface_decls = (uu___123_5983.remaining_iface_decls);
          syntax_only = (uu___123_5983.syntax_only);
          ds_hooks = (uu___123_5983.ds_hooks)
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
      let k_global_def lid1 uu___104_6073 =
        match uu___104_6073 with
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
                   (fun uu___103_6096  ->
                      match uu___103_6096 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | uu____6097 -> false))
               in
            if uu____6092
            then
              let uu____6100 =
                FStar_Syntax_Syntax.lid_as_fv lid1
                  FStar_Syntax_Syntax.Delta_constant
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
            let uu____6126 =
              FStar_Syntax_Syntax.lid_as_fv lid1
                FStar_Syntax_Syntax.Delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
               in
            FStar_Pervasives_Native.Some uu____6126
        | uu____6127 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____6133  -> FStar_Pervasives_Native.None)
        (fun uu____6135  -> FStar_Pervasives_Native.None) k_global_def
  
let (find_all_datacons :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___105_6168 =
        match uu___105_6168 with
        | ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_inductive_typ
               (uu____6177,uu____6178,uu____6179,uu____6180,datas,uu____6182);
             FStar_Syntax_Syntax.sigrng = uu____6183;
             FStar_Syntax_Syntax.sigquals = uu____6184;
             FStar_Syntax_Syntax.sigmeta = uu____6185;
             FStar_Syntax_Syntax.sigattrs = uu____6186;_},uu____6187)
            -> FStar_Pervasives_Native.Some datas
        | uu____6202 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____6212  -> FStar_Pervasives_Native.None)
        (fun uu____6216  -> FStar_Pervasives_Native.None) k_global_def
  
let (record_cache_aux_with_filter :
  ((unit -> unit,unit -> unit,unit -> record_or_dc Prims.list,record_or_dc ->
                                                                unit)
     FStar_Pervasives_Native.tuple4,unit -> unit)
    FStar_Pervasives_Native.tuple2)
  =
  let record_cache = FStar_Util.mk_ref [[]]  in
  let push1 uu____6268 =
    let uu____6269 =
      let uu____6274 =
        let uu____6277 = FStar_ST.op_Bang record_cache  in
        FStar_List.hd uu____6277  in
      let uu____6337 = FStar_ST.op_Bang record_cache  in uu____6274 ::
        uu____6337
       in
    FStar_ST.op_Colon_Equals record_cache uu____6269  in
  let pop1 uu____6455 =
    let uu____6456 =
      let uu____6461 = FStar_ST.op_Bang record_cache  in
      FStar_List.tl uu____6461  in
    FStar_ST.op_Colon_Equals record_cache uu____6456  in
  let peek1 uu____6581 =
    let uu____6582 = FStar_ST.op_Bang record_cache  in
    FStar_List.hd uu____6582  in
  let insert r =
    let uu____6648 =
      let uu____6653 = let uu____6656 = peek1 ()  in r :: uu____6656  in
      let uu____6659 =
        let uu____6664 = FStar_ST.op_Bang record_cache  in
        FStar_List.tl uu____6664  in
      uu____6653 :: uu____6659  in
    FStar_ST.op_Colon_Equals record_cache uu____6648  in
  let filter1 uu____6784 =
    let rc = peek1 ()  in
    let filtered =
      FStar_List.filter
        (fun r  -> Prims.op_Negation r.is_private_or_abstract) rc
       in
    let uu____6793 =
      let uu____6798 =
        let uu____6803 = FStar_ST.op_Bang record_cache  in
        FStar_List.tl uu____6803  in
      filtered :: uu____6798  in
    FStar_ST.op_Colon_Equals record_cache uu____6793  in
  let aux = (push1, pop1, peek1, insert)  in (aux, filter1) 
let (record_cache_aux :
  (unit -> unit,unit -> unit,unit -> record_or_dc Prims.list,record_or_dc ->
                                                               unit)
    FStar_Pervasives_Native.tuple4)
  =
  let uu____7002 = record_cache_aux_with_filter  in
  match uu____7002 with | (aux,uu____7055) -> aux 
let (filter_record_cache : unit -> unit) =
  let uu____7110 = record_cache_aux_with_filter  in
  match uu____7110 with | (uu____7143,filter1) -> filter1 
let (push_record_cache : unit -> unit) =
  let uu____7199 = record_cache_aux  in
  match uu____7199 with | (push1,uu____7226,uu____7227,uu____7228) -> push1 
let (pop_record_cache : unit -> unit) =
  let uu____7261 = record_cache_aux  in
  match uu____7261 with | (uu____7287,pop1,uu____7289,uu____7290) -> pop1 
let (peek_record_cache : unit -> record_or_dc Prims.list) =
  let uu____7325 = record_cache_aux  in
  match uu____7325 with | (uu____7353,uu____7354,peek1,uu____7356) -> peek1 
let (insert_record_cache : record_or_dc -> unit) =
  let uu____7389 = record_cache_aux  in
  match uu____7389 with | (uu____7415,uu____7416,uu____7417,insert) -> insert 
let (extract_record :
  env ->
    scope_mod Prims.list FStar_ST.ref -> FStar_Syntax_Syntax.sigelt -> unit)
  =
  fun e  ->
    fun new_globs  ->
      fun se  ->
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_bundle (sigs,uu____7493) ->
            let is_record =
              FStar_Util.for_some
                (fun uu___106_7511  ->
                   match uu___106_7511 with
                   | FStar_Syntax_Syntax.RecordType uu____7512 -> true
                   | FStar_Syntax_Syntax.RecordConstructor uu____7521 -> true
                   | uu____7530 -> false)
               in
            let find_dc dc =
              FStar_All.pipe_right sigs
                (FStar_Util.find_opt
                   (fun uu___107_7554  ->
                      match uu___107_7554 with
                      | {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_datacon
                            (lid,uu____7556,uu____7557,uu____7558,uu____7559,uu____7560);
                          FStar_Syntax_Syntax.sigrng = uu____7561;
                          FStar_Syntax_Syntax.sigquals = uu____7562;
                          FStar_Syntax_Syntax.sigmeta = uu____7563;
                          FStar_Syntax_Syntax.sigattrs = uu____7564;_} ->
                          FStar_Ident.lid_equals dc lid
                      | uu____7573 -> false))
               in
            FStar_All.pipe_right sigs
              (FStar_List.iter
                 (fun uu___108_7608  ->
                    match uu___108_7608 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ
                          (typename,univs1,parms,uu____7612,uu____7613,dc::[]);
                        FStar_Syntax_Syntax.sigrng = uu____7615;
                        FStar_Syntax_Syntax.sigquals = typename_quals;
                        FStar_Syntax_Syntax.sigmeta = uu____7617;
                        FStar_Syntax_Syntax.sigattrs = uu____7618;_} ->
                        let uu____7629 =
                          let uu____7630 = find_dc dc  in
                          FStar_All.pipe_left FStar_Util.must uu____7630  in
                        (match uu____7629 with
                         | {
                             FStar_Syntax_Syntax.sigel =
                               FStar_Syntax_Syntax.Sig_datacon
                               (constrname,uu____7636,t,uu____7638,uu____7639,uu____7640);
                             FStar_Syntax_Syntax.sigrng = uu____7641;
                             FStar_Syntax_Syntax.sigquals = uu____7642;
                             FStar_Syntax_Syntax.sigmeta = uu____7643;
                             FStar_Syntax_Syntax.sigattrs = uu____7644;_} ->
                             let uu____7653 =
                               FStar_Syntax_Util.arrow_formals t  in
                             (match uu____7653 with
                              | (formals,uu____7667) ->
                                  let is_rec = is_record typename_quals  in
                                  let formals' =
                                    FStar_All.pipe_right formals
                                      (FStar_List.collect
                                         (fun uu____7716  ->
                                            match uu____7716 with
                                            | (x,q) ->
                                                let uu____7729 =
                                                  (FStar_Syntax_Syntax.is_null_bv
                                                     x)
                                                    ||
                                                    (is_rec &&
                                                       (FStar_Syntax_Syntax.is_implicit
                                                          q))
                                                   in
                                                if uu____7729
                                                then []
                                                else [(x, q)]))
                                     in
                                  let fields' =
                                    FStar_All.pipe_right formals'
                                      (FStar_List.map
                                         (fun uu____7782  ->
                                            match uu____7782 with
                                            | (x,q) ->
                                                let uu____7795 =
                                                  if is_rec
                                                  then
                                                    FStar_Syntax_Util.unmangle_field_name
                                                      x.FStar_Syntax_Syntax.ppname
                                                  else
                                                    x.FStar_Syntax_Syntax.ppname
                                                   in
                                                (uu____7795,
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
                                  ((let uu____7808 =
                                      let uu____7811 =
                                        FStar_ST.op_Bang new_globs  in
                                      (Record_or_dc record) :: uu____7811  in
                                    FStar_ST.op_Colon_Equals new_globs
                                      uu____7808);
                                   (match () with
                                    | () ->
                                        ((let add_field uu____7922 =
                                            match uu____7922 with
                                            | (id1,uu____7928) ->
                                                let modul =
                                                  let uu____7930 =
                                                    FStar_Ident.lid_of_ids
                                                      constrname.FStar_Ident.ns
                                                     in
                                                  uu____7930.FStar_Ident.str
                                                   in
                                                let uu____7931 =
                                                  get_exported_id_set e modul
                                                   in
                                                (match uu____7931 with
                                                 | FStar_Pervasives_Native.Some
                                                     my_ex ->
                                                     let my_exported_ids =
                                                       my_ex
                                                         Exported_id_field
                                                        in
                                                     ((let uu____7965 =
                                                         let uu____7966 =
                                                           FStar_ST.op_Bang
                                                             my_exported_ids
                                                            in
                                                         FStar_Util.set_add
                                                           id1.FStar_Ident.idText
                                                           uu____7966
                                                          in
                                                       FStar_ST.op_Colon_Equals
                                                         my_exported_ids
                                                         uu____7965);
                                                      (match () with
                                                       | () ->
                                                           let projname =
                                                             let uu____8060 =
                                                               let uu____8061
                                                                 =
                                                                 FStar_Syntax_Util.mk_field_projector_name_from_ident
                                                                   constrname
                                                                   id1
                                                                  in
                                                               uu____8061.FStar_Ident.ident
                                                                in
                                                             uu____8060.FStar_Ident.idText
                                                              in
                                                           let uu____8063 =
                                                             let uu____8064 =
                                                               FStar_ST.op_Bang
                                                                 my_exported_ids
                                                                in
                                                             FStar_Util.set_add
                                                               projname
                                                               uu____8064
                                                              in
                                                           FStar_ST.op_Colon_Equals
                                                             my_exported_ids
                                                             uu____8063))
                                                 | FStar_Pervasives_Native.None
                                                      -> ())
                                             in
                                          FStar_List.iter add_field fields');
                                         (match () with
                                          | () -> insert_record_cache record)))))
                         | uu____8166 -> ())
                    | uu____8167 -> ()))
        | uu____8168 -> ()
  
let (try_lookup_record_or_dc_by_field_name :
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option) =
  fun env  ->
    fun fieldname  ->
      let find_in_cache fieldname1 =
        let uu____8189 =
          ((fieldname1.FStar_Ident.ns), (fieldname1.FStar_Ident.ident))  in
        match uu____8189 with
        | (ns,id1) ->
            let uu____8206 = peek_record_cache ()  in
            FStar_Util.find_map uu____8206
              (fun record  ->
                 let uu____8212 =
                   find_in_record ns id1 record (fun r  -> Cont_ok r)  in
                 option_of_cont
                   (fun uu____8218  -> FStar_Pervasives_Native.None)
                   uu____8212)
         in
      resolve_in_open_namespaces'' env fieldname Exported_id_field
        (fun uu____8220  -> Cont_ignore) (fun uu____8222  -> Cont_ignore)
        (fun r  -> Cont_ok r)
        (fun fn  ->
           let uu____8228 = find_in_cache fn  in
           cont_of_option Cont_ignore uu____8228)
        (fun k  -> fun uu____8234  -> k)
  
let (try_lookup_record_by_field_name :
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option) =
  fun env  ->
    fun fieldname  ->
      let uu____8249 = try_lookup_record_or_dc_by_field_name env fieldname
         in
      match uu____8249 with
      | FStar_Pervasives_Native.Some r when r.is_record ->
          FStar_Pervasives_Native.Some r
      | uu____8255 -> FStar_Pervasives_Native.None
  
let (belongs_to_record :
  env -> FStar_Ident.lident -> record_or_dc -> Prims.bool) =
  fun env  ->
    fun lid  ->
      fun record  ->
        let uu____8273 = try_lookup_record_by_field_name env lid  in
        match uu____8273 with
        | FStar_Pervasives_Native.Some record' when
            let uu____8277 =
              let uu____8278 =
                FStar_Ident.path_of_ns (record.typename).FStar_Ident.ns  in
              FStar_Ident.text_of_path uu____8278  in
            let uu____8279 =
              let uu____8280 =
                FStar_Ident.path_of_ns (record'.typename).FStar_Ident.ns  in
              FStar_Ident.text_of_path uu____8280  in
            uu____8277 = uu____8279 ->
            let uu____8281 =
              find_in_record (record.typename).FStar_Ident.ns
                lid.FStar_Ident.ident record (fun uu____8285  -> Cont_ok ())
               in
            (match uu____8281 with
             | Cont_ok uu____8286 -> true
             | uu____8287 -> false)
        | uu____8290 -> false
  
let (try_lookup_dc_by_field_name :
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident,Prims.bool) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun fieldname  ->
      let uu____8309 = try_lookup_record_or_dc_by_field_name env fieldname
         in
      match uu____8309 with
      | FStar_Pervasives_Native.Some r ->
          let uu____8319 =
            let uu____8324 =
              let uu____8325 =
                FStar_Ident.lid_of_ids
                  (FStar_List.append (r.typename).FStar_Ident.ns
                     [r.constrname])
                 in
              let uu____8326 = FStar_Ident.range_of_lid fieldname  in
              FStar_Ident.set_lid_range uu____8325 uu____8326  in
            (uu____8324, (r.is_record))  in
          FStar_Pervasives_Native.Some uu____8319
      | uu____8331 -> FStar_Pervasives_Native.None
  
let (string_set_ref_new : unit -> Prims.string FStar_Util.set FStar_ST.ref) =
  fun uu____8357  ->
    let uu____8358 = FStar_Util.new_set FStar_Util.compare  in
    FStar_Util.mk_ref uu____8358
  
let (exported_id_set_new :
  unit -> exported_id_kind -> Prims.string FStar_Util.set FStar_ST.ref) =
  fun uu____8385  ->
    let term_type_set = string_set_ref_new ()  in
    let field_set = string_set_ref_new ()  in
    fun uu___109_8396  ->
      match uu___109_8396 with
      | Exported_id_term_type  -> term_type_set
      | Exported_id_field  -> field_set
  
let (unique :
  Prims.bool -> Prims.bool -> env -> FStar_Ident.lident -> Prims.bool) =
  fun any_val  ->
    fun exclude_interface  ->
      fun env  ->
        fun lid  ->
          let filter_scope_mods uu___110_8448 =
            match uu___110_8448 with
            | Rec_binding uu____8449 -> true
            | uu____8450 -> false  in
          let this_env =
            let uu___124_8452 = env  in
            let uu____8453 =
              FStar_List.filter filter_scope_mods env.scope_mods  in
            {
              curmodule = (uu___124_8452.curmodule);
              curmonad = (uu___124_8452.curmonad);
              modules = (uu___124_8452.modules);
              scope_mods = uu____8453;
              exported_ids = empty_exported_id_smap;
              trans_exported_ids = (uu___124_8452.trans_exported_ids);
              includes = empty_include_smap;
              sigaccum = (uu___124_8452.sigaccum);
              sigmap = (uu___124_8452.sigmap);
              iface = (uu___124_8452.iface);
              admitted_iface = (uu___124_8452.admitted_iface);
              expect_typ = (uu___124_8452.expect_typ);
              docs = (uu___124_8452.docs);
              remaining_iface_decls = (uu___124_8452.remaining_iface_decls);
              syntax_only = (uu___124_8452.syntax_only);
              ds_hooks = (uu___124_8452.ds_hooks)
            }  in
          let uu____8456 =
            try_lookup_lid' any_val exclude_interface this_env lid  in
          match uu____8456 with
          | FStar_Pervasives_Native.None  -> true
          | FStar_Pervasives_Native.Some uu____8475 -> false
  
let (push_scope_mod : env -> scope_mod -> env) =
  fun env  ->
    fun scope_mod  ->
      let uu___125_8502 = env  in
      {
        curmodule = (uu___125_8502.curmodule);
        curmonad = (uu___125_8502.curmonad);
        modules = (uu___125_8502.modules);
        scope_mods = (scope_mod :: (env.scope_mods));
        exported_ids = (uu___125_8502.exported_ids);
        trans_exported_ids = (uu___125_8502.trans_exported_ids);
        includes = (uu___125_8502.includes);
        sigaccum = (uu___125_8502.sigaccum);
        sigmap = (uu___125_8502.sigmap);
        iface = (uu___125_8502.iface);
        admitted_iface = (uu___125_8502.admitted_iface);
        expect_typ = (uu___125_8502.expect_typ);
        docs = (uu___125_8502.docs);
        remaining_iface_decls = (uu___125_8502.remaining_iface_decls);
        syntax_only = (uu___125_8502.syntax_only);
        ds_hooks = (uu___125_8502.ds_hooks)
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
        let uu____8567 =
          (unique false true env l) || (FStar_Options.interactive ())  in
        if uu____8567
        then push_scope_mod env (Rec_binding (x, l, dd))
        else
          (let uu____8569 = FStar_Ident.range_of_lid l  in
           FStar_Errors.raise_error
             (FStar_Errors.Fatal_DuplicateTopLevelNames,
               (Prims.strcat "Duplicate top-level names " l.FStar_Ident.str))
             uu____8569)
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let err l =
        let sopt = FStar_Util.smap_try_find (sigmap env) l.FStar_Ident.str
           in
        let r =
          match sopt with
          | FStar_Pervasives_Native.Some (se,uu____8599) ->
              let uu____8604 =
                FStar_Util.find_opt (FStar_Ident.lid_equals l)
                  (FStar_Syntax_Util.lids_of_sigelt se)
                 in
              (match uu____8604 with
               | FStar_Pervasives_Native.Some l1 ->
                   let uu____8608 = FStar_Ident.range_of_lid l1  in
                   FStar_All.pipe_left FStar_Range.string_of_range uu____8608
               | FStar_Pervasives_Native.None  -> "<unknown>")
          | FStar_Pervasives_Native.None  -> "<unknown>"  in
        let uu____8613 =
          let uu____8618 =
            let uu____8619 = FStar_Ident.text_of_lid l  in
            FStar_Util.format2
              "Duplicate top-level names [%s]; previously declared at %s"
              uu____8619 r
             in
          (FStar_Errors.Fatal_DuplicateTopLevelNames, uu____8618)  in
        let uu____8620 = FStar_Ident.range_of_lid l  in
        FStar_Errors.raise_error uu____8613 uu____8620  in
      let globals = FStar_Util.mk_ref env.scope_mods  in
      let env1 =
        let uu____8629 =
          match s.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let uu____8638 -> (false, true)
          | FStar_Syntax_Syntax.Sig_bundle uu____8645 -> (false, true)
          | uu____8654 -> (false, false)  in
        match uu____8629 with
        | (any_val,exclude_interface) ->
            let lids = FStar_Syntax_Util.lids_of_sigelt s  in
            let uu____8660 =
              FStar_Util.find_map lids
                (fun l  ->
                   let uu____8666 =
                     let uu____8667 = unique any_val exclude_interface env l
                        in
                     Prims.op_Negation uu____8667  in
                   if uu____8666
                   then FStar_Pervasives_Native.Some l
                   else FStar_Pervasives_Native.None)
               in
            (match uu____8660 with
             | FStar_Pervasives_Native.Some l -> err l
             | uu____8672 ->
                 (extract_record env globals s;
                  (let uu___126_8698 = env  in
                   {
                     curmodule = (uu___126_8698.curmodule);
                     curmonad = (uu___126_8698.curmonad);
                     modules = (uu___126_8698.modules);
                     scope_mods = (uu___126_8698.scope_mods);
                     exported_ids = (uu___126_8698.exported_ids);
                     trans_exported_ids = (uu___126_8698.trans_exported_ids);
                     includes = (uu___126_8698.includes);
                     sigaccum = (s :: (env.sigaccum));
                     sigmap = (uu___126_8698.sigmap);
                     iface = (uu___126_8698.iface);
                     admitted_iface = (uu___126_8698.admitted_iface);
                     expect_typ = (uu___126_8698.expect_typ);
                     docs = (uu___126_8698.docs);
                     remaining_iface_decls =
                       (uu___126_8698.remaining_iface_decls);
                     syntax_only = (uu___126_8698.syntax_only);
                     ds_hooks = (uu___126_8698.ds_hooks)
                   })))
         in
      let env2 =
        let uu___127_8700 = env1  in
        let uu____8701 = FStar_ST.op_Bang globals  in
        {
          curmodule = (uu___127_8700.curmodule);
          curmonad = (uu___127_8700.curmonad);
          modules = (uu___127_8700.modules);
          scope_mods = uu____8701;
          exported_ids = (uu___127_8700.exported_ids);
          trans_exported_ids = (uu___127_8700.trans_exported_ids);
          includes = (uu___127_8700.includes);
          sigaccum = (uu___127_8700.sigaccum);
          sigmap = (uu___127_8700.sigmap);
          iface = (uu___127_8700.iface);
          admitted_iface = (uu___127_8700.admitted_iface);
          expect_typ = (uu___127_8700.expect_typ);
          docs = (uu___127_8700.docs);
          remaining_iface_decls = (uu___127_8700.remaining_iface_decls);
          syntax_only = (uu___127_8700.syntax_only);
          ds_hooks = (uu___127_8700.ds_hooks)
        }  in
      let uu____8753 =
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_bundle (ses,uu____8779) ->
            let uu____8788 =
              FStar_List.map
                (fun se  -> ((FStar_Syntax_Util.lids_of_sigelt se), se)) ses
               in
            (env2, uu____8788)
        | uu____8815 -> (env2, [((FStar_Syntax_Util.lids_of_sigelt s), s)])
         in
      match uu____8753 with
      | (env3,lss) ->
          (FStar_All.pipe_right lss
             (FStar_List.iter
                (fun uu____8874  ->
                   match uu____8874 with
                   | (lids,se) ->
                       FStar_All.pipe_right lids
                         (FStar_List.iter
                            (fun lid  ->
                               (let uu____8896 =
                                  let uu____8899 = FStar_ST.op_Bang globals
                                     in
                                  (Top_level_def (lid.FStar_Ident.ident)) ::
                                    uu____8899
                                   in
                                FStar_ST.op_Colon_Equals globals uu____8896);
                               (match () with
                                | () ->
                                    let modul =
                                      let uu____9001 =
                                        FStar_Ident.lid_of_ids
                                          lid.FStar_Ident.ns
                                         in
                                      uu____9001.FStar_Ident.str  in
                                    ((let uu____9003 =
                                        get_exported_id_set env3 modul  in
                                      match uu____9003 with
                                      | FStar_Pervasives_Native.Some f ->
                                          let my_exported_ids =
                                            f Exported_id_term_type  in
                                          let uu____9036 =
                                            let uu____9037 =
                                              FStar_ST.op_Bang
                                                my_exported_ids
                                               in
                                            FStar_Util.set_add
                                              (lid.FStar_Ident.ident).FStar_Ident.idText
                                              uu____9037
                                             in
                                          FStar_ST.op_Colon_Equals
                                            my_exported_ids uu____9036
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
              let uu___128_9141 = env3  in
              let uu____9142 = FStar_ST.op_Bang globals  in
              {
                curmodule = (uu___128_9141.curmodule);
                curmonad = (uu___128_9141.curmonad);
                modules = (uu___128_9141.modules);
                scope_mods = uu____9142;
                exported_ids = (uu___128_9141.exported_ids);
                trans_exported_ids = (uu___128_9141.trans_exported_ids);
                includes = (uu___128_9141.includes);
                sigaccum = (uu___128_9141.sigaccum);
                sigmap = (uu___128_9141.sigmap);
                iface = (uu___128_9141.iface);
                admitted_iface = (uu___128_9141.admitted_iface);
                expect_typ = (uu___128_9141.expect_typ);
                docs = (uu___128_9141.docs);
                remaining_iface_decls = (uu___128_9141.remaining_iface_decls);
                syntax_only = (uu___128_9141.syntax_only);
                ds_hooks = (uu___128_9141.ds_hooks)
              }  in
            env4))
  
let (push_namespace : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun ns  ->
      let uu____9204 =
        let uu____9209 = resolve_module_name env ns false  in
        match uu____9209 with
        | FStar_Pervasives_Native.None  ->
            let modules = env.modules  in
            let uu____9223 =
              FStar_All.pipe_right modules
                (FStar_Util.for_some
                   (fun uu____9239  ->
                      match uu____9239 with
                      | (m,uu____9245) ->
                          let uu____9246 =
                            let uu____9247 = FStar_Ident.text_of_lid m  in
                            Prims.strcat uu____9247 "."  in
                          let uu____9248 =
                            let uu____9249 = FStar_Ident.text_of_lid ns  in
                            Prims.strcat uu____9249 "."  in
                          FStar_Util.starts_with uu____9246 uu____9248))
               in
            if uu____9223
            then (ns, Open_namespace)
            else
              (let uu____9255 =
                 let uu____9260 =
                   let uu____9261 = FStar_Ident.text_of_lid ns  in
                   FStar_Util.format1 "Namespace %s cannot be found"
                     uu____9261
                    in
                 (FStar_Errors.Fatal_NameSpaceNotFound, uu____9260)  in
               let uu____9262 = FStar_Ident.range_of_lid ns  in
               FStar_Errors.raise_error uu____9255 uu____9262)
        | FStar_Pervasives_Native.Some ns' ->
            (fail_if_curmodule env ns ns'; (ns', Open_module))
         in
      match uu____9204 with
      | (ns',kd) ->
          ((env.ds_hooks).ds_push_open_hook env (ns', kd);
           push_scope_mod env (Open_module_or_namespace (ns', kd)))
  
let (push_include : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun ns  ->
      let ns0 = ns  in
      let uu____9283 = resolve_module_name env ns false  in
      match uu____9283 with
      | FStar_Pervasives_Native.Some ns1 ->
          ((env.ds_hooks).ds_push_include_hook env ns1;
           fail_if_curmodule env ns0 ns1;
           (let env1 =
              push_scope_mod env
                (Open_module_or_namespace (ns1, Open_module))
               in
            let curmod =
              let uu____9291 = current_module env1  in
              uu____9291.FStar_Ident.str  in
            (let uu____9293 = FStar_Util.smap_try_find env1.includes curmod
                in
             match uu____9293 with
             | FStar_Pervasives_Native.None  -> ()
             | FStar_Pervasives_Native.Some incl ->
                 let uu____9317 =
                   let uu____9320 = FStar_ST.op_Bang incl  in ns1 ::
                     uu____9320
                    in
                 FStar_ST.op_Colon_Equals incl uu____9317);
            (match () with
             | () ->
                 let uu____9421 =
                   get_trans_exported_id_set env1 ns1.FStar_Ident.str  in
                 (match uu____9421 with
                  | FStar_Pervasives_Native.Some ns_trans_exports ->
                      ((let uu____9441 =
                          let uu____9544 = get_exported_id_set env1 curmod
                             in
                          let uu____9594 =
                            get_trans_exported_id_set env1 curmod  in
                          (uu____9544, uu____9594)  in
                        match uu____9441 with
                        | (FStar_Pervasives_Native.Some
                           cur_exports,FStar_Pervasives_Native.Some
                           cur_trans_exports) ->
                            let update_exports k =
                              let ns_ex =
                                let uu____10037 = ns_trans_exports k  in
                                FStar_ST.op_Bang uu____10037  in
                              let ex = cur_exports k  in
                              (let uu____10223 =
                                 let uu____10226 = FStar_ST.op_Bang ex  in
                                 FStar_Util.set_difference uu____10226 ns_ex
                                  in
                               FStar_ST.op_Colon_Equals ex uu____10223);
                              (match () with
                               | () ->
                                   let trans_ex = cur_trans_exports k  in
                                   let uu____10430 =
                                     let uu____10433 =
                                       FStar_ST.op_Bang trans_ex  in
                                     FStar_Util.set_union uu____10433 ns_ex
                                      in
                                   FStar_ST.op_Colon_Equals trans_ex
                                     uu____10430)
                               in
                            FStar_List.iter update_exports
                              all_exported_id_kinds
                        | uu____10570 -> ());
                       (match () with | () -> env1))
                  | FStar_Pervasives_Native.None  ->
                      let uu____10678 =
                        let uu____10683 =
                          FStar_Util.format1
                            "include: Module %s was not prepared"
                            ns1.FStar_Ident.str
                           in
                        (FStar_Errors.Fatal_IncludeModuleNotPrepared,
                          uu____10683)
                         in
                      let uu____10684 = FStar_Ident.range_of_lid ns1  in
                      FStar_Errors.raise_error uu____10678 uu____10684))))
      | uu____10685 ->
          let uu____10688 =
            let uu____10693 =
              FStar_Util.format1 "include: Module %s cannot be found"
                ns.FStar_Ident.str
               in
            (FStar_Errors.Fatal_ModuleNotFound, uu____10693)  in
          let uu____10694 = FStar_Ident.range_of_lid ns  in
          FStar_Errors.raise_error uu____10688 uu____10694
  
let (push_module_abbrev :
  env -> FStar_Ident.ident -> FStar_Ident.lident -> env) =
  fun env  ->
    fun x  ->
      fun l  ->
        let uu____10710 = module_is_defined env l  in
        if uu____10710
        then
          (fail_if_curmodule env l l;
           (env.ds_hooks).ds_push_module_abbrev_hook env x l;
           push_scope_mod env (Module_abbrev (x, l)))
        else
          (let uu____10714 =
             let uu____10719 =
               let uu____10720 = FStar_Ident.text_of_lid l  in
               FStar_Util.format1 "Module %s cannot be found" uu____10720  in
             (FStar_Errors.Fatal_ModuleNotFound, uu____10719)  in
           let uu____10721 = FStar_Ident.range_of_lid l  in
           FStar_Errors.raise_error uu____10714 uu____10721)
  
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
            ((let uu____10743 =
                FStar_Util.smap_try_find env.docs l.FStar_Ident.str  in
              match uu____10743 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some old_doc ->
                  let uu____10747 = FStar_Ident.range_of_lid l  in
                  let uu____10748 =
                    let uu____10753 =
                      let uu____10754 = FStar_Ident.string_of_lid l  in
                      let uu____10755 =
                        FStar_Parser_AST.string_of_fsdoc old_doc  in
                      let uu____10756 = FStar_Parser_AST.string_of_fsdoc doc1
                         in
                      FStar_Util.format3
                        "Overwriting doc of %s; old doc was [%s]; new doc are [%s]"
                        uu____10754 uu____10755 uu____10756
                       in
                    (FStar_Errors.Warning_DocOverwrite, uu____10753)  in
                  FStar_Errors.log_issue uu____10747 uu____10748);
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
                      let uu____10798 =
                        FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption)
                         in
                      Prims.op_Negation uu____10798 ->
                      let uu____10801 =
                        FStar_Util.smap_try_find (sigmap env)
                          l.FStar_Ident.str
                         in
                      (match uu____10801 with
                       | FStar_Pervasives_Native.Some
                           ({
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_let uu____10814;
                              FStar_Syntax_Syntax.sigrng = uu____10815;
                              FStar_Syntax_Syntax.sigquals = uu____10816;
                              FStar_Syntax_Syntax.sigmeta = uu____10817;
                              FStar_Syntax_Syntax.sigattrs = uu____10818;_},uu____10819)
                           -> lids
                       | FStar_Pervasives_Native.Some
                           ({
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_inductive_typ
                                uu____10834;
                              FStar_Syntax_Syntax.sigrng = uu____10835;
                              FStar_Syntax_Syntax.sigquals = uu____10836;
                              FStar_Syntax_Syntax.sigmeta = uu____10837;
                              FStar_Syntax_Syntax.sigattrs = uu____10838;_},uu____10839)
                           -> lids
                       | uu____10864 ->
                           ((let uu____10872 =
                               let uu____10873 = FStar_Options.interactive ()
                                  in
                               Prims.op_Negation uu____10873  in
                             if uu____10872
                             then
                               let uu____10874 = FStar_Ident.range_of_lid l
                                  in
                               let uu____10875 =
                                 let uu____10880 =
                                   let uu____10881 =
                                     FStar_Ident.string_of_lid l  in
                                   FStar_Util.format1
                                     "Admitting %s without a definition"
                                     uu____10881
                                    in
                                 (FStar_Errors.Warning_AdmitWithoutDefinition,
                                   uu____10880)
                                  in
                               FStar_Errors.log_issue uu____10874 uu____10875
                             else ());
                            (let quals = FStar_Syntax_Syntax.Assumption ::
                               (se.FStar_Syntax_Syntax.sigquals)  in
                             FStar_Util.smap_add (sigmap env)
                               l.FStar_Ident.str
                               ((let uu___129_10892 = se  in
                                 {
                                   FStar_Syntax_Syntax.sigel =
                                     (uu___129_10892.FStar_Syntax_Syntax.sigel);
                                   FStar_Syntax_Syntax.sigrng =
                                     (uu___129_10892.FStar_Syntax_Syntax.sigrng);
                                   FStar_Syntax_Syntax.sigquals = quals;
                                   FStar_Syntax_Syntax.sigmeta =
                                     (uu___129_10892.FStar_Syntax_Syntax.sigmeta);
                                   FStar_Syntax_Syntax.sigattrs =
                                     (uu___129_10892.FStar_Syntax_Syntax.sigattrs)
                                 }), false);
                             l
                             ::
                             lids)))
                  | uu____10893 -> lids) [])
         in
      let uu___130_10894 = m  in
      let uu____10895 =
        FStar_All.pipe_right m.FStar_Syntax_Syntax.declarations
          (FStar_List.map
             (fun s  ->
                match s.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_declare_typ
                    (lid,uu____10905,uu____10906) when
                    FStar_List.existsb
                      (fun l  -> FStar_Ident.lid_equals l lid)
                      admitted_sig_lids
                    ->
                    let uu___131_10909 = s  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___131_10909.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___131_10909.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals =
                        (FStar_Syntax_Syntax.Assumption ::
                        (s.FStar_Syntax_Syntax.sigquals));
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___131_10909.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___131_10909.FStar_Syntax_Syntax.sigattrs)
                    }
                | uu____10910 -> s))
         in
      {
        FStar_Syntax_Syntax.name = (uu___130_10894.FStar_Syntax_Syntax.name);
        FStar_Syntax_Syntax.declarations = uu____10895;
        FStar_Syntax_Syntax.exports =
          (uu___130_10894.FStar_Syntax_Syntax.exports);
        FStar_Syntax_Syntax.is_interface =
          (uu___130_10894.FStar_Syntax_Syntax.is_interface)
      }
  
let (finish : env -> FStar_Syntax_Syntax.modul -> env) =
  fun env  ->
    fun modul  ->
      FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations
        (FStar_List.iter
           (fun se  ->
              let quals = se.FStar_Syntax_Syntax.sigquals  in
              match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_bundle (ses,uu____10933) ->
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
                                (lid,uu____10953,uu____10954,uu____10955,uu____10956,uu____10957)
                                ->
                                FStar_Util.smap_remove (sigmap env)
                                  lid.FStar_Ident.str
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (lid,univ_names,binders,typ,uu____10970,uu____10971)
                                ->
                                (FStar_Util.smap_remove (sigmap env)
                                   lid.FStar_Ident.str;
                                 if
                                   Prims.op_Negation
                                     (FStar_List.contains
                                        FStar_Syntax_Syntax.Private quals)
                                 then
                                   (let sigel =
                                      let uu____10986 =
                                        let uu____10993 =
                                          let uu____10994 =
                                            FStar_Ident.range_of_lid lid  in
                                          let uu____10995 =
                                            let uu____11002 =
                                              let uu____11003 =
                                                let uu____11016 =
                                                  FStar_Syntax_Syntax.mk_Total
                                                    typ
                                                   in
                                                (binders, uu____11016)  in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____11003
                                               in
                                            FStar_Syntax_Syntax.mk
                                              uu____11002
                                             in
                                          uu____10995
                                            FStar_Pervasives_Native.None
                                            uu____10994
                                           in
                                        (lid, univ_names, uu____10993)  in
                                      FStar_Syntax_Syntax.Sig_declare_typ
                                        uu____10986
                                       in
                                    let se2 =
                                      let uu___132_11031 = se1  in
                                      {
                                        FStar_Syntax_Syntax.sigel = sigel;
                                        FStar_Syntax_Syntax.sigrng =
                                          (uu___132_11031.FStar_Syntax_Syntax.sigrng);
                                        FStar_Syntax_Syntax.sigquals =
                                          (FStar_Syntax_Syntax.Assumption ::
                                          quals);
                                        FStar_Syntax_Syntax.sigmeta =
                                          (uu___132_11031.FStar_Syntax_Syntax.sigmeta);
                                        FStar_Syntax_Syntax.sigattrs =
                                          (uu___132_11031.FStar_Syntax_Syntax.sigattrs)
                                      }  in
                                    FStar_Util.smap_add (sigmap env)
                                      lid.FStar_Ident.str (se2, false))
                                 else ())
                            | uu____11037 -> ()))
                  else ()
              | FStar_Syntax_Syntax.Sig_declare_typ
                  (lid,uu____11040,uu____11041) ->
                  if FStar_List.contains FStar_Syntax_Syntax.Private quals
                  then
                    FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str
                  else ()
              | FStar_Syntax_Syntax.Sig_let ((uu____11047,lbs),uu____11049)
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
                             let uu____11064 =
                               let uu____11065 =
                                 let uu____11066 =
                                   let uu____11069 =
                                     FStar_Util.right
                                       lb.FStar_Syntax_Syntax.lbname
                                      in
                                   uu____11069.FStar_Syntax_Syntax.fv_name
                                    in
                                 uu____11066.FStar_Syntax_Syntax.v  in
                               uu____11065.FStar_Ident.str  in
                             FStar_Util.smap_remove (sigmap env) uu____11064))
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
                               let uu____11083 =
                                 let uu____11086 =
                                   FStar_Util.right
                                     lb.FStar_Syntax_Syntax.lbname
                                    in
                                 uu____11086.FStar_Syntax_Syntax.fv_name  in
                               uu____11083.FStar_Syntax_Syntax.v  in
                             let quals1 = FStar_Syntax_Syntax.Assumption ::
                               quals  in
                             let decl =
                               let uu___133_11091 = se  in
                               {
                                 FStar_Syntax_Syntax.sigel =
                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                      (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                        (lb.FStar_Syntax_Syntax.lbtyp)));
                                 FStar_Syntax_Syntax.sigrng =
                                   (uu___133_11091.FStar_Syntax_Syntax.sigrng);
                                 FStar_Syntax_Syntax.sigquals = quals1;
                                 FStar_Syntax_Syntax.sigmeta =
                                   (uu___133_11091.FStar_Syntax_Syntax.sigmeta);
                                 FStar_Syntax_Syntax.sigattrs =
                                   (uu___133_11091.FStar_Syntax_Syntax.sigattrs)
                               }  in
                             FStar_Util.smap_add (sigmap env)
                               lid.FStar_Ident.str (decl, false)))
                   else ())
              | uu____11097 -> ()));
      (let curmod =
         let uu____11099 = current_module env  in uu____11099.FStar_Ident.str
          in
       (let uu____11101 =
          let uu____11204 = get_exported_id_set env curmod  in
          let uu____11254 = get_trans_exported_id_set env curmod  in
          (uu____11204, uu____11254)  in
        match uu____11101 with
        | (FStar_Pervasives_Native.Some cur_ex,FStar_Pervasives_Native.Some
           cur_trans_ex) ->
            let update_exports eikind =
              let cur_ex_set =
                let uu____11699 = cur_ex eikind  in
                FStar_ST.op_Bang uu____11699  in
              let cur_trans_ex_set_ref = cur_trans_ex eikind  in
              let uu____11898 =
                let uu____11901 = FStar_ST.op_Bang cur_trans_ex_set_ref  in
                FStar_Util.set_union cur_ex_set uu____11901  in
              FStar_ST.op_Colon_Equals cur_trans_ex_set_ref uu____11898  in
            FStar_List.iter update_exports all_exported_id_kinds
        | uu____12038 -> ());
       (match () with
        | () ->
            (filter_record_cache ();
             (match () with
              | () ->
                  let uu___134_12142 = env  in
                  {
                    curmodule = FStar_Pervasives_Native.None;
                    curmonad = (uu___134_12142.curmonad);
                    modules = (((modul.FStar_Syntax_Syntax.name), modul) ::
                      (env.modules));
                    scope_mods = [];
                    exported_ids = (uu___134_12142.exported_ids);
                    trans_exported_ids = (uu___134_12142.trans_exported_ids);
                    includes = (uu___134_12142.includes);
                    sigaccum = [];
                    sigmap = (uu___134_12142.sigmap);
                    iface = (uu___134_12142.iface);
                    admitted_iface = (uu___134_12142.admitted_iface);
                    expect_typ = (uu___134_12142.expect_typ);
                    docs = (uu___134_12142.docs);
                    remaining_iface_decls =
                      (uu___134_12142.remaining_iface_decls);
                    syntax_only = (uu___134_12142.syntax_only);
                    ds_hooks = (uu___134_12142.ds_hooks)
                  }))))
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push : env -> env) =
  fun env  ->
    push_record_cache ();
    (let uu____12171 =
       let uu____12174 = FStar_ST.op_Bang stack  in env :: uu____12174  in
     FStar_ST.op_Colon_Equals stack uu____12171);
    (let uu___135_12231 = env  in
     let uu____12232 = FStar_Util.smap_copy (sigmap env)  in
     let uu____12243 = FStar_Util.smap_copy env.docs  in
     {
       curmodule = (uu___135_12231.curmodule);
       curmonad = (uu___135_12231.curmonad);
       modules = (uu___135_12231.modules);
       scope_mods = (uu___135_12231.scope_mods);
       exported_ids = (uu___135_12231.exported_ids);
       trans_exported_ids = (uu___135_12231.trans_exported_ids);
       includes = (uu___135_12231.includes);
       sigaccum = (uu___135_12231.sigaccum);
       sigmap = uu____12232;
       iface = (uu___135_12231.iface);
       admitted_iface = (uu___135_12231.admitted_iface);
       expect_typ = (uu___135_12231.expect_typ);
       docs = uu____12243;
       remaining_iface_decls = (uu___135_12231.remaining_iface_decls);
       syntax_only = (uu___135_12231.syntax_only);
       ds_hooks = (uu___135_12231.ds_hooks)
     })
  
let (pop : unit -> env) =
  fun uu____12250  ->
    let uu____12251 = FStar_ST.op_Bang stack  in
    match uu____12251 with
    | env::tl1 ->
        (pop_record_cache (); FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____12314 -> failwith "Impossible: Too many pops"
  
let (export_interface : FStar_Ident.lident -> env -> env) =
  fun m  ->
    fun env  ->
      let sigelt_in_m se =
        match FStar_Syntax_Util.lids_of_sigelt se with
        | l::uu____12334 -> l.FStar_Ident.nsstr = m.FStar_Ident.str
        | uu____12337 -> false  in
      let sm = sigmap env  in
      let env1 = pop ()  in
      let keys = FStar_Util.smap_keys sm  in
      let sm' = sigmap env1  in
      FStar_All.pipe_right keys
        (FStar_List.iter
           (fun k  ->
              let uu____12371 = FStar_Util.smap_try_find sm' k  in
              match uu____12371 with
              | FStar_Pervasives_Native.Some (se,true ) when sigelt_in_m se
                  ->
                  (FStar_Util.smap_remove sm' k;
                   (let se1 =
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t) ->
                          let uu___136_12396 = se  in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (uu___136_12396.FStar_Syntax_Syntax.sigel);
                            FStar_Syntax_Syntax.sigrng =
                              (uu___136_12396.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (FStar_Syntax_Syntax.Assumption ::
                              (se.FStar_Syntax_Syntax.sigquals));
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___136_12396.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___136_12396.FStar_Syntax_Syntax.sigattrs)
                          }
                      | uu____12397 -> se  in
                    FStar_Util.smap_add sm' k (se1, false)))
              | uu____12402 -> ()));
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
      let uu____12425 = finish env modul1  in (uu____12425, modul1)
  
type exported_ids =
  {
  exported_id_terms: Prims.string Prims.list ;
  exported_id_fields: Prims.string Prims.list }[@@deriving show]
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
      let uu____12513 =
        let uu____12516 = e Exported_id_term_type  in
        FStar_ST.op_Bang uu____12516  in
      FStar_Util.set_elements uu____12513  in
    let fields =
      let uu____12638 =
        let uu____12641 = e Exported_id_field  in
        FStar_ST.op_Bang uu____12641  in
      FStar_Util.set_elements uu____12638  in
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
          let uu____12800 =
            FStar_Util.as_set e1.exported_id_terms FStar_Util.compare  in
          FStar_Util.mk_ref uu____12800  in
        let fields =
          let uu____12810 =
            FStar_Util.as_set e1.exported_id_fields FStar_Util.compare  in
          FStar_Util.mk_ref uu____12810  in
        (fun uu___111_12815  ->
           match uu___111_12815 with
           | Exported_id_term_type  -> terms
           | Exported_id_field  -> fields)
  
type module_inclusion_info =
  {
  mii_exported_ids: exported_ids FStar_Pervasives_Native.option ;
  mii_trans_exported_ids: exported_ids FStar_Pervasives_Native.option ;
  mii_includes: FStar_Ident.lident Prims.list FStar_Pervasives_Native.option }
[@@deriving show]
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
  'Auu____12946 .
    'Auu____12946 Prims.list FStar_Pervasives_Native.option ->
      'Auu____12946 Prims.list FStar_ST.ref
  =
  fun uu___112_12959  ->
    match uu___112_12959 with
    | FStar_Pervasives_Native.None  -> FStar_Util.mk_ref []
    | FStar_Pervasives_Native.Some l -> FStar_Util.mk_ref l
  
let (inclusion_info : env -> FStar_Ident.lident -> module_inclusion_info) =
  fun env  ->
    fun l  ->
      let mname = FStar_Ident.string_of_lid l  in
      let as_ids_opt m =
        let uu____13000 = FStar_Util.smap_try_find m mname  in
        FStar_Util.map_opt uu____13000 as_exported_ids  in
      let uu____13006 = as_ids_opt env.exported_ids  in
      let uu____13009 = as_ids_opt env.trans_exported_ids  in
      let uu____13012 =
        let uu____13017 = FStar_Util.smap_try_find env.includes mname  in
        FStar_Util.map_opt uu____13017 (fun r  -> FStar_ST.op_Bang r)  in
      {
        mii_exported_ids = uu____13006;
        mii_trans_exported_ids = uu____13009;
        mii_includes = uu____13012
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
                let uu____13136 = FStar_Ident.text_of_lid mname  in
                FStar_Util.strcat uu____13136 ".fst"  in
              let auto_open =
                FStar_Parser_Dep.hard_coded_dependencies filename  in
              let auto_open1 =
                let convert_kind uu___113_13156 =
                  match uu___113_13156 with
                  | FStar_Parser_Dep.Open_namespace  -> Open_namespace
                  | FStar_Parser_Dep.Open_module  -> Open_module  in
                FStar_List.map
                  (fun uu____13168  ->
                     match uu____13168 with
                     | (lid,kind) -> (lid, (convert_kind kind))) auto_open
                 in
              let namespace_of_module =
                if
                  (FStar_List.length mname.FStar_Ident.ns) >
                    (Prims.parse_int "0")
                then
                  let uu____13192 =
                    let uu____13197 =
                      FStar_Ident.lid_of_ids mname.FStar_Ident.ns  in
                    (uu____13197, Open_namespace)  in
                  [uu____13192]
                else []  in
              let auto_open2 =
                FStar_List.append namespace_of_module
                  (FStar_List.rev auto_open1)
                 in
              (let uu____13227 = as_exported_id_set mii.mii_exported_ids  in
               FStar_Util.smap_add env1.exported_ids mname.FStar_Ident.str
                 uu____13227);
              (match () with
               | () ->
                   ((let uu____13254 =
                       as_exported_id_set mii.mii_trans_exported_ids  in
                     FStar_Util.smap_add env1.trans_exported_ids
                       mname.FStar_Ident.str uu____13254);
                    (match () with
                     | () ->
                         ((let uu____13281 = as_includes mii.mii_includes  in
                           FStar_Util.smap_add env1.includes
                             mname.FStar_Ident.str uu____13281);
                          (match () with
                           | () ->
                               let env' =
                                 let uu___137_13313 = env1  in
                                 let uu____13314 =
                                   FStar_List.map
                                     (fun x  -> Open_module_or_namespace x)
                                     auto_open2
                                    in
                                 {
                                   curmodule =
                                     (FStar_Pervasives_Native.Some mname);
                                   curmonad = (uu___137_13313.curmonad);
                                   modules = (uu___137_13313.modules);
                                   scope_mods = uu____13314;
                                   exported_ids =
                                     (uu___137_13313.exported_ids);
                                   trans_exported_ids =
                                     (uu___137_13313.trans_exported_ids);
                                   includes = (uu___137_13313.includes);
                                   sigaccum = (uu___137_13313.sigaccum);
                                   sigmap = (env1.sigmap);
                                   iface = intf;
                                   admitted_iface = admitted;
                                   expect_typ = (uu___137_13313.expect_typ);
                                   docs = (uu___137_13313.docs);
                                   remaining_iface_decls =
                                     (uu___137_13313.remaining_iface_decls);
                                   syntax_only = (uu___137_13313.syntax_only);
                                   ds_hooks = (uu___137_13313.ds_hooks)
                                 }  in
                               (FStar_List.iter
                                  (fun op  ->
                                     (env1.ds_hooks).ds_push_open_hook env'
                                       op) (FStar_List.rev auto_open2);
                                env'))))))
               in
            let uu____13326 =
              FStar_All.pipe_right env.modules
                (FStar_Util.find_opt
                   (fun uu____13352  ->
                      match uu____13352 with
                      | (l,uu____13358) -> FStar_Ident.lid_equals l mname))
               in
            match uu____13326 with
            | FStar_Pervasives_Native.None  ->
                let uu____13367 = prep env  in (uu____13367, false)
            | FStar_Pervasives_Native.Some (uu____13368,m) ->
                ((let uu____13375 =
                    (let uu____13378 = FStar_Options.interactive ()  in
                     Prims.op_Negation uu____13378) &&
                      ((Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)
                         || intf)
                     in
                  if uu____13375
                  then
                    let uu____13379 =
                      let uu____13384 =
                        FStar_Util.format1
                          "Duplicate module or interface name: %s"
                          mname.FStar_Ident.str
                         in
                      (FStar_Errors.Fatal_DuplicateModuleOrInterface,
                        uu____13384)
                       in
                    let uu____13385 = FStar_Ident.range_of_lid mname  in
                    FStar_Errors.raise_error uu____13379 uu____13385
                  else ());
                 (let uu____13387 =
                    let uu____13388 = push env  in prep uu____13388  in
                  (uu____13387, true)))
  
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
          let uu___138_13400 = env  in
          {
            curmodule = (uu___138_13400.curmodule);
            curmonad = (FStar_Pervasives_Native.Some mname);
            modules = (uu___138_13400.modules);
            scope_mods = (uu___138_13400.scope_mods);
            exported_ids = (uu___138_13400.exported_ids);
            trans_exported_ids = (uu___138_13400.trans_exported_ids);
            includes = (uu___138_13400.includes);
            sigaccum = (uu___138_13400.sigaccum);
            sigmap = (uu___138_13400.sigmap);
            iface = (uu___138_13400.iface);
            admitted_iface = (uu___138_13400.admitted_iface);
            expect_typ = (uu___138_13400.expect_typ);
            docs = (uu___138_13400.docs);
            remaining_iface_decls = (uu___138_13400.remaining_iface_decls);
            syntax_only = (uu___138_13400.syntax_only);
            ds_hooks = (uu___138_13400.ds_hooks)
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
        let uu____13434 = lookup1 lid  in
        match uu____13434 with
        | FStar_Pervasives_Native.None  ->
            let opened_modules =
              FStar_List.map
                (fun uu____13447  ->
                   match uu____13447 with
                   | (lid1,uu____13453) -> FStar_Ident.text_of_lid lid1)
                env.modules
               in
            let msg =
              let uu____13455 = FStar_Ident.text_of_lid lid  in
              FStar_Util.format1 "Identifier not found: [%s]" uu____13455  in
            let msg1 =
              if
                (FStar_List.length lid.FStar_Ident.ns) =
                  (Prims.parse_int "0")
              then msg
              else
                (let modul =
                   let uu____13460 =
                     FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
                   let uu____13461 = FStar_Ident.range_of_lid lid  in
                   FStar_Ident.set_lid_range uu____13460 uu____13461  in
                 let uu____13462 = resolve_module_name env modul true  in
                 match uu____13462 with
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
            let uu____13471 = FStar_Ident.range_of_lid lid  in
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_IdentifierNotFound, msg1) uu____13471
        | FStar_Pervasives_Native.Some r -> r
  
let fail_or2 :
  'a .
    (FStar_Ident.ident -> 'a FStar_Pervasives_Native.option) ->
      FStar_Ident.ident -> 'a
  =
  fun lookup1  ->
    fun id1  ->
      let uu____13499 = lookup1 id1  in
      match uu____13499 with
      | FStar_Pervasives_Native.None  ->
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_IdentifierNotFound,
              (Prims.strcat "Identifier not found ["
                 (Prims.strcat id1.FStar_Ident.idText "]")))
            id1.FStar_Ident.idRange
      | FStar_Pervasives_Native.Some r -> r
  
let (mk_copy : env -> env) =
  fun en  ->
    let uu___139_13508 = en  in
    let uu____13509 = FStar_Util.smap_copy en.exported_ids  in
    let uu____13514 = FStar_Util.smap_copy en.trans_exported_ids  in
    let uu____13519 = FStar_Util.smap_copy en.sigmap  in
    let uu____13530 = FStar_Util.smap_copy en.docs  in
    {
      curmodule = (uu___139_13508.curmodule);
      curmonad = (uu___139_13508.curmonad);
      modules = (uu___139_13508.modules);
      scope_mods = (uu___139_13508.scope_mods);
      exported_ids = uu____13509;
      trans_exported_ids = uu____13514;
      includes = (uu___139_13508.includes);
      sigaccum = (uu___139_13508.sigaccum);
      sigmap = uu____13519;
      iface = (uu___139_13508.iface);
      admitted_iface = (uu___139_13508.admitted_iface);
      expect_typ = (uu___139_13508.expect_typ);
      docs = uu____13530;
      remaining_iface_decls = (uu___139_13508.remaining_iface_decls);
      syntax_only = (uu___139_13508.syntax_only);
      ds_hooks = (uu___139_13508.ds_hooks)
    }
  