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
            let uu____1910 = exported_id_set Exported_id_term_type  in
            FStar_ST.op_Bang uu____1910  in
          FStar_All.pipe_right uu____1909 FStar_Util.set_elements
  
let (open_modules :
  env ->
    (FStar_Ident.lident,FStar_Syntax_Syntax.modul)
      FStar_Pervasives_Native.tuple2 Prims.list)
  = fun e  -> e.modules 
let (open_modules_and_namespaces : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    FStar_List.filter_map
      (fun uu___82_2052  ->
         match uu___82_2052 with
         | Open_module_or_namespace (lid,_info) ->
             FStar_Pervasives_Native.Some lid
         | uu____2057 -> FStar_Pervasives_Native.None) env.scope_mods
  
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun e  ->
    fun l  ->
      let uu___117_2068 = e  in
      {
        curmodule = (FStar_Pervasives_Native.Some l);
        curmonad = (uu___117_2068.curmonad);
        modules = (uu___117_2068.modules);
        scope_mods = (uu___117_2068.scope_mods);
        exported_ids = (uu___117_2068.exported_ids);
        trans_exported_ids = (uu___117_2068.trans_exported_ids);
        includes = (uu___117_2068.includes);
        sigaccum = (uu___117_2068.sigaccum);
        sigmap = (uu___117_2068.sigmap);
        iface = (uu___117_2068.iface);
        admitted_iface = (uu___117_2068.admitted_iface);
        expect_typ = (uu___117_2068.expect_typ);
        docs = (uu___117_2068.docs);
        remaining_iface_decls = (uu___117_2068.remaining_iface_decls);
        syntax_only = (uu___117_2068.syntax_only);
        ds_hooks = (uu___117_2068.ds_hooks)
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
      let uu____2089 =
        FStar_All.pipe_right env.remaining_iface_decls
          (FStar_List.tryFind
             (fun uu____2123  ->
                match uu____2123 with
                | (m,uu____2131) -> FStar_Ident.lid_equals l m))
         in
      match uu____2089 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (uu____2148,decls) ->
          FStar_Pervasives_Native.Some decls
  
let (set_iface_decls :
  env -> FStar_Ident.lident -> FStar_Parser_AST.decl Prims.list -> env) =
  fun env  ->
    fun l  ->
      fun ds  ->
        let uu____2181 =
          FStar_List.partition
            (fun uu____2211  ->
               match uu____2211 with
               | (m,uu____2219) -> FStar_Ident.lid_equals l m)
            env.remaining_iface_decls
           in
        match uu____2181 with
        | (uu____2224,rest) ->
            let uu___118_2258 = env  in
            {
              curmodule = (uu___118_2258.curmodule);
              curmonad = (uu___118_2258.curmonad);
              modules = (uu___118_2258.modules);
              scope_mods = (uu___118_2258.scope_mods);
              exported_ids = (uu___118_2258.exported_ids);
              trans_exported_ids = (uu___118_2258.trans_exported_ids);
              includes = (uu___118_2258.includes);
              sigaccum = (uu___118_2258.sigaccum);
              sigmap = (uu___118_2258.sigmap);
              iface = (uu___118_2258.iface);
              admitted_iface = (uu___118_2258.admitted_iface);
              expect_typ = (uu___118_2258.expect_typ);
              docs = (uu___118_2258.docs);
              remaining_iface_decls = ((l, ds) :: rest);
              syntax_only = (uu___118_2258.syntax_only);
              ds_hooks = (uu___118_2258.ds_hooks)
            }
  
let (qual : FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident) =
  FStar_Syntax_Util.qual_id 
let (qualify : env -> FStar_Ident.ident -> FStar_Ident.lident) =
  fun env  ->
    fun id1  ->
      match env.curmonad with
      | FStar_Pervasives_Native.None  ->
          let uu____2285 = current_module env  in qual uu____2285 id1
      | FStar_Pervasives_Native.Some monad ->
          let uu____2287 =
            let uu____2288 = current_module env  in qual uu____2288 monad  in
          FStar_Syntax_Util.mk_field_projector_name_from_ident uu____2287 id1
  
let (syntax_only : env -> Prims.bool) = fun env  -> env.syntax_only 
let (set_syntax_only : env -> Prims.bool -> env) =
  fun env  ->
    fun b  ->
      let uu___119_2304 = env  in
      {
        curmodule = (uu___119_2304.curmodule);
        curmonad = (uu___119_2304.curmonad);
        modules = (uu___119_2304.modules);
        scope_mods = (uu___119_2304.scope_mods);
        exported_ids = (uu___119_2304.exported_ids);
        trans_exported_ids = (uu___119_2304.trans_exported_ids);
        includes = (uu___119_2304.includes);
        sigaccum = (uu___119_2304.sigaccum);
        sigmap = (uu___119_2304.sigmap);
        iface = (uu___119_2304.iface);
        admitted_iface = (uu___119_2304.admitted_iface);
        expect_typ = (uu___119_2304.expect_typ);
        docs = (uu___119_2304.docs);
        remaining_iface_decls = (uu___119_2304.remaining_iface_decls);
        syntax_only = b;
        ds_hooks = (uu___119_2304.ds_hooks)
      }
  
let (ds_hooks : env -> dsenv_hooks) = fun env  -> env.ds_hooks 
let (set_ds_hooks : env -> dsenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___120_2320 = env  in
      {
        curmodule = (uu___120_2320.curmodule);
        curmonad = (uu___120_2320.curmonad);
        modules = (uu___120_2320.modules);
        scope_mods = (uu___120_2320.scope_mods);
        exported_ids = (uu___120_2320.exported_ids);
        trans_exported_ids = (uu___120_2320.trans_exported_ids);
        includes = (uu___120_2320.includes);
        sigaccum = (uu___120_2320.sigaccum);
        sigmap = (uu___120_2320.sigmap);
        iface = (uu___120_2320.iface);
        admitted_iface = (uu___120_2320.admitted_iface);
        expect_typ = (uu___120_2320.expect_typ);
        docs = (uu___120_2320.docs);
        remaining_iface_decls = (uu___120_2320.remaining_iface_decls);
        syntax_only = (uu___120_2320.syntax_only);
        ds_hooks = hooks
      }
  
let new_sigmap : 'Auu____2325 . unit -> 'Auu____2325 FStar_Util.smap =
  fun uu____2332  -> FStar_Util.smap_create (Prims.parse_int "100") 
let (empty_env : unit -> env) =
  fun uu____2337  ->
    let uu____2338 = new_sigmap ()  in
    let uu____2343 = new_sigmap ()  in
    let uu____2348 = new_sigmap ()  in
    let uu____2359 = new_sigmap ()  in
    let uu____2370 = new_sigmap ()  in
    {
      curmodule = FStar_Pervasives_Native.None;
      curmonad = FStar_Pervasives_Native.None;
      modules = [];
      scope_mods = [];
      exported_ids = uu____2338;
      trans_exported_ids = uu____2343;
      includes = uu____2348;
      sigaccum = [];
      sigmap = uu____2359;
      iface = false;
      admitted_iface = false;
      expect_typ = false;
      docs = uu____2370;
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
      (fun uu____2406  ->
         match uu____2406 with
         | (m,uu____2412) ->
             FStar_Ident.lid_equals m FStar_Parser_Const.all_lid) env.modules
  
let (set_bv_range :
  FStar_Syntax_Syntax.bv -> FStar_Range.range -> FStar_Syntax_Syntax.bv) =
  fun bv  ->
    fun r  ->
      let id1 =
        let uu___121_2424 = bv.FStar_Syntax_Syntax.ppname  in
        {
          FStar_Ident.idText = (uu___121_2424.FStar_Ident.idText);
          FStar_Ident.idRange = r
        }  in
      let uu___122_2425 = bv  in
      {
        FStar_Syntax_Syntax.ppname = id1;
        FStar_Syntax_Syntax.index = (uu___122_2425.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = (uu___122_2425.FStar_Syntax_Syntax.sort)
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
        (fun uu____2518  ->
           match uu____2518 with
           | (x,y,dd,dq) ->
               if id1.FStar_Ident.idText = x
               then
                 let uu____2541 =
                   let uu____2542 =
                     FStar_Ident.lid_of_path ["Prims"; y]
                       id1.FStar_Ident.idRange
                      in
                   FStar_Syntax_Syntax.fvar uu____2542 dd dq  in
                 FStar_Pervasives_Native.Some uu____2541
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
    match projectee with | Cont_ok _0 -> true | uu____2589 -> false
  
let __proj__Cont_ok__item___0 : 'a . 'a cont_t -> 'a =
  fun projectee  -> match projectee with | Cont_ok _0 -> _0 
let uu___is_Cont_fail : 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_fail  -> true | uu____2622 -> false
  
let uu___is_Cont_ignore : 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_ignore  -> true | uu____2639 -> false
  
let option_of_cont :
  'a .
    (unit -> 'a FStar_Pervasives_Native.option) ->
      'a cont_t -> 'a FStar_Pervasives_Native.option
  =
  fun k_ignore  ->
    fun uu___83_2667  ->
      match uu___83_2667 with
      | Cont_ok a -> FStar_Pervasives_Native.Some a
      | Cont_fail  -> FStar_Pervasives_Native.None
      | Cont_ignore  -> k_ignore ()
  
let find_in_record :
  'Auu____2685 .
    FStar_Ident.ident Prims.list ->
      FStar_Ident.ident ->
        record_or_dc ->
          (record_or_dc -> 'Auu____2685 cont_t) -> 'Auu____2685 cont_t
  =
  fun ns  ->
    fun id1  ->
      fun record  ->
        fun cont  ->
          let typename' =
            FStar_Ident.lid_of_ids
              (FStar_List.append ns [(record.typename).FStar_Ident.ident])
             in
          let uu____2722 = FStar_Ident.lid_equals typename' record.typename
             in
          if uu____2722
          then
            let fname =
              FStar_Ident.lid_of_ids
                (FStar_List.append (record.typename).FStar_Ident.ns [id1])
               in
            let find1 =
              FStar_Util.find_map record.fields
                (fun uu____2736  ->
                   match uu____2736 with
                   | (f,uu____2744) ->
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
  fun uu___84_2806  ->
    match uu___84_2806 with
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
              let rec aux uu___85_2877 =
                match uu___85_2877 with
                | [] -> find_in_module_default
                | modul::q ->
                    let mname = modul.FStar_Ident.str  in
                    let not_shadowed =
                      let uu____2888 = get_exported_id_set env mname  in
                      match uu____2888 with
                      | FStar_Pervasives_Native.None  -> true
                      | FStar_Pervasives_Native.Some mex ->
                          let mexports =
                            let uu____2913 = mex eikind  in
                            FStar_ST.op_Bang uu____2913  in
                          FStar_Util.set_mem idstr mexports
                       in
                    let mincludes =
                      let uu____3035 =
                        FStar_Util.smap_try_find env.includes mname  in
                      match uu____3035 with
                      | FStar_Pervasives_Native.None  -> []
                      | FStar_Pervasives_Native.Some minc ->
                          FStar_ST.op_Bang minc
                       in
                    let look_into =
                      if not_shadowed
                      then
                        let uu____3115 = qual modul id1  in
                        find_in_module uu____3115
                      else Cont_ignore  in
                    (match look_into with
                     | Cont_ignore  -> aux (FStar_List.append mincludes q)
                     | uu____3119 -> look_into)
                 in
              aux [ns]
  
let (is_exported_id_field : exported_id_kind -> Prims.bool) =
  fun uu___86_3126  ->
    match uu___86_3126 with
    | Exported_id_field  -> true
    | uu____3127 -> false
  
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
                  let check_local_binding_id uu___87_3248 =
                    match uu___87_3248 with
                    | (id',uu____3250,uu____3251) ->
                        id'.FStar_Ident.idText = id1.FStar_Ident.idText
                     in
                  let check_rec_binding_id uu___88_3257 =
                    match uu___88_3257 with
                    | (id',uu____3259,uu____3260) ->
                        id'.FStar_Ident.idText = id1.FStar_Ident.idText
                     in
                  let curmod_ns =
                    let uu____3264 = current_module env  in
                    FStar_Ident.ids_of_lid uu____3264  in
                  let proc uu___89_3272 =
                    match uu___89_3272 with
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
                        let uu____3280 = FStar_Ident.lid_of_ids curmod_ns  in
                        find_in_module_with_includes Exported_id_field
                          (fun lid  ->
                             let id2 = lid.FStar_Ident.ident  in
                             find_in_record lid.FStar_Ident.ns id2 r k_record)
                          Cont_ignore env uu____3280 id1
                    | uu____3285 -> Cont_ignore  in
                  let rec aux uu___90_3295 =
                    match uu___90_3295 with
                    | a::q ->
                        let uu____3304 = proc a  in
                        option_of_cont (fun uu____3308  -> aux q) uu____3304
                    | [] ->
                        let uu____3309 = lookup_default_id Cont_fail id1  in
                        option_of_cont
                          (fun uu____3313  -> FStar_Pervasives_Native.None)
                          uu____3309
                     in
                  aux env.scope_mods
  
let found_local_binding :
  'Auu____3322 'Auu____3323 .
    FStar_Range.range ->
      ('Auu____3322,FStar_Syntax_Syntax.bv,'Auu____3323)
        FStar_Pervasives_Native.tuple3 ->
        (FStar_Syntax_Syntax.term,'Auu____3323)
          FStar_Pervasives_Native.tuple2
  =
  fun r  ->
    fun uu____3343  ->
      match uu____3343 with
      | (id',x,mut) -> let uu____3353 = bv_to_name x r  in (uu____3353, mut)
  
let find_in_module :
  'Auu____3364 .
    env ->
      FStar_Ident.lident ->
        (FStar_Ident.lident ->
           (FStar_Syntax_Syntax.sigelt,Prims.bool)
             FStar_Pervasives_Native.tuple2 -> 'Auu____3364)
          -> 'Auu____3364 -> 'Auu____3364
  =
  fun env  ->
    fun lid  ->
      fun k_global_def  ->
        fun k_not_found  ->
          let uu____3403 =
            FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str  in
          match uu____3403 with
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
      let uu____3443 = unmangleOpName id1  in
      match uu____3443 with
      | FStar_Pervasives_Native.Some f -> FStar_Pervasives_Native.Some f
      | uu____3469 ->
          try_lookup_id'' env id1 Exported_id_term_type
            (fun r  ->
               let uu____3483 = found_local_binding id1.FStar_Ident.idRange r
                  in
               Cont_ok uu____3483) (fun uu____3493  -> Cont_fail)
            (fun uu____3499  -> Cont_ignore)
            (fun i  ->
               find_in_module env i
                 (fun uu____3514  -> fun uu____3515  -> Cont_fail)
                 Cont_ignore)
            (fun uu____3530  -> fun uu____3531  -> Cont_fail)
  
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
            | FStar_Pervasives_Native.Some uu____3610 ->
                let lid = qualify env id1  in
                let uu____3612 =
                  FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str
                   in
                (match uu____3612 with
                 | FStar_Pervasives_Native.Some r ->
                     let uu____3636 = k_global_def lid r  in
                     FStar_Pervasives_Native.Some uu____3636
                 | FStar_Pervasives_Native.None  ->
                     FStar_Pervasives_Native.None)
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             in
          match find_in_monad with
          | FStar_Pervasives_Native.Some v1 -> v1
          | FStar_Pervasives_Native.None  ->
              let lid =
                let uu____3659 = current_module env  in qual uu____3659 id1
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
        let rec aux uu___91_3722 =
          match uu___91_3722 with
          | [] ->
              let uu____3727 = module_is_defined env lid  in
              if uu____3727
              then FStar_Pervasives_Native.Some lid
              else FStar_Pervasives_Native.None
          | (Open_module_or_namespace (ns,Open_namespace ))::q when honor_ns
              ->
              let new_lid =
                let uu____3736 =
                  let uu____3737 = FStar_Ident.path_of_lid ns  in
                  let uu____3740 = FStar_Ident.path_of_lid lid  in
                  FStar_List.append uu____3737 uu____3740  in
                let uu____3743 = FStar_Ident.range_of_lid lid  in
                FStar_Ident.lid_of_path uu____3736 uu____3743  in
              let uu____3744 = module_is_defined env new_lid  in
              if uu____3744
              then FStar_Pervasives_Native.Some new_lid
              else aux q
          | (Module_abbrev (name,modul))::uu____3750 when
              (nslen = (Prims.parse_int "0")) &&
                (name.FStar_Ident.idText =
                   (lid.FStar_Ident.ident).FStar_Ident.idText)
              -> FStar_Pervasives_Native.Some modul
          | uu____3757::q -> aux q  in
        aux env.scope_mods
  
let (fail_if_curmodule :
  env -> FStar_Ident.lident -> FStar_Ident.lident -> unit) =
  fun env  ->
    fun ns_original  ->
      fun ns_resolved  ->
        let uu____3776 =
          let uu____3777 = current_module env  in
          FStar_Ident.lid_equals ns_resolved uu____3777  in
        if uu____3776
        then
          let uu____3778 =
            FStar_Ident.lid_equals ns_resolved FStar_Parser_Const.prims_lid
             in
          (if uu____3778
           then ()
           else
             (let uu____3780 =
                let uu____3785 =
                  FStar_Util.format1
                    "Reference %s to current module is forbidden (see GitHub issue #451)"
                    ns_original.FStar_Ident.str
                   in
                (FStar_Errors.Fatal_ForbiddenReferenceToCurrentModule,
                  uu____3785)
                 in
              let uu____3786 = FStar_Ident.range_of_lid ns_original  in
              FStar_Errors.raise_error uu____3780 uu____3786))
        else ()
  
let (fail_if_qualified_by_curmodule : env -> FStar_Ident.lident -> unit) =
  fun env  ->
    fun lid  ->
      match lid.FStar_Ident.ns with
      | [] -> ()
      | uu____3798 ->
          let modul_orig = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          let uu____3802 = resolve_module_name env modul_orig true  in
          (match uu____3802 with
           | FStar_Pervasives_Native.Some modul_res ->
               fail_if_curmodule env modul_orig modul_res
           | uu____3806 -> ())
  
let (is_open : env -> FStar_Ident.lident -> open_kind -> Prims.bool) =
  fun env  ->
    fun lid  ->
      fun open_kind  ->
        FStar_List.existsb
          (fun uu___92_3827  ->
             match uu___92_3827 with
             | Open_module_or_namespace (ns,k) ->
                 (k = open_kind) && (FStar_Ident.lid_equals lid ns)
             | uu____3830 -> false) env.scope_mods
  
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
                 let uu____3949 = aux rev_ns_prefix ns_last_id  in
                 FStar_All.pipe_right uu____3949
                   (FStar_Util.map_option
                      (fun uu____3999  ->
                         match uu____3999 with
                         | (stripped_ids,rev_kept_ids) ->
                             (stripped_ids, (id1 :: rev_kept_ids)))))
           in
        let do_shorten env1 ids1 =
          match FStar_List.rev ids1 with
          | [] -> ([], [])
          | ns_last_id::ns_rev_prefix ->
              let uu____4069 = aux ns_rev_prefix ns_last_id  in
              (match uu____4069 with
               | FStar_Pervasives_Native.None  -> ([], ids1)
               | FStar_Pervasives_Native.Some (stripped_ids,rev_kept_ids) ->
                   (stripped_ids, (FStar_List.rev rev_kept_ids)))
           in
        if is_full_path
        then
          let uu____4130 =
            let uu____4133 = FStar_Ident.lid_of_ids ids  in
            resolve_module_name env uu____4133 true  in
          match uu____4130 with
          | FStar_Pervasives_Native.Some m when module_is_open env m ->
              (ids, [])
          | uu____4147 -> do_shorten env ids
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
                  | uu____4266::uu____4267 ->
                      let uu____4270 =
                        let uu____4273 =
                          let uu____4274 =
                            FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
                          let uu____4275 = FStar_Ident.range_of_lid lid  in
                          FStar_Ident.set_lid_range uu____4274 uu____4275  in
                        resolve_module_name env uu____4273 true  in
                      (match uu____4270 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some modul ->
                           let uu____4279 =
                             find_in_module_with_includes eikind f_module
                               Cont_fail env modul lid.FStar_Ident.ident
                              in
                           option_of_cont
                             (fun uu____4283  -> FStar_Pervasives_Native.None)
                             uu____4279)
                  | [] ->
                      try_lookup_id'' env lid.FStar_Ident.ident eikind
                        k_local_binding k_rec_binding k_record f_module
                        l_default
  
let cont_of_option :
  'a . 'a cont_t -> 'a FStar_Pervasives_Native.option -> 'a cont_t =
  fun k_none  ->
    fun uu___93_4306  ->
      match uu___93_4306 with
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
              let uu____4422 = k_global_def lid1 def  in
              cont_of_option k uu____4422  in
            let f_module lid' =
              let k = Cont_ignore  in
              find_in_module env lid' (k_global_def' k) k  in
            let l_default k i = lookup_default_id env i (k_global_def' k) k
               in
            resolve_in_open_namespaces'' env lid Exported_id_term_type
              (fun l  ->
                 let uu____4458 = k_local_binding l  in
                 cont_of_option Cont_fail uu____4458)
              (fun r  ->
                 let uu____4464 = k_rec_binding r  in
                 cont_of_option Cont_fail uu____4464)
              (fun uu____4468  -> Cont_ignore) f_module l_default
  
let (fv_qual_of_se :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option)
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____4478,uu____4479,uu____4480,l,uu____4482,uu____4483) ->
        let qopt =
          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
            (fun uu___94_4494  ->
               match uu___94_4494 with
               | FStar_Syntax_Syntax.RecordConstructor (uu____4497,fs) ->
                   FStar_Pervasives_Native.Some
                     (FStar_Syntax_Syntax.Record_ctor (l, fs))
               | uu____4509 -> FStar_Pervasives_Native.None)
           in
        (match qopt with
         | FStar_Pervasives_Native.None  ->
             FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor
         | x -> x)
    | FStar_Syntax_Syntax.Sig_declare_typ (uu____4515,uu____4516,uu____4517)
        -> FStar_Pervasives_Native.None
    | uu____4518 -> FStar_Pervasives_Native.None
  
let (lb_fv :
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Ident.lident -> FStar_Syntax_Syntax.fv)
  =
  fun lbs  ->
    fun lid  ->
      let uu____4533 =
        FStar_Util.find_map lbs
          (fun lb  ->
             let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
             let uu____4541 = FStar_Syntax_Syntax.fv_eq_lid fv lid  in
             if uu____4541
             then FStar_Pervasives_Native.Some fv
             else FStar_Pervasives_Native.None)
         in
      FStar_All.pipe_right uu____4533 FStar_Util.must
  
let (ns_of_lid_equals :
  FStar_Ident.lident -> FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    fun ns  ->
      (let uu____4559 =
         let uu____4560 = FStar_Ident.ids_of_lid ns  in
         FStar_List.length uu____4560  in
       (FStar_List.length lid.FStar_Ident.ns) = uu____4559) &&
        (let uu____4568 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
         FStar_Ident.lid_equals uu____4568 ns)
  
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
          let k_global_def source_lid uu___99_4610 =
            match uu___99_4610 with
            | (uu____4617,true ) when exclude_interf ->
                FStar_Pervasives_Native.None
            | (se,uu____4619) ->
                (match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_inductive_typ uu____4622 ->
                     let uu____4639 =
                       let uu____4640 =
                         let uu____4649 =
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.Delta_constant
                             FStar_Pervasives_Native.None
                            in
                         (uu____4649, false,
                           (se.FStar_Syntax_Syntax.sigattrs))
                          in
                       Term_name uu____4640  in
                     FStar_Pervasives_Native.Some uu____4639
                 | FStar_Syntax_Syntax.Sig_datacon uu____4652 ->
                     let uu____4667 =
                       let uu____4668 =
                         let uu____4677 =
                           let uu____4678 = fv_qual_of_se se  in
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.Delta_constant uu____4678
                            in
                         (uu____4677, false,
                           (se.FStar_Syntax_Syntax.sigattrs))
                          in
                       Term_name uu____4668  in
                     FStar_Pervasives_Native.Some uu____4667
                 | FStar_Syntax_Syntax.Sig_let ((uu____4683,lbs),uu____4685)
                     ->
                     let fv = lb_fv lbs source_lid  in
                     let uu____4701 =
                       let uu____4702 =
                         let uu____4711 =
                           FStar_Syntax_Syntax.fvar source_lid
                             fv.FStar_Syntax_Syntax.fv_delta
                             fv.FStar_Syntax_Syntax.fv_qual
                            in
                         (uu____4711, false,
                           (se.FStar_Syntax_Syntax.sigattrs))
                          in
                       Term_name uu____4702  in
                     FStar_Pervasives_Native.Some uu____4701
                 | FStar_Syntax_Syntax.Sig_declare_typ
                     (lid1,uu____4715,uu____4716) ->
                     let quals = se.FStar_Syntax_Syntax.sigquals  in
                     let uu____4720 =
                       any_val ||
                         (FStar_All.pipe_right quals
                            (FStar_Util.for_some
                               (fun uu___95_4724  ->
                                  match uu___95_4724 with
                                  | FStar_Syntax_Syntax.Assumption  -> true
                                  | uu____4725 -> false)))
                        in
                     if uu____4720
                     then
                       let lid2 =
                         let uu____4729 = FStar_Ident.range_of_lid source_lid
                            in
                         FStar_Ident.set_lid_range lid1 uu____4729  in
                       let dd =
                         let uu____4731 =
                           (FStar_Syntax_Util.is_primop_lid lid2) ||
                             (FStar_All.pipe_right quals
                                (FStar_Util.for_some
                                   (fun uu___96_4736  ->
                                      match uu___96_4736 with
                                      | FStar_Syntax_Syntax.Projector
                                          uu____4737 -> true
                                      | FStar_Syntax_Syntax.Discriminator
                                          uu____4742 -> true
                                      | uu____4743 -> false)))
                            in
                         if uu____4731
                         then FStar_Syntax_Syntax.Delta_equational
                         else FStar_Syntax_Syntax.Delta_constant  in
                       let dd1 =
                         let uu____4746 =
                           FStar_All.pipe_right quals
                             (FStar_Util.for_some
                                (fun uu___97_4750  ->
                                   match uu___97_4750 with
                                   | FStar_Syntax_Syntax.Abstract  -> true
                                   | uu____4751 -> false))
                            in
                         if uu____4746
                         then FStar_Syntax_Syntax.Delta_abstract dd
                         else dd  in
                       let uu____4753 =
                         FStar_Util.find_map quals
                           (fun uu___98_4758  ->
                              match uu___98_4758 with
                              | FStar_Syntax_Syntax.Reflectable refl_monad ->
                                  FStar_Pervasives_Native.Some refl_monad
                              | uu____4762 -> FStar_Pervasives_Native.None)
                          in
                       (match uu____4753 with
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
                        | uu____4773 ->
                            let uu____4776 =
                              let uu____4777 =
                                let uu____4786 =
                                  let uu____4787 = fv_qual_of_se se  in
                                  FStar_Syntax_Syntax.fvar lid2 dd1
                                    uu____4787
                                   in
                                (uu____4786, false,
                                  (se.FStar_Syntax_Syntax.sigattrs))
                                 in
                              Term_name uu____4777  in
                            FStar_Pervasives_Native.Some uu____4776)
                     else FStar_Pervasives_Native.None
                 | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
                     let uu____4794 =
                       let uu____4795 =
                         let uu____4800 =
                           let uu____4801 =
                             FStar_Ident.range_of_lid source_lid  in
                           FStar_Ident.set_lid_range
                             ne.FStar_Syntax_Syntax.mname uu____4801
                            in
                         (se, uu____4800)  in
                       Eff_name uu____4795  in
                     FStar_Pervasives_Native.Some uu____4794
                 | FStar_Syntax_Syntax.Sig_new_effect ne ->
                     let uu____4803 =
                       let uu____4804 =
                         let uu____4809 =
                           let uu____4810 =
                             FStar_Ident.range_of_lid source_lid  in
                           FStar_Ident.set_lid_range
                             ne.FStar_Syntax_Syntax.mname uu____4810
                            in
                         (se, uu____4809)  in
                       Eff_name uu____4804  in
                     FStar_Pervasives_Native.Some uu____4803
                 | FStar_Syntax_Syntax.Sig_effect_abbrev uu____4811 ->
                     FStar_Pervasives_Native.Some (Eff_name (se, source_lid))
                 | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
                     let uu____4830 =
                       let uu____4831 =
                         let uu____4840 =
                           FStar_Syntax_Syntax.fvar source_lid
                             (FStar_Syntax_Syntax.Delta_defined_at_level
                                (Prims.parse_int "1"))
                             FStar_Pervasives_Native.None
                            in
                         (uu____4840, false, [])  in
                       Term_name uu____4831  in
                     FStar_Pervasives_Native.Some uu____4830
                 | uu____4843 -> FStar_Pervasives_Native.None)
             in
          let k_local_binding r =
            let uu____4864 =
              let uu____4869 = FStar_Ident.range_of_lid lid  in
              found_local_binding uu____4869 r  in
            match uu____4864 with
            | (t,mut) ->
                FStar_Pervasives_Native.Some (Term_name (t, mut, []))
             in
          let k_rec_binding uu____4889 =
            match uu____4889 with
            | (id1,l,dd) ->
                let uu____4901 =
                  let uu____4902 =
                    let uu____4911 =
                      let uu____4912 =
                        let uu____4913 = FStar_Ident.range_of_lid lid  in
                        FStar_Ident.set_lid_range l uu____4913  in
                      FStar_Syntax_Syntax.fvar uu____4912 dd
                        FStar_Pervasives_Native.None
                       in
                    (uu____4911, false, [])  in
                  Term_name uu____4902  in
                FStar_Pervasives_Native.Some uu____4901
             in
          let found_unmangled =
            match lid.FStar_Ident.ns with
            | [] ->
                let uu____4921 = unmangleOpName lid.FStar_Ident.ident  in
                (match uu____4921 with
                 | FStar_Pervasives_Native.Some (t,mut) ->
                     FStar_Pervasives_Native.Some (Term_name (t, mut, []))
                 | uu____4938 -> FStar_Pervasives_Native.None)
            | uu____4945 -> FStar_Pervasives_Native.None  in
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
        let uu____4980 = try_lookup_name true exclude_interf env lid  in
        match uu____4980 with
        | FStar_Pervasives_Native.Some (Eff_name (o,l)) ->
            FStar_Pervasives_Native.Some (o, l)
        | uu____4995 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____5014 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____5014 with
      | FStar_Pervasives_Native.Some (o,l1) ->
          FStar_Pervasives_Native.Some l1
      | uu____5029 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_name_and_attributes :
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident,FStar_Syntax_Syntax.cflags Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____5054 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____5054 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____5070;
             FStar_Syntax_Syntax.sigquals = uu____5071;
             FStar_Syntax_Syntax.sigmeta = uu____5072;
             FStar_Syntax_Syntax.sigattrs = uu____5073;_},l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____5092;
             FStar_Syntax_Syntax.sigquals = uu____5093;
             FStar_Syntax_Syntax.sigmeta = uu____5094;
             FStar_Syntax_Syntax.sigattrs = uu____5095;_},l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (uu____5113,uu____5114,uu____5115,uu____5116,cattributes);
             FStar_Syntax_Syntax.sigrng = uu____5118;
             FStar_Syntax_Syntax.sigquals = uu____5119;
             FStar_Syntax_Syntax.sigmeta = uu____5120;
             FStar_Syntax_Syntax.sigattrs = uu____5121;_},l1)
          -> FStar_Pervasives_Native.Some (l1, cattributes)
      | uu____5143 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_defn :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.eff_decl FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____5168 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____5168 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____5178;
             FStar_Syntax_Syntax.sigquals = uu____5179;
             FStar_Syntax_Syntax.sigmeta = uu____5180;
             FStar_Syntax_Syntax.sigattrs = uu____5181;_},uu____5182)
          -> FStar_Pervasives_Native.Some ne
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____5192;
             FStar_Syntax_Syntax.sigquals = uu____5193;
             FStar_Syntax_Syntax.sigmeta = uu____5194;
             FStar_Syntax_Syntax.sigattrs = uu____5195;_},uu____5196)
          -> FStar_Pervasives_Native.Some ne
      | uu____5205 -> FStar_Pervasives_Native.None
  
let (is_effect_name : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____5222 = try_lookup_effect_name env lid  in
      match uu____5222 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____5225 -> true
  
let (try_lookup_root_effect_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____5238 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____5238 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (l',uu____5248,uu____5249,uu____5250,uu____5251);
             FStar_Syntax_Syntax.sigrng = uu____5252;
             FStar_Syntax_Syntax.sigquals = uu____5253;
             FStar_Syntax_Syntax.sigmeta = uu____5254;
             FStar_Syntax_Syntax.sigattrs = uu____5255;_},uu____5256)
          ->
          let rec aux new_name =
            let uu____5277 =
              FStar_Util.smap_try_find (sigmap env) new_name.FStar_Ident.str
               in
            match uu____5277 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (s,uu____5295) ->
                (match s.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
                     let uu____5303 =
                       let uu____5304 = FStar_Ident.range_of_lid l  in
                       FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname
                         uu____5304
                        in
                     FStar_Pervasives_Native.Some uu____5303
                 | FStar_Syntax_Syntax.Sig_new_effect ne ->
                     let uu____5306 =
                       let uu____5307 = FStar_Ident.range_of_lid l  in
                       FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname
                         uu____5307
                        in
                     FStar_Pervasives_Native.Some uu____5306
                 | FStar_Syntax_Syntax.Sig_effect_abbrev
                     (uu____5308,uu____5309,uu____5310,cmp,uu____5312) ->
                     let l'' = FStar_Syntax_Util.comp_effect_name cmp  in
                     aux l''
                 | uu____5318 -> FStar_Pervasives_Native.None)
             in
          aux l'
      | FStar_Pervasives_Native.Some (uu____5319,l') ->
          FStar_Pervasives_Native.Some l'
      | uu____5325 -> FStar_Pervasives_Native.None
  
let (lookup_letbinding_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___100_5362 =
        match uu___100_5362 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____5371,uu____5372,uu____5373);
             FStar_Syntax_Syntax.sigrng = uu____5374;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____5376;
             FStar_Syntax_Syntax.sigattrs = uu____5377;_},uu____5378)
            -> FStar_Pervasives_Native.Some quals
        | uu____5385 -> FStar_Pervasives_Native.None  in
      let uu____5392 =
        resolve_in_open_namespaces' env lid
          (fun uu____5400  -> FStar_Pervasives_Native.None)
          (fun uu____5404  -> FStar_Pervasives_Native.None) k_global_def
         in
      match uu____5392 with
      | FStar_Pervasives_Native.Some quals -> quals
      | uu____5414 -> []
  
let (try_lookup_module :
  env ->
    FStar_Ident.path ->
      FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun path  ->
      let uu____5431 =
        FStar_List.tryFind
          (fun uu____5446  ->
             match uu____5446 with
             | (mlid,modul) ->
                 let uu____5453 = FStar_Ident.path_of_lid mlid  in
                 uu____5453 = path) env.modules
         in
      match uu____5431 with
      | FStar_Pervasives_Native.Some (uu____5456,modul) ->
          FStar_Pervasives_Native.Some modul
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (try_lookup_let :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___101_5494 =
        match uu___101_5494 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               ((uu____5501,lbs),uu____5503);
             FStar_Syntax_Syntax.sigrng = uu____5504;
             FStar_Syntax_Syntax.sigquals = uu____5505;
             FStar_Syntax_Syntax.sigmeta = uu____5506;
             FStar_Syntax_Syntax.sigattrs = uu____5507;_},uu____5508)
            ->
            let fv = lb_fv lbs lid1  in
            let uu____5528 =
              FStar_Syntax_Syntax.fvar lid1 fv.FStar_Syntax_Syntax.fv_delta
                fv.FStar_Syntax_Syntax.fv_qual
               in
            FStar_Pervasives_Native.Some uu____5528
        | uu____5529 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____5535  -> FStar_Pervasives_Native.None)
        (fun uu____5537  -> FStar_Pervasives_Native.None) k_global_def
  
let (try_lookup_definition :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___102_5568 =
        match uu___102_5568 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               (lbs,uu____5578);
             FStar_Syntax_Syntax.sigrng = uu____5579;
             FStar_Syntax_Syntax.sigquals = uu____5580;
             FStar_Syntax_Syntax.sigmeta = uu____5581;
             FStar_Syntax_Syntax.sigattrs = uu____5582;_},uu____5583)
            ->
            FStar_Util.find_map (FStar_Pervasives_Native.snd lbs)
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inr fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv lid1 ->
                     FStar_Pervasives_Native.Some
                       (lb.FStar_Syntax_Syntax.lbdef)
                 | uu____5606 -> FStar_Pervasives_Native.None)
        | uu____5613 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____5623  -> FStar_Pervasives_Native.None)
        (fun uu____5627  -> FStar_Pervasives_Native.None) k_global_def
  
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
          let uu____5684 = try_lookup_name any_val exclude_interface env lid
             in
          match uu____5684 with
          | FStar_Pervasives_Native.Some (Term_name (e,mut,attrs)) ->
              FStar_Pervasives_Native.Some (e, mut, attrs)
          | uu____5714 -> FStar_Pervasives_Native.None
  
let (drop_attributes :
  (FStar_Syntax_Syntax.term,Prims.bool,FStar_Syntax_Syntax.attribute
                                         Prims.list)
    FStar_Pervasives_Native.tuple3 FStar_Pervasives_Native.option ->
    (FStar_Syntax_Syntax.term,Prims.bool) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option)
  =
  fun x  ->
    match x with
    | FStar_Pervasives_Native.Some (t,mut,uu____5770) ->
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
      let uu____5845 = try_lookup_lid_with_attributes env l  in
      FStar_All.pipe_right uu____5845 drop_attributes
  
let (resolve_to_fully_qualified_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____5884 = try_lookup_lid env l  in
      match uu____5884 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (e,uu____5898) ->
          let uu____5903 =
            let uu____5904 = FStar_Syntax_Subst.compress e  in
            uu____5904.FStar_Syntax_Syntax.n  in
          (match uu____5903 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               FStar_Pervasives_Native.Some
                 ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
           | uu____5910 -> FStar_Pervasives_Native.None)
  
let (shorten_lid' : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____5921 = shorten_module_path env lid.FStar_Ident.ns true  in
      match uu____5921 with
      | (uu____5930,short) ->
          FStar_Ident.lid_of_ns_and_id short lid.FStar_Ident.ident
  
let (shorten_lid : env -> FStar_Ident.lid -> FStar_Ident.lid) =
  fun env  ->
    fun lid  ->
      match env.curmodule with
      | FStar_Pervasives_Native.None  -> shorten_lid' env lid
      | uu____5950 ->
          let lid_without_ns =
            FStar_Ident.lid_of_ns_and_id [] lid.FStar_Ident.ident  in
          let uu____5954 = resolve_to_fully_qualified_name env lid_without_ns
             in
          (match uu____5954 with
           | FStar_Pervasives_Native.Some lid' when
               lid'.FStar_Ident.str = lid.FStar_Ident.str -> lid_without_ns
           | uu____5958 -> shorten_lid' env lid)
  
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
        let uu___123_5992 = env  in
        {
          curmodule = (uu___123_5992.curmodule);
          curmonad = (uu___123_5992.curmonad);
          modules = (uu___123_5992.modules);
          scope_mods = [];
          exported_ids = empty_exported_id_smap;
          trans_exported_ids = (uu___123_5992.trans_exported_ids);
          includes = empty_include_smap;
          sigaccum = (uu___123_5992.sigaccum);
          sigmap = (uu___123_5992.sigmap);
          iface = (uu___123_5992.iface);
          admitted_iface = (uu___123_5992.admitted_iface);
          expect_typ = (uu___123_5992.expect_typ);
          docs = (uu___123_5992.docs);
          remaining_iface_decls = (uu___123_5992.remaining_iface_decls);
          syntax_only = (uu___123_5992.syntax_only);
          ds_hooks = (uu___123_5992.ds_hooks)
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
      let uu____6015 = try_lookup_lid_with_attributes_no_resolve env l  in
      FStar_All.pipe_right uu____6015 drop_attributes
  
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
      let k_global_def lid1 uu___104_6082 =
        match uu___104_6082 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____6089,uu____6090,uu____6091);
             FStar_Syntax_Syntax.sigrng = uu____6092;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____6094;
             FStar_Syntax_Syntax.sigattrs = uu____6095;_},uu____6096)
            ->
            let uu____6101 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___103_6105  ->
                      match uu___103_6105 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | uu____6106 -> false))
               in
            if uu____6101
            then
              let uu____6109 =
                FStar_Syntax_Syntax.lid_as_fv lid1
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Pervasives_Native.Some uu____6109
            else FStar_Pervasives_Native.None
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
               uu____6111;
             FStar_Syntax_Syntax.sigrng = uu____6112;
             FStar_Syntax_Syntax.sigquals = uu____6113;
             FStar_Syntax_Syntax.sigmeta = uu____6114;
             FStar_Syntax_Syntax.sigattrs = uu____6115;_},uu____6116)
            ->
            let uu____6135 =
              FStar_Syntax_Syntax.lid_as_fv lid1
                FStar_Syntax_Syntax.Delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
               in
            FStar_Pervasives_Native.Some uu____6135
        | uu____6136 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____6142  -> FStar_Pervasives_Native.None)
        (fun uu____6144  -> FStar_Pervasives_Native.None) k_global_def
  
let (find_all_datacons :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___105_6177 =
        match uu___105_6177 with
        | ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_inductive_typ
               (uu____6186,uu____6187,uu____6188,uu____6189,datas,uu____6191);
             FStar_Syntax_Syntax.sigrng = uu____6192;
             FStar_Syntax_Syntax.sigquals = uu____6193;
             FStar_Syntax_Syntax.sigmeta = uu____6194;
             FStar_Syntax_Syntax.sigattrs = uu____6195;_},uu____6196)
            -> FStar_Pervasives_Native.Some datas
        | uu____6211 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____6221  -> FStar_Pervasives_Native.None)
        (fun uu____6225  -> FStar_Pervasives_Native.None) k_global_def
  
let (record_cache_aux_with_filter :
  ((unit -> unit,unit -> unit,unit -> record_or_dc Prims.list,record_or_dc ->
                                                                unit)
     FStar_Pervasives_Native.tuple4,unit -> unit)
    FStar_Pervasives_Native.tuple2)
  =
  let record_cache = FStar_Util.mk_ref [[]]  in
  let push1 uu____6277 =
    let uu____6278 =
      let uu____6283 =
        let uu____6286 = FStar_ST.op_Bang record_cache  in
        FStar_List.hd uu____6286  in
      let uu____6346 = FStar_ST.op_Bang record_cache  in uu____6283 ::
        uu____6346
       in
    FStar_ST.op_Colon_Equals record_cache uu____6278  in
  let pop1 uu____6464 =
    let uu____6465 =
      let uu____6470 = FStar_ST.op_Bang record_cache  in
      FStar_List.tl uu____6470  in
    FStar_ST.op_Colon_Equals record_cache uu____6465  in
  let peek1 uu____6590 =
    let uu____6591 = FStar_ST.op_Bang record_cache  in
    FStar_List.hd uu____6591  in
  let insert r =
    let uu____6657 =
      let uu____6662 = let uu____6665 = peek1 ()  in r :: uu____6665  in
      let uu____6668 =
        let uu____6673 = FStar_ST.op_Bang record_cache  in
        FStar_List.tl uu____6673  in
      uu____6662 :: uu____6668  in
    FStar_ST.op_Colon_Equals record_cache uu____6657  in
  let filter1 uu____6793 =
    let rc = peek1 ()  in
    let filtered =
      FStar_List.filter
        (fun r  -> Prims.op_Negation r.is_private_or_abstract) rc
       in
    let uu____6802 =
      let uu____6807 =
        let uu____6812 = FStar_ST.op_Bang record_cache  in
        FStar_List.tl uu____6812  in
      filtered :: uu____6807  in
    FStar_ST.op_Colon_Equals record_cache uu____6802  in
  let aux = (push1, pop1, peek1, insert)  in (aux, filter1) 
let (record_cache_aux :
  (unit -> unit,unit -> unit,unit -> record_or_dc Prims.list,record_or_dc ->
                                                               unit)
    FStar_Pervasives_Native.tuple4)
  =
  let uu____7011 = record_cache_aux_with_filter  in
  match uu____7011 with | (aux,uu____7064) -> aux 
let (filter_record_cache : unit -> unit) =
  let uu____7119 = record_cache_aux_with_filter  in
  match uu____7119 with | (uu____7152,filter1) -> filter1 
let (push_record_cache : unit -> unit) =
  let uu____7208 = record_cache_aux  in
  match uu____7208 with | (push1,uu____7235,uu____7236,uu____7237) -> push1 
let (pop_record_cache : unit -> unit) =
  let uu____7270 = record_cache_aux  in
  match uu____7270 with | (uu____7296,pop1,uu____7298,uu____7299) -> pop1 
let (peek_record_cache : unit -> record_or_dc Prims.list) =
  let uu____7334 = record_cache_aux  in
  match uu____7334 with | (uu____7362,uu____7363,peek1,uu____7365) -> peek1 
let (insert_record_cache : record_or_dc -> unit) =
  let uu____7398 = record_cache_aux  in
  match uu____7398 with | (uu____7424,uu____7425,uu____7426,insert) -> insert 
let (extract_record :
  env ->
    scope_mod Prims.list FStar_ST.ref -> FStar_Syntax_Syntax.sigelt -> unit)
  =
  fun e  ->
    fun new_globs  ->
      fun se  ->
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_bundle (sigs,uu____7502) ->
            let is_record =
              FStar_Util.for_some
                (fun uu___106_7520  ->
                   match uu___106_7520 with
                   | FStar_Syntax_Syntax.RecordType uu____7521 -> true
                   | FStar_Syntax_Syntax.RecordConstructor uu____7530 -> true
                   | uu____7539 -> false)
               in
            let find_dc dc =
              FStar_All.pipe_right sigs
                (FStar_Util.find_opt
                   (fun uu___107_7563  ->
                      match uu___107_7563 with
                      | {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_datacon
                            (lid,uu____7565,uu____7566,uu____7567,uu____7568,uu____7569);
                          FStar_Syntax_Syntax.sigrng = uu____7570;
                          FStar_Syntax_Syntax.sigquals = uu____7571;
                          FStar_Syntax_Syntax.sigmeta = uu____7572;
                          FStar_Syntax_Syntax.sigattrs = uu____7573;_} ->
                          FStar_Ident.lid_equals dc lid
                      | uu____7582 -> false))
               in
            FStar_All.pipe_right sigs
              (FStar_List.iter
                 (fun uu___108_7617  ->
                    match uu___108_7617 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ
                          (typename,univs1,parms,uu____7621,uu____7622,dc::[]);
                        FStar_Syntax_Syntax.sigrng = uu____7624;
                        FStar_Syntax_Syntax.sigquals = typename_quals;
                        FStar_Syntax_Syntax.sigmeta = uu____7626;
                        FStar_Syntax_Syntax.sigattrs = uu____7627;_} ->
                        let uu____7638 =
                          let uu____7639 = find_dc dc  in
                          FStar_All.pipe_left FStar_Util.must uu____7639  in
                        (match uu____7638 with
                         | {
                             FStar_Syntax_Syntax.sigel =
                               FStar_Syntax_Syntax.Sig_datacon
                               (constrname,uu____7645,t,uu____7647,uu____7648,uu____7649);
                             FStar_Syntax_Syntax.sigrng = uu____7650;
                             FStar_Syntax_Syntax.sigquals = uu____7651;
                             FStar_Syntax_Syntax.sigmeta = uu____7652;
                             FStar_Syntax_Syntax.sigattrs = uu____7653;_} ->
                             let uu____7662 =
                               FStar_Syntax_Util.arrow_formals t  in
                             (match uu____7662 with
                              | (formals,uu____7676) ->
                                  let is_rec = is_record typename_quals  in
                                  let formals' =
                                    FStar_All.pipe_right formals
                                      (FStar_List.collect
                                         (fun uu____7725  ->
                                            match uu____7725 with
                                            | (x,q) ->
                                                let uu____7738 =
                                                  (FStar_Syntax_Syntax.is_null_bv
                                                     x)
                                                    ||
                                                    (is_rec &&
                                                       (FStar_Syntax_Syntax.is_implicit
                                                          q))
                                                   in
                                                if uu____7738
                                                then []
                                                else [(x, q)]))
                                     in
                                  let fields' =
                                    FStar_All.pipe_right formals'
                                      (FStar_List.map
                                         (fun uu____7795  ->
                                            match uu____7795 with
                                            | (x,q) ->
                                                let uu____7808 =
                                                  if is_rec
                                                  then
                                                    FStar_Syntax_Util.unmangle_field_name
                                                      x.FStar_Syntax_Syntax.ppname
                                                  else
                                                    x.FStar_Syntax_Syntax.ppname
                                                   in
                                                (uu____7808,
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
                                  ((let uu____7823 =
                                      let uu____7826 =
                                        FStar_ST.op_Bang new_globs  in
                                      (Record_or_dc record) :: uu____7826  in
                                    FStar_ST.op_Colon_Equals new_globs
                                      uu____7823);
                                   (match () with
                                    | () ->
                                        ((let add_field uu____7939 =
                                            match uu____7939 with
                                            | (id1,uu____7947) ->
                                                let modul =
                                                  let uu____7953 =
                                                    FStar_Ident.lid_of_ids
                                                      constrname.FStar_Ident.ns
                                                     in
                                                  uu____7953.FStar_Ident.str
                                                   in
                                                let uu____7954 =
                                                  get_exported_id_set e modul
                                                   in
                                                (match uu____7954 with
                                                 | FStar_Pervasives_Native.Some
                                                     my_ex ->
                                                     let my_exported_ids =
                                                       my_ex
                                                         Exported_id_field
                                                        in
                                                     ((let uu____7988 =
                                                         let uu____7989 =
                                                           FStar_ST.op_Bang
                                                             my_exported_ids
                                                            in
                                                         FStar_Util.set_add
                                                           id1.FStar_Ident.idText
                                                           uu____7989
                                                          in
                                                       FStar_ST.op_Colon_Equals
                                                         my_exported_ids
                                                         uu____7988);
                                                      (match () with
                                                       | () ->
                                                           let projname =
                                                             let uu____8083 =
                                                               let uu____8084
                                                                 =
                                                                 FStar_Syntax_Util.mk_field_projector_name_from_ident
                                                                   constrname
                                                                   id1
                                                                  in
                                                               uu____8084.FStar_Ident.ident
                                                                in
                                                             uu____8083.FStar_Ident.idText
                                                              in
                                                           let uu____8086 =
                                                             let uu____8087 =
                                                               FStar_ST.op_Bang
                                                                 my_exported_ids
                                                                in
                                                             FStar_Util.set_add
                                                               projname
                                                               uu____8087
                                                              in
                                                           FStar_ST.op_Colon_Equals
                                                             my_exported_ids
                                                             uu____8086))
                                                 | FStar_Pervasives_Native.None
                                                      -> ())
                                             in
                                          FStar_List.iter add_field fields');
                                         (match () with
                                          | () -> insert_record_cache record)))))
                         | uu____8191 -> ())
                    | uu____8192 -> ()))
        | uu____8193 -> ()
  
let (try_lookup_record_or_dc_by_field_name :
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option) =
  fun env  ->
    fun fieldname  ->
      let find_in_cache fieldname1 =
        let uu____8214 =
          ((fieldname1.FStar_Ident.ns), (fieldname1.FStar_Ident.ident))  in
        match uu____8214 with
        | (ns,id1) ->
            let uu____8231 = peek_record_cache ()  in
            FStar_Util.find_map uu____8231
              (fun record  ->
                 let uu____8237 =
                   find_in_record ns id1 record (fun r  -> Cont_ok r)  in
                 option_of_cont
                   (fun uu____8243  -> FStar_Pervasives_Native.None)
                   uu____8237)
         in
      resolve_in_open_namespaces'' env fieldname Exported_id_field
        (fun uu____8245  -> Cont_ignore) (fun uu____8247  -> Cont_ignore)
        (fun r  -> Cont_ok r)
        (fun fn  ->
           let uu____8253 = find_in_cache fn  in
           cont_of_option Cont_ignore uu____8253)
        (fun k  -> fun uu____8259  -> k)
  
let (try_lookup_record_by_field_name :
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option) =
  fun env  ->
    fun fieldname  ->
      let uu____8274 = try_lookup_record_or_dc_by_field_name env fieldname
         in
      match uu____8274 with
      | FStar_Pervasives_Native.Some r when r.is_record ->
          FStar_Pervasives_Native.Some r
      | uu____8280 -> FStar_Pervasives_Native.None
  
let (belongs_to_record :
  env -> FStar_Ident.lident -> record_or_dc -> Prims.bool) =
  fun env  ->
    fun lid  ->
      fun record  ->
        let uu____8298 = try_lookup_record_by_field_name env lid  in
        match uu____8298 with
        | FStar_Pervasives_Native.Some record' when
            let uu____8302 =
              let uu____8303 =
                FStar_Ident.path_of_ns (record.typename).FStar_Ident.ns  in
              FStar_Ident.text_of_path uu____8303  in
            let uu____8304 =
              let uu____8305 =
                FStar_Ident.path_of_ns (record'.typename).FStar_Ident.ns  in
              FStar_Ident.text_of_path uu____8305  in
            uu____8302 = uu____8304 ->
            let uu____8306 =
              find_in_record (record.typename).FStar_Ident.ns
                lid.FStar_Ident.ident record (fun uu____8310  -> Cont_ok ())
               in
            (match uu____8306 with
             | Cont_ok uu____8311 -> true
             | uu____8312 -> false)
        | uu____8315 -> false
  
let (try_lookup_dc_by_field_name :
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident,Prims.bool) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun fieldname  ->
      let uu____8334 = try_lookup_record_or_dc_by_field_name env fieldname
         in
      match uu____8334 with
      | FStar_Pervasives_Native.Some r ->
          let uu____8344 =
            let uu____8349 =
              let uu____8350 =
                FStar_Ident.lid_of_ids
                  (FStar_List.append (r.typename).FStar_Ident.ns
                     [r.constrname])
                 in
              let uu____8351 = FStar_Ident.range_of_lid fieldname  in
              FStar_Ident.set_lid_range uu____8350 uu____8351  in
            (uu____8349, (r.is_record))  in
          FStar_Pervasives_Native.Some uu____8344
      | uu____8356 -> FStar_Pervasives_Native.None
  
let (string_set_ref_new : unit -> Prims.string FStar_Util.set FStar_ST.ref) =
  fun uu____8382  ->
    let uu____8383 = FStar_Util.new_set FStar_Util.compare  in
    FStar_Util.mk_ref uu____8383
  
let (exported_id_set_new :
  unit -> exported_id_kind -> Prims.string FStar_Util.set FStar_ST.ref) =
  fun uu____8410  ->
    let term_type_set = string_set_ref_new ()  in
    let field_set = string_set_ref_new ()  in
    fun uu___109_8421  ->
      match uu___109_8421 with
      | Exported_id_term_type  -> term_type_set
      | Exported_id_field  -> field_set
  
let (unique :
  Prims.bool -> Prims.bool -> env -> FStar_Ident.lident -> Prims.bool) =
  fun any_val  ->
    fun exclude_interface  ->
      fun env  ->
        fun lid  ->
          let filter_scope_mods uu___110_8473 =
            match uu___110_8473 with
            | Rec_binding uu____8474 -> true
            | uu____8475 -> false  in
          let this_env =
            let uu___124_8477 = env  in
            let uu____8478 =
              FStar_List.filter filter_scope_mods env.scope_mods  in
            {
              curmodule = (uu___124_8477.curmodule);
              curmonad = (uu___124_8477.curmonad);
              modules = (uu___124_8477.modules);
              scope_mods = uu____8478;
              exported_ids = empty_exported_id_smap;
              trans_exported_ids = (uu___124_8477.trans_exported_ids);
              includes = empty_include_smap;
              sigaccum = (uu___124_8477.sigaccum);
              sigmap = (uu___124_8477.sigmap);
              iface = (uu___124_8477.iface);
              admitted_iface = (uu___124_8477.admitted_iface);
              expect_typ = (uu___124_8477.expect_typ);
              docs = (uu___124_8477.docs);
              remaining_iface_decls = (uu___124_8477.remaining_iface_decls);
              syntax_only = (uu___124_8477.syntax_only);
              ds_hooks = (uu___124_8477.ds_hooks)
            }  in
          let uu____8481 =
            try_lookup_lid' any_val exclude_interface this_env lid  in
          match uu____8481 with
          | FStar_Pervasives_Native.None  -> true
          | FStar_Pervasives_Native.Some uu____8500 -> false
  
let (push_scope_mod : env -> scope_mod -> env) =
  fun env  ->
    fun scope_mod  ->
      let uu___125_8527 = env  in
      {
        curmodule = (uu___125_8527.curmodule);
        curmonad = (uu___125_8527.curmonad);
        modules = (uu___125_8527.modules);
        scope_mods = (scope_mod :: (env.scope_mods));
        exported_ids = (uu___125_8527.exported_ids);
        trans_exported_ids = (uu___125_8527.trans_exported_ids);
        includes = (uu___125_8527.includes);
        sigaccum = (uu___125_8527.sigaccum);
        sigmap = (uu___125_8527.sigmap);
        iface = (uu___125_8527.iface);
        admitted_iface = (uu___125_8527.admitted_iface);
        expect_typ = (uu___125_8527.expect_typ);
        docs = (uu___125_8527.docs);
        remaining_iface_decls = (uu___125_8527.remaining_iface_decls);
        syntax_only = (uu___125_8527.syntax_only);
        ds_hooks = (uu___125_8527.ds_hooks)
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
        let uu____8592 =
          (unique false true env l) || (FStar_Options.interactive ())  in
        if uu____8592
        then push_scope_mod env (Rec_binding (x, l, dd))
        else
          (let uu____8594 = FStar_Ident.range_of_lid l  in
           FStar_Errors.raise_error
             (FStar_Errors.Fatal_DuplicateTopLevelNames,
               (Prims.strcat "Duplicate top-level names " l.FStar_Ident.str))
             uu____8594)
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let err l =
        let sopt = FStar_Util.smap_try_find (sigmap env) l.FStar_Ident.str
           in
        let r =
          match sopt with
          | FStar_Pervasives_Native.Some (se,uu____8624) ->
              let uu____8629 =
                FStar_Util.find_opt (FStar_Ident.lid_equals l)
                  (FStar_Syntax_Util.lids_of_sigelt se)
                 in
              (match uu____8629 with
               | FStar_Pervasives_Native.Some l1 ->
                   let uu____8633 = FStar_Ident.range_of_lid l1  in
                   FStar_All.pipe_left FStar_Range.string_of_range uu____8633
               | FStar_Pervasives_Native.None  -> "<unknown>")
          | FStar_Pervasives_Native.None  -> "<unknown>"  in
        let uu____8638 =
          let uu____8643 =
            let uu____8644 = FStar_Ident.text_of_lid l  in
            FStar_Util.format2
              "Duplicate top-level names [%s]; previously declared at %s"
              uu____8644 r
             in
          (FStar_Errors.Fatal_DuplicateTopLevelNames, uu____8643)  in
        let uu____8645 = FStar_Ident.range_of_lid l  in
        FStar_Errors.raise_error uu____8638 uu____8645  in
      let globals = FStar_Util.mk_ref env.scope_mods  in
      let env1 =
        let uu____8654 =
          match s.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let uu____8663 -> (false, true)
          | FStar_Syntax_Syntax.Sig_bundle uu____8670 -> (false, true)
          | uu____8679 -> (false, false)  in
        match uu____8654 with
        | (any_val,exclude_interface) ->
            let lids = FStar_Syntax_Util.lids_of_sigelt s  in
            let uu____8685 =
              FStar_Util.find_map lids
                (fun l  ->
                   let uu____8691 =
                     let uu____8692 = unique any_val exclude_interface env l
                        in
                     Prims.op_Negation uu____8692  in
                   if uu____8691
                   then FStar_Pervasives_Native.Some l
                   else FStar_Pervasives_Native.None)
               in
            (match uu____8685 with
             | FStar_Pervasives_Native.Some l -> err l
             | uu____8697 ->
                 (extract_record env globals s;
                  (let uu___126_8723 = env  in
                   {
                     curmodule = (uu___126_8723.curmodule);
                     curmonad = (uu___126_8723.curmonad);
                     modules = (uu___126_8723.modules);
                     scope_mods = (uu___126_8723.scope_mods);
                     exported_ids = (uu___126_8723.exported_ids);
                     trans_exported_ids = (uu___126_8723.trans_exported_ids);
                     includes = (uu___126_8723.includes);
                     sigaccum = (s :: (env.sigaccum));
                     sigmap = (uu___126_8723.sigmap);
                     iface = (uu___126_8723.iface);
                     admitted_iface = (uu___126_8723.admitted_iface);
                     expect_typ = (uu___126_8723.expect_typ);
                     docs = (uu___126_8723.docs);
                     remaining_iface_decls =
                       (uu___126_8723.remaining_iface_decls);
                     syntax_only = (uu___126_8723.syntax_only);
                     ds_hooks = (uu___126_8723.ds_hooks)
                   })))
         in
      let env2 =
        let uu___127_8725 = env1  in
        let uu____8726 = FStar_ST.op_Bang globals  in
        {
          curmodule = (uu___127_8725.curmodule);
          curmonad = (uu___127_8725.curmonad);
          modules = (uu___127_8725.modules);
          scope_mods = uu____8726;
          exported_ids = (uu___127_8725.exported_ids);
          trans_exported_ids = (uu___127_8725.trans_exported_ids);
          includes = (uu___127_8725.includes);
          sigaccum = (uu___127_8725.sigaccum);
          sigmap = (uu___127_8725.sigmap);
          iface = (uu___127_8725.iface);
          admitted_iface = (uu___127_8725.admitted_iface);
          expect_typ = (uu___127_8725.expect_typ);
          docs = (uu___127_8725.docs);
          remaining_iface_decls = (uu___127_8725.remaining_iface_decls);
          syntax_only = (uu___127_8725.syntax_only);
          ds_hooks = (uu___127_8725.ds_hooks)
        }  in
      let uu____8778 =
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_bundle (ses,uu____8804) ->
            let uu____8813 =
              FStar_List.map
                (fun se  -> ((FStar_Syntax_Util.lids_of_sigelt se), se)) ses
               in
            (env2, uu____8813)
        | uu____8840 -> (env2, [((FStar_Syntax_Util.lids_of_sigelt s), s)])
         in
      match uu____8778 with
      | (env3,lss) ->
          (FStar_All.pipe_right lss
             (FStar_List.iter
                (fun uu____8899  ->
                   match uu____8899 with
                   | (lids,se) ->
                       FStar_All.pipe_right lids
                         (FStar_List.iter
                            (fun lid  ->
                               (let uu____8921 =
                                  let uu____8924 = FStar_ST.op_Bang globals
                                     in
                                  (Top_level_def (lid.FStar_Ident.ident)) ::
                                    uu____8924
                                   in
                                FStar_ST.op_Colon_Equals globals uu____8921);
                               (match () with
                                | () ->
                                    let modul =
                                      let uu____9026 =
                                        FStar_Ident.lid_of_ids
                                          lid.FStar_Ident.ns
                                         in
                                      uu____9026.FStar_Ident.str  in
                                    ((let uu____9028 =
                                        get_exported_id_set env3 modul  in
                                      match uu____9028 with
                                      | FStar_Pervasives_Native.Some f ->
                                          let my_exported_ids =
                                            f Exported_id_term_type  in
                                          let uu____9061 =
                                            let uu____9062 =
                                              FStar_ST.op_Bang
                                                my_exported_ids
                                               in
                                            FStar_Util.set_add
                                              (lid.FStar_Ident.ident).FStar_Ident.idText
                                              uu____9062
                                             in
                                          FStar_ST.op_Colon_Equals
                                            my_exported_ids uu____9061
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
              let uu___128_9166 = env3  in
              let uu____9167 = FStar_ST.op_Bang globals  in
              {
                curmodule = (uu___128_9166.curmodule);
                curmonad = (uu___128_9166.curmonad);
                modules = (uu___128_9166.modules);
                scope_mods = uu____9167;
                exported_ids = (uu___128_9166.exported_ids);
                trans_exported_ids = (uu___128_9166.trans_exported_ids);
                includes = (uu___128_9166.includes);
                sigaccum = (uu___128_9166.sigaccum);
                sigmap = (uu___128_9166.sigmap);
                iface = (uu___128_9166.iface);
                admitted_iface = (uu___128_9166.admitted_iface);
                expect_typ = (uu___128_9166.expect_typ);
                docs = (uu___128_9166.docs);
                remaining_iface_decls = (uu___128_9166.remaining_iface_decls);
                syntax_only = (uu___128_9166.syntax_only);
                ds_hooks = (uu___128_9166.ds_hooks)
              }  in
            env4))
  
let (push_namespace : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun ns  ->
      let uu____9229 =
        let uu____9234 = resolve_module_name env ns false  in
        match uu____9234 with
        | FStar_Pervasives_Native.None  ->
            let modules = env.modules  in
            let uu____9248 =
              FStar_All.pipe_right modules
                (FStar_Util.for_some
                   (fun uu____9264  ->
                      match uu____9264 with
                      | (m,uu____9270) ->
                          let uu____9271 =
                            let uu____9272 = FStar_Ident.text_of_lid m  in
                            Prims.strcat uu____9272 "."  in
                          let uu____9273 =
                            let uu____9274 = FStar_Ident.text_of_lid ns  in
                            Prims.strcat uu____9274 "."  in
                          FStar_Util.starts_with uu____9271 uu____9273))
               in
            if uu____9248
            then (ns, Open_namespace)
            else
              (let uu____9280 =
                 let uu____9285 =
                   let uu____9286 = FStar_Ident.text_of_lid ns  in
                   FStar_Util.format1 "Namespace %s cannot be found"
                     uu____9286
                    in
                 (FStar_Errors.Fatal_NameSpaceNotFound, uu____9285)  in
               let uu____9287 = FStar_Ident.range_of_lid ns  in
               FStar_Errors.raise_error uu____9280 uu____9287)
        | FStar_Pervasives_Native.Some ns' ->
            (fail_if_curmodule env ns ns'; (ns', Open_module))
         in
      match uu____9229 with
      | (ns',kd) ->
          ((env.ds_hooks).ds_push_open_hook env (ns', kd);
           push_scope_mod env (Open_module_or_namespace (ns', kd)))
  
let (push_include : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun ns  ->
      let ns0 = ns  in
      let uu____9308 = resolve_module_name env ns false  in
      match uu____9308 with
      | FStar_Pervasives_Native.Some ns1 ->
          ((env.ds_hooks).ds_push_include_hook env ns1;
           fail_if_curmodule env ns0 ns1;
           (let env1 =
              push_scope_mod env
                (Open_module_or_namespace (ns1, Open_module))
               in
            let curmod =
              let uu____9316 = current_module env1  in
              uu____9316.FStar_Ident.str  in
            (let uu____9318 = FStar_Util.smap_try_find env1.includes curmod
                in
             match uu____9318 with
             | FStar_Pervasives_Native.None  -> ()
             | FStar_Pervasives_Native.Some incl ->
                 let uu____9342 =
                   let uu____9345 = FStar_ST.op_Bang incl  in ns1 ::
                     uu____9345
                    in
                 FStar_ST.op_Colon_Equals incl uu____9342);
            (match () with
             | () ->
                 let uu____9446 =
                   get_trans_exported_id_set env1 ns1.FStar_Ident.str  in
                 (match uu____9446 with
                  | FStar_Pervasives_Native.Some ns_trans_exports ->
                      ((let uu____9466 =
                          let uu____9485 = get_exported_id_set env1 curmod
                             in
                          let uu____9493 =
                            get_trans_exported_id_set env1 curmod  in
                          (uu____9485, uu____9493)  in
                        match uu____9466 with
                        | (FStar_Pervasives_Native.Some
                           cur_exports,FStar_Pervasives_Native.Some
                           cur_trans_exports) ->
                            let update_exports k =
                              let ns_ex =
                                let uu____9558 = ns_trans_exports k  in
                                FStar_ST.op_Bang uu____9558  in
                              let ex = cur_exports k  in
                              (let uu____9692 =
                                 let uu____9693 = FStar_ST.op_Bang ex  in
                                 FStar_Util.set_difference uu____9693 ns_ex
                                  in
                               FStar_ST.op_Colon_Equals ex uu____9692);
                              (match () with
                               | () ->
                                   let trans_ex = cur_trans_exports k  in
                                   let uu____9801 =
                                     let uu____9802 =
                                       FStar_ST.op_Bang trans_ex  in
                                     FStar_Util.set_union uu____9802 ns_ex
                                      in
                                   FStar_ST.op_Colon_Equals trans_ex
                                     uu____9801)
                               in
                            FStar_List.iter update_exports
                              all_exported_id_kinds
                        | uu____9895 -> ());
                       (match () with | () -> env1))
                  | FStar_Pervasives_Native.None  ->
                      let uu____9919 =
                        let uu____9924 =
                          FStar_Util.format1
                            "include: Module %s was not prepared"
                            ns1.FStar_Ident.str
                           in
                        (FStar_Errors.Fatal_IncludeModuleNotPrepared,
                          uu____9924)
                         in
                      let uu____9925 = FStar_Ident.range_of_lid ns1  in
                      FStar_Errors.raise_error uu____9919 uu____9925))))
      | uu____9926 ->
          let uu____9929 =
            let uu____9934 =
              FStar_Util.format1 "include: Module %s cannot be found"
                ns.FStar_Ident.str
               in
            (FStar_Errors.Fatal_ModuleNotFound, uu____9934)  in
          let uu____9935 = FStar_Ident.range_of_lid ns  in
          FStar_Errors.raise_error uu____9929 uu____9935
  
let (push_module_abbrev :
  env -> FStar_Ident.ident -> FStar_Ident.lident -> env) =
  fun env  ->
    fun x  ->
      fun l  ->
        let uu____9951 = module_is_defined env l  in
        if uu____9951
        then
          (fail_if_curmodule env l l;
           (env.ds_hooks).ds_push_module_abbrev_hook env x l;
           push_scope_mod env (Module_abbrev (x, l)))
        else
          (let uu____9955 =
             let uu____9960 =
               let uu____9961 = FStar_Ident.text_of_lid l  in
               FStar_Util.format1 "Module %s cannot be found" uu____9961  in
             (FStar_Errors.Fatal_ModuleNotFound, uu____9960)  in
           let uu____9962 = FStar_Ident.range_of_lid l  in
           FStar_Errors.raise_error uu____9955 uu____9962)
  
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
            ((let uu____9984 =
                FStar_Util.smap_try_find env.docs l.FStar_Ident.str  in
              match uu____9984 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some old_doc ->
                  let uu____9988 = FStar_Ident.range_of_lid l  in
                  let uu____9989 =
                    let uu____9994 =
                      let uu____9995 = FStar_Ident.string_of_lid l  in
                      let uu____9996 =
                        FStar_Parser_AST.string_of_fsdoc old_doc  in
                      let uu____9997 = FStar_Parser_AST.string_of_fsdoc doc1
                         in
                      FStar_Util.format3
                        "Overwriting doc of %s; old doc was [%s]; new doc are [%s]"
                        uu____9995 uu____9996 uu____9997
                       in
                    (FStar_Errors.Warning_DocOverwrite, uu____9994)  in
                  FStar_Errors.log_issue uu____9988 uu____9989);
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
                      let uu____10037 =
                        FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption)
                         in
                      Prims.op_Negation uu____10037 ->
                      let uu____10040 =
                        FStar_Util.smap_try_find (sigmap env)
                          l.FStar_Ident.str
                         in
                      (match uu____10040 with
                       | FStar_Pervasives_Native.Some
                           ({
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_let uu____10053;
                              FStar_Syntax_Syntax.sigrng = uu____10054;
                              FStar_Syntax_Syntax.sigquals = uu____10055;
                              FStar_Syntax_Syntax.sigmeta = uu____10056;
                              FStar_Syntax_Syntax.sigattrs = uu____10057;_},uu____10058)
                           -> lids
                       | FStar_Pervasives_Native.Some
                           ({
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_inductive_typ
                                uu____10073;
                              FStar_Syntax_Syntax.sigrng = uu____10074;
                              FStar_Syntax_Syntax.sigquals = uu____10075;
                              FStar_Syntax_Syntax.sigmeta = uu____10076;
                              FStar_Syntax_Syntax.sigattrs = uu____10077;_},uu____10078)
                           -> lids
                       | uu____10103 ->
                           ((let uu____10111 =
                               let uu____10112 = FStar_Options.interactive ()
                                  in
                               Prims.op_Negation uu____10112  in
                             if uu____10111
                             then
                               let uu____10113 = FStar_Ident.range_of_lid l
                                  in
                               let uu____10114 =
                                 let uu____10119 =
                                   let uu____10120 =
                                     FStar_Ident.string_of_lid l  in
                                   FStar_Util.format1
                                     "Admitting %s without a definition"
                                     uu____10120
                                    in
                                 (FStar_Errors.Warning_AdmitWithoutDefinition,
                                   uu____10119)
                                  in
                               FStar_Errors.log_issue uu____10113 uu____10114
                             else ());
                            (let quals = FStar_Syntax_Syntax.Assumption ::
                               (se.FStar_Syntax_Syntax.sigquals)  in
                             FStar_Util.smap_add (sigmap env)
                               l.FStar_Ident.str
                               ((let uu___129_10131 = se  in
                                 {
                                   FStar_Syntax_Syntax.sigel =
                                     (uu___129_10131.FStar_Syntax_Syntax.sigel);
                                   FStar_Syntax_Syntax.sigrng =
                                     (uu___129_10131.FStar_Syntax_Syntax.sigrng);
                                   FStar_Syntax_Syntax.sigquals = quals;
                                   FStar_Syntax_Syntax.sigmeta =
                                     (uu___129_10131.FStar_Syntax_Syntax.sigmeta);
                                   FStar_Syntax_Syntax.sigattrs =
                                     (uu___129_10131.FStar_Syntax_Syntax.sigattrs)
                                 }), false);
                             l
                             ::
                             lids)))
                  | uu____10132 -> lids) [])
         in
      let uu___130_10133 = m  in
      let uu____10134 =
        FStar_All.pipe_right m.FStar_Syntax_Syntax.declarations
          (FStar_List.map
             (fun s  ->
                match s.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_declare_typ
                    (lid,uu____10144,uu____10145) when
                    FStar_List.existsb
                      (fun l  -> FStar_Ident.lid_equals l lid)
                      admitted_sig_lids
                    ->
                    let uu___131_10148 = s  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___131_10148.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___131_10148.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals =
                        (FStar_Syntax_Syntax.Assumption ::
                        (s.FStar_Syntax_Syntax.sigquals));
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___131_10148.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___131_10148.FStar_Syntax_Syntax.sigattrs)
                    }
                | uu____10149 -> s))
         in
      {
        FStar_Syntax_Syntax.name = (uu___130_10133.FStar_Syntax_Syntax.name);
        FStar_Syntax_Syntax.declarations = uu____10134;
        FStar_Syntax_Syntax.exports =
          (uu___130_10133.FStar_Syntax_Syntax.exports);
        FStar_Syntax_Syntax.is_interface =
          (uu___130_10133.FStar_Syntax_Syntax.is_interface)
      }
  
let (finish : env -> FStar_Syntax_Syntax.modul -> env) =
  fun env  ->
    fun modul  ->
      FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations
        (FStar_List.iter
           (fun se  ->
              let quals = se.FStar_Syntax_Syntax.sigquals  in
              match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_bundle (ses,uu____10170) ->
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
                                (lid,uu____10190,uu____10191,uu____10192,uu____10193,uu____10194)
                                ->
                                FStar_Util.smap_remove (sigmap env)
                                  lid.FStar_Ident.str
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (lid,univ_names,binders,typ,uu____10207,uu____10208)
                                ->
                                (FStar_Util.smap_remove (sigmap env)
                                   lid.FStar_Ident.str;
                                 if
                                   Prims.op_Negation
                                     (FStar_List.contains
                                        FStar_Syntax_Syntax.Private quals)
                                 then
                                   (let sigel =
                                      let uu____10223 =
                                        let uu____10230 =
                                          let uu____10233 =
                                            FStar_Ident.range_of_lid lid  in
                                          let uu____10234 =
                                            let uu____10241 =
                                              let uu____10242 =
                                                let uu____10255 =
                                                  FStar_Syntax_Syntax.mk_Total
                                                    typ
                                                   in
                                                (binders, uu____10255)  in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____10242
                                               in
                                            FStar_Syntax_Syntax.mk
                                              uu____10241
                                             in
                                          uu____10234
                                            FStar_Pervasives_Native.None
                                            uu____10233
                                           in
                                        (lid, univ_names, uu____10230)  in
                                      FStar_Syntax_Syntax.Sig_declare_typ
                                        uu____10223
                                       in
                                    let se2 =
                                      let uu___132_10262 = se1  in
                                      {
                                        FStar_Syntax_Syntax.sigel = sigel;
                                        FStar_Syntax_Syntax.sigrng =
                                          (uu___132_10262.FStar_Syntax_Syntax.sigrng);
                                        FStar_Syntax_Syntax.sigquals =
                                          (FStar_Syntax_Syntax.Assumption ::
                                          quals);
                                        FStar_Syntax_Syntax.sigmeta =
                                          (uu___132_10262.FStar_Syntax_Syntax.sigmeta);
                                        FStar_Syntax_Syntax.sigattrs =
                                          (uu___132_10262.FStar_Syntax_Syntax.sigattrs)
                                      }  in
                                    FStar_Util.smap_add (sigmap env)
                                      lid.FStar_Ident.str (se2, false))
                                 else ())
                            | uu____10268 -> ()))
                  else ()
              | FStar_Syntax_Syntax.Sig_declare_typ
                  (lid,uu____10271,uu____10272) ->
                  if FStar_List.contains FStar_Syntax_Syntax.Private quals
                  then
                    FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str
                  else ()
              | FStar_Syntax_Syntax.Sig_let ((uu____10278,lbs),uu____10280)
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
                             let uu____10301 =
                               let uu____10302 =
                                 let uu____10303 =
                                   let uu____10306 =
                                     FStar_Util.right
                                       lb.FStar_Syntax_Syntax.lbname
                                      in
                                   uu____10306.FStar_Syntax_Syntax.fv_name
                                    in
                                 uu____10303.FStar_Syntax_Syntax.v  in
                               uu____10302.FStar_Ident.str  in
                             FStar_Util.smap_remove (sigmap env) uu____10301))
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
                               let uu____10320 =
                                 let uu____10323 =
                                   FStar_Util.right
                                     lb.FStar_Syntax_Syntax.lbname
                                    in
                                 uu____10323.FStar_Syntax_Syntax.fv_name  in
                               uu____10320.FStar_Syntax_Syntax.v  in
                             let quals1 = FStar_Syntax_Syntax.Assumption ::
                               quals  in
                             let decl =
                               let uu___133_10328 = se  in
                               {
                                 FStar_Syntax_Syntax.sigel =
                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                      (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                        (lb.FStar_Syntax_Syntax.lbtyp)));
                                 FStar_Syntax_Syntax.sigrng =
                                   (uu___133_10328.FStar_Syntax_Syntax.sigrng);
                                 FStar_Syntax_Syntax.sigquals = quals1;
                                 FStar_Syntax_Syntax.sigmeta =
                                   (uu___133_10328.FStar_Syntax_Syntax.sigmeta);
                                 FStar_Syntax_Syntax.sigattrs =
                                   (uu___133_10328.FStar_Syntax_Syntax.sigattrs)
                               }  in
                             FStar_Util.smap_add (sigmap env)
                               lid.FStar_Ident.str (decl, false)))
                   else ())
              | uu____10338 -> ()));
      (let curmod =
         let uu____10340 = current_module env  in uu____10340.FStar_Ident.str
          in
       (let uu____10342 =
          let uu____10361 = get_exported_id_set env curmod  in
          let uu____10369 = get_trans_exported_id_set env curmod  in
          (uu____10361, uu____10369)  in
        match uu____10342 with
        | (FStar_Pervasives_Native.Some cur_ex,FStar_Pervasives_Native.Some
           cur_trans_ex) ->
            let update_exports eikind =
              let cur_ex_set =
                let uu____10434 = cur_ex eikind  in
                FStar_ST.op_Bang uu____10434  in
              let cur_trans_ex_set_ref = cur_trans_ex eikind  in
              let uu____10567 =
                let uu____10568 = FStar_ST.op_Bang cur_trans_ex_set_ref  in
                FStar_Util.set_union cur_ex_set uu____10568  in
              FStar_ST.op_Colon_Equals cur_trans_ex_set_ref uu____10567  in
            FStar_List.iter update_exports all_exported_id_kinds
        | uu____10661 -> ());
       (match () with
        | () ->
            (filter_record_cache ();
             (match () with
              | () ->
                  let uu___134_10681 = env  in
                  {
                    curmodule = FStar_Pervasives_Native.None;
                    curmonad = (uu___134_10681.curmonad);
                    modules = (((modul.FStar_Syntax_Syntax.name), modul) ::
                      (env.modules));
                    scope_mods = [];
                    exported_ids = (uu___134_10681.exported_ids);
                    trans_exported_ids = (uu___134_10681.trans_exported_ids);
                    includes = (uu___134_10681.includes);
                    sigaccum = [];
                    sigmap = (uu___134_10681.sigmap);
                    iface = (uu___134_10681.iface);
                    admitted_iface = (uu___134_10681.admitted_iface);
                    expect_typ = (uu___134_10681.expect_typ);
                    docs = (uu___134_10681.docs);
                    remaining_iface_decls =
                      (uu___134_10681.remaining_iface_decls);
                    syntax_only = (uu___134_10681.syntax_only);
                    ds_hooks = (uu___134_10681.ds_hooks)
                  }))))
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push : env -> env) =
  fun env  ->
    push_record_cache ();
    (let uu____10710 =
       let uu____10713 = FStar_ST.op_Bang stack  in env :: uu____10713  in
     FStar_ST.op_Colon_Equals stack uu____10710);
    (let uu___135_10770 = env  in
     let uu____10771 = FStar_Util.smap_copy (sigmap env)  in
     let uu____10782 = FStar_Util.smap_copy env.docs  in
     {
       curmodule = (uu___135_10770.curmodule);
       curmonad = (uu___135_10770.curmonad);
       modules = (uu___135_10770.modules);
       scope_mods = (uu___135_10770.scope_mods);
       exported_ids = (uu___135_10770.exported_ids);
       trans_exported_ids = (uu___135_10770.trans_exported_ids);
       includes = (uu___135_10770.includes);
       sigaccum = (uu___135_10770.sigaccum);
       sigmap = uu____10771;
       iface = (uu___135_10770.iface);
       admitted_iface = (uu___135_10770.admitted_iface);
       expect_typ = (uu___135_10770.expect_typ);
       docs = uu____10782;
       remaining_iface_decls = (uu___135_10770.remaining_iface_decls);
       syntax_only = (uu___135_10770.syntax_only);
       ds_hooks = (uu___135_10770.ds_hooks)
     })
  
let (pop : unit -> env) =
  fun uu____10789  ->
    let uu____10790 = FStar_ST.op_Bang stack  in
    match uu____10790 with
    | env::tl1 ->
        (pop_record_cache (); FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____10853 -> failwith "Impossible: Too many pops"
  
let (export_interface : FStar_Ident.lident -> env -> env) =
  fun m  ->
    fun env  ->
      let sigelt_in_m se =
        match FStar_Syntax_Util.lids_of_sigelt se with
        | l::uu____10873 -> l.FStar_Ident.nsstr = m.FStar_Ident.str
        | uu____10876 -> false  in
      let sm = sigmap env  in
      let env1 = pop ()  in
      let keys = FStar_Util.smap_keys sm  in
      let sm' = sigmap env1  in
      FStar_All.pipe_right keys
        (FStar_List.iter
           (fun k  ->
              let uu____10910 = FStar_Util.smap_try_find sm' k  in
              match uu____10910 with
              | FStar_Pervasives_Native.Some (se,true ) when sigelt_in_m se
                  ->
                  (FStar_Util.smap_remove sm' k;
                   (let se1 =
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t) ->
                          let uu___136_10935 = se  in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (uu___136_10935.FStar_Syntax_Syntax.sigel);
                            FStar_Syntax_Syntax.sigrng =
                              (uu___136_10935.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (FStar_Syntax_Syntax.Assumption ::
                              (se.FStar_Syntax_Syntax.sigquals));
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___136_10935.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___136_10935.FStar_Syntax_Syntax.sigattrs)
                          }
                      | uu____10936 -> se  in
                    FStar_Util.smap_add sm' k (se1, false)))
              | uu____10941 -> ()));
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
      let uu____10964 = finish env modul1  in (uu____10964, modul1)
  
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
      let uu____11052 =
        let uu____11055 = e Exported_id_term_type  in
        FStar_ST.op_Bang uu____11055  in
      FStar_Util.set_elements uu____11052  in
    let fields =
      let uu____11177 =
        let uu____11180 = e Exported_id_field  in
        FStar_ST.op_Bang uu____11180  in
      FStar_Util.set_elements uu____11177  in
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
          let uu____11339 =
            FStar_Util.as_set e1.exported_id_terms FStar_Util.compare  in
          FStar_Util.mk_ref uu____11339  in
        let fields =
          let uu____11349 =
            FStar_Util.as_set e1.exported_id_fields FStar_Util.compare  in
          FStar_Util.mk_ref uu____11349  in
        (fun uu___111_11354  ->
           match uu___111_11354 with
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
  'Auu____11485 .
    'Auu____11485 Prims.list FStar_Pervasives_Native.option ->
      'Auu____11485 Prims.list FStar_ST.ref
  =
  fun uu___112_11498  ->
    match uu___112_11498 with
    | FStar_Pervasives_Native.None  -> FStar_Util.mk_ref []
    | FStar_Pervasives_Native.Some l -> FStar_Util.mk_ref l
  
let (inclusion_info : env -> FStar_Ident.lident -> module_inclusion_info) =
  fun env  ->
    fun l  ->
      let mname = FStar_Ident.string_of_lid l  in
      let as_ids_opt m =
        let uu____11539 = FStar_Util.smap_try_find m mname  in
        FStar_Util.map_opt uu____11539 as_exported_ids  in
      let uu____11545 = as_ids_opt env.exported_ids  in
      let uu____11548 = as_ids_opt env.trans_exported_ids  in
      let uu____11551 =
        let uu____11556 = FStar_Util.smap_try_find env.includes mname  in
        FStar_Util.map_opt uu____11556 (fun r  -> FStar_ST.op_Bang r)  in
      {
        mii_exported_ids = uu____11545;
        mii_trans_exported_ids = uu____11548;
        mii_includes = uu____11551
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
                let uu____11675 = FStar_Ident.text_of_lid mname  in
                FStar_Util.strcat uu____11675 ".fst"  in
              let auto_open =
                FStar_Parser_Dep.hard_coded_dependencies filename  in
              let auto_open1 =
                let convert_kind uu___113_11695 =
                  match uu___113_11695 with
                  | FStar_Parser_Dep.Open_namespace  -> Open_namespace
                  | FStar_Parser_Dep.Open_module  -> Open_module  in
                FStar_List.map
                  (fun uu____11707  ->
                     match uu____11707 with
                     | (lid,kind) -> (lid, (convert_kind kind))) auto_open
                 in
              let namespace_of_module =
                if
                  (FStar_List.length mname.FStar_Ident.ns) >
                    (Prims.parse_int "0")
                then
                  let uu____11731 =
                    let uu____11736 =
                      FStar_Ident.lid_of_ids mname.FStar_Ident.ns  in
                    (uu____11736, Open_namespace)  in
                  [uu____11731]
                else []  in
              let auto_open2 =
                FStar_List.append namespace_of_module
                  (FStar_List.rev auto_open1)
                 in
              (let uu____11766 = as_exported_id_set mii.mii_exported_ids  in
               FStar_Util.smap_add env1.exported_ids mname.FStar_Ident.str
                 uu____11766);
              (match () with
               | () ->
                   ((let uu____11793 =
                       as_exported_id_set mii.mii_trans_exported_ids  in
                     FStar_Util.smap_add env1.trans_exported_ids
                       mname.FStar_Ident.str uu____11793);
                    (match () with
                     | () ->
                         ((let uu____11820 = as_includes mii.mii_includes  in
                           FStar_Util.smap_add env1.includes
                             mname.FStar_Ident.str uu____11820);
                          (match () with
                           | () ->
                               let env' =
                                 let uu___137_11852 = env1  in
                                 let uu____11853 =
                                   FStar_List.map
                                     (fun x  -> Open_module_or_namespace x)
                                     auto_open2
                                    in
                                 {
                                   curmodule =
                                     (FStar_Pervasives_Native.Some mname);
                                   curmonad = (uu___137_11852.curmonad);
                                   modules = (uu___137_11852.modules);
                                   scope_mods = uu____11853;
                                   exported_ids =
                                     (uu___137_11852.exported_ids);
                                   trans_exported_ids =
                                     (uu___137_11852.trans_exported_ids);
                                   includes = (uu___137_11852.includes);
                                   sigaccum = (uu___137_11852.sigaccum);
                                   sigmap = (env1.sigmap);
                                   iface = intf;
                                   admitted_iface = admitted;
                                   expect_typ = (uu___137_11852.expect_typ);
                                   docs = (uu___137_11852.docs);
                                   remaining_iface_decls =
                                     (uu___137_11852.remaining_iface_decls);
                                   syntax_only = (uu___137_11852.syntax_only);
                                   ds_hooks = (uu___137_11852.ds_hooks)
                                 }  in
                               (FStar_List.iter
                                  (fun op  ->
                                     (env1.ds_hooks).ds_push_open_hook env'
                                       op) (FStar_List.rev auto_open2);
                                env'))))))
               in
            let uu____11865 =
              FStar_All.pipe_right env.modules
                (FStar_Util.find_opt
                   (fun uu____11891  ->
                      match uu____11891 with
                      | (l,uu____11897) -> FStar_Ident.lid_equals l mname))
               in
            match uu____11865 with
            | FStar_Pervasives_Native.None  ->
                let uu____11906 = prep env  in (uu____11906, false)
            | FStar_Pervasives_Native.Some (uu____11907,m) ->
                ((let uu____11914 =
                    (let uu____11917 = FStar_Options.interactive ()  in
                     Prims.op_Negation uu____11917) &&
                      ((Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)
                         || intf)
                     in
                  if uu____11914
                  then
                    let uu____11918 =
                      let uu____11923 =
                        FStar_Util.format1
                          "Duplicate module or interface name: %s"
                          mname.FStar_Ident.str
                         in
                      (FStar_Errors.Fatal_DuplicateModuleOrInterface,
                        uu____11923)
                       in
                    let uu____11924 = FStar_Ident.range_of_lid mname  in
                    FStar_Errors.raise_error uu____11918 uu____11924
                  else ());
                 (let uu____11926 =
                    let uu____11927 = push env  in prep uu____11927  in
                  (uu____11926, true)))
  
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
          let uu___138_11939 = env  in
          {
            curmodule = (uu___138_11939.curmodule);
            curmonad = (FStar_Pervasives_Native.Some mname);
            modules = (uu___138_11939.modules);
            scope_mods = (uu___138_11939.scope_mods);
            exported_ids = (uu___138_11939.exported_ids);
            trans_exported_ids = (uu___138_11939.trans_exported_ids);
            includes = (uu___138_11939.includes);
            sigaccum = (uu___138_11939.sigaccum);
            sigmap = (uu___138_11939.sigmap);
            iface = (uu___138_11939.iface);
            admitted_iface = (uu___138_11939.admitted_iface);
            expect_typ = (uu___138_11939.expect_typ);
            docs = (uu___138_11939.docs);
            remaining_iface_decls = (uu___138_11939.remaining_iface_decls);
            syntax_only = (uu___138_11939.syntax_only);
            ds_hooks = (uu___138_11939.ds_hooks)
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
        let uu____11973 = lookup1 lid  in
        match uu____11973 with
        | FStar_Pervasives_Native.None  ->
            let opened_modules =
              FStar_List.map
                (fun uu____11986  ->
                   match uu____11986 with
                   | (lid1,uu____11992) -> FStar_Ident.text_of_lid lid1)
                env.modules
               in
            let msg =
              let uu____11994 = FStar_Ident.text_of_lid lid  in
              FStar_Util.format1 "Identifier not found: [%s]" uu____11994  in
            let msg1 =
              if
                (FStar_List.length lid.FStar_Ident.ns) =
                  (Prims.parse_int "0")
              then msg
              else
                (let modul =
                   let uu____11998 =
                     FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
                   let uu____11999 = FStar_Ident.range_of_lid lid  in
                   FStar_Ident.set_lid_range uu____11998 uu____11999  in
                 let uu____12000 = resolve_module_name env modul true  in
                 match uu____12000 with
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
            let uu____12009 = FStar_Ident.range_of_lid lid  in
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_IdentifierNotFound, msg1) uu____12009
        | FStar_Pervasives_Native.Some r -> r
  
let fail_or2 :
  'a .
    (FStar_Ident.ident -> 'a FStar_Pervasives_Native.option) ->
      FStar_Ident.ident -> 'a
  =
  fun lookup1  ->
    fun id1  ->
      let uu____12037 = lookup1 id1  in
      match uu____12037 with
      | FStar_Pervasives_Native.None  ->
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_IdentifierNotFound,
              (Prims.strcat "Identifier not found ["
                 (Prims.strcat id1.FStar_Ident.idText "]")))
            id1.FStar_Ident.idRange
      | FStar_Pervasives_Native.Some r -> r
  
let (mk_copy : env -> env) =
  fun en  ->
    let uu___139_12046 = en  in
    let uu____12047 = FStar_Util.smap_copy en.exported_ids  in
    let uu____12052 = FStar_Util.smap_copy en.trans_exported_ids  in
    let uu____12057 = FStar_Util.smap_copy en.sigmap  in
    let uu____12068 = FStar_Util.smap_copy en.docs  in
    {
      curmodule = (uu___139_12046.curmodule);
      curmonad = (uu___139_12046.curmonad);
      modules = (uu___139_12046.modules);
      scope_mods = (uu___139_12046.scope_mods);
      exported_ids = uu____12047;
      trans_exported_ids = uu____12052;
      includes = (uu___139_12046.includes);
      sigaccum = (uu___139_12046.sigaccum);
      sigmap = uu____12057;
      iface = (uu___139_12046.iface);
      admitted_iface = (uu___139_12046.admitted_iface);
      expect_typ = (uu___139_12046.expect_typ);
      docs = uu____12068;
      remaining_iface_decls = (uu___139_12046.remaining_iface_decls);
      syntax_only = (uu___139_12046.syntax_only);
      ds_hooks = (uu___139_12046.ds_hooks)
    }
  