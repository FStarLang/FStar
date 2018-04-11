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
    match projectee with | Open_module  -> true | uu____20 -> false
  
let (uu___is_Open_namespace : open_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Open_namespace  -> true | uu____24 -> false
  
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
    match projectee with | Local_binding _0 -> true | uu____189 -> false
  
let (__proj__Local_binding__item___0 : scope_mod -> local_binding) =
  fun projectee  -> match projectee with | Local_binding _0 -> _0 
let (uu___is_Rec_binding : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with | Rec_binding _0 -> true | uu____201 -> false
  
let (__proj__Rec_binding__item___0 : scope_mod -> rec_binding) =
  fun projectee  -> match projectee with | Rec_binding _0 -> _0 
let (uu___is_Module_abbrev : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with | Module_abbrev _0 -> true | uu____213 -> false
  
let (__proj__Module_abbrev__item___0 : scope_mod -> module_abbrev) =
  fun projectee  -> match projectee with | Module_abbrev _0 -> _0 
let (uu___is_Open_module_or_namespace : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Open_module_or_namespace _0 -> true
    | uu____225 -> false
  
let (__proj__Open_module_or_namespace__item___0 :
  scope_mod -> open_module_or_namespace) =
  fun projectee  -> match projectee with | Open_module_or_namespace _0 -> _0 
let (uu___is_Top_level_def : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with | Top_level_def _0 -> true | uu____237 -> false
  
let (__proj__Top_level_def__item___0 : scope_mod -> FStar_Ident.ident) =
  fun projectee  -> match projectee with | Top_level_def _0 -> _0 
let (uu___is_Record_or_dc : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with | Record_or_dc _0 -> true | uu____249 -> false
  
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
    | uu____262 -> false
  
let (uu___is_Exported_id_field : exported_id_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exported_id_field  -> true | uu____266 -> false
  
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
  ds_push_open_hook: env -> open_module_or_namespace -> Prims.unit ;
  ds_push_include_hook: env -> FStar_Ident.lident -> Prims.unit ;
  ds_push_module_abbrev_hook:
    env -> FStar_Ident.ident -> FStar_Ident.lident -> Prims.unit }[@@deriving
                                                                    show]
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
  dsenv_hooks -> env -> open_module_or_namespace -> Prims.unit) =
  fun projectee  ->
    match projectee with
    | { ds_push_open_hook = __fname__ds_push_open_hook;
        ds_push_include_hook = __fname__ds_push_include_hook;
        ds_push_module_abbrev_hook = __fname__ds_push_module_abbrev_hook;_}
        -> __fname__ds_push_open_hook
  
let (__proj__Mkdsenv_hooks__item__ds_push_include_hook :
  dsenv_hooks -> env -> FStar_Ident.lident -> Prims.unit) =
  fun projectee  ->
    match projectee with
    | { ds_push_open_hook = __fname__ds_push_open_hook;
        ds_push_include_hook = __fname__ds_push_include_hook;
        ds_push_module_abbrev_hook = __fname__ds_push_module_abbrev_hook;_}
        -> __fname__ds_push_include_hook
  
let (__proj__Mkdsenv_hooks__item__ds_push_module_abbrev_hook :
  dsenv_hooks -> env -> FStar_Ident.ident -> FStar_Ident.lident -> Prims.unit)
  =
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
    ds_push_open_hook = (fun uu____1535  -> fun uu____1536  -> ());
    ds_push_include_hook = (fun uu____1539  -> fun uu____1540  -> ());
    ds_push_module_abbrev_hook =
      (fun uu____1544  -> fun uu____1545  -> fun uu____1546  -> ())
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
    match projectee with | Term_name _0 -> true | uu____1579 -> false
  
let (__proj__Term_name__item___0 :
  foundname ->
    (FStar_Syntax_Syntax.typ,Prims.bool,FStar_Syntax_Syntax.attribute
                                          Prims.list)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Term_name _0 -> _0 
let (uu___is_Eff_name : foundname -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eff_name _0 -> true | uu____1619 -> false
  
let (__proj__Eff_name__item___0 :
  foundname ->
    (FStar_Syntax_Syntax.sigelt,FStar_Ident.lident)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Eff_name _0 -> _0 
let (set_iface : env -> Prims.bool -> env) =
  fun env  ->
    fun b  ->
      let uu___114_1645 = env  in
      {
        curmodule = (uu___114_1645.curmodule);
        curmonad = (uu___114_1645.curmonad);
        modules = (uu___114_1645.modules);
        scope_mods = (uu___114_1645.scope_mods);
        exported_ids = (uu___114_1645.exported_ids);
        trans_exported_ids = (uu___114_1645.trans_exported_ids);
        includes = (uu___114_1645.includes);
        sigaccum = (uu___114_1645.sigaccum);
        sigmap = (uu___114_1645.sigmap);
        iface = b;
        admitted_iface = (uu___114_1645.admitted_iface);
        expect_typ = (uu___114_1645.expect_typ);
        docs = (uu___114_1645.docs);
        remaining_iface_decls = (uu___114_1645.remaining_iface_decls);
        syntax_only = (uu___114_1645.syntax_only);
        ds_hooks = (uu___114_1645.ds_hooks)
      }
  
let (iface : env -> Prims.bool) = fun e  -> e.iface 
let (set_admitted_iface : env -> Prims.bool -> env) =
  fun e  ->
    fun b  ->
      let uu___115_1655 = e  in
      {
        curmodule = (uu___115_1655.curmodule);
        curmonad = (uu___115_1655.curmonad);
        modules = (uu___115_1655.modules);
        scope_mods = (uu___115_1655.scope_mods);
        exported_ids = (uu___115_1655.exported_ids);
        trans_exported_ids = (uu___115_1655.trans_exported_ids);
        includes = (uu___115_1655.includes);
        sigaccum = (uu___115_1655.sigaccum);
        sigmap = (uu___115_1655.sigmap);
        iface = (uu___115_1655.iface);
        admitted_iface = b;
        expect_typ = (uu___115_1655.expect_typ);
        docs = (uu___115_1655.docs);
        remaining_iface_decls = (uu___115_1655.remaining_iface_decls);
        syntax_only = (uu___115_1655.syntax_only);
        ds_hooks = (uu___115_1655.ds_hooks)
      }
  
let (admitted_iface : env -> Prims.bool) = fun e  -> e.admitted_iface 
let (set_expect_typ : env -> Prims.bool -> env) =
  fun e  ->
    fun b  ->
      let uu___116_1665 = e  in
      {
        curmodule = (uu___116_1665.curmodule);
        curmonad = (uu___116_1665.curmonad);
        modules = (uu___116_1665.modules);
        scope_mods = (uu___116_1665.scope_mods);
        exported_ids = (uu___116_1665.exported_ids);
        trans_exported_ids = (uu___116_1665.trans_exported_ids);
        includes = (uu___116_1665.includes);
        sigaccum = (uu___116_1665.sigaccum);
        sigmap = (uu___116_1665.sigmap);
        iface = (uu___116_1665.iface);
        admitted_iface = (uu___116_1665.admitted_iface);
        expect_typ = b;
        docs = (uu___116_1665.docs);
        remaining_iface_decls = (uu___116_1665.remaining_iface_decls);
        syntax_only = (uu___116_1665.syntax_only);
        ds_hooks = (uu___116_1665.ds_hooks)
      }
  
let (expect_typ : env -> Prims.bool) = fun e  -> e.expect_typ 
let (all_exported_id_kinds : exported_id_kind Prims.list) =
  [Exported_id_field; Exported_id_term_type] 
let (transitive_exported_ids :
  env -> FStar_Ident.lident -> Prims.string Prims.list) =
  fun env  ->
    fun lid  ->
      let module_name = FStar_Ident.string_of_lid lid  in
      let uu____1680 =
        FStar_Util.smap_try_find env.trans_exported_ids module_name  in
      match uu____1680 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some exported_id_set ->
          let uu____1686 =
            let uu____1687 = exported_id_set Exported_id_term_type  in
            FStar_ST.op_Bang uu____1687  in
          FStar_All.pipe_right uu____1686 FStar_Util.set_elements
  
let (open_modules :
  env ->
    (FStar_Ident.lident,FStar_Syntax_Syntax.modul)
      FStar_Pervasives_Native.tuple2 Prims.list)
  = fun e  -> e.modules 
let (open_modules_and_namespaces : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    FStar_List.filter_map
      (fun uu___82_1817  ->
         match uu___82_1817 with
         | Open_module_or_namespace (lid,_info) ->
             FStar_Pervasives_Native.Some lid
         | uu____1822 -> FStar_Pervasives_Native.None) env.scope_mods
  
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun e  ->
    fun l  ->
      let uu___117_1829 = e  in
      {
        curmodule = (FStar_Pervasives_Native.Some l);
        curmonad = (uu___117_1829.curmonad);
        modules = (uu___117_1829.modules);
        scope_mods = (uu___117_1829.scope_mods);
        exported_ids = (uu___117_1829.exported_ids);
        trans_exported_ids = (uu___117_1829.trans_exported_ids);
        includes = (uu___117_1829.includes);
        sigaccum = (uu___117_1829.sigaccum);
        sigmap = (uu___117_1829.sigmap);
        iface = (uu___117_1829.iface);
        admitted_iface = (uu___117_1829.admitted_iface);
        expect_typ = (uu___117_1829.expect_typ);
        docs = (uu___117_1829.docs);
        remaining_iface_decls = (uu___117_1829.remaining_iface_decls);
        syntax_only = (uu___117_1829.syntax_only);
        ds_hooks = (uu___117_1829.ds_hooks)
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
      let uu____1844 =
        FStar_All.pipe_right env.remaining_iface_decls
          (FStar_List.tryFind
             (fun uu____1878  ->
                match uu____1878 with
                | (m,uu____1886) -> FStar_Ident.lid_equals l m))
         in
      match uu____1844 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (uu____1903,decls) ->
          FStar_Pervasives_Native.Some decls
  
let (set_iface_decls :
  env -> FStar_Ident.lident -> FStar_Parser_AST.decl Prims.list -> env) =
  fun env  ->
    fun l  ->
      fun ds  ->
        let uu____1930 =
          FStar_List.partition
            (fun uu____1960  ->
               match uu____1960 with
               | (m,uu____1968) -> FStar_Ident.lid_equals l m)
            env.remaining_iface_decls
           in
        match uu____1930 with
        | (uu____1973,rest) ->
            let uu___118_2007 = env  in
            {
              curmodule = (uu___118_2007.curmodule);
              curmonad = (uu___118_2007.curmonad);
              modules = (uu___118_2007.modules);
              scope_mods = (uu___118_2007.scope_mods);
              exported_ids = (uu___118_2007.exported_ids);
              trans_exported_ids = (uu___118_2007.trans_exported_ids);
              includes = (uu___118_2007.includes);
              sigaccum = (uu___118_2007.sigaccum);
              sigmap = (uu___118_2007.sigmap);
              iface = (uu___118_2007.iface);
              admitted_iface = (uu___118_2007.admitted_iface);
              expect_typ = (uu___118_2007.expect_typ);
              docs = (uu___118_2007.docs);
              remaining_iface_decls = ((l, ds) :: rest);
              syntax_only = (uu___118_2007.syntax_only);
              ds_hooks = (uu___118_2007.ds_hooks)
            }
  
let (qual : FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident) =
  FStar_Syntax_Util.qual_id 
let (qualify : env -> FStar_Ident.ident -> FStar_Ident.lident) =
  fun env  ->
    fun id1  ->
      match env.curmonad with
      | FStar_Pervasives_Native.None  ->
          let uu____2026 = current_module env  in qual uu____2026 id1
      | FStar_Pervasives_Native.Some monad ->
          let uu____2028 =
            let uu____2029 = current_module env  in qual uu____2029 monad  in
          FStar_Syntax_Util.mk_field_projector_name_from_ident uu____2028 id1
  
let (syntax_only : env -> Prims.bool) = fun env  -> env.syntax_only 
let (set_syntax_only : env -> Prims.bool -> env) =
  fun env  ->
    fun b  ->
      let uu___119_2039 = env  in
      {
        curmodule = (uu___119_2039.curmodule);
        curmonad = (uu___119_2039.curmonad);
        modules = (uu___119_2039.modules);
        scope_mods = (uu___119_2039.scope_mods);
        exported_ids = (uu___119_2039.exported_ids);
        trans_exported_ids = (uu___119_2039.trans_exported_ids);
        includes = (uu___119_2039.includes);
        sigaccum = (uu___119_2039.sigaccum);
        sigmap = (uu___119_2039.sigmap);
        iface = (uu___119_2039.iface);
        admitted_iface = (uu___119_2039.admitted_iface);
        expect_typ = (uu___119_2039.expect_typ);
        docs = (uu___119_2039.docs);
        remaining_iface_decls = (uu___119_2039.remaining_iface_decls);
        syntax_only = b;
        ds_hooks = (uu___119_2039.ds_hooks)
      }
  
let (ds_hooks : env -> dsenv_hooks) = fun env  -> env.ds_hooks 
let (set_ds_hooks : env -> dsenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___120_2049 = env  in
      {
        curmodule = (uu___120_2049.curmodule);
        curmonad = (uu___120_2049.curmonad);
        modules = (uu___120_2049.modules);
        scope_mods = (uu___120_2049.scope_mods);
        exported_ids = (uu___120_2049.exported_ids);
        trans_exported_ids = (uu___120_2049.trans_exported_ids);
        includes = (uu___120_2049.includes);
        sigaccum = (uu___120_2049.sigaccum);
        sigmap = (uu___120_2049.sigmap);
        iface = (uu___120_2049.iface);
        admitted_iface = (uu___120_2049.admitted_iface);
        expect_typ = (uu___120_2049.expect_typ);
        docs = (uu___120_2049.docs);
        remaining_iface_decls = (uu___120_2049.remaining_iface_decls);
        syntax_only = (uu___120_2049.syntax_only);
        ds_hooks = hooks
      }
  
let new_sigmap : 'Auu____2052 . Prims.unit -> 'Auu____2052 FStar_Util.smap =
  fun uu____2058  -> FStar_Util.smap_create (Prims.parse_int "100") 
let (empty_env : Prims.unit -> env) =
  fun uu____2061  ->
    let uu____2062 = new_sigmap ()  in
    let uu____2065 = new_sigmap ()  in
    let uu____2068 = new_sigmap ()  in
    let uu____2079 = new_sigmap ()  in
    let uu____2090 = new_sigmap ()  in
    {
      curmodule = FStar_Pervasives_Native.None;
      curmonad = FStar_Pervasives_Native.None;
      modules = [];
      scope_mods = [];
      exported_ids = uu____2062;
      trans_exported_ids = uu____2065;
      includes = uu____2068;
      sigaccum = [];
      sigmap = uu____2079;
      iface = false;
      admitted_iface = false;
      expect_typ = false;
      docs = uu____2090;
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
      (fun uu____2122  ->
         match uu____2122 with
         | (m,uu____2128) ->
             FStar_Ident.lid_equals m FStar_Parser_Const.all_lid) env.modules
  
let (set_bv_range :
  FStar_Syntax_Syntax.bv -> FStar_Range.range -> FStar_Syntax_Syntax.bv) =
  fun bv  ->
    fun r  ->
      let id1 =
        let uu___121_2136 = bv.FStar_Syntax_Syntax.ppname  in
        {
          FStar_Ident.idText = (uu___121_2136.FStar_Ident.idText);
          FStar_Ident.idRange = r
        }  in
      let uu___122_2137 = bv  in
      {
        FStar_Syntax_Syntax.ppname = id1;
        FStar_Syntax_Syntax.index = (uu___122_2137.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = (uu___122_2137.FStar_Syntax_Syntax.sort)
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
        (fun uu____2224  ->
           match uu____2224 with
           | (x,y,dd,dq) ->
               if id1.FStar_Ident.idText = x
               then
                 let uu____2247 =
                   let uu____2248 =
                     FStar_Ident.lid_of_path ["Prims"; y]
                       id1.FStar_Ident.idRange
                      in
                   FStar_Syntax_Syntax.fvar uu____2248 dd dq  in
                 FStar_Pervasives_Native.Some uu____2247
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
    match projectee with | Cont_ok _0 -> true | uu____2291 -> false
  
let __proj__Cont_ok__item___0 : 'a . 'a cont_t -> 'a =
  fun projectee  -> match projectee with | Cont_ok _0 -> _0 
let uu___is_Cont_fail : 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_fail  -> true | uu____2320 -> false
  
let uu___is_Cont_ignore : 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_ignore  -> true | uu____2334 -> false
  
let option_of_cont :
  'a .
    (Prims.unit -> 'a FStar_Pervasives_Native.option) ->
      'a cont_t -> 'a FStar_Pervasives_Native.option
  =
  fun k_ignore  ->
    fun uu___83_2357  ->
      match uu___83_2357 with
      | Cont_ok a -> FStar_Pervasives_Native.Some a
      | Cont_fail  -> FStar_Pervasives_Native.None
      | Cont_ignore  -> k_ignore ()
  
let find_in_record :
  'Auu____2370 .
    FStar_Ident.ident Prims.list ->
      FStar_Ident.ident ->
        record_or_dc ->
          (record_or_dc -> 'Auu____2370 cont_t) -> 'Auu____2370 cont_t
  =
  fun ns  ->
    fun id1  ->
      fun record  ->
        fun cont  ->
          let typename' =
            FStar_Ident.lid_of_ids
              (FStar_List.append ns [(record.typename).FStar_Ident.ident])
             in
          let uu____2403 = FStar_Ident.lid_equals typename' record.typename
             in
          if uu____2403
          then
            let fname =
              FStar_Ident.lid_of_ids
                (FStar_List.append (record.typename).FStar_Ident.ns [id1])
               in
            let find1 =
              FStar_Util.find_map record.fields
                (fun uu____2417  ->
                   match uu____2417 with
                   | (f,uu____2425) ->
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
  fun uu___84_2471  ->
    match uu___84_2471 with
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
              let rec aux uu___85_2527 =
                match uu___85_2527 with
                | [] -> find_in_module_default
                | modul::q ->
                    let mname = modul.FStar_Ident.str  in
                    let not_shadowed =
                      let uu____2538 = get_exported_id_set env mname  in
                      match uu____2538 with
                      | FStar_Pervasives_Native.None  -> true
                      | FStar_Pervasives_Native.Some mex ->
                          let mexports =
                            let uu____2559 = mex eikind  in
                            FStar_ST.op_Bang uu____2559  in
                          FStar_Util.set_mem idstr mexports
                       in
                    let mincludes =
                      let uu____2673 =
                        FStar_Util.smap_try_find env.includes mname  in
                      match uu____2673 with
                      | FStar_Pervasives_Native.None  -> []
                      | FStar_Pervasives_Native.Some minc ->
                          FStar_ST.op_Bang minc
                       in
                    let look_into =
                      if not_shadowed
                      then
                        let uu____2749 = qual modul id1  in
                        find_in_module uu____2749
                      else Cont_ignore  in
                    (match look_into with
                     | Cont_ignore  -> aux (FStar_List.append mincludes q)
                     | uu____2753 -> look_into)
                 in
              aux [ns]
  
let (is_exported_id_field : exported_id_kind -> Prims.bool) =
  fun uu___86_2758  ->
    match uu___86_2758 with
    | Exported_id_field  -> true
    | uu____2759 -> false
  
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
                  let check_local_binding_id uu___87_2861 =
                    match uu___87_2861 with
                    | (id',uu____2863,uu____2864) ->
                        id'.FStar_Ident.idText = id1.FStar_Ident.idText
                     in
                  let check_rec_binding_id uu___88_2868 =
                    match uu___88_2868 with
                    | (id',uu____2870,uu____2871) ->
                        id'.FStar_Ident.idText = id1.FStar_Ident.idText
                     in
                  let curmod_ns =
                    let uu____2875 = current_module env  in
                    FStar_Ident.ids_of_lid uu____2875  in
                  let proc uu___89_2881 =
                    match uu___89_2881 with
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
                        let uu____2889 = FStar_Ident.lid_of_ids curmod_ns  in
                        find_in_module_with_includes Exported_id_field
                          (fun lid  ->
                             let id2 = lid.FStar_Ident.ident  in
                             find_in_record lid.FStar_Ident.ns id2 r k_record)
                          Cont_ignore env uu____2889 id1
                    | uu____2894 -> Cont_ignore  in
                  let rec aux uu___90_2902 =
                    match uu___90_2902 with
                    | a::q ->
                        let uu____2911 = proc a  in
                        option_of_cont (fun uu____2915  -> aux q) uu____2911
                    | [] ->
                        let uu____2916 = lookup_default_id Cont_fail id1  in
                        option_of_cont
                          (fun uu____2920  -> FStar_Pervasives_Native.None)
                          uu____2916
                     in
                  aux env.scope_mods
  
let found_local_binding :
  'Auu____2925 'Auu____2926 .
    FStar_Range.range ->
      ('Auu____2925,FStar_Syntax_Syntax.bv,'Auu____2926)
        FStar_Pervasives_Native.tuple3 ->
        (FStar_Syntax_Syntax.term,'Auu____2926)
          FStar_Pervasives_Native.tuple2
  =
  fun r  ->
    fun uu____2944  ->
      match uu____2944 with
      | (id',x,mut) -> let uu____2954 = bv_to_name x r  in (uu____2954, mut)
  
let find_in_module :
  'Auu____2960 .
    env ->
      FStar_Ident.lident ->
        (FStar_Ident.lident ->
           (FStar_Syntax_Syntax.sigelt,Prims.bool)
             FStar_Pervasives_Native.tuple2 -> 'Auu____2960)
          -> 'Auu____2960 -> 'Auu____2960
  =
  fun env  ->
    fun lid  ->
      fun k_global_def  ->
        fun k_not_found  ->
          let uu____2995 =
            FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str  in
          match uu____2995 with
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
      let uu____3031 = unmangleOpName id1  in
      match uu____3031 with
      | FStar_Pervasives_Native.Some f -> FStar_Pervasives_Native.Some f
      | uu____3057 ->
          try_lookup_id'' env id1 Exported_id_term_type
            (fun r  ->
               let uu____3071 = found_local_binding id1.FStar_Ident.idRange r
                  in
               Cont_ok uu____3071) (fun uu____3081  -> Cont_fail)
            (fun uu____3087  -> Cont_ignore)
            (fun i  ->
               find_in_module env i
                 (fun uu____3102  -> fun uu____3103  -> Cont_fail)
                 Cont_ignore)
            (fun uu____3118  -> fun uu____3119  -> Cont_fail)
  
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
            | FStar_Pervasives_Native.Some uu____3189 ->
                let lid = qualify env id1  in
                let uu____3191 =
                  FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str
                   in
                (match uu____3191 with
                 | FStar_Pervasives_Native.Some r ->
                     let uu____3215 = k_global_def lid r  in
                     FStar_Pervasives_Native.Some uu____3215
                 | FStar_Pervasives_Native.None  ->
                     FStar_Pervasives_Native.None)
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             in
          match find_in_monad with
          | FStar_Pervasives_Native.Some v1 -> v1
          | FStar_Pervasives_Native.None  ->
              let lid =
                let uu____3238 = current_module env  in qual uu____3238 id1
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
        let rec aux uu___91_3285 =
          match uu___91_3285 with
          | [] ->
              let uu____3290 = module_is_defined env lid  in
              if uu____3290
              then FStar_Pervasives_Native.Some lid
              else FStar_Pervasives_Native.None
          | (Open_module_or_namespace (ns,Open_namespace ))::q when honor_ns
              ->
              let new_lid =
                let uu____3299 =
                  let uu____3300 = FStar_Ident.path_of_lid ns  in
                  let uu____3303 = FStar_Ident.path_of_lid lid  in
                  FStar_List.append uu____3300 uu____3303  in
                let uu____3306 = FStar_Ident.range_of_lid lid  in
                FStar_Ident.lid_of_path uu____3299 uu____3306  in
              let uu____3307 = module_is_defined env new_lid  in
              if uu____3307
              then FStar_Pervasives_Native.Some new_lid
              else aux q
          | (Module_abbrev (name,modul))::uu____3313 when
              (nslen = (Prims.parse_int "0")) &&
                (name.FStar_Ident.idText =
                   (lid.FStar_Ident.ident).FStar_Ident.idText)
              -> FStar_Pervasives_Native.Some modul
          | uu____3320::q -> aux q  in
        aux env.scope_mods
  
let (fail_if_curmodule :
  env -> FStar_Ident.lident -> FStar_Ident.lident -> Prims.unit) =
  fun env  ->
    fun ns_original  ->
      fun ns_resolved  ->
        let uu____3333 =
          let uu____3334 = current_module env  in
          FStar_Ident.lid_equals ns_resolved uu____3334  in
        if uu____3333
        then
          let uu____3335 =
            FStar_Ident.lid_equals ns_resolved FStar_Parser_Const.prims_lid
             in
          (if uu____3335
           then ()
           else
             (let uu____3337 =
                let uu____3342 =
                  FStar_Util.format1
                    "Reference %s to current module is forbidden (see GitHub issue #451)"
                    ns_original.FStar_Ident.str
                   in
                (FStar_Errors.Fatal_ForbiddenReferenceToCurrentModule,
                  uu____3342)
                 in
              let uu____3343 = FStar_Ident.range_of_lid ns_original  in
              FStar_Errors.raise_error uu____3337 uu____3343))
        else ()
  
let (fail_if_qualified_by_curmodule :
  env -> FStar_Ident.lident -> Prims.unit) =
  fun env  ->
    fun lid  ->
      match lid.FStar_Ident.ns with
      | [] -> ()
      | uu____3351 ->
          let modul_orig = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          let uu____3355 = resolve_module_name env modul_orig true  in
          (match uu____3355 with
           | FStar_Pervasives_Native.Some modul_res ->
               fail_if_curmodule env modul_orig modul_res
           | uu____3359 -> ())
  
let (is_open : env -> FStar_Ident.lident -> open_kind -> Prims.bool) =
  fun env  ->
    fun lid  ->
      fun open_kind  ->
        FStar_List.existsb
          (fun uu___92_3374  ->
             match uu___92_3374 with
             | Open_module_or_namespace (ns,k) ->
                 (k = open_kind) && (FStar_Ident.lid_equals lid ns)
             | uu____3377 -> false) env.scope_mods
  
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
                 let uu____3478 = aux rev_ns_prefix ns_last_id  in
                 FStar_All.pipe_right uu____3478
                   (FStar_Util.map_option
                      (fun uu____3528  ->
                         match uu____3528 with
                         | (stripped_ids,rev_kept_ids) ->
                             (stripped_ids, (id1 :: rev_kept_ids)))))
           in
        let do_shorten env1 ids1 =
          match FStar_List.rev ids1 with
          | [] -> ([], [])
          | ns_last_id::ns_rev_prefix ->
              let uu____3594 = aux ns_rev_prefix ns_last_id  in
              (match uu____3594 with
               | FStar_Pervasives_Native.None  -> ([], ids1)
               | FStar_Pervasives_Native.Some (stripped_ids,rev_kept_ids) ->
                   (stripped_ids, (FStar_List.rev rev_kept_ids)))
           in
        if is_full_path
        then
          let uu____3655 =
            let uu____3658 = FStar_Ident.lid_of_ids ids  in
            resolve_module_name env uu____3658 true  in
          match uu____3655 with
          | FStar_Pervasives_Native.Some m when module_is_open env m ->
              (ids, [])
          | uu____3672 -> do_shorten env ids
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
                  | uu____3774::uu____3775 ->
                      let uu____3778 =
                        let uu____3781 =
                          let uu____3782 =
                            FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
                          let uu____3783 = FStar_Ident.range_of_lid lid  in
                          FStar_Ident.set_lid_range uu____3782 uu____3783  in
                        resolve_module_name env uu____3781 true  in
                      (match uu____3778 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some modul ->
                           let uu____3787 =
                             find_in_module_with_includes eikind f_module
                               Cont_fail env modul lid.FStar_Ident.ident
                              in
                           option_of_cont
                             (fun uu____3791  -> FStar_Pervasives_Native.None)
                             uu____3787)
                  | [] ->
                      try_lookup_id'' env lid.FStar_Ident.ident eikind
                        k_local_binding k_rec_binding k_record f_module
                        l_default
  
let cont_of_option :
  'a . 'a cont_t -> 'a FStar_Pervasives_Native.option -> 'a cont_t =
  fun k_none  ->
    fun uu___93_3809  ->
      match uu___93_3809 with
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
              let uu____3908 = k_global_def lid1 def  in
              cont_of_option k uu____3908  in
            let f_module lid' =
              let k = Cont_ignore  in
              find_in_module env lid' (k_global_def' k) k  in
            let l_default k i = lookup_default_id env i (k_global_def' k) k
               in
            resolve_in_open_namespaces'' env lid Exported_id_term_type
              (fun l  ->
                 let uu____3938 = k_local_binding l  in
                 cont_of_option Cont_fail uu____3938)
              (fun r  ->
                 let uu____3944 = k_rec_binding r  in
                 cont_of_option Cont_fail uu____3944)
              (fun uu____3948  -> Cont_ignore) f_module l_default
  
let (fv_qual_of_se :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option)
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____3956,uu____3957,uu____3958,l,uu____3960,uu____3961) ->
        let qopt =
          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
            (fun uu___94_3972  ->
               match uu___94_3972 with
               | FStar_Syntax_Syntax.RecordConstructor (uu____3975,fs) ->
                   FStar_Pervasives_Native.Some
                     (FStar_Syntax_Syntax.Record_ctor (l, fs))
               | uu____3987 -> FStar_Pervasives_Native.None)
           in
        (match qopt with
         | FStar_Pervasives_Native.None  ->
             FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor
         | x -> x)
    | FStar_Syntax_Syntax.Sig_declare_typ (uu____3993,uu____3994,uu____3995)
        -> FStar_Pervasives_Native.None
    | uu____3996 -> FStar_Pervasives_Native.None
  
let (lb_fv :
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Ident.lident -> FStar_Syntax_Syntax.fv)
  =
  fun lbs  ->
    fun lid  ->
      let uu____4007 =
        FStar_Util.find_map lbs
          (fun lb  ->
             let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
             let uu____4015 = FStar_Syntax_Syntax.fv_eq_lid fv lid  in
             if uu____4015
             then FStar_Pervasives_Native.Some fv
             else FStar_Pervasives_Native.None)
         in
      FStar_All.pipe_right uu____4007 FStar_Util.must
  
let (ns_of_lid_equals :
  FStar_Ident.lident -> FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    fun ns  ->
      (let uu____4029 =
         let uu____4030 = FStar_Ident.ids_of_lid ns  in
         FStar_List.length uu____4030  in
       (FStar_List.length lid.FStar_Ident.ns) = uu____4029) &&
        (let uu____4038 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
         FStar_Ident.lid_equals uu____4038 ns)
  
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
          let k_global_def source_lid uu___99_4068 =
            match uu___99_4068 with
            | (uu____4075,true ) when exclude_interf ->
                FStar_Pervasives_Native.None
            | (se,uu____4077) ->
                (match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_inductive_typ uu____4080 ->
                     let uu____4097 =
                       let uu____4098 =
                         let uu____4107 =
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.Delta_constant
                             FStar_Pervasives_Native.None
                            in
                         (uu____4107, false,
                           (se.FStar_Syntax_Syntax.sigattrs))
                          in
                       Term_name uu____4098  in
                     FStar_Pervasives_Native.Some uu____4097
                 | FStar_Syntax_Syntax.Sig_datacon uu____4110 ->
                     let uu____4125 =
                       let uu____4126 =
                         let uu____4135 =
                           let uu____4136 = fv_qual_of_se se  in
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.Delta_constant uu____4136
                            in
                         (uu____4135, false,
                           (se.FStar_Syntax_Syntax.sigattrs))
                          in
                       Term_name uu____4126  in
                     FStar_Pervasives_Native.Some uu____4125
                 | FStar_Syntax_Syntax.Sig_let ((uu____4141,lbs),uu____4143)
                     ->
                     let fv = lb_fv lbs source_lid  in
                     let uu____4159 =
                       let uu____4160 =
                         let uu____4169 =
                           FStar_Syntax_Syntax.fvar source_lid
                             fv.FStar_Syntax_Syntax.fv_delta
                             fv.FStar_Syntax_Syntax.fv_qual
                            in
                         (uu____4169, false,
                           (se.FStar_Syntax_Syntax.sigattrs))
                          in
                       Term_name uu____4160  in
                     FStar_Pervasives_Native.Some uu____4159
                 | FStar_Syntax_Syntax.Sig_declare_typ
                     (lid1,uu____4173,uu____4174) ->
                     let quals = se.FStar_Syntax_Syntax.sigquals  in
                     let uu____4178 =
                       any_val ||
                         (FStar_All.pipe_right quals
                            (FStar_Util.for_some
                               (fun uu___95_4182  ->
                                  match uu___95_4182 with
                                  | FStar_Syntax_Syntax.Assumption  -> true
                                  | uu____4183 -> false)))
                        in
                     if uu____4178
                     then
                       let lid2 =
                         let uu____4187 = FStar_Ident.range_of_lid source_lid
                            in
                         FStar_Ident.set_lid_range lid1 uu____4187  in
                       let dd =
                         let uu____4189 =
                           (FStar_Syntax_Util.is_primop_lid lid2) ||
                             (FStar_All.pipe_right quals
                                (FStar_Util.for_some
                                   (fun uu___96_4194  ->
                                      match uu___96_4194 with
                                      | FStar_Syntax_Syntax.Projector
                                          uu____4195 -> true
                                      | FStar_Syntax_Syntax.Discriminator
                                          uu____4200 -> true
                                      | uu____4201 -> false)))
                            in
                         if uu____4189
                         then FStar_Syntax_Syntax.Delta_equational
                         else FStar_Syntax_Syntax.Delta_constant  in
                       let dd1 =
                         let uu____4204 =
                           FStar_All.pipe_right quals
                             (FStar_Util.for_some
                                (fun uu___97_4208  ->
                                   match uu___97_4208 with
                                   | FStar_Syntax_Syntax.Abstract  -> true
                                   | uu____4209 -> false))
                            in
                         if uu____4204
                         then FStar_Syntax_Syntax.Delta_abstract dd
                         else dd  in
                       let uu____4211 =
                         FStar_Util.find_map quals
                           (fun uu___98_4216  ->
                              match uu___98_4216 with
                              | FStar_Syntax_Syntax.Reflectable refl_monad ->
                                  FStar_Pervasives_Native.Some refl_monad
                              | uu____4220 -> FStar_Pervasives_Native.None)
                          in
                       (match uu____4211 with
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
                        | uu____4231 ->
                            let uu____4234 =
                              let uu____4235 =
                                let uu____4244 =
                                  let uu____4245 = fv_qual_of_se se  in
                                  FStar_Syntax_Syntax.fvar lid2 dd1
                                    uu____4245
                                   in
                                (uu____4244, false,
                                  (se.FStar_Syntax_Syntax.sigattrs))
                                 in
                              Term_name uu____4235  in
                            FStar_Pervasives_Native.Some uu____4234)
                     else FStar_Pervasives_Native.None
                 | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
                     let uu____4252 =
                       let uu____4253 =
                         let uu____4258 =
                           let uu____4259 =
                             FStar_Ident.range_of_lid source_lid  in
                           FStar_Ident.set_lid_range
                             ne.FStar_Syntax_Syntax.mname uu____4259
                            in
                         (se, uu____4258)  in
                       Eff_name uu____4253  in
                     FStar_Pervasives_Native.Some uu____4252
                 | FStar_Syntax_Syntax.Sig_new_effect ne ->
                     let uu____4261 =
                       let uu____4262 =
                         let uu____4267 =
                           let uu____4268 =
                             FStar_Ident.range_of_lid source_lid  in
                           FStar_Ident.set_lid_range
                             ne.FStar_Syntax_Syntax.mname uu____4268
                            in
                         (se, uu____4267)  in
                       Eff_name uu____4262  in
                     FStar_Pervasives_Native.Some uu____4261
                 | FStar_Syntax_Syntax.Sig_effect_abbrev uu____4269 ->
                     FStar_Pervasives_Native.Some (Eff_name (se, source_lid))
                 | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
                     let uu____4288 =
                       let uu____4289 =
                         let uu____4298 =
                           FStar_Syntax_Syntax.fvar source_lid
                             (FStar_Syntax_Syntax.Delta_defined_at_level
                                (Prims.parse_int "1"))
                             FStar_Pervasives_Native.None
                            in
                         (uu____4298, false, [])  in
                       Term_name uu____4289  in
                     FStar_Pervasives_Native.Some uu____4288
                 | uu____4301 -> FStar_Pervasives_Native.None)
             in
          let k_local_binding r =
            let uu____4320 =
              let uu____4325 = FStar_Ident.range_of_lid lid  in
              found_local_binding uu____4325 r  in
            match uu____4320 with
            | (t,mut) ->
                FStar_Pervasives_Native.Some (Term_name (t, mut, []))
             in
          let k_rec_binding uu____4343 =
            match uu____4343 with
            | (id1,l,dd) ->
                let uu____4355 =
                  let uu____4356 =
                    let uu____4365 =
                      let uu____4366 =
                        let uu____4367 = FStar_Ident.range_of_lid lid  in
                        FStar_Ident.set_lid_range l uu____4367  in
                      FStar_Syntax_Syntax.fvar uu____4366 dd
                        FStar_Pervasives_Native.None
                       in
                    (uu____4365, false, [])  in
                  Term_name uu____4356  in
                FStar_Pervasives_Native.Some uu____4355
             in
          let found_unmangled =
            match lid.FStar_Ident.ns with
            | [] ->
                let uu____4375 = unmangleOpName lid.FStar_Ident.ident  in
                (match uu____4375 with
                 | FStar_Pervasives_Native.Some (t,mut) ->
                     FStar_Pervasives_Native.Some (Term_name (t, mut, []))
                 | uu____4392 -> FStar_Pervasives_Native.None)
            | uu____4399 -> FStar_Pervasives_Native.None  in
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
        let uu____4428 = try_lookup_name true exclude_interf env lid  in
        match uu____4428 with
        | FStar_Pervasives_Native.Some (Eff_name (o,l)) ->
            FStar_Pervasives_Native.Some (o, l)
        | uu____4443 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____4458 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____4458 with
      | FStar_Pervasives_Native.Some (o,l1) ->
          FStar_Pervasives_Native.Some l1
      | uu____4473 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_name_and_attributes :
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident,FStar_Syntax_Syntax.cflags Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____4494 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____4494 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____4510;
             FStar_Syntax_Syntax.sigquals = uu____4511;
             FStar_Syntax_Syntax.sigmeta = uu____4512;
             FStar_Syntax_Syntax.sigattrs = uu____4513;_},l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____4532;
             FStar_Syntax_Syntax.sigquals = uu____4533;
             FStar_Syntax_Syntax.sigmeta = uu____4534;
             FStar_Syntax_Syntax.sigattrs = uu____4535;_},l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (uu____4553,uu____4554,uu____4555,uu____4556,cattributes);
             FStar_Syntax_Syntax.sigrng = uu____4558;
             FStar_Syntax_Syntax.sigquals = uu____4559;
             FStar_Syntax_Syntax.sigmeta = uu____4560;
             FStar_Syntax_Syntax.sigattrs = uu____4561;_},l1)
          -> FStar_Pervasives_Native.Some (l1, cattributes)
      | uu____4583 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_defn :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.eff_decl FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____4604 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____4604 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____4614;
             FStar_Syntax_Syntax.sigquals = uu____4615;
             FStar_Syntax_Syntax.sigmeta = uu____4616;
             FStar_Syntax_Syntax.sigattrs = uu____4617;_},uu____4618)
          -> FStar_Pervasives_Native.Some ne
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____4628;
             FStar_Syntax_Syntax.sigquals = uu____4629;
             FStar_Syntax_Syntax.sigmeta = uu____4630;
             FStar_Syntax_Syntax.sigattrs = uu____4631;_},uu____4632)
          -> FStar_Pervasives_Native.Some ne
      | uu____4641 -> FStar_Pervasives_Native.None
  
let (is_effect_name : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____4654 = try_lookup_effect_name env lid  in
      match uu____4654 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____4657 -> true
  
let (try_lookup_root_effect_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____4666 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____4666 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (l',uu____4676,uu____4677,uu____4678,uu____4679);
             FStar_Syntax_Syntax.sigrng = uu____4680;
             FStar_Syntax_Syntax.sigquals = uu____4681;
             FStar_Syntax_Syntax.sigmeta = uu____4682;
             FStar_Syntax_Syntax.sigattrs = uu____4683;_},uu____4684)
          ->
          let rec aux new_name =
            let uu____4703 =
              FStar_Util.smap_try_find (sigmap env) new_name.FStar_Ident.str
               in
            match uu____4703 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (s,uu____4721) ->
                (match s.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
                     let uu____4729 =
                       let uu____4730 = FStar_Ident.range_of_lid l  in
                       FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname
                         uu____4730
                        in
                     FStar_Pervasives_Native.Some uu____4729
                 | FStar_Syntax_Syntax.Sig_new_effect ne ->
                     let uu____4732 =
                       let uu____4733 = FStar_Ident.range_of_lid l  in
                       FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname
                         uu____4733
                        in
                     FStar_Pervasives_Native.Some uu____4732
                 | FStar_Syntax_Syntax.Sig_effect_abbrev
                     (uu____4734,uu____4735,uu____4736,cmp,uu____4738) ->
                     let l'' = FStar_Syntax_Util.comp_effect_name cmp  in
                     aux l''
                 | uu____4744 -> FStar_Pervasives_Native.None)
             in
          aux l'
      | FStar_Pervasives_Native.Some (uu____4745,l') ->
          FStar_Pervasives_Native.Some l'
      | uu____4751 -> FStar_Pervasives_Native.None
  
let (lookup_letbinding_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___100_4780 =
        match uu___100_4780 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____4789,uu____4790,uu____4791);
             FStar_Syntax_Syntax.sigrng = uu____4792;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____4794;
             FStar_Syntax_Syntax.sigattrs = uu____4795;_},uu____4796)
            -> FStar_Pervasives_Native.Some quals
        | uu____4803 -> FStar_Pervasives_Native.None  in
      let uu____4810 =
        resolve_in_open_namespaces' env lid
          (fun uu____4818  -> FStar_Pervasives_Native.None)
          (fun uu____4822  -> FStar_Pervasives_Native.None) k_global_def
         in
      match uu____4810 with
      | FStar_Pervasives_Native.Some quals -> quals
      | uu____4832 -> []
  
let (try_lookup_module :
  env ->
    FStar_Ident.path ->
      FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun path  ->
      let uu____4845 =
        FStar_List.tryFind
          (fun uu____4860  ->
             match uu____4860 with
             | (mlid,modul) ->
                 let uu____4867 = FStar_Ident.path_of_lid mlid  in
                 uu____4867 = path) env.modules
         in
      match uu____4845 with
      | FStar_Pervasives_Native.Some (uu____4870,modul) ->
          FStar_Pervasives_Native.Some modul
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (try_lookup_let :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___101_4900 =
        match uu___101_4900 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               ((uu____4907,lbs),uu____4909);
             FStar_Syntax_Syntax.sigrng = uu____4910;
             FStar_Syntax_Syntax.sigquals = uu____4911;
             FStar_Syntax_Syntax.sigmeta = uu____4912;
             FStar_Syntax_Syntax.sigattrs = uu____4913;_},uu____4914)
            ->
            let fv = lb_fv lbs lid1  in
            let uu____4934 =
              FStar_Syntax_Syntax.fvar lid1 fv.FStar_Syntax_Syntax.fv_delta
                fv.FStar_Syntax_Syntax.fv_qual
               in
            FStar_Pervasives_Native.Some uu____4934
        | uu____4935 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____4941  -> FStar_Pervasives_Native.None)
        (fun uu____4943  -> FStar_Pervasives_Native.None) k_global_def
  
let (try_lookup_definition :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___102_4966 =
        match uu___102_4966 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               (lbs,uu____4976);
             FStar_Syntax_Syntax.sigrng = uu____4977;
             FStar_Syntax_Syntax.sigquals = uu____4978;
             FStar_Syntax_Syntax.sigmeta = uu____4979;
             FStar_Syntax_Syntax.sigattrs = uu____4980;_},uu____4981)
            ->
            FStar_Util.find_map (FStar_Pervasives_Native.snd lbs)
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inr fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv lid1 ->
                     FStar_Pervasives_Native.Some
                       (lb.FStar_Syntax_Syntax.lbdef)
                 | uu____5004 -> FStar_Pervasives_Native.None)
        | uu____5011 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____5021  -> FStar_Pervasives_Native.None)
        (fun uu____5025  -> FStar_Pervasives_Native.None) k_global_def
  
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
          let uu____5072 = try_lookup_name any_val exclude_interface env lid
             in
          match uu____5072 with
          | FStar_Pervasives_Native.Some (Term_name (e,mut,attrs)) ->
              FStar_Pervasives_Native.Some (e, mut, attrs)
          | uu____5102 -> FStar_Pervasives_Native.None
  
let (drop_attributes :
  (FStar_Syntax_Syntax.term,Prims.bool,FStar_Syntax_Syntax.attribute
                                         Prims.list)
    FStar_Pervasives_Native.tuple3 FStar_Pervasives_Native.option ->
    (FStar_Syntax_Syntax.term,Prims.bool) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option)
  =
  fun x  ->
    match x with
    | FStar_Pervasives_Native.Some (t,mut,uu____5156) ->
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
      let uu____5223 = try_lookup_lid_with_attributes env l  in
      FStar_All.pipe_right uu____5223 drop_attributes
  
let (resolve_to_fully_qualified_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____5258 = try_lookup_lid env l  in
      match uu____5258 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (e,uu____5272) ->
          let uu____5277 =
            let uu____5278 = FStar_Syntax_Subst.compress e  in
            uu____5278.FStar_Syntax_Syntax.n  in
          (match uu____5277 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               FStar_Pervasives_Native.Some
                 ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
           | uu____5284 -> FStar_Pervasives_Native.None)
  
let (shorten_lid' : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____5291 = shorten_module_path env lid.FStar_Ident.ns true  in
      match uu____5291 with
      | (uu____5300,short) ->
          FStar_Ident.lid_of_ns_and_id short lid.FStar_Ident.ident
  
let (shorten_lid : env -> FStar_Ident.lid -> FStar_Ident.lid) =
  fun env  ->
    fun lid  ->
      match env.curmodule with
      | FStar_Pervasives_Native.None  -> shorten_lid' env lid
      | uu____5316 ->
          let lid_without_ns =
            FStar_Ident.lid_of_ns_and_id [] lid.FStar_Ident.ident  in
          let uu____5320 = resolve_to_fully_qualified_name env lid_without_ns
             in
          (match uu____5320 with
           | FStar_Pervasives_Native.Some lid' when
               lid'.FStar_Ident.str = lid.FStar_Ident.str -> lid_without_ns
           | uu____5324 -> shorten_lid' env lid)
  
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
        let uu___123_5354 = env  in
        {
          curmodule = (uu___123_5354.curmodule);
          curmonad = (uu___123_5354.curmonad);
          modules = (uu___123_5354.modules);
          scope_mods = [];
          exported_ids = empty_exported_id_smap;
          trans_exported_ids = (uu___123_5354.trans_exported_ids);
          includes = empty_include_smap;
          sigaccum = (uu___123_5354.sigaccum);
          sigmap = (uu___123_5354.sigmap);
          iface = (uu___123_5354.iface);
          admitted_iface = (uu___123_5354.admitted_iface);
          expect_typ = (uu___123_5354.expect_typ);
          docs = (uu___123_5354.docs);
          remaining_iface_decls = (uu___123_5354.remaining_iface_decls);
          syntax_only = (uu___123_5354.syntax_only);
          ds_hooks = (uu___123_5354.ds_hooks)
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
      let uu____5373 = try_lookup_lid_with_attributes_no_resolve env l  in
      FStar_All.pipe_right uu____5373 drop_attributes
  
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
      let k_global_def lid1 uu___104_5428 =
        match uu___104_5428 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____5435,uu____5436,uu____5437);
             FStar_Syntax_Syntax.sigrng = uu____5438;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____5440;
             FStar_Syntax_Syntax.sigattrs = uu____5441;_},uu____5442)
            ->
            let uu____5447 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___103_5451  ->
                      match uu___103_5451 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | uu____5452 -> false))
               in
            if uu____5447
            then
              let uu____5455 =
                FStar_Syntax_Syntax.lid_as_fv lid1
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Pervasives_Native.Some uu____5455
            else FStar_Pervasives_Native.None
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
               uu____5457;
             FStar_Syntax_Syntax.sigrng = uu____5458;
             FStar_Syntax_Syntax.sigquals = uu____5459;
             FStar_Syntax_Syntax.sigmeta = uu____5460;
             FStar_Syntax_Syntax.sigattrs = uu____5461;_},uu____5462)
            ->
            let uu____5481 =
              FStar_Syntax_Syntax.lid_as_fv lid1
                FStar_Syntax_Syntax.Delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
               in
            FStar_Pervasives_Native.Some uu____5481
        | uu____5482 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____5488  -> FStar_Pervasives_Native.None)
        (fun uu____5490  -> FStar_Pervasives_Native.None) k_global_def
  
let (find_all_datacons :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___105_5515 =
        match uu___105_5515 with
        | ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_inductive_typ
               (uu____5524,uu____5525,uu____5526,uu____5527,datas,uu____5529);
             FStar_Syntax_Syntax.sigrng = uu____5530;
             FStar_Syntax_Syntax.sigquals = uu____5531;
             FStar_Syntax_Syntax.sigmeta = uu____5532;
             FStar_Syntax_Syntax.sigattrs = uu____5533;_},uu____5534)
            -> FStar_Pervasives_Native.Some datas
        | uu____5549 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____5559  -> FStar_Pervasives_Native.None)
        (fun uu____5563  -> FStar_Pervasives_Native.None) k_global_def
  
let (record_cache_aux_with_filter :
  ((Prims.unit -> Prims.unit,Prims.unit -> Prims.unit,Prims.unit ->
                                                        record_or_dc
                                                          Prims.list,
     record_or_dc -> Prims.unit) FStar_Pervasives_Native.tuple4,Prims.unit ->
                                                                  Prims.unit)
    FStar_Pervasives_Native.tuple2)
  =
  let record_cache = FStar_Util.mk_ref [[]]  in
  let push1 uu____5608 =
    let uu____5609 =
      let uu____5614 =
        let uu____5617 = FStar_ST.op_Bang record_cache  in
        FStar_List.hd uu____5617  in
      let uu____5673 = FStar_ST.op_Bang record_cache  in uu____5614 ::
        uu____5673
       in
    FStar_ST.op_Colon_Equals record_cache uu____5609  in
  let pop1 uu____5781 =
    let uu____5782 =
      let uu____5787 = FStar_ST.op_Bang record_cache  in
      FStar_List.tl uu____5787  in
    FStar_ST.op_Colon_Equals record_cache uu____5782  in
  let peek1 uu____5897 =
    let uu____5898 = FStar_ST.op_Bang record_cache  in
    FStar_List.hd uu____5898  in
  let insert r =
    let uu____5958 =
      let uu____5963 = let uu____5966 = peek1 ()  in r :: uu____5966  in
      let uu____5969 =
        let uu____5974 = FStar_ST.op_Bang record_cache  in
        FStar_List.tl uu____5974  in
      uu____5963 :: uu____5969  in
    FStar_ST.op_Colon_Equals record_cache uu____5958  in
  let filter1 uu____6084 =
    let rc = peek1 ()  in
    let filtered =
      FStar_List.filter
        (fun r  -> Prims.op_Negation r.is_private_or_abstract) rc
       in
    let uu____6093 =
      let uu____6098 =
        let uu____6103 = FStar_ST.op_Bang record_cache  in
        FStar_List.tl uu____6103  in
      filtered :: uu____6098  in
    FStar_ST.op_Colon_Equals record_cache uu____6093  in
  let aux = (push1, pop1, peek1, insert)  in (aux, filter1) 
let (record_cache_aux :
  (Prims.unit -> Prims.unit,Prims.unit -> Prims.unit,Prims.unit ->
                                                       record_or_dc
                                                         Prims.list,record_or_dc
                                                                    ->
                                                                    Prims.unit)
    FStar_Pervasives_Native.tuple4)
  =
  let uu____6277 = record_cache_aux_with_filter  in
  match uu____6277 with | (aux,uu____6321) -> aux 
let (filter_record_cache : Prims.unit -> Prims.unit) =
  let uu____6364 = record_cache_aux_with_filter  in
  match uu____6364 with | (uu____6391,filter1) -> filter1 
let (push_record_cache : Prims.unit -> Prims.unit) =
  let uu____6435 = record_cache_aux  in
  match uu____6435 with | (push1,uu____6457,uu____6458,uu____6459) -> push1 
let (pop_record_cache : Prims.unit -> Prims.unit) =
  let uu____6482 = record_cache_aux  in
  match uu____6482 with | (uu____6503,pop1,uu____6505,uu____6506) -> pop1 
let (peek_record_cache : Prims.unit -> record_or_dc Prims.list) =
  let uu____6531 = record_cache_aux  in
  match uu____6531 with | (uu____6554,uu____6555,peek1,uu____6557) -> peek1 
let (insert_record_cache : record_or_dc -> Prims.unit) =
  let uu____6580 = record_cache_aux  in
  match uu____6580 with | (uu____6601,uu____6602,uu____6603,insert) -> insert 
let (extract_record :
  env ->
    scope_mod Prims.list FStar_ST.ref ->
      FStar_Syntax_Syntax.sigelt -> Prims.unit)
  =
  fun e  ->
    fun new_globs  ->
      fun se  ->
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_bundle (sigs,uu____6665) ->
            let is_record =
              FStar_Util.for_some
                (fun uu___106_6681  ->
                   match uu___106_6681 with
                   | FStar_Syntax_Syntax.RecordType uu____6682 -> true
                   | FStar_Syntax_Syntax.RecordConstructor uu____6691 -> true
                   | uu____6700 -> false)
               in
            let find_dc dc =
              FStar_All.pipe_right sigs
                (FStar_Util.find_opt
                   (fun uu___107_6722  ->
                      match uu___107_6722 with
                      | {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_datacon
                            (lid,uu____6724,uu____6725,uu____6726,uu____6727,uu____6728);
                          FStar_Syntax_Syntax.sigrng = uu____6729;
                          FStar_Syntax_Syntax.sigquals = uu____6730;
                          FStar_Syntax_Syntax.sigmeta = uu____6731;
                          FStar_Syntax_Syntax.sigattrs = uu____6732;_} ->
                          FStar_Ident.lid_equals dc lid
                      | uu____6741 -> false))
               in
            FStar_All.pipe_right sigs
              (FStar_List.iter
                 (fun uu___108_6776  ->
                    match uu___108_6776 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ
                          (typename,univs1,parms,uu____6780,uu____6781,dc::[]);
                        FStar_Syntax_Syntax.sigrng = uu____6783;
                        FStar_Syntax_Syntax.sigquals = typename_quals;
                        FStar_Syntax_Syntax.sigmeta = uu____6785;
                        FStar_Syntax_Syntax.sigattrs = uu____6786;_} ->
                        let uu____6797 =
                          let uu____6798 = find_dc dc  in
                          FStar_All.pipe_left FStar_Util.must uu____6798  in
                        (match uu____6797 with
                         | {
                             FStar_Syntax_Syntax.sigel =
                               FStar_Syntax_Syntax.Sig_datacon
                               (constrname,uu____6804,t,uu____6806,uu____6807,uu____6808);
                             FStar_Syntax_Syntax.sigrng = uu____6809;
                             FStar_Syntax_Syntax.sigquals = uu____6810;
                             FStar_Syntax_Syntax.sigmeta = uu____6811;
                             FStar_Syntax_Syntax.sigattrs = uu____6812;_} ->
                             let uu____6821 =
                               FStar_Syntax_Util.arrow_formals t  in
                             (match uu____6821 with
                              | (formals,uu____6835) ->
                                  let is_rec = is_record typename_quals  in
                                  let formals' =
                                    FStar_All.pipe_right formals
                                      (FStar_List.collect
                                         (fun uu____6884  ->
                                            match uu____6884 with
                                            | (x,q) ->
                                                let uu____6897 =
                                                  (FStar_Syntax_Syntax.is_null_bv
                                                     x)
                                                    ||
                                                    (is_rec &&
                                                       (FStar_Syntax_Syntax.is_implicit
                                                          q))
                                                   in
                                                if uu____6897
                                                then []
                                                else [(x, q)]))
                                     in
                                  let fields' =
                                    FStar_All.pipe_right formals'
                                      (FStar_List.map
                                         (fun uu____6954  ->
                                            match uu____6954 with
                                            | (x,q) ->
                                                let uu____6967 =
                                                  if is_rec
                                                  then
                                                    FStar_Syntax_Util.unmangle_field_name
                                                      x.FStar_Syntax_Syntax.ppname
                                                  else
                                                    x.FStar_Syntax_Syntax.ppname
                                                   in
                                                (uu____6967,
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
                                  ((let uu____6982 =
                                      let uu____6985 =
                                        FStar_ST.op_Bang new_globs  in
                                      (Record_or_dc record) :: uu____6985  in
                                    FStar_ST.op_Colon_Equals new_globs
                                      uu____6982);
                                   (match () with
                                    | () ->
                                        ((let add_field uu____7088 =
                                            match uu____7088 with
                                            | (id1,uu____7096) ->
                                                let modul =
                                                  let uu____7102 =
                                                    FStar_Ident.lid_of_ids
                                                      constrname.FStar_Ident.ns
                                                     in
                                                  uu____7102.FStar_Ident.str
                                                   in
                                                let uu____7103 =
                                                  get_exported_id_set e modul
                                                   in
                                                (match uu____7103 with
                                                 | FStar_Pervasives_Native.Some
                                                     my_ex ->
                                                     let my_exported_ids =
                                                       my_ex
                                                         Exported_id_field
                                                        in
                                                     ((let uu____7134 =
                                                         let uu____7135 =
                                                           FStar_ST.op_Bang
                                                             my_exported_ids
                                                            in
                                                         FStar_Util.set_add
                                                           id1.FStar_Ident.idText
                                                           uu____7135
                                                          in
                                                       FStar_ST.op_Colon_Equals
                                                         my_exported_ids
                                                         uu____7134);
                                                      (match () with
                                                       | () ->
                                                           let projname =
                                                             let uu____7221 =
                                                               let uu____7222
                                                                 =
                                                                 FStar_Syntax_Util.mk_field_projector_name_from_ident
                                                                   constrname
                                                                   id1
                                                                  in
                                                               uu____7222.FStar_Ident.ident
                                                                in
                                                             uu____7221.FStar_Ident.idText
                                                              in
                                                           let uu____7224 =
                                                             let uu____7225 =
                                                               FStar_ST.op_Bang
                                                                 my_exported_ids
                                                                in
                                                             FStar_Util.set_add
                                                               projname
                                                               uu____7225
                                                              in
                                                           FStar_ST.op_Colon_Equals
                                                             my_exported_ids
                                                             uu____7224))
                                                 | FStar_Pervasives_Native.None
                                                      -> ())
                                             in
                                          FStar_List.iter add_field fields');
                                         (match () with
                                          | () -> insert_record_cache record)))))
                         | uu____7320 -> ())
                    | uu____7321 -> ()))
        | uu____7322 -> ()
  
let (try_lookup_record_or_dc_by_field_name :
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option) =
  fun env  ->
    fun fieldname  ->
      let find_in_cache fieldname1 =
        let uu____7337 =
          ((fieldname1.FStar_Ident.ns), (fieldname1.FStar_Ident.ident))  in
        match uu____7337 with
        | (ns,id1) ->
            let uu____7354 = peek_record_cache ()  in
            FStar_Util.find_map uu____7354
              (fun record  ->
                 let uu____7360 =
                   find_in_record ns id1 record (fun r  -> Cont_ok r)  in
                 option_of_cont
                   (fun uu____7366  -> FStar_Pervasives_Native.None)
                   uu____7360)
         in
      resolve_in_open_namespaces'' env fieldname Exported_id_field
        (fun uu____7368  -> Cont_ignore) (fun uu____7370  -> Cont_ignore)
        (fun r  -> Cont_ok r)
        (fun fn  ->
           let uu____7376 = find_in_cache fn  in
           cont_of_option Cont_ignore uu____7376)
        (fun k  -> fun uu____7382  -> k)
  
let (try_lookup_record_by_field_name :
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option) =
  fun env  ->
    fun fieldname  ->
      let uu____7393 = try_lookup_record_or_dc_by_field_name env fieldname
         in
      match uu____7393 with
      | FStar_Pervasives_Native.Some r when r.is_record ->
          FStar_Pervasives_Native.Some r
      | uu____7399 -> FStar_Pervasives_Native.None
  
let (belongs_to_record :
  env -> FStar_Ident.lident -> record_or_dc -> Prims.bool) =
  fun env  ->
    fun lid  ->
      fun record  ->
        let uu____7411 = try_lookup_record_by_field_name env lid  in
        match uu____7411 with
        | FStar_Pervasives_Native.Some record' when
            let uu____7415 =
              let uu____7416 =
                FStar_Ident.path_of_ns (record.typename).FStar_Ident.ns  in
              FStar_Ident.text_of_path uu____7416  in
            let uu____7417 =
              let uu____7418 =
                FStar_Ident.path_of_ns (record'.typename).FStar_Ident.ns  in
              FStar_Ident.text_of_path uu____7418  in
            uu____7415 = uu____7417 ->
            let uu____7419 =
              find_in_record (record.typename).FStar_Ident.ns
                lid.FStar_Ident.ident record (fun uu____7423  -> Cont_ok ())
               in
            (match uu____7419 with
             | Cont_ok uu____7424 -> true
             | uu____7425 -> false)
        | uu____7428 -> false
  
let (try_lookup_dc_by_field_name :
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident,Prims.bool) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun fieldname  ->
      let uu____7443 = try_lookup_record_or_dc_by_field_name env fieldname
         in
      match uu____7443 with
      | FStar_Pervasives_Native.Some r ->
          let uu____7453 =
            let uu____7458 =
              let uu____7459 =
                FStar_Ident.lid_of_ids
                  (FStar_List.append (r.typename).FStar_Ident.ns
                     [r.constrname])
                 in
              let uu____7460 = FStar_Ident.range_of_lid fieldname  in
              FStar_Ident.set_lid_range uu____7459 uu____7460  in
            (uu____7458, (r.is_record))  in
          FStar_Pervasives_Native.Some uu____7453
      | uu____7465 -> FStar_Pervasives_Native.None
  
let (string_set_ref_new :
  Prims.unit -> Prims.string FStar_Util.set FStar_ST.ref) =
  fun uu____7489  ->
    let uu____7490 = FStar_Util.new_set FStar_Util.compare  in
    FStar_Util.mk_ref uu____7490
  
let (exported_id_set_new :
  Prims.unit -> exported_id_kind -> Prims.string FStar_Util.set FStar_ST.ref)
  =
  fun uu____7514  ->
    let term_type_set = string_set_ref_new ()  in
    let field_set = string_set_ref_new ()  in
    fun uu___109_7525  ->
      match uu___109_7525 with
      | Exported_id_term_type  -> term_type_set
      | Exported_id_field  -> field_set
  
let (unique :
  Prims.bool -> Prims.bool -> env -> FStar_Ident.lident -> Prims.bool) =
  fun any_val  ->
    fun exclude_interface  ->
      fun env  ->
        fun lid  ->
          let filter_scope_mods uu___110_7567 =
            match uu___110_7567 with
            | Rec_binding uu____7568 -> true
            | uu____7569 -> false  in
          let this_env =
            let uu___124_7571 = env  in
            let uu____7572 =
              FStar_List.filter filter_scope_mods env.scope_mods  in
            {
              curmodule = (uu___124_7571.curmodule);
              curmonad = (uu___124_7571.curmonad);
              modules = (uu___124_7571.modules);
              scope_mods = uu____7572;
              exported_ids = empty_exported_id_smap;
              trans_exported_ids = (uu___124_7571.trans_exported_ids);
              includes = empty_include_smap;
              sigaccum = (uu___124_7571.sigaccum);
              sigmap = (uu___124_7571.sigmap);
              iface = (uu___124_7571.iface);
              admitted_iface = (uu___124_7571.admitted_iface);
              expect_typ = (uu___124_7571.expect_typ);
              docs = (uu___124_7571.docs);
              remaining_iface_decls = (uu___124_7571.remaining_iface_decls);
              syntax_only = (uu___124_7571.syntax_only);
              ds_hooks = (uu___124_7571.ds_hooks)
            }  in
          let uu____7575 =
            try_lookup_lid' any_val exclude_interface this_env lid  in
          match uu____7575 with
          | FStar_Pervasives_Native.None  -> true
          | FStar_Pervasives_Native.Some uu____7594 -> false
  
let (push_scope_mod : env -> scope_mod -> env) =
  fun env  ->
    fun scope_mod  ->
      let uu___125_7617 = env  in
      {
        curmodule = (uu___125_7617.curmodule);
        curmonad = (uu___125_7617.curmonad);
        modules = (uu___125_7617.modules);
        scope_mods = (scope_mod :: (env.scope_mods));
        exported_ids = (uu___125_7617.exported_ids);
        trans_exported_ids = (uu___125_7617.trans_exported_ids);
        includes = (uu___125_7617.includes);
        sigaccum = (uu___125_7617.sigaccum);
        sigmap = (uu___125_7617.sigmap);
        iface = (uu___125_7617.iface);
        admitted_iface = (uu___125_7617.admitted_iface);
        expect_typ = (uu___125_7617.expect_typ);
        docs = (uu___125_7617.docs);
        remaining_iface_decls = (uu___125_7617.remaining_iface_decls);
        syntax_only = (uu___125_7617.syntax_only);
        ds_hooks = (uu___125_7617.ds_hooks)
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
        let uu____7662 =
          (unique false true env l) || (FStar_Options.interactive ())  in
        if uu____7662
        then push_scope_mod env (Rec_binding (x, l, dd))
        else
          (let uu____7664 = FStar_Ident.range_of_lid l  in
           FStar_Errors.raise_error
             (FStar_Errors.Fatal_DuplicateTopLevelNames,
               (Prims.strcat "Duplicate top-level names " l.FStar_Ident.str))
             uu____7664)
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let err l =
        let sopt = FStar_Util.smap_try_find (sigmap env) l.FStar_Ident.str
           in
        let r =
          match sopt with
          | FStar_Pervasives_Native.Some (se,uu____7688) ->
              let uu____7693 =
                FStar_Util.find_opt (FStar_Ident.lid_equals l)
                  (FStar_Syntax_Util.lids_of_sigelt se)
                 in
              (match uu____7693 with
               | FStar_Pervasives_Native.Some l1 ->
                   let uu____7697 = FStar_Ident.range_of_lid l1  in
                   FStar_All.pipe_left FStar_Range.string_of_range uu____7697
               | FStar_Pervasives_Native.None  -> "<unknown>")
          | FStar_Pervasives_Native.None  -> "<unknown>"  in
        let uu____7702 =
          let uu____7707 =
            let uu____7708 = FStar_Ident.text_of_lid l  in
            FStar_Util.format2
              "Duplicate top-level names [%s]; previously declared at %s"
              uu____7708 r
             in
          (FStar_Errors.Fatal_DuplicateTopLevelNames, uu____7707)  in
        let uu____7709 = FStar_Ident.range_of_lid l  in
        FStar_Errors.raise_error uu____7702 uu____7709  in
      let globals = FStar_Util.mk_ref env.scope_mods  in
      let env1 =
        let uu____7718 =
          match s.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let uu____7727 -> (false, true)
          | FStar_Syntax_Syntax.Sig_bundle uu____7734 -> (false, true)
          | uu____7743 -> (false, false)  in
        match uu____7718 with
        | (any_val,exclude_interface) ->
            let lids = FStar_Syntax_Util.lids_of_sigelt s  in
            let uu____7749 =
              FStar_Util.find_map lids
                (fun l  ->
                   let uu____7755 =
                     let uu____7756 = unique any_val exclude_interface env l
                        in
                     Prims.op_Negation uu____7756  in
                   if uu____7755
                   then FStar_Pervasives_Native.Some l
                   else FStar_Pervasives_Native.None)
               in
            (match uu____7749 with
             | FStar_Pervasives_Native.Some l -> err l
             | uu____7761 ->
                 (extract_record env globals s;
                  (let uu___126_7787 = env  in
                   {
                     curmodule = (uu___126_7787.curmodule);
                     curmonad = (uu___126_7787.curmonad);
                     modules = (uu___126_7787.modules);
                     scope_mods = (uu___126_7787.scope_mods);
                     exported_ids = (uu___126_7787.exported_ids);
                     trans_exported_ids = (uu___126_7787.trans_exported_ids);
                     includes = (uu___126_7787.includes);
                     sigaccum = (s :: (env.sigaccum));
                     sigmap = (uu___126_7787.sigmap);
                     iface = (uu___126_7787.iface);
                     admitted_iface = (uu___126_7787.admitted_iface);
                     expect_typ = (uu___126_7787.expect_typ);
                     docs = (uu___126_7787.docs);
                     remaining_iface_decls =
                       (uu___126_7787.remaining_iface_decls);
                     syntax_only = (uu___126_7787.syntax_only);
                     ds_hooks = (uu___126_7787.ds_hooks)
                   })))
         in
      let env2 =
        let uu___127_7789 = env1  in
        let uu____7790 = FStar_ST.op_Bang globals  in
        {
          curmodule = (uu___127_7789.curmodule);
          curmonad = (uu___127_7789.curmonad);
          modules = (uu___127_7789.modules);
          scope_mods = uu____7790;
          exported_ids = (uu___127_7789.exported_ids);
          trans_exported_ids = (uu___127_7789.trans_exported_ids);
          includes = (uu___127_7789.includes);
          sigaccum = (uu___127_7789.sigaccum);
          sigmap = (uu___127_7789.sigmap);
          iface = (uu___127_7789.iface);
          admitted_iface = (uu___127_7789.admitted_iface);
          expect_typ = (uu___127_7789.expect_typ);
          docs = (uu___127_7789.docs);
          remaining_iface_decls = (uu___127_7789.remaining_iface_decls);
          syntax_only = (uu___127_7789.syntax_only);
          ds_hooks = (uu___127_7789.ds_hooks)
        }  in
      let uu____7838 =
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_bundle (ses,uu____7864) ->
            let uu____7873 =
              FStar_List.map
                (fun se  -> ((FStar_Syntax_Util.lids_of_sigelt se), se)) ses
               in
            (env2, uu____7873)
        | uu____7900 -> (env2, [((FStar_Syntax_Util.lids_of_sigelt s), s)])
         in
      match uu____7838 with
      | (env3,lss) ->
          (FStar_All.pipe_right lss
             (FStar_List.iter
                (fun uu____7959  ->
                   match uu____7959 with
                   | (lids,se) ->
                       FStar_All.pipe_right lids
                         (FStar_List.iter
                            (fun lid  ->
                               (let uu____7981 =
                                  let uu____7984 = FStar_ST.op_Bang globals
                                     in
                                  (Top_level_def (lid.FStar_Ident.ident)) ::
                                    uu____7984
                                   in
                                FStar_ST.op_Colon_Equals globals uu____7981);
                               (match () with
                                | () ->
                                    let modul =
                                      let uu____8078 =
                                        FStar_Ident.lid_of_ids
                                          lid.FStar_Ident.ns
                                         in
                                      uu____8078.FStar_Ident.str  in
                                    ((let uu____8080 =
                                        get_exported_id_set env3 modul  in
                                      match uu____8080 with
                                      | FStar_Pervasives_Native.Some f ->
                                          let my_exported_ids =
                                            f Exported_id_term_type  in
                                          let uu____8110 =
                                            let uu____8111 =
                                              FStar_ST.op_Bang
                                                my_exported_ids
                                               in
                                            FStar_Util.set_add
                                              (lid.FStar_Ident.ident).FStar_Ident.idText
                                              uu____8111
                                             in
                                          FStar_ST.op_Colon_Equals
                                            my_exported_ids uu____8110
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
              let uu___128_8206 = env3  in
              let uu____8207 = FStar_ST.op_Bang globals  in
              {
                curmodule = (uu___128_8206.curmodule);
                curmonad = (uu___128_8206.curmonad);
                modules = (uu___128_8206.modules);
                scope_mods = uu____8207;
                exported_ids = (uu___128_8206.exported_ids);
                trans_exported_ids = (uu___128_8206.trans_exported_ids);
                includes = (uu___128_8206.includes);
                sigaccum = (uu___128_8206.sigaccum);
                sigmap = (uu___128_8206.sigmap);
                iface = (uu___128_8206.iface);
                admitted_iface = (uu___128_8206.admitted_iface);
                expect_typ = (uu___128_8206.expect_typ);
                docs = (uu___128_8206.docs);
                remaining_iface_decls = (uu___128_8206.remaining_iface_decls);
                syntax_only = (uu___128_8206.syntax_only);
                ds_hooks = (uu___128_8206.ds_hooks)
              }  in
            env4))
  
let (push_namespace : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun ns  ->
      let uu____8261 =
        let uu____8266 = resolve_module_name env ns false  in
        match uu____8266 with
        | FStar_Pervasives_Native.None  ->
            let modules = env.modules  in
            let uu____8280 =
              FStar_All.pipe_right modules
                (FStar_Util.for_some
                   (fun uu____8296  ->
                      match uu____8296 with
                      | (m,uu____8302) ->
                          let uu____8303 =
                            let uu____8304 = FStar_Ident.text_of_lid m  in
                            Prims.strcat uu____8304 "."  in
                          let uu____8305 =
                            let uu____8306 = FStar_Ident.text_of_lid ns  in
                            Prims.strcat uu____8306 "."  in
                          FStar_Util.starts_with uu____8303 uu____8305))
               in
            if uu____8280
            then (ns, Open_namespace)
            else
              (let uu____8312 =
                 let uu____8317 =
                   let uu____8318 = FStar_Ident.text_of_lid ns  in
                   FStar_Util.format1 "Namespace %s cannot be found"
                     uu____8318
                    in
                 (FStar_Errors.Fatal_NameSpaceNotFound, uu____8317)  in
               let uu____8319 = FStar_Ident.range_of_lid ns  in
               FStar_Errors.raise_error uu____8312 uu____8319)
        | FStar_Pervasives_Native.Some ns' ->
            (fail_if_curmodule env ns ns'; (ns', Open_module))
         in
      match uu____8261 with
      | (ns',kd) ->
          ((env.ds_hooks).ds_push_open_hook env (ns', kd);
           push_scope_mod env (Open_module_or_namespace (ns', kd)))
  
let (push_include : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun ns  ->
      let ns0 = ns  in
      let uu____8336 = resolve_module_name env ns false  in
      match uu____8336 with
      | FStar_Pervasives_Native.Some ns1 ->
          ((env.ds_hooks).ds_push_include_hook env ns1;
           fail_if_curmodule env ns0 ns1;
           (let env1 =
              push_scope_mod env
                (Open_module_or_namespace (ns1, Open_module))
               in
            let curmod =
              let uu____8344 = current_module env1  in
              uu____8344.FStar_Ident.str  in
            (let uu____8346 = FStar_Util.smap_try_find env1.includes curmod
                in
             match uu____8346 with
             | FStar_Pervasives_Native.None  -> ()
             | FStar_Pervasives_Native.Some incl ->
                 let uu____8370 =
                   let uu____8373 = FStar_ST.op_Bang incl  in ns1 ::
                     uu____8373
                    in
                 FStar_ST.op_Colon_Equals incl uu____8370);
            (match () with
             | () ->
                 let uu____8466 =
                   get_trans_exported_id_set env1 ns1.FStar_Ident.str  in
                 (match uu____8466 with
                  | FStar_Pervasives_Native.Some ns_trans_exports ->
                      ((let uu____8483 =
                          let uu____8500 = get_exported_id_set env1 curmod
                             in
                          let uu____8507 =
                            get_trans_exported_id_set env1 curmod  in
                          (uu____8500, uu____8507)  in
                        match uu____8483 with
                        | (FStar_Pervasives_Native.Some
                           cur_exports,FStar_Pervasives_Native.Some
                           cur_trans_exports) ->
                            let update_exports k =
                              let ns_ex =
                                let uu____8561 = ns_trans_exports k  in
                                FStar_ST.op_Bang uu____8561  in
                              let ex = cur_exports k  in
                              (let uu____8687 =
                                 let uu____8688 = FStar_ST.op_Bang ex  in
                                 FStar_Util.set_difference uu____8688 ns_ex
                                  in
                               FStar_ST.op_Colon_Equals ex uu____8687);
                              (match () with
                               | () ->
                                   let trans_ex = cur_trans_exports k  in
                                   let uu____8788 =
                                     let uu____8789 =
                                       FStar_ST.op_Bang trans_ex  in
                                     FStar_Util.set_union uu____8789 ns_ex
                                      in
                                   FStar_ST.op_Colon_Equals trans_ex
                                     uu____8788)
                               in
                            FStar_List.iter update_exports
                              all_exported_id_kinds
                        | uu____8874 -> ());
                       (match () with | () -> env1))
                  | FStar_Pervasives_Native.None  ->
                      let uu____8895 =
                        let uu____8900 =
                          FStar_Util.format1
                            "include: Module %s was not prepared"
                            ns1.FStar_Ident.str
                           in
                        (FStar_Errors.Fatal_IncludeModuleNotPrepared,
                          uu____8900)
                         in
                      let uu____8901 = FStar_Ident.range_of_lid ns1  in
                      FStar_Errors.raise_error uu____8895 uu____8901))))
      | uu____8902 ->
          let uu____8905 =
            let uu____8910 =
              FStar_Util.format1 "include: Module %s cannot be found"
                ns.FStar_Ident.str
               in
            (FStar_Errors.Fatal_ModuleNotFound, uu____8910)  in
          let uu____8911 = FStar_Ident.range_of_lid ns  in
          FStar_Errors.raise_error uu____8905 uu____8911
  
let (push_module_abbrev :
  env -> FStar_Ident.ident -> FStar_Ident.lident -> env) =
  fun env  ->
    fun x  ->
      fun l  ->
        let uu____8921 = module_is_defined env l  in
        if uu____8921
        then
          (fail_if_curmodule env l l;
           (env.ds_hooks).ds_push_module_abbrev_hook env x l;
           push_scope_mod env (Module_abbrev (x, l)))
        else
          (let uu____8925 =
             let uu____8930 =
               let uu____8931 = FStar_Ident.text_of_lid l  in
               FStar_Util.format1 "Module %s cannot be found" uu____8931  in
             (FStar_Errors.Fatal_ModuleNotFound, uu____8930)  in
           let uu____8932 = FStar_Ident.range_of_lid l  in
           FStar_Errors.raise_error uu____8925 uu____8932)
  
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
            ((let uu____8948 =
                FStar_Util.smap_try_find env.docs l.FStar_Ident.str  in
              match uu____8948 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some old_doc ->
                  let uu____8952 = FStar_Ident.range_of_lid l  in
                  let uu____8953 =
                    let uu____8958 =
                      let uu____8959 = FStar_Ident.string_of_lid l  in
                      let uu____8960 =
                        FStar_Parser_AST.string_of_fsdoc old_doc  in
                      let uu____8961 = FStar_Parser_AST.string_of_fsdoc doc1
                         in
                      FStar_Util.format3
                        "Overwriting doc of %s; old doc was [%s]; new doc are [%s]"
                        uu____8959 uu____8960 uu____8961
                       in
                    (FStar_Errors.Warning_DocOverwrite, uu____8958)  in
                  FStar_Errors.log_issue uu____8952 uu____8953);
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
                      let uu____8997 =
                        FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption)
                         in
                      Prims.op_Negation uu____8997 ->
                      let uu____9000 =
                        FStar_Util.smap_try_find (sigmap env)
                          l.FStar_Ident.str
                         in
                      (match uu____9000 with
                       | FStar_Pervasives_Native.Some
                           ({
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_let uu____9013;
                              FStar_Syntax_Syntax.sigrng = uu____9014;
                              FStar_Syntax_Syntax.sigquals = uu____9015;
                              FStar_Syntax_Syntax.sigmeta = uu____9016;
                              FStar_Syntax_Syntax.sigattrs = uu____9017;_},uu____9018)
                           -> lids
                       | FStar_Pervasives_Native.Some
                           ({
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_inductive_typ
                                uu____9033;
                              FStar_Syntax_Syntax.sigrng = uu____9034;
                              FStar_Syntax_Syntax.sigquals = uu____9035;
                              FStar_Syntax_Syntax.sigmeta = uu____9036;
                              FStar_Syntax_Syntax.sigattrs = uu____9037;_},uu____9038)
                           -> lids
                       | uu____9063 ->
                           ((let uu____9071 =
                               let uu____9072 = FStar_Options.interactive ()
                                  in
                               Prims.op_Negation uu____9072  in
                             if uu____9071
                             then
                               let uu____9073 = FStar_Ident.range_of_lid l
                                  in
                               let uu____9074 =
                                 let uu____9079 =
                                   let uu____9080 =
                                     FStar_Ident.string_of_lid l  in
                                   FStar_Util.format1
                                     "Admitting %s without a definition"
                                     uu____9080
                                    in
                                 (FStar_Errors.Warning_AdmitWithoutDefinition,
                                   uu____9079)
                                  in
                               FStar_Errors.log_issue uu____9073 uu____9074
                             else ());
                            (let quals = FStar_Syntax_Syntax.Assumption ::
                               (se.FStar_Syntax_Syntax.sigquals)  in
                             FStar_Util.smap_add (sigmap env)
                               l.FStar_Ident.str
                               ((let uu___129_9091 = se  in
                                 {
                                   FStar_Syntax_Syntax.sigel =
                                     (uu___129_9091.FStar_Syntax_Syntax.sigel);
                                   FStar_Syntax_Syntax.sigrng =
                                     (uu___129_9091.FStar_Syntax_Syntax.sigrng);
                                   FStar_Syntax_Syntax.sigquals = quals;
                                   FStar_Syntax_Syntax.sigmeta =
                                     (uu___129_9091.FStar_Syntax_Syntax.sigmeta);
                                   FStar_Syntax_Syntax.sigattrs =
                                     (uu___129_9091.FStar_Syntax_Syntax.sigattrs)
                                 }), false);
                             l
                             ::
                             lids)))
                  | uu____9092 -> lids) [])
         in
      let uu___130_9093 = m  in
      let uu____9094 =
        FStar_All.pipe_right m.FStar_Syntax_Syntax.declarations
          (FStar_List.map
             (fun s  ->
                match s.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_declare_typ
                    (lid,uu____9104,uu____9105) when
                    FStar_List.existsb
                      (fun l  -> FStar_Ident.lid_equals l lid)
                      admitted_sig_lids
                    ->
                    let uu___131_9108 = s  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___131_9108.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___131_9108.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals =
                        (FStar_Syntax_Syntax.Assumption ::
                        (s.FStar_Syntax_Syntax.sigquals));
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___131_9108.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___131_9108.FStar_Syntax_Syntax.sigattrs)
                    }
                | uu____9109 -> s))
         in
      {
        FStar_Syntax_Syntax.name = (uu___130_9093.FStar_Syntax_Syntax.name);
        FStar_Syntax_Syntax.declarations = uu____9094;
        FStar_Syntax_Syntax.exports =
          (uu___130_9093.FStar_Syntax_Syntax.exports);
        FStar_Syntax_Syntax.is_interface =
          (uu___130_9093.FStar_Syntax_Syntax.is_interface)
      }
  
let (finish : env -> FStar_Syntax_Syntax.modul -> env) =
  fun env  ->
    fun modul  ->
      FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations
        (FStar_List.iter
           (fun se  ->
              let quals = se.FStar_Syntax_Syntax.sigquals  in
              match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_bundle (ses,uu____9126) ->
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
                                (lid,uu____9146,uu____9147,uu____9148,uu____9149,uu____9150)
                                ->
                                FStar_Util.smap_remove (sigmap env)
                                  lid.FStar_Ident.str
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (lid,univ_names,binders,typ,uu____9163,uu____9164)
                                ->
                                (FStar_Util.smap_remove (sigmap env)
                                   lid.FStar_Ident.str;
                                 if
                                   Prims.op_Negation
                                     (FStar_List.contains
                                        FStar_Syntax_Syntax.Private quals)
                                 then
                                   (let sigel =
                                      let uu____9179 =
                                        let uu____9186 =
                                          let uu____9189 =
                                            FStar_Ident.range_of_lid lid  in
                                          let uu____9190 =
                                            let uu____9193 =
                                              let uu____9194 =
                                                let uu____9207 =
                                                  FStar_Syntax_Syntax.mk_Total
                                                    typ
                                                   in
                                                (binders, uu____9207)  in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____9194
                                               in
                                            FStar_Syntax_Syntax.mk uu____9193
                                             in
                                          uu____9190
                                            FStar_Pervasives_Native.None
                                            uu____9189
                                           in
                                        (lid, univ_names, uu____9186)  in
                                      FStar_Syntax_Syntax.Sig_declare_typ
                                        uu____9179
                                       in
                                    let se2 =
                                      let uu___132_9214 = se1  in
                                      {
                                        FStar_Syntax_Syntax.sigel = sigel;
                                        FStar_Syntax_Syntax.sigrng =
                                          (uu___132_9214.FStar_Syntax_Syntax.sigrng);
                                        FStar_Syntax_Syntax.sigquals =
                                          (FStar_Syntax_Syntax.Assumption ::
                                          quals);
                                        FStar_Syntax_Syntax.sigmeta =
                                          (uu___132_9214.FStar_Syntax_Syntax.sigmeta);
                                        FStar_Syntax_Syntax.sigattrs =
                                          (uu___132_9214.FStar_Syntax_Syntax.sigattrs)
                                      }  in
                                    FStar_Util.smap_add (sigmap env)
                                      lid.FStar_Ident.str (se2, false))
                                 else ())
                            | uu____9220 -> ()))
                  else ()
              | FStar_Syntax_Syntax.Sig_declare_typ
                  (lid,uu____9223,uu____9224) ->
                  if FStar_List.contains FStar_Syntax_Syntax.Private quals
                  then
                    FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str
                  else ()
              | FStar_Syntax_Syntax.Sig_let ((uu____9230,lbs),uu____9232) ->
                  (if
                     (FStar_List.contains FStar_Syntax_Syntax.Private quals)
                       ||
                       (FStar_List.contains FStar_Syntax_Syntax.Abstract
                          quals)
                   then
                     FStar_All.pipe_right lbs
                       (FStar_List.iter
                          (fun lb  ->
                             let uu____9253 =
                               let uu____9254 =
                                 let uu____9255 =
                                   let uu____9258 =
                                     FStar_Util.right
                                       lb.FStar_Syntax_Syntax.lbname
                                      in
                                   uu____9258.FStar_Syntax_Syntax.fv_name  in
                                 uu____9255.FStar_Syntax_Syntax.v  in
                               uu____9254.FStar_Ident.str  in
                             FStar_Util.smap_remove (sigmap env) uu____9253))
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
                               let uu____9272 =
                                 let uu____9275 =
                                   FStar_Util.right
                                     lb.FStar_Syntax_Syntax.lbname
                                    in
                                 uu____9275.FStar_Syntax_Syntax.fv_name  in
                               uu____9272.FStar_Syntax_Syntax.v  in
                             let quals1 = FStar_Syntax_Syntax.Assumption ::
                               quals  in
                             let decl =
                               let uu___133_9280 = se  in
                               {
                                 FStar_Syntax_Syntax.sigel =
                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                      (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                        (lb.FStar_Syntax_Syntax.lbtyp)));
                                 FStar_Syntax_Syntax.sigrng =
                                   (uu___133_9280.FStar_Syntax_Syntax.sigrng);
                                 FStar_Syntax_Syntax.sigquals = quals1;
                                 FStar_Syntax_Syntax.sigmeta =
                                   (uu___133_9280.FStar_Syntax_Syntax.sigmeta);
                                 FStar_Syntax_Syntax.sigattrs =
                                   (uu___133_9280.FStar_Syntax_Syntax.sigattrs)
                               }  in
                             FStar_Util.smap_add (sigmap env)
                               lid.FStar_Ident.str (decl, false)))
                   else ())
              | uu____9290 -> ()));
      (let curmod =
         let uu____9292 = current_module env  in uu____9292.FStar_Ident.str
          in
       (let uu____9294 =
          let uu____9311 = get_exported_id_set env curmod  in
          let uu____9318 = get_trans_exported_id_set env curmod  in
          (uu____9311, uu____9318)  in
        match uu____9294 with
        | (FStar_Pervasives_Native.Some cur_ex,FStar_Pervasives_Native.Some
           cur_trans_ex) ->
            let update_exports eikind =
              let cur_ex_set =
                let uu____9372 = cur_ex eikind  in
                FStar_ST.op_Bang uu____9372  in
              let cur_trans_ex_set_ref = cur_trans_ex eikind  in
              let uu____9497 =
                let uu____9498 = FStar_ST.op_Bang cur_trans_ex_set_ref  in
                FStar_Util.set_union cur_ex_set uu____9498  in
              FStar_ST.op_Colon_Equals cur_trans_ex_set_ref uu____9497  in
            FStar_List.iter update_exports all_exported_id_kinds
        | uu____9583 -> ());
       (match () with
        | () ->
            (filter_record_cache ();
             (match () with
              | () ->
                  let uu___134_9601 = env  in
                  {
                    curmodule = FStar_Pervasives_Native.None;
                    curmonad = (uu___134_9601.curmonad);
                    modules = (((modul.FStar_Syntax_Syntax.name), modul) ::
                      (env.modules));
                    scope_mods = [];
                    exported_ids = (uu___134_9601.exported_ids);
                    trans_exported_ids = (uu___134_9601.trans_exported_ids);
                    includes = (uu___134_9601.includes);
                    sigaccum = [];
                    sigmap = (uu___134_9601.sigmap);
                    iface = (uu___134_9601.iface);
                    admitted_iface = (uu___134_9601.admitted_iface);
                    expect_typ = (uu___134_9601.expect_typ);
                    docs = (uu___134_9601.docs);
                    remaining_iface_decls =
                      (uu___134_9601.remaining_iface_decls);
                    syntax_only = (uu___134_9601.syntax_only);
                    ds_hooks = (uu___134_9601.ds_hooks)
                  }))))
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push : env -> env) =
  fun env  ->
    push_record_cache ();
    (let uu____9628 =
       let uu____9631 = FStar_ST.op_Bang stack  in env :: uu____9631  in
     FStar_ST.op_Colon_Equals stack uu____9628);
    (let uu___135_9680 = env  in
     let uu____9681 = FStar_Util.smap_copy (sigmap env)  in
     let uu____9692 = FStar_Util.smap_copy env.docs  in
     {
       curmodule = (uu___135_9680.curmodule);
       curmonad = (uu___135_9680.curmonad);
       modules = (uu___135_9680.modules);
       scope_mods = (uu___135_9680.scope_mods);
       exported_ids = (uu___135_9680.exported_ids);
       trans_exported_ids = (uu___135_9680.trans_exported_ids);
       includes = (uu___135_9680.includes);
       sigaccum = (uu___135_9680.sigaccum);
       sigmap = uu____9681;
       iface = (uu___135_9680.iface);
       admitted_iface = (uu___135_9680.admitted_iface);
       expect_typ = (uu___135_9680.expect_typ);
       docs = uu____9692;
       remaining_iface_decls = (uu___135_9680.remaining_iface_decls);
       syntax_only = (uu___135_9680.syntax_only);
       ds_hooks = (uu___135_9680.ds_hooks)
     })
  
let (pop : Prims.unit -> env) =
  fun uu____9697  ->
    let uu____9698 = FStar_ST.op_Bang stack  in
    match uu____9698 with
    | env::tl1 ->
        (pop_record_cache (); FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____9753 -> failwith "Impossible: Too many pops"
  
let (export_interface : FStar_Ident.lident -> env -> env) =
  fun m  ->
    fun env  ->
      let sigelt_in_m se =
        match FStar_Syntax_Util.lids_of_sigelt se with
        | l::uu____9767 -> l.FStar_Ident.nsstr = m.FStar_Ident.str
        | uu____9770 -> false  in
      let sm = sigmap env  in
      let env1 = pop ()  in
      let keys = FStar_Util.smap_keys sm  in
      let sm' = sigmap env1  in
      FStar_All.pipe_right keys
        (FStar_List.iter
           (fun k  ->
              let uu____9804 = FStar_Util.smap_try_find sm' k  in
              match uu____9804 with
              | FStar_Pervasives_Native.Some (se,true ) when sigelt_in_m se
                  ->
                  (FStar_Util.smap_remove sm' k;
                   (let se1 =
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t) ->
                          let uu___136_9829 = se  in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (uu___136_9829.FStar_Syntax_Syntax.sigel);
                            FStar_Syntax_Syntax.sigrng =
                              (uu___136_9829.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (FStar_Syntax_Syntax.Assumption ::
                              (se.FStar_Syntax_Syntax.sigquals));
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___136_9829.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___136_9829.FStar_Syntax_Syntax.sigattrs)
                          }
                      | uu____9830 -> se  in
                    FStar_Util.smap_add sm' k (se1, false)))
              | uu____9835 -> ()));
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
      let uu____9854 = finish env modul1  in (uu____9854, modul1)
  
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
      let uu____9932 =
        let uu____9935 = e Exported_id_term_type  in
        FStar_ST.op_Bang uu____9935  in
      FStar_Util.set_elements uu____9932  in
    let fields =
      let uu____10049 =
        let uu____10052 = e Exported_id_field  in
        FStar_ST.op_Bang uu____10052  in
      FStar_Util.set_elements uu____10049  in
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
          let uu____10199 =
            FStar_Util.as_set e1.exported_id_terms FStar_Util.compare  in
          FStar_Util.mk_ref uu____10199  in
        let fields =
          let uu____10209 =
            FStar_Util.as_set e1.exported_id_fields FStar_Util.compare  in
          FStar_Util.mk_ref uu____10209  in
        (fun uu___111_10214  ->
           match uu___111_10214 with
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
  'Auu____10334 .
    'Auu____10334 Prims.list FStar_Pervasives_Native.option ->
      'Auu____10334 Prims.list FStar_ST.ref
  =
  fun uu___112_10346  ->
    match uu___112_10346 with
    | FStar_Pervasives_Native.None  -> FStar_Util.mk_ref []
    | FStar_Pervasives_Native.Some l -> FStar_Util.mk_ref l
  
let (inclusion_info : env -> FStar_Ident.lident -> module_inclusion_info) =
  fun env  ->
    fun l  ->
      let mname = FStar_Ident.string_of_lid l  in
      let as_ids_opt m =
        let uu____10379 = FStar_Util.smap_try_find m mname  in
        FStar_Util.map_opt uu____10379 as_exported_ids  in
      let uu____10382 = as_ids_opt env.exported_ids  in
      let uu____10385 = as_ids_opt env.trans_exported_ids  in
      let uu____10388 =
        let uu____10393 = FStar_Util.smap_try_find env.includes mname  in
        FStar_Util.map_opt uu____10393 (fun r  -> FStar_ST.op_Bang r)  in
      {
        mii_exported_ids = uu____10382;
        mii_trans_exported_ids = uu____10385;
        mii_includes = uu____10388
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
                let uu____10496 = FStar_Ident.text_of_lid mname  in
                FStar_Util.strcat uu____10496 ".fst"  in
              let auto_open =
                FStar_Parser_Dep.hard_coded_dependencies filename  in
              let auto_open1 =
                let convert_kind uu___113_10514 =
                  match uu___113_10514 with
                  | FStar_Parser_Dep.Open_namespace  -> Open_namespace
                  | FStar_Parser_Dep.Open_module  -> Open_module  in
                FStar_List.map
                  (fun uu____10526  ->
                     match uu____10526 with
                     | (lid,kind) -> (lid, (convert_kind kind))) auto_open
                 in
              let namespace_of_module =
                if
                  (FStar_List.length mname.FStar_Ident.ns) >
                    (Prims.parse_int "0")
                then
                  let uu____10550 =
                    let uu____10555 =
                      FStar_Ident.lid_of_ids mname.FStar_Ident.ns  in
                    (uu____10555, Open_namespace)  in
                  [uu____10550]
                else []  in
              let auto_open2 =
                FStar_List.append namespace_of_module
                  (FStar_List.rev auto_open1)
                 in
              (let uu____10585 = as_exported_id_set mii.mii_exported_ids  in
               FStar_Util.smap_add env1.exported_ids mname.FStar_Ident.str
                 uu____10585);
              (match () with
               | () ->
                   ((let uu____10609 =
                       as_exported_id_set mii.mii_trans_exported_ids  in
                     FStar_Util.smap_add env1.trans_exported_ids
                       mname.FStar_Ident.str uu____10609);
                    (match () with
                     | () ->
                         ((let uu____10633 = as_includes mii.mii_includes  in
                           FStar_Util.smap_add env1.includes
                             mname.FStar_Ident.str uu____10633);
                          (match () with
                           | () ->
                               let env' =
                                 let uu___137_10665 = env1  in
                                 let uu____10666 =
                                   FStar_List.map
                                     (fun x  -> Open_module_or_namespace x)
                                     auto_open2
                                    in
                                 {
                                   curmodule =
                                     (FStar_Pervasives_Native.Some mname);
                                   curmonad = (uu___137_10665.curmonad);
                                   modules = (uu___137_10665.modules);
                                   scope_mods = uu____10666;
                                   exported_ids =
                                     (uu___137_10665.exported_ids);
                                   trans_exported_ids =
                                     (uu___137_10665.trans_exported_ids);
                                   includes = (uu___137_10665.includes);
                                   sigaccum = (uu___137_10665.sigaccum);
                                   sigmap = (env1.sigmap);
                                   iface = intf;
                                   admitted_iface = admitted;
                                   expect_typ = (uu___137_10665.expect_typ);
                                   docs = (uu___137_10665.docs);
                                   remaining_iface_decls =
                                     (uu___137_10665.remaining_iface_decls);
                                   syntax_only = (uu___137_10665.syntax_only);
                                   ds_hooks = (uu___137_10665.ds_hooks)
                                 }  in
                               (FStar_List.iter
                                  (fun op  ->
                                     (env1.ds_hooks).ds_push_open_hook env'
                                       op) (FStar_List.rev auto_open2);
                                env'))))))
               in
            let uu____10678 =
              FStar_All.pipe_right env.modules
                (FStar_Util.find_opt
                   (fun uu____10704  ->
                      match uu____10704 with
                      | (l,uu____10710) -> FStar_Ident.lid_equals l mname))
               in
            match uu____10678 with
            | FStar_Pervasives_Native.None  ->
                let uu____10719 = prep env  in (uu____10719, false)
            | FStar_Pervasives_Native.Some (uu____10720,m) ->
                ((let uu____10727 =
                    (let uu____10730 = FStar_Options.interactive ()  in
                     Prims.op_Negation uu____10730) &&
                      ((Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)
                         || intf)
                     in
                  if uu____10727
                  then
                    let uu____10731 =
                      let uu____10736 =
                        FStar_Util.format1
                          "Duplicate module or interface name: %s"
                          mname.FStar_Ident.str
                         in
                      (FStar_Errors.Fatal_DuplicateModuleOrInterface,
                        uu____10736)
                       in
                    let uu____10737 = FStar_Ident.range_of_lid mname  in
                    FStar_Errors.raise_error uu____10731 uu____10737
                  else ());
                 (let uu____10739 =
                    let uu____10740 = push env  in prep uu____10740  in
                  (uu____10739, true)))
  
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
          let uu___138_10748 = env  in
          {
            curmodule = (uu___138_10748.curmodule);
            curmonad = (FStar_Pervasives_Native.Some mname);
            modules = (uu___138_10748.modules);
            scope_mods = (uu___138_10748.scope_mods);
            exported_ids = (uu___138_10748.exported_ids);
            trans_exported_ids = (uu___138_10748.trans_exported_ids);
            includes = (uu___138_10748.includes);
            sigaccum = (uu___138_10748.sigaccum);
            sigmap = (uu___138_10748.sigmap);
            iface = (uu___138_10748.iface);
            admitted_iface = (uu___138_10748.admitted_iface);
            expect_typ = (uu___138_10748.expect_typ);
            docs = (uu___138_10748.docs);
            remaining_iface_decls = (uu___138_10748.remaining_iface_decls);
            syntax_only = (uu___138_10748.syntax_only);
            ds_hooks = (uu___138_10748.ds_hooks)
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
        let uu____10775 = lookup1 lid  in
        match uu____10775 with
        | FStar_Pervasives_Native.None  ->
            let opened_modules =
              FStar_List.map
                (fun uu____10788  ->
                   match uu____10788 with
                   | (lid1,uu____10794) -> FStar_Ident.text_of_lid lid1)
                env.modules
               in
            let msg =
              let uu____10796 = FStar_Ident.text_of_lid lid  in
              FStar_Util.format1 "Identifier not found: [%s]" uu____10796  in
            let msg1 =
              if
                (FStar_List.length lid.FStar_Ident.ns) =
                  (Prims.parse_int "0")
              then msg
              else
                (let modul =
                   let uu____10800 =
                     FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
                   let uu____10801 = FStar_Ident.range_of_lid lid  in
                   FStar_Ident.set_lid_range uu____10800 uu____10801  in
                 let uu____10802 = resolve_module_name env modul true  in
                 match uu____10802 with
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
            let uu____10811 = FStar_Ident.range_of_lid lid  in
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_IdentifierNotFound, msg1) uu____10811
        | FStar_Pervasives_Native.Some r -> r
  
let fail_or2 :
  'a .
    (FStar_Ident.ident -> 'a FStar_Pervasives_Native.option) ->
      FStar_Ident.ident -> 'a
  =
  fun lookup1  ->
    fun id1  ->
      let uu____10834 = lookup1 id1  in
      match uu____10834 with
      | FStar_Pervasives_Native.None  ->
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_IdentifierNotFound,
              (Prims.strcat "Identifier not found ["
                 (Prims.strcat id1.FStar_Ident.idText "]")))
            id1.FStar_Ident.idRange
      | FStar_Pervasives_Native.Some r -> r
  
let (mk_copy : env -> env) =
  fun en  ->
    let uu___139_10841 = en  in
    let uu____10842 = FStar_Util.smap_copy en.exported_ids  in
    let uu____10845 = FStar_Util.smap_copy en.trans_exported_ids  in
    let uu____10848 = FStar_Util.smap_copy en.sigmap  in
    let uu____10859 = FStar_Util.smap_copy en.docs  in
    {
      curmodule = (uu___139_10841.curmodule);
      curmonad = (uu___139_10841.curmonad);
      modules = (uu___139_10841.modules);
      scope_mods = (uu___139_10841.scope_mods);
      exported_ids = uu____10842;
      trans_exported_ids = uu____10845;
      includes = (uu___139_10841.includes);
      sigaccum = (uu___139_10841.sigaccum);
      sigmap = uu____10848;
      iface = (uu___139_10841.iface);
      admitted_iface = (uu___139_10841.admitted_iface);
      expect_typ = (uu___139_10841.expect_typ);
      docs = uu____10859;
      remaining_iface_decls = (uu___139_10841.remaining_iface_decls);
      syntax_only = (uu___139_10841.syntax_only);
      ds_hooks = (uu___139_10841.ds_hooks)
    }
  