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
      let uu___112_1645 = env  in
      {
        curmodule = (uu___112_1645.curmodule);
        curmonad = (uu___112_1645.curmonad);
        modules = (uu___112_1645.modules);
        scope_mods = (uu___112_1645.scope_mods);
        exported_ids = (uu___112_1645.exported_ids);
        trans_exported_ids = (uu___112_1645.trans_exported_ids);
        includes = (uu___112_1645.includes);
        sigaccum = (uu___112_1645.sigaccum);
        sigmap = (uu___112_1645.sigmap);
        iface = b;
        admitted_iface = (uu___112_1645.admitted_iface);
        expect_typ = (uu___112_1645.expect_typ);
        docs = (uu___112_1645.docs);
        remaining_iface_decls = (uu___112_1645.remaining_iface_decls);
        syntax_only = (uu___112_1645.syntax_only);
        ds_hooks = (uu___112_1645.ds_hooks)
      }
  
let (iface : env -> Prims.bool) = fun e  -> e.iface 
let (set_admitted_iface : env -> Prims.bool -> env) =
  fun e  ->
    fun b  ->
      let uu___113_1655 = e  in
      {
        curmodule = (uu___113_1655.curmodule);
        curmonad = (uu___113_1655.curmonad);
        modules = (uu___113_1655.modules);
        scope_mods = (uu___113_1655.scope_mods);
        exported_ids = (uu___113_1655.exported_ids);
        trans_exported_ids = (uu___113_1655.trans_exported_ids);
        includes = (uu___113_1655.includes);
        sigaccum = (uu___113_1655.sigaccum);
        sigmap = (uu___113_1655.sigmap);
        iface = (uu___113_1655.iface);
        admitted_iface = b;
        expect_typ = (uu___113_1655.expect_typ);
        docs = (uu___113_1655.docs);
        remaining_iface_decls = (uu___113_1655.remaining_iface_decls);
        syntax_only = (uu___113_1655.syntax_only);
        ds_hooks = (uu___113_1655.ds_hooks)
      }
  
let (admitted_iface : env -> Prims.bool) = fun e  -> e.admitted_iface 
let (set_expect_typ : env -> Prims.bool -> env) =
  fun e  ->
    fun b  ->
      let uu___114_1665 = e  in
      {
        curmodule = (uu___114_1665.curmodule);
        curmonad = (uu___114_1665.curmonad);
        modules = (uu___114_1665.modules);
        scope_mods = (uu___114_1665.scope_mods);
        exported_ids = (uu___114_1665.exported_ids);
        trans_exported_ids = (uu___114_1665.trans_exported_ids);
        includes = (uu___114_1665.includes);
        sigaccum = (uu___114_1665.sigaccum);
        sigmap = (uu___114_1665.sigmap);
        iface = (uu___114_1665.iface);
        admitted_iface = (uu___114_1665.admitted_iface);
        expect_typ = b;
        docs = (uu___114_1665.docs);
        remaining_iface_decls = (uu___114_1665.remaining_iface_decls);
        syntax_only = (uu___114_1665.syntax_only);
        ds_hooks = (uu___114_1665.ds_hooks)
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
      (fun uu___80_1817  ->
         match uu___80_1817 with
         | Open_module_or_namespace (lid,_info) ->
             FStar_Pervasives_Native.Some lid
         | uu____1822 -> FStar_Pervasives_Native.None) env.scope_mods
  
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun e  ->
    fun l  ->
      let uu___115_1829 = e  in
      {
        curmodule = (FStar_Pervasives_Native.Some l);
        curmonad = (uu___115_1829.curmonad);
        modules = (uu___115_1829.modules);
        scope_mods = (uu___115_1829.scope_mods);
        exported_ids = (uu___115_1829.exported_ids);
        trans_exported_ids = (uu___115_1829.trans_exported_ids);
        includes = (uu___115_1829.includes);
        sigaccum = (uu___115_1829.sigaccum);
        sigmap = (uu___115_1829.sigmap);
        iface = (uu___115_1829.iface);
        admitted_iface = (uu___115_1829.admitted_iface);
        expect_typ = (uu___115_1829.expect_typ);
        docs = (uu___115_1829.docs);
        remaining_iface_decls = (uu___115_1829.remaining_iface_decls);
        syntax_only = (uu___115_1829.syntax_only);
        ds_hooks = (uu___115_1829.ds_hooks)
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
            let uu___116_2007 = env  in
            {
              curmodule = (uu___116_2007.curmodule);
              curmonad = (uu___116_2007.curmonad);
              modules = (uu___116_2007.modules);
              scope_mods = (uu___116_2007.scope_mods);
              exported_ids = (uu___116_2007.exported_ids);
              trans_exported_ids = (uu___116_2007.trans_exported_ids);
              includes = (uu___116_2007.includes);
              sigaccum = (uu___116_2007.sigaccum);
              sigmap = (uu___116_2007.sigmap);
              iface = (uu___116_2007.iface);
              admitted_iface = (uu___116_2007.admitted_iface);
              expect_typ = (uu___116_2007.expect_typ);
              docs = (uu___116_2007.docs);
              remaining_iface_decls = ((l, ds) :: rest);
              syntax_only = (uu___116_2007.syntax_only);
              ds_hooks = (uu___116_2007.ds_hooks)
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
      let uu___117_2039 = env  in
      {
        curmodule = (uu___117_2039.curmodule);
        curmonad = (uu___117_2039.curmonad);
        modules = (uu___117_2039.modules);
        scope_mods = (uu___117_2039.scope_mods);
        exported_ids = (uu___117_2039.exported_ids);
        trans_exported_ids = (uu___117_2039.trans_exported_ids);
        includes = (uu___117_2039.includes);
        sigaccum = (uu___117_2039.sigaccum);
        sigmap = (uu___117_2039.sigmap);
        iface = (uu___117_2039.iface);
        admitted_iface = (uu___117_2039.admitted_iface);
        expect_typ = (uu___117_2039.expect_typ);
        docs = (uu___117_2039.docs);
        remaining_iface_decls = (uu___117_2039.remaining_iface_decls);
        syntax_only = b;
        ds_hooks = (uu___117_2039.ds_hooks)
      }
  
let (ds_hooks : env -> dsenv_hooks) = fun env  -> env.ds_hooks 
let (set_ds_hooks : env -> dsenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___118_2049 = env  in
      {
        curmodule = (uu___118_2049.curmodule);
        curmonad = (uu___118_2049.curmonad);
        modules = (uu___118_2049.modules);
        scope_mods = (uu___118_2049.scope_mods);
        exported_ids = (uu___118_2049.exported_ids);
        trans_exported_ids = (uu___118_2049.trans_exported_ids);
        includes = (uu___118_2049.includes);
        sigaccum = (uu___118_2049.sigaccum);
        sigmap = (uu___118_2049.sigmap);
        iface = (uu___118_2049.iface);
        admitted_iface = (uu___118_2049.admitted_iface);
        expect_typ = (uu___118_2049.expect_typ);
        docs = (uu___118_2049.docs);
        remaining_iface_decls = (uu___118_2049.remaining_iface_decls);
        syntax_only = (uu___118_2049.syntax_only);
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
        let uu___119_2136 = bv.FStar_Syntax_Syntax.ppname  in
        {
          FStar_Ident.idText = (uu___119_2136.FStar_Ident.idText);
          FStar_Ident.idRange = r
        }  in
      let uu___120_2137 = bv  in
      {
        FStar_Syntax_Syntax.ppname = id1;
        FStar_Syntax_Syntax.index = (uu___120_2137.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = (uu___120_2137.FStar_Syntax_Syntax.sort)
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
    fun uu___81_2357  ->
      match uu___81_2357 with
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
          if FStar_Ident.lid_equals typename' record.typename
          then
            let fname =
              FStar_Ident.lid_of_ids
                (FStar_List.append (record.typename).FStar_Ident.ns [id1])
               in
            let find1 =
              FStar_Util.find_map record.fields
                (fun uu____2416  ->
                   match uu____2416 with
                   | (f,uu____2424) ->
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
  fun uu___82_2470  ->
    match uu___82_2470 with
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
              let rec aux uu___83_2526 =
                match uu___83_2526 with
                | [] -> find_in_module_default
                | modul::q ->
                    let mname = modul.FStar_Ident.str  in
                    let not_shadowed =
                      let uu____2537 = get_exported_id_set env mname  in
                      match uu____2537 with
                      | FStar_Pervasives_Native.None  -> true
                      | FStar_Pervasives_Native.Some mex ->
                          let mexports =
                            let uu____2558 = mex eikind  in
                            FStar_ST.op_Bang uu____2558  in
                          FStar_Util.set_mem idstr mexports
                       in
                    let mincludes =
                      let uu____2672 =
                        FStar_Util.smap_try_find env.includes mname  in
                      match uu____2672 with
                      | FStar_Pervasives_Native.None  -> []
                      | FStar_Pervasives_Native.Some minc ->
                          FStar_ST.op_Bang minc
                       in
                    let look_into =
                      if not_shadowed
                      then
                        let uu____2748 = qual modul id1  in
                        find_in_module uu____2748
                      else Cont_ignore  in
                    (match look_into with
                     | Cont_ignore  -> aux (FStar_List.append mincludes q)
                     | uu____2752 -> look_into)
                 in
              aux [ns]
  
let (is_exported_id_field : exported_id_kind -> Prims.bool) =
  fun uu___84_2757  ->
    match uu___84_2757 with
    | Exported_id_field  -> true
    | uu____2758 -> false
  
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
                  let check_local_binding_id uu___85_2860 =
                    match uu___85_2860 with
                    | (id',uu____2862,uu____2863) ->
                        id'.FStar_Ident.idText = id1.FStar_Ident.idText
                     in
                  let check_rec_binding_id uu___86_2867 =
                    match uu___86_2867 with
                    | (id',uu____2869,uu____2870) ->
                        id'.FStar_Ident.idText = id1.FStar_Ident.idText
                     in
                  let curmod_ns =
                    let uu____2874 = current_module env  in
                    FStar_Ident.ids_of_lid uu____2874  in
                  let proc uu___87_2880 =
                    match uu___87_2880 with
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
                        let uu____2888 = FStar_Ident.lid_of_ids curmod_ns  in
                        find_in_module_with_includes Exported_id_field
                          (fun lid  ->
                             let id2 = lid.FStar_Ident.ident  in
                             find_in_record lid.FStar_Ident.ns id2 r k_record)
                          Cont_ignore env uu____2888 id1
                    | uu____2893 -> Cont_ignore  in
                  let rec aux uu___88_2901 =
                    match uu___88_2901 with
                    | a::q ->
                        let uu____2910 = proc a  in
                        option_of_cont (fun uu____2914  -> aux q) uu____2910
                    | [] ->
                        let uu____2915 = lookup_default_id Cont_fail id1  in
                        option_of_cont
                          (fun uu____2919  -> FStar_Pervasives_Native.None)
                          uu____2915
                     in
                  aux env.scope_mods
  
let found_local_binding :
  'Auu____2924 'Auu____2925 .
    FStar_Range.range ->
      ('Auu____2925,FStar_Syntax_Syntax.bv,'Auu____2924)
        FStar_Pervasives_Native.tuple3 ->
        (FStar_Syntax_Syntax.term,'Auu____2924)
          FStar_Pervasives_Native.tuple2
  =
  fun r  ->
    fun uu____2943  ->
      match uu____2943 with
      | (id',x,mut) -> let uu____2953 = bv_to_name x r  in (uu____2953, mut)
  
let find_in_module :
  'Auu____2959 .
    env ->
      FStar_Ident.lident ->
        (FStar_Ident.lident ->
           (FStar_Syntax_Syntax.sigelt,Prims.bool)
             FStar_Pervasives_Native.tuple2 -> 'Auu____2959)
          -> 'Auu____2959 -> 'Auu____2959
  =
  fun env  ->
    fun lid  ->
      fun k_global_def  ->
        fun k_not_found  ->
          let uu____2994 =
            FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str  in
          match uu____2994 with
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
      let uu____3030 = unmangleOpName id1  in
      match uu____3030 with
      | FStar_Pervasives_Native.Some f -> FStar_Pervasives_Native.Some f
      | uu____3056 ->
          try_lookup_id'' env id1 Exported_id_term_type
            (fun r  ->
               let uu____3070 = found_local_binding id1.FStar_Ident.idRange r
                  in
               Cont_ok uu____3070) (fun uu____3080  -> Cont_fail)
            (fun uu____3086  -> Cont_ignore)
            (fun i  ->
               find_in_module env i
                 (fun uu____3101  -> fun uu____3102  -> Cont_fail)
                 Cont_ignore)
            (fun uu____3117  -> fun uu____3118  -> Cont_fail)
  
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
            | FStar_Pervasives_Native.Some uu____3188 ->
                let lid = qualify env id1  in
                let uu____3190 =
                  FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str
                   in
                (match uu____3190 with
                 | FStar_Pervasives_Native.Some r ->
                     let uu____3214 = k_global_def lid r  in
                     FStar_Pervasives_Native.Some uu____3214
                 | FStar_Pervasives_Native.None  ->
                     FStar_Pervasives_Native.None)
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             in
          match find_in_monad with
          | FStar_Pervasives_Native.Some v1 -> v1
          | FStar_Pervasives_Native.None  ->
              let lid =
                let uu____3237 = current_module env  in qual uu____3237 id1
                 in
              find_in_module env lid k_global_def k_not_found
  
let (module_is_defined : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      (match env.curmodule with
       | FStar_Pervasives_Native.None  -> false
       | FStar_Pervasives_Native.Some m ->
           let uu____3247 = current_module env  in
           FStar_Ident.lid_equals lid uu____3247)
        ||
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
        let rec aux uu___89_3279 =
          match uu___89_3279 with
          | [] ->
              let uu____3284 = module_is_defined env lid  in
              if uu____3284
              then FStar_Pervasives_Native.Some lid
              else FStar_Pervasives_Native.None
          | (Open_module_or_namespace (ns,Open_namespace ))::q when honor_ns
              ->
              let new_lid =
                let uu____3293 =
                  let uu____3296 = FStar_Ident.path_of_lid ns  in
                  let uu____3299 = FStar_Ident.path_of_lid lid  in
                  FStar_List.append uu____3296 uu____3299  in
                FStar_Ident.lid_of_path uu____3293
                  (FStar_Ident.range_of_lid lid)
                 in
              let uu____3302 = module_is_defined env new_lid  in
              if uu____3302
              then FStar_Pervasives_Native.Some new_lid
              else aux q
          | (Module_abbrev (name,modul))::uu____3308 when
              (nslen = (Prims.parse_int "0")) &&
                (name.FStar_Ident.idText =
                   (lid.FStar_Ident.ident).FStar_Ident.idText)
              -> FStar_Pervasives_Native.Some modul
          | uu____3315::q -> aux q  in
        aux env.scope_mods
  
let (fail_if_curmodule :
  env -> FStar_Ident.lident -> FStar_Ident.lident -> Prims.unit) =
  fun env  ->
    fun ns_original  ->
      fun ns_resolved  ->
        let uu____3328 =
          let uu____3329 = current_module env  in
          FStar_Ident.lid_equals ns_resolved uu____3329  in
        if uu____3328
        then
          (if FStar_Ident.lid_equals ns_resolved FStar_Parser_Const.prims_lid
           then ()
           else
             (let uu____3331 =
                let uu____3336 =
                  FStar_Util.format1
                    "Reference %s to current module is forbidden (see GitHub issue #451)"
                    ns_original.FStar_Ident.str
                   in
                (FStar_Errors.Fatal_ForbiddenReferenceToCurrentModule,
                  uu____3336)
                 in
              FStar_Errors.raise_error uu____3331
                (FStar_Ident.range_of_lid ns_original)))
        else ()
  
let (fail_if_qualified_by_curmodule :
  env -> FStar_Ident.lident -> Prims.unit) =
  fun env  ->
    fun lid  ->
      match lid.FStar_Ident.ns with
      | [] -> ()
      | uu____3344 ->
          let modul_orig = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          let uu____3348 = resolve_module_name env modul_orig true  in
          (match uu____3348 with
           | FStar_Pervasives_Native.Some modul_res ->
               fail_if_curmodule env modul_orig modul_res
           | uu____3352 -> ())
  
let (namespace_is_open : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      FStar_List.existsb
        (fun uu___90_3363  ->
           match uu___90_3363 with
           | Open_module_or_namespace (ns,Open_namespace ) ->
               FStar_Ident.lid_equals lid ns
           | uu____3365 -> false) env.scope_mods
  
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
                 let uu____3454 = aux rev_ns_prefix ns_last_id  in
                 FStar_All.pipe_right uu____3454
                   (FStar_Util.map_option
                      (fun uu____3504  ->
                         match uu____3504 with
                         | (stripped_ids,rev_kept_ids) ->
                             (stripped_ids, (id1 :: rev_kept_ids)))))
           in
        let uu____3535 =
          is_full_path &&
            (let uu____3537 = FStar_Ident.lid_of_ids ids  in
             module_is_defined env uu____3537)
           in
        if uu____3535
        then (ids, [])
        else
          (match FStar_List.rev ids with
           | [] -> ([], [])
           | ns_last_id::ns_rev_prefix ->
               let uu____3567 = aux ns_rev_prefix ns_last_id  in
               (match uu____3567 with
                | FStar_Pervasives_Native.None  -> ([], ids)
                | FStar_Pervasives_Native.Some (stripped_ids,rev_kept_ids) ->
                    (stripped_ids, (FStar_List.rev rev_kept_ids))))
  
let (shorten_lid : env -> FStar_Ident.lid -> FStar_Ident.lid) =
  fun env  ->
    fun lid  ->
      let uu____3626 = shorten_module_path env lid.FStar_Ident.ns true  in
      match uu____3626 with
      | (uu____3635,short) ->
          FStar_Ident.lid_of_ns_and_id short lid.FStar_Ident.ident
  
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
                  | uu____3743::uu____3744 ->
                      let uu____3747 =
                        let uu____3750 =
                          let uu____3751 =
                            FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
                          FStar_Ident.set_lid_range uu____3751
                            (FStar_Ident.range_of_lid lid)
                           in
                        resolve_module_name env uu____3750 true  in
                      (match uu____3747 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some modul ->
                           let uu____3755 =
                             find_in_module_with_includes eikind f_module
                               Cont_fail env modul lid.FStar_Ident.ident
                              in
                           option_of_cont
                             (fun uu____3759  -> FStar_Pervasives_Native.None)
                             uu____3755)
                  | [] ->
                      try_lookup_id'' env lid.FStar_Ident.ident eikind
                        k_local_binding k_rec_binding k_record f_module
                        l_default
  
let cont_of_option :
  'a . 'a cont_t -> 'a FStar_Pervasives_Native.option -> 'a cont_t =
  fun k_none  ->
    fun uu___91_3777  ->
      match uu___91_3777 with
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
              let uu____3876 = k_global_def lid1 def  in
              cont_of_option k uu____3876  in
            let f_module lid' =
              let k = Cont_ignore  in
              find_in_module env lid' (k_global_def' k) k  in
            let l_default k i = lookup_default_id env i (k_global_def' k) k
               in
            resolve_in_open_namespaces'' env lid Exported_id_term_type
              (fun l  ->
                 let uu____3906 = k_local_binding l  in
                 cont_of_option Cont_fail uu____3906)
              (fun r  ->
                 let uu____3912 = k_rec_binding r  in
                 cont_of_option Cont_fail uu____3912)
              (fun uu____3916  -> Cont_ignore) f_module l_default
  
let (fv_qual_of_se :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option)
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____3924,uu____3925,uu____3926,l,uu____3928,uu____3929) ->
        let qopt =
          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
            (fun uu___92_3940  ->
               match uu___92_3940 with
               | FStar_Syntax_Syntax.RecordConstructor (uu____3943,fs) ->
                   FStar_Pervasives_Native.Some
                     (FStar_Syntax_Syntax.Record_ctor (l, fs))
               | uu____3955 -> FStar_Pervasives_Native.None)
           in
        (match qopt with
         | FStar_Pervasives_Native.None  ->
             FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor
         | x -> x)
    | FStar_Syntax_Syntax.Sig_declare_typ (uu____3961,uu____3962,uu____3963)
        -> FStar_Pervasives_Native.None
    | uu____3964 -> FStar_Pervasives_Native.None
  
let (lb_fv :
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Ident.lident -> FStar_Syntax_Syntax.fv)
  =
  fun lbs  ->
    fun lid  ->
      let uu____3975 =
        FStar_Util.find_map lbs
          (fun lb  ->
             let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
             let uu____3983 = FStar_Syntax_Syntax.fv_eq_lid fv lid  in
             if uu____3983
             then FStar_Pervasives_Native.Some fv
             else FStar_Pervasives_Native.None)
         in
      FStar_All.pipe_right uu____3975 FStar_Util.must
  
let (ns_of_lid_equals :
  FStar_Ident.lident -> FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    fun ns  ->
      ((FStar_List.length lid.FStar_Ident.ns) =
         (FStar_List.length (FStar_Ident.ids_of_lid ns)))
        &&
        (let uu____3996 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
         FStar_Ident.lid_equals uu____3996 ns)
  
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
          let k_global_def source_lid uu___97_4026 =
            match uu___97_4026 with
            | (uu____4033,true ) when exclude_interf ->
                FStar_Pervasives_Native.None
            | (se,uu____4035) ->
                (match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_inductive_typ uu____4038 ->
                     let uu____4055 =
                       let uu____4056 =
                         let uu____4065 =
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.Delta_constant
                             FStar_Pervasives_Native.None
                            in
                         (uu____4065, false,
                           (se.FStar_Syntax_Syntax.sigattrs))
                          in
                       Term_name uu____4056  in
                     FStar_Pervasives_Native.Some uu____4055
                 | FStar_Syntax_Syntax.Sig_datacon uu____4068 ->
                     let uu____4083 =
                       let uu____4084 =
                         let uu____4093 =
                           let uu____4094 = fv_qual_of_se se  in
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.Delta_constant uu____4094
                            in
                         (uu____4093, false,
                           (se.FStar_Syntax_Syntax.sigattrs))
                          in
                       Term_name uu____4084  in
                     FStar_Pervasives_Native.Some uu____4083
                 | FStar_Syntax_Syntax.Sig_let ((uu____4099,lbs),uu____4101)
                     ->
                     let fv = lb_fv lbs source_lid  in
                     let uu____4117 =
                       let uu____4118 =
                         let uu____4127 =
                           FStar_Syntax_Syntax.fvar source_lid
                             fv.FStar_Syntax_Syntax.fv_delta
                             fv.FStar_Syntax_Syntax.fv_qual
                            in
                         (uu____4127, false,
                           (se.FStar_Syntax_Syntax.sigattrs))
                          in
                       Term_name uu____4118  in
                     FStar_Pervasives_Native.Some uu____4117
                 | FStar_Syntax_Syntax.Sig_declare_typ
                     (lid1,uu____4131,uu____4132) ->
                     let quals = se.FStar_Syntax_Syntax.sigquals  in
                     let uu____4136 =
                       any_val ||
                         (FStar_All.pipe_right quals
                            (FStar_Util.for_some
                               (fun uu___93_4140  ->
                                  match uu___93_4140 with
                                  | FStar_Syntax_Syntax.Assumption  -> true
                                  | uu____4141 -> false)))
                        in
                     if uu____4136
                     then
                       let lid2 =
                         FStar_Ident.set_lid_range lid1
                           (FStar_Ident.range_of_lid source_lid)
                          in
                       let dd =
                         let uu____4146 =
                           (FStar_Syntax_Util.is_primop_lid lid2) ||
                             (FStar_All.pipe_right quals
                                (FStar_Util.for_some
                                   (fun uu___94_4151  ->
                                      match uu___94_4151 with
                                      | FStar_Syntax_Syntax.Projector
                                          uu____4152 -> true
                                      | FStar_Syntax_Syntax.Discriminator
                                          uu____4157 -> true
                                      | uu____4158 -> false)))
                            in
                         if uu____4146
                         then FStar_Syntax_Syntax.Delta_equational
                         else FStar_Syntax_Syntax.Delta_constant  in
                       let dd1 =
                         let uu____4161 =
                           FStar_All.pipe_right quals
                             (FStar_Util.for_some
                                (fun uu___95_4165  ->
                                   match uu___95_4165 with
                                   | FStar_Syntax_Syntax.Abstract  -> true
                                   | uu____4166 -> false))
                            in
                         if uu____4161
                         then FStar_Syntax_Syntax.Delta_abstract dd
                         else dd  in
                       let uu____4168 =
                         FStar_Util.find_map quals
                           (fun uu___96_4173  ->
                              match uu___96_4173 with
                              | FStar_Syntax_Syntax.Reflectable refl_monad ->
                                  FStar_Pervasives_Native.Some refl_monad
                              | uu____4177 -> FStar_Pervasives_Native.None)
                          in
                       (match uu____4168 with
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
                        | uu____4188 ->
                            let uu____4191 =
                              let uu____4192 =
                                let uu____4201 =
                                  let uu____4202 = fv_qual_of_se se  in
                                  FStar_Syntax_Syntax.fvar lid2 dd1
                                    uu____4202
                                   in
                                (uu____4201, false,
                                  (se.FStar_Syntax_Syntax.sigattrs))
                                 in
                              Term_name uu____4192  in
                            FStar_Pervasives_Native.Some uu____4191)
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
                 | FStar_Syntax_Syntax.Sig_effect_abbrev uu____4210 ->
                     FStar_Pervasives_Native.Some (Eff_name (se, source_lid))
                 | uu____4223 -> FStar_Pervasives_Native.None)
             in
          let k_local_binding r =
            let uu____4242 =
              found_local_binding (FStar_Ident.range_of_lid lid) r  in
            match uu____4242 with
            | (t,mut) ->
                FStar_Pervasives_Native.Some (Term_name (t, mut, []))
             in
          let k_rec_binding uu____4264 =
            match uu____4264 with
            | (id1,l,dd) ->
                let uu____4276 =
                  let uu____4277 =
                    let uu____4286 =
                      FStar_Syntax_Syntax.fvar
                        (FStar_Ident.set_lid_range l
                           (FStar_Ident.range_of_lid lid)) dd
                        FStar_Pervasives_Native.None
                       in
                    (uu____4286, false, [])  in
                  Term_name uu____4277  in
                FStar_Pervasives_Native.Some uu____4276
             in
          let found_unmangled =
            match lid.FStar_Ident.ns with
            | [] ->
                let uu____4294 = unmangleOpName lid.FStar_Ident.ident  in
                (match uu____4294 with
                 | FStar_Pervasives_Native.Some (t,mut) ->
                     FStar_Pervasives_Native.Some (Term_name (t, mut, []))
                 | uu____4311 -> FStar_Pervasives_Native.None)
            | uu____4318 -> FStar_Pervasives_Native.None  in
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
        let uu____4347 = try_lookup_name true exclude_interf env lid  in
        match uu____4347 with
        | FStar_Pervasives_Native.Some (Eff_name (o,l)) ->
            FStar_Pervasives_Native.Some (o, l)
        | uu____4362 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____4377 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____4377 with
      | FStar_Pervasives_Native.Some (o,l1) ->
          FStar_Pervasives_Native.Some l1
      | uu____4392 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_name_and_attributes :
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident,FStar_Syntax_Syntax.cflags Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____4413 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____4413 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____4429;
             FStar_Syntax_Syntax.sigquals = uu____4430;
             FStar_Syntax_Syntax.sigmeta = uu____4431;
             FStar_Syntax_Syntax.sigattrs = uu____4432;_},l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____4451;
             FStar_Syntax_Syntax.sigquals = uu____4452;
             FStar_Syntax_Syntax.sigmeta = uu____4453;
             FStar_Syntax_Syntax.sigattrs = uu____4454;_},l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (uu____4472,uu____4473,uu____4474,uu____4475,cattributes);
             FStar_Syntax_Syntax.sigrng = uu____4477;
             FStar_Syntax_Syntax.sigquals = uu____4478;
             FStar_Syntax_Syntax.sigmeta = uu____4479;
             FStar_Syntax_Syntax.sigattrs = uu____4480;_},l1)
          -> FStar_Pervasives_Native.Some (l1, cattributes)
      | uu____4502 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_defn :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.eff_decl FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____4523 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____4523 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____4533;
             FStar_Syntax_Syntax.sigquals = uu____4534;
             FStar_Syntax_Syntax.sigmeta = uu____4535;
             FStar_Syntax_Syntax.sigattrs = uu____4536;_},uu____4537)
          -> FStar_Pervasives_Native.Some ne
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____4547;
             FStar_Syntax_Syntax.sigquals = uu____4548;
             FStar_Syntax_Syntax.sigmeta = uu____4549;
             FStar_Syntax_Syntax.sigattrs = uu____4550;_},uu____4551)
          -> FStar_Pervasives_Native.Some ne
      | uu____4560 -> FStar_Pervasives_Native.None
  
let (is_effect_name : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____4573 = try_lookup_effect_name env lid  in
      match uu____4573 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____4576 -> true
  
let (try_lookup_root_effect_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____4585 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____4585 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (l',uu____4595,uu____4596,uu____4597,uu____4598);
             FStar_Syntax_Syntax.sigrng = uu____4599;
             FStar_Syntax_Syntax.sigquals = uu____4600;
             FStar_Syntax_Syntax.sigmeta = uu____4601;
             FStar_Syntax_Syntax.sigattrs = uu____4602;_},uu____4603)
          ->
          let rec aux new_name =
            let uu____4622 =
              FStar_Util.smap_try_find (sigmap env) new_name.FStar_Ident.str
               in
            match uu____4622 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (s,uu____4640) ->
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
                     (uu____4649,uu____4650,uu____4651,cmp,uu____4653) ->
                     let l'' = FStar_Syntax_Util.comp_effect_name cmp  in
                     aux l''
                 | uu____4659 -> FStar_Pervasives_Native.None)
             in
          aux l'
      | FStar_Pervasives_Native.Some (uu____4660,l') ->
          FStar_Pervasives_Native.Some l'
      | uu____4666 -> FStar_Pervasives_Native.None
  
let (lookup_letbinding_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___98_4695 =
        match uu___98_4695 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____4704,uu____4705,uu____4706);
             FStar_Syntax_Syntax.sigrng = uu____4707;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____4709;
             FStar_Syntax_Syntax.sigattrs = uu____4710;_},uu____4711)
            -> FStar_Pervasives_Native.Some quals
        | uu____4718 -> FStar_Pervasives_Native.None  in
      let uu____4725 =
        resolve_in_open_namespaces' env lid
          (fun uu____4733  -> FStar_Pervasives_Native.None)
          (fun uu____4737  -> FStar_Pervasives_Native.None) k_global_def
         in
      match uu____4725 with
      | FStar_Pervasives_Native.Some quals -> quals
      | uu____4747 -> []
  
let (try_lookup_module :
  env ->
    Prims.string Prims.list ->
      FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun path  ->
      let uu____4764 =
        FStar_List.tryFind
          (fun uu____4779  ->
             match uu____4779 with
             | (mlid,modul) ->
                 let uu____4786 = FStar_Ident.path_of_lid mlid  in
                 uu____4786 = path) env.modules
         in
      match uu____4764 with
      | FStar_Pervasives_Native.Some (uu____4793,modul) ->
          FStar_Pervasives_Native.Some modul
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (try_lookup_let :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___99_4823 =
        match uu___99_4823 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               ((uu____4830,lbs),uu____4832);
             FStar_Syntax_Syntax.sigrng = uu____4833;
             FStar_Syntax_Syntax.sigquals = uu____4834;
             FStar_Syntax_Syntax.sigmeta = uu____4835;
             FStar_Syntax_Syntax.sigattrs = uu____4836;_},uu____4837)
            ->
            let fv = lb_fv lbs lid1  in
            let uu____4857 =
              FStar_Syntax_Syntax.fvar lid1 fv.FStar_Syntax_Syntax.fv_delta
                fv.FStar_Syntax_Syntax.fv_qual
               in
            FStar_Pervasives_Native.Some uu____4857
        | uu____4858 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____4864  -> FStar_Pervasives_Native.None)
        (fun uu____4866  -> FStar_Pervasives_Native.None) k_global_def
  
let (try_lookup_definition :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___100_4889 =
        match uu___100_4889 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               (lbs,uu____4899);
             FStar_Syntax_Syntax.sigrng = uu____4900;
             FStar_Syntax_Syntax.sigquals = uu____4901;
             FStar_Syntax_Syntax.sigmeta = uu____4902;
             FStar_Syntax_Syntax.sigattrs = uu____4903;_},uu____4904)
            ->
            FStar_Util.find_map (FStar_Pervasives_Native.snd lbs)
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inr fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv lid1 ->
                     FStar_Pervasives_Native.Some
                       (lb.FStar_Syntax_Syntax.lbdef)
                 | uu____4927 -> FStar_Pervasives_Native.None)
        | uu____4934 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____4944  -> FStar_Pervasives_Native.None)
        (fun uu____4948  -> FStar_Pervasives_Native.None) k_global_def
  
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
          let uu____4995 = try_lookup_name any_val exclude_interface env lid
             in
          match uu____4995 with
          | FStar_Pervasives_Native.Some (Term_name (e,mut,attrs)) ->
              FStar_Pervasives_Native.Some (e, mut, attrs)
          | uu____5025 -> FStar_Pervasives_Native.None
  
let (drop_attributes :
  (FStar_Syntax_Syntax.term,Prims.bool,FStar_Syntax_Syntax.attribute
                                         Prims.list)
    FStar_Pervasives_Native.tuple3 FStar_Pervasives_Native.option ->
    (FStar_Syntax_Syntax.term,Prims.bool) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option)
  =
  fun x  ->
    match x with
    | FStar_Pervasives_Native.Some (t,mut,uu____5079) ->
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
      let uu____5146 = try_lookup_lid_with_attributes env l  in
      FStar_All.pipe_right uu____5146 drop_attributes
  
let (resolve_to_fully_qualified_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____5181 = try_lookup_lid env l  in
      match uu____5181 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (e,uu____5195) ->
          let uu____5200 =
            let uu____5201 = FStar_Syntax_Subst.compress e  in
            uu____5201.FStar_Syntax_Syntax.n  in
          (match uu____5200 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               FStar_Pervasives_Native.Some
                 ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
           | uu____5207 -> FStar_Pervasives_Native.None)
  
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
        let uu___121_5235 = env  in
        {
          curmodule = (uu___121_5235.curmodule);
          curmonad = (uu___121_5235.curmonad);
          modules = (uu___121_5235.modules);
          scope_mods = [];
          exported_ids = empty_exported_id_smap;
          trans_exported_ids = (uu___121_5235.trans_exported_ids);
          includes = empty_include_smap;
          sigaccum = (uu___121_5235.sigaccum);
          sigmap = (uu___121_5235.sigmap);
          iface = (uu___121_5235.iface);
          admitted_iface = (uu___121_5235.admitted_iface);
          expect_typ = (uu___121_5235.expect_typ);
          docs = (uu___121_5235.docs);
          remaining_iface_decls = (uu___121_5235.remaining_iface_decls);
          syntax_only = (uu___121_5235.syntax_only);
          ds_hooks = (uu___121_5235.ds_hooks)
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
      let uu____5254 = try_lookup_lid_with_attributes_no_resolve env l  in
      FStar_All.pipe_right uu____5254 drop_attributes
  
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
      let k_global_def lid1 uu___102_5309 =
        match uu___102_5309 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____5316,uu____5317,uu____5318);
             FStar_Syntax_Syntax.sigrng = uu____5319;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____5321;
             FStar_Syntax_Syntax.sigattrs = uu____5322;_},uu____5323)
            ->
            let uu____5328 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___101_5332  ->
                      match uu___101_5332 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | uu____5333 -> false))
               in
            if uu____5328
            then
              let uu____5336 =
                FStar_Syntax_Syntax.lid_as_fv lid1
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Pervasives_Native.Some uu____5336
            else FStar_Pervasives_Native.None
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
               uu____5338;
             FStar_Syntax_Syntax.sigrng = uu____5339;
             FStar_Syntax_Syntax.sigquals = uu____5340;
             FStar_Syntax_Syntax.sigmeta = uu____5341;
             FStar_Syntax_Syntax.sigattrs = uu____5342;_},uu____5343)
            ->
            let uu____5362 =
              FStar_Syntax_Syntax.lid_as_fv lid1
                FStar_Syntax_Syntax.Delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
               in
            FStar_Pervasives_Native.Some uu____5362
        | uu____5363 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____5369  -> FStar_Pervasives_Native.None)
        (fun uu____5371  -> FStar_Pervasives_Native.None) k_global_def
  
let (find_all_datacons :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___103_5396 =
        match uu___103_5396 with
        | ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_inductive_typ
               (uu____5405,uu____5406,uu____5407,uu____5408,datas,uu____5410);
             FStar_Syntax_Syntax.sigrng = uu____5411;
             FStar_Syntax_Syntax.sigquals = uu____5412;
             FStar_Syntax_Syntax.sigmeta = uu____5413;
             FStar_Syntax_Syntax.sigattrs = uu____5414;_},uu____5415)
            -> FStar_Pervasives_Native.Some datas
        | uu____5430 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____5440  -> FStar_Pervasives_Native.None)
        (fun uu____5444  -> FStar_Pervasives_Native.None) k_global_def
  
let (record_cache_aux_with_filter :
  ((Prims.unit -> Prims.unit,Prims.unit -> Prims.unit,Prims.unit ->
                                                        record_or_dc
                                                          Prims.list,
     record_or_dc -> Prims.unit) FStar_Pervasives_Native.tuple4,Prims.unit ->
                                                                  Prims.unit)
    FStar_Pervasives_Native.tuple2)
  =
  let record_cache = FStar_Util.mk_ref [[]]  in
  let push1 uu____5489 =
    let uu____5490 =
      let uu____5495 =
        let uu____5498 = FStar_ST.op_Bang record_cache  in
        FStar_List.hd uu____5498  in
      let uu____5554 = FStar_ST.op_Bang record_cache  in uu____5495 ::
        uu____5554
       in
    FStar_ST.op_Colon_Equals record_cache uu____5490  in
  let pop1 uu____5662 =
    let uu____5663 =
      let uu____5668 = FStar_ST.op_Bang record_cache  in
      FStar_List.tl uu____5668  in
    FStar_ST.op_Colon_Equals record_cache uu____5663  in
  let peek1 uu____5778 =
    let uu____5779 = FStar_ST.op_Bang record_cache  in
    FStar_List.hd uu____5779  in
  let insert r =
    let uu____5839 =
      let uu____5844 = let uu____5847 = peek1 ()  in r :: uu____5847  in
      let uu____5850 =
        let uu____5855 = FStar_ST.op_Bang record_cache  in
        FStar_List.tl uu____5855  in
      uu____5844 :: uu____5850  in
    FStar_ST.op_Colon_Equals record_cache uu____5839  in
  let filter1 uu____5965 =
    let rc = peek1 ()  in
    let filtered =
      FStar_List.filter
        (fun r  -> Prims.op_Negation r.is_private_or_abstract) rc
       in
    let uu____5974 =
      let uu____5979 =
        let uu____5984 = FStar_ST.op_Bang record_cache  in
        FStar_List.tl uu____5984  in
      filtered :: uu____5979  in
    FStar_ST.op_Colon_Equals record_cache uu____5974  in
  let aux = (push1, pop1, peek1, insert)  in (aux, filter1) 
let (record_cache_aux :
  (Prims.unit -> Prims.unit,Prims.unit -> Prims.unit,Prims.unit ->
                                                       record_or_dc
                                                         Prims.list,record_or_dc
                                                                    ->
                                                                    Prims.unit)
    FStar_Pervasives_Native.tuple4)
  =
  let uu____6158 = record_cache_aux_with_filter  in
  match uu____6158 with | (aux,uu____6202) -> aux 
let (filter_record_cache : Prims.unit -> Prims.unit) =
  let uu____6245 = record_cache_aux_with_filter  in
  match uu____6245 with | (uu____6272,filter1) -> filter1 
let (push_record_cache : Prims.unit -> Prims.unit) =
  let uu____6316 = record_cache_aux  in
  match uu____6316 with | (push1,uu____6338,uu____6339,uu____6340) -> push1 
let (pop_record_cache : Prims.unit -> Prims.unit) =
  let uu____6363 = record_cache_aux  in
  match uu____6363 with | (uu____6384,pop1,uu____6386,uu____6387) -> pop1 
let (peek_record_cache : Prims.unit -> record_or_dc Prims.list) =
  let uu____6412 = record_cache_aux  in
  match uu____6412 with | (uu____6435,uu____6436,peek1,uu____6438) -> peek1 
let (insert_record_cache : record_or_dc -> Prims.unit) =
  let uu____6461 = record_cache_aux  in
  match uu____6461 with | (uu____6482,uu____6483,uu____6484,insert) -> insert 
let (extract_record :
  env ->
    scope_mod Prims.list FStar_ST.ref ->
      FStar_Syntax_Syntax.sigelt -> Prims.unit)
  =
  fun e  ->
    fun new_globs  ->
      fun se  ->
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_bundle (sigs,uu____6546) ->
            let is_record =
              FStar_Util.for_some
                (fun uu___104_6562  ->
                   match uu___104_6562 with
                   | FStar_Syntax_Syntax.RecordType uu____6563 -> true
                   | FStar_Syntax_Syntax.RecordConstructor uu____6572 -> true
                   | uu____6581 -> false)
               in
            let find_dc dc =
              FStar_All.pipe_right sigs
                (FStar_Util.find_opt
                   (fun uu___105_6603  ->
                      match uu___105_6603 with
                      | {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_datacon
                            (lid,uu____6605,uu____6606,uu____6607,uu____6608,uu____6609);
                          FStar_Syntax_Syntax.sigrng = uu____6610;
                          FStar_Syntax_Syntax.sigquals = uu____6611;
                          FStar_Syntax_Syntax.sigmeta = uu____6612;
                          FStar_Syntax_Syntax.sigattrs = uu____6613;_} ->
                          FStar_Ident.lid_equals dc lid
                      | uu____6622 -> false))
               in
            FStar_All.pipe_right sigs
              (FStar_List.iter
                 (fun uu___106_6657  ->
                    match uu___106_6657 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ
                          (typename,univs1,parms,uu____6661,uu____6662,dc::[]);
                        FStar_Syntax_Syntax.sigrng = uu____6664;
                        FStar_Syntax_Syntax.sigquals = typename_quals;
                        FStar_Syntax_Syntax.sigmeta = uu____6666;
                        FStar_Syntax_Syntax.sigattrs = uu____6667;_} ->
                        let uu____6678 =
                          let uu____6679 = find_dc dc  in
                          FStar_All.pipe_left FStar_Util.must uu____6679  in
                        (match uu____6678 with
                         | {
                             FStar_Syntax_Syntax.sigel =
                               FStar_Syntax_Syntax.Sig_datacon
                               (constrname,uu____6685,t,uu____6687,uu____6688,uu____6689);
                             FStar_Syntax_Syntax.sigrng = uu____6690;
                             FStar_Syntax_Syntax.sigquals = uu____6691;
                             FStar_Syntax_Syntax.sigmeta = uu____6692;
                             FStar_Syntax_Syntax.sigattrs = uu____6693;_} ->
                             let uu____6702 =
                               FStar_Syntax_Util.arrow_formals t  in
                             (match uu____6702 with
                              | (formals,uu____6716) ->
                                  let is_rec = is_record typename_quals  in
                                  let formals' =
                                    FStar_All.pipe_right formals
                                      (FStar_List.collect
                                         (fun uu____6765  ->
                                            match uu____6765 with
                                            | (x,q) ->
                                                let uu____6778 =
                                                  (FStar_Syntax_Syntax.is_null_bv
                                                     x)
                                                    ||
                                                    (is_rec &&
                                                       (FStar_Syntax_Syntax.is_implicit
                                                          q))
                                                   in
                                                if uu____6778
                                                then []
                                                else [(x, q)]))
                                     in
                                  let fields' =
                                    FStar_All.pipe_right formals'
                                      (FStar_List.map
                                         (fun uu____6835  ->
                                            match uu____6835 with
                                            | (x,q) ->
                                                let uu____6848 =
                                                  if is_rec
                                                  then
                                                    FStar_Syntax_Util.unmangle_field_name
                                                      x.FStar_Syntax_Syntax.ppname
                                                  else
                                                    x.FStar_Syntax_Syntax.ppname
                                                   in
                                                (uu____6848,
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
                                  ((let uu____6863 =
                                      let uu____6866 =
                                        FStar_ST.op_Bang new_globs  in
                                      (Record_or_dc record) :: uu____6866  in
                                    FStar_ST.op_Colon_Equals new_globs
                                      uu____6863);
                                   (match () with
                                    | () ->
                                        ((let add_field uu____6969 =
                                            match uu____6969 with
                                            | (id1,uu____6977) ->
                                                let modul =
                                                  let uu____6983 =
                                                    FStar_Ident.lid_of_ids
                                                      constrname.FStar_Ident.ns
                                                     in
                                                  uu____6983.FStar_Ident.str
                                                   in
                                                let uu____6984 =
                                                  get_exported_id_set e modul
                                                   in
                                                (match uu____6984 with
                                                 | FStar_Pervasives_Native.Some
                                                     my_ex ->
                                                     let my_exported_ids =
                                                       my_ex
                                                         Exported_id_field
                                                        in
                                                     ((let uu____7015 =
                                                         let uu____7016 =
                                                           FStar_ST.op_Bang
                                                             my_exported_ids
                                                            in
                                                         FStar_Util.set_add
                                                           id1.FStar_Ident.idText
                                                           uu____7016
                                                          in
                                                       FStar_ST.op_Colon_Equals
                                                         my_exported_ids
                                                         uu____7015);
                                                      (match () with
                                                       | () ->
                                                           let projname =
                                                             let uu____7102 =
                                                               let uu____7103
                                                                 =
                                                                 FStar_Syntax_Util.mk_field_projector_name_from_ident
                                                                   constrname
                                                                   id1
                                                                  in
                                                               uu____7103.FStar_Ident.ident
                                                                in
                                                             uu____7102.FStar_Ident.idText
                                                              in
                                                           let uu____7105 =
                                                             let uu____7106 =
                                                               FStar_ST.op_Bang
                                                                 my_exported_ids
                                                                in
                                                             FStar_Util.set_add
                                                               projname
                                                               uu____7106
                                                              in
                                                           FStar_ST.op_Colon_Equals
                                                             my_exported_ids
                                                             uu____7105))
                                                 | FStar_Pervasives_Native.None
                                                      -> ())
                                             in
                                          FStar_List.iter add_field fields');
                                         (match () with
                                          | () -> insert_record_cache record)))))
                         | uu____7201 -> ())
                    | uu____7202 -> ()))
        | uu____7203 -> ()
  
let (try_lookup_record_or_dc_by_field_name :
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option) =
  fun env  ->
    fun fieldname  ->
      let find_in_cache fieldname1 =
        let uu____7218 =
          ((fieldname1.FStar_Ident.ns), (fieldname1.FStar_Ident.ident))  in
        match uu____7218 with
        | (ns,id1) ->
            let uu____7235 = peek_record_cache ()  in
            FStar_Util.find_map uu____7235
              (fun record  ->
                 let uu____7241 =
                   find_in_record ns id1 record (fun r  -> Cont_ok r)  in
                 option_of_cont
                   (fun uu____7247  -> FStar_Pervasives_Native.None)
                   uu____7241)
         in
      resolve_in_open_namespaces'' env fieldname Exported_id_field
        (fun uu____7249  -> Cont_ignore) (fun uu____7251  -> Cont_ignore)
        (fun r  -> Cont_ok r)
        (fun fn  ->
           let uu____7257 = find_in_cache fn  in
           cont_of_option Cont_ignore uu____7257)
        (fun k  -> fun uu____7263  -> k)
  
let (try_lookup_record_by_field_name :
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option) =
  fun env  ->
    fun fieldname  ->
      let uu____7274 = try_lookup_record_or_dc_by_field_name env fieldname
         in
      match uu____7274 with
      | FStar_Pervasives_Native.Some r when r.is_record ->
          FStar_Pervasives_Native.Some r
      | uu____7280 -> FStar_Pervasives_Native.None
  
let (belongs_to_record :
  env -> FStar_Ident.lident -> record_or_dc -> Prims.bool) =
  fun env  ->
    fun lid  ->
      fun record  ->
        let uu____7292 = try_lookup_record_by_field_name env lid  in
        match uu____7292 with
        | FStar_Pervasives_Native.Some record' when
            let uu____7296 =
              let uu____7297 =
                FStar_Ident.path_of_ns (record.typename).FStar_Ident.ns  in
              FStar_Ident.text_of_path uu____7297  in
            let uu____7300 =
              let uu____7301 =
                FStar_Ident.path_of_ns (record'.typename).FStar_Ident.ns  in
              FStar_Ident.text_of_path uu____7301  in
            uu____7296 = uu____7300 ->
            let uu____7304 =
              find_in_record (record.typename).FStar_Ident.ns
                lid.FStar_Ident.ident record (fun uu____7308  -> Cont_ok ())
               in
            (match uu____7304 with
             | Cont_ok uu____7309 -> true
             | uu____7310 -> false)
        | uu____7313 -> false
  
let (try_lookup_dc_by_field_name :
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident,Prims.bool) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun fieldname  ->
      let uu____7328 = try_lookup_record_or_dc_by_field_name env fieldname
         in
      match uu____7328 with
      | FStar_Pervasives_Native.Some r ->
          let uu____7338 =
            let uu____7343 =
              let uu____7344 =
                FStar_Ident.lid_of_ids
                  (FStar_List.append (r.typename).FStar_Ident.ns
                     [r.constrname])
                 in
              FStar_Ident.set_lid_range uu____7344
                (FStar_Ident.range_of_lid fieldname)
               in
            (uu____7343, (r.is_record))  in
          FStar_Pervasives_Native.Some uu____7338
      | uu____7349 -> FStar_Pervasives_Native.None
  
let (string_set_ref_new :
  Prims.unit -> Prims.string FStar_Util.set FStar_ST.ref) =
  fun uu____7373  ->
    let uu____7374 = FStar_Util.new_set FStar_Util.compare  in
    FStar_Util.mk_ref uu____7374
  
let (exported_id_set_new :
  Prims.unit -> exported_id_kind -> Prims.string FStar_Util.set FStar_ST.ref)
  =
  fun uu____7398  ->
    let term_type_set = string_set_ref_new ()  in
    let field_set = string_set_ref_new ()  in
    fun uu___107_7409  ->
      match uu___107_7409 with
      | Exported_id_term_type  -> term_type_set
      | Exported_id_field  -> field_set
  
let (unique :
  Prims.bool -> Prims.bool -> env -> FStar_Ident.lident -> Prims.bool) =
  fun any_val  ->
    fun exclude_interface  ->
      fun env  ->
        fun lid  ->
          let filter_scope_mods uu___108_7451 =
            match uu___108_7451 with
            | Rec_binding uu____7452 -> true
            | uu____7453 -> false  in
          let this_env =
            let uu___122_7455 = env  in
            let uu____7456 =
              FStar_List.filter filter_scope_mods env.scope_mods  in
            {
              curmodule = (uu___122_7455.curmodule);
              curmonad = (uu___122_7455.curmonad);
              modules = (uu___122_7455.modules);
              scope_mods = uu____7456;
              exported_ids = empty_exported_id_smap;
              trans_exported_ids = (uu___122_7455.trans_exported_ids);
              includes = empty_include_smap;
              sigaccum = (uu___122_7455.sigaccum);
              sigmap = (uu___122_7455.sigmap);
              iface = (uu___122_7455.iface);
              admitted_iface = (uu___122_7455.admitted_iface);
              expect_typ = (uu___122_7455.expect_typ);
              docs = (uu___122_7455.docs);
              remaining_iface_decls = (uu___122_7455.remaining_iface_decls);
              syntax_only = (uu___122_7455.syntax_only);
              ds_hooks = (uu___122_7455.ds_hooks)
            }  in
          let uu____7459 =
            try_lookup_lid' any_val exclude_interface this_env lid  in
          match uu____7459 with
          | FStar_Pervasives_Native.None  -> true
          | FStar_Pervasives_Native.Some uu____7478 -> false
  
let (push_scope_mod : env -> scope_mod -> env) =
  fun env  ->
    fun scope_mod  ->
      let uu___123_7501 = env  in
      {
        curmodule = (uu___123_7501.curmodule);
        curmonad = (uu___123_7501.curmonad);
        modules = (uu___123_7501.modules);
        scope_mods = (scope_mod :: (env.scope_mods));
        exported_ids = (uu___123_7501.exported_ids);
        trans_exported_ids = (uu___123_7501.trans_exported_ids);
        includes = (uu___123_7501.includes);
        sigaccum = (uu___123_7501.sigaccum);
        sigmap = (uu___123_7501.sigmap);
        iface = (uu___123_7501.iface);
        admitted_iface = (uu___123_7501.admitted_iface);
        expect_typ = (uu___123_7501.expect_typ);
        docs = (uu___123_7501.docs);
        remaining_iface_decls = (uu___123_7501.remaining_iface_decls);
        syntax_only = (uu___123_7501.syntax_only);
        ds_hooks = (uu___123_7501.ds_hooks)
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
        let uu____7546 =
          (unique false true env l) || (FStar_Options.interactive ())  in
        if uu____7546
        then push_scope_mod env (Rec_binding (x, l, dd))
        else
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_DuplicateTopLevelNames,
              (Prims.strcat "Duplicate top-level names " l.FStar_Ident.str))
            (FStar_Ident.range_of_lid l)
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let err l =
        let sopt = FStar_Util.smap_try_find (sigmap env) l.FStar_Ident.str
           in
        let r =
          match sopt with
          | FStar_Pervasives_Native.Some (se,uu____7571) ->
              let uu____7576 =
                FStar_Util.find_opt (FStar_Ident.lid_equals l)
                  (FStar_Syntax_Util.lids_of_sigelt se)
                 in
              (match uu____7576 with
               | FStar_Pervasives_Native.Some l1 ->
                   FStar_All.pipe_left FStar_Range.string_of_range
                     (FStar_Ident.range_of_lid l1)
               | FStar_Pervasives_Native.None  -> "<unknown>")
          | FStar_Pervasives_Native.None  -> "<unknown>"  in
        let uu____7584 =
          let uu____7589 =
            FStar_Util.format2
              "Duplicate top-level names [%s]; previously declared at %s"
              (FStar_Ident.text_of_lid l) r
             in
          (FStar_Errors.Fatal_DuplicateTopLevelNames, uu____7589)  in
        FStar_Errors.raise_error uu____7584 (FStar_Ident.range_of_lid l)  in
      let globals = FStar_Util.mk_ref env.scope_mods  in
      let env1 =
        let uu____7598 =
          match s.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let uu____7607 -> (false, true)
          | FStar_Syntax_Syntax.Sig_bundle uu____7614 -> (false, true)
          | uu____7623 -> (false, false)  in
        match uu____7598 with
        | (any_val,exclude_interface) ->
            let lids = FStar_Syntax_Util.lids_of_sigelt s  in
            let uu____7629 =
              FStar_Util.find_map lids
                (fun l  ->
                   let uu____7635 =
                     let uu____7636 = unique any_val exclude_interface env l
                        in
                     Prims.op_Negation uu____7636  in
                   if uu____7635
                   then FStar_Pervasives_Native.Some l
                   else FStar_Pervasives_Native.None)
               in
            (match uu____7629 with
             | FStar_Pervasives_Native.Some l -> err l
             | uu____7641 ->
                 (extract_record env globals s;
                  (let uu___124_7667 = env  in
                   {
                     curmodule = (uu___124_7667.curmodule);
                     curmonad = (uu___124_7667.curmonad);
                     modules = (uu___124_7667.modules);
                     scope_mods = (uu___124_7667.scope_mods);
                     exported_ids = (uu___124_7667.exported_ids);
                     trans_exported_ids = (uu___124_7667.trans_exported_ids);
                     includes = (uu___124_7667.includes);
                     sigaccum = (s :: (env.sigaccum));
                     sigmap = (uu___124_7667.sigmap);
                     iface = (uu___124_7667.iface);
                     admitted_iface = (uu___124_7667.admitted_iface);
                     expect_typ = (uu___124_7667.expect_typ);
                     docs = (uu___124_7667.docs);
                     remaining_iface_decls =
                       (uu___124_7667.remaining_iface_decls);
                     syntax_only = (uu___124_7667.syntax_only);
                     ds_hooks = (uu___124_7667.ds_hooks)
                   })))
         in
      let env2 =
        let uu___125_7669 = env1  in
        let uu____7670 = FStar_ST.op_Bang globals  in
        {
          curmodule = (uu___125_7669.curmodule);
          curmonad = (uu___125_7669.curmonad);
          modules = (uu___125_7669.modules);
          scope_mods = uu____7670;
          exported_ids = (uu___125_7669.exported_ids);
          trans_exported_ids = (uu___125_7669.trans_exported_ids);
          includes = (uu___125_7669.includes);
          sigaccum = (uu___125_7669.sigaccum);
          sigmap = (uu___125_7669.sigmap);
          iface = (uu___125_7669.iface);
          admitted_iface = (uu___125_7669.admitted_iface);
          expect_typ = (uu___125_7669.expect_typ);
          docs = (uu___125_7669.docs);
          remaining_iface_decls = (uu___125_7669.remaining_iface_decls);
          syntax_only = (uu___125_7669.syntax_only);
          ds_hooks = (uu___125_7669.ds_hooks)
        }  in
      let uu____7718 =
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_bundle (ses,uu____7744) ->
            let uu____7753 =
              FStar_List.map
                (fun se  -> ((FStar_Syntax_Util.lids_of_sigelt se), se)) ses
               in
            (env2, uu____7753)
        | uu____7780 -> (env2, [((FStar_Syntax_Util.lids_of_sigelt s), s)])
         in
      match uu____7718 with
      | (env3,lss) ->
          (FStar_All.pipe_right lss
             (FStar_List.iter
                (fun uu____7839  ->
                   match uu____7839 with
                   | (lids,se) ->
                       FStar_All.pipe_right lids
                         (FStar_List.iter
                            (fun lid  ->
                               (let uu____7861 =
                                  let uu____7864 = FStar_ST.op_Bang globals
                                     in
                                  (Top_level_def (lid.FStar_Ident.ident)) ::
                                    uu____7864
                                   in
                                FStar_ST.op_Colon_Equals globals uu____7861);
                               (match () with
                                | () ->
                                    let modul =
                                      let uu____7958 =
                                        FStar_Ident.lid_of_ids
                                          lid.FStar_Ident.ns
                                         in
                                      uu____7958.FStar_Ident.str  in
                                    ((let uu____7960 =
                                        get_exported_id_set env3 modul  in
                                      match uu____7960 with
                                      | FStar_Pervasives_Native.Some f ->
                                          let my_exported_ids =
                                            f Exported_id_term_type  in
                                          let uu____7990 =
                                            let uu____7991 =
                                              FStar_ST.op_Bang
                                                my_exported_ids
                                               in
                                            FStar_Util.set_add
                                              (lid.FStar_Ident.ident).FStar_Ident.idText
                                              uu____7991
                                             in
                                          FStar_ST.op_Colon_Equals
                                            my_exported_ids uu____7990
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
              let uu___126_8086 = env3  in
              let uu____8087 = FStar_ST.op_Bang globals  in
              {
                curmodule = (uu___126_8086.curmodule);
                curmonad = (uu___126_8086.curmonad);
                modules = (uu___126_8086.modules);
                scope_mods = uu____8087;
                exported_ids = (uu___126_8086.exported_ids);
                trans_exported_ids = (uu___126_8086.trans_exported_ids);
                includes = (uu___126_8086.includes);
                sigaccum = (uu___126_8086.sigaccum);
                sigmap = (uu___126_8086.sigmap);
                iface = (uu___126_8086.iface);
                admitted_iface = (uu___126_8086.admitted_iface);
                expect_typ = (uu___126_8086.expect_typ);
                docs = (uu___126_8086.docs);
                remaining_iface_decls = (uu___126_8086.remaining_iface_decls);
                syntax_only = (uu___126_8086.syntax_only);
                ds_hooks = (uu___126_8086.ds_hooks)
              }  in
            env4))
  
let (push_namespace : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun ns  ->
      let uu____8141 =
        let uu____8146 = resolve_module_name env ns false  in
        match uu____8146 with
        | FStar_Pervasives_Native.None  ->
            let modules = env.modules  in
            let uu____8160 =
              FStar_All.pipe_right modules
                (FStar_Util.for_some
                   (fun uu____8174  ->
                      match uu____8174 with
                      | (m,uu____8180) ->
                          FStar_Util.starts_with
                            (Prims.strcat (FStar_Ident.text_of_lid m) ".")
                            (Prims.strcat (FStar_Ident.text_of_lid ns) ".")))
               in
            if uu____8160
            then (ns, Open_namespace)
            else
              (let uu____8186 =
                 let uu____8191 =
                   FStar_Util.format1 "Namespace %s cannot be found"
                     (FStar_Ident.text_of_lid ns)
                    in
                 (FStar_Errors.Fatal_NameSpaceNotFound, uu____8191)  in
               FStar_Errors.raise_error uu____8186
                 (FStar_Ident.range_of_lid ns))
        | FStar_Pervasives_Native.Some ns' ->
            (fail_if_curmodule env ns ns'; (ns', Open_module))
         in
      match uu____8141 with
      | (ns',kd) ->
          ((env.ds_hooks).ds_push_open_hook env (ns', kd);
           push_scope_mod env (Open_module_or_namespace (ns', kd)))
  
let (push_include : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun ns  ->
      let ns0 = ns  in
      let uu____8208 = resolve_module_name env ns false  in
      match uu____8208 with
      | FStar_Pervasives_Native.Some ns1 ->
          ((env.ds_hooks).ds_push_include_hook env ns1;
           fail_if_curmodule env ns0 ns1;
           (let env1 =
              push_scope_mod env
                (Open_module_or_namespace (ns1, Open_module))
               in
            let curmod =
              let uu____8216 = current_module env1  in
              uu____8216.FStar_Ident.str  in
            (let uu____8218 = FStar_Util.smap_try_find env1.includes curmod
                in
             match uu____8218 with
             | FStar_Pervasives_Native.None  -> ()
             | FStar_Pervasives_Native.Some incl ->
                 let uu____8242 =
                   let uu____8245 = FStar_ST.op_Bang incl  in ns1 ::
                     uu____8245
                    in
                 FStar_ST.op_Colon_Equals incl uu____8242);
            (match () with
             | () ->
                 let uu____8338 =
                   get_trans_exported_id_set env1 ns1.FStar_Ident.str  in
                 (match uu____8338 with
                  | FStar_Pervasives_Native.Some ns_trans_exports ->
                      ((let uu____8355 =
                          let uu____8372 = get_exported_id_set env1 curmod
                             in
                          let uu____8379 =
                            get_trans_exported_id_set env1 curmod  in
                          (uu____8372, uu____8379)  in
                        match uu____8355 with
                        | (FStar_Pervasives_Native.Some
                           cur_exports,FStar_Pervasives_Native.Some
                           cur_trans_exports) ->
                            let update_exports k =
                              let ns_ex =
                                let uu____8433 = ns_trans_exports k  in
                                FStar_ST.op_Bang uu____8433  in
                              let ex = cur_exports k  in
                              (let uu____8559 =
                                 let uu____8560 = FStar_ST.op_Bang ex  in
                                 FStar_Util.set_difference uu____8560 ns_ex
                                  in
                               FStar_ST.op_Colon_Equals ex uu____8559);
                              (match () with
                               | () ->
                                   let trans_ex = cur_trans_exports k  in
                                   let uu____8660 =
                                     let uu____8661 =
                                       FStar_ST.op_Bang trans_ex  in
                                     FStar_Util.set_union uu____8661 ns_ex
                                      in
                                   FStar_ST.op_Colon_Equals trans_ex
                                     uu____8660)
                               in
                            FStar_List.iter update_exports
                              all_exported_id_kinds
                        | uu____8746 -> ());
                       (match () with | () -> env1))
                  | FStar_Pervasives_Native.None  ->
                      let uu____8767 =
                        let uu____8772 =
                          FStar_Util.format1
                            "include: Module %s was not prepared"
                            ns1.FStar_Ident.str
                           in
                        (FStar_Errors.Fatal_IncludeModuleNotPrepared,
                          uu____8772)
                         in
                      FStar_Errors.raise_error uu____8767
                        (FStar_Ident.range_of_lid ns1)))))
      | uu____8773 ->
          let uu____8776 =
            let uu____8781 =
              FStar_Util.format1 "include: Module %s cannot be found"
                ns.FStar_Ident.str
               in
            (FStar_Errors.Fatal_ModuleNotFound, uu____8781)  in
          FStar_Errors.raise_error uu____8776 (FStar_Ident.range_of_lid ns)
  
let (push_module_abbrev :
  env -> FStar_Ident.ident -> FStar_Ident.lident -> env) =
  fun env  ->
    fun x  ->
      fun l  ->
        let uu____8791 = module_is_defined env l  in
        if uu____8791
        then
          (fail_if_curmodule env l l;
           (env.ds_hooks).ds_push_module_abbrev_hook env x l;
           push_scope_mod env (Module_abbrev (x, l)))
        else
          (let uu____8795 =
             let uu____8800 =
               FStar_Util.format1 "Module %s cannot be found"
                 (FStar_Ident.text_of_lid l)
                in
             (FStar_Errors.Fatal_ModuleNotFound, uu____8800)  in
           FStar_Errors.raise_error uu____8795 (FStar_Ident.range_of_lid l))
  
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
            ((let uu____8816 =
                FStar_Util.smap_try_find env.docs l.FStar_Ident.str  in
              match uu____8816 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some old_doc ->
                  let uu____8820 =
                    let uu____8825 =
                      let uu____8826 = FStar_Ident.string_of_lid l  in
                      let uu____8827 =
                        FStar_Parser_AST.string_of_fsdoc old_doc  in
                      let uu____8828 = FStar_Parser_AST.string_of_fsdoc doc1
                         in
                      FStar_Util.format3
                        "Overwriting doc of %s; old doc was [%s]; new doc are [%s]"
                        uu____8826 uu____8827 uu____8828
                       in
                    (FStar_Errors.Warning_DocOverwrite, uu____8825)  in
                  FStar_Errors.log_issue (FStar_Ident.range_of_lid l)
                    uu____8820);
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
                      let uu____8864 =
                        FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption)
                         in
                      Prims.op_Negation uu____8864 ->
                      let uu____8867 =
                        FStar_Util.smap_try_find (sigmap env)
                          l.FStar_Ident.str
                         in
                      (match uu____8867 with
                       | FStar_Pervasives_Native.Some
                           ({
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_let uu____8880;
                              FStar_Syntax_Syntax.sigrng = uu____8881;
                              FStar_Syntax_Syntax.sigquals = uu____8882;
                              FStar_Syntax_Syntax.sigmeta = uu____8883;
                              FStar_Syntax_Syntax.sigattrs = uu____8884;_},uu____8885)
                           -> lids
                       | FStar_Pervasives_Native.Some
                           ({
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_inductive_typ
                                uu____8900;
                              FStar_Syntax_Syntax.sigrng = uu____8901;
                              FStar_Syntax_Syntax.sigquals = uu____8902;
                              FStar_Syntax_Syntax.sigmeta = uu____8903;
                              FStar_Syntax_Syntax.sigattrs = uu____8904;_},uu____8905)
                           -> lids
                       | uu____8930 ->
                           ((let uu____8938 =
                               let uu____8939 = FStar_Options.interactive ()
                                  in
                               Prims.op_Negation uu____8939  in
                             if uu____8938
                             then
                               let uu____8940 =
                                 let uu____8945 =
                                   let uu____8946 =
                                     FStar_Syntax_Print.lid_to_string l  in
                                   FStar_Util.format1
                                     "Admitting %s without a definition"
                                     uu____8946
                                    in
                                 (FStar_Errors.Warning_AdmitWithoutDefinition,
                                   uu____8945)
                                  in
                               FStar_Errors.log_issue
                                 (FStar_Ident.range_of_lid l) uu____8940
                             else ());
                            (let quals = FStar_Syntax_Syntax.Assumption ::
                               (se.FStar_Syntax_Syntax.sigquals)  in
                             FStar_Util.smap_add (sigmap env)
                               l.FStar_Ident.str
                               ((let uu___127_8957 = se  in
                                 {
                                   FStar_Syntax_Syntax.sigel =
                                     (uu___127_8957.FStar_Syntax_Syntax.sigel);
                                   FStar_Syntax_Syntax.sigrng =
                                     (uu___127_8957.FStar_Syntax_Syntax.sigrng);
                                   FStar_Syntax_Syntax.sigquals = quals;
                                   FStar_Syntax_Syntax.sigmeta =
                                     (uu___127_8957.FStar_Syntax_Syntax.sigmeta);
                                   FStar_Syntax_Syntax.sigattrs =
                                     (uu___127_8957.FStar_Syntax_Syntax.sigattrs)
                                 }), false);
                             l
                             ::
                             lids)))
                  | uu____8958 -> lids) [])
         in
      let uu___128_8959 = m  in
      let uu____8960 =
        FStar_All.pipe_right m.FStar_Syntax_Syntax.declarations
          (FStar_List.map
             (fun s  ->
                match s.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_declare_typ
                    (lid,uu____8970,uu____8971) when
                    FStar_List.existsb
                      (fun l  -> FStar_Ident.lid_equals l lid)
                      admitted_sig_lids
                    ->
                    let uu___129_8974 = s  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___129_8974.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___129_8974.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals =
                        (FStar_Syntax_Syntax.Assumption ::
                        (s.FStar_Syntax_Syntax.sigquals));
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___129_8974.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___129_8974.FStar_Syntax_Syntax.sigattrs)
                    }
                | uu____8975 -> s))
         in
      {
        FStar_Syntax_Syntax.name = (uu___128_8959.FStar_Syntax_Syntax.name);
        FStar_Syntax_Syntax.declarations = uu____8960;
        FStar_Syntax_Syntax.exports =
          (uu___128_8959.FStar_Syntax_Syntax.exports);
        FStar_Syntax_Syntax.is_interface =
          (uu___128_8959.FStar_Syntax_Syntax.is_interface)
      }
  
let (finish : env -> FStar_Syntax_Syntax.modul -> env) =
  fun env  ->
    fun modul  ->
      FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations
        (FStar_List.iter
           (fun se  ->
              let quals = se.FStar_Syntax_Syntax.sigquals  in
              match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_bundle (ses,uu____8992) ->
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
                                (lid,uu____9012,uu____9013,uu____9014,uu____9015,uu____9016)
                                ->
                                FStar_Util.smap_remove (sigmap env)
                                  lid.FStar_Ident.str
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (lid,univ_names,binders,typ,uu____9029,uu____9030)
                                ->
                                (FStar_Util.smap_remove (sigmap env)
                                   lid.FStar_Ident.str;
                                 if
                                   Prims.op_Negation
                                     (FStar_List.contains
                                        FStar_Syntax_Syntax.Private quals)
                                 then
                                   (let sigel =
                                      let uu____9045 =
                                        let uu____9052 =
                                          let uu____9055 =
                                            let uu____9058 =
                                              let uu____9059 =
                                                let uu____9072 =
                                                  FStar_Syntax_Syntax.mk_Total
                                                    typ
                                                   in
                                                (binders, uu____9072)  in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____9059
                                               in
                                            FStar_Syntax_Syntax.mk uu____9058
                                             in
                                          uu____9055
                                            FStar_Pervasives_Native.None
                                            (FStar_Ident.range_of_lid lid)
                                           in
                                        (lid, univ_names, uu____9052)  in
                                      FStar_Syntax_Syntax.Sig_declare_typ
                                        uu____9045
                                       in
                                    let se2 =
                                      let uu___130_9079 = se1  in
                                      {
                                        FStar_Syntax_Syntax.sigel = sigel;
                                        FStar_Syntax_Syntax.sigrng =
                                          (uu___130_9079.FStar_Syntax_Syntax.sigrng);
                                        FStar_Syntax_Syntax.sigquals =
                                          (FStar_Syntax_Syntax.Assumption ::
                                          quals);
                                        FStar_Syntax_Syntax.sigmeta =
                                          (uu___130_9079.FStar_Syntax_Syntax.sigmeta);
                                        FStar_Syntax_Syntax.sigattrs =
                                          (uu___130_9079.FStar_Syntax_Syntax.sigattrs)
                                      }  in
                                    FStar_Util.smap_add (sigmap env)
                                      lid.FStar_Ident.str (se2, false))
                                 else ())
                            | uu____9085 -> ()))
                  else ()
              | FStar_Syntax_Syntax.Sig_declare_typ
                  (lid,uu____9088,uu____9089) ->
                  if FStar_List.contains FStar_Syntax_Syntax.Private quals
                  then
                    FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str
                  else ()
              | FStar_Syntax_Syntax.Sig_let ((uu____9095,lbs),uu____9097) ->
                  (if
                     (FStar_List.contains FStar_Syntax_Syntax.Private quals)
                       ||
                       (FStar_List.contains FStar_Syntax_Syntax.Abstract
                          quals)
                   then
                     FStar_All.pipe_right lbs
                       (FStar_List.iter
                          (fun lb  ->
                             let uu____9118 =
                               let uu____9119 =
                                 let uu____9120 =
                                   let uu____9123 =
                                     FStar_Util.right
                                       lb.FStar_Syntax_Syntax.lbname
                                      in
                                   uu____9123.FStar_Syntax_Syntax.fv_name  in
                                 uu____9120.FStar_Syntax_Syntax.v  in
                               uu____9119.FStar_Ident.str  in
                             FStar_Util.smap_remove (sigmap env) uu____9118))
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
                               let uu____9137 =
                                 let uu____9140 =
                                   FStar_Util.right
                                     lb.FStar_Syntax_Syntax.lbname
                                    in
                                 uu____9140.FStar_Syntax_Syntax.fv_name  in
                               uu____9137.FStar_Syntax_Syntax.v  in
                             let quals1 = FStar_Syntax_Syntax.Assumption ::
                               quals  in
                             let decl =
                               let uu___131_9145 = se  in
                               {
                                 FStar_Syntax_Syntax.sigel =
                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                      (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                        (lb.FStar_Syntax_Syntax.lbtyp)));
                                 FStar_Syntax_Syntax.sigrng =
                                   (uu___131_9145.FStar_Syntax_Syntax.sigrng);
                                 FStar_Syntax_Syntax.sigquals = quals1;
                                 FStar_Syntax_Syntax.sigmeta =
                                   (uu___131_9145.FStar_Syntax_Syntax.sigmeta);
                                 FStar_Syntax_Syntax.sigattrs =
                                   (uu___131_9145.FStar_Syntax_Syntax.sigattrs)
                               }  in
                             FStar_Util.smap_add (sigmap env)
                               lid.FStar_Ident.str (decl, false)))
                   else ())
              | uu____9155 -> ()));
      (let curmod =
         let uu____9157 = current_module env  in uu____9157.FStar_Ident.str
          in
       (let uu____9159 =
          let uu____9176 = get_exported_id_set env curmod  in
          let uu____9183 = get_trans_exported_id_set env curmod  in
          (uu____9176, uu____9183)  in
        match uu____9159 with
        | (FStar_Pervasives_Native.Some cur_ex,FStar_Pervasives_Native.Some
           cur_trans_ex) ->
            let update_exports eikind =
              let cur_ex_set =
                let uu____9237 = cur_ex eikind  in
                FStar_ST.op_Bang uu____9237  in
              let cur_trans_ex_set_ref = cur_trans_ex eikind  in
              let uu____9362 =
                let uu____9363 = FStar_ST.op_Bang cur_trans_ex_set_ref  in
                FStar_Util.set_union cur_ex_set uu____9363  in
              FStar_ST.op_Colon_Equals cur_trans_ex_set_ref uu____9362  in
            FStar_List.iter update_exports all_exported_id_kinds
        | uu____9448 -> ());
       (match () with
        | () ->
            (filter_record_cache ();
             (match () with
              | () ->
                  let uu___132_9466 = env  in
                  {
                    curmodule = FStar_Pervasives_Native.None;
                    curmonad = (uu___132_9466.curmonad);
                    modules = (((modul.FStar_Syntax_Syntax.name), modul) ::
                      (env.modules));
                    scope_mods = [];
                    exported_ids = (uu___132_9466.exported_ids);
                    trans_exported_ids = (uu___132_9466.trans_exported_ids);
                    includes = (uu___132_9466.includes);
                    sigaccum = [];
                    sigmap = (uu___132_9466.sigmap);
                    iface = (uu___132_9466.iface);
                    admitted_iface = (uu___132_9466.admitted_iface);
                    expect_typ = (uu___132_9466.expect_typ);
                    docs = (uu___132_9466.docs);
                    remaining_iface_decls =
                      (uu___132_9466.remaining_iface_decls);
                    syntax_only = (uu___132_9466.syntax_only);
                    ds_hooks = (uu___132_9466.ds_hooks)
                  }))))
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push : env -> env) =
  fun env  ->
    push_record_cache ();
    (let uu____9493 =
       let uu____9496 = FStar_ST.op_Bang stack  in env :: uu____9496  in
     FStar_ST.op_Colon_Equals stack uu____9493);
    (let uu___133_9545 = env  in
     let uu____9546 = FStar_Util.smap_copy (sigmap env)  in
     let uu____9557 = FStar_Util.smap_copy env.docs  in
     {
       curmodule = (uu___133_9545.curmodule);
       curmonad = (uu___133_9545.curmonad);
       modules = (uu___133_9545.modules);
       scope_mods = (uu___133_9545.scope_mods);
       exported_ids = (uu___133_9545.exported_ids);
       trans_exported_ids = (uu___133_9545.trans_exported_ids);
       includes = (uu___133_9545.includes);
       sigaccum = (uu___133_9545.sigaccum);
       sigmap = uu____9546;
       iface = (uu___133_9545.iface);
       admitted_iface = (uu___133_9545.admitted_iface);
       expect_typ = (uu___133_9545.expect_typ);
       docs = uu____9557;
       remaining_iface_decls = (uu___133_9545.remaining_iface_decls);
       syntax_only = (uu___133_9545.syntax_only);
       ds_hooks = (uu___133_9545.ds_hooks)
     })
  
let (pop : Prims.unit -> env) =
  fun uu____9562  ->
    let uu____9563 = FStar_ST.op_Bang stack  in
    match uu____9563 with
    | env::tl1 ->
        (pop_record_cache (); FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____9618 -> failwith "Impossible: Too many pops"
  
let (export_interface : FStar_Ident.lident -> env -> env) =
  fun m  ->
    fun env  ->
      let sigelt_in_m se =
        match FStar_Syntax_Util.lids_of_sigelt se with
        | l::uu____9632 -> l.FStar_Ident.nsstr = m.FStar_Ident.str
        | uu____9635 -> false  in
      let sm = sigmap env  in
      let env1 = pop ()  in
      let keys = FStar_Util.smap_keys sm  in
      let sm' = sigmap env1  in
      FStar_All.pipe_right keys
        (FStar_List.iter
           (fun k  ->
              let uu____9669 = FStar_Util.smap_try_find sm' k  in
              match uu____9669 with
              | FStar_Pervasives_Native.Some (se,true ) when sigelt_in_m se
                  ->
                  (FStar_Util.smap_remove sm' k;
                   (let se1 =
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t) ->
                          let uu___134_9694 = se  in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (uu___134_9694.FStar_Syntax_Syntax.sigel);
                            FStar_Syntax_Syntax.sigrng =
                              (uu___134_9694.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (FStar_Syntax_Syntax.Assumption ::
                              (se.FStar_Syntax_Syntax.sigquals));
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___134_9694.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___134_9694.FStar_Syntax_Syntax.sigattrs)
                          }
                      | uu____9695 -> se  in
                    FStar_Util.smap_add sm' k (se1, false)))
              | uu____9700 -> ()));
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
      let uu____9719 = finish env modul1  in (uu____9719, modul1)
  
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
      let uu____9797 =
        let uu____9800 = e Exported_id_term_type  in
        FStar_ST.op_Bang uu____9800  in
      FStar_Util.set_elements uu____9797  in
    let fields =
      let uu____9914 =
        let uu____9917 = e Exported_id_field  in FStar_ST.op_Bang uu____9917
         in
      FStar_Util.set_elements uu____9914  in
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
          let uu____10064 =
            FStar_Util.as_set e1.exported_id_terms FStar_Util.compare  in
          FStar_Util.mk_ref uu____10064  in
        let fields =
          let uu____10074 =
            FStar_Util.as_set e1.exported_id_fields FStar_Util.compare  in
          FStar_Util.mk_ref uu____10074  in
        (fun uu___109_10079  ->
           match uu___109_10079 with
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
  'Auu____10199 .
    'Auu____10199 Prims.list FStar_Pervasives_Native.option ->
      'Auu____10199 Prims.list FStar_ST.ref
  =
  fun uu___110_10211  ->
    match uu___110_10211 with
    | FStar_Pervasives_Native.None  -> FStar_Util.mk_ref []
    | FStar_Pervasives_Native.Some l -> FStar_Util.mk_ref l
  
let (inclusion_info : env -> FStar_Ident.lident -> module_inclusion_info) =
  fun env  ->
    fun l  ->
      let mname = FStar_Ident.string_of_lid l  in
      let as_ids_opt m =
        let uu____10244 = FStar_Util.smap_try_find m mname  in
        FStar_Util.map_opt uu____10244 as_exported_ids  in
      let uu____10247 = as_ids_opt env.exported_ids  in
      let uu____10250 = as_ids_opt env.trans_exported_ids  in
      let uu____10253 =
        let uu____10258 = FStar_Util.smap_try_find env.includes mname  in
        FStar_Util.map_opt uu____10258 (fun r  -> FStar_ST.op_Bang r)  in
      {
        mii_exported_ids = uu____10247;
        mii_trans_exported_ids = uu____10250;
        mii_includes = uu____10253
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
                FStar_Util.strcat (FStar_Ident.text_of_lid mname) ".fst"  in
              let auto_open =
                FStar_Parser_Dep.hard_coded_dependencies filename  in
              let auto_open1 =
                let convert_kind uu___111_10378 =
                  match uu___111_10378 with
                  | FStar_Parser_Dep.Open_namespace  -> Open_namespace
                  | FStar_Parser_Dep.Open_module  -> Open_module  in
                FStar_List.map
                  (fun uu____10390  ->
                     match uu____10390 with
                     | (lid,kind) -> (lid, (convert_kind kind))) auto_open
                 in
              let namespace_of_module =
                if
                  (FStar_List.length mname.FStar_Ident.ns) >
                    (Prims.parse_int "0")
                then
                  let uu____10414 =
                    let uu____10419 =
                      FStar_Ident.lid_of_ids mname.FStar_Ident.ns  in
                    (uu____10419, Open_namespace)  in
                  [uu____10414]
                else []  in
              let auto_open2 =
                FStar_List.append namespace_of_module
                  (FStar_List.rev auto_open1)
                 in
              (let uu____10449 = as_exported_id_set mii.mii_exported_ids  in
               FStar_Util.smap_add env1.exported_ids mname.FStar_Ident.str
                 uu____10449);
              (match () with
               | () ->
                   ((let uu____10473 =
                       as_exported_id_set mii.mii_trans_exported_ids  in
                     FStar_Util.smap_add env1.trans_exported_ids
                       mname.FStar_Ident.str uu____10473);
                    (match () with
                     | () ->
                         ((let uu____10497 = as_includes mii.mii_includes  in
                           FStar_Util.smap_add env1.includes
                             mname.FStar_Ident.str uu____10497);
                          (match () with
                           | () ->
                               let env' =
                                 let uu___135_10529 = env1  in
                                 let uu____10530 =
                                   FStar_List.map
                                     (fun x  -> Open_module_or_namespace x)
                                     auto_open2
                                    in
                                 {
                                   curmodule =
                                     (FStar_Pervasives_Native.Some mname);
                                   curmonad = (uu___135_10529.curmonad);
                                   modules = (uu___135_10529.modules);
                                   scope_mods = uu____10530;
                                   exported_ids =
                                     (uu___135_10529.exported_ids);
                                   trans_exported_ids =
                                     (uu___135_10529.trans_exported_ids);
                                   includes = (uu___135_10529.includes);
                                   sigaccum = (uu___135_10529.sigaccum);
                                   sigmap = (env1.sigmap);
                                   iface = intf;
                                   admitted_iface = admitted;
                                   expect_typ = (uu___135_10529.expect_typ);
                                   docs = (uu___135_10529.docs);
                                   remaining_iface_decls =
                                     (uu___135_10529.remaining_iface_decls);
                                   syntax_only = (uu___135_10529.syntax_only);
                                   ds_hooks = (uu___135_10529.ds_hooks)
                                 }  in
                               (FStar_List.iter
                                  (fun op  ->
                                     (env1.ds_hooks).ds_push_open_hook env'
                                       op) (FStar_List.rev auto_open2);
                                env'))))))
               in
            let uu____10542 =
              FStar_All.pipe_right env.modules
                (FStar_Util.find_opt
                   (fun uu____10568  ->
                      match uu____10568 with
                      | (l,uu____10574) -> FStar_Ident.lid_equals l mname))
               in
            match uu____10542 with
            | FStar_Pervasives_Native.None  ->
                let uu____10583 = prep env  in (uu____10583, false)
            | FStar_Pervasives_Native.Some (uu____10584,m) ->
                ((let uu____10591 =
                    (let uu____10594 = FStar_Options.interactive ()  in
                     Prims.op_Negation uu____10594) &&
                      ((Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)
                         || intf)
                     in
                  if uu____10591
                  then
                    let uu____10595 =
                      let uu____10600 =
                        FStar_Util.format1
                          "Duplicate module or interface name: %s"
                          mname.FStar_Ident.str
                         in
                      (FStar_Errors.Fatal_DuplicateModuleOrInterface,
                        uu____10600)
                       in
                    FStar_Errors.raise_error uu____10595
                      (FStar_Ident.range_of_lid mname)
                  else ());
                 (let uu____10602 =
                    let uu____10603 = push env  in prep uu____10603  in
                  (uu____10602, true)))
  
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
          let uu___136_10611 = env  in
          {
            curmodule = (uu___136_10611.curmodule);
            curmonad = (FStar_Pervasives_Native.Some mname);
            modules = (uu___136_10611.modules);
            scope_mods = (uu___136_10611.scope_mods);
            exported_ids = (uu___136_10611.exported_ids);
            trans_exported_ids = (uu___136_10611.trans_exported_ids);
            includes = (uu___136_10611.includes);
            sigaccum = (uu___136_10611.sigaccum);
            sigmap = (uu___136_10611.sigmap);
            iface = (uu___136_10611.iface);
            admitted_iface = (uu___136_10611.admitted_iface);
            expect_typ = (uu___136_10611.expect_typ);
            docs = (uu___136_10611.docs);
            remaining_iface_decls = (uu___136_10611.remaining_iface_decls);
            syntax_only = (uu___136_10611.syntax_only);
            ds_hooks = (uu___136_10611.ds_hooks)
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
        let uu____10638 = lookup1 lid  in
        match uu____10638 with
        | FStar_Pervasives_Native.None  ->
            let opened_modules =
              FStar_List.map
                (fun uu____10651  ->
                   match uu____10651 with
                   | (lid1,uu____10657) -> FStar_Ident.text_of_lid lid1)
                env.modules
               in
            let msg =
              FStar_Util.format1 "Identifier not found: [%s]"
                (FStar_Ident.text_of_lid lid)
               in
            let msg1 =
              if
                (FStar_List.length lid.FStar_Ident.ns) =
                  (Prims.parse_int "0")
              then msg
              else
                (let modul =
                   let uu____10662 =
                     FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
                   FStar_Ident.set_lid_range uu____10662
                     (FStar_Ident.range_of_lid lid)
                    in
                 let uu____10663 = resolve_module_name env modul true  in
                 match uu____10663 with
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
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_IdentifierNotFound, msg1)
              (FStar_Ident.range_of_lid lid)
        | FStar_Pervasives_Native.Some r -> r
  
let fail_or2 :
  'a .
    (FStar_Ident.ident -> 'a FStar_Pervasives_Native.option) ->
      FStar_Ident.ident -> 'a
  =
  fun lookup1  ->
    fun id1  ->
      let uu____10694 = lookup1 id1  in
      match uu____10694 with
      | FStar_Pervasives_Native.None  ->
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_IdentifierNotFound,
              (Prims.strcat "Identifier not found ["
                 (Prims.strcat id1.FStar_Ident.idText "]")))
            id1.FStar_Ident.idRange
      | FStar_Pervasives_Native.Some r -> r
  