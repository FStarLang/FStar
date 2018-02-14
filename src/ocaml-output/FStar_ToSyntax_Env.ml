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
    ds_push_open_hook = (fun uu____1613  -> fun uu____1614  -> ());
    ds_push_include_hook = (fun uu____1617  -> fun uu____1618  -> ());
    ds_push_module_abbrev_hook =
      (fun uu____1622  -> fun uu____1623  -> fun uu____1624  -> ())
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
    match projectee with | Term_name _0 -> true | uu____1657 -> false
  
let (__proj__Term_name__item___0 :
  foundname ->
    (FStar_Syntax_Syntax.typ,Prims.bool,FStar_Syntax_Syntax.attribute
                                          Prims.list)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Term_name _0 -> _0 
let (uu___is_Eff_name : foundname -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eff_name _0 -> true | uu____1697 -> false
  
let (__proj__Eff_name__item___0 :
  foundname ->
    (FStar_Syntax_Syntax.sigelt,FStar_Ident.lident)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Eff_name _0 -> _0 
let (set_iface : env -> Prims.bool -> env) =
  fun env  ->
    fun b  ->
      let uu___111_1723 = env  in
      {
        curmodule = (uu___111_1723.curmodule);
        curmonad = (uu___111_1723.curmonad);
        modules = (uu___111_1723.modules);
        scope_mods = (uu___111_1723.scope_mods);
        exported_ids = (uu___111_1723.exported_ids);
        trans_exported_ids = (uu___111_1723.trans_exported_ids);
        includes = (uu___111_1723.includes);
        sigaccum = (uu___111_1723.sigaccum);
        sigmap = (uu___111_1723.sigmap);
        iface = b;
        admitted_iface = (uu___111_1723.admitted_iface);
        expect_typ = (uu___111_1723.expect_typ);
        docs = (uu___111_1723.docs);
        remaining_iface_decls = (uu___111_1723.remaining_iface_decls);
        syntax_only = (uu___111_1723.syntax_only);
        ds_hooks = (uu___111_1723.ds_hooks)
      }
  
let (iface : env -> Prims.bool) = fun e  -> e.iface 
let (set_admitted_iface : env -> Prims.bool -> env) =
  fun e  ->
    fun b  ->
      let uu___112_1733 = e  in
      {
        curmodule = (uu___112_1733.curmodule);
        curmonad = (uu___112_1733.curmonad);
        modules = (uu___112_1733.modules);
        scope_mods = (uu___112_1733.scope_mods);
        exported_ids = (uu___112_1733.exported_ids);
        trans_exported_ids = (uu___112_1733.trans_exported_ids);
        includes = (uu___112_1733.includes);
        sigaccum = (uu___112_1733.sigaccum);
        sigmap = (uu___112_1733.sigmap);
        iface = (uu___112_1733.iface);
        admitted_iface = b;
        expect_typ = (uu___112_1733.expect_typ);
        docs = (uu___112_1733.docs);
        remaining_iface_decls = (uu___112_1733.remaining_iface_decls);
        syntax_only = (uu___112_1733.syntax_only);
        ds_hooks = (uu___112_1733.ds_hooks)
      }
  
let (admitted_iface : env -> Prims.bool) = fun e  -> e.admitted_iface 
let (set_expect_typ : env -> Prims.bool -> env) =
  fun e  ->
    fun b  ->
      let uu___113_1743 = e  in
      {
        curmodule = (uu___113_1743.curmodule);
        curmonad = (uu___113_1743.curmonad);
        modules = (uu___113_1743.modules);
        scope_mods = (uu___113_1743.scope_mods);
        exported_ids = (uu___113_1743.exported_ids);
        trans_exported_ids = (uu___113_1743.trans_exported_ids);
        includes = (uu___113_1743.includes);
        sigaccum = (uu___113_1743.sigaccum);
        sigmap = (uu___113_1743.sigmap);
        iface = (uu___113_1743.iface);
        admitted_iface = (uu___113_1743.admitted_iface);
        expect_typ = b;
        docs = (uu___113_1743.docs);
        remaining_iface_decls = (uu___113_1743.remaining_iface_decls);
        syntax_only = (uu___113_1743.syntax_only);
        ds_hooks = (uu___113_1743.ds_hooks)
      }
  
let (expect_typ : env -> Prims.bool) = fun e  -> e.expect_typ 
let (all_exported_id_kinds : exported_id_kind Prims.list) =
  [Exported_id_field; Exported_id_term_type] 
let (transitive_exported_ids :
  env -> FStar_Ident.lident -> Prims.string Prims.list) =
  fun env  ->
    fun lid  ->
      let module_name = FStar_Ident.string_of_lid lid  in
      let uu____1758 =
        FStar_Util.smap_try_find env.trans_exported_ids module_name  in
      match uu____1758 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some exported_id_set ->
          let uu____1764 =
            let uu____1765 = exported_id_set Exported_id_term_type  in
            FStar_ST.op_Bang uu____1765  in
          FStar_All.pipe_right uu____1764 FStar_Util.set_elements
  
let (open_modules :
  env ->
    (FStar_Ident.lident,FStar_Syntax_Syntax.modul)
      FStar_Pervasives_Native.tuple2 Prims.list)
  = fun e  -> e.modules 
let (open_modules_and_namespaces : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    FStar_List.filter_map
      (fun uu___79_1973  ->
         match uu___79_1973 with
         | Open_module_or_namespace (lid,_info) ->
             FStar_Pervasives_Native.Some lid
         | uu____1978 -> FStar_Pervasives_Native.None) env.scope_mods
  
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun e  ->
    fun l  ->
      let uu___114_1985 = e  in
      {
        curmodule = (FStar_Pervasives_Native.Some l);
        curmonad = (uu___114_1985.curmonad);
        modules = (uu___114_1985.modules);
        scope_mods = (uu___114_1985.scope_mods);
        exported_ids = (uu___114_1985.exported_ids);
        trans_exported_ids = (uu___114_1985.trans_exported_ids);
        includes = (uu___114_1985.includes);
        sigaccum = (uu___114_1985.sigaccum);
        sigmap = (uu___114_1985.sigmap);
        iface = (uu___114_1985.iface);
        admitted_iface = (uu___114_1985.admitted_iface);
        expect_typ = (uu___114_1985.expect_typ);
        docs = (uu___114_1985.docs);
        remaining_iface_decls = (uu___114_1985.remaining_iface_decls);
        syntax_only = (uu___114_1985.syntax_only);
        ds_hooks = (uu___114_1985.ds_hooks)
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
      let uu____2000 =
        FStar_All.pipe_right env.remaining_iface_decls
          (FStar_List.tryFind
             (fun uu____2034  ->
                match uu____2034 with
                | (m,uu____2042) -> FStar_Ident.lid_equals l m))
         in
      match uu____2000 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (uu____2059,decls) ->
          FStar_Pervasives_Native.Some decls
  
let (set_iface_decls :
  env -> FStar_Ident.lident -> FStar_Parser_AST.decl Prims.list -> env) =
  fun env  ->
    fun l  ->
      fun ds  ->
        let uu____2086 =
          FStar_List.partition
            (fun uu____2116  ->
               match uu____2116 with
               | (m,uu____2124) -> FStar_Ident.lid_equals l m)
            env.remaining_iface_decls
           in
        match uu____2086 with
        | (uu____2129,rest) ->
            let uu___115_2163 = env  in
            {
              curmodule = (uu___115_2163.curmodule);
              curmonad = (uu___115_2163.curmonad);
              modules = (uu___115_2163.modules);
              scope_mods = (uu___115_2163.scope_mods);
              exported_ids = (uu___115_2163.exported_ids);
              trans_exported_ids = (uu___115_2163.trans_exported_ids);
              includes = (uu___115_2163.includes);
              sigaccum = (uu___115_2163.sigaccum);
              sigmap = (uu___115_2163.sigmap);
              iface = (uu___115_2163.iface);
              admitted_iface = (uu___115_2163.admitted_iface);
              expect_typ = (uu___115_2163.expect_typ);
              docs = (uu___115_2163.docs);
              remaining_iface_decls = ((l, ds) :: rest);
              syntax_only = (uu___115_2163.syntax_only);
              ds_hooks = (uu___115_2163.ds_hooks)
            }
  
let (qual : FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident) =
  FStar_Syntax_Util.qual_id 
let (qualify : env -> FStar_Ident.ident -> FStar_Ident.lident) =
  fun env  ->
    fun id1  ->
      match env.curmonad with
      | FStar_Pervasives_Native.None  ->
          let uu____2182 = current_module env  in qual uu____2182 id1
      | FStar_Pervasives_Native.Some monad ->
          let uu____2184 =
            let uu____2185 = current_module env  in qual uu____2185 monad  in
          FStar_Syntax_Util.mk_field_projector_name_from_ident uu____2184 id1
  
let (syntax_only : env -> Prims.bool) = fun env  -> env.syntax_only 
let (set_syntax_only : env -> Prims.bool -> env) =
  fun env  ->
    fun b  ->
      let uu___116_2195 = env  in
      {
        curmodule = (uu___116_2195.curmodule);
        curmonad = (uu___116_2195.curmonad);
        modules = (uu___116_2195.modules);
        scope_mods = (uu___116_2195.scope_mods);
        exported_ids = (uu___116_2195.exported_ids);
        trans_exported_ids = (uu___116_2195.trans_exported_ids);
        includes = (uu___116_2195.includes);
        sigaccum = (uu___116_2195.sigaccum);
        sigmap = (uu___116_2195.sigmap);
        iface = (uu___116_2195.iface);
        admitted_iface = (uu___116_2195.admitted_iface);
        expect_typ = (uu___116_2195.expect_typ);
        docs = (uu___116_2195.docs);
        remaining_iface_decls = (uu___116_2195.remaining_iface_decls);
        syntax_only = b;
        ds_hooks = (uu___116_2195.ds_hooks)
      }
  
let (ds_hooks : env -> dsenv_hooks) = fun env  -> env.ds_hooks 
let (set_ds_hooks : env -> dsenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___117_2205 = env  in
      {
        curmodule = (uu___117_2205.curmodule);
        curmonad = (uu___117_2205.curmonad);
        modules = (uu___117_2205.modules);
        scope_mods = (uu___117_2205.scope_mods);
        exported_ids = (uu___117_2205.exported_ids);
        trans_exported_ids = (uu___117_2205.trans_exported_ids);
        includes = (uu___117_2205.includes);
        sigaccum = (uu___117_2205.sigaccum);
        sigmap = (uu___117_2205.sigmap);
        iface = (uu___117_2205.iface);
        admitted_iface = (uu___117_2205.admitted_iface);
        expect_typ = (uu___117_2205.expect_typ);
        docs = (uu___117_2205.docs);
        remaining_iface_decls = (uu___117_2205.remaining_iface_decls);
        syntax_only = (uu___117_2205.syntax_only);
        ds_hooks = hooks
      }
  
let new_sigmap : 'Auu____2208 . Prims.unit -> 'Auu____2208 FStar_Util.smap =
  fun uu____2214  -> FStar_Util.smap_create (Prims.parse_int "100") 
let (empty_env : Prims.unit -> env) =
  fun uu____2217  ->
    let uu____2218 = new_sigmap ()  in
    let uu____2221 = new_sigmap ()  in
    let uu____2224 = new_sigmap ()  in
    let uu____2235 = new_sigmap ()  in
    let uu____2246 = new_sigmap ()  in
    {
      curmodule = FStar_Pervasives_Native.None;
      curmonad = FStar_Pervasives_Native.None;
      modules = [];
      scope_mods = [];
      exported_ids = uu____2218;
      trans_exported_ids = uu____2221;
      includes = uu____2224;
      sigaccum = [];
      sigmap = uu____2235;
      iface = false;
      admitted_iface = false;
      expect_typ = false;
      docs = uu____2246;
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
      (fun uu____2278  ->
         match uu____2278 with
         | (m,uu____2284) ->
             FStar_Ident.lid_equals m FStar_Parser_Const.all_lid) env.modules
  
let (set_bv_range :
  FStar_Syntax_Syntax.bv -> FStar_Range.range -> FStar_Syntax_Syntax.bv) =
  fun bv  ->
    fun r  ->
      let id1 =
        let uu___118_2292 = bv.FStar_Syntax_Syntax.ppname  in
        {
          FStar_Ident.idText = (uu___118_2292.FStar_Ident.idText);
          FStar_Ident.idRange = r
        }  in
      let uu___119_2293 = bv  in
      {
        FStar_Syntax_Syntax.ppname = id1;
        FStar_Syntax_Syntax.index = (uu___119_2293.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = (uu___119_2293.FStar_Syntax_Syntax.sort)
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
        (fun uu____2380  ->
           match uu____2380 with
           | (x,y,dd,dq) ->
               if id1.FStar_Ident.idText = x
               then
                 let uu____2403 =
                   let uu____2404 =
                     FStar_Ident.lid_of_path ["Prims"; y]
                       id1.FStar_Ident.idRange
                      in
                   FStar_Syntax_Syntax.fvar uu____2404 dd dq  in
                 FStar_Pervasives_Native.Some uu____2403
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
    match projectee with | Cont_ok _0 -> true | uu____2447 -> false
  
let __proj__Cont_ok__item___0 : 'a . 'a cont_t -> 'a =
  fun projectee  -> match projectee with | Cont_ok _0 -> _0 
let uu___is_Cont_fail : 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_fail  -> true | uu____2476 -> false
  
let uu___is_Cont_ignore : 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_ignore  -> true | uu____2490 -> false
  
let option_of_cont :
  'a .
    (Prims.unit -> 'a FStar_Pervasives_Native.option) ->
      'a cont_t -> 'a FStar_Pervasives_Native.option
  =
  fun k_ignore  ->
    fun uu___80_2513  ->
      match uu___80_2513 with
      | Cont_ok a -> FStar_Pervasives_Native.Some a
      | Cont_fail  -> FStar_Pervasives_Native.None
      | Cont_ignore  -> k_ignore ()
  
let find_in_record :
  'Auu____2526 .
    FStar_Ident.ident Prims.list ->
      FStar_Ident.ident ->
        record_or_dc ->
          (record_or_dc -> 'Auu____2526 cont_t) -> 'Auu____2526 cont_t
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
                (fun uu____2572  ->
                   match uu____2572 with
                   | (f,uu____2580) ->
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
  fun uu___81_2626  ->
    match uu___81_2626 with
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
              let rec aux uu___82_2682 =
                match uu___82_2682 with
                | [] -> find_in_module_default
                | modul::q ->
                    let mname = modul.FStar_Ident.str  in
                    let not_shadowed =
                      let uu____2693 = get_exported_id_set env mname  in
                      match uu____2693 with
                      | FStar_Pervasives_Native.None  -> true
                      | FStar_Pervasives_Native.Some mex ->
                          let mexports =
                            let uu____2714 = mex eikind  in
                            FStar_ST.op_Bang uu____2714  in
                          FStar_Util.set_mem idstr mexports
                       in
                    let mincludes =
                      let uu____2906 =
                        FStar_Util.smap_try_find env.includes mname  in
                      match uu____2906 with
                      | FStar_Pervasives_Native.None  -> []
                      | FStar_Pervasives_Native.Some minc ->
                          FStar_ST.op_Bang minc
                       in
                    let look_into =
                      if not_shadowed
                      then
                        let uu____3034 = qual modul id1  in
                        find_in_module uu____3034
                      else Cont_ignore  in
                    (match look_into with
                     | Cont_ignore  -> aux (FStar_List.append mincludes q)
                     | uu____3038 -> look_into)
                 in
              aux [ns]
  
let (is_exported_id_field : exported_id_kind -> Prims.bool) =
  fun uu___83_3043  ->
    match uu___83_3043 with
    | Exported_id_field  -> true
    | uu____3044 -> false
  
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
                  let check_local_binding_id uu___84_3146 =
                    match uu___84_3146 with
                    | (id',uu____3148,uu____3149) ->
                        id'.FStar_Ident.idText = id1.FStar_Ident.idText
                     in
                  let check_rec_binding_id uu___85_3153 =
                    match uu___85_3153 with
                    | (id',uu____3155,uu____3156) ->
                        id'.FStar_Ident.idText = id1.FStar_Ident.idText
                     in
                  let curmod_ns =
                    let uu____3160 = current_module env  in
                    FStar_Ident.ids_of_lid uu____3160  in
                  let proc uu___86_3166 =
                    match uu___86_3166 with
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
                        let uu____3174 = FStar_Ident.lid_of_ids curmod_ns  in
                        find_in_module_with_includes Exported_id_field
                          (fun lid  ->
                             let id2 = lid.FStar_Ident.ident  in
                             find_in_record lid.FStar_Ident.ns id2 r k_record)
                          Cont_ignore env uu____3174 id1
                    | uu____3179 -> Cont_ignore  in
                  let rec aux uu___87_3187 =
                    match uu___87_3187 with
                    | a::q ->
                        let uu____3196 = proc a  in
                        option_of_cont (fun uu____3200  -> aux q) uu____3196
                    | [] ->
                        let uu____3201 = lookup_default_id Cont_fail id1  in
                        option_of_cont
                          (fun uu____3205  -> FStar_Pervasives_Native.None)
                          uu____3201
                     in
                  aux env.scope_mods
  
let found_local_binding :
  'Auu____3210 'Auu____3211 .
    FStar_Range.range ->
      ('Auu____3211,FStar_Syntax_Syntax.bv,'Auu____3210)
        FStar_Pervasives_Native.tuple3 ->
        (FStar_Syntax_Syntax.term,'Auu____3210)
          FStar_Pervasives_Native.tuple2
  =
  fun r  ->
    fun uu____3229  ->
      match uu____3229 with
      | (id',x,mut) -> let uu____3239 = bv_to_name x r  in (uu____3239, mut)
  
let find_in_module :
  'Auu____3245 .
    env ->
      FStar_Ident.lident ->
        (FStar_Ident.lident ->
           (FStar_Syntax_Syntax.sigelt,Prims.bool)
             FStar_Pervasives_Native.tuple2 -> 'Auu____3245)
          -> 'Auu____3245 -> 'Auu____3245
  =
  fun env  ->
    fun lid  ->
      fun k_global_def  ->
        fun k_not_found  ->
          let uu____3280 =
            FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str  in
          match uu____3280 with
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
      let uu____3316 = unmangleOpName id1  in
      match uu____3316 with
      | FStar_Pervasives_Native.Some f -> FStar_Pervasives_Native.Some f
      | uu____3342 ->
          try_lookup_id'' env id1 Exported_id_term_type
            (fun r  ->
               let uu____3356 = found_local_binding id1.FStar_Ident.idRange r
                  in
               Cont_ok uu____3356) (fun uu____3366  -> Cont_fail)
            (fun uu____3372  -> Cont_ignore)
            (fun i  ->
               find_in_module env i
                 (fun uu____3387  -> fun uu____3388  -> Cont_fail)
                 Cont_ignore)
            (fun uu____3403  -> fun uu____3404  -> Cont_fail)
  
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
            | FStar_Pervasives_Native.Some uu____3474 ->
                let lid = qualify env id1  in
                let uu____3476 =
                  FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str
                   in
                (match uu____3476 with
                 | FStar_Pervasives_Native.Some r ->
                     let uu____3500 = k_global_def lid r  in
                     FStar_Pervasives_Native.Some uu____3500
                 | FStar_Pervasives_Native.None  ->
                     FStar_Pervasives_Native.None)
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             in
          match find_in_monad with
          | FStar_Pervasives_Native.Some v1 -> v1
          | FStar_Pervasives_Native.None  ->
              let lid =
                let uu____3523 = current_module env  in qual uu____3523 id1
                 in
              find_in_module env lid k_global_def k_not_found
  
let (module_is_defined : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      (match env.curmodule with
       | FStar_Pervasives_Native.None  -> false
       | FStar_Pervasives_Native.Some m ->
           let uu____3533 = current_module env  in
           FStar_Ident.lid_equals lid uu____3533)
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
        let rec aux uu___88_3565 =
          match uu___88_3565 with
          | [] ->
              let uu____3570 = module_is_defined env lid  in
              if uu____3570
              then FStar_Pervasives_Native.Some lid
              else FStar_Pervasives_Native.None
          | (Open_module_or_namespace (ns,Open_namespace ))::q when honor_ns
              ->
              let new_lid =
                let uu____3579 =
                  let uu____3582 = FStar_Ident.path_of_lid ns  in
                  let uu____3585 = FStar_Ident.path_of_lid lid  in
                  FStar_List.append uu____3582 uu____3585  in
                FStar_Ident.lid_of_path uu____3579
                  (FStar_Ident.range_of_lid lid)
                 in
              let uu____3588 = module_is_defined env new_lid  in
              if uu____3588
              then FStar_Pervasives_Native.Some new_lid
              else aux q
          | (Module_abbrev (name,modul))::uu____3594 when
              (nslen = (Prims.parse_int "0")) &&
                (name.FStar_Ident.idText =
                   (lid.FStar_Ident.ident).FStar_Ident.idText)
              -> FStar_Pervasives_Native.Some modul
          | uu____3601::q -> aux q  in
        aux env.scope_mods
  
let (fail_if_curmodule :
  env -> FStar_Ident.lident -> FStar_Ident.lident -> Prims.unit) =
  fun env  ->
    fun ns_original  ->
      fun ns_resolved  ->
        let uu____3614 =
          let uu____3615 = current_module env  in
          FStar_Ident.lid_equals ns_resolved uu____3615  in
        if uu____3614
        then
          (if FStar_Ident.lid_equals ns_resolved FStar_Parser_Const.prims_lid
           then ()
           else
             (let uu____3617 =
                let uu____3622 =
                  FStar_Util.format1
                    "Reference %s to current module is forbidden (see GitHub issue #451)"
                    ns_original.FStar_Ident.str
                   in
                (FStar_Errors.Fatal_ForbiddenReferenceToCurrentModule,
                  uu____3622)
                 in
              FStar_Errors.raise_error uu____3617
                (FStar_Ident.range_of_lid ns_original)))
        else ()
  
let (fail_if_qualified_by_curmodule :
  env -> FStar_Ident.lident -> Prims.unit) =
  fun env  ->
    fun lid  ->
      match lid.FStar_Ident.ns with
      | [] -> ()
      | uu____3630 ->
          let modul_orig = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          let uu____3634 = resolve_module_name env modul_orig true  in
          (match uu____3634 with
           | FStar_Pervasives_Native.Some modul_res ->
               fail_if_curmodule env modul_orig modul_res
           | uu____3638 -> ())
  
let (namespace_is_open : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      FStar_List.existsb
        (fun uu___89_3649  ->
           match uu___89_3649 with
           | Open_module_or_namespace (ns,Open_namespace ) ->
               FStar_Ident.lid_equals lid ns
           | uu____3651 -> false) env.scope_mods
  
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
                 let uu____3740 = aux rev_ns_prefix ns_last_id  in
                 FStar_All.pipe_right uu____3740
                   (FStar_Util.map_option
                      (fun uu____3790  ->
                         match uu____3790 with
                         | (stripped_ids,rev_kept_ids) ->
                             (stripped_ids, (id1 :: rev_kept_ids)))))
           in
        let uu____3821 =
          is_full_path &&
            (let uu____3823 = FStar_Ident.lid_of_ids ids  in
             module_is_defined env uu____3823)
           in
        if uu____3821
        then (ids, [])
        else
          (match FStar_List.rev ids with
           | [] -> ([], [])
           | ns_last_id::ns_rev_prefix ->
               let uu____3853 = aux ns_rev_prefix ns_last_id  in
               (match uu____3853 with
                | FStar_Pervasives_Native.None  -> ([], ids)
                | FStar_Pervasives_Native.Some (stripped_ids,rev_kept_ids) ->
                    (stripped_ids, (FStar_List.rev rev_kept_ids))))
  
let (shorten_lid : env -> FStar_Ident.lid -> FStar_Ident.lid) =
  fun env  ->
    fun lid  ->
      let uu____3912 = shorten_module_path env lid.FStar_Ident.ns true  in
      match uu____3912 with
      | (uu____3921,short) ->
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
                  | uu____4029::uu____4030 ->
                      let uu____4033 =
                        let uu____4036 =
                          let uu____4037 =
                            FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
                          FStar_Ident.set_lid_range uu____4037
                            (FStar_Ident.range_of_lid lid)
                           in
                        resolve_module_name env uu____4036 true  in
                      (match uu____4033 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some modul ->
                           let uu____4041 =
                             find_in_module_with_includes eikind f_module
                               Cont_fail env modul lid.FStar_Ident.ident
                              in
                           option_of_cont
                             (fun uu____4045  -> FStar_Pervasives_Native.None)
                             uu____4041)
                  | [] ->
                      try_lookup_id'' env lid.FStar_Ident.ident eikind
                        k_local_binding k_rec_binding k_record f_module
                        l_default
  
let cont_of_option :
  'a . 'a cont_t -> 'a FStar_Pervasives_Native.option -> 'a cont_t =
  fun k_none  ->
    fun uu___90_4063  ->
      match uu___90_4063 with
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
              let uu____4162 = k_global_def lid1 def  in
              cont_of_option k uu____4162  in
            let f_module lid' =
              let k = Cont_ignore  in
              find_in_module env lid' (k_global_def' k) k  in
            let l_default k i = lookup_default_id env i (k_global_def' k) k
               in
            resolve_in_open_namespaces'' env lid Exported_id_term_type
              (fun l  ->
                 let uu____4192 = k_local_binding l  in
                 cont_of_option Cont_fail uu____4192)
              (fun r  ->
                 let uu____4198 = k_rec_binding r  in
                 cont_of_option Cont_fail uu____4198)
              (fun uu____4202  -> Cont_ignore) f_module l_default
  
let (fv_qual_of_se :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option)
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____4210,uu____4211,uu____4212,l,uu____4214,uu____4215) ->
        let qopt =
          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
            (fun uu___91_4226  ->
               match uu___91_4226 with
               | FStar_Syntax_Syntax.RecordConstructor (uu____4229,fs) ->
                   FStar_Pervasives_Native.Some
                     (FStar_Syntax_Syntax.Record_ctor (l, fs))
               | uu____4241 -> FStar_Pervasives_Native.None)
           in
        (match qopt with
         | FStar_Pervasives_Native.None  ->
             FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor
         | x -> x)
    | FStar_Syntax_Syntax.Sig_declare_typ (uu____4247,uu____4248,uu____4249)
        -> FStar_Pervasives_Native.None
    | uu____4250 -> FStar_Pervasives_Native.None
  
let (lb_fv :
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Ident.lident -> FStar_Syntax_Syntax.fv)
  =
  fun lbs  ->
    fun lid  ->
      let uu____4261 =
        FStar_Util.find_map lbs
          (fun lb  ->
             let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
             let uu____4269 = FStar_Syntax_Syntax.fv_eq_lid fv lid  in
             if uu____4269
             then FStar_Pervasives_Native.Some fv
             else FStar_Pervasives_Native.None)
         in
      FStar_All.pipe_right uu____4261 FStar_Util.must
  
let (ns_of_lid_equals :
  FStar_Ident.lident -> FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    fun ns  ->
      ((FStar_List.length lid.FStar_Ident.ns) =
         (FStar_List.length (FStar_Ident.ids_of_lid ns)))
        &&
        (let uu____4282 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
         FStar_Ident.lid_equals uu____4282 ns)
  
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
          let k_global_def source_lid uu___96_4312 =
            match uu___96_4312 with
            | (uu____4319,true ) when exclude_interf ->
                FStar_Pervasives_Native.None
            | (se,uu____4321) ->
                (match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_inductive_typ uu____4324 ->
                     let uu____4341 =
                       let uu____4342 =
                         let uu____4351 =
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.Delta_constant
                             FStar_Pervasives_Native.None
                            in
                         (uu____4351, false,
                           (se.FStar_Syntax_Syntax.sigattrs))
                          in
                       Term_name uu____4342  in
                     FStar_Pervasives_Native.Some uu____4341
                 | FStar_Syntax_Syntax.Sig_datacon uu____4354 ->
                     let uu____4369 =
                       let uu____4370 =
                         let uu____4379 =
                           let uu____4380 = fv_qual_of_se se  in
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.Delta_constant uu____4380
                            in
                         (uu____4379, false,
                           (se.FStar_Syntax_Syntax.sigattrs))
                          in
                       Term_name uu____4370  in
                     FStar_Pervasives_Native.Some uu____4369
                 | FStar_Syntax_Syntax.Sig_let ((uu____4385,lbs),uu____4387)
                     ->
                     let fv = lb_fv lbs source_lid  in
                     let uu____4403 =
                       let uu____4404 =
                         let uu____4413 =
                           FStar_Syntax_Syntax.fvar source_lid
                             fv.FStar_Syntax_Syntax.fv_delta
                             fv.FStar_Syntax_Syntax.fv_qual
                            in
                         (uu____4413, false,
                           (se.FStar_Syntax_Syntax.sigattrs))
                          in
                       Term_name uu____4404  in
                     FStar_Pervasives_Native.Some uu____4403
                 | FStar_Syntax_Syntax.Sig_declare_typ
                     (lid1,uu____4417,uu____4418) ->
                     let quals = se.FStar_Syntax_Syntax.sigquals  in
                     let uu____4422 =
                       any_val ||
                         (FStar_All.pipe_right quals
                            (FStar_Util.for_some
                               (fun uu___92_4426  ->
                                  match uu___92_4426 with
                                  | FStar_Syntax_Syntax.Assumption  -> true
                                  | uu____4427 -> false)))
                        in
                     if uu____4422
                     then
                       let lid2 =
                         FStar_Ident.set_lid_range lid1
                           (FStar_Ident.range_of_lid source_lid)
                          in
                       let dd =
                         let uu____4432 =
                           (FStar_Syntax_Util.is_primop_lid lid2) ||
                             (FStar_All.pipe_right quals
                                (FStar_Util.for_some
                                   (fun uu___93_4437  ->
                                      match uu___93_4437 with
                                      | FStar_Syntax_Syntax.Projector
                                          uu____4438 -> true
                                      | FStar_Syntax_Syntax.Discriminator
                                          uu____4443 -> true
                                      | uu____4444 -> false)))
                            in
                         if uu____4432
                         then FStar_Syntax_Syntax.Delta_equational
                         else FStar_Syntax_Syntax.Delta_constant  in
                       let dd1 =
                         let uu____4447 =
                           FStar_All.pipe_right quals
                             (FStar_Util.for_some
                                (fun uu___94_4451  ->
                                   match uu___94_4451 with
                                   | FStar_Syntax_Syntax.Abstract  -> true
                                   | uu____4452 -> false))
                            in
                         if uu____4447
                         then FStar_Syntax_Syntax.Delta_abstract dd
                         else dd  in
                       let uu____4454 =
                         FStar_Util.find_map quals
                           (fun uu___95_4459  ->
                              match uu___95_4459 with
                              | FStar_Syntax_Syntax.Reflectable refl_monad ->
                                  FStar_Pervasives_Native.Some refl_monad
                              | uu____4463 -> FStar_Pervasives_Native.None)
                          in
                       (match uu____4454 with
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
                        | uu____4474 ->
                            let uu____4477 =
                              let uu____4478 =
                                let uu____4487 =
                                  let uu____4488 = fv_qual_of_se se  in
                                  FStar_Syntax_Syntax.fvar lid2 dd1
                                    uu____4488
                                   in
                                (uu____4487, false,
                                  (se.FStar_Syntax_Syntax.sigattrs))
                                 in
                              Term_name uu____4478  in
                            FStar_Pervasives_Native.Some uu____4477)
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
                 | FStar_Syntax_Syntax.Sig_effect_abbrev uu____4496 ->
                     FStar_Pervasives_Native.Some (Eff_name (se, source_lid))
                 | uu____4509 -> FStar_Pervasives_Native.None)
             in
          let k_local_binding r =
            let uu____4528 =
              found_local_binding (FStar_Ident.range_of_lid lid) r  in
            match uu____4528 with
            | (t,mut) ->
                FStar_Pervasives_Native.Some (Term_name (t, mut, []))
             in
          let k_rec_binding uu____4550 =
            match uu____4550 with
            | (id1,l,dd) ->
                let uu____4562 =
                  let uu____4563 =
                    let uu____4572 =
                      FStar_Syntax_Syntax.fvar
                        (FStar_Ident.set_lid_range l
                           (FStar_Ident.range_of_lid lid)) dd
                        FStar_Pervasives_Native.None
                       in
                    (uu____4572, false, [])  in
                  Term_name uu____4563  in
                FStar_Pervasives_Native.Some uu____4562
             in
          let found_unmangled =
            match lid.FStar_Ident.ns with
            | [] ->
                let uu____4580 = unmangleOpName lid.FStar_Ident.ident  in
                (match uu____4580 with
                 | FStar_Pervasives_Native.Some (t,mut) ->
                     FStar_Pervasives_Native.Some (Term_name (t, mut, []))
                 | uu____4597 -> FStar_Pervasives_Native.None)
            | uu____4604 -> FStar_Pervasives_Native.None  in
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
        let uu____4633 = try_lookup_name true exclude_interf env lid  in
        match uu____4633 with
        | FStar_Pervasives_Native.Some (Eff_name (o,l)) ->
            FStar_Pervasives_Native.Some (o, l)
        | uu____4648 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____4663 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____4663 with
      | FStar_Pervasives_Native.Some (o,l1) ->
          FStar_Pervasives_Native.Some l1
      | uu____4678 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_name_and_attributes :
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident,FStar_Syntax_Syntax.cflags Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____4699 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____4699 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____4715;
             FStar_Syntax_Syntax.sigquals = uu____4716;
             FStar_Syntax_Syntax.sigmeta = uu____4717;
             FStar_Syntax_Syntax.sigattrs = uu____4718;_},l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____4737;
             FStar_Syntax_Syntax.sigquals = uu____4738;
             FStar_Syntax_Syntax.sigmeta = uu____4739;
             FStar_Syntax_Syntax.sigattrs = uu____4740;_},l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (uu____4758,uu____4759,uu____4760,uu____4761,cattributes);
             FStar_Syntax_Syntax.sigrng = uu____4763;
             FStar_Syntax_Syntax.sigquals = uu____4764;
             FStar_Syntax_Syntax.sigmeta = uu____4765;
             FStar_Syntax_Syntax.sigattrs = uu____4766;_},l1)
          -> FStar_Pervasives_Native.Some (l1, cattributes)
      | uu____4788 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_defn :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.eff_decl FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____4809 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____4809 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____4819;
             FStar_Syntax_Syntax.sigquals = uu____4820;
             FStar_Syntax_Syntax.sigmeta = uu____4821;
             FStar_Syntax_Syntax.sigattrs = uu____4822;_},uu____4823)
          -> FStar_Pervasives_Native.Some ne
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____4833;
             FStar_Syntax_Syntax.sigquals = uu____4834;
             FStar_Syntax_Syntax.sigmeta = uu____4835;
             FStar_Syntax_Syntax.sigattrs = uu____4836;_},uu____4837)
          -> FStar_Pervasives_Native.Some ne
      | uu____4846 -> FStar_Pervasives_Native.None
  
let (is_effect_name : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____4859 = try_lookup_effect_name env lid  in
      match uu____4859 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____4862 -> true
  
let (try_lookup_root_effect_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____4871 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____4871 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (l',uu____4881,uu____4882,uu____4883,uu____4884);
             FStar_Syntax_Syntax.sigrng = uu____4885;
             FStar_Syntax_Syntax.sigquals = uu____4886;
             FStar_Syntax_Syntax.sigmeta = uu____4887;
             FStar_Syntax_Syntax.sigattrs = uu____4888;_},uu____4889)
          ->
          let rec aux new_name =
            let uu____4908 =
              FStar_Util.smap_try_find (sigmap env) new_name.FStar_Ident.str
               in
            match uu____4908 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (s,uu____4926) ->
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
                     (uu____4935,uu____4936,uu____4937,cmp,uu____4939) ->
                     let l'' = FStar_Syntax_Util.comp_effect_name cmp  in
                     aux l''
                 | uu____4945 -> FStar_Pervasives_Native.None)
             in
          aux l'
      | FStar_Pervasives_Native.Some (uu____4946,l') ->
          FStar_Pervasives_Native.Some l'
      | uu____4952 -> FStar_Pervasives_Native.None
  
let (lookup_letbinding_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___97_4981 =
        match uu___97_4981 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____4990,uu____4991,uu____4992);
             FStar_Syntax_Syntax.sigrng = uu____4993;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____4995;
             FStar_Syntax_Syntax.sigattrs = uu____4996;_},uu____4997)
            -> FStar_Pervasives_Native.Some quals
        | uu____5004 -> FStar_Pervasives_Native.None  in
      let uu____5011 =
        resolve_in_open_namespaces' env lid
          (fun uu____5019  -> FStar_Pervasives_Native.None)
          (fun uu____5023  -> FStar_Pervasives_Native.None) k_global_def
         in
      match uu____5011 with
      | FStar_Pervasives_Native.Some quals -> quals
      | uu____5033 -> []
  
let (try_lookup_module :
  env ->
    Prims.string Prims.list ->
      FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun path  ->
      let uu____5050 =
        FStar_List.tryFind
          (fun uu____5065  ->
             match uu____5065 with
             | (mlid,modul) ->
                 let uu____5072 = FStar_Ident.path_of_lid mlid  in
                 uu____5072 = path) env.modules
         in
      match uu____5050 with
      | FStar_Pervasives_Native.Some (uu____5079,modul) ->
          FStar_Pervasives_Native.Some modul
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (try_lookup_let :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___98_5109 =
        match uu___98_5109 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               ((uu____5116,lbs),uu____5118);
             FStar_Syntax_Syntax.sigrng = uu____5119;
             FStar_Syntax_Syntax.sigquals = uu____5120;
             FStar_Syntax_Syntax.sigmeta = uu____5121;
             FStar_Syntax_Syntax.sigattrs = uu____5122;_},uu____5123)
            ->
            let fv = lb_fv lbs lid1  in
            let uu____5143 =
              FStar_Syntax_Syntax.fvar lid1 fv.FStar_Syntax_Syntax.fv_delta
                fv.FStar_Syntax_Syntax.fv_qual
               in
            FStar_Pervasives_Native.Some uu____5143
        | uu____5144 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____5150  -> FStar_Pervasives_Native.None)
        (fun uu____5152  -> FStar_Pervasives_Native.None) k_global_def
  
let (try_lookup_definition :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___99_5175 =
        match uu___99_5175 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               (lbs,uu____5185);
             FStar_Syntax_Syntax.sigrng = uu____5186;
             FStar_Syntax_Syntax.sigquals = uu____5187;
             FStar_Syntax_Syntax.sigmeta = uu____5188;
             FStar_Syntax_Syntax.sigattrs = uu____5189;_},uu____5190)
            ->
            FStar_Util.find_map (FStar_Pervasives_Native.snd lbs)
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inr fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv lid1 ->
                     FStar_Pervasives_Native.Some
                       (lb.FStar_Syntax_Syntax.lbdef)
                 | uu____5213 -> FStar_Pervasives_Native.None)
        | uu____5220 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____5230  -> FStar_Pervasives_Native.None)
        (fun uu____5234  -> FStar_Pervasives_Native.None) k_global_def
  
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
          let uu____5281 = try_lookup_name any_val exclude_interface env lid
             in
          match uu____5281 with
          | FStar_Pervasives_Native.Some (Term_name (e,mut,attrs)) ->
              FStar_Pervasives_Native.Some (e, mut, attrs)
          | uu____5311 -> FStar_Pervasives_Native.None
  
let (drop_attributes :
  (FStar_Syntax_Syntax.term,Prims.bool,FStar_Syntax_Syntax.attribute
                                         Prims.list)
    FStar_Pervasives_Native.tuple3 FStar_Pervasives_Native.option ->
    (FStar_Syntax_Syntax.term,Prims.bool) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option)
  =
  fun x  ->
    match x with
    | FStar_Pervasives_Native.Some (t,mut,uu____5365) ->
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
      let uu____5432 = try_lookup_lid_with_attributes env l  in
      FStar_All.pipe_right uu____5432 drop_attributes
  
let (resolve_to_fully_qualified_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____5467 = try_lookup_lid env l  in
      match uu____5467 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (e,uu____5481) ->
          let uu____5486 =
            let uu____5487 = FStar_Syntax_Subst.compress e  in
            uu____5487.FStar_Syntax_Syntax.n  in
          (match uu____5486 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               FStar_Pervasives_Native.Some
                 ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
           | uu____5493 -> FStar_Pervasives_Native.None)
  
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
        let uu___120_5521 = env  in
        {
          curmodule = (uu___120_5521.curmodule);
          curmonad = (uu___120_5521.curmonad);
          modules = (uu___120_5521.modules);
          scope_mods = [];
          exported_ids = empty_exported_id_smap;
          trans_exported_ids = (uu___120_5521.trans_exported_ids);
          includes = empty_include_smap;
          sigaccum = (uu___120_5521.sigaccum);
          sigmap = (uu___120_5521.sigmap);
          iface = (uu___120_5521.iface);
          admitted_iface = (uu___120_5521.admitted_iface);
          expect_typ = (uu___120_5521.expect_typ);
          docs = (uu___120_5521.docs);
          remaining_iface_decls = (uu___120_5521.remaining_iface_decls);
          syntax_only = (uu___120_5521.syntax_only);
          ds_hooks = (uu___120_5521.ds_hooks)
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
      let uu____5540 = try_lookup_lid_with_attributes_no_resolve env l  in
      FStar_All.pipe_right uu____5540 drop_attributes
  
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
      let k_global_def lid1 uu___101_5595 =
        match uu___101_5595 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____5602,uu____5603,uu____5604);
             FStar_Syntax_Syntax.sigrng = uu____5605;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____5607;
             FStar_Syntax_Syntax.sigattrs = uu____5608;_},uu____5609)
            ->
            let uu____5614 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___100_5618  ->
                      match uu___100_5618 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | uu____5619 -> false))
               in
            if uu____5614
            then
              let uu____5622 =
                FStar_Syntax_Syntax.lid_as_fv lid1
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Pervasives_Native.Some uu____5622
            else FStar_Pervasives_Native.None
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
               uu____5624;
             FStar_Syntax_Syntax.sigrng = uu____5625;
             FStar_Syntax_Syntax.sigquals = uu____5626;
             FStar_Syntax_Syntax.sigmeta = uu____5627;
             FStar_Syntax_Syntax.sigattrs = uu____5628;_},uu____5629)
            ->
            let uu____5648 =
              FStar_Syntax_Syntax.lid_as_fv lid1
                FStar_Syntax_Syntax.Delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
               in
            FStar_Pervasives_Native.Some uu____5648
        | uu____5649 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____5655  -> FStar_Pervasives_Native.None)
        (fun uu____5657  -> FStar_Pervasives_Native.None) k_global_def
  
let (find_all_datacons :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___102_5682 =
        match uu___102_5682 with
        | ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_inductive_typ
               (uu____5691,uu____5692,uu____5693,uu____5694,datas,uu____5696);
             FStar_Syntax_Syntax.sigrng = uu____5697;
             FStar_Syntax_Syntax.sigquals = uu____5698;
             FStar_Syntax_Syntax.sigmeta = uu____5699;
             FStar_Syntax_Syntax.sigattrs = uu____5700;_},uu____5701)
            -> FStar_Pervasives_Native.Some datas
        | uu____5716 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____5726  -> FStar_Pervasives_Native.None)
        (fun uu____5730  -> FStar_Pervasives_Native.None) k_global_def
  
let (record_cache_aux_with_filter :
  ((Prims.unit -> Prims.unit,Prims.unit -> Prims.unit,Prims.unit ->
                                                        record_or_dc
                                                          Prims.list,
     record_or_dc -> Prims.unit) FStar_Pervasives_Native.tuple4,Prims.unit ->
                                                                  Prims.unit)
    FStar_Pervasives_Native.tuple2)
  =
  let record_cache = FStar_Util.mk_ref [[]]  in
  let push1 uu____5775 =
    let uu____5776 =
      let uu____5781 =
        let uu____5784 = FStar_ST.op_Bang record_cache  in
        FStar_List.hd uu____5784  in
      let uu____5892 = FStar_ST.op_Bang record_cache  in uu____5781 ::
        uu____5892
       in
    FStar_ST.op_Colon_Equals record_cache uu____5776  in
  let pop1 uu____6104 =
    let uu____6105 =
      let uu____6110 = FStar_ST.op_Bang record_cache  in
      FStar_List.tl uu____6110  in
    FStar_ST.op_Colon_Equals record_cache uu____6105  in
  let peek1 uu____6324 =
    let uu____6325 = FStar_ST.op_Bang record_cache  in
    FStar_List.hd uu____6325  in
  let insert r =
    let uu____6437 =
      let uu____6442 = let uu____6445 = peek1 ()  in r :: uu____6445  in
      let uu____6448 =
        let uu____6453 = FStar_ST.op_Bang record_cache  in
        FStar_List.tl uu____6453  in
      uu____6442 :: uu____6448  in
    FStar_ST.op_Colon_Equals record_cache uu____6437  in
  let filter1 uu____6667 =
    let rc = peek1 ()  in
    let filtered =
      FStar_List.filter
        (fun r  -> Prims.op_Negation r.is_private_or_abstract) rc
       in
    let uu____6676 =
      let uu____6681 =
        let uu____6686 = FStar_ST.op_Bang record_cache  in
        FStar_List.tl uu____6686  in
      filtered :: uu____6681  in
    FStar_ST.op_Colon_Equals record_cache uu____6676  in
  let aux = (push1, pop1, peek1, insert)  in (aux, filter1) 
let (record_cache_aux :
  (Prims.unit -> Prims.unit,Prims.unit -> Prims.unit,Prims.unit ->
                                                       record_or_dc
                                                         Prims.list,record_or_dc
                                                                    ->
                                                                    Prims.unit)
    FStar_Pervasives_Native.tuple4)
  =
  let uu____6964 = record_cache_aux_with_filter  in
  match uu____6964 with | (aux,uu____7008) -> aux 
let (filter_record_cache : Prims.unit -> Prims.unit) =
  let uu____7051 = record_cache_aux_with_filter  in
  match uu____7051 with | (uu____7078,filter1) -> filter1 
let (push_record_cache : Prims.unit -> Prims.unit) =
  let uu____7122 = record_cache_aux  in
  match uu____7122 with | (push1,uu____7144,uu____7145,uu____7146) -> push1 
let (pop_record_cache : Prims.unit -> Prims.unit) =
  let uu____7169 = record_cache_aux  in
  match uu____7169 with | (uu____7190,pop1,uu____7192,uu____7193) -> pop1 
let (peek_record_cache : Prims.unit -> record_or_dc Prims.list) =
  let uu____7218 = record_cache_aux  in
  match uu____7218 with | (uu____7241,uu____7242,peek1,uu____7244) -> peek1 
let (insert_record_cache : record_or_dc -> Prims.unit) =
  let uu____7267 = record_cache_aux  in
  match uu____7267 with | (uu____7288,uu____7289,uu____7290,insert) -> insert 
let (extract_record :
  env ->
    scope_mod Prims.list FStar_ST.ref ->
      FStar_Syntax_Syntax.sigelt -> Prims.unit)
  =
  fun e  ->
    fun new_globs  ->
      fun se  ->
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_bundle (sigs,uu____7404) ->
            let is_record =
              FStar_Util.for_some
                (fun uu___103_7420  ->
                   match uu___103_7420 with
                   | FStar_Syntax_Syntax.RecordType uu____7421 -> true
                   | FStar_Syntax_Syntax.RecordConstructor uu____7430 -> true
                   | uu____7439 -> false)
               in
            let find_dc dc =
              FStar_All.pipe_right sigs
                (FStar_Util.find_opt
                   (fun uu___104_7461  ->
                      match uu___104_7461 with
                      | {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_datacon
                            (lid,uu____7463,uu____7464,uu____7465,uu____7466,uu____7467);
                          FStar_Syntax_Syntax.sigrng = uu____7468;
                          FStar_Syntax_Syntax.sigquals = uu____7469;
                          FStar_Syntax_Syntax.sigmeta = uu____7470;
                          FStar_Syntax_Syntax.sigattrs = uu____7471;_} ->
                          FStar_Ident.lid_equals dc lid
                      | uu____7480 -> false))
               in
            FStar_All.pipe_right sigs
              (FStar_List.iter
                 (fun uu___105_7515  ->
                    match uu___105_7515 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ
                          (typename,univs1,parms,uu____7519,uu____7520,dc::[]);
                        FStar_Syntax_Syntax.sigrng = uu____7522;
                        FStar_Syntax_Syntax.sigquals = typename_quals;
                        FStar_Syntax_Syntax.sigmeta = uu____7524;
                        FStar_Syntax_Syntax.sigattrs = uu____7525;_} ->
                        let uu____7536 =
                          let uu____7537 = find_dc dc  in
                          FStar_All.pipe_left FStar_Util.must uu____7537  in
                        (match uu____7536 with
                         | {
                             FStar_Syntax_Syntax.sigel =
                               FStar_Syntax_Syntax.Sig_datacon
                               (constrname,uu____7543,t,uu____7545,uu____7546,uu____7547);
                             FStar_Syntax_Syntax.sigrng = uu____7548;
                             FStar_Syntax_Syntax.sigquals = uu____7549;
                             FStar_Syntax_Syntax.sigmeta = uu____7550;
                             FStar_Syntax_Syntax.sigattrs = uu____7551;_} ->
                             let uu____7560 =
                               FStar_Syntax_Util.arrow_formals t  in
                             (match uu____7560 with
                              | (formals,uu____7574) ->
                                  let is_rec = is_record typename_quals  in
                                  let formals' =
                                    FStar_All.pipe_right formals
                                      (FStar_List.collect
                                         (fun uu____7623  ->
                                            match uu____7623 with
                                            | (x,q) ->
                                                let uu____7636 =
                                                  (FStar_Syntax_Syntax.is_null_bv
                                                     x)
                                                    ||
                                                    (is_rec &&
                                                       (FStar_Syntax_Syntax.is_implicit
                                                          q))
                                                   in
                                                if uu____7636
                                                then []
                                                else [(x, q)]))
                                     in
                                  let fields' =
                                    FStar_All.pipe_right formals'
                                      (FStar_List.map
                                         (fun uu____7693  ->
                                            match uu____7693 with
                                            | (x,q) ->
                                                let uu____7706 =
                                                  if is_rec
                                                  then
                                                    FStar_Syntax_Util.unmangle_field_name
                                                      x.FStar_Syntax_Syntax.ppname
                                                  else
                                                    x.FStar_Syntax_Syntax.ppname
                                                   in
                                                (uu____7706,
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
                                  ((let uu____7721 =
                                      let uu____7724 =
                                        FStar_ST.op_Bang new_globs  in
                                      (Record_or_dc record) :: uu____7724  in
                                    FStar_ST.op_Colon_Equals new_globs
                                      uu____7721);
                                   (match () with
                                    | () ->
                                        ((let add_field uu____7931 =
                                            match uu____7931 with
                                            | (id1,uu____7939) ->
                                                let modul =
                                                  let uu____7945 =
                                                    FStar_Ident.lid_of_ids
                                                      constrname.FStar_Ident.ns
                                                     in
                                                  uu____7945.FStar_Ident.str
                                                   in
                                                let uu____7946 =
                                                  get_exported_id_set e modul
                                                   in
                                                (match uu____7946 with
                                                 | FStar_Pervasives_Native.Some
                                                     my_ex ->
                                                     let my_exported_ids =
                                                       my_ex
                                                         Exported_id_field
                                                        in
                                                     ((let uu____8003 =
                                                         let uu____8004 =
                                                           FStar_ST.op_Bang
                                                             my_exported_ids
                                                            in
                                                         FStar_Util.set_add
                                                           id1.FStar_Ident.idText
                                                           uu____8004
                                                          in
                                                       FStar_ST.op_Colon_Equals
                                                         my_exported_ids
                                                         uu____8003);
                                                      (match () with
                                                       | () ->
                                                           let projname =
                                                             let uu____8194 =
                                                               let uu____8195
                                                                 =
                                                                 FStar_Syntax_Util.mk_field_projector_name_from_ident
                                                                   constrname
                                                                   id1
                                                                  in
                                                               uu____8195.FStar_Ident.ident
                                                                in
                                                             uu____8194.FStar_Ident.idText
                                                              in
                                                           let uu____8197 =
                                                             let uu____8198 =
                                                               FStar_ST.op_Bang
                                                                 my_exported_ids
                                                                in
                                                             FStar_Util.set_add
                                                               projname
                                                               uu____8198
                                                              in
                                                           FStar_ST.op_Colon_Equals
                                                             my_exported_ids
                                                             uu____8197))
                                                 | FStar_Pervasives_Native.None
                                                      -> ())
                                             in
                                          FStar_List.iter add_field fields');
                                         (match () with
                                          | () -> insert_record_cache record)))))
                         | uu____8397 -> ())
                    | uu____8398 -> ()))
        | uu____8399 -> ()
  
let (try_lookup_record_or_dc_by_field_name :
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option) =
  fun env  ->
    fun fieldname  ->
      let find_in_cache fieldname1 =
        let uu____8414 =
          ((fieldname1.FStar_Ident.ns), (fieldname1.FStar_Ident.ident))  in
        match uu____8414 with
        | (ns,id1) ->
            let uu____8431 = peek_record_cache ()  in
            FStar_Util.find_map uu____8431
              (fun record  ->
                 let uu____8437 =
                   find_in_record ns id1 record (fun r  -> Cont_ok r)  in
                 option_of_cont
                   (fun uu____8443  -> FStar_Pervasives_Native.None)
                   uu____8437)
         in
      resolve_in_open_namespaces'' env fieldname Exported_id_field
        (fun uu____8445  -> Cont_ignore) (fun uu____8447  -> Cont_ignore)
        (fun r  -> Cont_ok r)
        (fun fn  ->
           let uu____8453 = find_in_cache fn  in
           cont_of_option Cont_ignore uu____8453)
        (fun k  -> fun uu____8459  -> k)
  
let (try_lookup_record_by_field_name :
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option) =
  fun env  ->
    fun fieldname  ->
      let uu____8470 = try_lookup_record_or_dc_by_field_name env fieldname
         in
      match uu____8470 with
      | FStar_Pervasives_Native.Some r when r.is_record ->
          FStar_Pervasives_Native.Some r
      | uu____8476 -> FStar_Pervasives_Native.None
  
let (belongs_to_record :
  env -> FStar_Ident.lident -> record_or_dc -> Prims.bool) =
  fun env  ->
    fun lid  ->
      fun record  ->
        let uu____8488 = try_lookup_record_by_field_name env lid  in
        match uu____8488 with
        | FStar_Pervasives_Native.Some record' when
            let uu____8492 =
              let uu____8493 =
                FStar_Ident.path_of_ns (record.typename).FStar_Ident.ns  in
              FStar_Ident.text_of_path uu____8493  in
            let uu____8496 =
              let uu____8497 =
                FStar_Ident.path_of_ns (record'.typename).FStar_Ident.ns  in
              FStar_Ident.text_of_path uu____8497  in
            uu____8492 = uu____8496 ->
            let uu____8500 =
              find_in_record (record.typename).FStar_Ident.ns
                lid.FStar_Ident.ident record (fun uu____8504  -> Cont_ok ())
               in
            (match uu____8500 with
             | Cont_ok uu____8505 -> true
             | uu____8506 -> false)
        | uu____8509 -> false
  
let (try_lookup_dc_by_field_name :
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident,Prims.bool) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun fieldname  ->
      let uu____8524 = try_lookup_record_or_dc_by_field_name env fieldname
         in
      match uu____8524 with
      | FStar_Pervasives_Native.Some r ->
          let uu____8534 =
            let uu____8539 =
              let uu____8540 =
                FStar_Ident.lid_of_ids
                  (FStar_List.append (r.typename).FStar_Ident.ns
                     [r.constrname])
                 in
              FStar_Ident.set_lid_range uu____8540
                (FStar_Ident.range_of_lid fieldname)
               in
            (uu____8539, (r.is_record))  in
          FStar_Pervasives_Native.Some uu____8534
      | uu____8545 -> FStar_Pervasives_Native.None
  
let (string_set_ref_new :
  Prims.unit -> Prims.string FStar_Util.set FStar_ST.ref) =
  fun uu____8595  ->
    let uu____8596 = FStar_Util.new_set FStar_Util.compare  in
    FStar_Util.mk_ref uu____8596
  
let (exported_id_set_new :
  Prims.unit -> exported_id_kind -> Prims.string FStar_Util.set FStar_ST.ref)
  =
  fun uu____8646  ->
    let term_type_set = string_set_ref_new ()  in
    let field_set = string_set_ref_new ()  in
    fun uu___106_8657  ->
      match uu___106_8657 with
      | Exported_id_term_type  -> term_type_set
      | Exported_id_field  -> field_set
  
let (unique :
  Prims.bool -> Prims.bool -> env -> FStar_Ident.lident -> Prims.bool) =
  fun any_val  ->
    fun exclude_interface  ->
      fun env  ->
        fun lid  ->
          let filter_scope_mods uu___107_8751 =
            match uu___107_8751 with
            | Rec_binding uu____8752 -> true
            | uu____8753 -> false  in
          let this_env =
            let uu___121_8755 = env  in
            let uu____8756 =
              FStar_List.filter filter_scope_mods env.scope_mods  in
            {
              curmodule = (uu___121_8755.curmodule);
              curmonad = (uu___121_8755.curmonad);
              modules = (uu___121_8755.modules);
              scope_mods = uu____8756;
              exported_ids = empty_exported_id_smap;
              trans_exported_ids = (uu___121_8755.trans_exported_ids);
              includes = empty_include_smap;
              sigaccum = (uu___121_8755.sigaccum);
              sigmap = (uu___121_8755.sigmap);
              iface = (uu___121_8755.iface);
              admitted_iface = (uu___121_8755.admitted_iface);
              expect_typ = (uu___121_8755.expect_typ);
              docs = (uu___121_8755.docs);
              remaining_iface_decls = (uu___121_8755.remaining_iface_decls);
              syntax_only = (uu___121_8755.syntax_only);
              ds_hooks = (uu___121_8755.ds_hooks)
            }  in
          let uu____8759 =
            try_lookup_lid' any_val exclude_interface this_env lid  in
          match uu____8759 with
          | FStar_Pervasives_Native.None  -> true
          | FStar_Pervasives_Native.Some uu____8778 -> false
  
let (push_scope_mod : env -> scope_mod -> env) =
  fun env  ->
    fun scope_mod  ->
      let uu___122_8801 = env  in
      {
        curmodule = (uu___122_8801.curmodule);
        curmonad = (uu___122_8801.curmonad);
        modules = (uu___122_8801.modules);
        scope_mods = (scope_mod :: (env.scope_mods));
        exported_ids = (uu___122_8801.exported_ids);
        trans_exported_ids = (uu___122_8801.trans_exported_ids);
        includes = (uu___122_8801.includes);
        sigaccum = (uu___122_8801.sigaccum);
        sigmap = (uu___122_8801.sigmap);
        iface = (uu___122_8801.iface);
        admitted_iface = (uu___122_8801.admitted_iface);
        expect_typ = (uu___122_8801.expect_typ);
        docs = (uu___122_8801.docs);
        remaining_iface_decls = (uu___122_8801.remaining_iface_decls);
        syntax_only = (uu___122_8801.syntax_only);
        ds_hooks = (uu___122_8801.ds_hooks)
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
        let uu____8846 =
          (unique false true env l) || (FStar_Options.interactive ())  in
        if uu____8846
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
          | FStar_Pervasives_Native.Some (se,uu____8871) ->
              let uu____8876 =
                FStar_Util.find_opt (FStar_Ident.lid_equals l)
                  (FStar_Syntax_Util.lids_of_sigelt se)
                 in
              (match uu____8876 with
               | FStar_Pervasives_Native.Some l1 ->
                   FStar_All.pipe_left FStar_Range.string_of_range
                     (FStar_Ident.range_of_lid l1)
               | FStar_Pervasives_Native.None  -> "<unknown>")
          | FStar_Pervasives_Native.None  -> "<unknown>"  in
        let uu____8884 =
          let uu____8889 =
            FStar_Util.format2
              "Duplicate top-level names [%s]; previously declared at %s"
              (FStar_Ident.text_of_lid l) r
             in
          (FStar_Errors.Fatal_DuplicateTopLevelNames, uu____8889)  in
        FStar_Errors.raise_error uu____8884 (FStar_Ident.range_of_lid l)  in
      let globals = FStar_Util.mk_ref env.scope_mods  in
      let env1 =
        let uu____8898 =
          match s.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let uu____8907 -> (false, true)
          | FStar_Syntax_Syntax.Sig_bundle uu____8914 -> (false, true)
          | uu____8923 -> (false, false)  in
        match uu____8898 with
        | (any_val,exclude_interface) ->
            let lids = FStar_Syntax_Util.lids_of_sigelt s  in
            let uu____8929 =
              FStar_Util.find_map lids
                (fun l  ->
                   let uu____8935 =
                     let uu____8936 = unique any_val exclude_interface env l
                        in
                     Prims.op_Negation uu____8936  in
                   if uu____8935
                   then FStar_Pervasives_Native.Some l
                   else FStar_Pervasives_Native.None)
               in
            (match uu____8929 with
             | FStar_Pervasives_Native.Some l -> err l
             | uu____8941 ->
                 (extract_record env globals s;
                  (let uu___123_9019 = env  in
                   {
                     curmodule = (uu___123_9019.curmodule);
                     curmonad = (uu___123_9019.curmonad);
                     modules = (uu___123_9019.modules);
                     scope_mods = (uu___123_9019.scope_mods);
                     exported_ids = (uu___123_9019.exported_ids);
                     trans_exported_ids = (uu___123_9019.trans_exported_ids);
                     includes = (uu___123_9019.includes);
                     sigaccum = (s :: (env.sigaccum));
                     sigmap = (uu___123_9019.sigmap);
                     iface = (uu___123_9019.iface);
                     admitted_iface = (uu___123_9019.admitted_iface);
                     expect_typ = (uu___123_9019.expect_typ);
                     docs = (uu___123_9019.docs);
                     remaining_iface_decls =
                       (uu___123_9019.remaining_iface_decls);
                     syntax_only = (uu___123_9019.syntax_only);
                     ds_hooks = (uu___123_9019.ds_hooks)
                   })))
         in
      let env2 =
        let uu___124_9021 = env1  in
        let uu____9022 = FStar_ST.op_Bang globals  in
        {
          curmodule = (uu___124_9021.curmodule);
          curmonad = (uu___124_9021.curmonad);
          modules = (uu___124_9021.modules);
          scope_mods = uu____9022;
          exported_ids = (uu___124_9021.exported_ids);
          trans_exported_ids = (uu___124_9021.trans_exported_ids);
          includes = (uu___124_9021.includes);
          sigaccum = (uu___124_9021.sigaccum);
          sigmap = (uu___124_9021.sigmap);
          iface = (uu___124_9021.iface);
          admitted_iface = (uu___124_9021.admitted_iface);
          expect_typ = (uu___124_9021.expect_typ);
          docs = (uu___124_9021.docs);
          remaining_iface_decls = (uu___124_9021.remaining_iface_decls);
          syntax_only = (uu___124_9021.syntax_only);
          ds_hooks = (uu___124_9021.ds_hooks)
        }  in
      let uu____9122 =
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_bundle (ses,uu____9148) ->
            let uu____9157 =
              FStar_List.map
                (fun se  -> ((FStar_Syntax_Util.lids_of_sigelt se), se)) ses
               in
            (env2, uu____9157)
        | uu____9184 -> (env2, [((FStar_Syntax_Util.lids_of_sigelt s), s)])
         in
      match uu____9122 with
      | (env3,lss) ->
          (FStar_All.pipe_right lss
             (FStar_List.iter
                (fun uu____9243  ->
                   match uu____9243 with
                   | (lids,se) ->
                       FStar_All.pipe_right lids
                         (FStar_List.iter
                            (fun lid  ->
                               (let uu____9265 =
                                  let uu____9268 = FStar_ST.op_Bang globals
                                     in
                                  (Top_level_def (lid.FStar_Ident.ident)) ::
                                    uu____9268
                                   in
                                FStar_ST.op_Colon_Equals globals uu____9265);
                               (match () with
                                | () ->
                                    let modul =
                                      let uu____9466 =
                                        FStar_Ident.lid_of_ids
                                          lid.FStar_Ident.ns
                                         in
                                      uu____9466.FStar_Ident.str  in
                                    ((let uu____9468 =
                                        get_exported_id_set env3 modul  in
                                      match uu____9468 with
                                      | FStar_Pervasives_Native.Some f ->
                                          let my_exported_ids =
                                            f Exported_id_term_type  in
                                          let uu____9524 =
                                            let uu____9525 =
                                              FStar_ST.op_Bang
                                                my_exported_ids
                                               in
                                            FStar_Util.set_add
                                              (lid.FStar_Ident.ident).FStar_Ident.idText
                                              uu____9525
                                             in
                                          FStar_ST.op_Colon_Equals
                                            my_exported_ids uu____9524
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
              let uu___125_9724 = env3  in
              let uu____9725 = FStar_ST.op_Bang globals  in
              {
                curmodule = (uu___125_9724.curmodule);
                curmonad = (uu___125_9724.curmonad);
                modules = (uu___125_9724.modules);
                scope_mods = uu____9725;
                exported_ids = (uu___125_9724.exported_ids);
                trans_exported_ids = (uu___125_9724.trans_exported_ids);
                includes = (uu___125_9724.includes);
                sigaccum = (uu___125_9724.sigaccum);
                sigmap = (uu___125_9724.sigmap);
                iface = (uu___125_9724.iface);
                admitted_iface = (uu___125_9724.admitted_iface);
                expect_typ = (uu___125_9724.expect_typ);
                docs = (uu___125_9724.docs);
                remaining_iface_decls = (uu___125_9724.remaining_iface_decls);
                syntax_only = (uu___125_9724.syntax_only);
                ds_hooks = (uu___125_9724.ds_hooks)
              }  in
            env4))
  
let (push_namespace : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun ns  ->
      let uu____9831 =
        let uu____9836 = resolve_module_name env ns false  in
        match uu____9836 with
        | FStar_Pervasives_Native.None  ->
            let modules = env.modules  in
            let uu____9850 =
              FStar_All.pipe_right modules
                (FStar_Util.for_some
                   (fun uu____9864  ->
                      match uu____9864 with
                      | (m,uu____9870) ->
                          FStar_Util.starts_with
                            (Prims.strcat (FStar_Ident.text_of_lid m) ".")
                            (Prims.strcat (FStar_Ident.text_of_lid ns) ".")))
               in
            if uu____9850
            then (ns, Open_namespace)
            else
              (let uu____9876 =
                 let uu____9881 =
                   FStar_Util.format1 "Namespace %s cannot be found"
                     (FStar_Ident.text_of_lid ns)
                    in
                 (FStar_Errors.Fatal_NameSpaceNotFound, uu____9881)  in
               FStar_Errors.raise_error uu____9876
                 (FStar_Ident.range_of_lid ns))
        | FStar_Pervasives_Native.Some ns' ->
            (fail_if_curmodule env ns ns'; (ns', Open_module))
         in
      match uu____9831 with
      | (ns',kd) ->
          ((env.ds_hooks).ds_push_open_hook env (ns', kd);
           push_scope_mod env (Open_module_or_namespace (ns', kd)))
  
let (push_include : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun ns  ->
      let ns0 = ns  in
      let uu____9898 = resolve_module_name env ns false  in
      match uu____9898 with
      | FStar_Pervasives_Native.Some ns1 ->
          ((env.ds_hooks).ds_push_include_hook env ns1;
           fail_if_curmodule env ns0 ns1;
           (let env1 =
              push_scope_mod env
                (Open_module_or_namespace (ns1, Open_module))
               in
            let curmod =
              let uu____9906 = current_module env1  in
              uu____9906.FStar_Ident.str  in
            (let uu____9908 = FStar_Util.smap_try_find env1.includes curmod
                in
             match uu____9908 with
             | FStar_Pervasives_Native.None  -> ()
             | FStar_Pervasives_Native.Some incl ->
                 let uu____9932 =
                   let uu____9935 = FStar_ST.op_Bang incl  in ns1 ::
                     uu____9935
                    in
                 FStar_ST.op_Colon_Equals incl uu____9932);
            (match () with
             | () ->
                 let uu____10132 =
                   get_trans_exported_id_set env1 ns1.FStar_Ident.str  in
                 (match uu____10132 with
                  | FStar_Pervasives_Native.Some ns_trans_exports ->
                      ((let uu____10149 =
                          let uu____10166 = get_exported_id_set env1 curmod
                             in
                          let uu____10173 =
                            get_trans_exported_id_set env1 curmod  in
                          (uu____10166, uu____10173)  in
                        match uu____10149 with
                        | (FStar_Pervasives_Native.Some
                           cur_exports,FStar_Pervasives_Native.Some
                           cur_trans_exports) ->
                            let update_exports k =
                              let ns_ex =
                                let uu____10227 = ns_trans_exports k  in
                                FStar_ST.op_Bang uu____10227  in
                              let ex = cur_exports k  in
                              (let uu____10457 =
                                 let uu____10458 = FStar_ST.op_Bang ex  in
                                 FStar_Util.set_difference uu____10458 ns_ex
                                  in
                               FStar_ST.op_Colon_Equals ex uu____10457);
                              (match () with
                               | () ->
                                   let trans_ex = cur_trans_exports k  in
                                   let uu____10688 =
                                     let uu____10689 =
                                       FStar_ST.op_Bang trans_ex  in
                                     FStar_Util.set_union uu____10689 ns_ex
                                      in
                                   FStar_ST.op_Colon_Equals trans_ex
                                     uu____10688)
                               in
                            FStar_List.iter update_exports
                              all_exported_id_kinds
                        | uu____10878 -> ());
                       (match () with | () -> env1))
                  | FStar_Pervasives_Native.None  ->
                      let uu____10899 =
                        let uu____10904 =
                          FStar_Util.format1
                            "include: Module %s was not prepared"
                            ns1.FStar_Ident.str
                           in
                        (FStar_Errors.Fatal_IncludeModuleNotPrepared,
                          uu____10904)
                         in
                      FStar_Errors.raise_error uu____10899
                        (FStar_Ident.range_of_lid ns1)))))
      | uu____10905 ->
          let uu____10908 =
            let uu____10913 =
              FStar_Util.format1 "include: Module %s cannot be found"
                ns.FStar_Ident.str
               in
            (FStar_Errors.Fatal_ModuleNotFound, uu____10913)  in
          FStar_Errors.raise_error uu____10908 (FStar_Ident.range_of_lid ns)
  
let (push_module_abbrev :
  env -> FStar_Ident.ident -> FStar_Ident.lident -> env) =
  fun env  ->
    fun x  ->
      fun l  ->
        let uu____10923 = module_is_defined env l  in
        if uu____10923
        then
          (fail_if_curmodule env l l;
           (env.ds_hooks).ds_push_module_abbrev_hook env x l;
           push_scope_mod env (Module_abbrev (x, l)))
        else
          (let uu____10927 =
             let uu____10932 =
               FStar_Util.format1 "Module %s cannot be found"
                 (FStar_Ident.text_of_lid l)
                in
             (FStar_Errors.Fatal_ModuleNotFound, uu____10932)  in
           FStar_Errors.raise_error uu____10927 (FStar_Ident.range_of_lid l))
  
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
            ((let uu____10948 =
                FStar_Util.smap_try_find env.docs l.FStar_Ident.str  in
              match uu____10948 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some old_doc ->
                  let uu____10952 =
                    let uu____10957 =
                      let uu____10958 = FStar_Ident.string_of_lid l  in
                      let uu____10959 =
                        FStar_Parser_AST.string_of_fsdoc old_doc  in
                      let uu____10960 = FStar_Parser_AST.string_of_fsdoc doc1
                         in
                      FStar_Util.format3
                        "Overwriting doc of %s; old doc was [%s]; new doc are [%s]"
                        uu____10958 uu____10959 uu____10960
                       in
                    (FStar_Errors.Warning_DocOverwrite, uu____10957)  in
                  FStar_Errors.log_issue (FStar_Ident.range_of_lid l)
                    uu____10952);
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
                  | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t) ->
                      let uu____10993 = try_lookup_lid env l  in
                      (match uu____10993 with
                       | FStar_Pervasives_Native.None  ->
                           ((let uu____11007 =
                               let uu____11008 = FStar_Options.interactive ()
                                  in
                               Prims.op_Negation uu____11008  in
                             if uu____11007
                             then
                               let uu____11009 =
                                 let uu____11014 =
                                   let uu____11015 =
                                     FStar_Syntax_Print.lid_to_string l  in
                                   FStar_Util.format1
                                     "Admitting %s without a definition"
                                     uu____11015
                                    in
                                 (FStar_Errors.Warning_AdmitWithoutDefinition,
                                   uu____11014)
                                  in
                               FStar_Errors.log_issue
                                 (FStar_Ident.range_of_lid l) uu____11009
                             else ());
                            (let quals = FStar_Syntax_Syntax.Assumption ::
                               (se.FStar_Syntax_Syntax.sigquals)  in
                             FStar_Util.smap_add (sigmap env)
                               l.FStar_Ident.str
                               ((let uu___126_11026 = se  in
                                 {
                                   FStar_Syntax_Syntax.sigel =
                                     (uu___126_11026.FStar_Syntax_Syntax.sigel);
                                   FStar_Syntax_Syntax.sigrng =
                                     (uu___126_11026.FStar_Syntax_Syntax.sigrng);
                                   FStar_Syntax_Syntax.sigquals = quals;
                                   FStar_Syntax_Syntax.sigmeta =
                                     (uu___126_11026.FStar_Syntax_Syntax.sigmeta);
                                   FStar_Syntax_Syntax.sigattrs =
                                     (uu___126_11026.FStar_Syntax_Syntax.sigattrs)
                                 }), false);
                             l
                             ::
                             lids))
                       | FStar_Pervasives_Native.Some uu____11027 -> lids)
                  | uu____11036 -> lids) [])
         in
      let uu___127_11037 = m  in
      let uu____11038 =
        FStar_All.pipe_right m.FStar_Syntax_Syntax.declarations
          (FStar_List.map
             (fun s  ->
                match s.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_declare_typ
                    (lid,uu____11049,uu____11050) when
                    FStar_List.existsb
                      (fun l  -> FStar_Ident.lid_equals l lid)
                      admitted_sig_lids
                    ->
                    (FStar_Util.print_string "Adding qual\n\n";
                     (let uu___128_11054 = s  in
                      {
                        FStar_Syntax_Syntax.sigel =
                          (uu___128_11054.FStar_Syntax_Syntax.sigel);
                        FStar_Syntax_Syntax.sigrng =
                          (uu___128_11054.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (FStar_Syntax_Syntax.Assumption ::
                          (s.FStar_Syntax_Syntax.sigquals));
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___128_11054.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs =
                          (uu___128_11054.FStar_Syntax_Syntax.sigattrs)
                      }))
                | uu____11055 -> s))
         in
      {
        FStar_Syntax_Syntax.name = (uu___127_11037.FStar_Syntax_Syntax.name);
        FStar_Syntax_Syntax.declarations = uu____11038;
        FStar_Syntax_Syntax.is_interface =
          (uu___127_11037.FStar_Syntax_Syntax.is_interface)
      }
  
let (finish : env -> FStar_Syntax_Syntax.modul -> env) =
  fun env  ->
    fun modul  ->
      FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations
        (FStar_List.iter
           (fun se  ->
              let quals = se.FStar_Syntax_Syntax.sigquals  in
              match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_bundle (ses,uu____11072) ->
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
                                (lid,uu____11092,uu____11093,uu____11094,uu____11095,uu____11096)
                                ->
                                FStar_Util.smap_remove (sigmap env)
                                  lid.FStar_Ident.str
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (lid,univ_names,binders,typ,uu____11109,uu____11110)
                                ->
                                (FStar_Util.smap_remove (sigmap env)
                                   lid.FStar_Ident.str;
                                 if
                                   Prims.op_Negation
                                     (FStar_List.contains
                                        FStar_Syntax_Syntax.Private quals)
                                 then
                                   (let sigel =
                                      let uu____11125 =
                                        let uu____11132 =
                                          let uu____11135 =
                                            let uu____11138 =
                                              let uu____11139 =
                                                let uu____11152 =
                                                  FStar_Syntax_Syntax.mk_Total
                                                    typ
                                                   in
                                                (binders, uu____11152)  in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____11139
                                               in
                                            FStar_Syntax_Syntax.mk
                                              uu____11138
                                             in
                                          uu____11135
                                            FStar_Pervasives_Native.None
                                            (FStar_Ident.range_of_lid lid)
                                           in
                                        (lid, univ_names, uu____11132)  in
                                      FStar_Syntax_Syntax.Sig_declare_typ
                                        uu____11125
                                       in
                                    let se2 =
                                      let uu___129_11159 = se1  in
                                      {
                                        FStar_Syntax_Syntax.sigel = sigel;
                                        FStar_Syntax_Syntax.sigrng =
                                          (uu___129_11159.FStar_Syntax_Syntax.sigrng);
                                        FStar_Syntax_Syntax.sigquals =
                                          (FStar_Syntax_Syntax.Assumption ::
                                          quals);
                                        FStar_Syntax_Syntax.sigmeta =
                                          (uu___129_11159.FStar_Syntax_Syntax.sigmeta);
                                        FStar_Syntax_Syntax.sigattrs =
                                          (uu___129_11159.FStar_Syntax_Syntax.sigattrs)
                                      }  in
                                    FStar_Util.smap_add (sigmap env)
                                      lid.FStar_Ident.str (se2, false))
                                 else ())
                            | uu____11165 -> ()))
                  else ()
              | FStar_Syntax_Syntax.Sig_declare_typ
                  (lid,uu____11168,uu____11169) ->
                  if FStar_List.contains FStar_Syntax_Syntax.Private quals
                  then
                    FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str
                  else ()
              | FStar_Syntax_Syntax.Sig_let ((uu____11175,lbs),uu____11177)
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
                             let uu____11198 =
                               let uu____11199 =
                                 let uu____11200 =
                                   let uu____11203 =
                                     FStar_Util.right
                                       lb.FStar_Syntax_Syntax.lbname
                                      in
                                   uu____11203.FStar_Syntax_Syntax.fv_name
                                    in
                                 uu____11200.FStar_Syntax_Syntax.v  in
                               uu____11199.FStar_Ident.str  in
                             FStar_Util.smap_remove (sigmap env) uu____11198))
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
                               let uu____11217 =
                                 let uu____11220 =
                                   FStar_Util.right
                                     lb.FStar_Syntax_Syntax.lbname
                                    in
                                 uu____11220.FStar_Syntax_Syntax.fv_name  in
                               uu____11217.FStar_Syntax_Syntax.v  in
                             let quals1 = FStar_Syntax_Syntax.Assumption ::
                               quals  in
                             let decl =
                               let uu___130_11225 = se  in
                               {
                                 FStar_Syntax_Syntax.sigel =
                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                      (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                        (lb.FStar_Syntax_Syntax.lbtyp)));
                                 FStar_Syntax_Syntax.sigrng =
                                   (uu___130_11225.FStar_Syntax_Syntax.sigrng);
                                 FStar_Syntax_Syntax.sigquals = quals1;
                                 FStar_Syntax_Syntax.sigmeta =
                                   (uu___130_11225.FStar_Syntax_Syntax.sigmeta);
                                 FStar_Syntax_Syntax.sigattrs =
                                   (uu___130_11225.FStar_Syntax_Syntax.sigattrs)
                               }  in
                             FStar_Util.smap_add (sigmap env)
                               lid.FStar_Ident.str (decl, false)))
                   else ())
              | uu____11235 -> ()));
      (let curmod =
         let uu____11237 = current_module env  in uu____11237.FStar_Ident.str
          in
       (let uu____11239 =
          let uu____11256 = get_exported_id_set env curmod  in
          let uu____11263 = get_trans_exported_id_set env curmod  in
          (uu____11256, uu____11263)  in
        match uu____11239 with
        | (FStar_Pervasives_Native.Some cur_ex,FStar_Pervasives_Native.Some
           cur_trans_ex) ->
            let update_exports eikind =
              let cur_ex_set =
                let uu____11317 = cur_ex eikind  in
                FStar_ST.op_Bang uu____11317  in
              let cur_trans_ex_set_ref = cur_trans_ex eikind  in
              let uu____11546 =
                let uu____11547 = FStar_ST.op_Bang cur_trans_ex_set_ref  in
                FStar_Util.set_union cur_ex_set uu____11547  in
              FStar_ST.op_Colon_Equals cur_trans_ex_set_ref uu____11546  in
            FStar_List.iter update_exports all_exported_id_kinds
        | uu____11736 -> ());
       (match () with
        | () ->
            (filter_record_cache ();
             (match () with
              | () ->
                  let uu___131_11754 = env  in
                  {
                    curmodule = FStar_Pervasives_Native.None;
                    curmonad = (uu___131_11754.curmonad);
                    modules = (((modul.FStar_Syntax_Syntax.name), modul) ::
                      (env.modules));
                    scope_mods = [];
                    exported_ids = (uu___131_11754.exported_ids);
                    trans_exported_ids = (uu___131_11754.trans_exported_ids);
                    includes = (uu___131_11754.includes);
                    sigaccum = [];
                    sigmap = (uu___131_11754.sigmap);
                    iface = (uu___131_11754.iface);
                    admitted_iface = (uu___131_11754.admitted_iface);
                    expect_typ = (uu___131_11754.expect_typ);
                    docs = (uu___131_11754.docs);
                    remaining_iface_decls =
                      (uu___131_11754.remaining_iface_decls);
                    syntax_only = (uu___131_11754.syntax_only);
                    ds_hooks = (uu___131_11754.ds_hooks)
                  }))))
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push : env -> env) =
  fun env  ->
    push_record_cache ();
    (let uu____11807 =
       let uu____11810 = FStar_ST.op_Bang stack  in env :: uu____11810  in
     FStar_ST.op_Colon_Equals stack uu____11807);
    (let uu___132_11859 = env  in
     let uu____11860 = FStar_Util.smap_copy (sigmap env)  in
     let uu____11871 = FStar_Util.smap_copy env.docs  in
     {
       curmodule = (uu___132_11859.curmodule);
       curmonad = (uu___132_11859.curmonad);
       modules = (uu___132_11859.modules);
       scope_mods = (uu___132_11859.scope_mods);
       exported_ids = (uu___132_11859.exported_ids);
       trans_exported_ids = (uu___132_11859.trans_exported_ids);
       includes = (uu___132_11859.includes);
       sigaccum = (uu___132_11859.sigaccum);
       sigmap = uu____11860;
       iface = (uu___132_11859.iface);
       admitted_iface = (uu___132_11859.admitted_iface);
       expect_typ = (uu___132_11859.expect_typ);
       docs = uu____11871;
       remaining_iface_decls = (uu___132_11859.remaining_iface_decls);
       syntax_only = (uu___132_11859.syntax_only);
       ds_hooks = (uu___132_11859.ds_hooks)
     })
  
let (pop : Prims.unit -> env) =
  fun uu____11876  ->
    let uu____11877 = FStar_ST.op_Bang stack  in
    match uu____11877 with
    | env::tl1 ->
        (pop_record_cache (); FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____11932 -> failwith "Impossible: Too many pops"
  
let (export_interface : FStar_Ident.lident -> env -> env) =
  fun m  ->
    fun env  ->
      let sigelt_in_m se =
        match FStar_Syntax_Util.lids_of_sigelt se with
        | l::uu____11946 -> l.FStar_Ident.nsstr = m.FStar_Ident.str
        | uu____11949 -> false  in
      let sm = sigmap env  in
      let env1 = pop ()  in
      let keys = FStar_Util.smap_keys sm  in
      let sm' = sigmap env1  in
      FStar_All.pipe_right keys
        (FStar_List.iter
           (fun k  ->
              let uu____11983 = FStar_Util.smap_try_find sm' k  in
              match uu____11983 with
              | FStar_Pervasives_Native.Some (se,true ) when sigelt_in_m se
                  ->
                  (FStar_Util.smap_remove sm' k;
                   (let se1 =
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t) ->
                          let uu___133_12008 = se  in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (uu___133_12008.FStar_Syntax_Syntax.sigel);
                            FStar_Syntax_Syntax.sigrng =
                              (uu___133_12008.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (FStar_Syntax_Syntax.Assumption ::
                              (se.FStar_Syntax_Syntax.sigquals));
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___133_12008.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___133_12008.FStar_Syntax_Syntax.sigattrs)
                          }
                      | uu____12009 -> se  in
                    FStar_Util.smap_add sm' k (se1, false)))
              | uu____12014 -> ()));
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
      let uu____12033 = finish env modul1  in (uu____12033, modul1)
  
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
      let uu____12189 =
        let uu____12192 = e Exported_id_term_type  in
        FStar_ST.op_Bang uu____12192  in
      FStar_Util.set_elements uu____12189  in
    let fields =
      let uu____12384 =
        let uu____12387 = e Exported_id_field  in
        FStar_ST.op_Bang uu____12387  in
      FStar_Util.set_elements uu____12384  in
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
          let uu____12638 =
            FStar_Util.as_set e1.exported_id_terms FStar_Util.compare  in
          FStar_Util.mk_ref uu____12638  in
        let fields =
          let uu____12648 =
            FStar_Util.as_set e1.exported_id_fields FStar_Util.compare  in
          FStar_Util.mk_ref uu____12648  in
        (fun uu___108_12653  ->
           match uu___108_12653 with
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
  'Auu____12851 .
    'Auu____12851 Prims.list FStar_Pervasives_Native.option ->
      'Auu____12851 Prims.list FStar_ST.ref
  =
  fun uu___109_12863  ->
    match uu___109_12863 with
    | FStar_Pervasives_Native.None  -> FStar_Util.mk_ref []
    | FStar_Pervasives_Native.Some l -> FStar_Util.mk_ref l
  
let (inclusion_info : env -> FStar_Ident.lident -> module_inclusion_info) =
  fun env  ->
    fun l  ->
      let mname = FStar_Ident.string_of_lid l  in
      let as_ids_opt m =
        let uu____12896 = FStar_Util.smap_try_find m mname  in
        FStar_Util.map_opt uu____12896 as_exported_ids  in
      let uu____12899 = as_ids_opt env.exported_ids  in
      let uu____12902 = as_ids_opt env.trans_exported_ids  in
      let uu____12905 =
        let uu____12910 = FStar_Util.smap_try_find env.includes mname  in
        FStar_Util.map_opt uu____12910 (fun r  -> FStar_ST.op_Bang r)  in
      {
        mii_exported_ids = uu____12899;
        mii_trans_exported_ids = uu____12902;
        mii_includes = uu____12905
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
                let convert_kind uu___110_13108 =
                  match uu___110_13108 with
                  | FStar_Parser_Dep.Open_namespace  -> Open_namespace
                  | FStar_Parser_Dep.Open_module  -> Open_module  in
                FStar_List.map
                  (fun uu____13120  ->
                     match uu____13120 with
                     | (lid,kind) -> (lid, (convert_kind kind))) auto_open
                 in
              let namespace_of_module =
                if
                  (FStar_List.length mname.FStar_Ident.ns) >
                    (Prims.parse_int "0")
                then
                  let uu____13144 =
                    let uu____13149 =
                      FStar_Ident.lid_of_ids mname.FStar_Ident.ns  in
                    (uu____13149, Open_namespace)  in
                  [uu____13144]
                else []  in
              let auto_open2 =
                FStar_List.append namespace_of_module
                  (FStar_List.rev auto_open1)
                 in
              (let uu____13179 = as_exported_id_set mii.mii_exported_ids  in
               FStar_Util.smap_add env1.exported_ids mname.FStar_Ident.str
                 uu____13179);
              (match () with
               | () ->
                   ((let uu____13255 =
                       as_exported_id_set mii.mii_trans_exported_ids  in
                     FStar_Util.smap_add env1.trans_exported_ids
                       mname.FStar_Ident.str uu____13255);
                    (match () with
                     | () ->
                         ((let uu____13331 = as_includes mii.mii_includes  in
                           FStar_Util.smap_add env1.includes
                             mname.FStar_Ident.str uu____13331);
                          (match () with
                           | () ->
                               let env' =
                                 let uu___134_13415 = env1  in
                                 let uu____13416 =
                                   FStar_List.map
                                     (fun x  -> Open_module_or_namespace x)
                                     auto_open2
                                    in
                                 {
                                   curmodule =
                                     (FStar_Pervasives_Native.Some mname);
                                   curmonad = (uu___134_13415.curmonad);
                                   modules = (uu___134_13415.modules);
                                   scope_mods = uu____13416;
                                   exported_ids =
                                     (uu___134_13415.exported_ids);
                                   trans_exported_ids =
                                     (uu___134_13415.trans_exported_ids);
                                   includes = (uu___134_13415.includes);
                                   sigaccum = (uu___134_13415.sigaccum);
                                   sigmap = (env1.sigmap);
                                   iface = intf;
                                   admitted_iface = admitted;
                                   expect_typ = (uu___134_13415.expect_typ);
                                   docs = (uu___134_13415.docs);
                                   remaining_iface_decls =
                                     (uu___134_13415.remaining_iface_decls);
                                   syntax_only = (uu___134_13415.syntax_only);
                                   ds_hooks = (uu___134_13415.ds_hooks)
                                 }  in
                               (FStar_List.iter
                                  (fun op  ->
                                     (env1.ds_hooks).ds_push_open_hook env'
                                       op) (FStar_List.rev auto_open2);
                                env'))))))
               in
            let uu____13428 =
              FStar_All.pipe_right env.modules
                (FStar_Util.find_opt
                   (fun uu____13454  ->
                      match uu____13454 with
                      | (l,uu____13460) -> FStar_Ident.lid_equals l mname))
               in
            match uu____13428 with
            | FStar_Pervasives_Native.None  ->
                let uu____13469 = prep env  in (uu____13469, false)
            | FStar_Pervasives_Native.Some (uu____13470,m) ->
                ((let uu____13477 =
                    (let uu____13480 = FStar_Options.interactive ()  in
                     Prims.op_Negation uu____13480) &&
                      ((Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)
                         || intf)
                     in
                  if uu____13477
                  then
                    let uu____13481 =
                      let uu____13486 =
                        FStar_Util.format1
                          "Duplicate module or interface name: %s"
                          mname.FStar_Ident.str
                         in
                      (FStar_Errors.Fatal_DuplicateModuleOrInterface,
                        uu____13486)
                       in
                    FStar_Errors.raise_error uu____13481
                      (FStar_Ident.range_of_lid mname)
                  else ());
                 (let uu____13488 =
                    let uu____13489 = push env  in prep uu____13489  in
                  (uu____13488, true)))
  
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
          let uu___135_13497 = env  in
          {
            curmodule = (uu___135_13497.curmodule);
            curmonad = (FStar_Pervasives_Native.Some mname);
            modules = (uu___135_13497.modules);
            scope_mods = (uu___135_13497.scope_mods);
            exported_ids = (uu___135_13497.exported_ids);
            trans_exported_ids = (uu___135_13497.trans_exported_ids);
            includes = (uu___135_13497.includes);
            sigaccum = (uu___135_13497.sigaccum);
            sigmap = (uu___135_13497.sigmap);
            iface = (uu___135_13497.iface);
            admitted_iface = (uu___135_13497.admitted_iface);
            expect_typ = (uu___135_13497.expect_typ);
            docs = (uu___135_13497.docs);
            remaining_iface_decls = (uu___135_13497.remaining_iface_decls);
            syntax_only = (uu___135_13497.syntax_only);
            ds_hooks = (uu___135_13497.ds_hooks)
          }
  
let fail_or :
  'a .
    env ->
      (FStar_Ident.lident -> 'a FStar_Pervasives_Native.option) ->
        FStar_Ident.lident -> 'a
  =
  fun env  ->
    fun lookup  ->
      fun lid  ->
        let uu____13524 = lookup lid  in
        match uu____13524 with
        | FStar_Pervasives_Native.None  ->
            let opened_modules =
              FStar_List.map
                (fun uu____13537  ->
                   match uu____13537 with
                   | (lid1,uu____13543) -> FStar_Ident.text_of_lid lid1)
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
                   let uu____13548 =
                     FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
                   FStar_Ident.set_lid_range uu____13548
                     (FStar_Ident.range_of_lid lid)
                    in
                 let uu____13549 = resolve_module_name env modul true  in
                 match uu____13549 with
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
  fun lookup  ->
    fun id1  ->
      let uu____13580 = lookup id1  in
      match uu____13580 with
      | FStar_Pervasives_Native.None  ->
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_IdentifierNotFound,
              (Prims.strcat "Identifier not found ["
                 (Prims.strcat id1.FStar_Ident.idText "]")))
            id1.FStar_Ident.idRange
      | FStar_Pervasives_Native.Some r -> r
  