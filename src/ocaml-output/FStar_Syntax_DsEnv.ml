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
    match projectee with | Local_binding _0 -> true | uu____207 -> false
  
let (__proj__Local_binding__item___0 : scope_mod -> local_binding) =
  fun projectee  -> match projectee with | Local_binding _0 -> _0 
let (uu___is_Rec_binding : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with | Rec_binding _0 -> true | uu____221 -> false
  
let (__proj__Rec_binding__item___0 : scope_mod -> rec_binding) =
  fun projectee  -> match projectee with | Rec_binding _0 -> _0 
let (uu___is_Module_abbrev : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with | Module_abbrev _0 -> true | uu____235 -> false
  
let (__proj__Module_abbrev__item___0 : scope_mod -> module_abbrev) =
  fun projectee  -> match projectee with | Module_abbrev _0 -> _0 
let (uu___is_Open_module_or_namespace : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Open_module_or_namespace _0 -> true
    | uu____249 -> false
  
let (__proj__Open_module_or_namespace__item___0 :
  scope_mod -> open_module_or_namespace) =
  fun projectee  -> match projectee with | Open_module_or_namespace _0 -> _0 
let (uu___is_Top_level_def : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with | Top_level_def _0 -> true | uu____263 -> false
  
let (__proj__Top_level_def__item___0 : scope_mod -> FStar_Ident.ident) =
  fun projectee  -> match projectee with | Top_level_def _0 -> _0 
let (uu___is_Record_or_dc : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with | Record_or_dc _0 -> true | uu____277 -> false
  
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
    | uu____292 -> false
  
let (uu___is_Exported_id_field : exported_id_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exported_id_field  -> true | uu____298 -> false
  
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
    ds_push_open_hook = (fun uu____1685  -> fun uu____1686  -> ());
    ds_push_include_hook = (fun uu____1689  -> fun uu____1690  -> ());
    ds_push_module_abbrev_hook =
      (fun uu____1694  -> fun uu____1695  -> fun uu____1696  -> ())
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
    match projectee with | Term_name _0 -> true | uu____1731 -> false
  
let (__proj__Term_name__item___0 :
  foundname ->
    (FStar_Syntax_Syntax.typ,Prims.bool,FStar_Syntax_Syntax.attribute
                                          Prims.list)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Term_name _0 -> _0 
let (uu___is_Eff_name : foundname -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eff_name _0 -> true | uu____1773 -> false
  
let (__proj__Eff_name__item___0 :
  foundname ->
    (FStar_Syntax_Syntax.sigelt,FStar_Ident.lident)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Eff_name _0 -> _0 
let (set_iface : env -> Prims.bool -> env) =
  fun env  ->
    fun b  ->
      let uu___114_1803 = env  in
      {
        curmodule = (uu___114_1803.curmodule);
        curmonad = (uu___114_1803.curmonad);
        modules = (uu___114_1803.modules);
        scope_mods = (uu___114_1803.scope_mods);
        exported_ids = (uu___114_1803.exported_ids);
        trans_exported_ids = (uu___114_1803.trans_exported_ids);
        includes = (uu___114_1803.includes);
        sigaccum = (uu___114_1803.sigaccum);
        sigmap = (uu___114_1803.sigmap);
        iface = b;
        admitted_iface = (uu___114_1803.admitted_iface);
        expect_typ = (uu___114_1803.expect_typ);
        docs = (uu___114_1803.docs);
        remaining_iface_decls = (uu___114_1803.remaining_iface_decls);
        syntax_only = (uu___114_1803.syntax_only);
        ds_hooks = (uu___114_1803.ds_hooks)
      }
  
let (iface : env -> Prims.bool) = fun e  -> e.iface 
let (set_admitted_iface : env -> Prims.bool -> env) =
  fun e  ->
    fun b  ->
      let uu___115_1819 = e  in
      {
        curmodule = (uu___115_1819.curmodule);
        curmonad = (uu___115_1819.curmonad);
        modules = (uu___115_1819.modules);
        scope_mods = (uu___115_1819.scope_mods);
        exported_ids = (uu___115_1819.exported_ids);
        trans_exported_ids = (uu___115_1819.trans_exported_ids);
        includes = (uu___115_1819.includes);
        sigaccum = (uu___115_1819.sigaccum);
        sigmap = (uu___115_1819.sigmap);
        iface = (uu___115_1819.iface);
        admitted_iface = b;
        expect_typ = (uu___115_1819.expect_typ);
        docs = (uu___115_1819.docs);
        remaining_iface_decls = (uu___115_1819.remaining_iface_decls);
        syntax_only = (uu___115_1819.syntax_only);
        ds_hooks = (uu___115_1819.ds_hooks)
      }
  
let (admitted_iface : env -> Prims.bool) = fun e  -> e.admitted_iface 
let (set_expect_typ : env -> Prims.bool -> env) =
  fun e  ->
    fun b  ->
      let uu___116_1835 = e  in
      {
        curmodule = (uu___116_1835.curmodule);
        curmonad = (uu___116_1835.curmonad);
        modules = (uu___116_1835.modules);
        scope_mods = (uu___116_1835.scope_mods);
        exported_ids = (uu___116_1835.exported_ids);
        trans_exported_ids = (uu___116_1835.trans_exported_ids);
        includes = (uu___116_1835.includes);
        sigaccum = (uu___116_1835.sigaccum);
        sigmap = (uu___116_1835.sigmap);
        iface = (uu___116_1835.iface);
        admitted_iface = (uu___116_1835.admitted_iface);
        expect_typ = b;
        docs = (uu___116_1835.docs);
        remaining_iface_decls = (uu___116_1835.remaining_iface_decls);
        syntax_only = (uu___116_1835.syntax_only);
        ds_hooks = (uu___116_1835.ds_hooks)
      }
  
let (expect_typ : env -> Prims.bool) = fun e  -> e.expect_typ 
let (all_exported_id_kinds : exported_id_kind Prims.list) =
  [Exported_id_field; Exported_id_term_type] 
let (transitive_exported_ids :
  env -> FStar_Ident.lident -> Prims.string Prims.list) =
  fun env  ->
    fun lid  ->
      let module_name = FStar_Ident.string_of_lid lid  in
      let uu____1856 =
        FStar_Util.smap_try_find env.trans_exported_ids module_name  in
      match uu____1856 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some exported_id_set ->
          let uu____1867 =
            let uu____1868 = exported_id_set Exported_id_term_type  in
            FStar_ST.op_Bang uu____1868  in
          FStar_All.pipe_right uu____1867 FStar_Util.set_elements
  
let (open_modules :
  env ->
    (FStar_Ident.lident,FStar_Syntax_Syntax.modul)
      FStar_Pervasives_Native.tuple2 Prims.list)
  = fun e  -> e.modules 
let (open_modules_and_namespaces : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    FStar_List.filter_map
      (fun uu___82_2010  ->
         match uu___82_2010 with
         | Open_module_or_namespace (lid,_info) ->
             FStar_Pervasives_Native.Some lid
         | uu____2015 -> FStar_Pervasives_Native.None) env.scope_mods
  
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun e  ->
    fun l  ->
      let uu___117_2026 = e  in
      {
        curmodule = (FStar_Pervasives_Native.Some l);
        curmonad = (uu___117_2026.curmonad);
        modules = (uu___117_2026.modules);
        scope_mods = (uu___117_2026.scope_mods);
        exported_ids = (uu___117_2026.exported_ids);
        trans_exported_ids = (uu___117_2026.trans_exported_ids);
        includes = (uu___117_2026.includes);
        sigaccum = (uu___117_2026.sigaccum);
        sigmap = (uu___117_2026.sigmap);
        iface = (uu___117_2026.iface);
        admitted_iface = (uu___117_2026.admitted_iface);
        expect_typ = (uu___117_2026.expect_typ);
        docs = (uu___117_2026.docs);
        remaining_iface_decls = (uu___117_2026.remaining_iface_decls);
        syntax_only = (uu___117_2026.syntax_only);
        ds_hooks = (uu___117_2026.ds_hooks)
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
      let uu____2047 =
        FStar_All.pipe_right env.remaining_iface_decls
          (FStar_List.tryFind
             (fun uu____2081  ->
                match uu____2081 with
                | (m,uu____2089) -> FStar_Ident.lid_equals l m))
         in
      match uu____2047 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (uu____2106,decls) ->
          FStar_Pervasives_Native.Some decls
  
let (set_iface_decls :
  env -> FStar_Ident.lident -> FStar_Parser_AST.decl Prims.list -> env) =
  fun env  ->
    fun l  ->
      fun ds  ->
        let uu____2139 =
          FStar_List.partition
            (fun uu____2169  ->
               match uu____2169 with
               | (m,uu____2177) -> FStar_Ident.lid_equals l m)
            env.remaining_iface_decls
           in
        match uu____2139 with
        | (uu____2182,rest) ->
            let uu___118_2216 = env  in
            {
              curmodule = (uu___118_2216.curmodule);
              curmonad = (uu___118_2216.curmonad);
              modules = (uu___118_2216.modules);
              scope_mods = (uu___118_2216.scope_mods);
              exported_ids = (uu___118_2216.exported_ids);
              trans_exported_ids = (uu___118_2216.trans_exported_ids);
              includes = (uu___118_2216.includes);
              sigaccum = (uu___118_2216.sigaccum);
              sigmap = (uu___118_2216.sigmap);
              iface = (uu___118_2216.iface);
              admitted_iface = (uu___118_2216.admitted_iface);
              expect_typ = (uu___118_2216.expect_typ);
              docs = (uu___118_2216.docs);
              remaining_iface_decls = ((l, ds) :: rest);
              syntax_only = (uu___118_2216.syntax_only);
              ds_hooks = (uu___118_2216.ds_hooks)
            }
  
let (qual : FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident) =
  FStar_Syntax_Util.qual_id 
let (qualify : env -> FStar_Ident.ident -> FStar_Ident.lident) =
  fun env  ->
    fun id1  ->
      match env.curmonad with
      | FStar_Pervasives_Native.None  ->
          let uu____2243 = current_module env  in qual uu____2243 id1
      | FStar_Pervasives_Native.Some monad ->
          let uu____2245 =
            let uu____2246 = current_module env  in qual uu____2246 monad  in
          FStar_Syntax_Util.mk_field_projector_name_from_ident uu____2245 id1
  
let (syntax_only : env -> Prims.bool) = fun env  -> env.syntax_only 
let (set_syntax_only : env -> Prims.bool -> env) =
  fun env  ->
    fun b  ->
      let uu___119_2262 = env  in
      {
        curmodule = (uu___119_2262.curmodule);
        curmonad = (uu___119_2262.curmonad);
        modules = (uu___119_2262.modules);
        scope_mods = (uu___119_2262.scope_mods);
        exported_ids = (uu___119_2262.exported_ids);
        trans_exported_ids = (uu___119_2262.trans_exported_ids);
        includes = (uu___119_2262.includes);
        sigaccum = (uu___119_2262.sigaccum);
        sigmap = (uu___119_2262.sigmap);
        iface = (uu___119_2262.iface);
        admitted_iface = (uu___119_2262.admitted_iface);
        expect_typ = (uu___119_2262.expect_typ);
        docs = (uu___119_2262.docs);
        remaining_iface_decls = (uu___119_2262.remaining_iface_decls);
        syntax_only = b;
        ds_hooks = (uu___119_2262.ds_hooks)
      }
  
let (ds_hooks : env -> dsenv_hooks) = fun env  -> env.ds_hooks 
let (set_ds_hooks : env -> dsenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___120_2278 = env  in
      {
        curmodule = (uu___120_2278.curmodule);
        curmonad = (uu___120_2278.curmonad);
        modules = (uu___120_2278.modules);
        scope_mods = (uu___120_2278.scope_mods);
        exported_ids = (uu___120_2278.exported_ids);
        trans_exported_ids = (uu___120_2278.trans_exported_ids);
        includes = (uu___120_2278.includes);
        sigaccum = (uu___120_2278.sigaccum);
        sigmap = (uu___120_2278.sigmap);
        iface = (uu___120_2278.iface);
        admitted_iface = (uu___120_2278.admitted_iface);
        expect_typ = (uu___120_2278.expect_typ);
        docs = (uu___120_2278.docs);
        remaining_iface_decls = (uu___120_2278.remaining_iface_decls);
        syntax_only = (uu___120_2278.syntax_only);
        ds_hooks = hooks
      }
  
let new_sigmap : 'Auu____2283 . unit -> 'Auu____2283 FStar_Util.smap =
  fun uu____2290  -> FStar_Util.smap_create (Prims.parse_int "100") 
let (empty_env : unit -> env) =
  fun uu____2295  ->
    let uu____2296 = new_sigmap ()  in
    let uu____2301 = new_sigmap ()  in
    let uu____2306 = new_sigmap ()  in
    let uu____2317 = new_sigmap ()  in
    let uu____2328 = new_sigmap ()  in
    {
      curmodule = FStar_Pervasives_Native.None;
      curmonad = FStar_Pervasives_Native.None;
      modules = [];
      scope_mods = [];
      exported_ids = uu____2296;
      trans_exported_ids = uu____2301;
      includes = uu____2306;
      sigaccum = [];
      sigmap = uu____2317;
      iface = false;
      admitted_iface = false;
      expect_typ = false;
      docs = uu____2328;
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
      (fun uu____2364  ->
         match uu____2364 with
         | (m,uu____2370) ->
             FStar_Ident.lid_equals m FStar_Parser_Const.all_lid) env.modules
  
let (set_bv_range :
  FStar_Syntax_Syntax.bv -> FStar_Range.range -> FStar_Syntax_Syntax.bv) =
  fun bv  ->
    fun r  ->
      let id1 =
        let uu___121_2382 = bv.FStar_Syntax_Syntax.ppname  in
        {
          FStar_Ident.idText = (uu___121_2382.FStar_Ident.idText);
          FStar_Ident.idRange = r
        }  in
      let uu___122_2383 = bv  in
      {
        FStar_Syntax_Syntax.ppname = id1;
        FStar_Syntax_Syntax.index = (uu___122_2383.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = (uu___122_2383.FStar_Syntax_Syntax.sort)
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
        (fun uu____2476  ->
           match uu____2476 with
           | (x,y,dd,dq) ->
               if id1.FStar_Ident.idText = x
               then
                 let uu____2499 =
                   let uu____2500 =
                     FStar_Ident.lid_of_path ["Prims"; y]
                       id1.FStar_Ident.idRange
                      in
                   FStar_Syntax_Syntax.fvar uu____2500 dd dq  in
                 FStar_Pervasives_Native.Some uu____2499
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
    match projectee with | Cont_ok _0 -> true | uu____2546 -> false
  
let __proj__Cont_ok__item___0 : 'a . 'a cont_t -> 'a =
  fun projectee  -> match projectee with | Cont_ok _0 -> _0 
let uu___is_Cont_fail : 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_fail  -> true | uu____2579 -> false
  
let uu___is_Cont_ignore : 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_ignore  -> true | uu____2596 -> false
  
let option_of_cont :
  'a .
    (unit -> 'a FStar_Pervasives_Native.option) ->
      'a cont_t -> 'a FStar_Pervasives_Native.option
  =
  fun k_ignore  ->
    fun uu___83_2624  ->
      match uu___83_2624 with
      | Cont_ok a -> FStar_Pervasives_Native.Some a
      | Cont_fail  -> FStar_Pervasives_Native.None
      | Cont_ignore  -> k_ignore ()
  
let find_in_record :
  'Auu____2642 .
    FStar_Ident.ident Prims.list ->
      FStar_Ident.ident ->
        record_or_dc ->
          (record_or_dc -> 'Auu____2642 cont_t) -> 'Auu____2642 cont_t
  =
  fun ns  ->
    fun id1  ->
      fun record  ->
        fun cont  ->
          let typename' =
            FStar_Ident.lid_of_ids
              (FStar_List.append ns [(record.typename).FStar_Ident.ident])
             in
          let uu____2679 = FStar_Ident.lid_equals typename' record.typename
             in
          if uu____2679
          then
            let fname =
              FStar_Ident.lid_of_ids
                (FStar_List.append (record.typename).FStar_Ident.ns [id1])
               in
            let find1 =
              FStar_Util.find_map record.fields
                (fun uu____2693  ->
                   match uu____2693 with
                   | (f,uu____2701) ->
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
  fun uu___84_2763  ->
    match uu___84_2763 with
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
              let rec aux uu___85_2833 =
                match uu___85_2833 with
                | [] -> find_in_module_default
                | modul::q ->
                    let mname = modul.FStar_Ident.str  in
                    let not_shadowed =
                      let uu____2844 = get_exported_id_set env mname  in
                      match uu____2844 with
                      | FStar_Pervasives_Native.None  -> true
                      | FStar_Pervasives_Native.Some mex ->
                          let mexports =
                            let uu____2869 = mex eikind  in
                            FStar_ST.op_Bang uu____2869  in
                          FStar_Util.set_mem idstr mexports
                       in
                    let mincludes =
                      let uu____2991 =
                        FStar_Util.smap_try_find env.includes mname  in
                      match uu____2991 with
                      | FStar_Pervasives_Native.None  -> []
                      | FStar_Pervasives_Native.Some minc ->
                          FStar_ST.op_Bang minc
                       in
                    let look_into =
                      if not_shadowed
                      then
                        let uu____3071 = qual modul id1  in
                        find_in_module uu____3071
                      else Cont_ignore  in
                    (match look_into with
                     | Cont_ignore  -> aux (FStar_List.append mincludes q)
                     | uu____3075 -> look_into)
                 in
              aux [ns]
  
let (is_exported_id_field : exported_id_kind -> Prims.bool) =
  fun uu___86_3082  ->
    match uu___86_3082 with
    | Exported_id_field  -> true
    | uu____3083 -> false
  
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
                  let check_local_binding_id uu___87_3203 =
                    match uu___87_3203 with
                    | (id',uu____3205,uu____3206) ->
                        id'.FStar_Ident.idText = id1.FStar_Ident.idText
                     in
                  let check_rec_binding_id uu___88_3211 =
                    match uu___88_3211 with
                    | (id',uu____3213,uu____3214) ->
                        id'.FStar_Ident.idText = id1.FStar_Ident.idText
                     in
                  let curmod_ns =
                    let uu____3218 = current_module env  in
                    FStar_Ident.ids_of_lid uu____3218  in
                  let proc uu___89_3225 =
                    match uu___89_3225 with
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
                        let uu____3233 = FStar_Ident.lid_of_ids curmod_ns  in
                        find_in_module_with_includes Exported_id_field
                          (fun lid  ->
                             let id2 = lid.FStar_Ident.ident  in
                             find_in_record lid.FStar_Ident.ns id2 r k_record)
                          Cont_ignore env uu____3233 id1
                    | uu____3238 -> Cont_ignore  in
                  let rec aux uu___90_3247 =
                    match uu___90_3247 with
                    | a::q ->
                        let uu____3256 = proc a  in
                        option_of_cont (fun uu____3260  -> aux q) uu____3256
                    | [] ->
                        let uu____3261 = lookup_default_id Cont_fail id1  in
                        option_of_cont
                          (fun uu____3265  -> FStar_Pervasives_Native.None)
                          uu____3261
                     in
                  aux env.scope_mods
  
let found_local_binding :
  'Auu____3274 'Auu____3275 .
    FStar_Range.range ->
      ('Auu____3274,FStar_Syntax_Syntax.bv,'Auu____3275)
        FStar_Pervasives_Native.tuple3 ->
        (FStar_Syntax_Syntax.term,'Auu____3275)
          FStar_Pervasives_Native.tuple2
  =
  fun r  ->
    fun uu____3295  ->
      match uu____3295 with
      | (id',x,mut) -> let uu____3305 = bv_to_name x r  in (uu____3305, mut)
  
let find_in_module :
  'Auu____3316 .
    env ->
      FStar_Ident.lident ->
        (FStar_Ident.lident ->
           (FStar_Syntax_Syntax.sigelt,Prims.bool)
             FStar_Pervasives_Native.tuple2 -> 'Auu____3316)
          -> 'Auu____3316 -> 'Auu____3316
  =
  fun env  ->
    fun lid  ->
      fun k_global_def  ->
        fun k_not_found  ->
          let uu____3355 =
            FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str  in
          match uu____3355 with
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
      let uu____3395 = unmangleOpName id1  in
      match uu____3395 with
      | FStar_Pervasives_Native.Some f -> FStar_Pervasives_Native.Some f
      | uu____3421 ->
          try_lookup_id'' env id1 Exported_id_term_type
            (fun r  ->
               let uu____3435 = found_local_binding id1.FStar_Ident.idRange r
                  in
               Cont_ok uu____3435) (fun uu____3445  -> Cont_fail)
            (fun uu____3451  -> Cont_ignore)
            (fun i  ->
               find_in_module env i
                 (fun uu____3466  -> fun uu____3467  -> Cont_fail)
                 Cont_ignore)
            (fun uu____3482  -> fun uu____3483  -> Cont_fail)
  
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
            | FStar_Pervasives_Native.Some uu____3562 ->
                let lid = qualify env id1  in
                let uu____3564 =
                  FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str
                   in
                (match uu____3564 with
                 | FStar_Pervasives_Native.Some r ->
                     let uu____3588 = k_global_def lid r  in
                     FStar_Pervasives_Native.Some uu____3588
                 | FStar_Pervasives_Native.None  ->
                     FStar_Pervasives_Native.None)
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             in
          match find_in_monad with
          | FStar_Pervasives_Native.Some v1 -> v1
          | FStar_Pervasives_Native.None  ->
              let lid =
                let uu____3611 = current_module env  in qual uu____3611 id1
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
        let rec aux uu___91_3673 =
          match uu___91_3673 with
          | [] ->
              let uu____3678 = module_is_defined env lid  in
              if uu____3678
              then FStar_Pervasives_Native.Some lid
              else FStar_Pervasives_Native.None
          | (Open_module_or_namespace (ns,Open_namespace ))::q when honor_ns
              ->
              let new_lid =
                let uu____3687 =
                  let uu____3688 = FStar_Ident.path_of_lid ns  in
                  let uu____3691 = FStar_Ident.path_of_lid lid  in
                  FStar_List.append uu____3688 uu____3691  in
                let uu____3694 = FStar_Ident.range_of_lid lid  in
                FStar_Ident.lid_of_path uu____3687 uu____3694  in
              let uu____3695 = module_is_defined env new_lid  in
              if uu____3695
              then FStar_Pervasives_Native.Some new_lid
              else aux q
          | (Module_abbrev (name,modul))::uu____3701 when
              (nslen = (Prims.parse_int "0")) &&
                (name.FStar_Ident.idText =
                   (lid.FStar_Ident.ident).FStar_Ident.idText)
              -> FStar_Pervasives_Native.Some modul
          | uu____3708::q -> aux q  in
        aux env.scope_mods
  
let (fail_if_curmodule :
  env -> FStar_Ident.lident -> FStar_Ident.lident -> unit) =
  fun env  ->
    fun ns_original  ->
      fun ns_resolved  ->
        let uu____3727 =
          let uu____3728 = current_module env  in
          FStar_Ident.lid_equals ns_resolved uu____3728  in
        if uu____3727
        then
          let uu____3729 =
            FStar_Ident.lid_equals ns_resolved FStar_Parser_Const.prims_lid
             in
          (if uu____3729
           then ()
           else
             (let uu____3731 =
                let uu____3736 =
                  FStar_Util.format1
                    "Reference %s to current module is forbidden (see GitHub issue #451)"
                    ns_original.FStar_Ident.str
                   in
                (FStar_Errors.Fatal_ForbiddenReferenceToCurrentModule,
                  uu____3736)
                 in
              let uu____3737 = FStar_Ident.range_of_lid ns_original  in
              FStar_Errors.raise_error uu____3731 uu____3737))
        else ()
  
let (fail_if_qualified_by_curmodule : env -> FStar_Ident.lident -> unit) =
  fun env  ->
    fun lid  ->
      match lid.FStar_Ident.ns with
      | [] -> ()
      | uu____3749 ->
          let modul_orig = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          let uu____3753 = resolve_module_name env modul_orig true  in
          (match uu____3753 with
           | FStar_Pervasives_Native.Some modul_res ->
               fail_if_curmodule env modul_orig modul_res
           | uu____3757 -> ())
  
let (is_open : env -> FStar_Ident.lident -> open_kind -> Prims.bool) =
  fun env  ->
    fun lid  ->
      fun open_kind  ->
        FStar_List.existsb
          (fun uu___92_3778  ->
             match uu___92_3778 with
             | Open_module_or_namespace (ns,k) ->
                 (k = open_kind) && (FStar_Ident.lid_equals lid ns)
             | uu____3781 -> false) env.scope_mods
  
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
                 let uu____3898 = aux rev_ns_prefix ns_last_id  in
                 FStar_All.pipe_right uu____3898
                   (FStar_Util.map_option
                      (fun uu____3948  ->
                         match uu____3948 with
                         | (stripped_ids,rev_kept_ids) ->
                             (stripped_ids, (id1 :: rev_kept_ids)))))
           in
        let do_shorten env1 ids1 =
          match FStar_List.rev ids1 with
          | [] -> ([], [])
          | ns_last_id::ns_rev_prefix ->
              let uu____4016 = aux ns_rev_prefix ns_last_id  in
              (match uu____4016 with
               | FStar_Pervasives_Native.None  -> ([], ids1)
               | FStar_Pervasives_Native.Some (stripped_ids,rev_kept_ids) ->
                   (stripped_ids, (FStar_List.rev rev_kept_ids)))
           in
        if is_full_path
        then
          let uu____4077 =
            let uu____4080 = FStar_Ident.lid_of_ids ids  in
            resolve_module_name env uu____4080 true  in
          match uu____4077 with
          | FStar_Pervasives_Native.Some m when module_is_open env m ->
              (ids, [])
          | uu____4094 -> do_shorten env ids
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
                  | uu____4213::uu____4214 ->
                      let uu____4217 =
                        let uu____4220 =
                          let uu____4221 =
                            FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
                          let uu____4222 = FStar_Ident.range_of_lid lid  in
                          FStar_Ident.set_lid_range uu____4221 uu____4222  in
                        resolve_module_name env uu____4220 true  in
                      (match uu____4217 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some modul ->
                           let uu____4226 =
                             find_in_module_with_includes eikind f_module
                               Cont_fail env modul lid.FStar_Ident.ident
                              in
                           option_of_cont
                             (fun uu____4230  -> FStar_Pervasives_Native.None)
                             uu____4226)
                  | [] ->
                      try_lookup_id'' env lid.FStar_Ident.ident eikind
                        k_local_binding k_rec_binding k_record f_module
                        l_default
  
let cont_of_option :
  'a . 'a cont_t -> 'a FStar_Pervasives_Native.option -> 'a cont_t =
  fun k_none  ->
    fun uu___93_4253  ->
      match uu___93_4253 with
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
              let uu____4366 = k_global_def lid1 def  in
              cont_of_option k uu____4366  in
            let f_module lid' =
              let k = Cont_ignore  in
              find_in_module env lid' (k_global_def' k) k  in
            let l_default k i = lookup_default_id env i (k_global_def' k) k
               in
            resolve_in_open_namespaces'' env lid Exported_id_term_type
              (fun l  ->
                 let uu____4399 = k_local_binding l  in
                 cont_of_option Cont_fail uu____4399)
              (fun r  ->
                 let uu____4405 = k_rec_binding r  in
                 cont_of_option Cont_fail uu____4405)
              (fun uu____4409  -> Cont_ignore) f_module l_default
  
let (fv_qual_of_se :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option)
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____4419,uu____4420,uu____4421,l,uu____4423,uu____4424) ->
        let qopt =
          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
            (fun uu___94_4435  ->
               match uu___94_4435 with
               | FStar_Syntax_Syntax.RecordConstructor (uu____4438,fs) ->
                   FStar_Pervasives_Native.Some
                     (FStar_Syntax_Syntax.Record_ctor (l, fs))
               | uu____4450 -> FStar_Pervasives_Native.None)
           in
        (match qopt with
         | FStar_Pervasives_Native.None  ->
             FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor
         | x -> x)
    | FStar_Syntax_Syntax.Sig_declare_typ (uu____4456,uu____4457,uu____4458)
        -> FStar_Pervasives_Native.None
    | uu____4459 -> FStar_Pervasives_Native.None
  
let (lb_fv :
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Ident.lident -> FStar_Syntax_Syntax.fv)
  =
  fun lbs  ->
    fun lid  ->
      let uu____4474 =
        FStar_Util.find_map lbs
          (fun lb  ->
             let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
             let uu____4482 = FStar_Syntax_Syntax.fv_eq_lid fv lid  in
             if uu____4482
             then FStar_Pervasives_Native.Some fv
             else FStar_Pervasives_Native.None)
         in
      FStar_All.pipe_right uu____4474 FStar_Util.must
  
let (ns_of_lid_equals :
  FStar_Ident.lident -> FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    fun ns  ->
      (let uu____4500 =
         let uu____4501 = FStar_Ident.ids_of_lid ns  in
         FStar_List.length uu____4501  in
       (FStar_List.length lid.FStar_Ident.ns) = uu____4500) &&
        (let uu____4509 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
         FStar_Ident.lid_equals uu____4509 ns)
  
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
          let k_global_def source_lid uu___99_4549 =
            match uu___99_4549 with
            | (uu____4556,true ) when exclude_interf ->
                FStar_Pervasives_Native.None
            | (se,uu____4558) ->
                (match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_inductive_typ uu____4561 ->
                     let uu____4578 =
                       let uu____4579 =
                         let uu____4588 =
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.Delta_constant
                             FStar_Pervasives_Native.None
                            in
                         (uu____4588, false,
                           (se.FStar_Syntax_Syntax.sigattrs))
                          in
                       Term_name uu____4579  in
                     FStar_Pervasives_Native.Some uu____4578
                 | FStar_Syntax_Syntax.Sig_datacon uu____4591 ->
                     let uu____4606 =
                       let uu____4607 =
                         let uu____4616 =
                           let uu____4617 = fv_qual_of_se se  in
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.Delta_constant uu____4617
                            in
                         (uu____4616, false,
                           (se.FStar_Syntax_Syntax.sigattrs))
                          in
                       Term_name uu____4607  in
                     FStar_Pervasives_Native.Some uu____4606
                 | FStar_Syntax_Syntax.Sig_let ((uu____4622,lbs),uu____4624)
                     ->
                     let fv = lb_fv lbs source_lid  in
                     let uu____4640 =
                       let uu____4641 =
                         let uu____4650 =
                           FStar_Syntax_Syntax.fvar source_lid
                             fv.FStar_Syntax_Syntax.fv_delta
                             fv.FStar_Syntax_Syntax.fv_qual
                            in
                         (uu____4650, false,
                           (se.FStar_Syntax_Syntax.sigattrs))
                          in
                       Term_name uu____4641  in
                     FStar_Pervasives_Native.Some uu____4640
                 | FStar_Syntax_Syntax.Sig_declare_typ
                     (lid1,uu____4654,uu____4655) ->
                     let quals = se.FStar_Syntax_Syntax.sigquals  in
                     let uu____4659 =
                       any_val ||
                         (FStar_All.pipe_right quals
                            (FStar_Util.for_some
                               (fun uu___95_4663  ->
                                  match uu___95_4663 with
                                  | FStar_Syntax_Syntax.Assumption  -> true
                                  | uu____4664 -> false)))
                        in
                     if uu____4659
                     then
                       let lid2 =
                         let uu____4668 = FStar_Ident.range_of_lid source_lid
                            in
                         FStar_Ident.set_lid_range lid1 uu____4668  in
                       let dd =
                         let uu____4670 =
                           (FStar_Syntax_Util.is_primop_lid lid2) ||
                             (FStar_All.pipe_right quals
                                (FStar_Util.for_some
                                   (fun uu___96_4675  ->
                                      match uu___96_4675 with
                                      | FStar_Syntax_Syntax.Projector
                                          uu____4676 -> true
                                      | FStar_Syntax_Syntax.Discriminator
                                          uu____4681 -> true
                                      | uu____4682 -> false)))
                            in
                         if uu____4670
                         then FStar_Syntax_Syntax.Delta_equational
                         else FStar_Syntax_Syntax.Delta_constant  in
                       let dd1 =
                         let uu____4685 =
                           FStar_All.pipe_right quals
                             (FStar_Util.for_some
                                (fun uu___97_4689  ->
                                   match uu___97_4689 with
                                   | FStar_Syntax_Syntax.Abstract  -> true
                                   | uu____4690 -> false))
                            in
                         if uu____4685
                         then FStar_Syntax_Syntax.Delta_abstract dd
                         else dd  in
                       let uu____4692 =
                         FStar_Util.find_map quals
                           (fun uu___98_4697  ->
                              match uu___98_4697 with
                              | FStar_Syntax_Syntax.Reflectable refl_monad ->
                                  FStar_Pervasives_Native.Some refl_monad
                              | uu____4701 -> FStar_Pervasives_Native.None)
                          in
                       (match uu____4692 with
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
                        | uu____4712 ->
                            let uu____4715 =
                              let uu____4716 =
                                let uu____4725 =
                                  let uu____4726 = fv_qual_of_se se  in
                                  FStar_Syntax_Syntax.fvar lid2 dd1
                                    uu____4726
                                   in
                                (uu____4725, false,
                                  (se.FStar_Syntax_Syntax.sigattrs))
                                 in
                              Term_name uu____4716  in
                            FStar_Pervasives_Native.Some uu____4715)
                     else FStar_Pervasives_Native.None
                 | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
                     let uu____4733 =
                       let uu____4734 =
                         let uu____4739 =
                           let uu____4740 =
                             FStar_Ident.range_of_lid source_lid  in
                           FStar_Ident.set_lid_range
                             ne.FStar_Syntax_Syntax.mname uu____4740
                            in
                         (se, uu____4739)  in
                       Eff_name uu____4734  in
                     FStar_Pervasives_Native.Some uu____4733
                 | FStar_Syntax_Syntax.Sig_new_effect ne ->
                     let uu____4742 =
                       let uu____4743 =
                         let uu____4748 =
                           let uu____4749 =
                             FStar_Ident.range_of_lid source_lid  in
                           FStar_Ident.set_lid_range
                             ne.FStar_Syntax_Syntax.mname uu____4749
                            in
                         (se, uu____4748)  in
                       Eff_name uu____4743  in
                     FStar_Pervasives_Native.Some uu____4742
                 | FStar_Syntax_Syntax.Sig_effect_abbrev uu____4750 ->
                     FStar_Pervasives_Native.Some (Eff_name (se, source_lid))
                 | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
                     let uu____4769 =
                       let uu____4770 =
                         let uu____4779 =
                           FStar_Syntax_Syntax.fvar source_lid
                             (FStar_Syntax_Syntax.Delta_defined_at_level
                                (Prims.parse_int "1"))
                             FStar_Pervasives_Native.None
                            in
                         (uu____4779, false, [])  in
                       Term_name uu____4770  in
                     FStar_Pervasives_Native.Some uu____4769
                 | uu____4782 -> FStar_Pervasives_Native.None)
             in
          let k_local_binding r =
            let uu____4802 =
              let uu____4807 = FStar_Ident.range_of_lid lid  in
              found_local_binding uu____4807 r  in
            match uu____4802 with
            | (t,mut) ->
                FStar_Pervasives_Native.Some (Term_name (t, mut, []))
             in
          let k_rec_binding uu____4826 =
            match uu____4826 with
            | (id1,l,dd) ->
                let uu____4838 =
                  let uu____4839 =
                    let uu____4848 =
                      let uu____4849 =
                        let uu____4850 = FStar_Ident.range_of_lid lid  in
                        FStar_Ident.set_lid_range l uu____4850  in
                      FStar_Syntax_Syntax.fvar uu____4849 dd
                        FStar_Pervasives_Native.None
                       in
                    (uu____4848, false, [])  in
                  Term_name uu____4839  in
                FStar_Pervasives_Native.Some uu____4838
             in
          let found_unmangled =
            match lid.FStar_Ident.ns with
            | [] ->
                let uu____4858 = unmangleOpName lid.FStar_Ident.ident  in
                (match uu____4858 with
                 | FStar_Pervasives_Native.Some (t,mut) ->
                     FStar_Pervasives_Native.Some (Term_name (t, mut, []))
                 | uu____4875 -> FStar_Pervasives_Native.None)
            | uu____4882 -> FStar_Pervasives_Native.None  in
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
        let uu____4917 = try_lookup_name true exclude_interf env lid  in
        match uu____4917 with
        | FStar_Pervasives_Native.Some (Eff_name (o,l)) ->
            FStar_Pervasives_Native.Some (o, l)
        | uu____4932 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____4951 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____4951 with
      | FStar_Pervasives_Native.Some (o,l1) ->
          FStar_Pervasives_Native.Some l1
      | uu____4966 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_name_and_attributes :
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident,FStar_Syntax_Syntax.cflags Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____4991 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____4991 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____5007;
             FStar_Syntax_Syntax.sigquals = uu____5008;
             FStar_Syntax_Syntax.sigmeta = uu____5009;
             FStar_Syntax_Syntax.sigattrs = uu____5010;_},l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____5029;
             FStar_Syntax_Syntax.sigquals = uu____5030;
             FStar_Syntax_Syntax.sigmeta = uu____5031;
             FStar_Syntax_Syntax.sigattrs = uu____5032;_},l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (uu____5050,uu____5051,uu____5052,uu____5053,cattributes);
             FStar_Syntax_Syntax.sigrng = uu____5055;
             FStar_Syntax_Syntax.sigquals = uu____5056;
             FStar_Syntax_Syntax.sigmeta = uu____5057;
             FStar_Syntax_Syntax.sigattrs = uu____5058;_},l1)
          -> FStar_Pervasives_Native.Some (l1, cattributes)
      | uu____5080 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_defn :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.eff_decl FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____5105 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____5105 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____5115;
             FStar_Syntax_Syntax.sigquals = uu____5116;
             FStar_Syntax_Syntax.sigmeta = uu____5117;
             FStar_Syntax_Syntax.sigattrs = uu____5118;_},uu____5119)
          -> FStar_Pervasives_Native.Some ne
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____5129;
             FStar_Syntax_Syntax.sigquals = uu____5130;
             FStar_Syntax_Syntax.sigmeta = uu____5131;
             FStar_Syntax_Syntax.sigattrs = uu____5132;_},uu____5133)
          -> FStar_Pervasives_Native.Some ne
      | uu____5142 -> FStar_Pervasives_Native.None
  
let (is_effect_name : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____5159 = try_lookup_effect_name env lid  in
      match uu____5159 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____5162 -> true
  
let (try_lookup_root_effect_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____5175 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____5175 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (l',uu____5185,uu____5186,uu____5187,uu____5188);
             FStar_Syntax_Syntax.sigrng = uu____5189;
             FStar_Syntax_Syntax.sigquals = uu____5190;
             FStar_Syntax_Syntax.sigmeta = uu____5191;
             FStar_Syntax_Syntax.sigattrs = uu____5192;_},uu____5193)
          ->
          let rec aux new_name =
            let uu____5213 =
              FStar_Util.smap_try_find (sigmap env) new_name.FStar_Ident.str
               in
            match uu____5213 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (s,uu____5231) ->
                (match s.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
                     let uu____5239 =
                       let uu____5240 = FStar_Ident.range_of_lid l  in
                       FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname
                         uu____5240
                        in
                     FStar_Pervasives_Native.Some uu____5239
                 | FStar_Syntax_Syntax.Sig_new_effect ne ->
                     let uu____5242 =
                       let uu____5243 = FStar_Ident.range_of_lid l  in
                       FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname
                         uu____5243
                        in
                     FStar_Pervasives_Native.Some uu____5242
                 | FStar_Syntax_Syntax.Sig_effect_abbrev
                     (uu____5244,uu____5245,uu____5246,cmp,uu____5248) ->
                     let l'' = FStar_Syntax_Util.comp_effect_name cmp  in
                     aux l''
                 | uu____5254 -> FStar_Pervasives_Native.None)
             in
          aux l'
      | FStar_Pervasives_Native.Some (uu____5255,l') ->
          FStar_Pervasives_Native.Some l'
      | uu____5261 -> FStar_Pervasives_Native.None
  
let (lookup_letbinding_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___100_5296 =
        match uu___100_5296 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____5305,uu____5306,uu____5307);
             FStar_Syntax_Syntax.sigrng = uu____5308;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____5310;
             FStar_Syntax_Syntax.sigattrs = uu____5311;_},uu____5312)
            -> FStar_Pervasives_Native.Some quals
        | uu____5319 -> FStar_Pervasives_Native.None  in
      let uu____5326 =
        resolve_in_open_namespaces' env lid
          (fun uu____5334  -> FStar_Pervasives_Native.None)
          (fun uu____5338  -> FStar_Pervasives_Native.None) k_global_def
         in
      match uu____5326 with
      | FStar_Pervasives_Native.Some quals -> quals
      | uu____5348 -> []
  
let (try_lookup_module :
  env ->
    FStar_Ident.path ->
      FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun path  ->
      let uu____5365 =
        FStar_List.tryFind
          (fun uu____5380  ->
             match uu____5380 with
             | (mlid,modul) ->
                 let uu____5387 = FStar_Ident.path_of_lid mlid  in
                 uu____5387 = path) env.modules
         in
      match uu____5365 with
      | FStar_Pervasives_Native.Some (uu____5390,modul) ->
          FStar_Pervasives_Native.Some modul
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (try_lookup_let :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___101_5426 =
        match uu___101_5426 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               ((uu____5433,lbs),uu____5435);
             FStar_Syntax_Syntax.sigrng = uu____5436;
             FStar_Syntax_Syntax.sigquals = uu____5437;
             FStar_Syntax_Syntax.sigmeta = uu____5438;
             FStar_Syntax_Syntax.sigattrs = uu____5439;_},uu____5440)
            ->
            let fv = lb_fv lbs lid1  in
            let uu____5460 =
              FStar_Syntax_Syntax.fvar lid1 fv.FStar_Syntax_Syntax.fv_delta
                fv.FStar_Syntax_Syntax.fv_qual
               in
            FStar_Pervasives_Native.Some uu____5460
        | uu____5461 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____5467  -> FStar_Pervasives_Native.None)
        (fun uu____5469  -> FStar_Pervasives_Native.None) k_global_def
  
let (try_lookup_definition :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___102_5498 =
        match uu___102_5498 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               (lbs,uu____5508);
             FStar_Syntax_Syntax.sigrng = uu____5509;
             FStar_Syntax_Syntax.sigquals = uu____5510;
             FStar_Syntax_Syntax.sigmeta = uu____5511;
             FStar_Syntax_Syntax.sigattrs = uu____5512;_},uu____5513)
            ->
            FStar_Util.find_map (FStar_Pervasives_Native.snd lbs)
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inr fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv lid1 ->
                     FStar_Pervasives_Native.Some
                       (lb.FStar_Syntax_Syntax.lbdef)
                 | uu____5536 -> FStar_Pervasives_Native.None)
        | uu____5543 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____5553  -> FStar_Pervasives_Native.None)
        (fun uu____5557  -> FStar_Pervasives_Native.None) k_global_def
  
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
          let uu____5614 = try_lookup_name any_val exclude_interface env lid
             in
          match uu____5614 with
          | FStar_Pervasives_Native.Some (Term_name (e,mut,attrs)) ->
              FStar_Pervasives_Native.Some (e, mut, attrs)
          | uu____5644 -> FStar_Pervasives_Native.None
  
let (drop_attributes :
  (FStar_Syntax_Syntax.term,Prims.bool,FStar_Syntax_Syntax.attribute
                                         Prims.list)
    FStar_Pervasives_Native.tuple3 FStar_Pervasives_Native.option ->
    (FStar_Syntax_Syntax.term,Prims.bool) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option)
  =
  fun x  ->
    match x with
    | FStar_Pervasives_Native.Some (t,mut,uu____5700) ->
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
      let uu____5775 = try_lookup_lid_with_attributes env l  in
      FStar_All.pipe_right uu____5775 drop_attributes
  
let (resolve_to_fully_qualified_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____5814 = try_lookup_lid env l  in
      match uu____5814 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (e,uu____5828) ->
          let uu____5833 =
            let uu____5834 = FStar_Syntax_Subst.compress e  in
            uu____5834.FStar_Syntax_Syntax.n  in
          (match uu____5833 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               FStar_Pervasives_Native.Some
                 ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
           | uu____5840 -> FStar_Pervasives_Native.None)
  
let (shorten_lid' : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____5851 = shorten_module_path env lid.FStar_Ident.ns true  in
      match uu____5851 with
      | (uu____5860,short) ->
          FStar_Ident.lid_of_ns_and_id short lid.FStar_Ident.ident
  
let (shorten_lid : env -> FStar_Ident.lid -> FStar_Ident.lid) =
  fun env  ->
    fun lid  ->
      match env.curmodule with
      | FStar_Pervasives_Native.None  -> shorten_lid' env lid
      | uu____5880 ->
          let lid_without_ns =
            FStar_Ident.lid_of_ns_and_id [] lid.FStar_Ident.ident  in
          let uu____5884 = resolve_to_fully_qualified_name env lid_without_ns
             in
          (match uu____5884 with
           | FStar_Pervasives_Native.Some lid' when
               lid'.FStar_Ident.str = lid.FStar_Ident.str -> lid_without_ns
           | uu____5888 -> shorten_lid' env lid)
  
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
        let uu___123_5922 = env  in
        {
          curmodule = (uu___123_5922.curmodule);
          curmonad = (uu___123_5922.curmonad);
          modules = (uu___123_5922.modules);
          scope_mods = [];
          exported_ids = empty_exported_id_smap;
          trans_exported_ids = (uu___123_5922.trans_exported_ids);
          includes = empty_include_smap;
          sigaccum = (uu___123_5922.sigaccum);
          sigmap = (uu___123_5922.sigmap);
          iface = (uu___123_5922.iface);
          admitted_iface = (uu___123_5922.admitted_iface);
          expect_typ = (uu___123_5922.expect_typ);
          docs = (uu___123_5922.docs);
          remaining_iface_decls = (uu___123_5922.remaining_iface_decls);
          syntax_only = (uu___123_5922.syntax_only);
          ds_hooks = (uu___123_5922.ds_hooks)
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
      let uu____5945 = try_lookup_lid_with_attributes_no_resolve env l  in
      FStar_All.pipe_right uu____5945 drop_attributes
  
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
      let k_global_def lid1 uu___104_6010 =
        match uu___104_6010 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____6017,uu____6018,uu____6019);
             FStar_Syntax_Syntax.sigrng = uu____6020;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____6022;
             FStar_Syntax_Syntax.sigattrs = uu____6023;_},uu____6024)
            ->
            let uu____6029 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___103_6033  ->
                      match uu___103_6033 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | uu____6034 -> false))
               in
            if uu____6029
            then
              let uu____6037 =
                FStar_Syntax_Syntax.lid_as_fv lid1
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Pervasives_Native.Some uu____6037
            else FStar_Pervasives_Native.None
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
               uu____6039;
             FStar_Syntax_Syntax.sigrng = uu____6040;
             FStar_Syntax_Syntax.sigquals = uu____6041;
             FStar_Syntax_Syntax.sigmeta = uu____6042;
             FStar_Syntax_Syntax.sigattrs = uu____6043;_},uu____6044)
            ->
            let uu____6063 =
              FStar_Syntax_Syntax.lid_as_fv lid1
                FStar_Syntax_Syntax.Delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
               in
            FStar_Pervasives_Native.Some uu____6063
        | uu____6064 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____6070  -> FStar_Pervasives_Native.None)
        (fun uu____6072  -> FStar_Pervasives_Native.None) k_global_def
  
let (find_all_datacons :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___105_6103 =
        match uu___105_6103 with
        | ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_inductive_typ
               (uu____6112,uu____6113,uu____6114,uu____6115,datas,uu____6117);
             FStar_Syntax_Syntax.sigrng = uu____6118;
             FStar_Syntax_Syntax.sigquals = uu____6119;
             FStar_Syntax_Syntax.sigmeta = uu____6120;
             FStar_Syntax_Syntax.sigattrs = uu____6121;_},uu____6122)
            -> FStar_Pervasives_Native.Some datas
        | uu____6137 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____6147  -> FStar_Pervasives_Native.None)
        (fun uu____6151  -> FStar_Pervasives_Native.None) k_global_def
  
let (record_cache_aux_with_filter :
  ((unit -> unit,unit -> unit,unit -> record_or_dc Prims.list,record_or_dc ->
                                                                unit)
     FStar_Pervasives_Native.tuple4,unit -> unit)
    FStar_Pervasives_Native.tuple2)
  =
  let record_cache = FStar_Util.mk_ref [[]]  in
  let push1 uu____6202 =
    let uu____6203 =
      let uu____6208 =
        let uu____6211 = FStar_ST.op_Bang record_cache  in
        FStar_List.hd uu____6211  in
      let uu____6271 = FStar_ST.op_Bang record_cache  in uu____6208 ::
        uu____6271
       in
    FStar_ST.op_Colon_Equals record_cache uu____6203  in
  let pop1 uu____6388 =
    let uu____6389 =
      let uu____6394 = FStar_ST.op_Bang record_cache  in
      FStar_List.tl uu____6394  in
    FStar_ST.op_Colon_Equals record_cache uu____6389  in
  let peek1 uu____6513 =
    let uu____6514 = FStar_ST.op_Bang record_cache  in
    FStar_List.hd uu____6514  in
  let insert r =
    let uu____6579 =
      let uu____6584 = let uu____6587 = peek1 ()  in r :: uu____6587  in
      let uu____6590 =
        let uu____6595 = FStar_ST.op_Bang record_cache  in
        FStar_List.tl uu____6595  in
      uu____6584 :: uu____6590  in
    FStar_ST.op_Colon_Equals record_cache uu____6579  in
  let filter1 uu____6714 =
    let rc = peek1 ()  in
    let filtered =
      FStar_List.filter
        (fun r  -> Prims.op_Negation r.is_private_or_abstract) rc
       in
    let uu____6723 =
      let uu____6728 =
        let uu____6733 = FStar_ST.op_Bang record_cache  in
        FStar_List.tl uu____6733  in
      filtered :: uu____6728  in
    FStar_ST.op_Colon_Equals record_cache uu____6723  in
  let aux = (push1, pop1, peek1, insert)  in (aux, filter1) 
let (record_cache_aux :
  (unit -> unit,unit -> unit,unit -> record_or_dc Prims.list,record_or_dc ->
                                                               unit)
    FStar_Pervasives_Native.tuple4)
  =
  let uu____6932 = record_cache_aux_with_filter  in
  match uu____6932 with | (aux,uu____6985) -> aux 
let (filter_record_cache : unit -> unit) =
  let uu____7040 = record_cache_aux_with_filter  in
  match uu____7040 with | (uu____7073,filter1) -> filter1 
let (push_record_cache : unit -> unit) =
  let uu____7129 = record_cache_aux  in
  match uu____7129 with | (push1,uu____7156,uu____7157,uu____7158) -> push1 
let (pop_record_cache : unit -> unit) =
  let uu____7191 = record_cache_aux  in
  match uu____7191 with | (uu____7217,pop1,uu____7219,uu____7220) -> pop1 
let (peek_record_cache : unit -> record_or_dc Prims.list) =
  let uu____7255 = record_cache_aux  in
  match uu____7255 with | (uu____7283,uu____7284,peek1,uu____7286) -> peek1 
let (insert_record_cache : record_or_dc -> unit) =
  let uu____7319 = record_cache_aux  in
  match uu____7319 with | (uu____7345,uu____7346,uu____7347,insert) -> insert 
let (extract_record :
  env ->
    scope_mod Prims.list FStar_ST.ref -> FStar_Syntax_Syntax.sigelt -> unit)
  =
  fun e  ->
    fun new_globs  ->
      fun se  ->
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_bundle (sigs,uu____7423) ->
            let is_record =
              FStar_Util.for_some
                (fun uu___106_7440  ->
                   match uu___106_7440 with
                   | FStar_Syntax_Syntax.RecordType uu____7441 -> true
                   | FStar_Syntax_Syntax.RecordConstructor uu____7450 -> true
                   | uu____7459 -> false)
               in
            let find_dc dc =
              FStar_All.pipe_right sigs
                (FStar_Util.find_opt
                   (fun uu___107_7482  ->
                      match uu___107_7482 with
                      | {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_datacon
                            (lid,uu____7484,uu____7485,uu____7486,uu____7487,uu____7488);
                          FStar_Syntax_Syntax.sigrng = uu____7489;
                          FStar_Syntax_Syntax.sigquals = uu____7490;
                          FStar_Syntax_Syntax.sigmeta = uu____7491;
                          FStar_Syntax_Syntax.sigattrs = uu____7492;_} ->
                          FStar_Ident.lid_equals dc lid
                      | uu____7501 -> false))
               in
            FStar_All.pipe_right sigs
              (FStar_List.iter
                 (fun uu___108_7536  ->
                    match uu___108_7536 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ
                          (typename,univs1,parms,uu____7540,uu____7541,dc::[]);
                        FStar_Syntax_Syntax.sigrng = uu____7543;
                        FStar_Syntax_Syntax.sigquals = typename_quals;
                        FStar_Syntax_Syntax.sigmeta = uu____7545;
                        FStar_Syntax_Syntax.sigattrs = uu____7546;_} ->
                        let uu____7557 =
                          let uu____7558 = find_dc dc  in
                          FStar_All.pipe_left FStar_Util.must uu____7558  in
                        (match uu____7557 with
                         | {
                             FStar_Syntax_Syntax.sigel =
                               FStar_Syntax_Syntax.Sig_datacon
                               (constrname,uu____7564,t,uu____7566,uu____7567,uu____7568);
                             FStar_Syntax_Syntax.sigrng = uu____7569;
                             FStar_Syntax_Syntax.sigquals = uu____7570;
                             FStar_Syntax_Syntax.sigmeta = uu____7571;
                             FStar_Syntax_Syntax.sigattrs = uu____7572;_} ->
                             let uu____7581 =
                               FStar_Syntax_Util.arrow_formals t  in
                             (match uu____7581 with
                              | (formals,uu____7595) ->
                                  let is_rec = is_record typename_quals  in
                                  let formals' =
                                    FStar_All.pipe_right formals
                                      (FStar_List.collect
                                         (fun uu____7644  ->
                                            match uu____7644 with
                                            | (x,q) ->
                                                let uu____7657 =
                                                  (FStar_Syntax_Syntax.is_null_bv
                                                     x)
                                                    ||
                                                    (is_rec &&
                                                       (FStar_Syntax_Syntax.is_implicit
                                                          q))
                                                   in
                                                if uu____7657
                                                then []
                                                else [(x, q)]))
                                     in
                                  let fields' =
                                    FStar_All.pipe_right formals'
                                      (FStar_List.map
                                         (fun uu____7714  ->
                                            match uu____7714 with
                                            | (x,q) ->
                                                let uu____7727 =
                                                  if is_rec
                                                  then
                                                    FStar_Syntax_Util.unmangle_field_name
                                                      x.FStar_Syntax_Syntax.ppname
                                                  else
                                                    x.FStar_Syntax_Syntax.ppname
                                                   in
                                                (uu____7727,
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
                                  let uu____7741 =
                                    let uu____7742 =
                                      let uu____7745 =
                                        FStar_ST.op_Bang new_globs  in
                                      (Record_or_dc record) :: uu____7745  in
                                    FStar_ST.op_Colon_Equals new_globs
                                      uu____7742
                                     in
                                  (match uu____7741 with
                                   | () ->
                                       let uu____7846 =
                                         let add_field uu____7857 =
                                           match uu____7857 with
                                           | (id1,uu____7865) ->
                                               let modul =
                                                 let uu____7871 =
                                                   FStar_Ident.lid_of_ids
                                                     constrname.FStar_Ident.ns
                                                    in
                                                 uu____7871.FStar_Ident.str
                                                  in
                                               let uu____7872 =
                                                 get_exported_id_set e modul
                                                  in
                                               (match uu____7872 with
                                                | FStar_Pervasives_Native.Some
                                                    my_ex ->
                                                    let my_exported_ids =
                                                      my_ex Exported_id_field
                                                       in
                                                    let uu____7905 =
                                                      let uu____7906 =
                                                        let uu____7907 =
                                                          FStar_ST.op_Bang
                                                            my_exported_ids
                                                           in
                                                        FStar_Util.set_add
                                                          id1.FStar_Ident.idText
                                                          uu____7907
                                                         in
                                                      FStar_ST.op_Colon_Equals
                                                        my_exported_ids
                                                        uu____7906
                                                       in
                                                    (match uu____7905 with
                                                     | () ->
                                                         let projname =
                                                           let uu____8001 =
                                                             let uu____8002 =
                                                               FStar_Syntax_Util.mk_field_projector_name_from_ident
                                                                 constrname
                                                                 id1
                                                                in
                                                             uu____8002.FStar_Ident.ident
                                                              in
                                                           uu____8001.FStar_Ident.idText
                                                            in
                                                         let uu____8003 =
                                                           let uu____8004 =
                                                             let uu____8005 =
                                                               FStar_ST.op_Bang
                                                                 my_exported_ids
                                                                in
                                                             FStar_Util.set_add
                                                               projname
                                                               uu____8005
                                                              in
                                                           FStar_ST.op_Colon_Equals
                                                             my_exported_ids
                                                             uu____8004
                                                            in
                                                         ())
                                                | FStar_Pervasives_Native.None
                                                     -> ())
                                            in
                                         FStar_List.iter add_field fields'
                                          in
                                       (match uu____7846 with
                                        | () -> insert_record_cache record)))
                         | uu____8109 -> ())
                    | uu____8110 -> ()))
        | uu____8111 -> ()
  
let (try_lookup_record_or_dc_by_field_name :
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option) =
  fun env  ->
    fun fieldname  ->
      let find_in_cache fieldname1 =
        let uu____8131 =
          ((fieldname1.FStar_Ident.ns), (fieldname1.FStar_Ident.ident))  in
        match uu____8131 with
        | (ns,id1) ->
            let uu____8148 = peek_record_cache ()  in
            FStar_Util.find_map uu____8148
              (fun record  ->
                 let uu____8154 =
                   find_in_record ns id1 record (fun r  -> Cont_ok r)  in
                 option_of_cont
                   (fun uu____8160  -> FStar_Pervasives_Native.None)
                   uu____8154)
         in
      resolve_in_open_namespaces'' env fieldname Exported_id_field
        (fun uu____8162  -> Cont_ignore) (fun uu____8164  -> Cont_ignore)
        (fun r  -> Cont_ok r)
        (fun fn  ->
           let uu____8170 = find_in_cache fn  in
           cont_of_option Cont_ignore uu____8170)
        (fun k  -> fun uu____8176  -> k)
  
let (try_lookup_record_by_field_name :
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option) =
  fun env  ->
    fun fieldname  ->
      let uu____8191 = try_lookup_record_or_dc_by_field_name env fieldname
         in
      match uu____8191 with
      | FStar_Pervasives_Native.Some r when r.is_record ->
          FStar_Pervasives_Native.Some r
      | uu____8197 -> FStar_Pervasives_Native.None
  
let (belongs_to_record :
  env -> FStar_Ident.lident -> record_or_dc -> Prims.bool) =
  fun env  ->
    fun lid  ->
      fun record  ->
        let uu____8215 = try_lookup_record_by_field_name env lid  in
        match uu____8215 with
        | FStar_Pervasives_Native.Some record' when
            let uu____8219 =
              let uu____8220 =
                FStar_Ident.path_of_ns (record.typename).FStar_Ident.ns  in
              FStar_Ident.text_of_path uu____8220  in
            let uu____8221 =
              let uu____8222 =
                FStar_Ident.path_of_ns (record'.typename).FStar_Ident.ns  in
              FStar_Ident.text_of_path uu____8222  in
            uu____8219 = uu____8221 ->
            let uu____8223 =
              find_in_record (record.typename).FStar_Ident.ns
                lid.FStar_Ident.ident record (fun uu____8227  -> Cont_ok ())
               in
            (match uu____8223 with
             | Cont_ok uu____8228 -> true
             | uu____8229 -> false)
        | uu____8232 -> false
  
let (try_lookup_dc_by_field_name :
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident,Prims.bool) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun fieldname  ->
      let uu____8251 = try_lookup_record_or_dc_by_field_name env fieldname
         in
      match uu____8251 with
      | FStar_Pervasives_Native.Some r ->
          let uu____8261 =
            let uu____8266 =
              let uu____8267 =
                FStar_Ident.lid_of_ids
                  (FStar_List.append (r.typename).FStar_Ident.ns
                     [r.constrname])
                 in
              let uu____8268 = FStar_Ident.range_of_lid fieldname  in
              FStar_Ident.set_lid_range uu____8267 uu____8268  in
            (uu____8266, (r.is_record))  in
          FStar_Pervasives_Native.Some uu____8261
      | uu____8273 -> FStar_Pervasives_Native.None
  
let (string_set_ref_new : unit -> Prims.string FStar_Util.set FStar_ST.ref) =
  fun uu____8299  ->
    let uu____8300 = FStar_Util.new_set FStar_Util.compare  in
    FStar_Util.mk_ref uu____8300
  
let (exported_id_set_new :
  unit -> exported_id_kind -> Prims.string FStar_Util.set FStar_ST.ref) =
  fun uu____8327  ->
    let term_type_set = string_set_ref_new ()  in
    let field_set = string_set_ref_new ()  in
    fun uu___109_8338  ->
      match uu___109_8338 with
      | Exported_id_term_type  -> term_type_set
      | Exported_id_field  -> field_set
  
let (unique :
  Prims.bool -> Prims.bool -> env -> FStar_Ident.lident -> Prims.bool) =
  fun any_val  ->
    fun exclude_interface  ->
      fun env  ->
        fun lid  ->
          let filter_scope_mods uu___110_8389 =
            match uu___110_8389 with
            | Rec_binding uu____8390 -> true
            | uu____8391 -> false  in
          let this_env =
            let uu___124_8393 = env  in
            let uu____8394 =
              FStar_List.filter filter_scope_mods env.scope_mods  in
            {
              curmodule = (uu___124_8393.curmodule);
              curmonad = (uu___124_8393.curmonad);
              modules = (uu___124_8393.modules);
              scope_mods = uu____8394;
              exported_ids = empty_exported_id_smap;
              trans_exported_ids = (uu___124_8393.trans_exported_ids);
              includes = empty_include_smap;
              sigaccum = (uu___124_8393.sigaccum);
              sigmap = (uu___124_8393.sigmap);
              iface = (uu___124_8393.iface);
              admitted_iface = (uu___124_8393.admitted_iface);
              expect_typ = (uu___124_8393.expect_typ);
              docs = (uu___124_8393.docs);
              remaining_iface_decls = (uu___124_8393.remaining_iface_decls);
              syntax_only = (uu___124_8393.syntax_only);
              ds_hooks = (uu___124_8393.ds_hooks)
            }  in
          let uu____8397 =
            try_lookup_lid' any_val exclude_interface this_env lid  in
          match uu____8397 with
          | FStar_Pervasives_Native.None  -> true
          | FStar_Pervasives_Native.Some uu____8416 -> false
  
let (push_scope_mod : env -> scope_mod -> env) =
  fun env  ->
    fun scope_mod  ->
      let uu___125_8443 = env  in
      {
        curmodule = (uu___125_8443.curmodule);
        curmonad = (uu___125_8443.curmonad);
        modules = (uu___125_8443.modules);
        scope_mods = (scope_mod :: (env.scope_mods));
        exported_ids = (uu___125_8443.exported_ids);
        trans_exported_ids = (uu___125_8443.trans_exported_ids);
        includes = (uu___125_8443.includes);
        sigaccum = (uu___125_8443.sigaccum);
        sigmap = (uu___125_8443.sigmap);
        iface = (uu___125_8443.iface);
        admitted_iface = (uu___125_8443.admitted_iface);
        expect_typ = (uu___125_8443.expect_typ);
        docs = (uu___125_8443.docs);
        remaining_iface_decls = (uu___125_8443.remaining_iface_decls);
        syntax_only = (uu___125_8443.syntax_only);
        ds_hooks = (uu___125_8443.ds_hooks)
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
        let uu____8508 =
          (unique false true env l) || (FStar_Options.interactive ())  in
        if uu____8508
        then push_scope_mod env (Rec_binding (x, l, dd))
        else
          (let uu____8510 = FStar_Ident.range_of_lid l  in
           FStar_Errors.raise_error
             (FStar_Errors.Fatal_DuplicateTopLevelNames,
               (Prims.strcat "Duplicate top-level names " l.FStar_Ident.str))
             uu____8510)
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let err l =
        let sopt = FStar_Util.smap_try_find (sigmap env) l.FStar_Ident.str
           in
        let r =
          match sopt with
          | FStar_Pervasives_Native.Some (se,uu____8539) ->
              let uu____8544 =
                FStar_Util.find_opt (FStar_Ident.lid_equals l)
                  (FStar_Syntax_Util.lids_of_sigelt se)
                 in
              (match uu____8544 with
               | FStar_Pervasives_Native.Some l1 ->
                   let uu____8548 = FStar_Ident.range_of_lid l1  in
                   FStar_All.pipe_left FStar_Range.string_of_range uu____8548
               | FStar_Pervasives_Native.None  -> "<unknown>")
          | FStar_Pervasives_Native.None  -> "<unknown>"  in
        let uu____8553 =
          let uu____8558 =
            let uu____8559 = FStar_Ident.text_of_lid l  in
            FStar_Util.format2
              "Duplicate top-level names [%s]; previously declared at %s"
              uu____8559 r
             in
          (FStar_Errors.Fatal_DuplicateTopLevelNames, uu____8558)  in
        let uu____8560 = FStar_Ident.range_of_lid l  in
        FStar_Errors.raise_error uu____8553 uu____8560  in
      let globals = FStar_Util.mk_ref env.scope_mods  in
      let env1 =
        let uu____8569 =
          match s.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let uu____8578 -> (false, true)
          | FStar_Syntax_Syntax.Sig_bundle uu____8585 -> (false, true)
          | uu____8594 -> (false, false)  in
        match uu____8569 with
        | (any_val,exclude_interface) ->
            let lids = FStar_Syntax_Util.lids_of_sigelt s  in
            let uu____8600 =
              FStar_Util.find_map lids
                (fun l  ->
                   let uu____8606 =
                     let uu____8607 = unique any_val exclude_interface env l
                        in
                     Prims.op_Negation uu____8607  in
                   if uu____8606
                   then FStar_Pervasives_Native.Some l
                   else FStar_Pervasives_Native.None)
               in
            (match uu____8600 with
             | FStar_Pervasives_Native.Some l -> err l
             | uu____8612 ->
                 let uu____8615 = extract_record env globals s  in
                 let uu___126_8638 = env  in
                 {
                   curmodule = (uu___126_8638.curmodule);
                   curmonad = (uu___126_8638.curmonad);
                   modules = (uu___126_8638.modules);
                   scope_mods = (uu___126_8638.scope_mods);
                   exported_ids = (uu___126_8638.exported_ids);
                   trans_exported_ids = (uu___126_8638.trans_exported_ids);
                   includes = (uu___126_8638.includes);
                   sigaccum = (s :: (env.sigaccum));
                   sigmap = (uu___126_8638.sigmap);
                   iface = (uu___126_8638.iface);
                   admitted_iface = (uu___126_8638.admitted_iface);
                   expect_typ = (uu___126_8638.expect_typ);
                   docs = (uu___126_8638.docs);
                   remaining_iface_decls =
                     (uu___126_8638.remaining_iface_decls);
                   syntax_only = (uu___126_8638.syntax_only);
                   ds_hooks = (uu___126_8638.ds_hooks)
                 })
         in
      let env2 =
        let uu___127_8640 = env1  in
        let uu____8641 = FStar_ST.op_Bang globals  in
        {
          curmodule = (uu___127_8640.curmodule);
          curmonad = (uu___127_8640.curmonad);
          modules = (uu___127_8640.modules);
          scope_mods = uu____8641;
          exported_ids = (uu___127_8640.exported_ids);
          trans_exported_ids = (uu___127_8640.trans_exported_ids);
          includes = (uu___127_8640.includes);
          sigaccum = (uu___127_8640.sigaccum);
          sigmap = (uu___127_8640.sigmap);
          iface = (uu___127_8640.iface);
          admitted_iface = (uu___127_8640.admitted_iface);
          expect_typ = (uu___127_8640.expect_typ);
          docs = (uu___127_8640.docs);
          remaining_iface_decls = (uu___127_8640.remaining_iface_decls);
          syntax_only = (uu___127_8640.syntax_only);
          ds_hooks = (uu___127_8640.ds_hooks)
        }  in
      let uu____8693 =
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_bundle (ses,uu____8719) ->
            let uu____8728 =
              FStar_List.map
                (fun se  -> ((FStar_Syntax_Util.lids_of_sigelt se), se)) ses
               in
            (env2, uu____8728)
        | uu____8755 -> (env2, [((FStar_Syntax_Util.lids_of_sigelt s), s)])
         in
      match uu____8693 with
      | (env3,lss) ->
          let uu____8796 =
            FStar_All.pipe_right lss
              (FStar_List.iter
                 (fun uu____8814  ->
                    match uu____8814 with
                    | (lids,se) ->
                        FStar_All.pipe_right lids
                          (FStar_List.iter
                             (fun lid  ->
                                let uu____8835 =
                                  let uu____8836 =
                                    let uu____8839 = FStar_ST.op_Bang globals
                                       in
                                    (Top_level_def (lid.FStar_Ident.ident))
                                      :: uu____8839
                                     in
                                  FStar_ST.op_Colon_Equals globals uu____8836
                                   in
                                match uu____8835 with
                                | () ->
                                    let modul =
                                      let uu____8941 =
                                        FStar_Ident.lid_of_ids
                                          lid.FStar_Ident.ns
                                         in
                                      uu____8941.FStar_Ident.str  in
                                    let uu____8942 =
                                      let uu____8943 =
                                        get_exported_id_set env3 modul  in
                                      match uu____8943 with
                                      | FStar_Pervasives_Native.Some f ->
                                          let my_exported_ids =
                                            f Exported_id_term_type  in
                                          let uu____8976 =
                                            let uu____8977 =
                                              FStar_ST.op_Bang
                                                my_exported_ids
                                               in
                                            FStar_Util.set_add
                                              (lid.FStar_Ident.ident).FStar_Ident.idText
                                              uu____8977
                                             in
                                          FStar_ST.op_Colon_Equals
                                            my_exported_ids uu____8976
                                      | FStar_Pervasives_Native.None  -> ()
                                       in
                                    (match uu____8942 with
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
                                                   env3.admitted_iface))))))))
             in
          let env4 =
            let uu___128_9081 = env3  in
            let uu____9082 = FStar_ST.op_Bang globals  in
            {
              curmodule = (uu___128_9081.curmodule);
              curmonad = (uu___128_9081.curmonad);
              modules = (uu___128_9081.modules);
              scope_mods = uu____9082;
              exported_ids = (uu___128_9081.exported_ids);
              trans_exported_ids = (uu___128_9081.trans_exported_ids);
              includes = (uu___128_9081.includes);
              sigaccum = (uu___128_9081.sigaccum);
              sigmap = (uu___128_9081.sigmap);
              iface = (uu___128_9081.iface);
              admitted_iface = (uu___128_9081.admitted_iface);
              expect_typ = (uu___128_9081.expect_typ);
              docs = (uu___128_9081.docs);
              remaining_iface_decls = (uu___128_9081.remaining_iface_decls);
              syntax_only = (uu___128_9081.syntax_only);
              ds_hooks = (uu___128_9081.ds_hooks)
            }  in
          env4
  
let (push_namespace : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun ns  ->
      let uu____9144 =
        let uu____9149 = resolve_module_name env ns false  in
        match uu____9149 with
        | FStar_Pervasives_Native.None  ->
            let modules = env.modules  in
            let uu____9163 =
              FStar_All.pipe_right modules
                (FStar_Util.for_some
                   (fun uu____9179  ->
                      match uu____9179 with
                      | (m,uu____9185) ->
                          let uu____9186 =
                            let uu____9187 = FStar_Ident.text_of_lid m  in
                            Prims.strcat uu____9187 "."  in
                          let uu____9188 =
                            let uu____9189 = FStar_Ident.text_of_lid ns  in
                            Prims.strcat uu____9189 "."  in
                          FStar_Util.starts_with uu____9186 uu____9188))
               in
            if uu____9163
            then (ns, Open_namespace)
            else
              (let uu____9195 =
                 let uu____9200 =
                   let uu____9201 = FStar_Ident.text_of_lid ns  in
                   FStar_Util.format1 "Namespace %s cannot be found"
                     uu____9201
                    in
                 (FStar_Errors.Fatal_NameSpaceNotFound, uu____9200)  in
               let uu____9202 = FStar_Ident.range_of_lid ns  in
               FStar_Errors.raise_error uu____9195 uu____9202)
        | FStar_Pervasives_Native.Some ns' ->
            let uu____9208 = fail_if_curmodule env ns ns'  in
            (ns', Open_module)
         in
      match uu____9144 with
      | (ns',kd) ->
          let uu____9211 = (env.ds_hooks).ds_push_open_hook env (ns', kd)  in
          push_scope_mod env (Open_module_or_namespace (ns', kd))
  
let (push_include : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun ns  ->
      let ns0 = ns  in
      let uu____9223 = resolve_module_name env ns false  in
      match uu____9223 with
      | FStar_Pervasives_Native.Some ns1 ->
          let uu____9227 = (env.ds_hooks).ds_push_include_hook env ns1  in
          let uu____9228 = fail_if_curmodule env ns0 ns1  in
          let env1 =
            push_scope_mod env (Open_module_or_namespace (ns1, Open_module))
             in
          let curmod =
            let uu____9231 = current_module env1  in
            uu____9231.FStar_Ident.str  in
          let uu____9232 =
            let uu____9233 = FStar_Util.smap_try_find env1.includes curmod
               in
            match uu____9233 with
            | FStar_Pervasives_Native.None  -> ()
            | FStar_Pervasives_Native.Some incl ->
                let uu____9257 =
                  let uu____9260 = FStar_ST.op_Bang incl  in ns1 ::
                    uu____9260
                   in
                FStar_ST.op_Colon_Equals incl uu____9257
             in
          (match uu____9232 with
           | () ->
               let uu____9361 =
                 get_trans_exported_id_set env1 ns1.FStar_Ident.str  in
               (match uu____9361 with
                | FStar_Pervasives_Native.Some ns_trans_exports ->
                    let uu____9380 =
                      let uu____9381 =
                        let uu____9400 = get_exported_id_set env1 curmod  in
                        let uu____9408 =
                          get_trans_exported_id_set env1 curmod  in
                        (uu____9400, uu____9408)  in
                      match uu____9381 with
                      | (FStar_Pervasives_Native.Some
                         cur_exports,FStar_Pervasives_Native.Some
                         cur_trans_exports) ->
                          let update_exports k =
                            let ns_ex =
                              let uu____9472 = ns_trans_exports k  in
                              FStar_ST.op_Bang uu____9472  in
                            let ex = cur_exports k  in
                            let uu____9605 =
                              let uu____9606 =
                                let uu____9607 = FStar_ST.op_Bang ex  in
                                FStar_Util.set_difference uu____9607 ns_ex
                                 in
                              FStar_ST.op_Colon_Equals ex uu____9606  in
                            match uu____9605 with
                            | () ->
                                let trans_ex = cur_trans_exports k  in
                                let uu____9714 =
                                  let uu____9715 =
                                    let uu____9716 =
                                      FStar_ST.op_Bang trans_ex  in
                                    FStar_Util.set_union uu____9716 ns_ex  in
                                  FStar_ST.op_Colon_Equals trans_ex
                                    uu____9715
                                   in
                                ()
                             in
                          FStar_List.iter update_exports
                            all_exported_id_kinds
                      | uu____9809 -> ()  in
                    (match uu____9380 with | () -> env1)
                | FStar_Pervasives_Native.None  ->
                    let uu____9833 =
                      let uu____9838 =
                        FStar_Util.format1
                          "include: Module %s was not prepared"
                          ns1.FStar_Ident.str
                         in
                      (FStar_Errors.Fatal_IncludeModuleNotPrepared,
                        uu____9838)
                       in
                    let uu____9839 = FStar_Ident.range_of_lid ns1  in
                    FStar_Errors.raise_error uu____9833 uu____9839))
      | uu____9840 ->
          let uu____9843 =
            let uu____9848 =
              FStar_Util.format1 "include: Module %s cannot be found"
                ns.FStar_Ident.str
               in
            (FStar_Errors.Fatal_ModuleNotFound, uu____9848)  in
          let uu____9849 = FStar_Ident.range_of_lid ns  in
          FStar_Errors.raise_error uu____9843 uu____9849
  
let (push_module_abbrev :
  env -> FStar_Ident.ident -> FStar_Ident.lident -> env) =
  fun env  ->
    fun x  ->
      fun l  ->
        let uu____9865 = module_is_defined env l  in
        if uu____9865
        then
          let uu____9866 = fail_if_curmodule env l l  in
          let uu____9867 = (env.ds_hooks).ds_push_module_abbrev_hook env x l
             in
          push_scope_mod env (Module_abbrev (x, l))
        else
          (let uu____9869 =
             let uu____9874 =
               let uu____9875 = FStar_Ident.text_of_lid l  in
               FStar_Util.format1 "Module %s cannot be found" uu____9875  in
             (FStar_Errors.Fatal_ModuleNotFound, uu____9874)  in
           let uu____9876 = FStar_Ident.range_of_lid l  in
           FStar_Errors.raise_error uu____9869 uu____9876)
  
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
            let uu____9897 =
              let uu____9898 =
                FStar_Util.smap_try_find env.docs l.FStar_Ident.str  in
              match uu____9898 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some old_doc ->
                  let uu____9902 = FStar_Ident.range_of_lid l  in
                  let uu____9903 =
                    let uu____9908 =
                      let uu____9909 = FStar_Ident.string_of_lid l  in
                      let uu____9910 =
                        FStar_Parser_AST.string_of_fsdoc old_doc  in
                      let uu____9911 = FStar_Parser_AST.string_of_fsdoc doc1
                         in
                      FStar_Util.format3
                        "Overwriting doc of %s; old doc was [%s]; new doc are [%s]"
                        uu____9909 uu____9910 uu____9911
                       in
                    (FStar_Errors.Warning_DocOverwrite, uu____9908)  in
                  FStar_Errors.log_issue uu____9902 uu____9903
               in
            let uu____9912 =
              FStar_Util.smap_add env.docs l.FStar_Ident.str doc1  in
            env
  
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
                      let uu____9951 =
                        FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption)
                         in
                      Prims.op_Negation uu____9951 ->
                      let uu____9954 =
                        FStar_Util.smap_try_find (sigmap env)
                          l.FStar_Ident.str
                         in
                      (match uu____9954 with
                       | FStar_Pervasives_Native.Some
                           ({
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_let uu____9967;
                              FStar_Syntax_Syntax.sigrng = uu____9968;
                              FStar_Syntax_Syntax.sigquals = uu____9969;
                              FStar_Syntax_Syntax.sigmeta = uu____9970;
                              FStar_Syntax_Syntax.sigattrs = uu____9971;_},uu____9972)
                           -> lids
                       | FStar_Pervasives_Native.Some
                           ({
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_inductive_typ
                                uu____9987;
                              FStar_Syntax_Syntax.sigrng = uu____9988;
                              FStar_Syntax_Syntax.sigquals = uu____9989;
                              FStar_Syntax_Syntax.sigmeta = uu____9990;
                              FStar_Syntax_Syntax.sigattrs = uu____9991;_},uu____9992)
                           -> lids
                       | uu____10017 ->
                           let uu____10024 =
                             let uu____10025 =
                               let uu____10026 = FStar_Options.interactive ()
                                  in
                               Prims.op_Negation uu____10026  in
                             if uu____10025
                             then
                               let uu____10027 = FStar_Ident.range_of_lid l
                                  in
                               let uu____10028 =
                                 let uu____10033 =
                                   let uu____10034 =
                                     FStar_Ident.string_of_lid l  in
                                   FStar_Util.format1
                                     "Admitting %s without a definition"
                                     uu____10034
                                    in
                                 (FStar_Errors.Warning_AdmitWithoutDefinition,
                                   uu____10033)
                                  in
                               FStar_Errors.log_issue uu____10027 uu____10028
                             else ()  in
                           let quals = FStar_Syntax_Syntax.Assumption ::
                             (se.FStar_Syntax_Syntax.sigquals)  in
                           let uu____10039 =
                             FStar_Util.smap_add (sigmap env)
                               l.FStar_Ident.str
                               ((let uu___129_10045 = se  in
                                 {
                                   FStar_Syntax_Syntax.sigel =
                                     (uu___129_10045.FStar_Syntax_Syntax.sigel);
                                   FStar_Syntax_Syntax.sigrng =
                                     (uu___129_10045.FStar_Syntax_Syntax.sigrng);
                                   FStar_Syntax_Syntax.sigquals = quals;
                                   FStar_Syntax_Syntax.sigmeta =
                                     (uu___129_10045.FStar_Syntax_Syntax.sigmeta);
                                   FStar_Syntax_Syntax.sigattrs =
                                     (uu___129_10045.FStar_Syntax_Syntax.sigattrs)
                                 }), false)
                              in
                           l :: lids)
                  | uu____10046 -> lids) [])
         in
      let uu___130_10047 = m  in
      let uu____10048 =
        FStar_All.pipe_right m.FStar_Syntax_Syntax.declarations
          (FStar_List.map
             (fun s  ->
                match s.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_declare_typ
                    (lid,uu____10058,uu____10059) when
                    FStar_List.existsb
                      (fun l  -> FStar_Ident.lid_equals l lid)
                      admitted_sig_lids
                    ->
                    let uu___131_10062 = s  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___131_10062.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___131_10062.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals =
                        (FStar_Syntax_Syntax.Assumption ::
                        (s.FStar_Syntax_Syntax.sigquals));
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___131_10062.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___131_10062.FStar_Syntax_Syntax.sigattrs)
                    }
                | uu____10063 -> s))
         in
      {
        FStar_Syntax_Syntax.name = (uu___130_10047.FStar_Syntax_Syntax.name);
        FStar_Syntax_Syntax.declarations = uu____10048;
        FStar_Syntax_Syntax.exports =
          (uu___130_10047.FStar_Syntax_Syntax.exports);
        FStar_Syntax_Syntax.is_interface =
          (uu___130_10047.FStar_Syntax_Syntax.is_interface)
      }
  
let (finish : env -> FStar_Syntax_Syntax.modul -> env) =
  fun env  ->
    fun modul  ->
      let uu____10074 =
        FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations
          (FStar_List.iter
             (fun se  ->
                let quals = se.FStar_Syntax_Syntax.sigquals  in
                match se.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_bundle (ses,uu____10084) ->
                    if
                      (FStar_List.contains FStar_Syntax_Syntax.Private quals)
                        ||
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract
                           quals)
                    then
                      FStar_All.pipe_right ses
                        (FStar_List.iter
                           (fun se1  ->
                              match se1.FStar_Syntax_Syntax.sigel with
                              | FStar_Syntax_Syntax.Sig_datacon
                                  (lid,uu____10104,uu____10105,uu____10106,uu____10107,uu____10108)
                                  ->
                                  FStar_Util.smap_remove (sigmap env)
                                    lid.FStar_Ident.str
                              | FStar_Syntax_Syntax.Sig_inductive_typ
                                  (lid,univ_names,binders,typ,uu____10121,uu____10122)
                                  ->
                                  let uu____10131 =
                                    FStar_Util.smap_remove (sigmap env)
                                      lid.FStar_Ident.str
                                     in
                                  if
                                    Prims.op_Negation
                                      (FStar_List.contains
                                         FStar_Syntax_Syntax.Private quals)
                                  then
                                    let sigel =
                                      let uu____10137 =
                                        let uu____10144 =
                                          let uu____10147 =
                                            FStar_Ident.range_of_lid lid  in
                                          let uu____10148 =
                                            let uu____10153 =
                                              let uu____10154 =
                                                let uu____10167 =
                                                  FStar_Syntax_Syntax.mk_Total
                                                    typ
                                                   in
                                                (binders, uu____10167)  in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____10154
                                               in
                                            FStar_Syntax_Syntax.mk
                                              uu____10153
                                             in
                                          uu____10148
                                            FStar_Pervasives_Native.None
                                            uu____10147
                                           in
                                        (lid, univ_names, uu____10144)  in
                                      FStar_Syntax_Syntax.Sig_declare_typ
                                        uu____10137
                                       in
                                    let se2 =
                                      let uu___132_10174 = se1  in
                                      {
                                        FStar_Syntax_Syntax.sigel = sigel;
                                        FStar_Syntax_Syntax.sigrng =
                                          (uu___132_10174.FStar_Syntax_Syntax.sigrng);
                                        FStar_Syntax_Syntax.sigquals =
                                          (FStar_Syntax_Syntax.Assumption ::
                                          quals);
                                        FStar_Syntax_Syntax.sigmeta =
                                          (uu___132_10174.FStar_Syntax_Syntax.sigmeta);
                                        FStar_Syntax_Syntax.sigattrs =
                                          (uu___132_10174.FStar_Syntax_Syntax.sigattrs)
                                      }  in
                                    FStar_Util.smap_add (sigmap env)
                                      lid.FStar_Ident.str (se2, false)
                                  else ()
                              | uu____10180 -> ()))
                    else ()
                | FStar_Syntax_Syntax.Sig_declare_typ
                    (lid,uu____10183,uu____10184) ->
                    if FStar_List.contains FStar_Syntax_Syntax.Private quals
                    then
                      FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str
                    else ()
                | FStar_Syntax_Syntax.Sig_let ((uu____10190,lbs),uu____10192)
                    ->
                    let uu____10207 =
                      if
                        (FStar_List.contains FStar_Syntax_Syntax.Private
                           quals)
                          ||
                          (FStar_List.contains FStar_Syntax_Syntax.Abstract
                             quals)
                      then
                        FStar_All.pipe_right lbs
                          (FStar_List.iter
                             (fun lb  ->
                                let uu____10213 =
                                  let uu____10214 =
                                    let uu____10215 =
                                      let uu____10218 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname
                                         in
                                      uu____10218.FStar_Syntax_Syntax.fv_name
                                       in
                                    uu____10215.FStar_Syntax_Syntax.v  in
                                  uu____10214.FStar_Ident.str  in
                                FStar_Util.smap_remove (sigmap env)
                                  uu____10213))
                      else ()  in
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
                                let uu____10232 =
                                  let uu____10235 =
                                    FStar_Util.right
                                      lb.FStar_Syntax_Syntax.lbname
                                     in
                                  uu____10235.FStar_Syntax_Syntax.fv_name  in
                                uu____10232.FStar_Syntax_Syntax.v  in
                              let quals1 = FStar_Syntax_Syntax.Assumption ::
                                quals  in
                              let decl =
                                let uu___133_10240 = se  in
                                {
                                  FStar_Syntax_Syntax.sigel =
                                    (FStar_Syntax_Syntax.Sig_declare_typ
                                       (lid,
                                         (lb.FStar_Syntax_Syntax.lbunivs),
                                         (lb.FStar_Syntax_Syntax.lbtyp)));
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___133_10240.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals = quals1;
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___133_10240.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (uu___133_10240.FStar_Syntax_Syntax.sigattrs)
                                }  in
                              FStar_Util.smap_add (sigmap env)
                                lid.FStar_Ident.str (decl, false)))
                    else ()
                | uu____10250 -> ()))
         in
      let curmod =
        let uu____10252 = current_module env  in uu____10252.FStar_Ident.str
         in
      let uu____10253 =
        let uu____10254 =
          let uu____10273 = get_exported_id_set env curmod  in
          let uu____10281 = get_trans_exported_id_set env curmod  in
          (uu____10273, uu____10281)  in
        match uu____10254 with
        | (FStar_Pervasives_Native.Some cur_ex,FStar_Pervasives_Native.Some
           cur_trans_ex) ->
            let update_exports eikind =
              let cur_ex_set =
                let uu____10345 = cur_ex eikind  in
                FStar_ST.op_Bang uu____10345  in
              let cur_trans_ex_set_ref = cur_trans_ex eikind  in
              let uu____10478 =
                let uu____10479 = FStar_ST.op_Bang cur_trans_ex_set_ref  in
                FStar_Util.set_union cur_ex_set uu____10479  in
              FStar_ST.op_Colon_Equals cur_trans_ex_set_ref uu____10478  in
            FStar_List.iter update_exports all_exported_id_kinds
        | uu____10572 -> ()  in
      match uu____10253 with
      | () ->
          let uu____10591 = filter_record_cache ()  in
          (match uu____10591 with
           | () ->
               let uu___134_10592 = env  in
               {
                 curmodule = FStar_Pervasives_Native.None;
                 curmonad = (uu___134_10592.curmonad);
                 modules = (((modul.FStar_Syntax_Syntax.name), modul) ::
                   (env.modules));
                 scope_mods = [];
                 exported_ids = (uu___134_10592.exported_ids);
                 trans_exported_ids = (uu___134_10592.trans_exported_ids);
                 includes = (uu___134_10592.includes);
                 sigaccum = [];
                 sigmap = (uu___134_10592.sigmap);
                 iface = (uu___134_10592.iface);
                 admitted_iface = (uu___134_10592.admitted_iface);
                 expect_typ = (uu___134_10592.expect_typ);
                 docs = (uu___134_10592.docs);
                 remaining_iface_decls =
                   (uu___134_10592.remaining_iface_decls);
                 syntax_only = (uu___134_10592.syntax_only);
                 ds_hooks = (uu___134_10592.ds_hooks)
               })
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push : env -> env) =
  fun env  ->
    let uu____10619 = push_record_cache ()  in
    let uu____10620 =
      let uu____10621 =
        let uu____10624 = FStar_ST.op_Bang stack  in env :: uu____10624  in
      FStar_ST.op_Colon_Equals stack uu____10621  in
    let uu___135_10681 = env  in
    let uu____10682 = FStar_Util.smap_copy (sigmap env)  in
    let uu____10693 = FStar_Util.smap_copy env.docs  in
    {
      curmodule = (uu___135_10681.curmodule);
      curmonad = (uu___135_10681.curmonad);
      modules = (uu___135_10681.modules);
      scope_mods = (uu___135_10681.scope_mods);
      exported_ids = (uu___135_10681.exported_ids);
      trans_exported_ids = (uu___135_10681.trans_exported_ids);
      includes = (uu___135_10681.includes);
      sigaccum = (uu___135_10681.sigaccum);
      sigmap = uu____10682;
      iface = (uu___135_10681.iface);
      admitted_iface = (uu___135_10681.admitted_iface);
      expect_typ = (uu___135_10681.expect_typ);
      docs = uu____10693;
      remaining_iface_decls = (uu___135_10681.remaining_iface_decls);
      syntax_only = (uu___135_10681.syntax_only);
      ds_hooks = (uu___135_10681.ds_hooks)
    }
  
let (pop : unit -> env) =
  fun uu____10700  ->
    let uu____10701 = FStar_ST.op_Bang stack  in
    match uu____10701 with
    | env::tl1 ->
        let uu____10735 = pop_record_cache ()  in
        let uu____10736 = FStar_ST.op_Colon_Equals stack tl1  in env
    | uu____10764 -> failwith "Impossible: Too many pops"
  
let (export_interface : FStar_Ident.lident -> env -> env) =
  fun m  ->
    fun env  ->
      let sigelt_in_m se =
        match FStar_Syntax_Util.lids_of_sigelt se with
        | l::uu____10783 -> l.FStar_Ident.nsstr = m.FStar_Ident.str
        | uu____10786 -> false  in
      let sm = sigmap env  in
      let env1 = pop ()  in
      let keys = FStar_Util.smap_keys sm  in
      let sm' = sigmap env1  in
      let uu____10811 =
        FStar_All.pipe_right keys
          (FStar_List.iter
             (fun k  ->
                let uu____10820 = FStar_Util.smap_try_find sm' k  in
                match uu____10820 with
                | FStar_Pervasives_Native.Some (se,true ) when sigelt_in_m se
                    ->
                    let uu____10836 = FStar_Util.smap_remove sm' k  in
                    let se1 =
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t) ->
                          let uu___136_10845 = se  in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (uu___136_10845.FStar_Syntax_Syntax.sigel);
                            FStar_Syntax_Syntax.sigrng =
                              (uu___136_10845.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (FStar_Syntax_Syntax.Assumption ::
                              (se.FStar_Syntax_Syntax.sigquals));
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___136_10845.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___136_10845.FStar_Syntax_Syntax.sigattrs)
                          }
                      | uu____10846 -> se  in
                    FStar_Util.smap_add sm' k (se1, false)
                | uu____10851 -> ()))
         in
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
      let uu____10874 = finish env modul1  in (uu____10874, modul1)
  
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
      let uu____10960 =
        let uu____10963 = e Exported_id_term_type  in
        FStar_ST.op_Bang uu____10963  in
      FStar_Util.set_elements uu____10960  in
    let fields =
      let uu____11085 =
        let uu____11088 = e Exported_id_field  in
        FStar_ST.op_Bang uu____11088  in
      FStar_Util.set_elements uu____11085  in
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
          let uu____11247 =
            FStar_Util.as_set e1.exported_id_terms FStar_Util.compare  in
          FStar_Util.mk_ref uu____11247  in
        let fields =
          let uu____11257 =
            FStar_Util.as_set e1.exported_id_fields FStar_Util.compare  in
          FStar_Util.mk_ref uu____11257  in
        (fun uu___111_11262  ->
           match uu___111_11262 with
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
  'Auu____11390 .
    'Auu____11390 Prims.list FStar_Pervasives_Native.option ->
      'Auu____11390 Prims.list FStar_ST.ref
  =
  fun uu___112_11403  ->
    match uu___112_11403 with
    | FStar_Pervasives_Native.None  -> FStar_Util.mk_ref []
    | FStar_Pervasives_Native.Some l -> FStar_Util.mk_ref l
  
let (inclusion_info : env -> FStar_Ident.lident -> module_inclusion_info) =
  fun env  ->
    fun l  ->
      let mname = FStar_Ident.string_of_lid l  in
      let as_ids_opt m =
        let uu____11443 = FStar_Util.smap_try_find m mname  in
        FStar_Util.map_opt uu____11443 as_exported_ids  in
      let uu____11449 = as_ids_opt env.exported_ids  in
      let uu____11452 = as_ids_opt env.trans_exported_ids  in
      let uu____11455 =
        let uu____11460 = FStar_Util.smap_try_find env.includes mname  in
        FStar_Util.map_opt uu____11460 (fun r  -> FStar_ST.op_Bang r)  in
      {
        mii_exported_ids = uu____11449;
        mii_trans_exported_ids = uu____11452;
        mii_includes = uu____11455
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
                let uu____11578 = FStar_Ident.text_of_lid mname  in
                FStar_Util.strcat uu____11578 ".fst"  in
              let auto_open =
                FStar_Parser_Dep.hard_coded_dependencies filename  in
              let auto_open1 =
                let convert_kind uu___113_11597 =
                  match uu___113_11597 with
                  | FStar_Parser_Dep.Open_namespace  -> Open_namespace
                  | FStar_Parser_Dep.Open_module  -> Open_module  in
                FStar_List.map
                  (fun uu____11609  ->
                     match uu____11609 with
                     | (lid,kind) -> (lid, (convert_kind kind))) auto_open
                 in
              let namespace_of_module =
                if
                  (FStar_List.length mname.FStar_Ident.ns) >
                    (Prims.parse_int "0")
                then
                  let uu____11633 =
                    let uu____11638 =
                      FStar_Ident.lid_of_ids mname.FStar_Ident.ns  in
                    (uu____11638, Open_namespace)  in
                  [uu____11633]
                else []  in
              let auto_open2 =
                FStar_List.append namespace_of_module
                  (FStar_List.rev auto_open1)
                 in
              let uu____11667 =
                let uu____11668 = as_exported_id_set mii.mii_exported_ids  in
                FStar_Util.smap_add env1.exported_ids mname.FStar_Ident.str
                  uu____11668
                 in
              match uu____11667 with
              | () ->
                  let uu____11693 =
                    let uu____11694 =
                      as_exported_id_set mii.mii_trans_exported_ids  in
                    FStar_Util.smap_add env1.trans_exported_ids
                      mname.FStar_Ident.str uu____11694
                     in
                  (match uu____11693 with
                   | () ->
                       let uu____11719 =
                         let uu____11720 = as_includes mii.mii_includes  in
                         FStar_Util.smap_add env1.includes
                           mname.FStar_Ident.str uu____11720
                          in
                       (match uu____11719 with
                        | () ->
                            let env' =
                              let uu___137_11752 = env1  in
                              let uu____11753 =
                                FStar_List.map
                                  (fun x  -> Open_module_or_namespace x)
                                  auto_open2
                                 in
                              {
                                curmodule =
                                  (FStar_Pervasives_Native.Some mname);
                                curmonad = (uu___137_11752.curmonad);
                                modules = (uu___137_11752.modules);
                                scope_mods = uu____11753;
                                exported_ids = (uu___137_11752.exported_ids);
                                trans_exported_ids =
                                  (uu___137_11752.trans_exported_ids);
                                includes = (uu___137_11752.includes);
                                sigaccum = (uu___137_11752.sigaccum);
                                sigmap = (env1.sigmap);
                                iface = intf;
                                admitted_iface = admitted;
                                expect_typ = (uu___137_11752.expect_typ);
                                docs = (uu___137_11752.docs);
                                remaining_iface_decls =
                                  (uu___137_11752.remaining_iface_decls);
                                syntax_only = (uu___137_11752.syntax_only);
                                ds_hooks = (uu___137_11752.ds_hooks)
                              }  in
                            let uu____11758 =
                              FStar_List.iter
                                (fun op  ->
                                   (env1.ds_hooks).ds_push_open_hook env' op)
                                (FStar_List.rev auto_open2)
                               in
                            env'))
               in
            let uu____11765 =
              FStar_All.pipe_right env.modules
                (FStar_Util.find_opt
                   (fun uu____11791  ->
                      match uu____11791 with
                      | (l,uu____11797) -> FStar_Ident.lid_equals l mname))
               in
            match uu____11765 with
            | FStar_Pervasives_Native.None  ->
                let uu____11806 = prep env  in (uu____11806, false)
            | FStar_Pervasives_Native.Some (uu____11807,m) ->
                let uu____11813 =
                  let uu____11814 =
                    (let uu____11817 = FStar_Options.interactive ()  in
                     Prims.op_Negation uu____11817) &&
                      ((Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)
                         || intf)
                     in
                  if uu____11814
                  then
                    let uu____11818 =
                      let uu____11823 =
                        FStar_Util.format1
                          "Duplicate module or interface name: %s"
                          mname.FStar_Ident.str
                         in
                      (FStar_Errors.Fatal_DuplicateModuleOrInterface,
                        uu____11823)
                       in
                    let uu____11824 = FStar_Ident.range_of_lid mname  in
                    FStar_Errors.raise_error uu____11818 uu____11824
                  else ()  in
                let uu____11826 =
                  let uu____11827 = push env  in prep uu____11827  in
                (uu____11826, true)
  
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
          let uu___138_11839 = env  in
          {
            curmodule = (uu___138_11839.curmodule);
            curmonad = (FStar_Pervasives_Native.Some mname);
            modules = (uu___138_11839.modules);
            scope_mods = (uu___138_11839.scope_mods);
            exported_ids = (uu___138_11839.exported_ids);
            trans_exported_ids = (uu___138_11839.trans_exported_ids);
            includes = (uu___138_11839.includes);
            sigaccum = (uu___138_11839.sigaccum);
            sigmap = (uu___138_11839.sigmap);
            iface = (uu___138_11839.iface);
            admitted_iface = (uu___138_11839.admitted_iface);
            expect_typ = (uu___138_11839.expect_typ);
            docs = (uu___138_11839.docs);
            remaining_iface_decls = (uu___138_11839.remaining_iface_decls);
            syntax_only = (uu___138_11839.syntax_only);
            ds_hooks = (uu___138_11839.ds_hooks)
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
        let uu____11873 = lookup1 lid  in
        match uu____11873 with
        | FStar_Pervasives_Native.None  ->
            let opened_modules =
              FStar_List.map
                (fun uu____11886  ->
                   match uu____11886 with
                   | (lid1,uu____11892) -> FStar_Ident.text_of_lid lid1)
                env.modules
               in
            let msg =
              let uu____11894 = FStar_Ident.text_of_lid lid  in
              FStar_Util.format1 "Identifier not found: [%s]" uu____11894  in
            let msg1 =
              if
                (FStar_List.length lid.FStar_Ident.ns) =
                  (Prims.parse_int "0")
              then msg
              else
                (let modul =
                   let uu____11898 =
                     FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
                   let uu____11899 = FStar_Ident.range_of_lid lid  in
                   FStar_Ident.set_lid_range uu____11898 uu____11899  in
                 let uu____11900 = resolve_module_name env modul true  in
                 match uu____11900 with
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
            let uu____11909 = FStar_Ident.range_of_lid lid  in
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_IdentifierNotFound, msg1) uu____11909
        | FStar_Pervasives_Native.Some r -> r
  
let fail_or2 :
  'a .
    (FStar_Ident.ident -> 'a FStar_Pervasives_Native.option) ->
      FStar_Ident.ident -> 'a
  =
  fun lookup1  ->
    fun id1  ->
      let uu____11937 = lookup1 id1  in
      match uu____11937 with
      | FStar_Pervasives_Native.None  ->
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_IdentifierNotFound,
              (Prims.strcat "Identifier not found ["
                 (Prims.strcat id1.FStar_Ident.idText "]")))
            id1.FStar_Ident.idRange
      | FStar_Pervasives_Native.Some r -> r
  
let (mk_copy : env -> env) =
  fun en  ->
    let uu___139_11946 = en  in
    let uu____11947 = FStar_Util.smap_copy en.exported_ids  in
    let uu____11952 = FStar_Util.smap_copy en.trans_exported_ids  in
    let uu____11957 = FStar_Util.smap_copy en.sigmap  in
    let uu____11968 = FStar_Util.smap_copy en.docs  in
    {
      curmodule = (uu___139_11946.curmodule);
      curmonad = (uu___139_11946.curmonad);
      modules = (uu___139_11946.modules);
      scope_mods = (uu___139_11946.scope_mods);
      exported_ids = uu____11947;
      trans_exported_ids = uu____11952;
      includes = (uu___139_11946.includes);
      sigaccum = (uu___139_11946.sigaccum);
      sigmap = uu____11957;
      iface = (uu___139_11946.iface);
      admitted_iface = (uu___139_11946.admitted_iface);
      expect_typ = (uu___139_11946.expect_typ);
      docs = uu____11968;
      remaining_iface_decls = (uu___139_11946.remaining_iface_decls);
      syntax_only = (uu___139_11946.syntax_only);
      ds_hooks = (uu___139_11946.ds_hooks)
    }
  